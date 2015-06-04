/* -*- Mode: C; tab-width: 4; c-basic-offset: 4; indent-tabs-mode: nil -*- */
#include "memcached.h"
#include <sys/stat.h>
#include <sys/socket.h>
#include <sys/signal.h>
#include <sys/resource.h>
#include <fcntl.h>
#include <netinet/in.h>
#include <errno.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <assert.h>
#include <unistd.h>

/* Forward Declarations */
static void item_link_q(item *it);
static void item_unlink_q(item *it);

#define LARGEST_ID POWER_LARGEST
typedef struct {
    uint64_t evicted;//因为LRU踢了多少个item
     //即使一个item的exptime设置为0，也是会被踢的
    uint64_t evicted_nonzero;//被踢的item中，超时时间(exptime)不为0的item数

    //最后一次踢item时，被踢的item已经过期多久了
    //itemstats[id].evicted_time = current_time - search->time;
    rel_time_t evicted_time;
    uint64_t reclaimed;//在申请item时，发现过期并回收的item数量
    uint64_t outofmemory;//为item申请内存，失败的次数
    uint64_t tailrepairs;//需要修复的item数量(除非worker线程有问题否则一般为0)


    uint64_t expired_unfetched;//直到被超时删除时都还没被访问过的item数量 
    uint64_t evicted_unfetched;//直到被LRU踢出时都还没有被访问过的item数量
    uint64_t crawler_reclaimed;//被LRU爬虫发现的过期item数量 
    //申请item而搜索LRU队列时，被其他worker线程引用的item数量
    uint64_t lrutail_reflocked;
} itemstats_t;

static item *heads[LARGEST_ID];//指向每一个LRU队列头
static item *tails[LARGEST_ID];//指向每一个LRU队列尾
static crawler crawlers[LARGEST_ID];

//itemstats变量是一个数组，它是和slabclass数组一一对应
//itemstats数组的元素负责收集slabclass数组中对应元素的信息
static itemstats_t itemstats[LARGEST_ID];
static unsigned int sizes[LARGEST_ID];//每一个LRU队列有多少个item

static int crawler_count = 0;//本次任务要处理多少个LRU队列
static volatile int do_run_lru_crawler_thread = 0;
static int lru_crawler_initialized = 0;
static pthread_mutex_t lru_crawler_lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t  lru_crawler_cond = PTHREAD_COND_INITIALIZER;

void item_stats_reset(void) {
    mutex_lock(&cache_lock);
    memset(itemstats, 0, sizeof(itemstats));
    mutex_unlock(&cache_lock);
}


/* Get the next CAS id for a new item. */
uint64_t get_cas_id(void) {
    static uint64_t cas_id = 0;
    return ++cas_id;
}

/* Enable this for reference-count debugging. */
#if 0
# define DEBUG_REFCNT(it,op) \
                fprintf(stderr, "item %x refcnt(%c) %d %c%c%c\n", \
                        it, op, it->refcount, \
                        (it->it_flags & ITEM_LINKED) ? 'L' : ' ', \
                        (it->it_flags & ITEM_SLABBED) ? 'S' : ' ')
#else
# define DEBUG_REFCNT(it,op) while(0)
#endif

/**
 * Generates the variable-sized part of the header for an object.
 *
 * key     - The key
 * nkey    - The length of the key
 * flags   - key flags
 * nbytes  - Number of bytes to hold value and addition CRLF terminator
 * suffix  - Buffer for the "VALUE" line suffix (flags, size).
 * nsuffix - The length of the suffix is stored here.
 *
 * Returns the total size of the header.
 */
static size_t item_make_header(const uint8_t nkey, const int flags, const int nbytes,
                     char *suffix, uint8_t *nsuffix) {
    /* suffix is defined at 40 chars elsewhere.. */
    *nsuffix = (uint8_t) snprintf(suffix, 40, " %d %d\r\n", flags, nbytes - 2);
    return sizeof(item) + nkey + *nsuffix + nbytes;
}

/*@null@*/
//key、flags、exptime三个参数是用户在使用set、add命令存储一条数据时输入的参数。
//nkey是key字符串的长度。nbytes则是用户要存储的data长度+2,因为在data的结尾处还要加上"\r\n"  
//cur_hv则是根据键值key计算得到的哈希值。
item *do_item_alloc(char *key, const size_t nkey, const int flags,
                    const rel_time_t exptime, const int nbytes,
                    const uint32_t cur_hv) {
    uint8_t nsuffix;
    item *it = NULL;
    char suffix[40];

    //要存储这个item需要的总空间。要注意第一个参数是nkey+1，
    //所以上面的那些宏计算时,使用了(item)->nkey + 1
    size_t ntotal = item_make_header(nkey + 1, flags, nbytes, suffix, &nsuffix);
    if (settings.use_cas) {//开启了CAS功能
        ntotal += sizeof(uint64_t);
    }

    //根据大小判断从属于哪个slab
    unsigned int id = slabs_clsid(ntotal);
    if (id == 0)//0表示不属于任何一个slab
        return 0;

    mutex_lock(&cache_lock);
    /* do a quick check if we have any expired items in the tail.. */
    int tries = 5;
    /* Avoid hangs if a slab has nothing but refcounted stuff in it. */
    int tries_lrutail_reflocked = 1000;
    int tried_alloc = 0;
    item *search;
    item *next_it;
    void *hold_lock = NULL;
    rel_time_t oldest_live = settings.oldest_live;

    search = tails[id];
    /* We walk up *only* for locked items. Never searching for expired.
     * Waste of CPU for almost all deployments */
    for (; tries > 0 && search != NULL; tries--, search=next_it) {
        /* we might relink search mid-loop, so search->prev isn't reliable */
        next_it = search->prev;
        if (search->nbytes == 0 && search->nkey == 0 && search->it_flags == 1) {
            /* We are a crawler, ignore it. */
            tries++;
            continue;
        }
        uint32_t hv = hash(ITEM_key(search), search->nkey);
        /* Attempt to hash item lock the "search" item. If locked, no
         * other callers can incr the refcount
         */
        /* Don't accidentally grab ourselves, or bail if we can't quicklock */
        if (hv == cur_hv || (hold_lock = item_trylock(hv)) == NULL)
            continue;
        /* Now see if the item is refcount locked */
        if (refcount_incr(&search->refcount) != 2) {{//引用数，还有其他线程在引用，不能霸占这个item
            /* Avoid pathological case with ref'ed items in tail */
            //刷新这个item的访问时间以及在LRU队列中的位置
            do_item_update_nolock(search);
            tries_lrutail_reflocked--;
            tries++;
            refcount_decr(&search->refcount);//此时引用数>=2
            itemstats[id].lrutail_reflocked++;
            /* Old rare bug could cause a refcount leak. We haven't seen
             * it in years, but we leave this code in to prevent failures
             * just in case */
            if (settings.tail_repair_time &&//启动了检测
                    search->time + settings.tail_repair_time < current_time) {//在这个时间距离内都没有访问过
                itemstats[id].tailrepairs++;
                search->refcount = 1;//释放线程对item的引用
                do_item_unlink_nolock(search, hv);//这里会把item从哈希表和LRU队列中删除并将引用计数减一 
            }
            if (hold_lock)
                item_trylock_unlock(hold_lock);

            if (tries_lrutail_reflocked < 1)
                break;

            continue;
        }


        /* Expired or flushed */
        //search指向的item的refcount等于2，这说明此时这个item除了本worker
        //线程外，没有其他任何worker线程索引其。可以放心释放并重用这个item 
        //因为这个循环是从lru链表的后面开始遍历的。所以一开始search就指向
        //了最不常用的item，如果这个item都没有过期。那么其他的比其更常用
        //的item就不要删除了(即使它们过期了)。此时只能向slabs申请内存
        if ((search->exptime != 0 && search->exptime < current_time)
            || (search->time <= oldest_live && oldest_live <= current_time)) {

            itemstats[id].reclaimed++;
            if ((search->it_flags & ITEM_FETCHED) == 0) {
                itemstats[id].expired_unfetched++;
            }
            //search指向的item是一个过期失效的item，可以使用之
            it = search;
            //重新计算一下这个slabclass_t分配出去的内存大小 
            //直接霸占旧的item就需要重新计算
            slabs_adjust_mem_requested(it->slabs_clsid, ITEM_ntotal(it), ntotal);
            do_item_unlink_nolock(it, hv);//从哈希表和lru链表中删除
            /* Initialize the item block: */
            it->slabs_clsid = 0;
        } else if ((it = slabs_alloc(ntotal, id)) == NULL) {//从slab分配器中申请内存
            //此刻，过期失效的item没有找到，申请内存又失败了。看来只能使用
            //LRU淘汰一个item(即使这个item并没有过期失效)
            tried_alloc = 1;
            if (settings.evict_to_free == 0) {//设置了不进行LRU淘汰item
                //此时只能向客户端回复错误了
                itemstats[id].outofmemory++;
            } else {
                itemstats[id].evicted++;//增加被踢的item数
                itemstats[id].evicted_time = current_time - search->time;
                //即使一个item的exptime成员设置为永不超时(0)，还是会被踢的
                if (search->exptime != 0)
                    itemstats[id].evicted_nonzero++;
                if ((search->it_flags & ITEM_FETCHED) == 0) {
                    itemstats[id].evicted_unfetched++;
                }
                //即使一个item的exptime成员设置为永不超时(0)，还是会被踢的
                it = search;
                //重新计算一下这个slabclass_t分配出去的内存大小
                //直接霸占旧的item就需要重新计算
                slabs_adjust_mem_requested(it->slabs_clsid, ITEM_ntotal(it), ntotal);
                do_item_unlink_nolock(it, hv);//从哈希表和lru链表中删除
                /* Initialize the item block: */
                it->slabs_clsid = 0;

                /* If we've just evicted an item, and the automover is set to
                 * angry bird mode, attempt to rip memory into this slab class.
                 * TODO: Move valid object detection into a function, and on a
                 * "successful" memory pull, look behind and see if the next alloc
                 * would be an eviction. Then kick off the slab mover before the
                 * eviction happens.
                 */
                //一旦发现有item被踢，那么就启动内存页重分配操作
                //这个太频繁了，不推荐
                if (settings.slab_automove == 2)
                    //内存页重分配处理函数
                    slabs_reassign(-1, id);
            }
        }

        //引用计数减一。此时该item已经没有任何worker线程索引其，
        //并且哈希表也不再索引其
        refcount_decr(&search->refcount);
        /* If hash values were equal, we don't grab a second lock */
        if (hold_lock)
            item_trylock_unlock(hold_lock);
        break;
    }

    if (!tried_alloc && (tries == 0 || search == NULL))
        it = slabs_alloc(ntotal, id);

    if (it == NULL) {
        itemstats[id].outofmemory++;
        mutex_unlock(&cache_lock);
        return NULL;
    }

    assert(it->slabs_clsid == 0);
    assert(it != heads[id]);

    /* Item initialization can happen outside of the lock; the item's already
     * been removed from the slab LRU.
     */
    it->refcount = 1;     /* the caller will have a reference */
    mutex_unlock(&cache_lock);
    it->next = it->prev = it->h_next = 0;
    it->slabs_clsid = id;

    DEBUG_REFCNT(it, '*');
    it->it_flags = settings.use_cas ? ITEM_CAS : 0;
    it->nkey = nkey;
    it->nbytes = nbytes;
    memcpy(ITEM_key(it), key, nkey);
    it->exptime = exptime;
    memcpy(ITEM_suffix(it), suffix, (size_t)nsuffix);
    it->nsuffix = nsuffix;
    return it;
}

void item_free(item *it) {
    size_t ntotal = ITEM_ntotal(it);
    unsigned int clsid;
    assert((it->it_flags & ITEM_LINKED) == 0);
    assert(it != heads[it->slabs_clsid]);
    assert(it != tails[it->slabs_clsid]);
    assert(it->refcount == 0);

    /* so slab size changer can tell later if item is already free or not */
    clsid = it->slabs_clsid;
    it->slabs_clsid = 0;
    DEBUG_REFCNT(it, 'F');
    slabs_free(it, ntotal, clsid);
}

/**
 * Returns true if an item will fit in the cache (its size does not exceed
 * the maximum for a cache entry.)
 */
bool item_size_ok(const size_t nkey, const int flags, const int nbytes) {
    char prefix[40];
    uint8_t nsuffix;

    size_t ntotal = item_make_header(nkey + 1, flags, nbytes,
                                     prefix, &nsuffix);
    if (settings.use_cas) {
        ntotal += sizeof(uint64_t);
    }

    return slabs_clsid(ntotal) != 0;
}

//将item插入到LRU队列的头部
static void item_link_q(item *it) { /* item is the new head */
    item **head, **tail;
    assert(it->slabs_clsid < LARGEST_ID);
    assert((it->it_flags & ITEM_SLABBED) == 0);

    head = &heads[it->slabs_clsid];
    tail = &tails[it->slabs_clsid];
    assert(it != *head);
    assert((*head && *tail) || (*head == 0 && *tail == 0));

    //头插法插入该item
    it->prev = 0;
    it->next = *head;
    if (it->next) it->next->prev = it;
    *head = it;//该item作为对应链表的第一个节点

    //如果该item是对应id上的第一个item，那么还会被认为是该id链上的最后一个item
    //因为在head那里使用头插法，所以第一个插入的item，到了后面确实成了最后一个item
    if (*tail == 0) *tail = it;
    sizes[it->slabs_clsid]++;//个数加一
    return;
}


//将it从对应的LRU队列中删除
static void item_unlink_q(item *it) {
    item **head, **tail;
    assert(it->slabs_clsid < LARGEST_ID);
    head = &heads[it->slabs_clsid];
    tail = &tails[it->slabs_clsid];

    if (*head == it) {//链表上的第一个节点
        assert(it->prev == 0);
        *head = it->next;
    }
    if (*tail == it) {//链表上的最后一个节点
        assert(it->next == 0);
        *tail = it->prev;
    }
    assert(it->next != it);
    assert(it->prev != it);

    //链表上的最后一个节点
    if (it->next) it->next->prev = it->prev;
    if (it->prev) it->prev->next = it->next;
    sizes[it->slabs_clsid]--;//个数减一
    return;
}


//将item插入到哈希表和LRU队列中，插入到哈希表需要哈希值hv
int do_item_link(item *it, const uint32_t hv) {
    MEMCACHED_ITEM_LINK(ITEM_key(it), it->nkey, it->nbytes);

    //确保这个item已经从slab分配出去并且还没插入到LRU队列中
    assert((it->it_flags & (ITEM_LINKED|ITEM_SLABBED)) == 0);

    //当哈希表不在为扩展而迁移数据时，就往哈希表插入item
    //当哈希表在迁移数据时，会占有这个锁。
    mutex_lock(&cache_lock);
    it->it_flags |= ITEM_LINKED;//加入 已link标志
    it->time = current_time;

    STATS_LOCK();
    stats.curr_bytes += ITEM_ntotal(it);
    stats.curr_items += 1;
    stats.total_items += 1;
    STATS_UNLOCK();

    /* Allocate a new CAS ID on link. */
    ITEM_set_cas(it, (settings.use_cas) ? get_cas_id() : 0);
    assoc_insert(it, hv);//将这个item插入到哈希表
    item_link_q(it);//将这个item插入到链表中
    refcount_incr(&it->refcount);//引用计数加一
    mutex_unlock(&cache_lock);

    return 1;
}

//从哈希表删除，所以需要哈希值hv
void do_item_unlink(item *it, const uint32_t hv) {
    MEMCACHED_ITEM_UNLINK(ITEM_key(it), it->nkey, it->nbytes);
    mutex_lock(&cache_lock);
    if ((it->it_flags & ITEM_LINKED) != 0) {
        it->it_flags &= ~ITEM_LINKED;//减去已link标志 
        STATS_LOCK();
        stats.curr_bytes -= ITEM_ntotal(it);
        stats.curr_items -= 1;
        STATS_UNLOCK();
        assoc_delete(ITEM_key(it), it->nkey, hv);//将这个item从哈希表中删除
        item_unlink_q(it);//从链表中删除该item
        do_item_remove(it);//向slab归还这个item
    }
    mutex_unlock(&cache_lock);
}

/* FIXME: Is it necessary to keep this copy/pasted code? */
void do_item_unlink_nolock(item *it, const uint32_t hv) {
    MEMCACHED_ITEM_UNLINK(ITEM_key(it), it->nkey, it->nbytes);
    if ((it->it_flags & ITEM_LINKED) != 0) {
        it->it_flags &= ~ITEM_LINKED;
        STATS_LOCK();
        stats.curr_bytes -= ITEM_ntotal(it);
        stats.curr_items -= 1;
        STATS_UNLOCK();
        assoc_delete(ITEM_key(it), it->nkey, hv);
        item_unlink_q(it);
        do_item_remove(it);
    }
}

//----------------------------------->>>>>>
//可以看到，这是因为减少一个item的引用数可能要删除这个item。为什么呢？考虑这样的情景，线程A因为要读一个item而增加了这个item的引用计数，此时线程B进来了，它要删除这个item。这个删除命令是肯定会执行的，而不是说这个item被别的线程引用了就不执行删除命令。但又肯定不能马上删除，因为线程A还在使用这个item，此时memcached就采用延迟删除的做法。线程B执行删除命令时减多一次item的引用数，使得当线程A释放自己对item的引用后，item的引用数变成0。此时item就被释放了(归还给slab分配器)。
// 
//         有一点要注意：当一个item插入到哈希表和LRU队列后，那么这个item就被哈希表和LRU队列所引用了。此时，如果没有其他线程在引用这个item的话，那么这个item的引用数为1(哈希表和LRU队列看作一个引用)。所以一个worker线程要删除一个item(当然在删除前这个worker线程要占有这个item)，那么需要减少两次item的引用数，一次是减少哈希表和LRU队列的引用，另外一次是减少自己的引用。所以经常能在代码中看到删除一个item需要调用函数do_item_unlink (it, hv)和do_item_remove(it)这两个函数。
//<<<<<<<--------------------------------




//在使用do_item_remove函数向slab归还item时，
//会先测试这个item的引用数是否等于0。引用数
//可以简单理解为有没有worker线程在使用这个item
void do_item_remove(item *it) {
    MEMCACHED_ITEM_REMOVE(ITEM_key(it), it->nkey, it->nbytes);
    assert((it->it_flags & ITEM_SLABBED) == 0);
    assert(it->refcount > 0);

    if (refcount_decr(&it->refcount) == 0) {//引用计数等于0的时候归还
        item_free(it);//归还该item给slab.归还该item给slab分配器
    }
}

/* Copy/paste to avoid adding two extra branches for all common calls, since
 * _nolock is only used in an uncommon case. */
void do_item_update_nolock(item *it) {
    MEMCACHED_ITEM_UPDATE(ITEM_key(it), it->nkey, it->nbytes);
    if (it->time < current_time - ITEM_UPDATE_INTERVAL) {
        assert((it->it_flags & ITEM_SLABBED) == 0);

        if ((it->it_flags & ITEM_LINKED) != 0) {
            item_unlink_q(it);
            it->time = current_time;
            item_link_q(it);
        }
    }
}



// 为什么要把item插入到LRU队列头部呢？当然实现简单是其中一个原因。但更重要的是这是一个LRU队列！！还记得操作系统里面的LRU吧。这是一种淘汰机制。在LRU队列中，排得越靠后就认为是越少使用的item，此时被淘汰的几率就越大。所以新鲜item(访问时间新)，要排在不那么新鲜item的前面，所以插入LRU队列的头部是不二选择。下面的do_item_update函数佐证了这一点。do_item_update函数是先把旧的item从LRU队列中删除，然后再插入到LRU队列中(此时它在LRU队列中排得最前)。除了更新item在队列中的位置外，还会更新item的time成员，该成员指明上一次访问的时间(绝对时间)。如果不是为了LRU，那么do_item_update函数最简单的实现就是直接更新time成员即可。
void do_item_update(item *it) {
    MEMCACHED_ITEM_UPDATE(ITEM_key(it), it->nkey, it->nbytes);




    //下面的代码可以看到update操作是耗时的。如果这个item频繁被访问，  
    //那么会导致过多的update，过多的一系列费时操作。此时更新间隔就应运而生  
    //了。如果上一次的访问时间(也可以说是update时间)距离现在(current_time)  
    //还在更新间隔内的，就不更新。超出了才更新
    if (it->time < current_time - ITEM_UPDATE_INTERVAL) {
        assert((it->it_flags & ITEM_SLABBED) == 0);

        //o_item_update函数耗时还是会有一定的耗时，因为要抢占cache_lock锁。
        //如果频繁调用do_item_update函数性能将下降很多。
        //于是memcached就是使用了更新间隔
        mutex_lock(&cache_lock);
        if ((it->it_flags & ITEM_LINKED) != 0) {
            item_unlink_q(it);//从LRU队列中删除
            it->time = current_time;//更新访问时间
            item_link_q(it);//插入到LRU队列的头部
        }
        mutex_unlock(&cache_lock);
    }
}

int do_item_replace(item *it, item *new_it, const uint32_t hv) {
    MEMCACHED_ITEM_REPLACE(ITEM_key(it), it->nkey, it->nbytes,
                           ITEM_key(new_it), new_it->nkey, new_it->nbytes);
    assert((it->it_flags & ITEM_SLABBED) == 0);

    do_item_unlink(it, hv);
    return do_item_link(new_it, hv);
}

/*@null@*/
char *do_item_cachedump(const unsigned int slabs_clsid, const unsigned int limit, unsigned int *bytes) {
    unsigned int memlimit = 2 * 1024 * 1024;   /* 2MB max response size */
    char *buffer;
    unsigned int bufcurr;
    item *it;
    unsigned int len;
    unsigned int shown = 0;
    char key_temp[KEY_MAX_LENGTH + 1];
    char temp[512];

    it = heads[slabs_clsid];

    buffer = malloc((size_t)memlimit);
    if (buffer == 0) return NULL;
    bufcurr = 0;

    while (it != NULL && (limit == 0 || shown < limit)) {
        assert(it->nkey <= KEY_MAX_LENGTH);
        if (it->nbytes == 0 && it->nkey == 0) {
            it = it->next;
            continue;
        }
        /* Copy the key since it may not be null-terminated in the struct */
        strncpy(key_temp, ITEM_key(it), it->nkey);
        key_temp[it->nkey] = 0x00; /* terminate */
        len = snprintf(temp, sizeof(temp), "ITEM %s [%d b; %lu s]\r\n",
                       key_temp, it->nbytes - 2,
                       (unsigned long)it->exptime + process_started);
        if (bufcurr + len + 6 > memlimit)  /* 6 is END\r\n\0 */
            break;
        memcpy(buffer + bufcurr, temp, len);
        bufcurr += len;
        shown++;
        it = it->next;
    }

    memcpy(buffer + bufcurr, "END\r\n", 6);
    bufcurr += 5;

    *bytes = bufcurr;
    return buffer;
}

void item_stats_evictions(uint64_t *evicted) {
    int i;
    mutex_lock(&cache_lock);
    for (i = 0; i < LARGEST_ID; i++) {
        evicted[i] = itemstats[i].evicted;
    }
    mutex_unlock(&cache_lock);
}

void do_item_stats_totals(ADD_STAT add_stats, void *c) {
    itemstats_t totals;
    memset(&totals, 0, sizeof(itemstats_t));
    int i;
    for (i = 0; i < LARGEST_ID; i++) {
        totals.expired_unfetched += itemstats[i].expired_unfetched;
        totals.evicted_unfetched += itemstats[i].evicted_unfetched;
        totals.evicted += itemstats[i].evicted;
        totals.reclaimed += itemstats[i].reclaimed;
        totals.crawler_reclaimed += itemstats[i].crawler_reclaimed;
        totals.lrutail_reflocked += itemstats[i].lrutail_reflocked;
    }
    APPEND_STAT("expired_unfetched", "%llu",
                (unsigned long long)totals.expired_unfetched);
    APPEND_STAT("evicted_unfetched", "%llu",
                (unsigned long long)totals.evicted_unfetched);
    APPEND_STAT("evictions", "%llu",
                (unsigned long long)totals.evicted);
    APPEND_STAT("reclaimed", "%llu",
                (unsigned long long)totals.reclaimed);
    APPEND_STAT("crawler_reclaimed", "%llu",
                (unsigned long long)totals.crawler_reclaimed);
    APPEND_STAT("lrutail_reflocked", "%llu",
                (unsigned long long)totals.lrutail_reflocked);
}

void do_item_stats(ADD_STAT add_stats, void *c) {
    int i;
    for (i = 0; i < LARGEST_ID; i++) {
        if (tails[i] != NULL) {
            const char *fmt = "items:%d:%s";
            char key_str[STAT_KEY_LEN];
            char val_str[STAT_VAL_LEN];
            int klen = 0, vlen = 0;
            if (tails[i] == NULL) {
                /* We removed all of the items in this slab class */
                continue;
            }
            APPEND_NUM_FMT_STAT(fmt, i, "number", "%u", sizes[i]);
            APPEND_NUM_FMT_STAT(fmt, i, "age", "%u", current_time - tails[i]->time);
            APPEND_NUM_FMT_STAT(fmt, i, "evicted",
                                "%llu", (unsigned long long)itemstats[i].evicted);
            APPEND_NUM_FMT_STAT(fmt, i, "evicted_nonzero",
                                "%llu", (unsigned long long)itemstats[i].evicted_nonzero);
            APPEND_NUM_FMT_STAT(fmt, i, "evicted_time",
                                "%u", itemstats[i].evicted_time);
            APPEND_NUM_FMT_STAT(fmt, i, "outofmemory",
                                "%llu", (unsigned long long)itemstats[i].outofmemory);
            APPEND_NUM_FMT_STAT(fmt, i, "tailrepairs",
                                "%llu", (unsigned long long)itemstats[i].tailrepairs);
            APPEND_NUM_FMT_STAT(fmt, i, "reclaimed",
                                "%llu", (unsigned long long)itemstats[i].reclaimed);
            APPEND_NUM_FMT_STAT(fmt, i, "expired_unfetched",
                                "%llu", (unsigned long long)itemstats[i].expired_unfetched);
            APPEND_NUM_FMT_STAT(fmt, i, "evicted_unfetched",
                                "%llu", (unsigned long long)itemstats[i].evicted_unfetched);
            APPEND_NUM_FMT_STAT(fmt, i, "crawler_reclaimed",
                                "%llu", (unsigned long long)itemstats[i].crawler_reclaimed);
            APPEND_NUM_FMT_STAT(fmt, i, "lrutail_reflocked",
                                "%llu", (unsigned long long)itemstats[i].lrutail_reflocked);
        }
    }

    /* getting here means both ascii and binary terminators fit */
    add_stats(NULL, 0, NULL, 0, c);
}

/** dumps out a list of objects of each size, with granularity of 32 bytes */
/*@null@*/
void do_item_stats_sizes(ADD_STAT add_stats, void *c) {

    /* max 1MB object, divided into 32 bytes size buckets */
    const int num_buckets = 32768;
    unsigned int *histogram = calloc(num_buckets, sizeof(int));

    if (histogram != NULL) {
        int i;

        /* build the histogram */
        for (i = 0; i < LARGEST_ID; i++) {
            item *iter = heads[i];
            while (iter) {
                int ntotal = ITEM_ntotal(iter);
                int bucket = ntotal / 32;
                if ((ntotal % 32) != 0) bucket++;
                if (bucket < num_buckets) histogram[bucket]++;
                iter = iter->next;
            }
        }

        /* write the buffer */
        for (i = 0; i < num_buckets; i++) {
            if (histogram[i] != 0) {
                char key[8];
                snprintf(key, sizeof(key), "%d", i * 32);
                APPEND_STAT(key, "%u", histogram[i]);
            }
        }
        free(histogram);
    }
    add_stats(NULL, 0, NULL, 0, c);
}


/** wrapper around assoc_find which does the lazy expiration logic */
//调用do_item_get的函数都已经加上了item_lock(hv)段级别锁或者全局锁
item *do_item_get(const char *key, const size_t nkey, const uint32_t hv) {
    //mutex_lock(&cache_lock);
    item *it = assoc_find(key, nkey, hv);//assoc_find函数内部没有加锁
    if (it != NULL) {//找到了，此时item的引用计数至少为1
        refcount_incr(&it->refcount);//线程安全地自增一
        /* Optimization for slab reassignment. prevents popular items from
         * jamming in busy wait. Can only do this here to satisfy lock order
         * of item_lock, cache_lock, slabs_lock. */
        if (slab_rebalance_signal &&
            ((void *)it >= slab_rebal.slab_start && (void *)it < slab_rebal.slab_end)) {

            //这个item刚好在要移动的内存页里面。此时不能返回这个item 
            //worker线程要负责把这个item从哈希表和LRU队列中删除这个item，
            //避免后面有其他worker线程又访问这个不能使用的item
            do_item_unlink(it, hv);
            do_item_remove(it);
            it = NULL;
        }
    }
    //mutex_unlock(&cache_lock);
    int was_found = 0;

    if (settings.verbose > 2) {
        int ii;
        if (it == NULL) {
            fprintf(stderr, "> NOT FOUND ");
        } else {
            fprintf(stderr, "> FOUND KEY ");
            was_found++;
        }
        for (ii = 0; ii < nkey; ++ii) {
            fprintf(stderr, "%c", key[ii]);
        }
    }

    if (it != NULL) {

        /*
         *settings.oldest_live初始化值为0  
         *检测用户是否使用过flush_all命令，删除所有item。  
         *it->time <= settings.oldest_live就说明用户在使用flush_all命令的时候
         *就已经存在该item了。那么该item是要删除的。  
         *flush_all命令可以有参数，用来设定在未来的某个时刻把所有的item都设置
         *为过期失效，此时settings.oldest_live是一个比worker接收到flush_all  
         *命令的那一刻大的时间,所以要判断settings.oldest_live <= current_time
         */
        if (settings.oldest_live != 0 && settings.oldest_live <= current_time &&
            it->time <= settings.oldest_live) {
            do_item_unlink(it, hv);
            do_item_remove(it);
            it = NULL;
            if (was_found) {
                fprintf(stderr, " -nuked by flush");
            }
        } else if (it->exptime != 0 && it->exptime <= current_time) {//该item已经过期失效了
            do_item_unlink(it, hv);//引用数会减一
            do_item_remove(it);//引用数减一,如果引用数等于0，就删除
            it = NULL;
            if (was_found) {
                fprintf(stderr, " -nuked by expire");
            }
        } else {
            it->it_flags |= ITEM_FETCHED;
            DEBUG_REFCNT(it, '+');
        }
    }

    if (settings.verbose > 2)
        fprintf(stderr, "\n");

    return it;
}

item *do_item_touch(const char *key, size_t nkey, uint32_t exptime,
                    const uint32_t hv) {
    item *it = do_item_get(key, nkey, hv);
    if (it != NULL) {
        it->exptime = exptime;
    }
    return it;
}

//--------------------------------------------------->>>>>
//过期失效是用户flush_all命令设置的。flush_all会将所有item都变成过期失效。所有item是指哪些item？因为多个客户端会不断地往memcached插入item，所以必须要明白所有item是指哪些。是以worker线程接收到这个命令那一刻为界?还是以删除那一刻为界？
//        当worker线程接收到flush_all命令后，会用全局变量settings的oldest_live成员存储接收到这个命令那一刻的时间(准确地说，是worker线程解析得知这是一个flush_all命令那一刻再减一)，代码为settings.oldest_live =current_time - 1;然后调用item_flush_expired函数锁上cache_lock，然后调用do_item_flush_expired函数完成工作
//<<<<<<<-------------------------------------------------



//+++++++++++++++++++++++++++++++++++++++++++++++++++++>>>>>
//        flush_all命令是可以有时间参数的。这个时间和其他时间一样取值范围是 1到REALTIME_MAXDELTA(30天)。如果命令为flush_all 100，那么99秒后所有的item失效。此时settings.oldest_live的值为current_time+100-1，do_item_flush_expired函数也没有什么用了(总不会被抢占CPU99秒吧)。也正是这个原因，需要在do_item_get里面，加入settings.oldest_live<= current_time这个判断，防止过早删除了item。
//        这里明显有一个bug。假如客户端A向服务器提交了flush_all10命令。过了5秒后，客户端B向服务器提交命令flush_all100。那么客户端A的命令将失效，没有起到任何作用
//<<<<<<<<<<<<++++++++++++++++++++++++++++++++++++++++++++++
/* expires items that are more recent than the oldest_live setting. */
void do_item_flush_expired(void) {
    int i;
    item *iter, *next;
    if (settings.oldest_live == 0)
        return;
    for (i = 0; i < LARGEST_ID; i++) {
        /* The LRU is sorted in decreasing time order, and an item's timestamp
         * is never newer than its last access time, so we only need to walk
         * back until we hit an item older than the oldest_live time.
         * The oldest_live checking will auto-expire the remaining items.
         */
        for (iter = heads[i]; iter != NULL; iter = next) {
            /* iter->time of 0 are magic objects. */

            //iter->time == 0的是lru爬虫item，直接忽略  
            //一般情况下iter->time是小于settings.oldest_live的。但在这种
            //情况下就有可能出现iter->time >= settings.oldest_live :  
            //worker1接收到flush_all命令，并给settings.oldest_live
            //赋值为current_time-1。worker1线程还没来得及调用
            //item_flush_expired函数，就被worker2抢占了cpu，然后worker2
            //往lru队列插入了一个item。这个item的time 成员就会满足
            //iter->time >= settings.oldest_live 

            if (iter->time != 0 && iter->time >= settings.oldest_live) {
                next = iter->next;
                if ((iter->it_flags & ITEM_SLABBED) == 0) {
                    //虽然调用的是nolock,但本函数的调用者item_flush_expired
                    //已经锁上了cache_lock，才调用本函数的
                    do_item_unlink_nolock(iter, hash(ITEM_key(iter), iter->nkey));
                }
            } else {
                /* We've hit the first old item. Continue to the next queue. */             
                //因为lru队列里面的item是根据time降序排序的，所以当存在一
                //个item的time成员小于settings.oldest_live,剩下的item都不
                //需要再比较了
                break;
            }
        }
    }
}

static void crawler_link_q(item *it) { /* item is the new tail */
    item **head, **tail;
    assert(it->slabs_clsid < LARGEST_ID);
    assert(it->it_flags == 1);
    assert(it->nbytes == 0);

    head = &heads[it->slabs_clsid];
    tail = &tails[it->slabs_clsid];
    assert(*tail != 0);
    assert(it != *tail);
    assert((*head && *tail) || (*head == 0 && *tail == 0));
    it->prev = *tail;
    it->next = 0;
    if (it->prev) {
        assert(it->prev->next == 0);
        it->prev->next = it;
    }
    *tail = it;
    if (*head == 0) *head = it;
    return;
}

static void crawler_unlink_q(item *it) {
    item **head, **tail;
    assert(it->slabs_clsid < LARGEST_ID);
    head = &heads[it->slabs_clsid];
    tail = &tails[it->slabs_clsid];

    if (*head == it) {
        assert(it->prev == 0);
        *head = it->next;
    }
    if (*tail == it) {
        assert(it->next == 0);
        *tail = it->prev;
    }
    assert(it->next != it);
    assert(it->prev != it);

    if (it->next) it->next->prev = it->prev;
    if (it->prev) it->prev->next = it->next;
    return;
}

/* This is too convoluted, but it's a difficult shuffle. Try to rewrite it
 * more clearly. */
static item *crawler_crawl_q(item *it) {
    item **head, **tail;
    assert(it->it_flags == 1);
    assert(it->nbytes == 0);
    assert(it->slabs_clsid < LARGEST_ID);
    head = &heads[it->slabs_clsid];
    tail = &tails[it->slabs_clsid];

    /* We've hit the head, pop off */
    if (it->prev == 0) {
        assert(*head == it);
        if (it->next) {
            *head = it->next;
            assert(it->next->prev == it);
            it->next->prev = 0;
        }
        return NULL; /* Done */
    }

    /* Swing ourselves in front of the next item */
    /* NB: If there is a prev, we can't be the head */
    assert(it->prev != it);
    if (it->prev) {
        if (*head == it->prev) {
            /* Prev was the head, now we're the head */
            *head = it;
        }
        if (*tail == it) {
            /* We are the tail, now they are the tail */
            *tail = it->prev;
        }
        assert(it->next != it);
        if (it->next) {
            assert(it->prev->next == it);
            it->prev->next = it->next;
            it->next->prev = it->prev;
        } else {
            /* Tail. Move this above? */
            it->prev->next = 0;
        }
        /* prev->prev's next is it->prev */
        it->next = it->prev;
        it->prev = it->next->prev;
        it->next->prev = it;
        /* New it->prev now, if we're not at the head. */
        if (it->prev) {
            it->prev->next = it;
        }
    }
    assert(it->next != it);
    assert(it->prev != it);

    return it->next; /* success */
}

/* I pulled this out to make the main thread clearer, but it reaches into the
 * main thread's values too much. Should rethink again.
 */
//如果这个item过期失效了，那么就删除其
static void item_crawler_evaluate(item *search, uint32_t hv, int i) {
    rel_time_t oldest_live = settings.oldest_live;

    //这个item的exptime时间戳到了，已经过期失效了
    if ((search->exptime != 0 && search->exptime < current_time)
            //因为客户端发送flush_all命令，导致这个item失效了
        || (search->time <= oldest_live && oldest_live <= current_time)) {
        itemstats[i].crawler_reclaimed++;

        if (settings.verbose > 1) {
            int ii;
            char *key = ITEM_key(search);
            fprintf(stderr, "LRU crawler found an expired item (flags: %d, slab: %d): ",
                search->it_flags, search->slabs_clsid);
            for (ii = 0; ii < search->nkey; ++ii) {
                fprintf(stderr, "%c", key[ii]);
            }
            fprintf(stderr, "\n");
        }
        if ((search->it_flags & ITEM_FETCHED) == 0) {
            itemstats[i].expired_unfetched++;
        }
        //将item从LRU队列中删除
        do_item_unlink_nolock(search, hv);
        do_item_remove(search);
        assert(search->slabs_clsid == 0);
    } else {
        refcount_decr(&search->refcount);
    }
}

static void *item_crawler_thread(void *arg) {
    int i;

    pthread_mutex_lock(&lru_crawler_lock);
    if (settings.verbose > 2)
        fprintf(stderr, "Starting LRU crawler background thread\n");
    while (do_run_lru_crawler_thread) {
    //lru_crawler_crawl函数和stop_item_crawler_thread函数会signal这个条件变量
    pthread_cond_wait(&lru_crawler_cond, &lru_crawler_lock);

    while (crawler_count) {//crawler_count表明要处理多少个LRU队列
        item *search = NULL;
        void *hold_lock = NULL;

        for (i = 0; i < LARGEST_ID; i++) {
            if (crawlers[i].it_flags != 1) {
                continue;
            }
            pthread_mutex_lock(&cache_lock);
            //返回crawlers[i]的前驱节点,并交换crawlers[i]和前驱节点的位置
            search = crawler_crawl_q((item *)&crawlers[i]);
            if (search == NULL ||//crawlers[i]是头节点，没有前驱节点
                //remaining的值为settings.lru_crawler_tocrawl。每次启动lru 
                //爬虫线程，检查每一个lru队列的多少个item。
                (crawlers[i].remaining && --crawlers[i].remaining < 1)) {
                if (settings.verbose > 2)
                    fprintf(stderr, "Nothing left to crawl for %d\n", i);

                //检查了足够多次，退出检查这个lru队列
                crawlers[i].it_flags = 0;
                crawler_count--;//清理完一个LRU队列,任务数减一
                crawler_unlink_q((item *)&crawlers[i]);//将这个伪item从LRU队列中删除
                pthread_mutex_unlock(&cache_lock);
                continue;
            }
            uint32_t hv = hash(ITEM_key(search), search->nkey);
            /* Attempt to hash item lock the "search" item. If locked, no
             * other callers can incr the refcount
             */
            //尝试锁住控制这个item的哈希表段级别锁
            if ((hold_lock = item_trylock(hv)) == NULL) {
                pthread_mutex_unlock(&cache_lock);
                continue;
            }
            /* Now see if the item is refcount locked */
            //此时有其他worker线程在引用这个item
            if (refcount_incr(&search->refcount) != 2) {
                refcount_decr(&search->refcount);//lru爬虫线程放弃引用该item
                if (hold_lock)
                    item_trylock_unlock(hold_lock);
                pthread_mutex_unlock(&cache_lock);
                continue;
            }

            /* Frees the item or decrements the refcount. */
            /* Interface for this could improve: do the free/decr here
             * instead? */
            //如果这个item过期失效了，那么就删除这个item
            item_crawler_evaluate(search, hv, i);

            if (hold_lock)
                item_trylock_unlock(hold_lock);
            pthread_mutex_unlock(&cache_lock);

            //lru爬虫不能不间断地爬lru队列，这样会妨碍worker线程的正常业务
            //所以需要挂起lru爬虫线程一段时间。在默认设置中，会休眠100微秒
            if (settings.lru_crawler_sleep)
                usleep(settings.lru_crawler_sleep);//微秒级
        }
    }
    if (settings.verbose > 2)
        fprintf(stderr, "LRU crawler thread sleeping\n");
    STATS_LOCK();
    stats.lru_crawler_running = false;
    STATS_UNLOCK();
    }
    pthread_mutex_unlock(&lru_crawler_lock);
    if (settings.verbose > 2)
        fprintf(stderr, "LRU crawler thread stopping\n");

    return NULL;
}

static pthread_t item_crawler_tid;

//worker线程在接收到"lru_crawler disable"命令会执行这个函数
int stop_item_crawler_thread(void) {
    int ret;
    pthread_mutex_lock(&lru_crawler_lock);
    do_run_lru_crawler_thread = 0;//停止LRU线程
    pthread_cond_signal(&lru_crawler_cond);
    pthread_mutex_unlock(&lru_crawler_lock);
    if ((ret = pthread_join(item_crawler_tid, NULL)) != 0) {
        fprintf(stderr, "Failed to stop LRU crawler thread: %s\n", strerror(ret));
        return -1;
    }
    settings.lru_crawler = false;
    return 0;
}

//worker线程接收到"lru_crawler enable"命令后会调用本函数
///启动memcached时如果有-o lru_crawler参数也是会调用本函数
int start_item_crawler_thread(void) {
    int ret;

    //在stop_item_crawler_thread函数可以看到pthread_join函数
    //在pthread_join返回后，才会把settings.lru_crawler设置为false
    //所以不会出现同时出现两个crawler线程
    if (settings.lru_crawler)
        return -1;
    pthread_mutex_lock(&lru_crawler_lock);
    do_run_lru_crawler_thread = 1;
    settings.lru_crawler = true;

    //创建一个LRU爬虫线程，线程函数为item_crawler_thread。LRU爬虫线程在进入
    //item_crawler_thread函数后，会调用pthread_cond_wait，等待worker线程
    //指定要处理的LRU队列
    if ((ret = pthread_create(&item_crawler_tid, NULL,
        item_crawler_thread, NULL)) != 0) {
        fprintf(stderr, "Can't create LRU crawler thread: %s\n",
            strerror(ret));
        pthread_mutex_unlock(&lru_crawler_lock);
        return -1;
    }
    pthread_mutex_unlock(&lru_crawler_lock);

    return 0;
}

//当客户端使用命令lru_crawler crawl <classid,classid,classid|all>时,
//worker线程就会调用本函数,并将命令的第二个参数作为本函数的参数
enum crawler_result_type lru_crawler_crawl(char *slabs) {
    char *b = NULL;
    uint32_t sid = 0;
    uint8_t tocrawl[POWER_LARGEST];

    //LRU爬虫线程进行清理的时候，会锁上lru_crawler_lock。直到完成所有
    //的清理任务才会解锁。所以客户端的前一个清理任务还没结束前，不能
    ///再提交另外一个清理任务 
    if (pthread_mutex_trylock(&lru_crawler_lock) != 0) {
        return CRAWLER_RUNNING;
    }
    pthread_mutex_lock(&cache_lock);


    //解析命令，如果命令要求对某一个LRU队列进行清理，那么就在tocrawl数组 
    //对应元素赋值1作为标志
    if (strcmp(slabs, "all") == 0) {//处理全部lru队列
        for (sid = 0; sid < LARGEST_ID; sid++) {
            tocrawl[sid] = 1;
        }
    } else {
        for (char *p = strtok_r(slabs, ",", &b);
             p != NULL;
             p = strtok_r(NULL, ",", &b)) {

            //解析出一个个的sid
            if (!safe_strtoul(p, &sid) || sid < POWER_SMALLEST
                    || sid >= POWER_LARGEST) {//sid越界
                pthread_mutex_unlock(&cache_lock);
                pthread_mutex_unlock(&lru_crawler_lock);
                return CRAWLER_BADCLASS;
            }
            tocrawl[sid] = 1;
        }
    }


    //crawlers是一个伪item类型数组。如果用户要清理某一个LRU队列，那么
    //就在这个LRU队列中插入一个伪item
    for (sid = 0; sid < LARGEST_ID; sid++) {
        if (tocrawl[sid] != 0 && tails[sid] != NULL) {
            if (settings.verbose > 2)
                fprintf(stderr, "Kicking LRU crawler off for slab %d\n", sid);
            //对于伪item和真正的item，可以用nkey、time这两个成员的值区别
            crawlers[sid].nbytes = 0;
            crawlers[sid].nkey = 0;
            crawlers[sid].it_flags = 1; /* For a crawler, this means enabled. */
            crawlers[sid].next = 0;
            crawlers[sid].prev = 0;
            crawlers[sid].time = 0;
            crawlers[sid].remaining = settings.lru_crawler_tocrawl;
            crawlers[sid].slabs_clsid = sid;

            //将这个伪item插入到对应的lru队列的尾部
            crawler_link_q((item *)&crawlers[sid]);
            crawler_count++;//要处理的LRU队列数加一
        }
    }
    pthread_mutex_unlock(&cache_lock);
    //有任务了，唤醒LRU爬虫线程，让其执行清理任务
    pthread_cond_signal(&lru_crawler_cond);
    STATS_LOCK();
    stats.lru_crawler_running = true;
    STATS_UNLOCK();
    pthread_mutex_unlock(&lru_crawler_lock);
    return CRAWLER_OK;
}

/* If we hold this lock, crawler can't wake up or move */
void lru_crawler_pause(void) {
    pthread_mutex_lock(&lru_crawler_lock);
}

void lru_crawler_resume(void) {
    pthread_mutex_unlock(&lru_crawler_lock);
}

int init_lru_crawler(void) {//main函数会调用该函数
    if (lru_crawler_initialized == 0) {
        if (pthread_cond_init(&lru_crawler_cond, NULL) != 0) {
            fprintf(stderr, "Can't initialize lru crawler condition\n");
            return -1;
        }
        pthread_mutex_init(&lru_crawler_lock, NULL);
        lru_crawler_initialized = 1;
    }
    return 0;
}
