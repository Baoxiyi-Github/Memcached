/* -*- Mode: C; tab-width: 4; c-basic-offset: 4; indent-tabs-mode: nil -*- */
/*
 * Hash table
 *
 * The hash function used here is by Bob Jenkins, 1996:
 *    <http://burtleburtle.net/bob/hash/doobs.html>
 *       "By Bob Jenkins, 1996.  bob_jenkins@burtleburtle.net.
 *       You may use this code any way you wish, private, educational,
 *       or commercial.  It's free."
 *
 * The rest of the file is licensed under the BSD license.  See LICENSE.
 */

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
#include <assert.h>
#include <pthread.h>

static pthread_cond_t maintenance_cond = PTHREAD_COND_INITIALIZER;
static pthread_mutex_t maintenance_lock = PTHREAD_MUTEX_INITIALIZER;

typedef  unsigned long  int  ub4;   /* unsigned 4-byte quantities */
typedef  unsigned       char ub1;   /* unsigned 1-byte quantities */

/* how many powers of 2's worth of buckets we use */
unsigned int hashpower = HASHPOWER_DEFAULT;

#define hashsize(n) ((ub4)1<<(n))
//hashsize(n)为2的幂，所以hashmask的值的二进制形式就是后面全为1的数。
//这就很像位操作里面的 &,value & hashmask(n)的结果肯定是比hashsize(n)
//小的一个数字.即结果在hash表里面,hashmask(n)也可以称为哈希掩码
#define hashmask(n) (hashsize(n)-1)

/* Main hash table. This is where we look except during expansion. */
//哈希表指针数组
static item** primary_hashtable = 0;

/*
 * Previous hash table. During expansion, we look here for keys that haven't
 * been moved over to the primary yet.
 */
static item** old_hashtable = 0;

/* Number of items in the hash table. */
static unsigned int hash_items = 0;//hash表中item的个数

/* Flag: Are we in the middle of expanding now? */
static bool expanding = false;//标明hash表是否处于扩展状态
static bool started_expanding = false;

/*
 * During expansion we migrate values with bucket granularity; this is how
 * far we've gotten so far. Ranges from 0 .. hashsize(hashpower - 1) - 1.
 */
static unsigned int expand_bucket = 0;//指向待迁移的桶

//默认参数值为0。本函数由main函数调用，参数的默认值为0
void assoc_init(const int hashtable_init) {
    if (hashtable_init) {
        hashpower = hashtable_init;
    }

    //因为哈希表会慢慢增大，所以要使用动态内存分配。哈希表存储的数据是一个  
    //指针，这样更省空间。hashsize(hashpower)就是哈希表的长度了
    primary_hashtable = calloc(hashsize(hashpower), sizeof(void *));
    if (! primary_hashtable) {
        fprintf(stderr, "Failed to init hashtable.\n");
        exit(EXIT_FAILURE);//哈希表是memcached工作的基础，如果失败只能退出运行
    }
    STATS_LOCK();
    stats.hash_power_level = hashpower;
    stats.hash_bytes = hashsize(hashpower) * sizeof(void *);
    STATS_UNLOCK();
}



//由于哈希值只能确定是在哈希表中的哪个桶(bucket)，但一个桶里面是有一条冲突链的  
//此时需要用到具体的键值遍历并一一比较冲突链上的所有节点。虽然key是以'\0'结尾  
//的字符串，但调用strlen还是有点耗时(需要遍历键值字符串)。所以需要另外一个参数  
//nkey指明这个key的长度
item *assoc_find(const char *key, const size_t nkey, const uint32_t hv) {
    item *it;
    unsigned int oldbucket;

    if (expanding &&//正在扩展哈希表
        (oldbucket = (hv & hashmask(hashpower - 1))) >= expand_bucket)//该item还在旧表里面
    {
        it = old_hashtable[oldbucket];
    } else {
        //由哈希值判断这个key是属于那个桶(bucket)的
        it = primary_hashtable[hv & hashmask(hashpower)];
    }

    //到这里，已经确定这个key是属于那个桶的。 遍历对应桶的冲突链即可
    item *ret = NULL;
    int depth = 0;
    while (it) {
        //长度相同的情况下才调用memcmp比较，更高效 
        if ((nkey == it->nkey) && (memcmp(key, ITEM_key(it), nkey) == 0)) {
            ret = it;
            break;
        }
        it = it->h_next;
        ++depth;
    }
    MEMCACHED_ASSOC_FIND(key, nkey, depth);
    return ret;
}

/* returns the address of the item pointer before the key.  if *item == 0,
   the item wasn't found */

//查找item。返回前驱节点的h_next成员地址,如果查找失败那么就返回冲突链中最后  
//一个节点的h_next成员地址。因为最后一个节点的h_next的值为NULL。通过对返回值  
//使用 * 运算符即可知道有没有查找成功。
static item** _hashitem_before (const char *key, const size_t nkey, const uint32_t hv) {
    item **pos;
    unsigned int oldbucket;

    if (expanding &&//正在扩展哈希表
        (oldbucket = (hv & hashmask(hashpower - 1))) >= expand_bucket)
    {
        pos = &old_hashtable[oldbucket];
    } else {
        //找到哈希表中对应的桶位置
        pos = &primary_hashtable[hv & hashmask(hashpower)];
    }
    
    //到这里已经确定了要查找的item是属于哪个表的了，并且也确定了桶位置。遍历对应桶的冲突链即可

    //遍历桶的冲突链查找item
    while (*pos && ((nkey != (*pos)->nkey) || memcmp(key, ITEM_key(*pos), nkey))) {
        pos = &(*pos)->h_next;
    }

    //*pos就可以知道有没有查找成功。如果*pos等于NULL那么查找失败，否则查找成功。
    return pos;
}


//当哈希表中item的数量达到了哈希表表长的1.5倍时，
//那么就会扩展哈希表增大哈希表的表长。memcached
//在插入一个item时会检查当前的item总数是否达到了
//哈希表表长的1.5倍。由于item的哈希值是比较均匀的，
//所以平均来说每个桶的冲突链长度大概就是1.5个节点。
//所以memcached的哈希查找还是很快的。

//assoc_insert函数会调用本函数，当item数量到了哈希表表长的1.5倍才会调用的

//---------------------------->>
    /*
     *为了避免在迁移的时候worker线程增删哈希表，所以要在数据迁移的时候加锁，worker线程抢到了锁才能增删查找哈希表。memcached为了实现快速响应(即worker线程能够快速完成增删查找操作)，就不能让迁移线程占锁太久。但数据迁移本身就是一个耗时的操作，这是一个矛盾。
     *memcached为了解决这个矛盾，就采用了逐步迁移的方法。其做法是，在一个循环里面：加锁-》只进行小部分数据的迁移-》解锁。这样做的效果是：虽然迁移线程会多次抢占锁，但每次占有锁的时间都是很短的，这就增加了worker线程抢到锁的概率，使得worker线程能够快速完成它的操作。一小部分是多少个item呢？前面说到的全局变量hash_bulk_move就指明是多少个桶的item，默认值是1个桶，后面为了方便叙述也就认为hash_bulk_move的值为1。
     *逐步迁移的具体做法是，调用assoc_expand函数申请一个新的更大的哈希表，每次只迁移旧哈希表一个桶的item到新哈希表，迁移完一桶就释放锁。此时就要求有一个旧哈希表和新哈希表。在memcached实现里面，用primary_hashtable表示新表(也有一些博文称之为主表)，old_hashtable表示旧表(副表)。
     */
//<<----------------------------



//迁移线程被创建后就会休眠直到被worker线程唤醒。
//当迁移线程醒来后，就会调用assoc_expand函数扩大哈希表的表长

/* grows the hashtable to the next power of 2. */
static void assoc_expand(void) {
    old_hashtable = primary_hashtable;

    //申请一个新哈希表，并用old_hashtable指向旧哈希表 
    primary_hashtable = calloc(hashsize(hashpower + 1), sizeof(void *));
    if (primary_hashtable) {
        if (settings.verbose > 1)
            fprintf(stderr, "Hash table expansion starting\n");
        hashpower++;
        expanding = true;//标明已经进入扩展状态
        expand_bucket = 0;//从0号桶开始数据迁移
        STATS_LOCK();
        stats.hash_power_level = hashpower;
        stats.hash_bytes += hashsize(hashpower) * sizeof(void *);
        stats.hash_is_expanding = 1;
        STATS_UNLOCK();
    } else {
        primary_hashtable = old_hashtable;
        /* Bad news, but we can keep running. */
    }
}

//assoc_insert函数会调用本函数，当item数量到了哈希表表长的1.5倍才会调用的
static void assoc_start_expand(void) {
    if (started_expanding)
        return;

    started_expanding = true;
    pthread_cond_signal(&maintenance_cond);
}

/* Note: this isn't an assoc_update.  The key must not already exist to call this */
//hv是这个item键值的哈希值
int assoc_insert(item *it, const uint32_t hv) {
    unsigned int oldbucket;

//    assert(assoc_find(ITEM_key(it), it->nkey) == 0);  /* shouldn't have duplicately named things defined */

    //使用头插法 插入一个item
    ///第一次看本函数，直接看else部分
    if (expanding &&//目前处于扩展hash表状态
        (oldbucket = (hv & hashmask(hashpower - 1))) >= expand_bucket)//数据迁移时还没迁移到这个桶
    {
        //插入到旧表
        it->h_next = old_hashtable[oldbucket];
        old_hashtable[oldbucket] = it;
    } else {
        //使用头插法插入哈希表中
        //插入到新表
        it->h_next = primary_hashtable[hv & hashmask(hashpower)];
        primary_hashtable[hv & hashmask(hashpower)] = it;
    }

    hash_items++;//哈希表的item数量加一

    //当hash表的item数量到达了hash表容量的1.5倍时，就会进行扩展
    //当然如果现在正处于扩展状态，是不会再扩展的
    if (! expanding && hash_items > (hashsize(hashpower) * 3) / 2) {
        assoc_start_expand();//唤醒迁移线程，扩展哈希表
    }

    MEMCACHED_ASSOC_INSERT(ITEM_key(it), it->nkey, hash_items);
    return 1;
}

void assoc_delete(const char *key, const size_t nkey, const uint32_t hv) {
    item **before = _hashitem_before(key, nkey, hv);//得到前驱节点的h_next成员地址

    if (*before) {//查找成功
        item *nxt;
        hash_items--;
        /* The DTrace probe cannot be triggered as the last instruction
         * due to possible tail-optimization by the compiler
         */
        MEMCACHED_ASSOC_DELETE(key, nkey, hash_items);
        //因为before是一个二级指针，其值为所查找item的前驱item的h_next成员地址. 
        //所以*before指向的是所查找的item.因为before是一个二级指针，所以  
        //*before作为左值时，可以给h_next成员变量赋值。所以下面三行代码是  
        //使得删除中间的item后，前后的item还能连得起来
        nxt = (*before)->h_next;
        (*before)->h_next = 0;   /* probably pointless, but whatever. */
        *before = nxt;
        return;
    }
    /* Note:  we never actually get here.  the callers don't delete things
       they can't find. */
    assert(*before != 0);
}


static volatile int do_run_maintenance_thread = 1;

#define DEFAULT_HASH_BULK_MOVE 1
int hash_bulk_move = DEFAULT_HASH_BULK_MOVE;

static void *assoc_maintenance_thread(void *arg) {

    mutex_lock(&maintenance_lock);

    //do_run_maintenance_thread是全局变量，初始值为1，在stop_assoc_maintenance_thread
    //函数中会被赋值0，终止迁移线程
    while (do_run_maintenance_thread) {
        int ii = 0;

        /* There is only one expansion thread, so no need to global lock. */
        for (ii = 0; ii < hash_bulk_move && expanding; ++ii) {
            item *it, *next;
            int bucket;
            void *item_lock = NULL;

            /* bucket = hv & hashmask(hashpower) =>the bucket of hash table
             * is the lowest N bits of the hv, and the bucket of item_locks is
             *  also the lowest M bits of hv, and N is greater than M.
             *  So we can process expanding with only one item_lock. cool! */
            //hash_bulk_move用来控制每次迁移，移动多少个桶的item。默认是一个.  
            //如果expanding为true才会进入循环体，所以迁移线程刚创建的时候，并不会进入循环体
            if ((item_lock = item_trylock(expand_bucket))) {
                    //在assoc_expand函数中expand_bucket会被赋值0  
                    //遍历旧哈希表中由expand_bucket指明的桶,将该桶的所有item  
                    //迁移到新哈希表中。
                    for (it = old_hashtable[expand_bucket]; NULL != it; it = next) {
                        next = it->h_next;
                         //重新计算新的哈希值,得到其在新哈希表的位置 
                        bucket = hash(ITEM_key(it), it->nkey) & hashmask(hashpower);
                         //将这个item插入到新哈希表中
                        it->h_next = primary_hashtable[bucket];
                        primary_hashtable[bucket] = it;
                    }

                    //不需要清空旧桶。直接将冲突链的链头赋值为NULL即可
                    old_hashtable[expand_bucket] = NULL;

                    //迁移完一个桶，接着把expand_bucket指向下一个待迁移的桶
                    expand_bucket++;
                    if (expand_bucket == hashsize(hashpower - 1)) {//全部数据迁移完毕
                        expanding = false;//将扩展标志设置为false
                        free(old_hashtable);
                        STATS_LOCK();
                        stats.hash_bytes -= hashsize(hashpower - 1) * sizeof(void *);
                        stats.hash_is_expanding = 0;
                        STATS_UNLOCK();
                        if (settings.verbose > 1)
                            fprintf(stderr, "Hash table expansion done\n");
                    }

            } else {
                usleep(10*1000);
            }

            if (item_lock) {
                //遍历完hash_bulk_move个桶的所有item后，就释放锁 
                item_trylock_unlock(item_lock);
                item_lock = NULL;
            }
        }

        if (!expanding) {//不需要迁移数据(了)
            /* We are done expanding.. just wait for next invocation */
            started_expanding = false;//重置

            //挂起迁移线程，直到worker线程插入数据后发现item数量已经到了1.5倍哈希表大小，  
            //此时调用worker线程调用assoc_start_expand函数，该函数会调用pthread_cond_signal  
            //唤醒迁移线程
            pthread_cond_wait(&maintenance_cond, &maintenance_lock);
            /* assoc_expand() swaps out the hash table entirely, so we need
             * all threads to not hold any references related to the hash
             * table while this happens.
             * This is instead of a more complex, possibly slower algorithm to
             * allow dynamic hash table expansion without causing significant
             * wait times.
             */
            pause_threads(PAUSE_ALL_THREADS);
            assoc_expand();//申请更大的哈希表,并将expanding设置为true
            pause_threads(RESUME_ALL_THREADS);
        }
    }
    return NULL;
}

static pthread_t maintenance_tid;

//main函数会调用本函数，启动数据迁移线程
int start_assoc_maintenance_thread() {
    int ret;
    char *env = getenv("MEMCACHED_HASH_BULK_MOVE");
    if (env != NULL) {
        //hash_bulk_move的作用在后面会说到。
        //这里是通过环境变量给hash_bulk_move赋值
        hash_bulk_move = atoi(env);
        if (hash_bulk_move == 0) {
            hash_bulk_move = DEFAULT_HASH_BULK_MOVE;
        }
    }
    pthread_mutex_init(&maintenance_lock, NULL);
    if ((ret = pthread_create(&maintenance_tid, NULL,
                              assoc_maintenance_thread, NULL)) != 0) {
        fprintf(stderr, "Can't create thread: %s\n", strerror(ret));
        return -1;
    }
    return 0;
}

void stop_assoc_maintenance_thread() {
    mutex_lock(&maintenance_lock);
    do_run_maintenance_thread = 0;
    pthread_cond_signal(&maintenance_cond);
    mutex_unlock(&maintenance_lock);

    /* Wait for the maintenance thread to stop */
    pthread_join(maintenance_tid, NULL);
}

