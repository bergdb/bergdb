/*
 * dag: Java's bergdb.dag.Dag (bergdb 012-08), the multiversion map of
 * keys: its put path (putKv, with the splits and new top nodes as Java
 * makes them), its reads at a time (getOne; getMany is getmany.h's
 * Chain), and dirtyNodeBound (005-31); with Java's PutData, GetData,
 * KeyAccessPath and Dag.SplitListener. Prefixes dag_, pd_, gd_, kap_.
 *
 * Every node and listener is 012-07's (knode.h, tnode.h, topds.h,
 * opdata.h). Memory follows 012-07, section 6: the Dag makes its objects
 * pending and holds what it keeps through counted fields (a key node's
 * pointers, a top node's, TopDs's super root); locals, KeyAccessPath's
 * nodes and the kwp's are borrowed, valid until the caller's next safe
 * point (obj_collect). So a put follows Java's order line for line,
 * temporaries included (lastVersion's node when a space split makes two
 * new ones), and the caller collects after the operation.
 *
 * A function that can fail returns false: a failed allocation of the Dag's
 * own (NOMEM), or a callback that returned false (opdata.h: the follower, a
 * listener), where Java would throw; the counts are kept, and after a
 * transaction's go point the caller fails the database (012-01, 4.5).
 * Java's asserts are C's (on in both builds). Left out: printGraph,
 * visitMemoryPointersOnce, visitMemoryNodes (debug walks; the tests have
 * their own), and Java's monitors (one caller).
 */
#ifndef BERGDB_DAG_H
#define BERGDB_DAG_H

#include <stdbool.h>
#include <stdint.h>
#include "knode.h"
#include "mem.h"
#include "node.h"
#include "obj.h"
#include "opdata.h"
#include "topds.h"
#include "vnode.h"

/* Dag.TIME_SPLIT_1 and the others: the kinds of splits. */
#define DAG_TIME_SPLIT_1 1
#define DAG_TIME_SPLIT_2 2
#define DAG_SPACE_SPLIT_1 11
#define DAG_SPACE_SPLIT_2 12
#define DAG_SPACE_SPLIT_3 13

/* KeyAccessPath: the key nodes a put passed, from the space root down, each
 * with the klong of its parent that led to it (Klong.NULL for the space
 * root). Its nodes are borrowed (a put's locals). */
struct kap {
    int32_t size;
    int32_t used;               /* the high-water mark: the entries of nodes that kap_add
                                   may have set since the last pd_clear, also through
                                   pd_clear_fast and later adds; pd_clear nulls only these
                                   (KeyAccessPath.used, bergdb 021-25, fix (c)) */
    int32_t cap;
    int64_t *klongs;            /* MEM_STATE, with nodes: cap of each */
    struct knode **nodes;
    struct mem *mem;
};

/* Dag.SplitListener */
struct dag_split_listener {
    void (*node_split)(void *ctx, int32_t split_type);
    void *ctx;
};

/* PutData: a put's settings, its output and its scratch. Made by
 * dag_new_put_data, whose pointer listener fills the access path, as
 * Dag.newPutData's; pd_free frees the path's arrays. Do not copy it: the
 * listeners' ctx is its address. */
struct putdata {
    struct opdata op;           /* OpData: pointerFollower, pointerListener, ... */
    struct op_node_change_listener node_change_listener;
    struct op_pointer_created_listener pointer_created_listener;
    struct kap key_access_path;
    struct dag_split_listener split_listener;
    int64_t tt;                 /* the transaction's time */
    int64_t space_split_count;
    int64_t time_split_count;
    struct kwp one_kwi[1];      /* scratch; borrowed nodes */
    struct kwp two_kwis[2];
};

/* GetData: a read's output and scratch. Made by dag_new_get_data, whose
 * pointer listener counts the pointers followed, as Dag.newGetData's. */
struct getdata {
    struct opdata op;
    int64_t actual_lookup_time; /* set by the database (Db.getOneInternal), not the Dag */
    int64_t kv_time;            /* the found pair's key node entry's time (not its write time) */
    int64_t tpos;               /* the found value's record (ValueNode.getTpos) */
    int64_t follow_memory_pointer_count;
    int64_t follow_stream_pointer_count;
    int32_t node_depth;
};

struct dag {
    struct topds top_ds;
    int32_t max_node_size;
    struct obj_ctx *cx;
};

/* new Dag(superRoot, maxNodeSize): TopDs holds super_root (counted). */
void dag_init(struct dag *d, struct obj_ctx *cx, struct tnode *super_root, int32_t max_node_size);

/* Dag.createEmpty(time, maxNodeSize, pointerFollower, pcl): a top node at
 * time and an empty segment leaf as its root (new KeyNode()), the
 * listener's pointerCreated. false: NOMEM or the listener. */
bool dag_create_empty(struct dag *d, struct obj_ctx *cx, int64_t time, int32_t max_node_size,
        const struct op_pointer_created_listener *pcl);

/* Releases what the Dag holds (its super root); the nodes go at the next
 * obj_collect, or with obj_free_all. */
void dag_free(struct dag *d);

/* Dag.getTopDs */
struct topds *dag_get_top_ds(struct dag *d);

/* Dag.newPutData: pd made for this Dag (its pointer listener fills the
 * access path, its split listener counts); the caller sets its pointer
 * follower and listeners as Db does. m: the access path's allocator. */
void dag_new_put_data(struct dag *d, struct putdata *pd, struct mem *m);

/* Frees the access path's arrays. */
void pd_free(struct putdata *pd);

/* PutData.clearFast (after each putKv) and clear (after a transaction). */
void pd_clear_fast(struct putdata *pd);
void pd_clear(struct putdata *pd);

/* PutData.getParent: the node above depth on the access path, NULL for the
 * space root. */
struct knode *pd_get_parent(const struct putdata *pd, int32_t depth);

/* KeyAccessPath.add: false on NOMEM. */
bool kap_add(struct kap *p, int64_t klong, struct knode *node);
int64_t kap_get_klong(const struct kap *p, int32_t index);
struct knode *kap_get(const struct kap *p, int32_t index);

/* Dag.newGetData: gd made for this Dag; the caller sets its follower. */
void dag_new_get_data(struct dag *d, struct getdata *gd);

/* Dag.findNode: from the super root, the pointers choices[0] to
 * choices[n - 1] followed in turn; *out NULL if one leads nowhere. */
bool dag_find_node(struct dag *d, const int32_t *choices, int32_t n, struct getdata *gd,
        struct node **out);

/* Dag.getOne: the value of the key (n segments) at time: *out the value
 * node (borrowed), or NULL if none; gd->kv_time and gd->tpos set when one
 * is found. */
bool dag_get_one(struct dag *d, int64_t time, const int64_t *key, int32_t n, struct getdata *gd,
        struct vnode **out);

/* Dag.putKv: the pair (key of n segments, value of len bytes) put at
 * pd->tt, or the key deleted if value is NULL (len ignored). New nodes and
 * changes are reported to pd's listeners, as Java's. */
bool dag_put_kv(struct dag *d, const int64_t *key, int32_t n, const uint8_t *value, int32_t len,
        struct putdata *pd);

/* Dag.dirtyNodeBound (005-31): an upper bound on the index nodes that a
 * transaction with these keys (keys[k], key_n[k] segments; deletes[k] true
 * for a delete), at a later time than 'time', can make dirty or create.
 * m: its scratch's allocator. */
bool dag_dirty_node_bound(struct dag *d, int64_t time, const int64_t *const *keys,
        const int32_t *key_n, const bool *deletes, int32_t count, struct getdata *gd,
        struct mem *m, int64_t *out);

#endif
