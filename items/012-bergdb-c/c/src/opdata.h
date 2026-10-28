/*
 * opdata: Java's bergdb.dag.OpData, and the interfaces of the Dag that the
 * nodes and TopDs call (bergdb 012-07): PointerFollower, Dag.PointerListener,
 * Dag.PointerCreatedListener, Dag.NodeChangeListener, Dag.CachePolicy, with
 * Java's do-nothing versions. Prefix op_. Dag's own (PutData, GetData, the
 * split listener) are 012-08's.
 *
 * Each interface is a struct of functions and their context. A function
 * that can fail returns bool, false on a failure (NOMEM, or a read of the
 * stream that failed), where Java's would throw: Db's listeners allocate (the
 * node table, the operation's marks), and a follower reads. The caller stops
 * and returns the failure; the one who set the function knows the error.
 */
#ifndef BERGDB_OPDATA_H
#define BERGDB_OPDATA_H

#include <stdbool.h>
#include <stdint.h>
#include "node.h"

struct opdata;
struct knode;
struct tnode;
struct vnode;

/* PointerFollower.followPointer: the node that pointer index of
 * predecessor leads to; NULL on a failure. */
struct op_follower {
    struct node *(*follow)(void *ctx, struct node *predecessor, int32_t index, struct opdata *op);
    void *ctx;
};

/* Dag.PointerListener */
struct op_pointer_listener {
    bool (*pointer_followed)(void *ctx, struct node *predecessor, int32_t index,
            struct node *result, int32_t pointer_type);
    bool (*super_root_accessed)(void *ctx, struct tnode *super_root);
    void *ctx;
};

/* Dag.PointerCreatedListener */
struct op_pointer_created_listener {
    bool (*pointer_created)(void *ctx, struct node *from, int32_t index, struct node *to);
    void *ctx;
};

/* Dag.NodeChangeListener; key_node_replaced and top_node_replaced do
 * nothing by default in Java (NULL here does nothing). */
struct op_node_change_listener {
    bool (*top_node_created)(void *ctx, struct tnode *node);
    bool (*key_node_created)(void *ctx, struct knode *node);
    bool (*value_node_created)(void *ctx, struct vnode *node, const int64_t *key, int32_t key_n);
    bool (*key_node_changed)(void *ctx, struct knode *node);
    bool (*key_node_replaced)(void *ctx, struct knode *node);
    bool (*top_node_replaced)(void *ctx, struct tnode *node);
    void *ctx;
};

/* Dag.CachePolicy */
struct op_cache_policy {
    bool (*should_cache)(void *ctx, const struct node *node);
    void *ctx;
};

/* OpData: an operation's settings and scratch (Java's fields). */
struct opdata {
    struct op_follower pointer_follower;
    struct op_pointer_listener pointer_listener;
    struct op_cache_policy cache_policy;
    int64_t access_data;
    struct pointer temp_pointer;        /* borrowed node (012-07, 6.4.2) */
    struct kwp kwi;                     /* borrowed node */
};

/* new OpData(): no functions, access data 0, the scratch reset. */
void op_init(struct opdata *op);

/* OpData.followPointer */
struct node *op_follow_pointer(struct opdata *op, struct node *predecessor, int32_t index);

/* Dag.DO_NOTHING_POINTER_LISTENER, DO_NOTHING_POINTER_CREATED_LISTENER,
 * DO_NOTHING_NODE_CHANGE_LISTENER: every function returns true. */
extern const struct op_pointer_listener OP_DO_NOTHING_POINTER_LISTENER;
extern const struct op_pointer_created_listener OP_DO_NOTHING_POINTER_CREATED_LISTENER;
extern const struct op_node_change_listener OP_DO_NOTHING_NODE_CHANGE_LISTENER;

/* The calls, each true if the function is NULL. */
bool op_pointer_created(const struct op_pointer_created_listener *l, struct node *from,
        int32_t index, struct node *to);
bool op_top_node_created(const struct op_node_change_listener *l, struct tnode *node);
bool op_top_node_replaced(const struct op_node_change_listener *l, struct tnode *node);
bool op_super_root_accessed(const struct op_pointer_listener *l, struct tnode *super_root);

#endif
