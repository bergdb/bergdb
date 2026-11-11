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
#include "err.h"
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
 * nothing by default in Java (NULL here does nothing). key_node_replaced:
 * a key node that existed before the transaction was replaced by a split,
 * or unlinked by a delete (bergdb 023-07, section 5.1; release 2026.4).
 * key_node_taken_back: a key node that the transaction made was taken back
 * (Dag.takeBack, Dag.takeBackRoot): no node names it and it is never
 * written; NULL calls key_node_replaced, as Java's default does. It is the
 * last member, so that a listener initialized by position leaves it NULL. */
struct op_node_change_listener {
    bool (*top_node_created)(void *ctx, struct tnode *node);
    bool (*key_node_created)(void *ctx, struct knode *node);
    bool (*value_node_created)(void *ctx, struct vnode *node, const int64_t *key, int32_t key_n);
    bool (*key_node_changed)(void *ctx, struct knode *node);
    bool (*key_node_replaced)(void *ctx, struct knode *node);
    bool (*top_node_replaced)(void *ctx, struct tnode *node);
    void *ctx;
    bool (*key_node_taken_back)(void *ctx, struct knode *node);
};

/* Dag.CachePolicy */
struct op_cache_policy {
    bool (*should_cache)(void *ctx, const struct node *node);
    void *ctx;
};

/* OpData: an operation's settings and scratch (Java's fields). err is C's:
 * where a failure of the Dag's own code goes (Dag.checkFound's DbException,
 * bergdb 019-32; a followed node of another type than the code casts it
 * to, op_cast_ok), set by the one who sets the follower to where it looks
 * for the follower's failures; NULL (op_init's): nowhere, and the caller
 * sees a failure without its text. */
struct opdata {
    struct op_follower pointer_follower;
    struct op_pointer_listener pointer_listener;
    struct op_cache_policy cache_policy;
    int64_t access_data;
    struct pointer temp_pointer;        /* borrowed node (012-07, 6.4.2) */
    struct kwp kwi;                     /* borrowed node */
    struct err *err;                    /* not counted, not owned */
    int64_t descent_mark;               /* the check of a descent for a cycle (op_descent_to) */
    uint32_t descent_steps;             /* unsigned: Java's int wraps, C's must not */
    uint32_t descent_power;
};

/* new OpData(): no functions, access data 0, the scratch reset. */
void op_init(struct opdata *op);

/* OpData.followPointer */
struct node *op_follow_pointer(struct opdata *op, struct node *predecessor, int32_t index);

/* OpData.descentFrom and descentTo (bergdb 020-32; Java's since release
 * 2026.4): the check of a descent for a cycle, which a damaged stream can
 * make (a key node's prevPos that names its own child's version before the
 * startup section: Rule R then made the node's pointer to that child a
 * pointer to the node itself, and a get looped without end). Brent's cycle
 * detection on node ids: the id of the node of step 2^k is kept, and each
 * node after it compared with it, so a cycle is found within about twice the
 * steps of the path and the cycle, in constant memory. A node without an id
 * (SPOS_NULL) is not compared. op_descent_from starts the check at root;
 * op_descent_to is a step to next: false, with Java's StreamFormatException
 * in *op->err (NodeCollection.cycle; every follower of C is a database's),
 * if the descent came back to a node it passed. */
void op_descent_from(struct opdata *op, const struct node *root);
bool op_descent_to(struct opdata *op, const struct node *next);

/* Java's cast of a node that a follow gave (KeyNode or TopNode: type
 * NODE_TYPE_KEY_NODE or NODE_TYPE_TOP_NODE), where C cast it with an assert:
 * true if node is of that type; else false, and Java's ClassCastException,
 * with the JVM's text, in *op->err (C-only, bergdb 019-32's class: Java's
 * checks of a pointer's pointee are in the follows, which do not see every
 * pointer that a start links, NodeCollection.linkToCanonical, or the writer
 * resolves, resolvePointers; C never reads a node as another type). */
bool op_cast_ok(struct opdata *op, const struct node *node, int32_t type);

/* Java's assert that a node that a follow gave is a KeyNode (GetMany's,
 * "next instanceof KeyNode", whose text is prefix and the node), as
 * op_cast_ok, with an AssertionError (Java's tests and harness run with
 * -ea). */
bool op_assert_key(struct opdata *op, const struct node *node, const char *prefix);

/* An error of the Dag's own code into *op->err (if set and still clear),
 * its text formatted as by printf; returns false. */
bool op_fail(struct opdata *op, enum err_code code, const char *java, const char *format, ...);

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
