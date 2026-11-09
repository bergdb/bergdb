/*
 * node: Java's bergdb.dag.Node, the interface of the three kinds of nodes
 * (key, top and value nodes), as a common head and accessors that switch
 * on the kind; with Java's Pointer, KlongWithPointer and AccessData's
 * constants (bergdb 012-07, section 6.1). Prefixes node_, ptr_, kwp_.
 *
 * A pointer of a key or a top node holds a struct obj *: NULL, a handle
 * (handle.h; a pointer to an index node) or a value node (a pointer to a
 * value), as Java's Pointee; and has a reference, a position, a vpos or
 * -1 (Spos.NULL). Left out: print, toString, accept (Java's debug text and
 * visitors).
 */
#ifndef BERGDB_NODE_H
#define BERGDB_NODE_H

#include <stdbool.h>
#include <stdint.h>
#include "obj.h"

/* Node.TYPE_TOP_NODE and the others: the type byte of a stored node. */
#define NODE_TYPE_TOP_NODE 10
#define NODE_TYPE_KEY_NODE 20
#define NODE_TYPE_VALUE 30
#define NODE_TYPE_DELETE 40

/* AccessData.DEFAULT_ACCESS_DATA and ZERO: since bergdb item 009, step 3a,
 * a pointer's reference is never access data; the constants are left. */
#define ACCESS_DATA_DEFAULT INT64_C(-10)
#define ACCESS_DATA_ZERO INT64_C(0)

/* Pointer.TYPE_MEMORY, TYPE_STREAM */
#define PTR_TYPE_MEMORY 1
#define PTR_TYPE_STREAM 2

/* The head of every node: Java's Node with its id and spos (the id until
 * the node is first written, then its latest version's position). */
struct node {
    struct obj o;
    int64_t id;
    int64_t spos;
};

/* Java's Pointer: an output parameter; node is borrowed (not counted). */
struct pointer {
    struct node *node;
    int64_t pos;
    int32_t index;
};

/* Java's KlongWithPointer: a search's result; node is borrowed. */
struct kwp {
    int64_t klong;              /* Klong.NULL if none */
    int32_t pointer_index;
    int64_t klong_time;
    struct node *node;
    int64_t pos;
};

/* Pointer.reset, new Pointer() */
void ptr_reset(struct pointer *p);
bool ptr_is_mem(const struct pointer *p);
bool ptr_is_null(const struct pointer *p);
/* Pointer.getSposForStream */
int64_t ptr_spos_for_stream(const struct pointer *p);
/* Pointer.isNull(node, pos) */
bool ptr_is_null2(const struct node *node, int64_t pos);

/* new KlongWithPointer() */
void kwp_init(struct kwp *k);
/* KlongWithPointer.isNullPointer */
bool kwp_is_null_pointer(const struct kwp *k);

/* Node's methods, for any of the three kinds. */
int32_t node_type(const struct node *n);          /* getType: NODE_TYPE_... */
bool node_is_index_node(const struct node *n);
bool node_is_key_node(const struct node *n);
bool node_is_top_node(const struct node *n);
bool node_is_value_node(const struct node *n);
int64_t node_spos(const struct node *n);
void node_set_spos(struct node *n, int64_t spos);
int64_t node_id(const struct node *n);
void node_set_id(struct node *n, int64_t id);
bool node_is_dirty(const struct node *n);
/* setDirty; a value node is never dirty (asserted, where Java throws). */
void node_set_dirty(struct node *n, bool dirty);
bool node_is_canonical(const struct node *n);
void node_set_canonical(struct node *n, bool canonical);
bool node_is_in_trans_nodes(const struct node *n);
void node_set_in_trans_nodes(struct node *n, bool b);
/* getSize: the number of pointers (a value node has none). */
int32_t node_size(const struct node *n);
int32_t node_size_at_time(const struct node *n, int64_t lookup_time);
/* getPointerNode, getPointerPos, getPointee, getPointer, getSerializedRef:
 * of a key or a top node (asserted). */
struct node *node_pointer_node(const struct node *n, int32_t index);
int64_t node_pointer_pos(const struct node *n, int32_t index);
struct obj *node_pointee(const struct node *n, int32_t index);
void node_get_pointer(const struct node *n, int32_t index, struct pointer *p);
int64_t node_serialized_ref(const struct node *n, int32_t index);
/* setPointee, setRef, raiseRef, swizzle, setPointer: of a key or a top
 * node; the pointee counted (obj.h). */
void node_set_pointee(struct obj_ctx *cx, struct node *n, int32_t index, struct obj *pointee);
void node_set_ref(struct node *n, int32_t index, int64_t ref);
void node_raise_ref(struct node *n, int32_t index, int64_t ref);
bool node_swizzle(struct obj_ctx *cx, struct node *n, int32_t index, struct obj *expected,
        struct obj *pointee);
void node_set_pointer(struct obj_ctx *cx, struct node *n, int32_t index, struct obj *pointee,
        int64_t ref);
int32_t node_memory_pointer_count(const struct node *n);
/* getMemSize: Java's estimate of the object's bytes. */
int32_t node_mem_size(const struct node *n);

#endif
