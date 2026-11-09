/*
 * tnode: Java's bergdb.dag.TopNode (bergdb 012-07), and the making of a top
 * node object from a parsed one (StoredTopNode.parse's second half). Prefix
 * tn_.
 *
 * A top node is one link of the chain of top nodes, a skip list in time
 * (topds.h): its root pointer names the B-tree's root key node of its time
 * (root_time), and its skip pointers name older top nodes, pointer i set
 * exactly when bit i of its ordinal (Java's topNodeId) is. Its pointers hold
 * handles (counted) or nothing; each has a reference, and each skip pointer
 * caches its target's root time. Pointer 0 is the root pointer, pointer
 * i + 1 skip pointer i, as in Java. The skip pointers are fixed when the
 * node is made, so they are in the node's own block (MEM_INDEX).
 * Left out: toString, printGraph, print (debug text), accept.
 */
#ifndef BERGDB_TNODE_H
#define BERGDB_TNODE_H

#include <stdbool.h>
#include <stdint.h>
#include "handle.h"
#include "node.h"
#include "obj.h"

struct knode;

/* TopNode.MAX_HEIGHT, MAX_TOP_NODE_ID_VALUE (2^48 - 1; bergdb 005-02) */
#define TN_MAX_HEIGHT 48
#define TN_MAX_TOP_NODE_ID_VALUE ((INT64_C(1) << TN_MAX_HEIGHT) - 1)

struct tskip {
    struct handle *p;           /* TopNode.pointers[i], counted */
    int64_t pos;                /* pointersPos[i] */
    int64_t time;               /* pointersTime[i]: the target's root time; -1 if unset */
};

struct tnode {
    struct node n;
    int64_t top_node_id;        /* the ordinal (final) */
    int64_t root_time;
    struct handle *root_pointer;        /* counted; NULL: a stream pointer */
    int64_t root_pointer_pos;
    struct handle *handle;      /* TopNode.handle, the back reference: not counted */
    int16_t pointers_length;    /* h, the ordinal's bit length (final) */
    struct tskip skip[];        /* pointers_length of them */
};

/* TopNode.height: the bit length of id, 0 to 48 (id at most the maximum,
 * asserted; Java throws IllegalStateException). */
int32_t tn_height(int64_t id);

/* TopNode.power2 */
int64_t tn_power2(int32_t x);

/* new TopNode(topNodeId, rootPointer, rootPointerPos, rootTime, spos): a
 * root object becomes its handle (hd_of), with its position as the
 * reference; without one, root_pointer_pos is a stream pointer's position.
 * The skip pointers unset, the id -1. Pending (obj.h); NULL: NOMEM. */
struct tnode *tn_new(struct obj_ctx *cx, int64_t top_node_id, struct knode *root_pointer,
        int64_t root_pointer_pos, int64_t root_time, int64_t spos);

/* TopNode.createDummy, for tests. */
struct tnode *tn_create_dummy(struct obj_ctx *cx, int64_t top_node_id);

/* StoredTopNode.parse's object: the parsed ordinal (at most the maximum),
 * root pointer's position, root time, spos and id, and its h skip pointers
 * as pos and time pairs, little-endian at skips_le (16 bytes each); h must
 * be the ordinal's height (the parser's check). Every pointer a stream
 * pointer. NULL: NOMEM. */
struct tnode *tn_new_stored(struct obj_ctx *cx, int64_t top_node_id, int64_t root_pointer_pos,
        int64_t root_time, int64_t spos, int64_t id, int32_t h, const uint8_t *skips_le);

/* getSize: pointerCount, h + 1. */
int32_t tn_get_size(const struct tnode *t);
/* getPointerTime: the root time for 0, else skip pointer index - 1's. */
int64_t tn_get_pointer_time(const struct tnode *t, int32_t index);
void tn_get_pointer(const struct tnode *t, int32_t index, struct pointer *p);
struct node *tn_get_pointer_node(const struct tnode *t, int32_t index);
int64_t tn_get_pointer_pos(const struct tnode *t, int32_t index);
struct obj *tn_get_pointee(const struct tnode *t, int32_t index);
/* setPointee, setRef, raiseRef, swizzle, setPointer; the pointee (a handle
 * or NULL) counted. */
void tn_set_pointee(struct obj_ctx *cx, struct tnode *t, int32_t index, struct obj *pointee);
void tn_set_ref(struct tnode *t, int32_t index, int64_t ref);
void tn_raise_ref(struct tnode *t, int32_t index, int64_t ref);
bool tn_swizzle(struct obj_ctx *cx, struct tnode *t, int32_t index, struct obj *expected,
        struct obj *pointee);
void tn_set_pointer(struct obj_ctx *cx, struct tnode *t, int32_t index, struct obj *pointee,
        int64_t ref);
/* getSerializedRef: the record rule (hd_serialized_ref). */
int64_t tn_get_serialized_ref(const struct tnode *t, int32_t index);
/* getMemSize: 112 + 24 h; getMemoryPointerCount. */
int32_t tn_get_mem_size(const struct tnode *t);
int32_t tn_get_memory_pointer_count(const struct tnode *t);

/* The free of a top node (obj.c): releases its handles (if release) and
 * frees the node. */
void tn_destroy(struct obj_ctx *cx, struct tnode *t, bool release);

#endif
