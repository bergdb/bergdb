/*
 * vnode: Java's bergdb.dag.ValueNode (bergdb 012-07), and the making of a
 * value node object from a parsed one (StoredValueNode.parse's second
 * half). Prefix vn_.
 *
 * A value node holds the value of one key-value pair of a transaction, or,
 * as a delete node, its deletion (Java's value == null; len -1 here). Its
 * bytes are in its own block (MEM_VALUE), copied when it is made; its key
 * is not in it, as in Java: the record and the parsed node have it. A value
 * node is always canonical, never dirty, and has no pointers.
 */
#ifndef BERGDB_VNODE_H
#define BERGDB_VNODE_H

#include <stdbool.h>
#include <stdint.h>
#include "node.h"
#include "obj.h"

struct vnode {
    struct node n;
    uint32_t offset_from_trans; /* ValueNode.offsetFromTrans: spos - tpos, unsigned (005-34) */
    int32_t len;                /* the value's length; -1: a delete (value == null) */
    uint8_t value[];
};

/* new ValueNode(value, spos): a copy of value[0] to value[len - 1]; len -1
 * (value NULL) for a delete. Pending (obj.h); NULL: NOMEM. */
struct vnode *vn_new(struct obj_ctx *cx, const uint8_t *value, int32_t len, int64_t spos);

/* ValueNode.createDelete: a delete node, spos -1. */
struct vnode *vn_create_delete(struct obj_ctx *cx);

/* StoredValueNode.parse's object: the value (len -1 for a delete node) at
 * spos with the id, and offsetFromTrans = spos - tpos, its record's
 * position computed by the parser (RecoverableStream.getStartSpos). */
struct vnode *vn_new_stored(struct obj_ctx *cx, const uint8_t *value, int32_t len, int64_t spos,
        int64_t id, int64_t tpos);

/* ValueNode.getTpos: the position of the record that wrote the node, -1 if
 * it is not written yet (its spos -1 or a vpos). */
int64_t vn_get_tpos(const struct vnode *v);
/* ValueNode.getOffsetFromTrans: offsetFromTrans as an unsigned int. */
int64_t vn_get_offset_from_trans(const struct vnode *v);
/* ValueNode.getType: NODE_TYPE_DELETE or NODE_TYPE_VALUE. */
int32_t vn_get_type(const struct vnode *v);
bool vn_is_delete(const struct vnode *v);
/* ValueNode.getMemSize: 36 for a delete, else 56 + the value's length. */
int32_t vn_get_mem_size(const struct vnode *v);

/* The free of a value node (obj.c): it holds nothing. */
void vn_destroy(struct obj_ctx *cx, struct vnode *v);

#endif
