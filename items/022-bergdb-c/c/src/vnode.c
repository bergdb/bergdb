/* vnode: ported from Java's bergdb.dag.ValueNode; see vnode.h. */
#include "vnode.h"
#include <assert.h>
#include <string.h>
#include "jsem.h"
#include "spos.h"

static size_t value_bytes(int32_t len) {
    return sizeof(struct vnode) + (len < 0 ? 0 : (size_t) len);
}

/* ValueNode(byte[] value, long spos) */
struct vnode *vn_new(struct obj_ctx *cx, const uint8_t *value, int32_t len, int64_t spos) {
    assert(len >= -1);
    assert(len <= 0 || value != NULL);
    struct vnode *v = obj_alloc(cx, value_bytes(len), OBJ_VALUE);
    if (v == NULL) {
        return NULL;
    }
    v->len = len;
    if (len > 0) {
        memcpy(v->value, value, (size_t) len);
    }
    v->n.spos = spos;
    v->n.id = 0;                /* Java's default; Db sets it (setIdOfNode) */
    v->offset_from_trans = 0;
    v->n.o.flags |= OBJ_CANONICAL;      /* isCanonical: always true */
    return v;
}

/* ValueNode.createDelete */
struct vnode *vn_create_delete(struct obj_ctx *cx) {
    return vn_new(cx, NULL, -1, SPOS_NULL);
}

/* StoredValueNode.parse, from "new ValueNode(value, spos)" on. */
struct vnode *vn_new_stored(struct obj_ctx *cx, const uint8_t *value, int32_t len, int64_t spos,
        int64_t id, int64_t tpos) {
    struct vnode *valueNode = vn_new(cx, value, len, spos);
    if (valueNode == NULL) {
        return NULL;
    }
    valueNode->n.id = id;
    valueNode->offset_from_trans = (uint32_t) j_l2i(spos - tpos);     /* (int) (spos - tpos) */
    return valueNode;
}

/* ValueNode.getTpos */
int64_t vn_get_tpos(const struct vnode *v) {
    const int64_t p = v->n.spos;
    return spos_is_null(p) || spos_is_vpos(p) ? SPOS_NULL
            : p - (int64_t) v->offset_from_trans;          /* Integer.toUnsignedLong */
}

/* ValueNode.getOffsetFromTrans */
int64_t vn_get_offset_from_trans(const struct vnode *v) {
    return (int64_t) v->offset_from_trans;
}

/* ValueNode.getType */
int32_t vn_get_type(const struct vnode *v) {
    return v->len < 0 ? NODE_TYPE_DELETE : NODE_TYPE_VALUE;
}

/* ValueNode.isDelete */
bool vn_is_delete(const struct vnode *v) {
    return v->len < 0;
}

/* ValueNode.getMemSize */
int32_t vn_get_mem_size(const struct vnode *v) {
    return v->len < 0 ? 36 : 56 + v->len;
}

void vn_destroy(struct obj_ctx *cx, struct vnode *v) {
    obj_dealloc(cx, &v->n.o, value_bytes(v->len));
}
