/* node: Java's Node interface over the three kinds, Pointer and
 * KlongWithPointer; see node.h. */
#include "node.h"
#include <assert.h>
#include "klong.h"
#include "knode.h"
#include "spos.h"
#include "tnode.h"
#include "vnode.h"

/* Pointer.reset */
void ptr_reset(struct pointer *p) {
    p->node = NULL;
    p->pos = SPOS_NULL;
    p->index = -1;
}

/* Pointer.isMem */
bool ptr_is_mem(const struct pointer *p) {
    return p->node != NULL;
}

/* Pointer.isNull */
bool ptr_is_null(const struct pointer *p) {
    return ptr_is_null2(p->node, p->pos);
}

/* Pointer.getSposForStream */
int64_t ptr_spos_for_stream(const struct pointer *p) {
    return ptr_is_mem(p) ? p->node->spos : p->pos;
}

/* Pointer.isNull(node, pos) */
bool ptr_is_null2(const struct node *node, int64_t pos) {
    return node == NULL && pos == SPOS_NULL;
}

/* new KlongWithPointer() */
void kwp_init(struct kwp *k) {
    k->klong = KL_NULL;
    k->pointer_index = -1;
    k->klong_time = -1;
    k->node = NULL;
    k->pos = SPOS_NULL;
}

/* KlongWithPointer.isNullPointer */
bool kwp_is_null_pointer(const struct kwp *k) {
    return ptr_is_null2(k->node, k->pos);
}

int32_t node_type(const struct node *n) {
    switch ((enum obj_kind) n->o.kind) {
    case OBJ_KEY:
        return NODE_TYPE_KEY_NODE;
    case OBJ_TOP:
        return NODE_TYPE_TOP_NODE;
    case OBJ_VALUE:
        return vn_get_type((const struct vnode *) n);
    case OBJ_HANDLE:
        break;
    }
    assert(0 && "not a node");
    return 0;
}

/* Node.name's kind */
const char *node_kind(int32_t type) {
    return type == NODE_TYPE_KEY_NODE ? "key node" : type == NODE_TYPE_TOP_NODE ? "top node"
            : "value node";
}

bool node_is_index_node(const struct node *n) {
    return n->o.kind == OBJ_KEY || n->o.kind == OBJ_TOP;
}

bool node_is_key_node(const struct node *n) {
    return n->o.kind == OBJ_KEY;
}

bool node_is_top_node(const struct node *n) {
    return n->o.kind == OBJ_TOP;
}

bool node_is_value_node(const struct node *n) {
    return n->o.kind == OBJ_VALUE;
}

int64_t node_spos(const struct node *n) {
    return n->spos;
}

void node_set_spos(struct node *n, int64_t spos) {
    n->spos = spos;
}

int64_t node_id(const struct node *n) {
    return n->id;
}

void node_set_id(struct node *n, int64_t id) {
    n->id = id;
}

static void set_flag(struct node *n, uint16_t flag, bool on) {
    if (on) {
        n->o.flags |= flag;
    } else {
        n->o.flags &= (uint16_t) ~flag;
    }
}

bool node_is_dirty(const struct node *n) {
    return (n->o.flags & OBJ_DIRTY) != 0;
}

/* setDirty: ValueNode.setDirty(true) throws IllegalArgumentException. */
void node_set_dirty(struct node *n, bool dirty) {
    assert(!(dirty && n->o.kind == OBJ_VALUE) && "A ValueNode cannot be dirty.");
    set_flag(n, OBJ_DIRTY, dirty);
}

bool node_is_canonical(const struct node *n) {
    return (n->o.flags & OBJ_CANONICAL) != 0;
}

/* setCanonical: no effect for a value node, which is always canonical. */
void node_set_canonical(struct node *n, bool canonical) {
    if (n->o.kind != OBJ_VALUE) {
        set_flag(n, OBJ_CANONICAL, canonical);
    }
}

bool node_is_in_trans_nodes(const struct node *n) {
    return (n->o.flags & OBJ_IN_TRANS) != 0;
}

void node_set_in_trans_nodes(struct node *n, bool b) {
    set_flag(n, OBJ_IN_TRANS, b);
}

int32_t node_size(const struct node *n) {
    switch ((enum obj_kind) n->o.kind) {
    case OBJ_KEY:
        return kn_get_size((const struct knode *) n);
    case OBJ_TOP:
        return tn_get_size((const struct tnode *) n);
    case OBJ_VALUE:
    case OBJ_HANDLE:
        break;
    }
    return 0;
}

int32_t node_size_at_time(const struct node *n, int64_t lookupTime) {
    if (n->o.kind == OBJ_KEY) {
        return kn_get_size_at_time((const struct knode *) n, lookupTime);
    }
    return node_size(n);
}

struct node *node_pointer_node(const struct node *n, int32_t index) {
    if (n->o.kind == OBJ_KEY) {
        return kn_get_pointer_node((const struct knode *) n, index);
    }
    assert(n->o.kind == OBJ_TOP && "A ValueNode has no pointers");
    return tn_get_pointer_node((const struct tnode *) n, index);
}

int64_t node_pointer_pos(const struct node *n, int32_t index) {
    if (n->o.kind == OBJ_KEY) {
        return kn_get_pointer_pos((const struct knode *) n, index);
    }
    assert(n->o.kind == OBJ_TOP && "A ValueNode has no pointers");
    return tn_get_pointer_pos((const struct tnode *) n, index);
}

struct obj *node_pointee(const struct node *n, int32_t index) {
    if (n->o.kind == OBJ_KEY) {
        return kn_get_pointee((const struct knode *) n, index);
    }
    assert(n->o.kind == OBJ_TOP && "A ValueNode has no pointers");
    return tn_get_pointee((const struct tnode *) n, index);
}

void node_get_pointer(const struct node *n, int32_t index, struct pointer *p) {
    if (n->o.kind == OBJ_KEY) {
        kn_get_pointer((const struct knode *) n, index, p);
        return;
    }
    assert(n->o.kind == OBJ_TOP && "A ValueNode has no pointers");
    tn_get_pointer((const struct tnode *) n, index, p);
}

int64_t node_serialized_ref(const struct node *n, int32_t index) {
    if (n->o.kind == OBJ_KEY) {
        return kn_get_serialized_ref((const struct knode *) n, index);
    }
    assert(n->o.kind == OBJ_TOP && "a value node has no pointers");
    return tn_get_serialized_ref((const struct tnode *) n, index);
}

void node_set_pointee(struct obj_ctx *cx, struct node *n, int32_t index, struct obj *pointee) {
    if (n->o.kind == OBJ_KEY) {
        kn_set_pointee(cx, (struct knode *) n, index, pointee);
        return;
    }
    assert(n->o.kind == OBJ_TOP && "A ValueNode has no pointers to set");
    tn_set_pointee(cx, (struct tnode *) n, index, pointee);
}

void node_set_ref(struct node *n, int32_t index, int64_t ref) {
    if (n->o.kind == OBJ_KEY) {
        kn_set_ref((struct knode *) n, index, ref);
        return;
    }
    assert(n->o.kind == OBJ_TOP && "A ValueNode has no pointers to set");
    tn_set_ref((struct tnode *) n, index, ref);
}

void node_raise_ref(struct node *n, int32_t index, int64_t ref) {
    if (n->o.kind == OBJ_KEY) {
        kn_raise_ref((struct knode *) n, index, ref);
        return;
    }
    assert(n->o.kind == OBJ_TOP && "A ValueNode has no pointers to set");
    tn_raise_ref((struct tnode *) n, index, ref);
}

bool node_swizzle(struct obj_ctx *cx, struct node *n, int32_t index, struct obj *expected,
        struct obj *pointee) {
    if (n->o.kind == OBJ_KEY) {
        return kn_swizzle(cx, (struct knode *) n, index, expected, pointee);
    }
    assert(n->o.kind == OBJ_TOP && "A ValueNode has no pointers to set");
    return tn_swizzle(cx, (struct tnode *) n, index, expected, pointee);
}

void node_set_pointer(struct obj_ctx *cx, struct node *n, int32_t index, struct obj *pointee,
        int64_t ref) {
    if (n->o.kind == OBJ_KEY) {
        kn_set_pointer(cx, (struct knode *) n, index, pointee, ref);
        return;
    }
    assert(n->o.kind == OBJ_TOP && "A ValueNode has no pointers to set");
    tn_set_pointer(cx, (struct tnode *) n, index, pointee, ref);
}

int32_t node_memory_pointer_count(const struct node *n) {
    switch ((enum obj_kind) n->o.kind) {
    case OBJ_KEY:
        return kn_get_memory_pointer_count((const struct knode *) n);
    case OBJ_TOP:
        return tn_get_memory_pointer_count((const struct tnode *) n);
    case OBJ_VALUE:
    case OBJ_HANDLE:
        break;
    }
    return 0;
}

int32_t node_mem_size(const struct node *n) {
    switch ((enum obj_kind) n->o.kind) {
    case OBJ_KEY:
        return kn_get_mem_size((const struct knode *) n);
    case OBJ_TOP:
        return tn_get_mem_size((const struct tnode *) n);
    case OBJ_VALUE:
        return vn_get_mem_size((const struct vnode *) n);
    case OBJ_HANDLE:
        break;
    }
    return 0;
}
