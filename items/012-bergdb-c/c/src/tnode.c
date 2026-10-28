/* tnode: ported from Java's bergdb.dag.TopNode; see tnode.h. */
#include "tnode.h"
#include <assert.h>
#include "bytes.h"
#include "handle.h"
#include "jsem.h"
#include "knode.h"
#include "spos.h"

static size_t top_bytes(int32_t h) {
    return sizeof(struct tnode) + (size_t) h * sizeof(struct tskip);
}

/* TopNode.power2 */
int64_t tn_power2(int32_t x) {
    return j_shl64(1, x);
}

/* TopNode.height */
int32_t tn_height(int64_t id) {
    /*
     * power2: 1  2  4  8
     *      i: 0  1  2  3
     */
    assert(id <= TN_MAX_TOP_NODE_ID_VALUE && "Bad id value");

    int32_t i = 0;
    for (i = 0; i < TN_MAX_HEIGHT; i++) {
        if (id < tn_power2(i)) {
            break;
        }
    }
    return i;
}

/* TopNode(topNodeId, rootPointer, rootPointerPos, rootTime, spos) */
struct tnode *tn_new(struct obj_ctx *cx, int64_t topNodeId, struct knode *rootPointer,
        int64_t rootPointerPos, int64_t rootTime, int64_t spos) {
    const int32_t h = tn_height(topNodeId);
    struct handle *root = NULL;
    if (rootPointer != NULL) {
        root = hd_of(cx, &rootPointer->n);
        if (root == NULL) {
            return NULL;
        }
    }
    struct tnode *t = obj_alloc(cx, top_bytes(h), OBJ_TOP);
    if (t == NULL) {
        return NULL;
    }
    /* A root object becomes its handle, with its position as the reference
     * (bergdb item 009, step 3a); without one, rootPointerPos is the stream
     * pointer's position. */
    obj_retain(root == NULL ? NULL : &root->o);
    t->root_pointer = root;
    t->root_pointer_pos = rootPointer == NULL ? rootPointerPos : rootPointer->n.spos;
    t->root_time = rootTime;

    assert(h < INT16_MAX - 1);
    t->pointers_length = (int16_t) h;

    t->n.spos = spos;
    t->n.id = SPOS_NULL;
    t->top_node_id = topNodeId;
    t->handle = NULL;

    for (int32_t i = 0; i < h; i++) {
        t->skip[i].p = NULL;
        t->skip[i].pos = SPOS_NULL;
        t->skip[i].time = -1;
    }
    return t;
}

/* TopNode.createDummy */
struct tnode *tn_create_dummy(struct obj_ctx *cx, int64_t topNodeId) {
    int64_t keyNodeSpos = 100;

    struct knode *k = kn_new(cx, true);
    if (k == NULL) {
        return NULL;
    }
    k->n.spos = keyNodeSpos;
    k->n.id = keyNodeSpos;

    struct tnode *result = tn_new(cx, topNodeId, k, k->n.spos, 1, 100);
    if (result == NULL) {
        return NULL;
    }
    result->n.id = 103;
    for (int32_t i = 0; i < result->pointers_length; i++) {
        if ((topNodeId & tn_power2(i)) != 0) {
            result->skip[i].pos = 16 * (i + 1);
            result->skip[i].time = 0;
        }
    }
    return result;
}

/* StoredTopNode.parse, from "new TopNode(topNodeId, null, ...)" on. */
struct tnode *tn_new_stored(struct obj_ctx *cx, int64_t topNodeId, int64_t rootPointerPos,
        int64_t rootTime, int64_t spos, int64_t id, int32_t pointerCount,
        const uint8_t *skips_le) {
    struct tnode *t = tn_new(cx, topNodeId, NULL, rootPointerPos, rootTime, spos);
    if (t == NULL) {
        return NULL;
    }
    assert(pointerCount == t->pointers_length);     /* the parser's check */
    t->n.id = id;
    for (int32_t i = 0; i < t->pointers_length; i++) {
        int64_t pos = bytes_get_long_le(skips_le + 16 * (size_t) i);
        if (pos == SPOS_NULL) {
            t->skip[i].p = NULL;
            t->skip[i].pos = SPOS_NULL;
            t->skip[i].time = -1;
        } else {
            t->skip[i].p = NULL;
            t->skip[i].pos = pos;
            t->skip[i].time = bytes_get_long_le(skips_le + 16 * (size_t) i + 8);
        }
    }
    return t;
}

/* TopNode.getSize */
int32_t tn_get_size(const struct tnode *t) {
    return t->pointers_length + 1;
}

/* TopNode.getPointerTime */
int64_t tn_get_pointer_time(const struct tnode *t, int32_t index) {
    return index == 0 ? t->root_time : t->skip[index - 1].time;
}

/* TopNode.getPointer */
void tn_get_pointer(const struct tnode *t, int32_t index, struct pointer *pointer) {
    pointer->index = index;
    pointer->node = tn_get_pointer_node(t, index);
    pointer->pos = tn_get_pointer_pos(t, index);
}

/* TopNode.getPointerNode: the handle's object if it may serve the pointer. */
struct node *tn_get_pointer_node(const struct tnode *t, int32_t index) {
    assert(index >= 0 && index <= t->pointers_length);
    const struct handle *h = index == 0 ? t->root_pointer : t->skip[index - 1].p;
    if (h == NULL) {
        return NULL;
    }
    struct node *o = h->obj;
    return o != NULL && hd_usable(o, tn_get_pointer_pos(t, index)) ? o : NULL;
}

/* TopNode.getPointerPos */
int64_t tn_get_pointer_pos(const struct tnode *t, int32_t index) {
    return index == 0 ? t->root_pointer_pos : t->skip[index - 1].pos;
}

/* TopNode.getPointee */
struct obj *tn_get_pointee(const struct tnode *t, int32_t index) {
    const struct handle *h = index == 0 ? t->root_pointer : t->skip[index - 1].p;
    return h == NULL ? NULL : (struct obj *) &h->o;
}

/* TopNode.setPointee */
void tn_set_pointee(struct obj_ctx *cx, struct tnode *t, int32_t index, struct obj *pointee) {
    assert(pointee == NULL || pointee->kind == OBJ_HANDLE);     /* Java's cast (Handle) */
    struct handle **field = index == 0 ? &t->root_pointer : &t->skip[index - 1].p;
    struct handle *old = *field;
    obj_retain(pointee);
    *field = (struct handle *) pointee;
    obj_release(cx, old == NULL ? NULL : &old->o);
}

/* TopNode.setRef */
void tn_set_ref(struct tnode *t, int32_t index, int64_t ref) {
    if (index == 0) {
        t->root_pointer_pos = ref;
    } else {
        t->skip[index - 1].pos = ref;
    }
}

/* TopNode.raiseRef */
void tn_raise_ref(struct tnode *t, int32_t index, int64_t ref) {
    if (spos_newer(ref, tn_get_pointer_pos(t, index))) {
        tn_set_ref(t, index, ref);
    }
}

/* TopNode.swizzle */
bool tn_swizzle(struct obj_ctx *cx, struct tnode *t, int32_t index, struct obj *expected,
        struct obj *pointee) {
    if (tn_get_pointee(t, index) != expected) {
        return false;
    }
    tn_set_pointee(cx, t, index, pointee);
    return true;
}

/* TopNode.setPointer */
void tn_set_pointer(struct obj_ctx *cx, struct tnode *t, int32_t index, struct obj *pointee,
        int64_t ref) {
    tn_set_pointee(cx, t, index, pointee);
    tn_set_ref(t, index, ref);
}

/* TopNode.getSerializedRef */
int64_t tn_get_serialized_ref(const struct tnode *t, int32_t index) {
    return hd_serialized_ref(tn_get_pointee(t, index), tn_get_pointer_pos(t, index));
}

/* TopNode.getMemSize */
int32_t tn_get_mem_size(const struct tnode *t) {
    return 112 + t->pointers_length * 24;
}

/* TopNode.getMemoryPointerCount */
int32_t tn_get_memory_pointer_count(const struct tnode *t) {
    int32_t count = 0;
    for (int32_t i = 0; i < tn_get_size(t); i++) {
        if (tn_get_pointer_node(t, i) != NULL) {
            count++;
        }
    }
    return count;
}

void tn_destroy(struct obj_ctx *cx, struct tnode *t, bool release) {
    if (release) {
        assert(t->handle == NULL);      /* as kn_destroy */
        for (int32_t i = 0; i <= t->pointers_length; i++) {
            tn_set_pointee(cx, t, i, NULL);
        }
    }
    obj_dealloc(cx, &t->n.o, top_bytes(t->pointers_length));
}
