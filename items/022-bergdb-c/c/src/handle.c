/* handle: ported from Java's bergdb.dag.Handle, with Cache3's changes of a
 * handle; see handle.h. */
#include "handle.h"
#include <assert.h>
#include "knode.h"
#include "spos.h"
#include "tnode.h"

/* The back reference of index object n (KeyNode.handle, TopNode.handle). */
static struct handle **back_ref(struct node *n) {
    if (n->o.kind == OBJ_KEY) {
        return &((struct knode *) n)->handle;
    }
    assert(n->o.kind == OBJ_TOP);
    return &((struct tnode *) n)->handle;
}

/* new Handle(id) */
struct handle *hd_new(struct obj_ctx *cx, int64_t id) {
    struct handle *h = obj_alloc(cx, sizeof(struct handle), OBJ_HANDLE);
    if (h == NULL) {
        return NULL;
    }
    h->id = id;
    h->obj = NULL;
    h->written_pos = SPOS_NULL;
    return h;
}

/* Handle.of */
struct handle *hd_of(struct obj_ctx *cx, struct node *n) {
    struct handle **ref = back_ref(n);
    if (*ref == NULL) {
        /* Java returns the handle the object was in, if it left one; no call
         * passes such an object (012-07, 6.3). */
        assert((n->o.flags & OBJ_LEFT) == 0 && "Handle.of of an object that left its handle");
        struct handle *h = hd_new(cx, n->id);     /* new Handle(id, obj) */
        if (h == NULL) {
            return NULL;
        }
        obj_retain(&n->o);
        h->obj = n;
        *ref = h;
    }
    return *ref;
}

/* Handle.pointeeOf */
bool hd_pointee_of(struct obj_ctx *cx, struct node *n, struct obj **out) {
    if (n == NULL) {
        *out = NULL;
        return true;
    }
    if (n->o.kind == OBJ_VALUE) {
        *out = &n->o;
        return true;
    }
    struct handle *h = hd_of(cx, n);
    *out = h == NULL ? NULL : &h->o;
    return h != NULL;
}

/* Handle.usable */
bool hd_usable(const struct node *o, int64_t ref) {
    return node_is_canonical(o) || (!spos_is_vpos(ref) && o->spos >= ref);
}

/* Handle.serializedRef */
int64_t hd_serialized_ref(const struct obj *p, int64_t ref) {
    if (p != NULL && p->kind == OBJ_VALUE) {
        return ((const struct node *) p)->spos;
    }
    if (p != NULL && p->kind == OBJ_HANDLE) {
        const struct handle *h = (const struct handle *) p;
        const struct node *o = h->obj;
        if (o != NULL && node_is_canonical(o)) {
            return o->spos;
        }
        int64_t w = h->written_pos;
        if (spos_is_valid(w) && !spos_is_vpos(w) && (spos_is_vpos(ref) || w > ref)) {
            return w;
        }
    }
    return ref;
}

bool hd_is_dead(const struct handle *h) {
    return (h->o.flags & OBJ_DEAD) != 0;
}

/* The handle stops holding its object; left: as Java's handle lets go of
 * it while the object keeps its back reference (OBJ_LEFT), or not, as when
 * the handle itself goes, which Java's object would keep alive. */
static void drop_obj(struct obj_ctx *cx, struct handle *h, bool left) {
    struct node *o = h->obj;
    if (o == NULL) {
        return;
    }
    h->obj = NULL;
    struct handle **ref = back_ref(o);
    if (*ref == h) {
        *ref = NULL;
        if (left) {
            o->o.flags |= OBJ_LEFT;
        }
    }
    obj_release(cx, &o->o);
}

/* Handle.obj = o, with Cache3.setHandle(o, h) */
void hd_set_obj(struct obj_ctx *cx, struct handle *h, struct node *o) {
    if (h->obj == o) {
        return;
    }
    if (o != NULL) {
        obj_retain(&o->o);
    }
    drop_obj(cx, h, true);
    h->obj = o;
    if (o != NULL) {
        struct handle **ref = back_ref(o);
        if (*ref != NULL && *ref != h) {
            /* o leaves the handle it was in (Java: setHandle replaces the
             * back reference; the other handle keeps o as its object). */
            assert((*ref)->obj != o && "an object in two handles");
        }
        *ref = h;
        o->o.flags &= (uint16_t) ~OBJ_LEFT;
    }
}

/* Cache3.kill, and the state change of Cache3.evict */
void hd_kill(struct obj_ctx *cx, struct handle *h) {
    struct node *o = h->obj;
    h->o.flags |= OBJ_DEAD;
    if (o == NULL) {
        return;
    }
    if (node_is_canonical(o)) {
        int64_t spos = o->spos;
        if (spos_is_valid(spos) && !spos_is_vpos(spos)) {
            h->written_pos = spos;
        }
        node_set_canonical(o, false);
    }
    drop_obj(cx, h, true);
}

void hd_destroy(struct obj_ctx *cx, struct handle *h, bool release) {
    if (release) {
        drop_obj(cx, h, false);
    }
    obj_dealloc(cx, &h->o, sizeof(struct handle));
}
