/* obj: the counted objects, the pending list, safe points; see obj.h. */
#include "obj.h"
#include <assert.h>
#include <string.h>
#include "handle.h"
#include "knode.h"
#include "tnode.h"
#include "vnode.h"

void obj_ctx_init(struct obj_ctx *cx, struct mem *m) {
    memset(cx, 0, sizeof *cx);
    cx->mem = m;
}

static enum mem_kind mem_kind_of(enum obj_kind kind) {
    switch (kind) {
    case OBJ_VALUE:
        return MEM_VALUE;
    case OBJ_HANDLE:
        return MEM_HANDLE;
    case OBJ_KEY:
    case OBJ_TOP:
        break;
    }
    return MEM_INDEX;
}

void *obj_alloc(struct obj_ctx *cx, size_t size, enum obj_kind kind) {
    assert(size >= sizeof(struct obj));
    struct obj *o = mem_zalloc(cx->mem, size, mem_kind_of(kind));
    if (o == NULL) {
        return NULL;
    }
    o->kind = (uint8_t) kind;
    cx->live[kind]++;
    obj_pend(cx, o);            /* made without a holder */
    return o;
}

void obj_dealloc(struct obj_ctx *cx, struct obj *o, size_t size) {
    enum obj_kind kind = (enum obj_kind) o->kind;
    cx->live[kind]--;
    mem_free(cx->mem, o, size, mem_kind_of(kind));
}

void obj_pend(struct obj_ctx *cx, struct obj *o) {
    if ((o->flags & OBJ_PENDING) == 0) {
        o->flags |= OBJ_PENDING;
        o->next = cx->pending;
        cx->pending = o;
    }
}

void obj_release(struct obj_ctx *cx, struct obj *o) {
    if (o == NULL) {
        return;
    }
    assert(o->refs > 0);
    if (--o->refs == 0) {
        obj_pend(cx, o);
    }
}

void obj_set(struct obj_ctx *cx, struct obj **field, struct obj *v) {
    struct obj *old = *field;
    obj_retain(v);
    *field = v;
    obj_release(cx, old);
}

/* The free of o, by its kind: releases what it holds (if release) and
 * frees its memory. */
static void destroy(struct obj_ctx *cx, struct obj *o, bool release) {
    switch ((enum obj_kind) o->kind) {
    case OBJ_KEY:
        kn_destroy(cx, (struct knode *) o, release);
        return;
    case OBJ_TOP:
        tn_destroy(cx, (struct tnode *) o, release);
        return;
    case OBJ_VALUE:
        vn_destroy(cx, (struct vnode *) o);
        return;
    case OBJ_HANDLE:
        hd_destroy(cx, (struct handle *) o, release);
        return;
    }
    assert(0 && "bad object kind");
}

void obj_collect(struct obj_ctx *cx) {
    while (cx->pending != NULL) {
        struct obj *o = cx->pending;
        cx->pending = o->next;
        o->next = NULL;
        o->flags &= (uint16_t) ~OBJ_PENDING;
        if (o->refs == 0) {
            destroy(cx, o, true);       /* may make more objects pending */
        }
    }
}

int32_t obj_held_count(const struct obj *o) {
    switch ((enum obj_kind) o->kind) {
    case OBJ_KEY:
        return ((const struct knode *) o)->size;
    case OBJ_TOP:
        return 1 + ((const struct tnode *) o)->pointers_length;
    case OBJ_HANDLE:
        return 1;
    case OBJ_VALUE:
        break;
    }
    return 0;
}

struct obj *obj_held(const struct obj *o, int32_t i) {
    switch ((enum obj_kind) o->kind) {
    case OBJ_KEY:
        return ((const struct knode *) o)->pointers[i];
    case OBJ_TOP: {
        const struct tnode *t = (const struct tnode *) o;
        const struct handle *h = i == 0 ? t->root_pointer : t->skip[i - 1].p;
        return h == NULL ? NULL : (struct obj *) &h->o;
    }
    case OBJ_HANDLE: {
        const struct handle *h = (const struct handle *) o;
        return h->obj == NULL ? NULL : &h->obj->o;
    }
    case OBJ_VALUE:
        break;
    }
    return NULL;
}

/*
 * The walk of obj_recount and obj_free_all, which allocates nothing: the
 * stack and the list of what it reached are linked through next. It starts
 * from the roots and the pending list (whose links it takes over), marks
 * each object it reaches (OBJ_MARK) when it pushes it, and returns the
 * list of every object reached, each once, linked by next. The objects
 * keep their OBJ_PENDING flags; the pending list is empty afterwards.
 */
static struct obj *walk(struct obj_ctx *cx, struct obj *const *roots, int32_t n) {
    struct obj *stack = NULL;
    struct obj *done = NULL;

    /* The pending list becomes the stack's start. */
    for (struct obj *o = cx->pending; o != NULL; o = o->next) {
        assert((o->flags & OBJ_MARK) == 0);
        o->flags |= OBJ_MARK;
    }
    stack = cx->pending;
    cx->pending = NULL;
    for (int32_t i = 0; i < n; i++) {
        struct obj *o = roots[i];
        if (o != NULL && (o->flags & OBJ_MARK) == 0) {
            o->flags |= OBJ_MARK;
            o->next = stack;
            stack = o;
        }
    }
    while (stack != NULL) {
        struct obj *o = stack;
        stack = o->next;
        o->next = done;
        done = o;
        int32_t count = obj_held_count(o);
        for (int32_t i = 0; i < count; i++) {
            struct obj *c = obj_held(o, i);
            if (c != NULL && (c->flags & OBJ_MARK) == 0) {
                c->flags |= OBJ_MARK;
                c->next = stack;
                stack = c;
            }
        }
    }
    return done;
}

int64_t obj_recount(struct obj_ctx *cx, struct obj *const *roots, int32_t n, int64_t *reached) {
    struct obj *done = walk(cx, roots, n);
    int64_t count = 0;
    int64_t wrong = 0;

    /* One less per counted holder found: each root, each reached object's
     * pointees and handle objects. */
    for (int32_t i = 0; i < n; i++) {
        if (roots[i] != NULL) {
            roots[i]->refs--;
        }
    }
    for (struct obj *o = done; o != NULL; o = o->next) {
        int32_t held = obj_held_count(o);
        for (int32_t i = 0; i < held; i++) {
            struct obj *c = obj_held(o, i);
            if (c != NULL) {
                c->refs--;
            }
        }
    }
    for (struct obj *o = done; o != NULL; o = o->next) {
        count++;
        if (o->refs != 0) {
            wrong++;
        }
    }
    /* The counts back, the marks cleared, the pending list again. */
    for (int32_t i = 0; i < n; i++) {
        if (roots[i] != NULL) {
            roots[i]->refs++;
        }
    }
    struct obj *o = done;
    while (o != NULL) {
        struct obj *next = o->next;
        int32_t held = obj_held_count(o);
        for (int32_t i = 0; i < held; i++) {
            struct obj *c = obj_held(o, i);
            if (c != NULL) {
                c->refs++;
            }
        }
        o->flags &= (uint16_t) ~OBJ_MARK;
        o->next = NULL;
        if ((o->flags & OBJ_PENDING) != 0) {
            o->next = cx->pending;
            cx->pending = o;
        }
        o = next;
    }
    if (reached != NULL) {
        *reached = count;
    }
    return wrong;
}

int64_t obj_free_all(struct obj_ctx *cx, struct obj *const *roots, int32_t n) {
    struct obj *done = walk(cx, roots, n);
    int64_t count = 0;
    while (done != NULL) {
        struct obj *next = done->next;
        destroy(cx, done, false);
        count++;
        done = next;
    }
    return count;
}
