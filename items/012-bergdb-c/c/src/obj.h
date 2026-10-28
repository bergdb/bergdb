/*
 * obj: the counted objects of the index, and their memory (bergdb 012-07,
 * section 6.4; 012-01, 4.5). Java leaves these objects to its garbage
 * collector; C counts their holders and frees at safe points. Prefix obj_.
 *
 * Four kinds share the head struct obj: key nodes (knode.h), top nodes
 * (tnode.h), value nodes (vnode.h) and handles (handle.h). Each counts its
 * holders in refs: the fields that hold it beyond a safe point (012-07,
 * 6.4.2), never locals. An object is made with no holder and goes on the
 * pending list at once; an object whose count falls to 0 goes on it too.
 * Nothing is freed then. At a safe point (obj_collect) each pending object
 * leaves the list and is freed if its count is still 0; its free releases
 * what it holds, which can make more objects pending, in the same loop. So
 * the ported code can hold any object in locals between two safe points, in
 * Java's order, and nothing it uses is freed under it.
 *
 * The struct obj_ctx is the database's (one per database, no global
 * state): its allocator and its pending list. One caller at a time.
 */
#ifndef BERGDB_OBJ_H
#define BERGDB_OBJ_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include "mem.h"

enum obj_kind {
    OBJ_KEY = 1,        /* struct knode, Java's KeyNode */
    OBJ_TOP = 2,        /* struct tnode, TopNode */
    OBJ_VALUE = 3,      /* struct vnode, ValueNode */
    OBJ_HANDLE = 4      /* struct handle, Handle */
};

/* The flags: the memory's, then Java's booleans and the handle's state. */
#define OBJ_PENDING   0x0001u   /* on the pending list */
#define OBJ_MARK      0x0002u   /* reached by a walk (obj_recount, obj_free_all) */
#define OBJ_DIRTY     0x0004u   /* Node.isDirty: key and top nodes */
#define OBJ_CANONICAL 0x0008u   /* Node.isCanonical: key and top nodes */
#define OBJ_IN_TRANS  0x0010u   /* isInTransNodes, ValueNode.isInTransactionNodes */
#define OBJ_LEAF      0x0020u   /* KeyNode.isSegmentLeaf (final) */
#define OBJ_DEAD      0x0040u   /* a handle's DEAD; LIVE without it */
#define OBJ_REF       0x0080u   /* Handle.ref, the CLOCK bit */
#define OBJ_LEFT      0x0100u   /* an index object that a handle let go of (handle.h) */
#define OBJ_REPLACED  0x0200u   /* in Db.replacedInTrans during a transaction (db.h) */

struct obj {
    int32_t refs;               /* the counted holders */
    uint8_t kind;               /* enum obj_kind */
    uint8_t unused;
    uint16_t flags;
    struct obj *next;           /* the pending list's link, or a walk's */
};

struct obj_ctx {
    struct mem *mem;
    struct obj *pending;        /* the pending list, linked by next */
    int64_t live[5];            /* live objects by kind, 1 to 4 */
};

void obj_ctx_init(struct obj_ctx *cx, struct mem *m);

/* A zeroed object of size bytes and the kind, with refs 0, on the pending
 * list (made without a holder); NULL on a failed allocation (NOMEM). */
void *obj_alloc(struct obj_ctx *cx, size_t size, enum obj_kind kind);

/* Frees the block of object o, of size bytes as allocated, without any
 * release: for the kinds' free functions. */
void obj_dealloc(struct obj_ctx *cx, struct obj *o, size_t size);

/* A field starts to hold o (NULL allowed). */
static inline void obj_retain(struct obj *o) {
    if (o != NULL) {
        o->refs++;
    }
}

/* A field stops holding o (NULL allowed): its count falls by one, and at
 * 0 it goes on the pending list. */
void obj_release(struct obj_ctx *cx, struct obj *o);

/* *field = v as a counted holder: v retained, then the old one released. */
void obj_set(struct obj_ctx *cx, struct obj **field, struct obj *v);

/* Puts o on the pending list, unless it is on it. */
void obj_pend(struct obj_ctx *cx, struct obj *o);

/* A safe point: every pending object leaves the list and is freed if no
 * holder holds it, until the list is empty. */
void obj_collect(struct obj_ctx *cx);

/* The number of objects o holds, and the i-th (NULL for an empty slot): a
 * key node's pointers 0 to size - 1, a top node's root pointer and skip
 * pointers, a handle's object; a value holds none. */
int32_t obj_held_count(const struct obj *o);
struct obj *obj_held(const struct obj *o, int32_t i);

/* The recount (012-07, 6.4.1): from roots[0] to roots[n - 1], each one
 * counted holder (an object listed twice is held twice), and from the
 * pending list, every reachable object; then each count must equal its
 * holders among them. Returns the number of objects whose count is wrong
 * (0: all right), and in *reached, if not NULL, the objects reached. The
 * pending list keeps its objects (not its order). Allocates nothing. */
int64_t obj_recount(struct obj_ctx *cx, struct obj *const *roots, int32_t n, int64_t *reached);

/* Close's walk, which frees (012-01, 4.5, point 6) every object reachable from
 * roots[0] to roots[n - 1] and the pending list, once each, without
 * trusting the counts (it works after a failure). Allocates nothing.
 * Returns the number of objects freed. */
int64_t obj_free_all(struct obj_ctx *cx, struct obj *const *roots, int32_t n);

#endif
