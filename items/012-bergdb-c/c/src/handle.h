/*
 * handle: Java's bergdb.dag.Handle (bergdb item 009; 009-02, 4.1), and the
 * changes that Java's Cache3 makes to a handle (bergdb 012-07, section
 * 6.3). Prefix hd_.
 *
 * One handle per index node that has a resident object or that a pointer of
 * a resident object names. A pointer to an index node holds the node's
 * handle, and the handle holds the node's one object, canonical or a
 * version (counted), so that evicting the object changes the handle only.
 * States: LIVE, the node table's handle for the node, with an object or
 * none; DEAD (OBJ_DEAD), evicted: out of the table, no object, never live
 * again, and freed when no pointer holds it. Java's LOADING, for concurrent
 * loaders, is left out: one caller. The CLOCK bit is OBJ_REF.
 *
 * The back reference of an index object (struct knode and struct tnode's
 * handle) is not counted; its rule: an object's back reference is NULL or
 * the handle that holds it. A handle that lets go of its object clears the
 * object's back reference and sets OBJ_LEFT on the object (Java keeps the
 * reference; no call of Handle.of in Java passes such an object, which
 * hd_of asserts).
 */
#ifndef BERGDB_HANDLE_H
#define BERGDB_HANDLE_H

#include <stdbool.h>
#include <stdint.h>
#include "node.h"
#include "obj.h"

struct handle {
    struct obj o;
    int64_t id;                 /* the node id (final) */
    struct node *obj;           /* the node's one object, counted; or NULL */
    int64_t written_pos;        /* where a canonical object was when hd_kill killed it; -1 */
};

/* new Handle(id): a live handle with no object, pending (obj.h); NULL:
 * NOMEM. */
struct handle *hd_new(struct obj_ctx *cx, int64_t id);

/* Handle.of: index node object n's handle, its back reference, made (with
 * n as its object) if it has none; NULL: NOMEM. */
struct handle *hd_of(struct obj_ctx *cx, struct node *n);

/* Handle.pointeeOf: what a pointer to object n holds: n itself if a value,
 * else n's handle (hd_of); NULL for NULL. Returns false on NOMEM. */
bool hd_pointee_of(struct obj_ctx *cx, struct node *n, struct obj **out);

/* Handle.usable: object o may serve a pointer whose reference is ref. */
bool hd_usable(const struct node *o, int64_t ref);

/* Handle.serializedRef, the record rule (009-02, 4.6): what a pointer that
 * holds p (NULL, a handle or a value) with reference ref is written as. */
int64_t hd_serialized_ref(const struct obj *p, int64_t ref);

bool hd_is_dead(const struct handle *h);

/* The handle's object becomes o (NULL allowed), counted; the object it
 * held before is let go: released, its back reference cleared. o's back
 * reference becomes h. What Cache3.register, install and makeCanonical do
 * to Handle.obj (with Cache3.setHandle). */
void hd_set_obj(struct obj_ctx *cx, struct handle *h, struct node *o);

/* Cache3.kill and the state change of Cache3.evict: a canonical object's
 * valid position (not a vpos) into written_pos, its canonical flag cleared,
 * the object let go, the handle DEAD. Removing it from the node table is
 * the table's. */
void hd_kill(struct obj_ctx *cx, struct handle *h);

/* The free of a handle (obj.c): lets go of its object; with release false
 * (close's walk) only the block is freed. */
void hd_destroy(struct obj_ctx *cx, struct handle *h, bool release);

#endif
