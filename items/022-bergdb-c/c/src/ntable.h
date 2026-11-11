/*
 * ntable: the node table, Java's bergdb.core.Cache3 as far as the startup
 * and the loads need it (bergdb 012-10; 012-07, sections 6.2 and 6.7): node
 * id to the node's live handle, at most one per id, and through it the
 * node's one resident object. register (the writer's and the startup's
 * objects, canonical), install (a version read by a follower), makeCanonical
 * (the writer's follow), liveHandle, liveOrNewHandle, getNode, dropIfEmpty,
 * and the handles in turn (linkD's byPos, close's roots). Prefix nt_.
 *
 * The table holds each live handle (counted, 012-07, 6.4.2: Cache3.maps).
 * A value has no handle and is not in the table (009-02, 4.8). Left out
 * for 012-12 (evict.h): the CLOCK walk, eviction's policy; evict (nt_evict)
 * and the sizes (nt_bytes, nt_shrink) are here. The residents and the
 * access clock are left out (the allocator counts the bytes; no byte
 * depends on them). Java's 4,096 maps and their locks
 * are one map here (lmap.h), whose iteration order is its own: Java's
 * handles() order decides nothing that is written (linkD's byPos is keyed by
 * distinct positions).
 */
#ifndef BERGDB_NTABLE_H
#define BERGDB_NTABLE_H

#include <stdbool.h>
#include <stdint.h>
#include "err.h"
#include "handle.h"
#include "lmap.h"
#include "mem.h"
#include "node.h"
#include "obj.h"

struct ntable {
    struct obj_ctx *cx;
    struct lmap map;            /* id to the live handle (the pointer as a long) */
};

void nt_init(struct ntable *t, struct obj_ctx *cx, struct mem *m);

/* Frees the map. With release, the table's counts of its handles are
 * released first (they go at the next obj_collect); without, close's walk
 * (obj_free_all) has taken them as roots. */
void nt_free(struct ntable *t, bool release);

/* liveHandle: the node's live handle, or NULL. */
struct handle *nt_live_handle(const struct ntable *t, int64_t id);

/* liveOrNewHandle: the node's live handle, made with no object (and held by
 * the table) if it has none. NULL: NOMEM. */
struct handle *nt_live_or_new_handle(struct ntable *t, int64_t id);

/* getNode: the object of the node's live handle, or NULL. */
struct node *nt_get_node(const struct ntable *t, int64_t id);

/* register: node, an object that the writer or the startup made, as its
 * node's object, in the node's live handle, made (or the object's own,
 * Handle.of's, adopted) if it has none. A canonical object already there is
 * kept; else node replaces the handle's object if it is better (canonical,
 * or a newer version). *out: the handle's object after the call; a value is
 * returned as it is. Refused (ERR_NOMEM; or ERR_FORMAT,
 * "StreamFormatException", Cache3.checkType, bergdb 019-32, release 2026.3:
 * the handle's object is of another type, one id with two types, which a
 * damaged node's id gives) with nothing changed but a new empty handle. */
enum err_code nt_register(struct ntable *t, struct node *node, struct node **out,
        struct err *e);

/* install: node, a version read from the stream, into its live handle h,
 * unless h has a better object. *out: the handle's object after the call.
 * Refused as register (checkType, 019-32), h unchanged. */
enum err_code nt_install(struct ntable *t, struct handle *h, struct node *node,
        struct node **out, struct err *e);

/* makeCanonical: the handle's canonical object if it has one, else the
 * newer of node and the handle's object, made canonical and the handle's
 * object. Returns it. */
struct node *nt_make_canonical(struct ntable *t, struct handle *h, struct node *node);

/* dropIfEmpty: live handle h, if it has no object, dies and leaves the
 * table. */
void nt_drop_if_empty(struct ntable *t, struct handle *h);

/* Cache3.dropNode (bergdb 023-07, section 5.1; Java's since release
 * 2026.4): node, a key node that its transaction made and took back
 * (dag.c's take_back, take_back_root), leaves the table as an evicted
 * object does: its handle dies (hd_kill), its canonical flag is cleared, and
 * the handle leaves the table. It was never written, and no node names it.
 * If the table's handle of its id holds another object, or there is none,
 * only the node's canonical flag is cleared. */
void nt_drop_node(struct ntable *t, struct node *node);

/* Cache3.evict (012-12): live handle h dies (hd_kill: a canonical object's
 * position into its written position, the object let go) and leaves the
 * table. The caller has checked that the object may go (evict.h). false if
 * h is dead already. */
bool nt_evict(struct ntable *t, struct handle *h);

/* The bytes of the table's own arrays, as allocated (012-12: part of the
 * resident bytes). */
int64_t nt_bytes(const struct ntable *t);

/* After eviction (012-12): a table that holds fewer than an eighth of its
 * slots is made again at its size, so that its arrays shrink as eviction
 * takes handles. Changes the slots' order; on NOMEM it stays as it is. */
void nt_shrink(struct ntable *t);

/* The number of live handles, and the handles in the table's order:
 * for (i = 0; i < nt_slots(t); i++) if ((h = nt_slot(t, i)) != NULL). */
int64_t nt_size(const struct ntable *t);
int64_t nt_slots(const struct ntable *t);
struct handle *nt_slot(const struct ntable *t, int64_t i);

#endif
