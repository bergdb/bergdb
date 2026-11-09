/*
 * evict: eviction to a memory budget, Level 4 (bergdb 012-12; docs/levels.md,
 * section 7): Java's bergdb.core.Eviction (the capacity controller, the
 * schedule BUDGET, and the admission of large values) and Cache3's evict
 * and clockStep, rewritten for one caller (012-01, 4.1 and 4.5). Prefix ev_.
 *
 * What is resident: the objects of the index in memory, counted exactly by
 * the allocator (P8): the key nodes and top nodes (MEM_INDEX), the values
 * (MEM_VALUE) and the handles (MEM_HANDLE), and the node table's arrays
 * (ntable.h, nt_bytes). Java counts estimates of its objects (Residents); C
 * counts the bytes it has allocated for them.
 *
 * What is pinned, as Java's Eviction.detachable: an object in the record
 * being written (OBJ_IN_TRANS); the super root; the newest written top node;
 * a canonical index object that is dirty (D) or in the record; and an object
 * whose position is not a stream position yet (a vpos). Everything else in
 * the node table is detachable. An object in use by the call that runs is
 * safe without a pin: eviction runs at safe points only (the end of a call;
 * between the pairs of the API's getMany, whose chain counts its links), so
 * an object that the call still uses is counted by its holder and outlives
 * the eviction of its handle, as a Java reader may finish with an object
 * that eviction took (Eviction's class comment).
 *
 * Evict (Cache3.evict, nt_evict): the object leaves its handle, which dies
 * and leaves the table; a canonical object's position goes into the
 * handle's written position (the record rule, Handle.serializedRef), so no
 * byte changes; a pointer that holds the dead handle finds the live one by
 * the id at its next follow, and the dead handle is freed when no pointer
 * holds it (012-07, 6.4). The object, when nothing else holds it, is freed
 * at once by the safe point that follows (obj_collect), with the values
 * that only it held.
 *
 * The policy (ev_run), Java's capacity controller made deterministic:
 * when the resident bytes are over the trigger (the budget, at first), a
 * sweep runs the CLOCK hand over the node table's slots from where it
 * stopped: a live handle with no object leaves the table; a pinned object
 * stays, and the written values of a pinned key node become stream pointers
 * (Eviction.unswizzleValues); a handle whose CLOCK bit is set (a follow since
 * the hand passed, ncoll.c's touch) gets it cleared; any other object is
 * evicted. The sweep stops when the resident bytes are at most the low
 * watermark (Java's LOW, 0.75 of the budget) or after two rounds of the
 * hand (the first may only clear CLOCK bits). After a sweep of two rounds,
 * everything that could go has gone: the resident bytes then, after the
 * node table's arrays have shrunk (nt_shrink), are the floor,
 * and the trigger becomes the budget or the floor plus the gap between the
 * watermarks if that is more (Java's pinnedOfLastRound + (high - low), with
 * the floor measured by the allocator rather than summed by the hand), so
 * that pinned state above the budget does not make every call sweep. When
 * the floor so raises the trigger, the margin over it is the gap or the node
 * table's own bytes (nt_bytes, after the shrink), whichever is more (bergdb
 * 022-06, U1-4): a sweep's work is the table's slots, two rounds, so a sweep
 * that cannot reach the budget comes only after the calls have loaded at
 * least as many bytes as the table has, and the work of such sweeps is
 * linear in the bytes loaded. With the gap alone, a budget under what must
 * stay (of one byte, say: a gap of one byte) made every pair that a
 * getMany loaded sweep the whole table, which grows with D, and a full scan
 * took time quadratic in its keys. The same margin over a call's floor
 * (call_trigger). When D
 * has shrunk to three quarters of its nodes at that sweep (the take wrote
 * them), the floor is old: the trigger is the budget again, and the next
 * sweep measures a new floor.
 * Java's bounds of a batch in time (2 ms) and handles (4,096; bergdb
 * 015-67) and its thread are left out: C evicts in the call, until the
 * resident bytes are at the low watermark or nothing more can go, and its
 * choice depends on the calls only, never on timing (12-memory-budget.md,
 * 5). The calls' safe points: the end of a transaction, committed or
 * refused (bergdb 022-06, U1-3: a refusal's warmup loads too; Java's loads
 * wake its eviction thread, which then evicts, whatever the transaction's
 * end), the end of a read, and a getMany's pairs.
 *
 * Admission (Eviction.largeValueCreated and recordWritten): a value over
 * 1 MiB that the writer put into a key node is kept counted in a list until
 * its record is written, and then its pointer, and every pointer of the
 * record's key nodes to a written value over 1 MiB, becomes a stream pointer,
 * as a read does not cache such a value either; whatever the budget, as
 * Java's (its schedule is BUDGET also with noEvict()). A start's rerun of
 * the transactions puts its large values on the list too, and the open
 * drains it before its first eviction (bergdb 015-68, as Java's since
 * release 2026.3), with every resident key node as a written one, which
 * takes the large values of the startup section's first transaction, not
 * rerun (bergdb 019-47, as Java's since release 2026.4): a database opened
 * for reads keeps none in memory.
 *
 * The debug check (BERGDB_TEST, ev_check_pins): after a sweep, every pinned
 * object is still its node's object in the node table.
 */
#ifndef BERGDB_EVICT_H
#define BERGDB_EVICT_H

#include <stdbool.h>
#include <stdint.h>
#include "mem.h"
#include "node.h"
#include "ntable.h"
#include "obj.h"
#include "tnode.h"
#include "transnodes.h"
#include "transseq.h"

/* Eviction.lowOf: the low watermark of a budget, floor(3 budget / 4) in
 * integers, without overflow; INT64_MAX for none (bergdb 005-79, as Java's
 * since release 2026.2; (long) (budget * 0.75) until then, the same below
 * 2^53 / 3). */
int64_t ev_low_of(int64_t budget);

/* Dag.CACHE_ALL_EXCEPT_LARGE_VALUE_NODES' limit: a value of more bytes is
 * large. */
#define EV_LARGE_VALUE 1048576

/* A large value the writer made in this transaction: {holder, index,
 * value}, holder and value counted. */
struct ev_large {
    struct knode *holder;
    int32_t index;
    struct vnode *value;
};

struct ev {
    struct mem *mem;
    struct obj_ctx *cx;
    int64_t high;               /* the budget, the high watermark; INT64_MAX: none */
    int64_t low;                /* ev_low_of(high) */
    int64_t trigger;            /* a sweep runs when the resident bytes are over it */
    int64_t floor;              /* the resident bytes after the last sweep of two rounds */
    int64_t floor_dirty;        /* D's got-dirty nodes then (TransSeq.dirtyCount) */
    int64_t call_trigger;       /* the trigger inside a call (ev_run's in_call), or 0 */
    int64_t hand;               /* the CLOCK hand: a slot of the node table */
    struct ev_large *large;     /* the large values of the transaction */
    int32_t nlarge;
    int32_t cap_large;
    /* The figures (Eviction.figures, stats): the sweeps, those of two rounds,
     * the slots the hand looked at (the sweeps' work), the objects evicted,
     * the empty handles dropped, the values unswizzled, the most resident
     * bytes seen at a sweep's start. */
    int64_t sweeps;
    int64_t complete_sweeps;
    int64_t examined;
    int64_t evicted;
    int64_t dropped;
    int64_t unswizzled;
    int64_t max_before;
};

/* What eviction reads of the database, at a safe point. */
struct ev_env {
    struct ntable *nt;
    struct tnode *super_root;
    struct tnode *newest_written_top;
    struct ts_seq *d;           /* D, for the debug check */
};

/* new Eviction(BUDGET, seed, budget): budget at least 1 (BERGDB_NO_EVICT,
 * INT64_MAX, for none). */
void ev_init(struct ev *ev, struct obj_ctx *cx, struct mem *m, int64_t budget);

/* The large values' holds released and the list freed: for the close, also
 * after a failure (before close's walk). */
void ev_free(struct ev *ev);

/* Eviction.setBudget: the watermarks and the trigger; budget at least 1. */
void ev_set_budget(struct ev *ev, int64_t budget);

/* The resident bytes (above), from the allocator's counts. */
int64_t ev_resident_bytes(const struct mem *m, const struct ntable *nt);

/* Eviction.detachable: object o (in the node table, or a value) may go. */
bool ev_detachable(const struct node *o, const struct tnode *superRoot,
        const struct tnode *newestWrittenTop);

/* The capacity controller at a safe point (afterTransaction, afterLoad,
 * setBudget's wake): what is pending is freed, then sweeps while the
 * resident bytes are over the trigger and the last sweep freed something.
 * in_call: a safe point inside a call (between a getMany's pairs), where
 * what the call holds stays until the call ends: a floor found there lasts
 * for the call only. Allocates nothing. */
void ev_run(struct ev *ev, const struct ev_env *env, bool in_call);

/* Eviction.largeValueCreated: pointer index of holder to v, a value over
 * EV_LARGE_VALUE, kept counted until the record is written. false: NOMEM
 * (nothing kept). */
bool ev_large_value_created(struct ev *ev, struct knode *holder, int32_t index,
        struct vnode *v);

/* Eviction.recordWritten (the admission): after the record of tn is
 * written, the list's large values and those that the record's key nodes
 * hold become stream pointers; the list is emptied. */
void ev_record_written(struct ev *ev, const struct transnodes *tn);

/* Eviction.recordWritten as Db's start calls it, with the resident key
 * nodes as the written nodes (recordWritten(this, cache.nodes().iterator())):
 * the list's large values, those of the start's rerun (bergdb 015-68), and
 * the large values that the key nodes of nt's live handles hold, all with
 * their records in the stream, become stream pointers; the list is
 * emptied. The pass takes the values of the startup section's first
 * transaction, which the start does not rerun but links into the
 * section's node versions (starter.c's create_memory_pointers), so the
 * rerun's listener never put them on the list (bergdb 019-47, as Java's
 * since release 2026.4). Allocates nothing; the values let go are freed at
 * the next safe point. */
void ev_record_written_start(struct ev *ev, const struct ntable *nt);

/* The bytes of what is pinned, as the allocator counts them: each pinned
 * object (D's got-dirty nodes, the super root, the newest written top node)
 * once, with its handle and what its pointers hold (values and handles,
 * once per pointer), and the node table's arrays. A walk of D: for reports
 * and tests (bergdb_stats). */
int64_t ev_pinned_bytes(const struct ev_env *env);

/* The debug check: every pinned object (D's got-dirty nodes, the super root,
 * the newest written top node) is the object of its node's live handle.
 * Returns the number that are not (0: all right). For the test build and
 * the tests; between calls. */
int64_t ev_check_pins(const struct ev_env *env);

#endif
