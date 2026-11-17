/*
 * transseq: D, the transactions of the startup section, and the take,
 * ported from Java's bergdb.core.TransSeq, TransSeq.TransInfo and
 * StartupPos (bergdb 012-09, part 1; 012-02, sections 8.7 and 8.9; 007-07).
 * Prefix ts_.
 *
 * D is a list of transactions, oldest first, each with its position, its
 * record's last position, time and startup position, its record's own
 * bytes (ts_own_bytes: 48 and its value and delete nodes), and its
 * got-dirty nodes: the index nodes that got dirty in it, in order. The
 * list keeps the sums D (the got-dirty nodes) and O (the own bytes).
 *
 * The take (ts_take, TransSeq.take, the paced take since b8ac8a1): before
 * a record is written, it takes whole transactions from D, oldest first,
 * as many as the record's share and the deadline ask for, within a byte
 * budget, and gives the new startup position. In 64-bit integers, as
 * Java's since bergdb 005-79 (release 2026.2; bergdb 015-02): the share and
 * the dither in units of 2^-16. Until then Java's doubles, in Java's order.
 *
 * The got-dirty nodes are the caller's objects (012-07's index nodes),
 * which this module does not look into: each is held with its id and type
 * (Node.getId, getType, which never change), for the checksum. What a
 * node adds to a record, its size now and 16 bytes (TransSeq.recordBytes),
 * is the caller's to compute: the take asks for it through a function,
 * only when Java computes it. The take hands the transactions it took to
 * the caller, who adds their nodes to the record (top nodes to the top
 * array, key nodes to the key array, in the take's order, as Java's
 * TransNodesForMe) and frees them.
 *
 * Memory: each TransInfo and its array of got-dirty nodes, through the
 * allocator (MEM_STATE). One caller at a time.
 */
#ifndef BERGDB_TRANSSEQ_H
#define BERGDB_TRANSSEQ_H

#include <stdbool.h>
#include <stdint.h>
#include "err.h"
#include "mem.h"

/* A got-dirty node: the caller's object, its id and its type (NODE_TOP or
 * NODE_KEY, snode.h). */
struct ts_node {
    void *node;
    int64_t id;
    int32_t type;
};

/* TransSeq.TransInfo. */
struct ts_info {
    struct ts_info *next;
    int64_t tpos;           /* the record's position */
    int64_t lastPos;        /* the position of its last byte */
    int64_t tt;             /* its time */
    int64_t startupPos;     /* its startup position */
    int64_t ownBytes;       /* its own bytes, ts_own_bytes() */
    struct ts_node *gotDirtyNodes;  /* the index nodes that got dirty in it, in order */
    int32_t ndirty;
    int32_t cap;
};

/* TransSeq: D. */
struct ts_seq {
    struct mem *mem;
    struct ts_info *first;  /* the oldest; NULL if D is empty */
    struct ts_info *last;   /* the newest */
    int32_t size;
    int64_t dirtyCount;     /* D: the got-dirty nodes of the transactions */
    int64_t ownBytes;       /* O: the own bytes of their records */
};

/* An empty TransInfo (its fields 0, no nodes), allocated through m; NULL
 * on a failure. */
struct ts_info *ts_info_new(struct mem *m);

/* TransInfo.addGotDirtyNode: appends a node. ERR_NOMEM, and nothing
 * added. */
enum err_code ts_info_add_node(struct ts_info *info, struct mem *m, void *node, int64_t id,
        int32_t type, struct err *e);

/* Frees a TransInfo (not its next, nor the nodes' objects). NULL allowed. */
void ts_info_free(struct ts_info *info, struct mem *m);

/* Frees a chain of TransInfos linked by next, as the take returns. */
void ts_info_free_chain(struct ts_info *info, struct mem *m);

/* An empty TransSeq. */
void ts_init(struct ts_seq *s, struct mem *m);

/* Frees the TransInfos left in s. */
void ts_free(struct ts_seq *s);

bool ts_is_empty(const struct ts_seq *s);
int32_t ts_size(const struct ts_seq *s);

/* TransSeq.span: the newest tpos minus the oldest, 0 if D is empty. */
int64_t ts_span(const struct ts_seq *s);

/* TransSeq.add: info, which s then owns, as the newest. Its tpos must be
 * larger than the newest's: ERR_ARG ("IllegalArgumentException", Java's
 * text), and info stays the caller's. */
enum err_code ts_add(struct ts_seq *s, struct ts_info *info, struct err *e);

/* TransSeq.posOfTransBefore: the tpos of the last transaction with tpos
 * below 'limit', or -1. */
int64_t ts_pos_of_trans_before(const struct ts_seq *s, int64_t limit);

/* TransSeq.ownBytes: a record's own bytes, 48 and its value nodes' bytes. */
int64_t ts_own_bytes(int64_t valueBytes);

/* TransSeq.ditherFp: a number from 0 to 65,535 (in units of 2^-16 a number
 * in [0, 1)) from a stream position, the top 16 bits of SplitMix64's
 * finalizer (bergdb 005-79; a double until then). */
int32_t ts_dither_fp(int64_t pos);

/* TransSeq.shareFp: the take's share in units of 2^-16 of a node,
 * floor(D o S 2^16 / (O sd)), at most D 2^16, in 64-bit integers with a
 * 128-bit product (j_mulhi64) and two divisions of 128 by 64 bits
 * (ts_divlu), exact (bergdb 005-79; a double until then). D is the got-dirty
 * nodes of the section's transactions, o the record's own bytes, O the
 * section's own bytes, S the section's length (streamLength - currentSp)
 * and sd the startup distance. Outside the bounds, D or S not below 2^32 and
 * 2^47, o not below 2^31, or O or sd not positive, it is INT64_MAX
 * (Long.MAX_VALUE): the share is all of D. */
int64_t ts_share_fp(int64_t D, int64_t o, int64_t O, int64_t S, int32_t sd);

/* TransSeq.divlu: the quotient of the 128-bit unsigned number u1 2^64 + u0
 * by v, where u1 < v, both unsigned (asserted): Hacker's Delight, 2nd
 * edition, 9-4, with 64-bit words in two 32-bit digits, as Java's. Private
 * in Java; here for ts_share_fp and the unit tests. */
int64_t ts_divlu(int64_t u1, int64_t u0, int64_t v);

/* What a transaction's got-dirty nodes may add to a record
 * (TransSeq.recordBytes): each node's size now and 16. The caller's. */
typedef int64_t (*ts_cost_fn)(void *ctx, const struct ts_info *info);

/* TransSeq.take: takes transactions from D, oldest first, and returns the
 * new startup position: the tpos of the last one taken, or currentSp if
 * none (at once if D is empty).
 *
 *   hardSp = streamLength - max(2 * startupDistance, span())   (longs)
 *   share  = ts_share_fp(D, recordOwnBytes, O, streamLength - currentSp,
 *            startupDistance)                         (units of 2^-16)
 *   u      = ts_dither_fp(streamLength)               (units of 2^-16)
 *
 * A transaction of count got-dirty nodes ends the take when it begins after
 * hardSp, ((taken + count) << 16) > share and share - (taken << 16) <= u *
 * count, below 2^49 within the bounds (TransSeq.take's comment); or,
 * unless maxBytes is INT64_MAX (Long.MAX_VALUE), when bytes + cost(ctx,
 * info) > maxBytes. Else it is taken: removed from D, with the sums.
 *
 * The transactions taken are linked by next, oldest first, from *taken
 * (NULL if none), and are the caller's: it adds their nodes to the record
 * in that order and frees them (ts_info_free_chain). *ntaken is their
 * number. 'cost' may be NULL when maxBytes is INT64_MAX. Asserts that O is
 * above 0 when D has transactions. */
int64_t ts_take(struct ts_seq *s, int64_t currentSp, int64_t streamLength,
        int32_t startupDistance, int64_t recordOwnBytes, int64_t maxBytes, ts_cost_fn cost,
        void *ctx, struct ts_info **taken, int32_t *ntaken);

/* TransSeq.checksum: CRC32 (java.util.zip.CRC32) of the size, D and O,
 * and of each transaction's lastPos, tt, tpos, startupPos, ownBytes and
 * its nodes' types (a byte each) and ids, each long as 8 bytes
 * little-endian (MyChecksum.updateWithLong). */
int64_t ts_checksum(const struct ts_seq *s);

/* TransSeq.visitGotDirtyNodes: calls visit for each got-dirty node of the
 * transactions with tpos at most 'limit', oldest first, with the
 * transaction's tpos and lastPos. */
typedef void (*ts_visit_fn)(void *ctx, const struct ts_node *node, int64_t tpos,
        int64_t lastTpos);
void ts_visit_got_dirty_nodes(const struct ts_seq *s, int64_t limit, ts_visit_fn visit,
        void *ctx);

/* StartupPos: the startup position, and the one released for eviction. */
struct ts_startup_pos {
    int64_t startupPos;
    int64_t evictPos;
};

/* StartupPos(pos): pos not negative, else ERR_ARG
 * ("IllegalArgumentException"); released for eviction at once. */
enum err_code ts_startup_pos_init(struct ts_startup_pos *p, int64_t pos, struct err *e);

/* StartupPos.get. */
int64_t ts_startup_pos_get(const struct ts_startup_pos *p);

/* StartupPos.set: not released for eviction until
 * ts_startup_pos_release_for_evict. Asserts pos >= 0. */
void ts_startup_pos_set(struct ts_startup_pos *p, int64_t pos);

/* StartupPos.releaseForEvict. */
void ts_startup_pos_release_for_evict(struct ts_startup_pos *p);

#endif
