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
 * The take (ts_take, TransSeq.take, the paced take since f89846d): before
 * a record is written, it takes whole transactions from D, oldest first,
 * as many as the record's share and the deadline ask for, within a byte
 * budget, and gives the new startup position. Java's doubles, in Java's
 * order (c/readme.md, section 3, rule 8; -ffp-contract=off).
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

/* TransSeq.dither: a number in [0, 1) from a stream position, SplitMix64's
 * finalizer, exact. */
double ts_dither(int64_t pos);

/* The take's share: (double) dirtyCount * recordOwnBytes / ownBytes *
 * distance / startupDistance, each long or int converted to double where it
 * meets a double, left to right, as TransSeq.take's expression (with
 * distance = streamLength - currentSp, subtracted as longs). */
double ts_share(int64_t dirtyCount, int64_t recordOwnBytes, int64_t ownBytes,
        int64_t distance, int32_t startupDistance);

/* What a transaction's got-dirty nodes may add to a record
 * (TransSeq.recordBytes): each node's size now and 16. The caller's. */
typedef int64_t (*ts_cost_fn)(void *ctx, const struct ts_info *info);

/* TransSeq.take: takes transactions from D, oldest first, and returns the
 * new startup position: the tpos of the last one taken, or currentSp if
 * none (at once if D is empty).
 *
 *   hardSp = streamLength - max(2 * startupDistance, span())   (longs)
 *   share  = (double) D * recordOwnBytes / O * (streamLength - currentSp)
 *            / startupDistance                                  (doubles)
 *   u      = ts_dither(streamLength)
 *
 * A transaction of count got-dirty nodes ends the take when it begins
 * after hardSp, taken + count > share and share - taken <= u * count; or,
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
