/*
 * replay: C's first reads of Java's databases, by a full replay of the
 * stream (bergdb 012-08; docs/levels.md, Level 1): a start as Java's
 * Db.startInner makes it, its checks and what it reports (StartInfo, the
 * status), but where Java reruns the startup section on the index nodes it
 * reads (012-10), every committed record from the creation on is applied
 * to a database in memory (mdb.h): its value and delete nodes as puts and
 * deletes at the record's time, in the record's order, which is the order
 * in which Java's transaction applied them. The Dag so made has the key
 * nodes Java's has, version for version (P2: restarts change none), so
 * every read at every time gives Java's answer; the nodes in memory are not
 * Java's after a start (that is 012-10). And getTrans (Db.getTrans), with
 * Java's refusals of positions (005-34, 005-43). Prefix replay_.
 *
 * Nothing is written. Java's start recovers a crashed stream first, the
 * zero fill of a torn record (012-02, 4.4); the replay takes recovery's
 * plan (rstream.h) instead: the length Java's stream has after the fill,
 * and the records before the torn one, which is all a read can see.
 *
 * Not a full replay, and refused as unsupported (ERR_ARG,
 * "UnsupportedOperationException", the reason in the text): an empty
 * stream, which Java's start creates (012-09); a cut stream, whose first
 * position is not 0 (reclaim's, 012-11; Level 3 needs Level 2); a database
 * with reclaim's table, whose first available time needs the table (012-11).
 */
#ifndef BERGDB_REPLAY_H
#define BERGDB_REPLAY_H

#include <stdbool.h>
#include <stdint.h>
#include "err.h"
#include "mdb.h"
#include "mem.h"
#include "meta.h"
#include "nstream.h"
#include "rstream.h"
#include "stream.h"
#include "strans.h"

struct replay {
    struct mem *mem;
    struct stream *s;           /* the caller's, open while the replay is */
    struct stream view;         /* s with its length cut at the torn record, for the walks:
                                   a copy of the struct that only reads (Java reads its
                                   stream after the fill, whose torn record is failed) */
    int32_t max_node_size;
    struct rs_recovery plan;    /* what Java's recovery would append */
    struct meta meta;           /* the in-memory meta block: the last valid one */
    struct mdb db;
    bool made;                  /* db made */
    bool failed;                /* a read failed on the storage: Db fails (005-30) */

    /* What Java's start reports. */
    int64_t length;             /* getStreamLength(): after recovery's fill */
    int32_t startup_distance;   /* getStartupDistance(): the meta block's */
    int64_t start_pos;          /* StartInfo.startPos: the startup position */
    int64_t start_time;         /* StartInfo.startTime: the startup section's first time */
    int32_t trans_count;        /* StartInfo.transCount: its records */
    int64_t last_pos;           /* StartInfo.lastPos: its last record's last byte */
    int64_t first_available_pos;        /* reclaim's: 0 without its table */
    int64_t first_available_time;       /* reclaim's: 0 without its table */

    /* The replay's own counts. */
    int64_t records;            /* committed records applied, the creation included */
    int64_t pairs;              /* value and delete nodes applied */

    /* getTrans's record: valid until the next replay_get_trans. */
    struct ns_iter gt;
    struct st_record gt_rec;
    bool gt_open;
};

/* Db.start on stream s, with the maximum node size of the start (005-50),
 * then the full replay. Refused as Java's start refuses, with Java's
 * exception: DatabaseNotCreatedException (005-33), StreamFormatException or
 * VersioningStreamException (another node size, 005-50; no valid meta
 * block; a walk's refusal; bad magic bytes, sr_bad_magic_bytes), the stream's
 * read errors; and the unsupported cases above. On an error the replay is
 * closed already. */
enum err_code replay_open(struct replay *r, struct stream *s, struct mem *m,
        int32_t max_node_size, struct err *e);

/* Frees what the replay holds (not the stream). */
void replay_close(struct replay *r);

/* Db.getTrans: the committed record at tpos, parsed, into *out (valid until
 * the next call). Refused as Java refuses: a position that cannot start a
 * record, negative, not a multiple of 8, in a meta block (ERR_ARG,
 * "IllegalArgumentException", 005-34), or at or past the end (005-43);
 * one before the stream's first position (ERR_NOT_AVAILABLE,
 * "LookupTimeNotAvailableException"); a read that fails or bytes that are
 * not a committed record fail the database (ERR_IO or ERR_FORMAT,
 * "DbFailedException", 005-30), as every later read. */
enum err_code replay_get_trans(struct replay *r, int64_t tpos, const struct st_record **out,
        struct err *e);

#endif
