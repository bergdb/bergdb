/*
 * sdb: a database opened by the bounded startup, for reads (bergdb 012-10,
 * part 1; docs/levels.md, Level 2): Db.startInner as starter.h ports it, on
 * a stream opened by the caller (a directory opened for writing, or a
 * stream in memory), then reads as Db's (getOne, getMany, getTrans) through
 * the readers' follower, which loads what is not in memory (ncoll.h). The
 * test vehicle of part 1 and bergdb-dump's way to open a database, until
 * 012-09's Db starts existing databases with starter.h (012-10 proper);
 * the full replay (replay.h) stays a test vehicle. Prefix sdb_.
 *
 * A start writes what Java's writes: recovery's fill after a crash (into
 * the stream's write buffer; the caller's stream_finish writes and forces
 * it, as Java's close). Nothing else is written: no transactions.
 *
 * Refused as unsupported (ERR_ARG, "UnsupportedOperationException"): an
 * empty stream, which Java's start creates (012-09). A database with
 * reclaim's table gets its first available position and time from it, and
 * a cut that the table marks but the files do not show is made, as Java's
 * initFromDb does (012-11).
 */
#ifndef BERGDB_SDB_H
#define BERGDB_SDB_H

#include <stdbool.h>
#include <stdint.h>
#include "dag.h"
#include "err.h"
#include "getmany.h"
#include "mem.h"
#include "ncoll.h"
#include "nstream.h"
#include "ntable.h"
#include "obj.h"
#include "rstream.h"
#include "starter.h"
#include "strans.h"
#include "transseq.h"

struct sdb {
    struct mem *mem;
    struct obj_ctx cx;
    struct stream *s;               /* the caller's, open while the database is */
    struct rs rs;
    struct ntable nt;
    struct ncoll nc;
    struct dag dag;
    bool dag_made;
    struct ts_seq ts;
    struct tnode *newest_written_top;   /* counted */
    int32_t max_node_size;
    struct rs_recovery plan;        /* what the recovery found and appended */
    struct sr_result start;         /* what the start set and read */
    int64_t last_trans_time;        /* DbClock.lastTransactionTime */
    int64_t first_available_pos;    /* reclaim's: 0 without its table */
    int64_t first_available_time;
    bool failed;                    /* a read failed on the storage: Db fails (005-30) */
    struct err failure;
    /* getTrans's record, valid until the next sdb_get_trans. */
    struct ns_iter gt;
    struct st_record gt_rec;
    bool gt_open;
};

/* Db.start on stream s with the start's node size (005-50): the checks, the
 * recovery, the bounded startup, initFromDb. Refused as Java's start
 * refuses (starter.h), or as unsupported (above). On an error everything is
 * freed (not the stream). check_link: linkToCanonical's check by node id,
 * as Java's under -ea (it reads a header per pointer). */
enum err_code sdb_open(struct sdb *d, struct stream *s, struct mem *m, int32_t max_node_size,
        bool check_link, struct err *e);

/* Frees everything but the stream (the caller finishes it). */
void sdb_close(struct sdb *d);

/* Db.newGetData, newGetMany: the readers' follower. */
void sdb_new_get_data(struct sdb *d, struct getdata *gd);
void sdb_new_get_many(struct sdb *d, struct getmany *g);

/* DbClock.lookupTime */
int64_t sdb_lookup_time(const struct sdb *d, int64_t wanted);

/* Db.getOneInternal: *out the value node (borrowed until the next call), or
 * NULL. A read that fails fails the database (ERR_IO or ERR_FORMAT,
 * "DbFailedException", 005-30); ERR_NOT_AVAILABLE before the first
 * available time. */
enum err_code sdb_get_one(struct sdb *d, int64_t lookup_time, const int64_t *key, int32_t n,
        struct getdata *gd, struct vnode **out, struct err *e);

/* Db.getMany: g made by sdb_new_get_many, its input set. */
enum err_code sdb_get_many(struct sdb *d, struct getmany *g, struct err *e);

/* Db.getTrans, as replay_get_trans. */
enum err_code sdb_get_trans(struct sdb *d, int64_t tpos, const struct st_record **out,
        struct err *e);

/* The recount (012-07, 6.4.1) from the database's roots; 0: all right. */
int64_t sdb_recount(struct sdb *d);

#endif
