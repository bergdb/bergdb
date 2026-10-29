/*
 * reclaim: stream space reclaim, Level 3, ported from Java's
 * bergdb.core.Reclaim (bergdb 012-11; 012-02, 8.13 and 9.4). Prefix rc_.
 *
 * As Java's: after each external transaction (rc_transaction_completed,
 * called by db_execute where Java's Db calls
 * Reclaim.transactionCompleted), a new iteration when the stream has grown
 * by twice the startup distance (the database's live one, 005-61) since
 * the last one started and a quarter of the retain duration has passed; a
 * step when the bytes rewritten so far are below the internal fraction of
 * the stream's growth since the iteration started: a scan of the pairs at
 * the iteration's start time after its last key (the maintenance follower,
 * which counts the index nodes it follows by id; the step reserve), the
 * live values stored before the cut point rewritten, the key range
 * touched (Trans.touch, db.c), and the row stored by a value
 * transformation, all in one internal transaction; the safe positions;
 * the cut decided when the last done, safe row ended before the retention
 * window; and the cut made (stream_pretruncate) at the first external
 * transaction at which the stream is durable up to the length at the
 * decision. With no thread, C's stream is durable after a sync and at the
 * close (012-01, 4.3), so C's physical cut comes at other moments than
 * Java's; the bytes from the decided cut do not differ (012-01, 3.2 point
 * 8; 012-02, C2).
 *
 * The table and the current row are StringMap texts (strmap.h): a row is 11
 * lines "name=value\n" in HashMap's order for these names, pCut, tEnd, cut,
 * pStart, tStart, lastKey, rewritten, pEnd, pSafe, done, kvCount, written
 * here directly (rc_row_text) so that the step's value transformation
 * needs no allocation; t_reclaim.c checks it against sm_serialize. Rows are
 * read back with sm_parse (IterationInfo.deserialize).
 *
 * Left out: Reclaim.Stats, the TouchCounter and recordWritten (statistics,
 * off unless enableStats(); no byte depends on them).
 */
#ifndef BERGDB_RECLAIM_H
#define BERGDB_RECLAIM_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include "err.h"
#include "mem.h"

struct db;
struct trans;

/* Reclaim's constants. */
#define RC_ITERATION_SPACING 0.25           /* ITERATION_SPACING */
#define RC_MIN_STEP_SIZE INT64_C(10000)     /* MIN_STEP_SIZE */
#define RC_MAX_STEP_SIZE INT64_C(16000)     /* MAX_STEP_SIZE */
#define RC_VALUE_NODE_BYTES 28              /* VALUE_NODE_BYTES */
#define RC_DEFAULT_INTERNAL_FRACTION 0.25   /* DEFAULT_INTERNAL_FRACTION */
#define RC_DEFAULT_STEP_RESERVE (INT64_C(4) << 20)  /* DEFAULT_STEP_RESERVE, 4 MiB */

/* The ikeys of the table and of the current row (TABLE_KEY_NAME,
 * CURRENT_KEY_NAME). */
#define RC_TABLE_KEY_NAME "/#i/dreclaim/-table.txt"
#define RC_CURRENT_KEY_NAME "/#i/dreclaim/-current.txt"

/* IterationInfo: a row of the table. */
struct rc_row {
    int64_t pStart;
    int64_t tStart;
    int64_t tEnd;
    int64_t kvCount;
    int64_t *lastKey;       /* the segments (owned, MEM_STATE); NULL with lastKeyNull */
    int32_t lastKey_n;
    bool lastKeyNull;       /* lastKey == null: none iterated yet */
    bool done;
    bool cut;
    int64_t rewritten;
    int64_t pEnd;           /* -1 until done */
    int64_t pSafe;          /* -1 until known */
    int64_t pCut;
};

struct reclaim {
    struct mem *mem;
    struct rc_row *rows;            /* IterationTable.rows */
    int32_t nrows;
    int32_t cap;
    int64_t tableKey[8];            /* Keys.toSegments(TABLE_KEY_NAME) */
    int32_t tableKey_n;
    int64_t currentKey[8];          /* Keys.toSegments(CURRENT_KEY_NAME) */
    int32_t currentKey_n;
    double internalFraction;
    int64_t retainDuration;         /* Long.MAX_VALUE: forever */
    int64_t stepReserve;
    int64_t firstAvailableLookupTime;
    int64_t firstAvailablePos;
    int64_t iterationCount;         /* iterations completed by this object */
    int64_t pendingCut;             /* a cut decided but not yet made, or -1 */
    int64_t pendingCutDurableAt;    /* the cut is made when this is durable */
    /* Statistics (a part of Java's Stats, for the tests): the steps made, and
     * those that the step reserve stopped (splitSteps). */
    int64_t steps;
    int64_t splitSteps;
};

/* new Reclaim(db, aos): no rows, retain forever, Java's defaults. */
void rc_init(struct reclaim *r, struct mem *m);

/* Frees the rows. */
void rc_free(struct reclaim *r);

/* setRetainDuration: at least one second, else ERR_ARG
 * ("IllegalArgumentException"). */
enum err_code rc_set_retain_duration(struct reclaim *r, int64_t d, struct err *e);

/* setInternalFraction: 0.001 to 0.90 inclusive (NaN passes, as Java's
 * comparisons let it), else ERR_ARG. */
enum err_code rc_set_internal_fraction(struct reclaim *r, double f, struct err *e);

/* setStepReserve: at least 1, else ERR_ARG. */
enum err_code rc_set_step_reserve(struct reclaim *r, int64_t bytes, struct err *e);

/* transactionCompleted(t): called by db_execute after each transaction,
 * the database active; returns at once for an internal one. Anything but
 * ERR_OK is a failure after the user transaction's go point: the caller
 * fails the database with it (Db.fail). */
enum err_code rc_transaction_completed(struct db *db, const struct trans *t, struct err *e);

/* initFromDb: the table and the current row read back at the latest time,
 * the first available position and time from the cut row with the largest
 * pStart, and a cut that the table marks but the stream does not show yet
 * made. The database active. ERR_FORMAT ("InternalDataException") for a
 * bad table; a read's errors as db_get_one's; ERR_NOMEM. */
enum err_code rc_init_from_db(struct db *db, struct err *e);

/* initFromDb's first available position and time from the table's text (n
 * bytes): the pCut and tEnd of the row marked cut with the largest pStart,
 * or 0 and 0. For a start that reads the database without a struct
 * reclaim (sdb.h). Errors as rc_table_parse's. */
enum err_code rc_first_available_of_table(struct mem *m, const char *s, size_t n, int64_t *pos,
        int64_t *time, struct err *e);

/* The bytes that rc_row_text may write for row (its NUL included). */
size_t rc_row_text_cap(const struct rc_row *row);

/* IterationInfo.serialize into buf (cap bytes, at least rc_row_text_cap):
 * the row's text, NUL-terminated; returns its length. */
size_t rc_row_text(const struct rc_row *row, char *buf, size_t cap);

/* IterationInfo.deserialize of n bytes of text into *row (whose lastKey it
 * allocates; rc_row_free frees it). ERR_FORMAT "InternalDataException" as
 * Java throws it; ERR_NOMEM. */
enum err_code rc_row_parse(struct mem *m, const char *s, size_t n, struct rc_row *row,
        struct err *e);

/* Frees a row's lastKey. */
void rc_row_free(struct mem *m, struct rc_row *row);

/* IterationTable.serialize: each row's text and "----next----\n", into a
 * buffer of the allocator's (MEM_BUFFER, *cap bytes, which the caller
 * frees); *n the text's length. ERR_NOMEM. */
enum err_code rc_table_text(const struct reclaim *r, char **out, size_t *n, size_t *cap,
        struct err *e);

/* IterationTable.parse: the rows of the text (split at "----next----", each
 * part trimmed, the empty ones skipped) appended to r's rows; none is
 * ERR_FORMAT ("InternalDataException"), as are bad rows. ERR_NOMEM. */
enum err_code rc_table_parse(struct reclaim *r, const char *s, size_t n, struct err *e);

#endif
