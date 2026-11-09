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
 * window; and the cut made (stream_pretruncate) when the stream is durable
 * up to the length at the decision. Java's buffer thread forces the stream
 * within about 20 ms; C has no thread (012-01, 4.3), so it forces the
 * stream itself in the call that decides the cut, one force per cut, and
 * cuts there (012-11, 6.4, Q1: option B, Frans 2026-10-29). C's physical
 * cut so comes at other moments than Java's; the bytes from the decided cut
 * do not differ (012-01, 3.2 point 8; 012-02, C2).
 *
 * The table and the current row are StringMap texts (strmap.h): a row is 11
 * lines "name=value\n" in HashMap's order for these names, pCut, tEnd, cut,
 * pStart, tStart, lastKey, rewritten, pEnd, pSafe, done, kvCount, written
 * here directly (rc_row_text) so that the step's value transformation
 * needs no allocation; t_reclaim.c checks it against sm_serialize. Rows are
 * read back with sm_parse (IterationInfo.deserialize).
 *
 * Reclaim's settings, the retain duration and the internal fraction, are
 * kept in the stream (bergdb 015-87, as Java's since release 2026.3): the
 * internal KV RC_SETTINGS_KEY_NAME, "retain=<time units>\nfraction=<units
 * of 2^-16>\n", which rc_set_settings commits when a setting changes and
 * rc_init_from_db reads at every start; a stream without it runs with the
 * defaults, forever and 16,384. They are no settings of the open.
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
#define RC_ITERATION_DIVISOR INT64_C(4)     /* ITERATION_DIVISOR: a quarter of the retain
                                               duration; (long) (0.25 * d) until 005-79 */
#define RC_MIN_STEP_SIZE INT64_C(10000)     /* MIN_STEP_SIZE */
#define RC_MAX_STEP_SIZE INT64_C(16000)     /* MAX_STEP_SIZE */
#define RC_VALUE_NODE_BYTES 28              /* VALUE_NODE_BYTES */
/* The internal fraction in units of 2^-16, an int (bergdb 005-79, as Java's
 * since release 2026.2; a double until then): FRACTION_ONE units are 1, the
 * default is 0.25 exactly, and 0.001 and 0.90 round to 66 and 58,982. */
#define RC_FRACTION_ONE (1 << 16)           /* FRACTION_ONE */
#define RC_DEFAULT_INTERNAL_FRACTION 16384  /* DEFAULT_INTERNAL_FRACTION */
#define RC_MIN_INTERNAL_FRACTION 66         /* MIN_INTERNAL_FRACTION */
#define RC_MAX_INTERNAL_FRACTION 58982      /* MAX_INTERNAL_FRACTION */
#define RC_DEFAULT_STEP_RESERVE (INT64_C(4) << 20)  /* DEFAULT_STEP_RESERVE, 4 MiB */

/* The ikeys of the table and of the current row (TABLE_KEY_NAME,
 * CURRENT_KEY_NAME). */
#define RC_TABLE_KEY_NAME "/#i/dreclaim/-table.txt"
#define RC_CURRENT_KEY_NAME "/#i/dreclaim/-current.txt"
/* SETTINGS_KEY_NAME: reclaim's settings (015-87). */
#define RC_SETTINGS_KEY_NAME "/#i/dreclaim/-settings.txt"
/* The bytes of the settings' value at most: two lines of a long each. */
#define RC_SETTINGS_TEXT_CAP 64

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
    int64_t settingsKey[8];         /* Keys.toSegments(SETTINGS_KEY_NAME) */
    int32_t settingsKey_n;
    int32_t internalFraction;       /* in units of 2^-16 (005-79) */
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

/* checkRetainDuration: at least one second, else ERR_ARG
 * ("IllegalArgumentException"). */
enum err_code rc_check_retain_duration(int64_t d, struct err *e);

/* checkInternalFraction: in units of 2^-16, RC_MIN_INTERNAL_FRACTION to
 * RC_MAX_INTERNAL_FRACTION inclusive, else ERR_ARG
 * ("IllegalArgumentException"). db_set_reclaim_internal_fraction converts
 * the API's double. */
enum err_code rc_check_internal_fraction(int32_t units, struct err *e);

/* serializeSettings: the value of RC_SETTINGS_KEY_NAME for the settings,
 * "retain=<d>\nfraction=<f>\n", into buf (RC_SETTINGS_TEXT_CAP bytes),
 * NUL-terminated; returns its length. */
size_t rc_settings_text(int64_t retainDuration, int32_t internalFraction, char *buf);

/* setSettings (015-87): the settings checked (ERR_ARG); if they are those
 * in force, nothing; else, refused once the top node ordinals are used up
 * (db_refuse_if_top_ordinals_used), an internal transaction puts
 * RC_SETTINGS_KEY_NAME with both, and the fields are set after its commit,
 * so the next transaction uses them. A commit refused before its go point
 * (the clock, NOMEM) or failed after it leaves them as they were; a
 * failure has failed the database, and a start takes what the stream
 * holds. The caller has checked that the database is active. */
enum err_code rc_set_settings(struct db *db, int64_t retainDuration, int32_t internalFraction,
        struct err *e);

/* parseSettings (015-87): the settings from a value of RC_SETTINGS_KEY_NAME
 * (n bytes), which must be in the one form that rc_settings_text writes,
 * byte for byte: the two lines in their order, the numbers in range; any
 * other value is damage, or the settings of a later version, and is
 * refused: ERR_FORMAT, "InternalDataException", with Java's text (as far as
 * the error's text holds it, and the value's bytes as they are where Java
 * decodes them as UTF-8). ERR_NOMEM. Also for a start that reads the
 * database without a struct reclaim (sdb.h). */
enum err_code rc_settings_parse(struct mem *m, const char *value, size_t n,
        int64_t *retainDuration, int32_t *internalFraction, struct err *e);

/* Reclaim.fractionOf: floor(g * f / 2^16), the part f (in units of 2^-16,
 * 0 to 2^16 - 1) of g bytes, exact for every int64_t g without overflow
 * (bergdb 005-79). */
int64_t rc_fraction_of(int64_t g, int32_t f);

/* setStepReserve: at least 1, else ERR_ARG. */
enum err_code rc_set_step_reserve(struct reclaim *r, int64_t bytes, struct err *e);

/* transactionCompleted(t): called by db_execute after each transaction,
 * the database active; returns at once for an internal one. Anything but
 * ERR_OK is a failure after the user transaction's go point: the caller
 * fails the database with it (Db.fail). */
enum err_code rc_transaction_completed(struct db *db, const struct trans *t, struct err *e);

/* initFromDb: reclaim's settings (015-87; the defaults if the stream has
 * none), the table and the current row read back at the latest time, the
 * first available position and time from the cut row with the largest
 * pStart, and a cut that the table marks but the stream does not show yet
 * made. The database active; the start calls it last, before any
 * transaction. ERR_FORMAT ("InternalDataException") for bad settings (any
 * other form than rc_settings_text's, byte for byte: parseSettings) or a
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
