/*
 * bergdb.h: the API of BergDB's Core in C (bergdb item 012), the C
 * counterpart of the public methods of Java's bergdb.core.Db. Designed in
 * bergdb 012-03, whose section 6 maps every public method of Db, every
 * setting of DbBuilder and the inner types to what is here, or gives the
 * reason it is left out. Prefix bergdb_ (BERGDB_ for constants).
 *
 * The same database as Java's: a multiversion ordered map from (key, time)
 * to value, in one append-only stream, byte for byte Java's (012-01,
 * section 3). A database made by Java opens here, and one made here opens
 * in Java. Left out (012-01, section 1): replicas, encryption (an encrypted
 * database is refused with BERGDB_FORMAT), the upper layers (Pub API),
 * threads.
 *
 *
 * A. One caller at a time
 *
 * A database, with its transactions and read contexts, is used by one
 * thread at a time, as a FILE is: the library has no threads, no locks and
 * no global state (bergdb 010-01, P9). Different databases may be used by
 * different threads at the same time. What Java does in threads of its own
 * happens inside the calls (012-01, 4.2 and 4.3): the stream's write buffer
 * is written when it is full, at bergdb_sync and at bergdb_close, and
 * written and forced by a transaction that decides a reclaim cut; eviction
 * runs at the end of a transaction and after loads, as in Java. A database
 * that is not called does nothing (P3). A committed transaction is in the
 * stream's write buffer (10 MB) until bergdb_sync, bergdb_close, a reclaim
 * cut or a full buffer writes it to the files, and durable on the device
 * after bergdb_sync, bergdb_close or a reclaim cut, which force it
 * (F_FULLFSYNC); a process that dies loses what the buffer holds, never
 * what was synced (the C directory's readme.md, section 9: durability).
 *
 *
 * B. Errors
 *
 * Every function that can fail returns BERGDB_OK (0) or an error code
 * (enum bergdb_error); results come through pointers. Each code maps
 * Java's exceptions (012-03, section 6.5). bergdb_errmsg gives the text of
 * a database's last error, bergdb_errname a code's name; bergdb_open, which
 * has no database when it fails, writes its text into a buffer of the
 * caller's.
 *
 * As in Java (levels.md, section 3; P7), a transaction has a go point.
 * Before it, everything that may refuse the transaction is checked and
 * nothing changes: a refused transaction (BERGDB_RERUN, BERGDB_LIMIT,
 * BERGDB_ARG, BERGDB_STATE, BERGDB_NOMEM) leaves the database as it was,
 * and the database goes on. After it, nothing refuses the transaction and nothing
 * is undone: if something fails there (the storage, memory, a bug), the
 * database fails, and the call returns BERGDB_FAILED. A read that fails on
 * the storage (an I/O error, corrupt data) fails the database the same
 * way. A failed database appends nothing more, and every later
 * transaction and read returns BERGDB_FAILED; bergdb_errmsg then also
 * gives the first failure's text, which the database keeps. The caller
 * closes the database and opens it again: the open rebuilds it from the
 * stream, which holds whole records only, as after a crash; the failed
 * transaction is then there or not, as its record was appended or not. A
 * database in memory is lost, as in a crash.
 *
 * What a failed database still does: bergdb_close; bergdb_sync, for the
 * transactions before the failure, while the storage works; bergdb_stats;
 * bergdb_current_time and bergdb_lookup_time; the setter of the cache
 * size indicator (it only sets the value); making and freeing transactions
 * and read contexts, and building transactions; bergdb_errmsg. Everything
 * else returns BERGDB_FAILED, the setters of the retain duration and the
 * internal fraction too, which commit as a transaction does (015-87).
 *
 *
 * C. Ownership and lifetimes (012-01, 4.5)
 *
 * The caller owns:
 *
 *   - a database (bergdb_db), from a successful bergdb_open until
 *     bergdb_close, which frees all of its memory. After the close the
 *     pointer is not valid, as a FILE after fclose: a second bergdb_close,
 *     or any other call with it, uses freed memory (AddressSanitizer
 *     reports it in a test build); a caller that may close twice sets its
 *     pointer to NULL, which bergdb_close takes (012-13, Q2);
 *   - a transaction (bergdb_trans) and a read context (bergdb_read), from
 *     its _new function until its _free function. Each belongs to the
 *     database that made it, is used with that database only, and is
 *     freed before the database is closed: bergdb_close frees those still
 *     there, and they must not be used or freed after it;
 *   - its own memory: keys, values, options and ranges given to a call are
 *     read during the call only. A transaction keeps copies of its keys
 *     and values.
 *
 * Results that point to bytes (struct bergdb_one, bergdb_many,
 * bergdb_stored) point into their read context's buffer: valid until that
 * context's next call (bergdb_get_one, bergdb_get_many, bergdb_get_trans),
 * its free, or the database's close, whichever comes first. A read copies
 * the value it returns, as the index object that holds it may be evicted
 * and freed after the call.
 *
 * Pointers the database keeps: the options' clock_ctx and mem, until the
 * database is closed (mem also after it, for the counts); a transform's
 * ctx (struct bergdb_transform), while its transaction may be executed.
 *
 *
 * D. Callbacks
 *
 * The callbacks are the clock (bergdb_clock_fn), getMany's stop condition
 * (bergdb_stop_fn) and a put's key and value transformations (struct
 * bergdb_transform). The data a callback is given is valid during the
 * callback only. A callback must not call its database, or a transaction
 * or read context of it: such a call returns BERGDB_STATE and does
 * nothing (a free function does nothing; bergdb_close frees the object
 * later). The functions without a database (bergdb_errname, the key
 * conversions, the test clock) may be called. The clock and the
 * transformations cannot fail: the transformations run after the go
 * point, where nothing may refuse the transaction, and the clock's time is
 * checked when it returns.
 *
 *
 * E. Keys and values
 *
 * Keys are bkeys: byte strings, compared as unsigned bytes, a shorter key
 * before a longer one with the same start; the empty key is a key (no
 * ikey gives it). Every call that takes a key takes any bkey, as Java's
 * Core API does. The
 * library converts a bkey to segments as Java's Keys.toSegments(byte[]).
 * The Core's text keys are ikeys (UTF-8, "/" separates the parts of a
 * path), which bergdb_ikey_to_bkey converts as Java's Keys.toBytes(String);
 * bergdb_bkey_to_ikey converts back. An ikey is well-formed UTF-8, as
 * every string that BergDB stores, in every language (bergdb 021-04):
 * bergdb_ikey_to_bkey refuses other bytes, as Java refuses a String with a
 * lone surrogate (021-05); and bergdb_bkey_to_ikey refuses a bkey without
 * an ikey (021-06: one with the byte 0 or 0x31, or whose bytes converted
 * are not well-formed), so that two bkeys never give one ikey. Such a bkey
 * is reached by its bytes only. Values are byte strings of any length
 * up to the record limit. Keys and values are at most INT32_MAX bytes, as a
 * Java array. A key or value pointer given to a call is never NULL, also
 * for an empty key or value; a returned value pointer is NULL where Java's
 * value is null (no value: never put, or deleted), and not NULL for an
 * empty value.
 *
 * Keys and the layers above (bergdb 020-22; 010-01, P12), as Java's Db
 * says since release 2026.4. The Core takes any key and knows nothing of
 * the layers above it. A database of Java's Pub API (bergdb.pub) keeps its
 * data in the Core under keys of its own, and the Core does not stop
 * another writer there: a write through this library can break the Pub
 * API's data, as an edit of the database's files can. In a database that
 * the Pub API uses, a key is of one of three kinds, by its first bytes
 * (its bkey):
 *
 *   - Your keys: every key that does not start with the bytes 01 66, 01 2f
 *     or 01 25, the bkeys of "/d", "/-" and "/#": a key whose first byte
 *     is not 01, or the bkey of an ikey such as "/k1". BergDB never reads
 *     them for their meaning or changes them, in this release or a later
 *     one: the Core keeps them as any key (reclaim copies a live value
 *     forward, as it copies every value).
 *   - The Pub API's keys: the bkey of the ikey of a Pub key, such as
 *     "/da/-b" for "/a/b". A put or a delete there is allowed: the Pub
 *     API's reads check what they read. But only the Pub API's own writes
 *     keep its indexes. A put at an object key (no suffix, or ".obj") of a
 *     directory that has an index, building or active, can leave the value
 *     out of the index's scans until the key is written again through the
 *     Pub API (a put of its own bytes will do), or the index is deleted and
 *     created again: write such keys before the index is created, or make
 *     it again after. (A put that keeps what the index takes from the
 *     value, the fields of its levels, changes nothing in the index.) A
 *     delete there leaves an entry that scans skip. Any other key that
 *     starts with "/d" or "/-" is reserved.
 *   - BergDB's keys: every key that starts with "/#", among them the
 *     internal prefix "/#i/": reclaim's state and the Pub API's index
 *     definitions, entries and markers. Do not write them. Data there that
 *     does not parse is refused (InternalDataException; BERGDB_FORMAT
 *     here), at a start or at the read that meets it. Data that parses but
 *     that BergDB did not write makes values missing from an index's
 *     scans, or an index disappear, and in reclaim's keys it can lose data.
 *
 * A scan of an index never returns a value that does not match its query,
 * whatever was written through the Core: it checks each value against the
 * index (bergdb 020-10, section 3.4). Java's rule to write through Db while
 * no Database runs on the stream holds here by the directory's lock: this
 * library and Java do not open one directory at once (BERGDB_IN_USE). Of
 * BergDB's keys, this library writes reclaim's, under "/#i/dreclaim/", and
 * "/#i/-dummy" (bergdb_set_startup_distance), also in a database that no
 * Pub API uses: every key that starts with 01 25 is BergDB's in every
 * database. A range returns them, and the counters of bergdb_stats count
 * their transactions; a stop function that answers BERGDB_CONTINUE for a
 * key that starts with 01 25 leaves them out (bergdb 020-24-09, U9-4, as
 * Java's Db says since release 2026.4).
 *
 *
 * F. Time and the clock (012-01, 4.4)
 *
 * Times are Java's: 100 ns units since 1970-01-01 00:00 UTC (leap seconds
 * not counted), from 0 to BERGDB_MAX_TIME (2^56 - 1, about the year 2198);
 * BERGDB_UNITS_PER_SEC a second. Durations (the retain duration) are in
 * the same units; positions are byte positions in the stream; the startup
 * distance and the cache size indicator are bytes.
 *
 * The database's clock is a function of the options (Java's
 * DbBuilder.clock): by default the system clock, Java's SystemClock
 * (milliseconds since 1970 times 10,000); or the test clock of this
 * library (struct bergdb_test_clock, Java's CoreTestClock), a time that
 * the caller sets, forward only, so that times and bytes are
 * deterministic; or a function of the caller's. Java's DbClock is ported
 * exactly:
 *
 *   - The clock is read when the database is created (the time of the
 *     primordial transaction), at each bergdb_execute (also of the dummy
 *     transaction of bergdb_set_startup_distance, and of reclaim's
 *     transactions, which run within a user transaction), and by
 *     bergdb_current_time. Nothing else reads it.
 *   - A transaction's time is the clock's time, but later than the last
 *     transaction's time and than the last time bergdb_current_time
 *     returned. So a call of bergdb_current_time can move the next
 *     transaction's time when the clock has not moved since. The clock may
 *     go back: bergdb_current_time's times never decrease (bergdb 020-23,
 *     Z1, as Java's since release 2026.4).
 *   - A clock time outside 0 to BERGDB_MAX_TIME, or no time left after the
 *     last transaction's, refuses the transaction (BERGDB_LIMIT; 005-18).
 *     So is an open that creates a database, as it writes the database's
 *     first transaction; an open of an existing database does not read the
 *     clock, and succeeds, and its transactions are refused while the
 *     clock is outside the range (as Java's Clock says since 2026.4,
 *     020-23, Z3).
 *   - A lookup time is clamped to the last transaction's time
 *     (bergdb_lookup_time); BERGDB_LATEST reads the latest state.
 *
 *
 * G. What bergdb_open creates
 *
 * A database is a directory, as with Java's FileStream, or a stream in
 * memory (dir NULL), which is lost at the close. In a directory, the open
 * creates the directory and its missing parents, as Java's FileStream
 * does, and the lock file bergdb.lock (kept; locked while a database has
 * the directory open, so that the open of another process, C's or Java's,
 * is refused with BERGDB_IN_USE: 005-63). Within one process, open a
 * directory once: the lock is the process's (POSIX), so a second open in
 * the same process is not refused, and its close releases the first
 * open's lock (012-13's decision, after 012-09, 6.4: no global state, P9).
 * When the stream is empty (no .bergdb file), the open creates the
 * database, as Java's start does: the first meta block and the primordial
 * transaction (264 bytes), the database id of the options (random by
 * default) and the clock's time; the first .bergdb file holds them from
 * the first write (a sync, the close; 015-06), so a refused creation
 * (BERGDB_LIMIT) leaves only bergdb.lock. It writes no
 * created.txt (the Pub API's). On an existing database, the open reads the
 * stream's tail and rebuilds the database in memory (bounded startup); it
 * may write what Java's start writes: the zero fill of a torn last record.
 */
#ifndef BERGDB_H
#define BERGDB_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>

#ifdef __cplusplus
extern "C" {
#endif


/* ======== Errors ======== */

/*
 * The error codes. Each maps Java's exceptions (012-03, section 6.5); a
 * code is a refusal, after which the database goes on, but for
 * BERGDB_FAILED and the codes of bergdb_open and bergdb_close.
 */
enum bergdb_error {
    BERGDB_OK = 0,
    /* A key of the transaction's read set was changed after its lookup
     * time (Java's RerunException, the STM's conflict): the transaction is
     * refused; read again and run a new one. */
    BERGDB_RERUN = 1,
    /* The lookup time is before the first available lookup time, or the
     * transaction asked for has been removed by reclaim
     * (LookupTimeNotAvailableException). */
    BERGDB_NOT_AVAILABLE = 2,
    /* The database has failed, before or in this call (DbFailedException;
     * section B): close it and open it again. */
    BERGDB_FAILED = 3,
    /* An I/O error at the open or the close: the directory or a file could
     * not be made, read, written or forced (StreamIoException, IOException
     * of FileStream). After the open, an I/O error fails the database
     * (BERGDB_FAILED). */
    BERGDB_IO = 4,
    /* The stream is not a BergDB stream that this version opens: another
     * record format or meta block version, a database written before
     * 2026-10-27, another maximum node size than the options', an
     * encrypted database, corrupt data, foreign files in the directory
     * (StreamFormatException, also for bad magic bytes, which was
     * BadCryptoKey until release 2026.4, bergdb 020-28;
     * VersioningStreamException, StreamChecksumException,
     * InternalDataException, BadDirStateException). At the open only;
     * after it, corrupt data fails the database. */
    BERGDB_FORMAT = 5,
    /* A call from a callback of the same database (section D)
     * (IllegalDbStateException, DbStoppingException). */
    BERGDB_STATE = 6,
    /* A bad argument: NULL, a length over INT32_MAX, a value out of the
     * allowed range, a position that is not a transaction's, an object of
     * another database (IllegalArgumentException). */
    BERGDB_ARG = 7,
    /* A limit of the database refuses the transaction: its values and
     * keys, or the index nodes it can make dirty, would not fit in a
     * record (005-17, 005-31); the top node ordinals are used up (005-02);
     * the clock's time is out of range, or no time is left (005-18)
     * (Java's DbException). */
    BERGDB_LIMIT = 8,
    /* The directory holds an incomplete creation and no committed
     * transaction (DatabaseNotCreatedException, 005-33): remove its
     * .bergdb files and open again, which creates the database. */
    BERGDB_NOT_CREATED = 9,
    /* A database of another process, C's or Java's, holds the directory
     * (DirectoryInUseException, 005-63): open it when that one is closed.
     * Within one process a directory is opened once (section G): a second
     * open there is not detected. */
    BERGDB_IN_USE = 10,
    /* Out of memory (OutOfMemoryError). A refusal; after a transaction's
     * go point, a failure (BERGDB_FAILED). */
    BERGDB_NOMEM = 11
};

typedef struct bergdb_db bergdb_db;         /* a database (Java's Db) */
typedef struct bergdb_trans bergdb_trans;   /* a transaction (Trans.Builder, Trans) */
typedef struct bergdb_read bergdb_read;     /* a read context (GetData, GetMany) */

/*
 * The text of the last error of a call on db or on one of its
 * transactions or read contexts; "" if that call succeeded. After
 * BERGDB_FAILED, the text includes the first failure's. The string is
 * db's: valid until the next call on db. db NULL gives "". The text, and
 * that of bergdb_open's error buffer, begins with the simple name of the
 * exception that Java throws in the same case and ": " ("DbException: The
 * transaction is too large: ..."), so that a tool can print Java's name, as
 * bergdb-run prints Run's "error=NAME" (012-09).
 */
const char *bergdb_errmsg(const bergdb_db *db);

/* The name of a code, such as "BERGDB_RERUN"; "BERGDB_UNKNOWN" for another
 * number. A constant string. */
const char *bergdb_errname(int code);


/* ======== Time ======== */

#define BERGDB_UNITS_PER_SEC INT64_C(10000000)          /* Clock.UNITS_PER_SEC */
#define BERGDB_MIN_TIME INT64_C(0)                      /* Klong.MIN_TIME */
#define BERGDB_MAX_TIME INT64_C(0x00ffffffffffffff)     /* Klong.MAX_TIME, 2^56 - 1 */
#define BERGDB_LATEST INT64_MAX     /* the lookup time of the latest state, Long.MAX_VALUE */
#define BERGDB_FOREVER INT64_MAX    /* the retain duration "forever", a new database's */
#define BERGDB_NULL_POS INT64_C(-1) /* no position (Spos.NULL) */

/*
 * A clock (Java's Clock.getTime): the time now, in 100 ns units since 1970,
 * from ctx. Its times must not decrease. It cannot fail; a time outside 0
 * to BERGDB_MAX_TIME refuses the transaction that reads it (BERGDB_LIMIT).
 * It must not call the database (section D).
 */
typedef int64_t (*bergdb_clock_fn)(void *ctx);

/*
 * The test clock (Java's CoreTestClock): a time that the caller sets and
 * that does not move by itself; 0 at first. Owned by the caller, who
 * initializes it to {0} and gives bergdb_test_clock_time as the clock and
 * the struct as its ctx. It must stay valid while a database uses it; it
 * may serve several databases in turn (a restart keeps its time).
 */
struct bergdb_test_clock {
    int64_t time;
};

/* The test clock's time (CoreTestClock.getTime): a bergdb_clock_fn whose
 * ctx is a struct bergdb_test_clock. */
int64_t bergdb_test_clock_time(void *ctx);

/* Sets the test clock (CoreTestClock.setTime). BERGDB_ARG, and no change,
 * unless time is later than its time. */
int bergdb_test_clock_set(struct bergdb_test_clock *clock, int64_t time);


/* ======== Memory ======== */

/*
 * The counts of the library's allocator (012-01, 4.5; src/mem.h), for a
 * caller that gives its own struct in the options (bergdb_options.mem):
 * the live bytes, in all and by kind, which the memory budget and the
 * tests' leak checks use; and fail_at, which makes allocation number
 * fail_at (1 is the first) fail, for the allocation-failure runs. Without
 * one, the database keeps its counts to itself. Owned by the caller, who
 * sets it to {0} before its first use; the database updates it during its
 * calls, from the open to the close, and counts all of its memory there:
 * its state, its transactions and read contexts, and their buffers. After
 * the close, live_total is 0. It may serve several databases in turn (a
 * restart), and the counts carry over.
 */
enum bergdb_mem_kind {
    BERGDB_MEM_INDEX,   /* index objects: key nodes, top nodes */
    BERGDB_MEM_VALUE,   /* values held by index objects */
    BERGDB_MEM_HANDLE,  /* handles */
    BERGDB_MEM_TABLE,   /* the node table */
    BERGDB_MEM_BUFFER,  /* buffers: the write buffer, read buffers */
    BERGDB_MEM_CALLER,  /* the caller's objects: transactions, read contexts */
    BERGDB_MEM_STATE,   /* the database's own state: D, reclaim's, the settings */
    BERGDB_MEM_KINDS
};

struct bergdb_mem {
    int64_t live[BERGDB_MEM_KINDS]; /* live bytes by kind */
    int64_t live_total;             /* live bytes in all */
    int64_t peak_total;             /* the largest live_total so far */
    int64_t live_blocks;            /* live blocks */
    int64_t allocs;                 /* allocations asked for, with reallocs and failures */
    int64_t failed;                 /* allocations that failed, made to or not */
    int64_t fail_at;                /* allocation number fail_at fails; 0: none */
};


/* ======== Opening and closing ======== */

#define BERGDB_ID_SIZE 16           /* DatabaseId: 16 bytes */
#define BERGDB_NO_EVICT INT64_MAX   /* the cache size indicator of DbBuilder.noEvict() */
#define BERGDB_ERRBUF_SIZE 512      /* the size of bergdb_open's error buffer */

/* Java's DatabaseId.TEST_ID, for bergdb_options.id (DbBuilder.testId()):
 * deterministic bytes. */
extern const uint8_t bergdb_test_id[BERGDB_ID_SIZE];

/*
 * The settings of an open (Java's DbBuilder). bergdb_options_init sets
 * Java's defaults, given here; bergdb_open checks each as Java's builder
 * does. The settings that DbBuilder has for tests only (audit, eviction
 * schedules, the step reserve, the second top ordinal), the streams'
 * buffers and created.txt are left out (012-03, section 6.3).
 */
struct bergdb_options {
    /* The maximum node size: 8, 14, 30 or 62 (maxNodeSize8() ...
     * maxNodeSize62()); 30 by default, the Pub API's. It is in the stream
     * from the creation, and an open with another one is refused
     * (BERGDB_FORMAT; 005-50). */
    int32_t max_node_size;
    /* The startup distance in bytes (startupDistance(int)): at least 10;
     * 50,000,000 by default. A setting in the stream: an existing database
     * uses the stream's (its meta blocks'), and bergdb_set_startup_distance
     * changes it, to a value that it clamps to a narrower range (015-76). */
    int32_t startup_distance;
    /* The cache size indicator in bytes, the memory budget
     * (cacheSizeIndicator(long)): 200,000,000 by default; BERGDB_NO_EVICT
     * for no eviction. For this run only (005-52). Under 1: BERGDB_ARG,
     * "IllegalArgumentException: Bad cacheSizeIndicator: N.", DbBuilder's
     * check (bergdb 020-27, C3; before, Cache3.setSizeIndicator's
     * "AssertionError"). The index's resident bytes (bergdb_stats) are kept
     * at most this, but for what must stay: the nodes changed since the
     * startup position and the newest top nodes (Level 4, 012-12). */
    int64_t cache_size_indicator;
    /* The clock (clock(Clock)): NULL for the system clock (the default,
     * Java's SystemClock), or a function and its ctx: the test clock's
     * (bergdb_test_clock_time and a struct bergdb_test_clock) or the
     * caller's. ctx must stay valid until the close. */
    bergdb_clock_fn clock;
    void *clock_ctx;
    /* The database id, for a database that the open creates (id(DatabaseId);
     * ignored for an existing one): all zeros (the default) for a random
     * id, as Java's; bergdb_test_id for Java's test id (testId()); or any
     * other 16 bytes. */
    uint8_t id[BERGDB_ID_SIZE];
    /* The allocator's counts (C's; struct bergdb_mem): NULL (the default),
     * or the caller's struct, which must stay valid until the close. */
    struct bergdb_mem *mem;
};

/* Sets opt to Java's defaults (DbBuilder's constructor). */
void bergdb_options_init(struct bergdb_options *opt);

/* What the open read (Java's StartInfo, start()'s result). */
struct bergdb_start_info {
    int64_t start_pos;          /* startPos: the startup position, where the open read from */
    /* startupDistance: the startup distance in force after the open, the
     * stream's setting at a restart (bergdb 005-73, F1, as Java's since
     * release 2026.2; -1 before), as bergdb_stats' */
    int32_t startup_distance;
    int64_t start_time;         /* startTime: the time of the first transaction read */
    int32_t trans_count;        /* transCount: the transactions read */
    int64_t last_pos;           /* lastPos: the last byte of the last transaction read */
};

/*
 * Opens the database in the directory dir, or a new one in memory if dir
 * is NULL, and starts it: Java's Db.builder() with the options, build()
 * and start(). What it creates: section G. opt NULL gives the defaults.
 * On success, *db is the database (the caller's until bergdb_close), and
 * *info, if info is not NULL, what the start read. On a failure, *db is
 * NULL and nothing is left open (no file, no lock, no memory). errbuf is
 * NULL or BERGDB_ERRBUF_SIZE bytes of the caller's: the error's text, or
 * "" after a success.
 *
 * Errors: BERGDB_ARG (db NULL; a setting out of range: the node size, a
 * startup distance under 10);
 * BERGDB_IN_USE (another process); BERGDB_IO; BERGDB_FORMAT; BERGDB_NOT_CREATED;
 * BERGDB_LIMIT (the clock's time out of range at the creation);
 * BERGDB_NOMEM. Java's start throws DbFailedException when the read of
 * reclaim's table or settings fails on the storage; here that is
 * BERGDB_IO or BERGDB_FORMAT, as no database is left to fail. Reclaim's
 * settings in any other form than the one the setters write are
 * BERGDB_FORMAT, "InternalDataException" (015-87).
 */
int bergdb_open(const char *dir, const struct bergdb_options *opt, bergdb_db **db,
        struct bergdb_start_info *info, char *errbuf);

/*
 * Closes the database (Java's close(), and stop(), which is the same here):
 * writes what is buffered, forces it to the device (F_FULLFSYNC, as Java's
 * force(true) on macOS), closes the files, releases the directory's lock,
 * and frees all of the database's memory, the transactions and read
 * contexts not yet freed with it. Works on a failed database too; then it
 * writes what the records before the failure left in the buffer. db NULL
 * does nothing.
 *
 * Returns BERGDB_OK, or BERGDB_IO if the last write or force failed, or
 * the storage had failed before (the stream takes no write after a
 * failure): the database is closed and freed all the same, and
 * transactions that no sync had made durable may be lost; the code has no
 * text, as the database is gone. Java's close() does not report it
 * (012-03, 6.8). BERGDB_STATE from a callback, and nothing is closed.
 * After the close, db is not valid (section C): Java's second close() is
 * harmless and its calls after a close throw IllegalDbStateException, while
 * here the handle is gone (012-13, Q2).
 */
int bergdb_close(bergdb_db *db);


/* ======== Keys ======== */

/*
 * Converts an ikey to its bkey (Java's Keys.toBytes(String), on the
 * string's UTF-8 bytes): "/" becomes the byte 1, every other byte b
 * becomes b + 2. ikey has len bytes, and so has bkey; they may be the same
 * buffer. BERGDB_ARG, with nothing written, for the empty key (Java: "The
 * empty string is not a valid key"), for bytes that are not well-formed
 * UTF-8 (RFC 3629: a cut sequence, an overlong form such as C0 80, a
 * surrogate such as ED A0 80, a value above U+10FFFF, the bytes C0, C1 and
 * F5 to FF), as Java refuses a String with a lone surrogate (section E;
 * bergdb 021-05), for len over INT32_MAX, or a NULL pointer.
 */
int bergdb_ikey_to_bkey(const uint8_t *ikey, size_t len, uint8_t *bkey);

/*
 * Converts a bkey to its ikey's bytes (Java's Keys.bkey2ikeyOrNull, before
 * its UTF-8 decoding): the byte 1 becomes "/", every other byte b becomes
 * b - 2. bkey and ikey have len bytes and may be the same buffer.
 * BERGDB_ARG, where Java returns null, for a bkey without an ikey (section
 * E; bergdb 021-06): one with the byte 0 or 0x31 ("/" + 2, which no ikey
 * gives, "/" being 1), or whose bytes so converted are not well-formed
 * UTF-8 (as bergdb_ikey_to_bkey); and for len over INT32_MAX or a NULL
 * pointer. ikey may then be partly written, and so may bkey when they are
 * the same buffer. Else the ikey's bkey is bkey: two bkeys never give one
 * ikey. The empty bkey gives the empty ikey, as Java's "" (which
 * bergdb_ikey_to_bkey refuses).
 */
int bergdb_bkey_to_ikey(const uint8_t *bkey, size_t len, uint8_t *ikey);


/* ======== Transactions ======== */

/*
 * Makes a transaction for db (Java's db.trans(), a Trans.Builder): empty,
 * with no read set and the lookup time BERGDB_LATEST. The caller owns it
 * until bergdb_trans_free (section C). The transaction is the builder:
 * bergdb_execute builds and executes it, and it can be executed again,
 * also after more puts, as a Java builder can be built again.
 *
 * Errors: BERGDB_ARG (NULL), BERGDB_STATE, BERGDB_NOMEM.
 */
int bergdb_trans_new(bergdb_db *db, bergdb_trans **t);

/* Frees a transaction. NULL does nothing. */
void bergdb_trans_free(bergdb_trans *t);

/*
 * Puts the value for the key (Trans.Builder.put(byte[], byte[])). The
 * transaction copies both. At the execute, the puts and deletes are sorted
 * by key, and for a key given several times the last one counts, but a
 * delete does not replace a put (Trans.Builder.build).
 *
 * Errors: BERGDB_ARG (t, key or value NULL, also when its length is 0: an
 * empty key or value has a pointer too; a length over INT32_MAX),
 * BERGDB_STATE, BERGDB_NOMEM; the transaction is then as before. The
 * transaction's size is checked at the execute.
 */
int bergdb_trans_put(bergdb_trans *t, const uint8_t *key, size_t key_len,
        const uint8_t *value, size_t value_len);

/*
 * A put's key and value transformations (Java's KeyTransformation and
 * ValueTransformation), called by bergdb_execute after the transaction's
 * go point, with the transaction's time, tt: for a key or a value that is
 * known only then, such as one with the time in it, or a counter
 * incremented without a read set. Either function may be NULL. They
 * cannot fail and must not call the database (section D); they may keep
 * state in ctx.
 *
 * key: *key and *key_len are the put's key; the function may set them to
 * another key. The key's write hash becomes the new key's, as Java's one
 * user (the Pub API's) sets it. It runs before the value function, whose
 * previous value is then the new key's.
 *
 * value: *value and *value_len are the put's value, and previous the
 * key's value before the transaction (NULL if none); the function may set
 * them to another value, or *value to NULL, which makes the put a delete,
 * as Java's null.
 *
 * What a function sets must stay valid until it is called again or the
 * execute returns; the transaction copies it, and keeps it in place of the
 * put's key or value, as Java's Kv does: executed again, the transaction
 * starts from the transformed key and value.
 *
 * What they set is not size-checked (bergdb 015-51, as Java's Javadoc
 * since release 2026.3): bergdb_execute checks the transaction's size
 * before the go point (BERGDB_LIMIT, 005-17) with each put's key and value
 * as given, before the functions run. A transformed key and value must
 * keep the transaction's value nodes, with its other puts, within the
 * value limit, 7/8 of the record limit (about 1.88 GB), as a key and value
 * given directly must. A larger result is the caller's fault: one whose
 * record does not fit the record limit fails the database (BERGDB_FAILED)
 * when the record is made, and the transaction is not in the stream.
 */
struct bergdb_transform {
    void (*key)(void *ctx, int64_t tt, const uint8_t **key, size_t *key_len);
    void (*value)(void *ctx, int64_t tt, const uint8_t *previous, size_t previous_len,
            const uint8_t **value, size_t *value_len);
    void *ctx;
};

/*
 * Puts the value for the key with transformations
 * (Trans.Builder.put(long[], KeyTransformation, byte[], ValueTransformation)).
 * tf is copied; tf->ctx must stay valid while the transaction may be
 * executed. tf NULL is bergdb_trans_put. Errors as bergdb_trans_put.
 */
int bergdb_trans_put_transformed(bergdb_trans *t, const uint8_t *key, size_t key_len,
        const uint8_t *value, size_t value_len, const struct bergdb_transform *tf);

/* Deletes the key's value (Trans.Builder.delete(byte[])). A delete of a
 * key that has no value writes nothing for it. Errors as bergdb_trans_put. */
int bergdb_trans_delete(bergdb_trans *t, const uint8_t *key, size_t key_len);

/*
 * Adds the key to the transaction's read set (Trans.Builder.keyRead): the
 * execute is refused with BERGDB_RERUN if a transaction after the lookup
 * time (bergdb_trans_lookup_time) changed the key, or the time is outside
 * the STM's coverage, including before the last recovered commit at open
 * (bergdb 005-70, option A). Errors as
 * bergdb_trans_put.
 */
int bergdb_trans_key_read(bergdb_trans *t, const uint8_t *key, size_t key_len);

/*
 * Sets the lookup time of the read set (Trans.Builder.lookupTime), the
 * time at which the caller read the keys of the read set; BERGDB_LATEST,
 * the default, never conflicts. BERGDB_ARG for a negative time, or t NULL.
 */
int bergdb_trans_lookup_time(bergdb_trans *t, int64_t time);

/* What an executed transaction gives (Trans's output fields). */
struct bergdb_executed {
    int64_t tt;             /* the transaction's time */
    int64_t tpos;           /* the position of its first byte */
    int64_t last_pos;       /* the position of its last byte, its commit byte */
    int64_t next_pos;       /* the position of the next transaction's first byte */
    int64_t startup_pos;    /* the startup position stored with it (Trans.startupPos) */
    int32_t node_count;     /* the nodes its record holds (Trans.nodeCount) */
};

/*
 * Executes the transaction on db (Java's execute(Trans) and
 * execute(Trans.Builder)): its puts and deletes at one new time, atomic,
 * with the STM check of its read set. An empty transaction is executed
 * too. On BERGDB_OK, the transaction is committed and *out, if out is not
 * NULL, says where; durable after a sync (section A).
 *
 * Refusals, which leave the database as it was (section B): BERGDB_ARG (a
 * NULL, or t of another database), BERGDB_STATE, BERGDB_RERUN,
 * BERGDB_LIMIT, BERGDB_NOMEM. BERGDB_FAILED: the database had failed, or
 * fails now (a read of the warm-up failed on the storage, or anything
 * after the go point failed, also out of memory); whether this
 * transaction is in the stream is known after the next open.
 */
int bergdb_execute(bergdb_db *db, bergdb_trans *t, struct bergdb_executed *out);


/* ======== Reads ======== */

/*
 * Makes a read context for db (Java's newGetData() and newGetMany()): it
 * holds the results of its last read, which point into its buffer (section
 * C). The caller owns it until bergdb_read_free. One context serves
 * bergdb_get_one, bergdb_get_many and bergdb_get_trans, one call at a
 * time; to keep two results at once, use two contexts.
 *
 * Errors: BERGDB_ARG (NULL), BERGDB_STATE, BERGDB_NOMEM.
 */
int bergdb_read_new(bergdb_db *db, bergdb_read **rd);

/* Frees a read context and its results. NULL does nothing. */
void bergdb_read_free(bergdb_read *rd);

/* What bergdb_get_one gives (getOne's value and GetData's output fields). */
struct bergdb_one {
    /* The value at the lookup time, in the read context's buffer; NULL if
     * none (never put, or deleted: Java's null). An empty value is not
     * NULL. */
    const uint8_t *value;
    size_t value_len;
    /* GetData.kvTime, when value is not NULL: the time of the key node entry
     * that points to the value, not the time of the write, but the time of
     * the transaction that made the entry, the write's or a later one, as
     * Java's says since release 2026.4 (bergdb 021-19). A transaction that
     * replaces a full key node, by a time split or a space split, makes
     * every entry that the node keeps anew, at its own time, also those of
     * keys that it does not write; and reclaim, which copies a value
     * forward, writes it anew (see tpos). So the time is at or after the
     * time of the write and at or before the lookup time, and two reads of a
     * value that did not change, at lookup times before and after such a
     * transaction, may give two times. For the time of the write, read the
     * transaction: bergdb_get_trans of tpos, its tt (for a value that
     * reclaim has copied, the step's). No exact value time exists (bergdb
     * 011-01, Q9). */
    int64_t time;
    /* GetData.tpos, when value is not NULL: the position of the transaction
     * that stored the value, for bergdb_get_trans: the transaction that
     * wrote it, or, for a value that reclaim has copied forward, reclaim's
     * step, whose time is the step's (bergdb 021-19). A get of the key at
     * the step's time less one, while that time can be read, gives the same
     * value and the position of the transaction that stored it before, the
     * write's or an earlier step's (bergdb 021-17). */
    int64_t tpos;
    int64_t actual_lookup_time;  /* GetData.actualLookupTime (bergdb_lookup_time) */
};

/*
 * Reads the key's value at the lookup time (Java's getOne): the value of
 * the last transaction at or before the lookup time that put or deleted
 * the key. lookup_time BERGDB_LATEST reads the latest state.
 *
 * Errors: BERGDB_ARG (a NULL, a key over INT32_MAX bytes, rd of another
 * database), BERGDB_STATE, BERGDB_NOT_AVAILABLE (the lookup time is before
 * the first available lookup time, also when a cut has overtaken the
 * read), BERGDB_FAILED (the database had failed, or the read failed on
 * the storage now, which fails it), BERGDB_NOMEM (the database goes on).
 * On an error, *out is not set.
 */
int bergdb_get_one(bergdb_db *db, bergdb_read *rd, int64_t lookup_time,
        const uint8_t *key, size_t key_len, struct bergdb_one *out);

/*
 * A pair that getMany found (Java's Kvt), and a value node of a stored
 * transaction (bergdb_get_trans). key and value point into the read
 * context's buffer, or, given to a stop condition, into the database's
 * memory during the callback only.
 */
struct bergdb_kvt {
    const uint8_t *key;     /* the bkey */
    size_t key_len;
    const uint8_t *value;   /* the value; NULL for a delete (bergdb_get_trans only) */
    size_t value_len;
    /* getMany: Kvt.time, the time of the key node entry that points to the
     * value, not the time of the write, but at or after it and at or before
     * the lookup time, as bergdb_one.time says (bergdb 021-19). For the time
     * of the write: bergdb_get_one of the key at the read's
     * actual_lookup_time gives the position of the value's transaction, its
     * tpos, and bergdb_get_trans of it its tt. bergdb_get_trans: the
     * transaction's time. */
    int64_t time;
    int64_t pos;            /* the value node's position (Kvt.spos) */
};

/* A stop condition's answers (GetMany.StopCondition's constants). */
enum bergdb_stop_answer {
    BERGDB_ADD = 1,             /* add the pair and go on */
    BERGDB_STOP = 2,            /* stop, without the pair */
    BERGDB_CONTINUE = 3,        /* go on, without the pair */
    BERGDB_ADD_AND_STOP = 4     /* add the pair and stop */
};

/*
 * A stop condition of the caller's (GetMany.StopCondition.handleKvt): what
 * to do with the pair, one of enum bergdb_stop_answer; another number ends
 * the read with BERGDB_ARG. The pair is valid during the call only. Java's
 * eod() is bergdb_many.eod.
 */
typedef int (*bergdb_stop_fn)(void *ctx, const struct bergdb_kvt *kvt);

/*
 * What bergdb_get_many reads (Java's GetMany's input fields, and its stop
 * conditions). bergdb_range_init sets GetMany's defaults: the latest
 * state, every key forward, no stop condition.
 *
 * The stop conditions are Java's: none (DontStop), an end key (Endpoint),
 * a prefix (Prefix), a count (GetN, GetOne), a prefix and a count
 * (PrefixN), or a function of the caller's. Several may be given; each
 * pair goes through those given in this order, and the first answer that
 * is not BERGDB_ADD decides, else the pair is added:
 *
 *   1. prefix: BERGDB_STOP at the first key that does not start with
 *      prefix (Prefix, PrefixN); a key that starts with it is read, the
 *      prefix's own key too. So a read from the prefix, inclusive
 *      (start_key the prefix, inclusive's default), gives every key that
 *      starts with it, and exclusive every one but the prefix's own. Until
 *      release 2026.4 a key equal to the prefix stopped the read, as
 *      Keys.isPrefix is a strict prefix (bergdb 021-18);
 *   2. end_key: BERGDB_STOP for a key past it in the read's direction, or
 *      at it if end_inclusive is false (Endpoint, with the read's
 *      direction as its backward flag);
 *   3. stop: the function's answer;
 *   4. max_count: BERGDB_ADD_AND_STOP for the max_count-th pair added
 *      (GetN); 0: no count. Java's GetN(0) gives no pair since release
 *      2026.4 (bergdb 020-27, C1; before, every pair, as 0 here); a read
 *      of no pair needs no call, so 0 stays the field's "not given".
 */
struct bergdb_range {
    int64_t lookup_time;            /* GetMany.lookupTime; BERGDB_LATEST */
    /* GetMany.startKey: the first key read is the first at or after it
     * (forward) or at or before it (backward); NULL (the default) reads
     * from the first key (forward) or the last (backward). */
    const uint8_t *start_key;
    size_t start_key_len;
    bool inclusive;     /* GetMany.inclusive: the start key itself may be read; true */
    bool forward;       /* GetMany.forward: increasing keys; true (false: setBackward()) */
    const uint8_t *prefix;          /* NULL: none */
    size_t prefix_len;
    const uint8_t *end_key;         /* NULL: none */
    size_t end_key_len;
    bool end_inclusive;             /* the end key itself may be read; true, as Endpoint(key) */
    int32_t max_count;              /* 0: none */
    bergdb_stop_fn stop;            /* NULL: none */
    void *stop_ctx;                 /* the function's ctx, used during the call only */
};

/* Sets r to GetMany's defaults (its constructor). */
void bergdb_range_init(struct bergdb_range *r);

/* What bergdb_get_many gives (GetMany's output fields). */
struct bergdb_many {
    const struct bergdb_kvt *kvts;  /* the pairs added (GetMany.result), in the read's order,
                                       in the read context's buffer; a pair's time is its
                                       key node entry's, not its write's (bergdb 021-19) */
    size_t count;
    int64_t actual_lookup_time;     /* GetMany.actualLookupTime */
    int32_t get_op_count;           /* GetMany.getOpCount: the pairs the stop conditions saw */
    bool eod;                       /* the end of the database was reached (StopCondition.eod()),
                                       also at once at a lookup time before the first
                                       transaction (bergdb 020-27, C2) */
};

/*
 * Reads the pairs of a range in key order at the lookup time (Java's
 * getMany), until a stop condition stops it or the end of the database.
 *
 * Errors: as bergdb_get_one, and BERGDB_ARG for a range NULL, a key over
 * INT32_MAX bytes, a negative max_count (GetN asserts it), or a stop
 * function's bad answer. On an error, *out is not set.
 */
int bergdb_get_many(bergdb_db *db, bergdb_read *rd, const struct bergdb_range *range,
        struct bergdb_many *out);

/* A stored transaction (Java's StoredTrans, its public fields). */
struct bergdb_stored {
    int64_t tt;             /* the transaction's time */
    int64_t tpos;           /* the position of its first byte */
    int64_t last_pos;       /* the position of its last byte */
    int64_t startup_pos;    /* the startup position stored with it */
    int64_t top_pos;        /* the position of the newest written top node's latest
                               version (011-11, 8.3), or BERGDB_NULL_POS */
    /* Its value and delete nodes, in record order (getValueNodes()), in the
     * read context's buffer: one for each key it put or deleted. A delete of
     * a key that had no value stores nothing and is not listed; a step of
     * reclaim lists the values it copied and reclaim's own keys (bergdb
     * 020-24-09, U9-9, as Java's Javadoc since release 2026.4). Index nodes
     * and the got-dirty list are left out (012-03, 6.4). */
    const struct bergdb_kvt *values;
    size_t count;
};

/*
 * Reads the transaction at the stream position tpos (Java's getTrans), as
 * bergdb_one.tpos gives it: for "which transaction wrote this value".
 *
 * Errors: BERGDB_ARG (rd of another database, out NULL, or tpos not a
 * position where a transaction can start: negative, not a multiple of 8,
 * in a meta block (005-34), at or past the end of the stream (005-43);
 * nothing is read), BERGDB_STATE, BERGDB_NOT_AVAILABLE (reclaim has
 * removed the transaction), BERGDB_FAILED (the database had failed, or the
 * read failed on the storage, or the bytes at tpos are not a committed
 * transaction: corrupt data, which fails it), BERGDB_NOMEM. On an error,
 * *out is not set.
 */
int bergdb_get_trans(bergdb_db *db, bergdb_read *rd, int64_t tpos, struct bergdb_stored *out);


/* ======== Durability ======== */

/* The sync levels (Java's SyncLevel, with its numbers; STRONG, 30, for a
 * replica, is gone as Java's since release 2026.3, which has no replicas). */
enum bergdb_sync_level {
    BERGDB_SYNC_NONE = 10,      /* nothing */
    BERGDB_SYNC_ORDINARY = 20   /* durable on the device */
};

/*
 * Makes the stream durable up to and including the byte at pos, a
 * transaction's last_pos; pos 0 for the last transaction executed (Java's
 * sync(level) and sync(pos, level)): writes the buffer and forces the
 * files written since the last force (F_FULLFSYNC); a new file and the
 * directory are forced when the file is made. With one stream, any pos
 * before the end makes all of it durable. A negative pos needs nothing; BERGDB_SYNC_NONE does nothing.
 * Durability: the C directory's readme.md, section 9.
 *
 * Errors: BERGDB_ARG (level not one of the two; pos at or past the end
 * of the stream, which Java waits for, as another thread's transaction can
 * reach it: here nothing could), BERGDB_STATE, BERGDB_FAILED (the write or
 * the force failed, which fails the database; or the database failed on
 * the storage before; a sync of the transactions before another failure
 * works).
 */
int bergdb_sync(bergdb_db *db, int64_t pos, int level);


/* ======== The clock's times ======== */

/*
 * The database's time now (Java's currentTime(), DbClock.currentTime): the
 * clock's time, at most BERGDB_MAX_TIME - 1024, or, when that is earlier,
 * the last time it gave or the last transaction's time, so its times never
 * decrease (bergdb 020-23, Z1). The next transaction's time is later than
 * it (section F). Errors: BERGDB_ARG (NULL), BERGDB_STATE.
 */
int bergdb_current_time(bergdb_db *db, int64_t *time);

/*
 * The lookup time a read uses for the wanted one (Java's lookupTime(long)):
 * wanted, but at most the last transaction's time. Errors: BERGDB_ARG
 * (NULL), BERGDB_STATE.
 */
int bergdb_lookup_time(bergdb_db *db, int64_t wanted, int64_t *actual);


/* ======== Settings and status ======== */

/*
 * Sets the startup distance, in bytes (Java's setStartupDistance(int)).
 * The value is clamped to 400,000 to 1,000,000,000 (twice the meta block
 * distance to 10^9), and the clamped value is set. A setting in the
 * stream: unless the clamped value is the one in force, the call executes
 * Java's dummy transaction (a 200,000-byte value under an internal key),
 * whose meta block records it, and the take moves the startup section
 * towards it as transactions are committed (007-03, D4); a call whose
 * clamped value is the one in force writes nothing (005-53). So on a
 * database whose setting is outside that range, which the open allows
 * (bergdb_options.startup_distance: 10 and up), any call writes and sets a
 * value inside it (bergdb 015-76, as Java's Javadoc since release 2026.3).
 * A refused or failed call leaves the setting as it was (005-53).
 *
 * Errors: BERGDB_ARG (negative), BERGDB_STATE, and the dummy transaction's,
 * as bergdb_execute's: BERGDB_LIMIT, BERGDB_NOMEM, BERGDB_FAILED.
 */
int bergdb_set_startup_distance(bergdb_db *db, int32_t distance);

/*
 * Sets the cache size indicator, the memory budget in bytes (Java's
 * setCacheSizeIndicator(long), 005-52), for this run only. After a
 * decrease, the call evicts at its end until the memory is within the new
 * budget, where Java wakes its eviction thread; what must stay in memory
 * may exceed it. On a failed database it only sets the value.
 * Errors: BERGDB_ARG (under 1), BERGDB_STATE.
 */
int bergdb_set_cache_size_indicator(bergdb_db *db, int64_t size);

/* Sets the retain duration in time units (Java's setRetainDuration(long)):
 * how long the history stays available for lookups; reclaim removes what
 * is older. BERGDB_FOREVER (the value of a new database) stops new
 * iterations and cuts; an iteration in progress goes on to its end, as
 * Java's. The front files of a cut are deleted once the stream is durable
 * up to the cut's decision: the library has no thread, so the
 * bergdb_execute call that decides a cut forces the stream itself (as a
 * bergdb_sync does; one force per cut, a few per retention period) and
 * deletes them, whether the application syncs or not (012-11, Q1, option
 * B).
 *
 * Kept in the stream, with the internal fraction (bergdb 015-87, as Java's
 * since release 2026.3; no option of the open): unless the value is the one
 * in force, the call commits a small internal transaction with reclaim's
 * settings, and a start reads them, so a restart keeps them. The value is
 * in force when the call returns. A call with the value in force writes
 * nothing; a refused call, or one whose commit fails, leaves the value as
 * it was.
 *
 * Errors: BERGDB_ARG (under BERGDB_UNITS_PER_SEC), BERGDB_STATE, and the
 * commit's, as bergdb_execute's: BERGDB_LIMIT (the clock out of range; the
 * top node ordinals used up), BERGDB_NOMEM, BERGDB_FAILED (a failed
 * database, or the commit failed it). */
int bergdb_set_retain_duration(bergdb_db *db, int64_t duration);

/* Sets reclaim's internal fraction (Java's setReclaimInternalFraction;
 * 0.25 in a new database), with Java's check: BERGDB_ARG for NaN, under
 * 0.001 or over 0.90, and the setting stays (bergdb 005-73). Reclaim keeps
 * the nearest multiple of 2^-16, an integer, and the double decides
 * nothing (bergdb 005-79): 0.25 exactly, 0.1 as 6,554 / 65,536, which
 * bergdb_stats' internal_fraction gives. Kept in the stream as the retain
 * duration is (bergdb_set_retain_duration; 015-87), with the same errors
 * but for the range. As Java's since release 2026.3. */
int bergdb_set_reclaim_internal_fraction(bergdb_db *db, double fraction);

/* The status, Db's getters, each a field (012-03, 6.2). */
struct bergdb_stats {
    int64_t stream_length;              /* getStreamLength() */
    int64_t durable_length;             /* getDurableLength(): the stream's length at the last
                                           force: the open (0 after a creation, as Java's),
                                           each bergdb_sync, a reclaim cut's (see
                                           bergdb_set_retain_duration), the close */
    int64_t last_trans_pos_of_last_valid_meta_block;
                                        /* getLastTransPosOfLastValidMetaBlock(): where recovery
                                           starts */
    int64_t first_available_lookup_time;    /* getFirstAvailableLookupTime() */
    int64_t first_available_pos;        /* getFirstAvailablePos() */
    int32_t startup_distance;           /* getStartupDistance() */
    int64_t cache_size_indicator;       /* getCacheSizeIndicator() */
    int64_t resident_bytes;             /* the bytes the index takes in memory, which the
                                           budget bounds (Level 4, 012-12): its key nodes,
                                           top nodes, values and handles, and the node
                                           table, as the allocator counts them (Java's
                                           CacheStats.residentBytes counts estimates) */
    int64_t evicted;                    /* the index objects evicted since the open, and the
                                           values that left memory (CacheStats.released) */
    int64_t pinned_bytes;               /* of the resident bytes, those that must stay: the
                                           nodes changed since the startup position (D) and
                                           the newest top nodes, with what they hold, and the
                                           node table (a walk of D, for reports) */
    int64_t retain_duration;            /* getRetainDuration() */
    double internal_fraction;           /* getInternalFraction(): reclaim's units of 2^-16
                                           over 65,536, exact (005-79) */
    int64_t reclaim_iteration_count;    /* getReclaimIterationCount() */
    int64_t transaction_count;          /* getTransactionCount(): since the open, BergDB's own
                                           too: reclaim's, and those of
                                           bergdb_set_startup_distance and of reclaim's
                                           settings (bergdb 020-24-09, U9-10) */
    int64_t kv_count;                   /* getKvCount(): the puts and deletes since the open,
                                           a delete of a key without a value too (U9-10) */
    int64_t get_op_count;               /* getGetOpCount(): since the open, one per getOne,
                                           one per pair a getMany's stop conditions saw, and
                                           the transactions' own reads (warm-up, previous
                                           values) */
};

/* Fills *stats. Also on a failed database. Errors: BERGDB_ARG (NULL),
 * BERGDB_STATE. */
int bergdb_stats(bergdb_db *db, struct bergdb_stats *stats);


/* ======== Debugging ======== */

/*
 * Prints the index in memory to out (Java's printDag), for tests and
 * development; the text is C's own: a line per node reached from the super
 * root by memory pointers, depth first, indented by its depth ("top ...",
 * "key ...", "value ...", "delete ..."), "-> POS" for a pointer to the
 * stream, and a last line with the counts. Errors: BERGDB_ARG (NULL),
 * BERGDB_STATE, BERGDB_FAILED, BERGDB_NOMEM.
 */
int bergdb_debug_print(bergdb_db *db, FILE *out);

/*
 * Checks every index object in memory (Java's checkNodes: KeyNode.check of
 * each key node reached from the super root), and recounts the holders of
 * every object of the database (C's, 012-01, 4.5), for tests. An
 * inconsistency is a bug, and stops the program with a failed assert, as
 * Java's AssertionError. Errors: BERGDB_ARG (NULL), BERGDB_STATE,
 * BERGDB_FAILED (a failed database's memory is not checked; Java's
 * checkNodes has no state check), BERGDB_NOMEM.
 */
int bergdb_debug_check(bergdb_db *db);

#ifdef __cplusplus
}
#endif

#endif
