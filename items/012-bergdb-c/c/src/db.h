/*
 * db: the database, ported from Java's bergdb.core.Db (bergdb 012-09; 012-02,
 * section 8): the creation (handleEmptyStream, writePrimordialTransaction,
 * and the start that reads the creation back, DbStarter's primordial
 * startup), execute with everything before and after its go point
 * (executeInner: checkSize, warmup, the top node ordinals, checkDirtyNodes,
 * ExecuteData.begin, the STM's check, the clock; then putKvs with the
 * marking of the got-dirty nodes, store with the take, the references, the
 * still-dirty nodes, the newest written top node and the record, and the
 * STM's record), setStartupDistance (005-53), the reads (getOneInternal,
 * getMany), sync, currentTime and the close. Prefix db_.
 *
 * The start of an existing database (012-10): Db.startInner's checks and
 * recovery and DbStarter, in starter.h (sr_check_and_recover, sr_start), on
 * the node table (ntable.h, Cache3 in part) and the node collection
 * (ncoll.h, NodeCollection: the followers, which load what is not in memory
 * with Rule R, and resolvePointers).
 *
 * Reclaim (Level 3, 012-11): reclaim.h's, called at the end of execute as
 * Java's Reclaim.transactionCompleted, with the touch of its steps here
 * (Trans.touch: touchRange, Trans.dirtiedBytes, the touch's marks kept at
 * endOfTrans), its settings and status, and the reads' refusals before the
 * first available lookup time; its table read back at a start
 * (rc_init_from_db).
 *
 * Eviction to the memory budget (012-12, evict.h): the capacity controller
 * runs at the end of the calls, safe points, where Java's runs: at the end
 * of execute (afterTransaction, before reclaim's transactionCompleted, as
 * Java's) and of the open (after the startup's loads), after the API's
 * reads (afterLoad; also between the pairs of its getMany), and in
 * setCacheSizeIndicator after a decrease (where Java wakes its thread). No
 * byte depends on it.
 *
 * Errors (err.h): before a transaction's go point a refusal leaves the
 * database as it was (ERR_LIMIT, ERR_RERUN, ERR_STATE, ERR_ARG, ERR_NOMEM);
 * after it, any failure fails the database (P7, 005-01): ERR_FAILED, and
 * every later call but close, sync, currentTime and the setters' values
 * gets ERR_FAILED with the first failure's text. One caller at a time.
 */
#ifndef BERGDB_DB_H
#define BERGDB_DB_H

#include <stdbool.h>
#include <stdint.h>
#include "clock.h"
#include "dag.h"
#include "err.h"
#include "evict.h"
#include "getmany.h"
#include "keymod.h"
#include "mem.h"
#include "ncoll.h"
#include "ntable.h"
#include "obj.h"
#include "reclaim.h"
#include "rstream.h"
#include "serial.h"
#include "stream.h"
#include "tnode.h"
#include "trans.h"
#include "transnodes.h"
#include "transseq.h"

/* Db.CREATION_LENGTH: the first meta block and the primordial record. */
#define DB_CREATION_LENGTH (128 + 136)

/* Db.LAST_TOP_ORDINAL: user transactions are refused from this super root's
 * ordinal on (005-02). */
#define DB_LAST_TOP_ORDINAL (TN_MAX_TOP_NODE_ID_VALUE - 1024)

/* setStartupDistance's clamp: 2 * META_BLOCK_DISTANCE to 1,000,000,000. */
#define DB_MIN_STARTUP_DISTANCE 400000
#define DB_MAX_STARTUP_DISTANCE 1000000000

enum db_state { DB_ZERO, DB_ACTIVE, DB_STOPPING, DB_FAILED };

/* The settings of an open: DbBuilder's, and two test settings. */
struct db_config {
    int32_t max_node_size;          /* 8, 14, 30 or 62 */
    int32_t startup_distance;       /* at least 10 */
    int64_t cache_size_indicator;   /* the memory budget, for this run only (012-12) */
    int64_t retain_duration;        /* at least one second; INT64_MAX: forever */
    clk_fn clock;                   /* NULL: the system clock */
    void *clock_ctx;
    bool random_id;                 /* DatabaseId.createRandom; else id */
    uint8_t id[16];
    int32_t buffer_size;            /* the write buffer's size; 0: Java's default */
    int64_t record_limit;           /* StoredTrans.recordLimit; 0: MAX_RECORD_SIZE */
    int64_t second_top_ordinal;     /* DbBuilder.secondTopOrdinal; 0: 1 */
    int64_t step_reserve;           /* DbBuilder.reclaimStepReserve; 0: 4 MiB (012-11) */
};

/* Java's StartInfo, and whether the open created the database. */
struct db_start_info {
    bool created;
    int64_t start_pos;
    int32_t startup_distance;       /* -1, as Java's (012-03, 6.8) */
    int64_t start_time;
    int32_t trans_count;
    int64_t last_pos;
};

struct db {
    struct mem *mem;
    struct obj_ctx cx;
    struct ntable node_table;       /* Db.cache, Cache3 (012-10) */
    struct ncoll node_coll;         /* Db.nodeCollection (012-10) */
    struct ev ev;                   /* Db.eviction (012-12) */
    struct stream stream;
    bool stream_open;
    struct rs rs;                   /* RecoverableStream with the in-memory meta block */
    struct dbclock clock;           /* Db.dbClock */
    struct kms key_mod_set;         /* Db.keyModSet */
    bool kms_made;
    struct ts_seq trans_seq;        /* D */
    struct ts_startup_pos startup_pos;  /* x.startupPos */
    struct dag dag;
    bool dag_made;
    struct putdata put_data;        /* x.putData */
    struct getdata get_data;        /* x.getData */
    struct transnodes trans_nodes;  /* x.transNodes */
    struct serial serializer;       /* NodeStream's */
    struct trans *trans;            /* x.trans, during execute */
    struct ts_info *trans_info;     /* x.transInfo, during execute (D's after store) */
    int64_t end_of_last_trans;      /* x.endOfLastTrans */
    int64_t next_vpos;              /* x.nextVpos */
    struct tnode *newest_written_top;   /* Db.newestWrittenTop, counted */

    /* The marking of an operation (Db.opMarks, opChanged, replacedInTrans,
     * touchMarks). opMarks borrows; replacedInTrans holds (counted), with the
     * flag OBJ_REPLACED on each node for its membership test. */
    struct node **op_marks;
    int32_t n_op_marks;
    int32_t cap_op_marks;
    bool op_changed;
    struct node **replaced;
    int32_t n_replaced;
    int32_t cap_replaced;
    int32_t touch_marks;

    int32_t max_node_size;
    int32_t startup_distance;       /* Db.startupDistance */
    int64_t cache_size_indicator;
    int64_t record_limit;
    int64_t second_top_ordinal;
    uint8_t database_id[16];

    enum db_state state;
    struct err failure;             /* the first failure, when state is DB_FAILED */
    struct err op_err;              /* a callback's failure (the follower, a listener) */
    struct op_pointer_listener dag_listener;    /* the Dag's own pointer listener, which
                                                   Db's calls first */
    struct reclaim reclaim;         /* Db.reclaim: its table, settings and status */

    /* Aux */
    int64_t transaction_count;
    int64_t kv_count;
    int64_t get_op_count;
};

/* new Db(builder) and start(): the directory dir opened for writing (or a
 * stream in memory, dir NULL), and, as the stream is empty, the database
 * created and started; else started (012-10). *info what the start read. On
 * an error nothing is left open or allocated: ERR_ARG (a bad setting; a
 * database with reclaim's table, unsupported before 012-11), ERR_IN_USE,
 * ERR_IO, ERR_FORMAT, ERR_NOT_CREATED, ERR_LIMIT (the clock at the
 * creation), ERR_NOMEM. A start that fails has written what Java's writes
 * (recovery's fill), and the stream is closed (005-32). */
enum err_code db_open(struct db *db, const char *dir, const struct db_config *cfg,
        struct mem *m, struct db_start_info *info, struct err *e);

/* close(): the stream written and forced and closed, the lock released,
 * every object and buffer freed. Also after a failure. ERR_IO if the last
 * write or force failed (the rest is closed all the same). */
enum err_code db_close(struct db *db, struct err *e);

/* execute(Trans): t built (tr_build) from a builder that does not change
 * until it returns. On ERR_OK, t's tt, tpos, last_pos, next_pos,
 * startup_pos and node_count are set. */
enum err_code db_execute(struct db *db, struct trans *t, struct err *e);

/* setStartupDistance(n) (005-53). */
enum err_code db_set_startup_distance(struct db *db, int32_t n, struct err *e);

/* setRetainDuration: under one second ERR_ARG (Reclaim's check). */
enum err_code db_set_retain_duration(struct db *db, int64_t d, struct err *e);

/* setReclaimInternalFraction: Java's range check (0.001 to 0.90, NaN let
 * through), used from the next step. */
enum err_code db_set_reclaim_internal_fraction(struct db *db, double f, struct err *e);

/* setCacheSizeIndicator: at least 1; the budget for this run, and on an
 * active database eviction to it at once (005-52; 012-12). */
enum err_code db_set_cache_size_indicator(struct db *db, int64_t size, struct err *e);

/* The end of a call that read (012-12): a safe point, then the capacity
 * controller (Eviction.afterLoad, run in the call). On an active database
 * only; the caller holds nothing uncounted. db_safe_point is the same for
 * a getMany's safe points between pairs (getmany.h), ctx the struct db. */
void db_evict(struct db *db);
void db_safe_point(void *ctx);

/* The resident bytes and the pinned bytes (evict.h), for bergdb_stats. */
int64_t db_resident_bytes(const struct db *db);
int64_t db_pinned_bytes(struct db *db);

/* currentTime(), lookupTime(t). */
int64_t db_current_time(struct db *db);
int64_t db_lookup_time(const struct db *db, int64_t wanted);

/* getStreamLength, getFirstAvailablePos, getFirstAvailableLookupTime
 * (reclaim's: 0 and 0 before a cut), getStartupDistance. */
int64_t db_stream_length(const struct db *db);
int64_t db_first_available_pos(const struct db *db);
int64_t db_first_available_time(const struct db *db);

/* sync(pos, level): pos 0 for the last transaction; the stream written and
 * forced. ERR_FAILED if that fails (the database fails, 005-30). */
enum err_code db_sync(struct db *db, int64_t pos, struct err *e);

/* NodeCollection.maintenance(): the follower of reclaim's scan and reads
 * (012-11), which loads without installing or swizzling. */
struct op_follower db_maintenance_follower(struct db *db);

/* newGetData, newGetMany: the database's reader follower set. */
void db_new_get_data(struct db *db, struct getdata *gd);
void db_new_get_many(struct db *db, struct getmany *g);

/* getOne (the state checked, then getOneInternal): *out the value node,
 * borrowed until the next call on the database (NULL: none). ERR_STATE,
 * ERR_FAILED, ERR_NOT_AVAILABLE, ERR_NOMEM. */
enum err_code db_get_one(struct db *db, int64_t lookup_time, const int64_t *key, int32_t n,
        struct getdata *gd, struct vnode **out, struct err *e);

/* getMany: g made by db_new_get_many, its input fields set. */
enum err_code db_get_many(struct db *db, struct getmany *g, struct err *e);

/* The state check of the calls (assertDbStateIsActive): ERR_STATE or
 * ERR_FAILED with Java's texts, the method's name in them. */
enum err_code db_check_active(const struct db *db, const char *method, struct err *e);

/* failOnStorage (005-30): a read or a sync that failed on the storage, or
 * read bytes that are not what they must be, fails the database (if it is
 * active): ERR_FAILED, "DbFailedException", with e's text as the cause; while
 * it stops, e's own code. what: "A read" or "A sync". */
enum err_code db_fail_on_storage(struct db *db, const char *what, struct err *e);

/* The recount (012-07, 6.4.1) from the database's roots: the objects whose
 * count is wrong (0: all right). For tests, between calls. */
int64_t db_recount(struct db *db);

#endif
