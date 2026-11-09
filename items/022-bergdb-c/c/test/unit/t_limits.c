/* Harness 6.4, sizes and times at their limits (Java's LimitsTester of
 * release 2026.4, bergdb 018-06; ported in 022-05): random transactions of
 * the Core at the edge of every limit: values whose nodes take the value
 * limit (db_value_limit, 7/8 of the record limit) and a few bytes more or
 * less, alone and together, long keys, many keys, value transformations that
 * grow a value, times at the last user time and past it, a clock out of
 * range or going back, and the setters at their bounds; with reclaim (a
 * retain duration of one second) and eviction (small budgets) on, and
 * restarts in a directory. The record limit is lowered (db_config's
 * record_limit, Java's StoredTrans.recordLimit; 012-18, section 3.2) to 240
 * kB, 300 kB or 1 MB, so that a value at the limit is a few hundred kB.
 *
 * What it checks, as Java's: each transaction is either refused before its
 * go point (ERR_LIMIT, Java's DbException) for a reason that holds (its
 * size, its index nodes, the time, the clock, the top node ordinals), and
 * the database goes on with nothing of it written; or it is committed, at a
 * time after the last and at most DBCLOCK_LAST_USER_TIME, and every value
 * reads back. The database never fails, and after a restart it holds every
 * committed value and setting and takes commits. The exception (015-51): a
 * value transformation's result above the value limit is the caller's
 * fault; a database that fails after one is counted so, the transaction is
 * not in the stream when its record did not fit, and the run ends.
 *
 * C's random numbers are test_random's, not java.util.Random's, so a seed
 * gives other runs than Java's; Java's eviction schedules (evictRandom)
 * are not C's (the budget only). Each failure prints the seed, the step and
 * the last calls. Each test ends with the allocator's count 0. */
#define _DARWIN_C_SOURCE        /* mkdtemp */
#include <assert.h>
#include <math.h>
#include <stdarg.h>
#include <stdlib.h>
#include <unistd.h>
#include "test.h"
#include "bergdb.h"
#include "clock.h"
#include "db.h"
#include "keys.h"
#include "klong.h"
#include "nwrite.h"
#include "plat.h"
#include "reclaim.h"
#include "stream.h"
#include "trans.h"
#include "vnode.h"

static const int64_t RECORD_LIMITS[] = {240 * 1000, 300 * 1000, 1000 * 1000};
static const int32_t STARTUP_DISTANCES[] = {10, 2000, 400 * 1000, 2000 * 1000};
static const int64_t CACHE_SIZES[] = {INT64_MAX, 1, 300 * 1000, 3000 * 1000};
static const int32_t SD_ARGS[] = {-1, 0, 10, 399999, 400000, 400001, 2000 * 1000,
        1000 * 1000 * 1000, 1000 * 1000 * 1000 + 1, INT32_MAX};
static const int64_t RETAIN_ARGS[] = {CLK_UNITS_PER_SEC - 1, CLK_UNITS_PER_SEC,
        2 * CLK_UNITS_PER_SEC, 30 * CLK_UNITS_PER_SEC, INT64_MAX - 1, INT64_MAX};
static const int64_t CACHE_ARGS[] = {0, 1, 1000, 300 * 1000, 10 * 1000 * 1000, INT64_MAX};
#define NFRACTION_ARGS 7
#define NELEM(a) ((int32_t) (sizeof (a) / sizeof (a)[0]))

#define LT_LOG 30               /* the last calls kept for a failure's report */
#define LT_KEY_CAP 3200         /* "/l/" + a digit + up to 3,006 chars, and the bkey */

/* The reference: each key's last value, len -1 for a deleted one. */
struct lt_entry {
    char *key;
    uint8_t *v;
    int32_t len;
};

/* A run's outcome. */
struct lt_result {
    int64_t committed, refusedSize, refusedTime, refusedNodes, refusedClock, refusedOrdinals,
            settings, restarts, cuts, iterations;
    bool callersFault;
};

/* A planned KV of a transaction: len -1 for a delete; tf for a value
 * transformation, whose result is made (made_len bytes, in the run's
 * buffer). */
struct lt_op {
    char *key;
    uint8_t *value;
    int32_t len;
    bool tf;
};

/* A value transformation's state: the result's length and its bytes. */
struct lt_tf {
    int32_t length;
    uint8_t *out;
    bool made;
};

/* One run: a database, its reference, and the random choices of its seed. */
struct lt_run {
    uint64_t seed;
    uint64_t r;
    int steps;
    int64_t now;                /* the clock: any time, also out of range */
    struct mem m;
    struct db db;
    bool open;
    char dir[1024];

    int64_t recordLimit;
    bool smallNodes;
    int32_t builderDistance;
    int64_t cacheSize;
    int endPhaseAt;             /* the step where the clock goes to the last times; -1 */
    int faultAt;                /* the step of the caller's fault; -1 for none */
    int64_t secondOrdinal;      /* near the last top node ordinal (005-02); 0: not given */

    struct lt_entry *ref;
    int32_t nref, capref;
    int32_t startupDistance;
    int64_t retain;
    int32_t fractionUnits;
    int64_t cacheIndicator;

    int step;
    bool endPhase;
    bool tainted;               /* a transformation's result above the value limit was taken */
    int64_t lastUserTime;
    int64_t maxClock;           /* the largest clock time in range that the database has seen */
    int64_t lastCut;
    bool failed;                /* a check failed: the run ends */
    struct lt_result res;
    char log[LT_LOG][240];
    int nlog;
    struct lt_tf tf;
};

static int64_t lt_clock(void *ctx) {
    return *(int64_t *) ctx;
}

static int32_t lt_rand(struct lt_run *run, int32_t n) {
    return test_random_below(&run->r, n);
}

static void note(struct lt_run *run, const char *fmt, ...) {
    char line[240];
    va_list ap;
    va_start(ap, fmt);
    vsnprintf(line, sizeof line, fmt, ap);
    va_end(ap);
    if (run->nlog == LT_LOG) {
        memmove(run->log[0], run->log[1], sizeof run->log[0] * (LT_LOG - 1));
        run->nlog--;
    }
    snprintf(run->log[run->nlog++], sizeof run->log[0], "%d: %s", run->step, line);
}

/* A failed check: the seed, the step, what, and the last calls; the run
 * ends. */
static void lt_fail_at(struct lt_run *run, int line, const char *fmt, ...) {
    char what[600];
    va_list ap;
    va_start(ap, fmt);
    vsnprintf(what, sizeof what, fmt, ap);
    va_end(ap);
    printf("LimitsTester in C, seed %llu, step %d: %s\nThe last calls:\n",
            (unsigned long long) run->seed, run->step, what);
    for (int i = 0; i < run->nlog; i++) {
        printf("  %s\n", run->log[i]);
    }
    test_checks_++;
    test_fail_(__FILE__, line, "a check of the run");
    run->failed = true;
}
#define lt_fail(run, ...) lt_fail_at(run, __LINE__, __VA_ARGS__)
#define lt_check(run, ok, ...) do { \
        test_checks_++; \
        if (!(ok) && !(run)->failed) lt_fail_at(run, __LINE__, __VA_ARGS__); \
    } while (0)

/* ======== The reference ======== */

static int32_t ref_find(const struct lt_run *run, const char *key) {
    for (int32_t i = 0; i < run->nref; i++) {
        if (strcmp(run->ref[i].key, key) == 0) {
            return i;
        }
    }
    return -1;
}

static void ref_put(struct lt_run *run, const char *key, const uint8_t *v, int32_t len) {
    int32_t i = ref_find(run, key);
    if (i < 0) {
        if (run->nref == run->capref) {
            run->capref = run->capref == 0 ? 64 : 2 * run->capref;
            run->ref = realloc(run->ref, sizeof *run->ref * (size_t) run->capref);
        }
        i = run->nref++;
        run->ref[i].key = strdup(key);
        run->ref[i].v = NULL;
    }
    free(run->ref[i].v);
    run->ref[i].v = NULL;
    run->ref[i].len = len;
    if (len > 0) {
        run->ref[i].v = malloc((size_t) len);
        memcpy(run->ref[i].v, v, (size_t) len);
    }
}

static void ref_free(struct lt_run *run) {
    for (int32_t i = 0; i < run->nref; i++) {
        free(run->ref[i].key);
        free(run->ref[i].v);
    }
    free(run->ref);
    run->ref = NULL;
    run->nref = run->capref = 0;
}

/* ======== Keys and values ======== */

/* The bkey of ikey and its segments; returns the segment count. */
static int32_t segments_of(const char *ikey, uint8_t *bkey, int32_t *kl, int64_t *seg) {
    *kl = (int32_t) strlen(ikey);
    bool ok = keys_ikey_to_bkey((const uint8_t *) ikey, *kl, bkey);
    assert(ok);
    (void) ok;
    keys_to_segments(bkey, *kl, seg);
    return keys_segment_count(*kl);
}

static int32_t segment_count(const char *ikey) {
    return keys_segment_count((int32_t) strlen(ikey));
}

/* StoredValueNode.getByteSizeLong of the op's value (its input for a
 * transformation, as checkSize counts it). */
static int64_t node_bytes(const struct lt_op *op) {
    return nw_value_byte_size_long(op->len, segment_count(op->key));
}

static uint8_t *value_of(struct lt_run *run, int32_t length) {
    uint8_t *v = malloc((size_t) length + 1);
    const uint8_t b = (uint8_t) test_random(&run->r);
    memset(v, b, (size_t) length);
    for (int32_t i = 0; i < length && i < 8; i++) {
        v[i] = (uint8_t) test_random(&run->r);
    }
    if (length > 8) {
        v[length - 1] = (uint8_t) test_random(&run->r);
    }
    return v;
}

/* The value length that makes key's value node take at most nodeBytes. */
static int32_t length_for(const char *key, int64_t nodeBytes) {
    const int32_t k = segment_count(key);
    int64_t n = nodeBytes - 28 - 8 * (int64_t) k;
    while (n > 0 && nw_value_byte_size_long(n, k) > nodeBytes) {
        n--;
    }
    return (int32_t) (n > 0 ? n : 0);
}

/* A small offset from the limit: 0, a few bytes, or more. */
static int64_t edge(struct lt_run *run) {
    switch (lt_rand(run, 8)) {
    case 0: return 0;
    case 1: return 1;
    case 2: return 3;
    case 3: return 4;
    case 4: return 5;
    case 5: return 100;
    case 6: return 1 + lt_rand(run, 5000);
    default: {
        int64_t half = db_value_limit(&run->db) / 2;
        return 1 + lt_rand(run, (int32_t) (half < 100000 ? half : 100000));
    }
    }
}

static void small_key(struct lt_run *run, char *out) {
    snprintf(out, LT_KEY_CAP, "/k/%d", lt_rand(run, 60));
}

static void big_key(struct lt_run *run, char *out) {
    snprintf(out, LT_KEY_CAP, "/v/%d", lt_rand(run, 16));
}

static void long_key(struct lt_run *run, char *out) {
    static const int32_t lengths[] = {20, 70, 140, 400, 1000, 1500, 3000};
    int32_t n = lengths[lt_rand(run, NELEM(lengths))] + lt_rand(run, 7);
    char c = (char) ('a' + lt_rand(run, 3));
    int32_t o = snprintf(out, LT_KEY_CAP, "/l/%d", lt_rand(run, 4));
    memset(out + o, c, (size_t) n);
    out[o + n] = '\0';
}

/* ======== Starting and stopping ======== */

static enum err_code start(struct lt_run *run, struct err *e) {
    struct db_config cfg;
    struct db_start_info info;
    memset(&cfg, 0, sizeof cfg);
    cfg.max_node_size = run->smallNodes ? 8 : 30;
    cfg.startup_distance = run->builderDistance;
    cfg.cache_size_indicator = run->cacheSize;
    cfg.clock = lt_clock;
    cfg.clock_ctx = &run->now;
    memcpy(cfg.id, bergdb_test_id, sizeof cfg.id);
    cfg.record_limit = run->recordLimit;
    cfg.second_top_ordinal = run->secondOrdinal;    /* at every start, as the node size */
    enum err_code rc = db_open(&run->db, run->dir, &cfg, &run->m, &info, e);
    run->open = rc == ERR_OK;
    return rc;
}

static void check_key(struct lt_run *run, const char *key);
static void check_all(struct lt_run *run);

/* True if a transaction may find no time left: the clock, a read's time or
 * the last user transaction's is near DBCLOCK_LAST_USER_TIME, with room for
 * the internal transactions after each user one. */
static bool near_end(const struct lt_run *run) {
    int64_t t = run->now > run->maxClock ? run->now : run->maxClock;
    t = t > run->lastUserTime + 1 ? t : run->lastUserTime + 1;
    return t > DBCLOCK_LAST_USER_TIME - 4096;
}

/* A setter's refusal at the end of the times or of the top node ordinals. */
static bool refused_at_end(const struct lt_run *run, const struct err *e) {
    return (strstr(e->text, "No database time is left") != NULL && near_end(run))
            || (strstr(e->text, "used its top node ordinals") != NULL && run->secondOrdinal > 0);
}

static void restart(struct lt_run *run) {
    struct err e;
    note(run, "restart");
    run->res.iterations += run->db.reclaim.iterationCount;
    run->open = false;
    enum err_code rc = db_close(&run->db, &e);
    lt_check(run, rc == ERR_OK, "the close before a restart: %s: %s", e.java, e.text);
    rc = start(run, &e);
    if (rc != ERR_OK) {
        lt_fail(run, "the restart: %s: %s", e.java, e.text);
        return;
    }
    run->res.restarts++;
    /* The cache size indicator is for the run only; a start takes the
     * builder's. */
    run->cacheIndicator = run->cacheSize;
    lt_check(run, run->db.startup_distance == run->startupDistance, "the startup distance after "
            "a restart: expected %d, got %d", run->startupDistance, run->db.startup_distance);
    lt_check(run, run->db.reclaim.retainDuration == run->retain, "the retain duration after a "
            "restart: expected %lld, got %lld", (long long) run->retain,
            (long long) run->db.reclaim.retainDuration);
    lt_check(run, run->db.reclaim.internalFraction == run->fractionUnits, "the internal fraction "
            "after a restart: expected %d units, got %d", run->fractionUnits,
            run->db.reclaim.internalFraction);
    lt_check(run, db_recount(&run->db) == 0, "the recount after a restart");
    check_all(run);
}

static void start_first(struct lt_run *run) {
    struct err e;
    struct db_config cfg;
    struct db_start_info info;
    /* DbBuilder.startupDistance(9) is refused: its least is 10. */
    memset(&cfg, 0, sizeof cfg);
    cfg.max_node_size = 30;
    cfg.startup_distance = 9;
    cfg.cache_size_indicator = INT64_MAX;
    cfg.clock = lt_clock;
    cfg.clock_ctx = &run->now;
    lt_check(run, db_open(&run->db, run->dir, &cfg, &run->m, &info, &e) == ERR_ARG,
            "a startup distance of 9 was not refused");
    if (start(run, &e) != ERR_OK) {
        lt_fail(run, "the first start: %s: %s", e.java, e.text);
        return;
    }
    run->startupDistance = run->db.startup_distance;
    note(run, "start: record limit %lld, value limit %lld, startup distance %d, cache %lld%s, "
            "end phase at %d, caller's fault at %d, second top ordinal %lld",
            (long long) run->recordLimit, (long long) db_value_limit(&run->db),
            run->builderDistance, (long long) run->cacheSize,
            run->smallNodes ? ", node size 8" : "", run->endPhaseAt, run->faultAt,
            (long long) run->secondOrdinal);
    if (lt_rand(run, 4) != 0) {
        if (db_set_retain_duration(&run->db, CLK_UNITS_PER_SEC, &e) == ERR_OK) {
            run->retain = CLK_UNITS_PER_SEC;
        } else {
            lt_check(run, refused_at_end(run, &e), "setRetainDuration at the start refused: "
                    "%s: %s", e.java, e.text);
        }
    }
}

/* ======== The checks ======== */

static void check_key(struct lt_run *run, const char *key) {
    if (run->failed) {
        return;
    }
    uint8_t bkey[LT_KEY_CAP];
    int64_t seg[LT_KEY_CAP / 7 + 2];
    int32_t kl;
    int32_t n = segments_of(key, bkey, &kl, seg);
    struct getdata gd;
    struct vnode *v = NULL;
    struct err e;
    db_new_get_data(&run->db, &gd);
    enum err_code rc = db_get_one(&run->db, INT64_MAX, seg, n, &gd, &v, &e);
    if (rc != ERR_OK) {
        lt_fail(run, "get(%.40s): %s: %s", key, e.java, e.text);
        return;
    }
    int32_t i = ref_find(run, key);
    int32_t expected = i < 0 ? -1 : run->ref[i].len;
    int32_t actual = v == NULL ? -1 : v->len;
    lt_check(run, expected == actual && (actual <= 0
            || memcmp(v->value, run->ref[i].v, (size_t) actual) == 0),
            "get(%.40s): expected %d bytes, got %d", key, expected, actual);
    db_evict(&run->db);         /* the end of the call, as bergdb_get_one's */
}

static void check_all(struct lt_run *run) {
    for (int32_t i = 0; i < run->nref && !run->failed; i++) {
        check_key(run, run->ref[i].key);
    }
}

static void check_active(struct lt_run *run) {
    if (run->db.state != DB_ACTIVE) {
        lt_fail(run, "the database is not active: %s: %s", run->db.failure.java,
                run->db.failure.text);
    }
}

static void update_cuts(struct lt_run *run) {
    int64_t cut = stream_first_pos(&run->db.stream);
    if (cut > run->lastCut) {
        run->lastCut = cut;
        run->res.cuts++;
    }
}

/* ======== Transactions ======== */

static void ops_free(struct lt_op *ops, int32_t n) {
    for (int32_t i = 0; i < n; i++) {
        free(ops[i].key);
        free(ops[i].value);
    }
}

static bool has_key(const struct lt_op *ops, int32_t n, const char *key) {
    for (int32_t i = 0; i < n; i++) {
        if (strcmp(ops[i].key, key) == 0) {
            return true;
        }
    }
    return false;
}

static void lt_value_tf(void *ctx, int64_t tt, const uint8_t *previous, size_t previous_len,
        const uint8_t **value, size_t *value_len) {
    struct lt_tf *f = ctx;
    const uint8_t *in = *value;
    const size_t in_len = *value_len;
    const size_t length = (size_t) f->length;
    memset(f->out, (uint8_t) tt, length);
    memcpy(f->out, in, in_len < length ? in_len : length);
    if (previous != NULL && length > in_len) {
        size_t k = length - in_len < 64 ? length - in_len : 64;
        memcpy(f->out + in_len, previous, previous_len < k ? previous_len : k);
    }
    f->made = true;
    *value = f->out;
    *value_len = length;
}

static void callers_fault(struct lt_run *run, struct lt_op *ops, int32_t n, bool atOnce);

/* Executes ops as one transaction at the clock's time; true if it was
 * committed. callers: a transformation's result above the value limit, the
 * caller's fault (015-51). */
static bool execute(struct lt_run *run, struct lt_op *ops, int32_t n, const char *what,
        bool callers) {
    if (run->failed || run->res.callersFault) {
        return false;
    }
    struct tr_builder b;
    struct trans t;
    struct err e;
    tr_builder_init(&b, &run->m);
    tr_init(&t, &run->m);
    int64_t bytes = 0;
    enum err_code rc = ERR_OK;
    run->tf.made = false;
    for (int32_t i = 0; i < n && rc == ERR_OK; i++) {
        uint8_t bkey[LT_KEY_CAP];
        int32_t kl = (int32_t) strlen(ops[i].key);
        keys_ikey_to_bkey((const uint8_t *) ops[i].key, kl, bkey);
        if (ops[i].len < 0) {
            rc = tr_delete(&b, bkey, kl, &e);
        } else {
            const struct tr_transform tf = { NULL, lt_value_tf, &run->tf };
            rc = tr_put(&b, bkey, kl, ops[i].len == 0 ? (const uint8_t *) "" : ops[i].value,
                    ops[i].len, ops[i].tf ? &tf : NULL, &e);
        }
        bytes += node_bytes(&ops[i]);
    }
    if (rc == ERR_OK) {
        rc = tr_build(&b, &t, &e);
    }
    lt_check(run, rc == ERR_OK, "%s: the transaction's build: %s", what, e.text);
    const int64_t clockTime = run->now;
    const bool clockOut = clockTime < KL_MIN_TIME || clockTime > KL_MAX_TIME;
    const bool over = bytes > db_value_limit(&run->db);
    const bool nearEnd = near_end(run);
    const int64_t length = db_stream_length(&run->db);
    note(run, "%s: %d KVs, the first %.30s (%lld bytes, clock %lld)", what, n, ops[0].key,
            (long long) bytes, (long long) clockTime);
    if (rc == ERR_OK) {
        rc = db_execute(&run->db, &t, &e);
    }
    tr_free(&t);
    tr_builder_free(&b);
    if (run->failed) {
        return false;
    }
    if (rc == ERR_FAILED) {
        if (callers || run->tainted) {
            callers_fault(run, ops, n, callers);
            return false;
        }
        lt_fail(run, "%s: the database failed: %s: %s", what, run->db.failure.java,
                run->db.failure.text);
        return false;
    }
    if (rc != ERR_OK) {
        /* Db checks the size first, then the top node ordinals, the index
         * nodes and the time: any reason that holds may be the one given. */
        bool holds = false;
        if (rc == ERR_LIMIT && strcmp(e.java, "DbException") == 0) {
            if (strstr(e.text, "outside the range") != NULL) {
                holds = clockOut;
                run->res.refusedClock++;
            } else if (strstr(e.text, "The transaction is too large: its values") != NULL) {
                holds = over;
                run->res.refusedSize++;
            } else if (strstr(e.text, "No database time is left") != NULL) {
                holds = nearEnd;
                run->res.refusedTime++;
            } else if (strstr(e.text, "used its top node ordinals") != NULL) {
                holds = run->secondOrdinal > 0;
                run->res.refusedOrdinals++;
            } else if (strstr(e.text, "index nodes it can make dirty") != NULL) {
                holds = true;           /* Db.checkDirtyNodes (005-31) */
                run->res.refusedNodes++;
            }
        }
        if (!holds) {
            lt_fail(run, "%s: refused for a reason that does not hold (%lld bytes, value limit "
                    "%lld, clock %lld, last user transaction %lld): %s: %s", what,
                    (long long) bytes, (long long) db_value_limit(&run->db),
                    (long long) clockTime, (long long) run->lastUserTime, e.java, e.text);
            return false;
        }
        note(run, "  refused: %.150s", e.text);
        check_active(run);
        lt_check(run, db_stream_length(&run->db) == length, "%s: refused, and the stream grew "
                "from %lld to %lld", what, (long long) length,
                (long long) db_stream_length(&run->db));
        for (int32_t i = 0; i < n; i++) {
            check_key(run, ops[i].key);
        }
        update_cuts(run);
        return false;
    }
    lt_check(run, !clockOut, "%s: taken with the clock out of range, %lld", what,
            (long long) clockTime);
    lt_check(run, !over, "%s: taken with %lld bytes, over the value limit %lld", what,
            (long long) bytes, (long long) db_value_limit(&run->db));
    lt_check(run, t.tt > run->lastUserTime, "%s: its time %lld not after the last, %lld", what,
            (long long) t.tt, (long long) run->lastUserTime);
    lt_check(run, t.tt <= DBCLOCK_LAST_USER_TIME, "%s: taken at %lld, after the last user time",
            what, (long long) t.tt);
    run->lastUserTime = t.tt;
    if (callers) {
        /* Its record fitted: the value is in, and later failures are the
         * caller's. */
        run->tainted = true;
        note(run, "  a transformation's result above the value limit was taken");
    }
    for (int32_t i = 0; i < n; i++) {
        if (ops[i].tf) {
            lt_check(run, run->tf.made, "%s: the transformation was not called", what);
            ref_put(run, ops[i].key, run->tf.out, run->tf.length);
        } else {
            ref_put(run, ops[i].key, ops[i].value, ops[i].len);
        }
    }
    run->res.committed++;
    check_active(run);
    for (int32_t i = 0; i < n; i++) {
        check_key(run, ops[i].key);
    }
    update_cuts(run);
    return true;
}

/* The database failed after a value transformation whose result is above
 * the value limit: the caller's fault (018-01, section 6.4; 015-51). The
 * transaction must not be in the stream when its record did not fit: a
 * restart has the state before it, and takes commits. The run ends. */
static void callers_fault(struct lt_run *run, struct lt_op *ops, int32_t n, bool atOnce) {
    struct err e;
    note(run, "  failed, the caller's fault: %.150s", run->db.failure.text);
    run->res.callersFault = true;
    const bool recordTooLarge = strstr(run->db.failure.text,
            "The record of the transaction would take") != NULL;
    run->open = false;
    db_close(&run->db, &e);             /* a failed database's close may report the failure */
    if (start(run, &e) != ERR_OK) {
        if (atOnce) {
            lt_fail(run, "the restart after the caller's fault failed: %s: %s", e.java, e.text);
        }
        /* A larger value taken before may fail every start; the caller's too. */
        return;
    }
    if (atOnce) {
        /* Its record did not fit, and nothing of it is in the stream; or it
         * was taken, and a later transaction of the same call failed
         * (reclaim's step, which rewrites the value with its row): then it
         * is in. */
        for (int32_t i = 0; i < n && !run->failed; i++) {
            if (!recordTooLarge && ops[i].tf && run->tf.made) {
                uint8_t bkey[LT_KEY_CAP];
                int64_t seg[LT_KEY_CAP / 7 + 2];
                int32_t kl;
                int32_t k = segments_of(ops[i].key, bkey, &kl, seg);
                struct getdata gd;
                struct vnode *v = NULL;
                db_new_get_data(&run->db, &gd);
                if (db_get_one(&run->db, INT64_MAX, seg, k, &gd, &v, &e) == ERR_OK && v != NULL
                        && v->len == run->tf.length
                        && memcmp(v->value, run->tf.out, (size_t) v->len) == 0) {
                    ref_put(run, ops[i].key, run->tf.out, run->tf.length);
                    run->tainted = true;
                }
            }
            check_key(run, ops[i].key);
        }
    }
    if (!atOnce) {
        return;             /* the state after a taken result is the caller's */
    }
    check_all(run);
    struct lt_op one = { strdup("/k/after"), malloc(1), 1, false };
    one.value[0] = 1;
    run->res.callersFault = false;      /* execute's guard; the run ends after this put */
    execute(run, &one, 1, "put after the restart", false);
    run->res.callersFault = true;
    ops_free(&one, 1);
}

/* ======== The steps ======== */

static void put_small(struct lt_run *run) {
    struct lt_op ops[3];
    int32_t n = 0;
    int32_t want = 1 + lt_rand(run, 3);
    for (int32_t i = 0; i < want; i++) {
        char k[LT_KEY_CAP];
        small_key(run, k);
        if (!has_key(ops, n, k)) {
            int32_t len = lt_rand(run, 100);
            ops[n] = (struct lt_op) { strdup(k), value_of(run, len), len, false };
            n++;
        }
    }
    execute(run, ops, n, "put small", false);
    ops_free(ops, n);
}

/* One value whose node takes the value limit, or a few bytes less or more. */
static void put_at_limit(struct lt_run *run) {
    char k[LT_KEY_CAP];
    if (lt_rand(run, 5) == 0) {
        long_key(run, k);
    } else {
        big_key(run, k);
    }
    const bool above = lt_rand(run, 4) == 0;
    const int64_t e = edge(run);
    const int64_t limit = db_value_limit(&run->db);
    const int64_t target = above ? limit + (e > 1 ? e : 1) : limit - e;
    int32_t n = length_for(k, target);
    if (above) {
        while (nw_value_byte_size_long(n, segment_count(k)) <= limit) {
            n++;
        }
    }
    struct lt_op op = { strdup(k), value_of(run, n), n, false };
    execute(run, &op, 1, above ? "put above the limit" : "put at the limit", false);
    ops_free(&op, 1);
}

/* Several values whose nodes take the value limit together, or a little
 * more. */
static void put_many_at_limit(struct lt_run *run) {
    const int32_t m = 2 + lt_rand(run, 5);
    const bool above = lt_rand(run, 4) == 0;
    const int64_t e = edge(run);
    const int64_t limit = db_value_limit(&run->db);
    const int64_t target = above ? limit + (e > 1 ? e : 1) : limit - e;
    struct lt_op ops[6];
    int32_t n = 0;
    while (n < m) {
        char k[LT_KEY_CAP];
        if (lt_rand(run, 2) == 0) {
            big_key(run, k);
        } else {
            small_key(run, k);
        }
        if (!has_key(ops, n, k)) {
            ops[n++] = (struct lt_op) { strdup(k), NULL, 0, false };
        }
    }
    int64_t left = target;
    for (int32_t i = 0; i < m; i++) {
        int64_t part = i == m - 1 ? left : left / (m - i) + lt_rand(run, 1000) - 500;
        int64_t least = nw_value_byte_size_long(0, segment_count(ops[i].key));
        part = part > least ? part : least;
        ops[i].len = length_for(ops[i].key, part);
        ops[i].value = value_of(run, ops[i].len);
        left -= node_bytes(&ops[i]);
    }
    execute(run, ops, n, "put many at the limit", false);
    ops_free(ops, n);
}

static void delete_keys(struct lt_run *run) {
    struct lt_op ops[2];
    int32_t n = 0;
    char k[LT_KEY_CAP];
    if (lt_rand(run, 2) == 0) {
        big_key(run, k);
    } else {
        small_key(run, k);
    }
    ops[n++] = (struct lt_op) { strdup(k), NULL, -1, false };
    if (lt_rand(run, 2) == 0) {
        char k2[LT_KEY_CAP];
        small_key(run, k2);
        if (strcmp(k2, k) != 0) {
            ops[n++] = (struct lt_op) { strdup(k2), NULL, -1, false };
        }
    }
    execute(run, ops, n, "delete", false);
    ops_free(ops, n);
}

/* A put with a value transformation that grows the value: its result is a
 * value of a given length, made of its input and the previous value. Within
 * the limit, or, for the caller's fault, above it. */
static void transform(struct lt_run *run, bool callers) {
    char k[LT_KEY_CAP];
    if (lt_rand(run, 2) == 0) {
        big_key(run, k);
    } else {
        small_key(run, k);
    }
    int32_t inLen = lt_rand(run, 50);
    uint8_t *in = value_of(run, inLen);
    const int64_t limit = db_value_limit(&run->db);
    int64_t target;
    if (callers) {
        /* Above the value limit: within the record limit or beyond it. */
        target = lt_rand(run, 2) == 0 ? limit + 1 + lt_rand(run, 1000)
                : run->recordLimit + 1 + lt_rand(run, 100000);
    } else {
        int64_t e = edge(run);
        target = lt_rand(run, 3) == 0 ? limit - e : 100 + lt_rand(run, 5000);
    }
    run->tf.length = length_for(k, target) + (callers ? 8 : 0);
    free(run->tf.out);
    run->tf.out = malloc((size_t) run->tf.length + 1);
    struct lt_op ops[2];
    int32_t n = 0;
    ops[n++] = (struct lt_op) { strdup(k), in, inLen, true };
    if (!callers && lt_rand(run, 2) == 0) {
        char k2[LT_KEY_CAP];
        small_key(run, k2);
        if (strcmp(k2, k) != 0) {
            int32_t len = lt_rand(run, 30);
            ops[n++] = (struct lt_op) { strdup(k2), value_of(run, len), len, false };
        }
    }
    execute(run, ops, n, callers ? "transform above the limit (the caller's fault)"
            : "transform", callers);
    ops_free(ops, n);
}

/* Many small KVs in one transaction, at the bound of its index nodes. */
static void put_many_keys(struct lt_run *run) {
    int32_t want = 50 + lt_rand(run, 1500);
    struct lt_op *ops = malloc(sizeof *ops * (size_t) want);
    char *seen = calloc(5000, 1);
    int32_t n = 0;
    for (int32_t i = 0; i < want; i++) {
        int32_t x = lt_rand(run, 5000);
        if (!seen[x]) {
            char k[32];
            seen[x] = 1;
            snprintf(k, sizeof k, "/m/%d", x);
            int32_t len = lt_rand(run, 20);
            ops[n++] = (struct lt_op) { strdup(k), value_of(run, len), len, false };
        }
    }
    execute(run, ops, n, "put many keys", false);
    ops_free(ops, n);
    free(ops);
    free(seen);
}

static void put_long_key(struct lt_run *run) {
    struct lt_op ops[6];
    int32_t n = 0;
    int32_t want = 1 + (lt_rand(run, 4) == 0 ? lt_rand(run, 6) : 0);
    for (int32_t i = 0; i < want; i++) {
        char k[LT_KEY_CAP];
        long_key(run, k);
        if (!has_key(ops, n, k)) {
            int32_t len = lt_rand(run, 200);
            ops[n++] = (struct lt_op) { strdup(k), value_of(run, len), len, false };
        }
    }
    execute(run, ops, n, "put long keys", false);
    ops_free(ops, n);
}

/* The clock goes back, or out of the range for one transaction. */
static void clock_edge(struct lt_run *run) {
    if (lt_rand(run, 4) == 0) {
        int64_t back = 1 + lt_rand(run, (int32_t) CLK_UNITS_PER_SEC);
        run->now = run->now - back > 0 ? run->now - back : 0;
        run->maxClock = run->maxClock > run->now ? run->maxClock : run->now;
        note(run, "clock back to %lld", (long long) run->now);
        put_small(run);
        return;
    }
    const int64_t saved = run->now;
    const int64_t outside[] = {-1, INT64_MIN, KL_MAX_TIME + 1, KL_MAX_TIME + 1
            + lt_rand(run, 1000), INT64_MAX};
    run->now = outside[lt_rand(run, NELEM(outside))];
    put_small(run);
    run->now = saved;
}

/* Db.setStartupDistance (015-76): the value clamped to 400,000 to 10^9 and
 * set; a call whose clamped value is in force writes nothing, others write; a
 * negative value is refused and changes nothing. */
static void set_startup_distance(struct lt_run *run) {
    struct err e;
    int32_t v = SD_ARGS[lt_rand(run, NELEM(SD_ARGS))];
    if (lt_rand(run, 4) == 0) {
        v = run->startupDistance;
    }
    int32_t clamped = v < 400 * 1000 ? 400 * 1000 : v > 1000 * 1000 * 1000 ? 1000 * 1000 * 1000
            : v;
    const int64_t length = db_stream_length(&run->db);
    note(run, "setStartupDistance(%d), in force %d", v, run->startupDistance);
    enum err_code rc = db_set_startup_distance(&run->db, v, &e);
    if (rc == ERR_ARG) {
        lt_check(run, v < 0, "setStartupDistance(%d) refused: %s", v, e.text);
        lt_check(run, run->db.startup_distance == run->startupDistance, "a refused "
                "setStartupDistance changed the setting");
        return;
    }
    if (rc == ERR_FAILED) {
        if (run->tainted) {
            callers_fault(run, NULL, 0, false);
            return;
        }
        lt_fail(run, "setStartupDistance(%d): the database failed: %s", v, run->db.failure.text);
        return;
    }
    if (rc != ERR_OK) {
        lt_check(run, refused_at_end(run, &e), "setStartupDistance(%d) refused: %s: %s", v,
                e.java, e.text);
        lt_check(run, run->db.startup_distance == run->startupDistance, "a refused "
                "setStartupDistance changed the setting");
        run->res.refusedTime++;
        return;
    }
    lt_check(run, v >= 0, "setStartupDistance(%d) was not refused", v);
    lt_check(run, run->db.startup_distance == clamped, "setStartupDistance(%d): expected the "
            "setting %d, got %d", v, clamped, run->db.startup_distance);
    const int64_t after = db_stream_length(&run->db);
    if (clamped == run->startupDistance) {
        lt_check(run, after == length, "setStartupDistance(%d) with %d in force wrote %lld "
                "bytes", v, clamped, (long long) (after - length));
    } else {
        lt_check(run, after > length, "setStartupDistance(%d) from %d wrote nothing", v,
                run->startupDistance);
    }
    run->startupDistance = clamped;
}

static void set_retain_duration(struct lt_run *run) {
    struct err e;
    int64_t v = RETAIN_ARGS[lt_rand(run, NELEM(RETAIN_ARGS))];
    note(run, "setRetainDuration(%lld)", (long long) v);
    enum err_code rc = db_set_retain_duration(&run->db, v, &e);
    if (rc == ERR_ARG) {
        lt_check(run, v < CLK_UNITS_PER_SEC, "setRetainDuration(%lld) refused: %s",
                (long long) v, e.text);
        lt_check(run, run->db.reclaim.retainDuration == run->retain, "a refused "
                "setRetainDuration changed the setting");
        return;
    }
    if (rc == ERR_FAILED) {
        if (run->tainted) {
            callers_fault(run, NULL, 0, false);
            return;
        }
        lt_fail(run, "setRetainDuration(%lld): the database failed: %s", (long long) v,
                run->db.failure.text);
        return;
    }
    if (rc != ERR_OK) {
        lt_check(run, refused_at_end(run, &e), "setRetainDuration(%lld) refused: %s: %s",
                (long long) v, e.java, e.text);
        lt_check(run, run->db.reclaim.retainDuration == run->retain, "a refused "
                "setRetainDuration changed the setting");
        run->res.refusedTime++;
        return;
    }
    lt_check(run, v >= CLK_UNITS_PER_SEC, "setRetainDuration(%lld) was not refused",
            (long long) v);
    lt_check(run, run->db.reclaim.retainDuration == v, "setRetainDuration(%lld): got %lld",
            (long long) v, (long long) run->db.reclaim.retainDuration);
    run->retain = v;
}

static void set_fraction(struct lt_run *run) {
    struct err e;
    const double args[NFRACTION_ARGS] = {0.0009, 0.001, 0.1, 0.25, 0.9, 0.9001, NAN};
    const double v = args[lt_rand(run, NFRACTION_ARGS)];
    const bool valid = !isnan(v) && v >= 0.001 && v <= 0.90;
    note(run, "setReclaimInternalFraction(%g)", v);
    enum err_code rc = db_set_reclaim_internal_fraction(&run->db, v, &e);
    if (rc == ERR_ARG) {
        lt_check(run, !valid, "setReclaimInternalFraction(%g) refused: %s", v, e.text);
        return;
    }
    if (rc == ERR_FAILED) {
        if (run->tainted) {
            callers_fault(run, NULL, 0, false);
            return;
        }
        lt_fail(run, "setReclaimInternalFraction(%g): the database failed: %s", v,
                run->db.failure.text);
        return;
    }
    if (rc != ERR_OK) {
        lt_check(run, refused_at_end(run, &e), "setReclaimInternalFraction(%g) refused: %s: %s",
                v, e.java, e.text);
        run->res.refusedTime++;
        return;
    }
    lt_check(run, valid, "setReclaimInternalFraction(%g) was not refused", v);
    /* (int) Math.round(v * FRACTION_ONE): Java's rounding, half up. */
    const int32_t units = (int32_t) floor(v * (double) RC_FRACTION_ONE + 0.5);
    lt_check(run, run->db.reclaim.internalFraction == units, "setReclaimInternalFraction(%g): "
            "expected %d units, got %d", v, units, run->db.reclaim.internalFraction);
    run->fractionUnits = units;
}

static void set_cache_size(struct lt_run *run) {
    struct err e;
    int64_t v = CACHE_ARGS[lt_rand(run, NELEM(CACHE_ARGS))];
    note(run, "setCacheSizeIndicator(%lld)", (long long) v);
    enum err_code rc = db_set_cache_size_indicator(&run->db, v, &e);
    if (rc != ERR_OK) {
        lt_check(run, rc == ERR_ARG && v < 1, "setCacheSizeIndicator(%lld) refused: %s",
                (long long) v, e.text);
        lt_check(run, run->db.cache_size_indicator == run->cacheIndicator, "a refused "
                "setCacheSizeIndicator changed the setting");
        return;
    }
    lt_check(run, v >= 1, "setCacheSizeIndicator(%lld) was not refused", (long long) v);
    lt_check(run, run->db.cache_size_indicator == v, "setCacheSizeIndicator(%lld): got %lld",
            (long long) v, (long long) run->db.cache_size_indicator);
    run->cacheIndicator = v;
}

static void setting(struct lt_run *run) {
    run->res.settings++;
    switch (lt_rand(run, 4)) {
    case 0: set_startup_distance(run); break;
    case 1: set_retain_duration(run); break;
    case 2: set_fraction(run); break;
    default: set_cache_size(run);
    }
    if (run->res.callersFault || run->failed) {
        return;
    }
    check_active(run);
    update_cuts(run);
}

/* The clock goes to the last user times, and stays there (015-55). */
static void enter_end_phase(struct lt_run *run) {
    run->endPhase = true;
    const int64_t at[] = {DBCLOCK_LAST_USER_TIME - lt_rand(run, 2000), DBCLOCK_LAST_USER_TIME,
            DBCLOCK_LAST_USER_TIME + 1, KL_MAX_TIME - lt_rand(run, 5), KL_MAX_TIME};
    run->now = at[lt_rand(run, NELEM(at))];
    run->maxClock = run->maxClock > run->now ? run->maxClock : run->now;
    note(run, "the end phase: clock %lld", (long long) run->now);
}

/* One step; false when the run ends. */
static bool step(struct lt_run *run) {
    if (run->step == run->endPhaseAt) {
        enter_end_phase(run);
    }
    if (run->endPhase) {
        int64_t t = run->now + lt_rand(run, 3);
        run->now = t < KL_MAX_TIME ? t : KL_MAX_TIME;
    } else {
        run->now += CLK_UNITS_PER_SEC / 40 + lt_rand(run, (int32_t) (CLK_UNITS_PER_SEC / 20));
    }
    run->maxClock = run->maxClock > run->now ? run->maxClock : run->now;
    if (run->step == run->faultAt) {
        transform(run, true);
        return run->open && !run->res.callersFault && !run->failed;
    }
    int32_t x = lt_rand(run, 100);
    if (x < 35) {
        put_small(run);
    } else if (x < 47) {
        put_at_limit(run);
    } else if (x < 54) {
        put_many_at_limit(run);
    } else if (x < 61) {
        delete_keys(run);
    } else if (x < 70) {
        transform(run, false);
    } else if (x < 75) {
        if (lt_rand(run, 3) == 0) {
            put_many_keys(run);
        } else {
            put_long_key(run);
        }
    } else if (x < 79) {
        clock_edge(run);
    } else if (x < 86) {
        setting(run);
    } else if (x < 88) {
        restart(run);
    } else {
        put_small(run);
        if (run->nref > 0 && !run->res.callersFault && !run->failed) {
            check_key(run, run->ref[lt_rand(run, run->nref)].key);
        }
    }
    return !run->res.callersFault && !run->failed;
}

static void temp_dir(char *out, size_t cap) {
    const char *t = getenv("TMPDIR");
    snprintf(out, cap, "%s/bergdb-t_limits-XXXXXX", t != NULL ? t : "/tmp");
    if (mkdtemp(out) == NULL) {
        out[0] = '\0';
    }
}

static void remove_dir(const char *dir) {
    char cmd[1200];
    snprintf(cmd, sizeof cmd, "rm -rf '%s'", dir);
    if (system(cmd) != 0) {
        printf("could not remove %s\n", dir);
    }
}

#ifdef BERGDB_TEST
/* The test build's seam (plat.h): the forces are no-ops, as what reaches
 * the disk is power.sh's part, not this harness's; the rest is real. In the
 * release build the forces are real. */
static int64_t lt_forces;

static enum err_code lt_force(int fd, enum plat_force_why why, struct err *e) {
    (void) fd;
    (void) why;
    (void) e;
    lt_forces++;
    return ERR_OK;
}

static enum err_code lt_force_dir(const char *dir, struct err *e) {
    (void) dir;
    (void) e;
    lt_forces++;
    return ERR_OK;
}
#endif

/* One run of steps from a seed. */
static void run_seed(uint64_t seed, int steps, struct lt_result *total) {
    static struct lt_run run;           /* large: its log */
    memset(&run, 0, sizeof run);
    run.seed = seed;
    run.r = seed * UINT64_C(0x9E3779B97F4A7C15) + 1;
    run.steps = steps;
    run.now = CLK_UNITS_PER_SEC;
    mem_init(&run.m);
    run.recordLimit = RECORD_LIMITS[lt_rand(&run, NELEM(RECORD_LIMITS))];
    run.smallNodes = lt_rand(&run, 3) == 0;
    run.builderDistance = STARTUP_DISTANCES[lt_rand(&run, NELEM(STARTUP_DISTANCES))];
    run.cacheSize = CACHE_SIZES[lt_rand(&run, NELEM(CACHE_SIZES))];
    run.endPhaseAt = lt_rand(&run, 3) == 0 ? steps * 3 / 4 + lt_rand(&run, steps / 4) : -1;
    run.faultAt = lt_rand(&run, 4) == 0 ? steps / 2 + lt_rand(&run, steps / 2) : -1;
    run.cacheIndicator = run.cacheSize;
    /* A new super root comes only when the tree grows a level: 1 to 3
     * before the last ordinal, the end comes within the run. */
    run.secondOrdinal = lt_rand(&run, 8) == 0 ? DB_LAST_TOP_ORDINAL - 1 - lt_rand(&run, 3) : 0;
    run.retain = INT64_MAX;
    run.fractionUnits = RC_DEFAULT_INTERNAL_FRACTION;
    run.lastUserTime = -1;
    run.maxClock = -1;
    temp_dir(run.dir, sizeof run.dir);
    REQUIRE(run.dir[0] != '\0');
    start_first(&run);
    for (run.step = 0; run.step < steps && run.open && !run.failed; run.step++) {
        if (!step(&run)) {
            break;
        }
    }
    if (!run.res.callersFault && !run.failed && run.open) {
        run.step = steps;
        check_all(&run);
        restart(&run);
        struct lt_op one = { strdup("/k/last"), malloc(1), 1, false };
        one.value[0] = 7;
        execute(&run, &one, 1, "put after the last restart", false);
        ops_free(&one, 1);
    }
    if (run.open) {
        struct err e;
        run.res.iterations += run.db.reclaim.iterationCount;
        if (!run.failed && !run.res.callersFault) {
            CHECK_EQ(db_recount(&run.db), 0);
        }
        run.open = false;
        db_close(&run.db, &e);
    }
    CHECK_MEM_ZERO(&run.m);
    remove_dir(run.dir);
    ref_free(&run);
    free(run.tf.out);
    printf("  limits seed %llu: %lld committed, refused: %lld size, %lld index nodes, %lld time, "
            "%lld clock, %lld top node ordinals; %lld settings calls, %lld restarts, %lld cuts, "
            "%lld reclaim iterations%s\n", (unsigned long long) seed,
            (long long) run.res.committed, (long long) run.res.refusedSize,
            (long long) run.res.refusedNodes, (long long) run.res.refusedTime,
            (long long) run.res.refusedClock, (long long) run.res.refusedOrdinals,
            (long long) run.res.settings, (long long) run.res.restarts,
            (long long) run.res.cuts, (long long) run.res.iterations,
            run.res.callersFault ? "; ended by the caller's fault" : "");
    total->committed += run.res.committed;
    total->refusedSize += run.res.refusedSize;
    total->refusedTime += run.res.refusedTime;
    total->refusedClock += run.res.refusedClock;
    total->restarts += run.res.restarts;
    total->cuts += run.res.cuts;
}

/* LimitsTester.testSeeds: short runs on fixed seeds, the unit tests: three
 * seeds of 40 steps (Java's take 100; in C's test build 3 of 100 take about
 * 2 s on a loaded F53), among them the end of the times (seed 3) and the
 * caller's fault (seed 2). BERGDB_LIMITS_SEEDS=A-B and BERGDB_LIMITS_STEPS=N
 * run others by hand, as testSeedsLong's 20 seeds of 500 steps:
 *
 *     BERGDB_LIMITS_SEEDS=1-20 BERGDB_LIMITS_STEPS=500 build/test/unit limits_
 *
 * (022-05: all passed, 6,760 transactions committed, 99 s in the test
 * build on a loaded F53). */
TEST(limits_seeds) {
    uint64_t from = 1, to = 3;
    int steps = 40;
    const char *s = getenv("BERGDB_LIMITS_SEEDS");
    if (s != NULL) {
        char *end;
        from = strtoull(s, &end, 10);
        to = *end == '-' ? strtoull(end + 1, NULL, 10) : from;
    }
    s = getenv("BERGDB_LIMITS_STEPS");
    if (s != NULL) {
        steps = atoi(s);
    }
    struct lt_result total;
    memset(&total, 0, sizeof total);
#ifdef BERGDB_TEST
    struct plat_io io = *plat_io_real();
    io.force = lt_force;
    io.force_dir = lt_force_dir;
    plat_io_set(&io);
#endif
    for (uint64_t seed = from; seed <= to; seed++) {
        run_seed(seed, steps, &total);
    }
#ifdef BERGDB_TEST
    plat_io_set(NULL);
    printf("  limits: %lld forces (no-ops in the test build)\n", (long long) lt_forces);
#endif
    CHECK(total.committed > 0);
}

const struct test limits_tests[] = {
    TEST_ENTRY(limits_seeds),
    TEST_END
};
