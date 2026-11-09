/* Functional tests of the API (bergdb 012-01, 6.4; 012-09): programs that use
 * include/bergdb.h only. A database created in a directory, its transactions
 * and reads; the refusals before the go point, which leave the database as
 * it was; a failed database (P7) and the allocation failures in turn through
 * the options' counts; a callback that calls its database. Each test ends
 * with the allocator's count 0. */
#define TEST_MAIN
#include <stdlib.h>
#include <sys/stat.h>
#include <unistd.h>
#include "test.h"
#include "bergdb.h"

/* A new empty directory for a test's database (under TMPDIR). */
static void temp_dir(char *out, size_t cap) {
    const char *t = getenv("TMPDIR");
    snprintf(out, cap, "%s/bergdb-func-XXXXXX", t != NULL ? t : "/tmp");
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

static int64_t file_size(const char *dir, const char *name) {
    char path[1200];
    struct stat st;
    snprintf(path, sizeof path, "%s/%s", dir, name);
    return stat(path, &st) == 0 ? (int64_t) st.st_size : -1;
}

static void options(struct bergdb_options *o, struct bergdb_test_clock *clock,
        struct bergdb_mem *m) {
    bergdb_options_init(o);
    o->clock = bergdb_test_clock_time;
    o->clock_ctx = clock;
    memcpy(o->id, bergdb_test_id, BERGDB_ID_SIZE);
    o->max_node_size = 8;
    o->startup_distance = 1000;
    o->mem = m;
}

static const uint8_t *k(const char *ikey, uint8_t *buf, size_t *len) {
    *len = strlen(ikey);
    bergdb_ikey_to_bkey((const uint8_t *) ikey, *len, buf);
    return buf;
}

/* A transaction of puts of /k/from to /k/to-1 (values "vN") at clock time tt. */
static int put_keys(bergdb_db *db, struct bergdb_test_clock *clock, int64_t tt, int from, int to,
        struct bergdb_executed *ex) {
    bergdb_trans *t;
    if (tt > clock->time) {
        bergdb_test_clock_set(clock, tt);
    }
    int rc = bergdb_trans_new(db, &t);
    if (rc != BERGDB_OK) {
        return rc;
    }
    for (int i = from; i < to && rc == BERGDB_OK; i++) {
        char ikey[32], value[32];
        uint8_t bkey[32];
        size_t kl;
        snprintf(ikey, sizeof ikey, "/k/%d", i);
        snprintf(value, sizeof value, "v%d", i);
        rc = bergdb_trans_put(t, k(ikey, bkey, &kl), kl, (const uint8_t *) value,
                strlen(value));
    }
    if (rc == BERGDB_OK) {
        rc = bergdb_execute(db, t, ex);
    }
    bergdb_trans_free(t);
    return rc;
}

/* Real read results across close/open, through the API (bergdb 005-70). */
TEST(api_stm_after_restart) {
    for (int mode = 0; mode < 2; mode++) {
        char dir[1024], errbuf[BERGDB_ERRBUF_SIZE];
        temp_dir(dir, sizeof dir);
        REQUIRE(dir[0] != '\0');
        struct bergdb_mem m = {0};
        struct bergdb_test_clock clock = {0};
        struct bergdb_options o;
        options(&o, &clock, &m);
        o.startup_distance = mode == 0 ? 100 : 1000000;
        bergdb_db *db;
        REQUIRE(bergdb_open(dir, &o, &db, NULL, errbuf) == BERGDB_OK);
        struct bergdb_executed ex;
        CHECK_EQ(put_keys(db, &clock, 10, 1, 2, &ex), BERGDB_OK);
        bergdb_read *rd;
        REQUIRE(bergdb_read_new(db, &rd) == BERGDB_OK);
        struct bergdb_one one;
        uint8_t key[4], out[2];
        CHECK_EQ(bergdb_ikey_to_bkey((const uint8_t *) "/k/1", 4, key), BERGDB_OK);
        CHECK_EQ(bergdb_ikey_to_bkey((const uint8_t *) "/j", 2, out), BERGDB_OK);
        CHECK_EQ(bergdb_get_one(db, rd, BERGDB_LATEST, key, 4, &one), BERGDB_OK);
        CHECK(one.value != NULL && one.value_len == 2 && memcmp(one.value, "v1", 2) == 0);
        int64_t old_read_time = one.actual_lookup_time;
        bergdb_trans *t;
        REQUIRE(bergdb_trans_new(db, &t) == BERGDB_OK);
        bergdb_test_clock_set(&clock, 20);
        CHECK_EQ(bergdb_trans_put(t, key, 4, (const uint8_t *) "new", 3), BERGDB_OK);
        CHECK_EQ(bergdb_execute(db, t, &ex), BERGDB_OK);
        bergdb_trans_free(t);
        /* The last recovered commit has no writes. */
        CHECK_EQ(put_keys(db, &clock, 30, 0, 0, &ex), BERGDB_OK);
        CHECK_EQ(bergdb_get_one(db, rd, BERGDB_LATEST, key, 4, &one), BERGDB_OK);
        int64_t boundary = one.actual_lookup_time;
        bergdb_read_free(rd);
        CHECK_EQ(bergdb_close(db), BERGDB_OK);
        CHECK_EQ(m.live_total, 0);

        REQUIRE(bergdb_open(dir, &o, &db, NULL, errbuf) == BERGDB_OK);
        REQUIRE(bergdb_trans_new(db, &t) == BERGDB_OK);
        CHECK_EQ(bergdb_trans_key_read(t, key, 4), BERGDB_OK);
        CHECK_EQ(bergdb_trans_lookup_time(t, old_read_time), BERGDB_OK);
        CHECK_EQ(bergdb_trans_put(t, out, 2, (const uint8_t *) "result", 6), BERGDB_OK);
        struct bergdb_stats before, after;
        CHECK_EQ(bergdb_stats(db, &before), BERGDB_OK);
        CHECK_EQ(bergdb_execute(db, t, &ex), BERGDB_RERUN);
        CHECK_EQ(bergdb_stats(db, &after), BERGDB_OK);
        CHECK_EQ(after.stream_length, before.stream_length);
        CHECK_EQ(bergdb_trans_lookup_time(t, boundary), BERGDB_OK);
        CHECK_EQ(bergdb_execute(db, t, &ex), BERGDB_OK);
        /* The first unrelated write preserves coverage back to the boundary. */
        CHECK_EQ(bergdb_execute(db, t, &ex), BERGDB_OK);
        CHECK_EQ(put_keys(db, &clock, 40, 1, 2, &ex), BERGDB_OK);
        CHECK_EQ(bergdb_execute(db, t, &ex), BERGDB_RERUN);
        bergdb_trans_free(t);
        CHECK_EQ(bergdb_close(db), BERGDB_OK);
        CHECK_EQ(m.live_total, 0);
        remove_dir(dir);
    }
}

TEST(api_create_and_read) {
    char dir[1024];
    temp_dir(dir, sizeof dir);
    REQUIRE(dir[0] != '\0');
    struct bergdb_mem m = {0};
    struct bergdb_test_clock clock = {0};
    struct bergdb_options o;
    struct bergdb_start_info info;
    char errbuf[BERGDB_ERRBUF_SIZE];
    bergdb_db *db;
    options(&o, &clock, &m);
    bergdb_test_clock_set(&clock, 1000);
    REQUIRE(bergdb_open(dir, &o, &db, &info, errbuf) == BERGDB_OK);
    CHECK_EQ(info.start_pos, 0);
    CHECK_EQ(info.start_time, 1000);
    CHECK_EQ(info.trans_count, 1);
    CHECK_EQ(info.last_pos, 263);
    CHECK_EQ(info.startup_distance, o.startup_distance);   /* in force (005-73, F1) */

    struct bergdb_executed ex;
    CHECK(put_keys(db, &clock, 2000, 0, 30, &ex) == BERGDB_OK);
    CHECK_EQ(ex.tt, 2000);
    CHECK_EQ(ex.tpos, 264);
    CHECK(put_keys(db, &clock, 0, 30, 40, &ex) == BERGDB_OK);    /* the clock unchanged */
    CHECK_EQ(ex.tt, 2001);
    int64_t now;
    bergdb_test_clock_set(&clock, 3000);
    CHECK(bergdb_current_time(db, &now) == BERGDB_OK);
    CHECK_EQ(now, 3000);
    CHECK(put_keys(db, &clock, 0, 40, 41, &ex) == BERGDB_OK);
    CHECK_EQ(ex.tt, 3001);                  /* later than the now (012-01, 4.4) */
    const int64_t tpos3 = ex.tpos;
    {   /* a delete, and a delete of a key that has no value */
        bergdb_trans *t;
        uint8_t b[32];
        size_t kl;
        bergdb_test_clock_set(&clock, 4000);
        REQUIRE(bergdb_trans_new(db, &t) == BERGDB_OK);
        CHECK(bergdb_trans_delete(t, k("/k/5", b, &kl), kl) == BERGDB_OK);
        CHECK(bergdb_trans_delete(t, k("/nothing", b, &kl), kl) == BERGDB_OK);
        CHECK(bergdb_execute(db, t, &ex) == BERGDB_OK);
        bergdb_trans_free(t);
    }

    bergdb_read *rd;
    REQUIRE(bergdb_read_new(db, &rd) == BERGDB_OK);
    struct bergdb_one one;
    uint8_t b[32];
    size_t kl;
    CHECK(bergdb_get_one(db, rd, BERGDB_LATEST, k("/k/7", b, &kl), kl, &one) == BERGDB_OK);
    CHECK(one.value != NULL && one.value_len == 2 && memcmp(one.value, "v7", 2) == 0);
    CHECK_EQ(one.tpos, 264);
    CHECK(bergdb_get_one(db, rd, BERGDB_LATEST, k("/k/5", b, &kl), kl, &one) == BERGDB_OK);
    CHECK(one.value == NULL);                       /* deleted */
    CHECK(bergdb_get_one(db, rd, 3500, k("/k/5", b, &kl), kl, &one) == BERGDB_OK);
    CHECK(one.value != NULL);                       /* before the delete */
    CHECK(bergdb_get_one(db, rd, 2000, k("/k/35", b, &kl), kl, &one) == BERGDB_OK);
    CHECK(one.value == NULL);                       /* not yet */

    struct bergdb_range r;
    struct bergdb_many many;
    bergdb_range_init(&r);
    CHECK(bergdb_get_many(db, rd, &r, &many) == BERGDB_OK);
    CHECK_EQ((int64_t) many.count, 40);             /* 41 puts, one deleted */
    CHECK(many.eod);
    /* Before the first transaction (1000): no state, and the end at once
     * (bergdb 020-27, C2; eod was false). */
    r.lookup_time = 999;
    CHECK(bergdb_get_many(db, rd, &r, &many) == BERGDB_OK);
    CHECK_EQ((int64_t) many.count, 0);
    CHECK(many.eod);
    r.lookup_time = BERGDB_LATEST;
    r.max_count = 3;
    r.forward = false;
    CHECK(bergdb_get_many(db, rd, &r, &many) == BERGDB_OK);
    CHECK_EQ((int64_t) many.count, 3);
    CHECK(many.count == 3 && many.kvts[0].key_len == 4 && memcmp(many.kvts[0].value, "v9", 2) == 0);
    bergdb_range_init(&r);
    uint8_t pb[32];
    size_t pl;
    r.prefix = k("/k/1", pb, &pl);
    r.prefix_len = pl;
    r.start_key = r.prefix;
    r.start_key_len = pl;
    r.inclusive = false;
    CHECK(bergdb_get_many(db, rd, &r, &many) == BERGDB_OK);
    CHECK_EQ((int64_t) many.count, 10);             /* /k/10 to /k/19 */

    struct bergdb_stored st;
    CHECK(bergdb_get_trans(db, rd, tpos3, &st) == BERGDB_OK);
    CHECK_EQ(st.tt, 3001);
    CHECK_EQ((int64_t) st.count, 1);
    CHECK(st.count == 1 && st.values[0].value_len == 3 && memcmp(st.values[0].value, "v40", 3) == 0);
    CHECK(bergdb_get_trans(db, rd, 7, &st) == BERGDB_ARG);
    CHECK(bergdb_get_trans(db, rd, 1000000, &st) == BERGDB_ARG);       /* past the end */
    bergdb_read_free(rd);

    struct bergdb_stats s;
    CHECK(bergdb_sync(db, 0, BERGDB_SYNC_ORDINARY) == BERGDB_OK);
    CHECK(bergdb_stats(db, &s) == BERGDB_OK);
    CHECK_EQ(s.durable_length, s.stream_length);
    CHECK_EQ(s.transaction_count, 4);
    CHECK_EQ(s.kv_count, 41 + 2);
    const int64_t length = s.stream_length;
    CHECK(bergdb_close(db) == BERGDB_OK);
    CHECK_EQ(m.live_total, 0);
    CHECK_EQ(file_size(dir, "00000000000000.bergdb"), length);
    CHECK(file_size(dir, "bergdb.lock") > 0);

    /* A start of the existing database (012-10): the bounded startup, the
     * same reads, nothing written; then a transaction after it. */
    REQUIRE(bergdb_open(dir, &o, &db, &info, errbuf) == BERGDB_OK);
    CHECK_EQ(file_size(dir, "00000000000000.bergdb"), length);
    CHECK_EQ(info.last_pos + 1, length);
    REQUIRE(bergdb_read_new(db, &rd) == BERGDB_OK);
    CHECK(bergdb_get_one(db, rd, BERGDB_LATEST, k("/k/7", b, &kl), kl, &one) == BERGDB_OK);
    CHECK(one.value != NULL && one.value_len == 2 && memcmp(one.value, "v7", 2) == 0);
    CHECK_EQ(one.tpos, 264);
    CHECK(bergdb_get_one(db, rd, BERGDB_LATEST, k("/k/5", b, &kl), kl, &one) == BERGDB_OK);
    CHECK(one.value == NULL);                       /* deleted */
    CHECK(bergdb_get_one(db, rd, 3500, k("/k/5", b, &kl), kl, &one) == BERGDB_OK);
    CHECK(one.value != NULL);                       /* before the delete */
    bergdb_range_init(&r);
    CHECK(bergdb_get_many(db, rd, &r, &many) == BERGDB_OK);
    CHECK_EQ((int64_t) many.count, 40);
    bergdb_read_free(rd);
    CHECK(put_keys(db, &clock, 5000, 41, 45, &ex) == BERGDB_OK);
    CHECK_EQ(ex.tt, 5000);
    CHECK_EQ(ex.tpos, length);
    CHECK(bergdb_close(db) == BERGDB_OK);
    CHECK_EQ(m.live_total, 0);
    remove_dir(dir);
}

/* The refusals before the go point leave the database as it was. */
static int calls_back;
static bergdb_db *the_db;

static int stop_calls_db(void *ctx, const struct bergdb_kvt *kvt) {
    (void) ctx, (void) kvt;
    bergdb_read *rd;
    calls_back = bergdb_read_new(the_db, &rd);      /* from a callback: refused */
    return BERGDB_ADD_AND_STOP;
}

TEST(api_refusals) {
    struct bergdb_mem m = {0};
    struct bergdb_test_clock clock = {0};
    struct bergdb_options o;
    bergdb_db *db;
    options(&o, &clock, &m);
    bergdb_test_clock_set(&clock, 1000);
    REQUIRE(bergdb_open(NULL, &o, &db, NULL, NULL) == BERGDB_OK);   /* in memory */
    struct bergdb_executed ex;
    CHECK(put_keys(db, &clock, 2000, 0, 5, &ex) == BERGDB_OK);
    struct bergdb_stats s0, s;
    bergdb_stats(db, &s0);

    /* The STM: /k/1 written at 2000, read at 1500. */
    bergdb_trans *t;
    uint8_t b[32];
    size_t kl;
    REQUIRE(bergdb_trans_new(db, &t) == BERGDB_OK);
    CHECK(bergdb_trans_key_read(t, k("/k/1", b, &kl), kl) == BERGDB_OK);
    CHECK(bergdb_trans_lookup_time(t, 1500) == BERGDB_OK);
    CHECK(bergdb_trans_put(t, k("/x", b, &kl), kl, (const uint8_t *) "", 0) == BERGDB_OK);
    bergdb_test_clock_set(&clock, 3000);
    CHECK(bergdb_execute(db, t, &ex) == BERGDB_RERUN);
    CHECK(strncmp(bergdb_errmsg(db), "RerunException", 14) == 0);
    CHECK(bergdb_trans_lookup_time(t, 2500) == BERGDB_OK);   /* read again: no conflict */
    CHECK(bergdb_trans_lookup_time(t, -1) == BERGDB_ARG);
    bergdb_stats(db, &s);
    CHECK_EQ(s.stream_length, s0.stream_length);
    CHECK(bergdb_execute(db, t, &ex) == BERGDB_OK);
    CHECK_EQ(ex.tt, 3000);
    bergdb_trans_free(t);

    /* A clock out of range (005-18). */
    bergdb_test_clock_set(&clock, BERGDB_MAX_TIME + 1);
    bergdb_stats(db, &s0);
    CHECK(put_keys(db, &clock, 0, 10, 11, &ex) == BERGDB_LIMIT);
    CHECK(strncmp(bergdb_errmsg(db), "DbException", 11) == 0);
    bergdb_stats(db, &s);
    CHECK_EQ(s.stream_length, s0.stream_length);

    /* Bad arguments. */
    CHECK(bergdb_trans_new(db, NULL) == BERGDB_ARG);
    CHECK(bergdb_execute(db, NULL, &ex) == BERGDB_ARG);
    CHECK(bergdb_set_startup_distance(db, -1) == BERGDB_ARG);
    CHECK(bergdb_sync(db, 0, 99) == BERGDB_ARG);

    /* A callback that calls its database (section D). */
    bergdb_read *rd;
    REQUIRE(bergdb_read_new(db, &rd) == BERGDB_OK);
    struct bergdb_range r;
    struct bergdb_many many;
    bergdb_range_init(&r);
    r.stop = stop_calls_db;
    the_db = db;
    calls_back = -1;
    CHECK(bergdb_get_many(db, rd, &r, &many) == BERGDB_OK);
    CHECK_EQ(calls_back, BERGDB_STATE);
    CHECK_EQ((int64_t) many.count, 1);

    /* getTrans at a position inside a record: corrupt data, as for the other
     * reads, fails the database (005-34; Java's DbFailedException). */
    struct bergdb_stored st;
    CHECK(bergdb_get_trans(db, rd, 264 + 8, &st) == BERGDB_FAILED);
    CHECK(put_keys(db, &clock, 0, 20, 21, &ex) == BERGDB_FAILED);
    CHECK(strstr(bergdb_errmsg(db), "DbFailedException") != NULL);
    bergdb_read_free(rd);
    CHECK(bergdb_close(db) == BERGDB_OK);
    CHECK_EQ(m.live_total, 0);
}

/* The key and value transformations (bergdb.h): a value computed from the
 * previous one at the transaction's time (a counter, without a read set),
 * and a key known only then. */
struct counter {
    uint8_t out[8];
    uint8_t key[32];
    size_t key_len;
    int calls;
};

static void count_up(void *ctx, int64_t tt, const uint8_t *previous, size_t previous_len,
        const uint8_t **value, size_t *value_len) {
    (void) tt;
    struct counter *c = ctx;
    uint8_t n = previous != NULL && previous_len == 8 ? previous[7] : 0;
    memset(c->out, 0, sizeof c->out);
    c->out[7] = (uint8_t) (n + 1);
    *value = c->out;
    *value_len = 8;
    c->calls++;
}

static void key_of_time(void *ctx, int64_t tt, const uint8_t **key, size_t *key_len) {
    struct counter *c = ctx;
    char ikey[32];
    snprintf(ikey, sizeof ikey, "/t/%lld", (long long) tt);
    c->key_len = strlen(ikey);
    bergdb_ikey_to_bkey((const uint8_t *) ikey, c->key_len, c->key);
    *key = c->key;
    *key_len = c->key_len;
}

TEST(api_transformations) {
    struct bergdb_mem m = {0};
    struct bergdb_test_clock clock = {0};
    struct bergdb_options o;
    bergdb_db *db;
    options(&o, &clock, &m);
    bergdb_test_clock_set(&clock, 1000);
    REQUIRE(bergdb_open(NULL, &o, &db, NULL, NULL) == BERGDB_OK);
    struct counter c;
    memset(&c, 0, sizeof c);
    struct bergdb_transform tf = { NULL, count_up, &c };
    uint8_t b[32];
    size_t kl;
    const uint8_t zero[8] = {0};
    for (int i = 0; i < 3; i++) {
        bergdb_trans *t;
        REQUIRE(bergdb_trans_new(db, &t) == BERGDB_OK);
        CHECK(bergdb_trans_put_transformed(t, k("/c", b, &kl), kl, zero, 8, &tf) == BERGDB_OK);
        bergdb_test_clock_set(&clock, 2000 + 10 * i);
        CHECK(bergdb_execute(db, t, NULL) == BERGDB_OK);
        bergdb_trans_free(t);
    }
    CHECK_EQ(c.calls, 3);
    bergdb_read *rd;
    REQUIRE(bergdb_read_new(db, &rd) == BERGDB_OK);
    struct bergdb_one one;
    CHECK(bergdb_get_one(db, rd, BERGDB_LATEST, k("/c", b, &kl), kl, &one) == BERGDB_OK);
    CHECK(one.value != NULL && one.value_len == 8 && one.value[7] == 3);
    CHECK(bergdb_get_one(db, rd, 2010, k("/c", b, &kl), kl, &one) == BERGDB_OK);
    CHECK(one.value != NULL && one.value[7] == 2);

    struct bergdb_transform kt = { key_of_time, NULL, &c };
    bergdb_trans *t;
    REQUIRE(bergdb_trans_new(db, &t) == BERGDB_OK);
    CHECK(bergdb_trans_put_transformed(t, k("/x", b, &kl), kl, (const uint8_t *) "v", 1, &kt)
            == BERGDB_OK);
    bergdb_test_clock_set(&clock, 3000);
    struct bergdb_executed ex;
    CHECK(bergdb_execute(db, t, &ex) == BERGDB_OK);
    bergdb_trans_free(t);
    CHECK_EQ(ex.tt, 3000);
    CHECK(bergdb_get_one(db, rd, BERGDB_LATEST, k("/t/3000", b, &kl), kl, &one) == BERGDB_OK);
    CHECK(one.value != NULL && one.value_len == 1 && one.value[0] == 'v');
    CHECK(bergdb_get_one(db, rd, BERGDB_LATEST, k("/x", b, &kl), kl, &one) == BERGDB_OK);
    CHECK(one.value == NULL);
    bergdb_read_free(rd);
    CHECK(bergdb_close(db) == BERGDB_OK);
    CHECK_EQ(m.live_total, 0);
}

/* The allocation failures in turn through the API: each run gives NOMEM at
 * the open (nothing left), a transaction refused with NOMEM (the database
 * goes on, the transaction is executed again), or a failed database (P7):
 * every later transaction and read gives BERGDB_FAILED, sync and close
 * work; the count 0 after each close. */
TEST(api_alloc_failures) {
    int64_t refused = 0, failed = 0, opens = 0;
    for (int64_t at = 1; at < 100000; at++) {
        struct bergdb_mem m = {0};
        struct bergdb_test_clock clock = {0};
        struct bergdb_options o;
        bergdb_db *db;
        options(&o, &clock, &m);
        m.fail_at = at;
        bergdb_test_clock_set(&clock, 1000);
        int rc = bergdb_open(NULL, &o, &db, NULL, NULL);
        if (rc != BERGDB_OK) {
            CHECK_EQ(rc, BERGDB_NOMEM);
            CHECK_EQ(m.live_total, 0);
            opens++;
            continue;
        }
        bool hit = false, dead = false;
        for (int i = 0; i < 12 && !dead; i++) {
            struct bergdb_executed ex;
            rc = put_keys(db, &clock, 2000 + 10 * i, 5 * i, 5 * i + 7, &ex);
            if (rc == BERGDB_NOMEM) {
                hit = true;
                refused++;
                m.fail_at = 0;
                CHECK(put_keys(db, &clock, 0, 5 * i, 5 * i + 7, &ex) == BERGDB_OK);
            } else if (rc == BERGDB_FAILED) {
                hit = true;
                failed++;
                dead = true;
                m.fail_at = 0;
                CHECK(put_keys(db, &clock, 0, 0, 1, &ex) == BERGDB_FAILED);
                bergdb_read *rd;
                if (bergdb_read_new(db, &rd) == BERGDB_OK) {
                    struct bergdb_one one;
                    uint8_t b[32];
                    size_t kl;
                    CHECK(bergdb_get_one(db, rd, BERGDB_LATEST, k("/k/1", b, &kl), kl, &one)
                            == BERGDB_FAILED);
                    bergdb_read_free(rd);
                }
                CHECK(bergdb_sync(db, 0, BERGDB_SYNC_ORDINARY) == BERGDB_OK);
            } else {
                CHECK_EQ(rc, BERGDB_OK);
            }
        }
        bergdb_close(db);
        CHECK_EQ(m.live_total, 0);
        if (!hit && m.allocs < at) {
            break;
        }
    }
    CHECK(opens > 0 && refused > 0 && failed > 0);
    printf("  api_alloc_failures: %lld opens refused, %lld transactions refused (NOMEM), "
            "%lld failed databases\n", (long long) opens, (long long) refused,
            (long long) failed);
}

/* A read whose node load fails on memory is a refusal, not a failed
 * database (012-14, 7.2): a read has no go point (03-c-api.md, the error
 * table: NOMEM is a refusal before a go point; Java's reads do not fail the
 * database on an OutOfMemoryError). Under a budget of one byte every read
 * loads; allocation 1 to 6 of each get_one fails in turn: BERGDB_NOMEM, and
 * the same read again gives the value; never BERGDB_FAILED. */
TEST(api_read_nomem) {
    struct bergdb_mem m = {0};
    struct bergdb_test_clock clock = {0};
    struct bergdb_options o;
    bergdb_db *db;
    options(&o, &clock, &m);
    o.cache_size_indicator = 1;
    bergdb_test_clock_set(&clock, 1000);
    REQUIRE(bergdb_open(NULL, &o, &db, NULL, NULL) == BERGDB_OK);
    struct bergdb_executed ex;
    for (int i = 0; i < 20; i++) {
        REQUIRE(put_keys(db, &clock, 2000 + 10 * i, 10 * i, 10 * i + 10, &ex) == BERGDB_OK);
    }
    bergdb_read *rd;
    REQUIRE(bergdb_read_new(db, &rd) == BERGDB_OK);
    int64_t refused = 0;
    for (int key = 0; key < 200; key += 7) {
        for (int64_t j = 1; j <= 6; j++) {
            char ikey[32], value[32];
            uint8_t b[32];
            size_t kl;
            struct bergdb_one one;
            snprintf(ikey, sizeof ikey, "/k/%d", key);
            snprintf(value, sizeof value, "v%d", key);
            m.fail_at = m.allocs + j;
            int rc = bergdb_get_one(db, rd, BERGDB_LATEST, k(ikey, b, &kl), kl, &one);
            m.fail_at = 0;
            CHECK(rc == BERGDB_OK || rc == BERGDB_NOMEM);
            if (rc == BERGDB_NOMEM) {
                refused++;
                rc = bergdb_get_one(db, rd, BERGDB_LATEST, k(ikey, b, &kl), kl, &one);
            }
            REQUIRE(rc == BERGDB_OK);
            CHECK(one.value != NULL && one.value_len == strlen(value)
                    && memcmp(one.value, value, one.value_len) == 0);
        }
    }
    CHECK(refused > 0);
    bergdb_read_free(rd);
    bergdb_close(db);
    CHECK_EQ(m.live_total, 0);
    printf("  api_read_nomem: %lld reads refused (NOMEM) and read again\n", (long long) refused);
}

/* Every call that takes a key takes any bkey, as Java's Core API does (bergdb
 * 022-02; 021-06): bkeys without an ikey, the byte 0, 021-04's CK1 (the bkey
 * of "/dd/-a" ED A0 80), 0x31 and FF FF, are keys as CK2 (the bkey of
 * "/dd/-a" EF BF BD, U+FFFD) is: put, read by getOne and by getMany in byte
 * order, by a prefix that is no ikey's, and after a restart; CK1 and CK2
 * stay two keys (Utf8ReadTester.testCk1AndCk2StayTwoKeys on the Core), and
 * bergdb_bkey_to_ikey gives an ikey for CK2 only. */
TEST(api_any_bkey) {
    static const struct { uint8_t b[9]; size_t n; } keys[] = {    /* in byte order */
        { { 0x00 }, 1 },
        { { 0x01, 0x66, 0x66, 0x01, 0x2f, 0x63, 0xef, 0xa2, 0x82 }, 9 },     /* CK1 */
        { { 0x01, 0x66, 0x66, 0x01, 0x2f, 0x63, 0xf1, 0xc1, 0xbf }, 9 },     /* CK2 */
        { { 0x31 }, 1 },
        { { 0xff, 0xff }, 2 },
    };
    static const char *const values[] = { "v0", "ck1", "ck2", "v3", "v4" };
    static const uint8_t ck1_ikey[] = { '/', 'd', 'd', '/', '-', 'a', 0xed, 0xa0, 0x80 };
    static const uint8_t ck2_ikey[] = { '/', 'd', 'd', '/', '-', 'a', 0xef, 0xbf, 0xbd };
    uint8_t ik[16], bk[16];
    for (int i = 0; i < 5; i++) {
        CHECK_EQ(bergdb_bkey_to_ikey(keys[i].b, keys[i].n, ik), i == 2 ? BERGDB_OK : BERGDB_ARG);
    }
    CHECK_EQ(bergdb_bkey_to_ikey(keys[2].b, 9, ik), BERGDB_OK);
    CHECK(memcmp(ik, ck2_ikey, 9) == 0);
    CHECK_EQ(bergdb_ikey_to_bkey(ik, 9, bk), BERGDB_OK);
    CHECK(memcmp(bk, keys[2].b, 9) == 0);
    CHECK_EQ(bergdb_ikey_to_bkey(ck1_ikey, 9, bk), BERGDB_ARG);

    char dir[1024], errbuf[BERGDB_ERRBUF_SIZE];
    temp_dir(dir, sizeof dir);
    REQUIRE(dir[0] != '\0');
    struct bergdb_mem m = {0};
    struct bergdb_test_clock clock = {0};
    struct bergdb_options o;
    options(&o, &clock, &m);
    bergdb_test_clock_set(&clock, 1000);
    bergdb_db *db;
    REQUIRE(bergdb_open(dir, &o, &db, NULL, errbuf) == BERGDB_OK);
    bergdb_trans *t;
    REQUIRE(bergdb_trans_new(db, &t) == BERGDB_OK);
    for (int i = 4; i >= 0; i--) {
        CHECK_EQ(bergdb_trans_put(t, keys[i].b, keys[i].n, (const uint8_t *) values[i],
                strlen(values[i])), BERGDB_OK);
    }
    CHECK_EQ(bergdb_execute(db, t, NULL), BERGDB_OK);
    bergdb_trans_free(t);
    for (int restart = 0; restart < 2; restart++) {
        if (restart == 1) {
            CHECK_EQ(bergdb_close(db), BERGDB_OK);
            CHECK_EQ(m.live_total, 0);
            REQUIRE(bergdb_open(dir, &o, &db, NULL, errbuf) == BERGDB_OK);
        }
        bergdb_read *rd;
        REQUIRE(bergdb_read_new(db, &rd) == BERGDB_OK);
        struct bergdb_one one;
        for (int i = 0; i < 5; i++) {
            CHECK_EQ(bergdb_get_one(db, rd, BERGDB_LATEST, keys[i].b, keys[i].n, &one),
                    BERGDB_OK);
            CHECK(one.value != NULL && one.value_len == strlen(values[i])
                    && memcmp(one.value, values[i], one.value_len) == 0);
        }
        struct bergdb_range r;
        struct bergdb_many many;
        bergdb_range_init(&r);
        CHECK_EQ(bergdb_get_many(db, rd, &r, &many), BERGDB_OK);
        CHECK_EQ((int64_t) many.count, 5);
        for (size_t i = 0; i < many.count && i < 5; i++) {
            CHECK(many.kvts[i].key_len == keys[i].n
                    && memcmp(many.kvts[i].key, keys[i].b, keys[i].n) == 0);
        }
        r.prefix = keys[1].b;           /* the bkey of "/dd/-a" ED: no ikey's */
        r.prefix_len = 7;
        r.start_key = r.prefix;
        r.start_key_len = r.prefix_len;
        CHECK_EQ(bergdb_get_many(db, rd, &r, &many), BERGDB_OK);
        CHECK_EQ((int64_t) many.count, 1);
        CHECK(many.count == 1 && memcmp(many.kvts[0].value, "ck1", 3) == 0);
        r.prefix_len = 6;               /* the bkey of "/dd/-a": CK1 and CK2 */
        r.start_key_len = r.prefix_len;
        CHECK_EQ(bergdb_get_many(db, rd, &r, &many), BERGDB_OK);
        CHECK_EQ((int64_t) many.count, 2);
        bergdb_read_free(rd);
    }
    CHECK_EQ(bergdb_close(db), BERGDB_OK);
    CHECK_EQ(m.live_total, 0);
    remove_dir(dir);
}

/* DbTesterLongKeys.key: length bytes of 'k', start's bytes first (malloc'd). */
static uint8_t *long_key(const char *start, size_t length) {
    uint8_t *key = malloc(length);
    if (key != NULL) {
        memset(key, 'k', length);
        memcpy(key, start, strlen(start));
    }
    return key;
}

static int put_one(bergdb_db *db, const uint8_t *key, size_t key_len, const char *value) {
    bergdb_trans *t;
    int rc = bergdb_trans_new(db, &t);
    if (rc == BERGDB_OK) {
        rc = bergdb_trans_put(t, key, key_len, (const uint8_t *) value, strlen(value));
    }
    if (rc == BERGDB_OK) {
        rc = bergdb_execute(db, t, NULL);
    }
    bergdb_trans_free(t);
    return rc;
}

static bool value_is(bergdb_db *db, const uint8_t *key, size_t key_len, const char *value) {
    bergdb_read *rd;
    struct bergdb_one one;
    if (bergdb_read_new(db, &rd) != BERGDB_OK) {
        return false;
    }
    bool is = bergdb_get_one(db, rd, BERGDB_LATEST, key, key_len, &one) == BERGDB_OK
            && one.value != NULL && one.value_len == strlen(value)
            && memcmp(one.value, value, one.value_len) == 0;
    bergdb_read_free(rd);
    return is;
}

/* The keys of a scan of the whole database, forward or backward, are a and b. */
static bool scan_is(bergdb_db *db, bool forward, const uint8_t *a, size_t a_len,
        const uint8_t *b, size_t b_len) {
    bergdb_read *rd;
    struct bergdb_range r;
    struct bergdb_many many;
    if (bergdb_read_new(db, &rd) != BERGDB_OK) {
        return false;
    }
    bergdb_range_init(&r);
    r.forward = forward;
    bool is = bergdb_get_many(db, rd, &r, &many) == BERGDB_OK && many.count == 2
            && many.kvts[0].key_len == a_len && memcmp(many.kvts[0].key, a, a_len) == 0
            && many.kvts[1].key_len == b_len && memcmp(many.kvts[1].key, b, b_len) == 0;
    bergdb_read_free(rd);
    return is;
}

/* Java's DbTesterLongKeys (bergdb 021-16; 020-24-05, U5-1 and U5-2): a key
 * is a tree of key nodes with a level per segment of 7 bytes, and Java's
 * walks of it were recursions with a frame per level, a StackOverflowError
 * at a start with a key of about 90 KB (the start's check) and at a put of
 * a key of 1,000,000 bytes after one of 100,000 (dirtyNodeBound's
 * freshTreeBound). C's walks have no recursion: the start's check walks the
 * node table, dag_dirty_node_bound keeps its work in an array, and the
 * reads are loops. testLongKeyRestart: a key of 200,000 bytes and a short
 * one, put, the database opened again from its directory, the values read,
 * both scans, the check, a longer put. testLongKeyAfterItsStart: a key of
 * 1,000,000 bytes after one of 100,000 with the same start, a startup
 * distance of 200 MB, then a short put. Both on the test build's stack,
 * under AddressSanitizer. */
TEST(api_long_keys) {
    char dir[1024];
    temp_dir(dir, sizeof dir);
    REQUIRE(dir[0] != '\0');
    struct bergdb_mem m = {0};
    struct bergdb_test_clock clock = {0};
    struct bergdb_options o;
    bergdb_db *db;
    bergdb_options_init(&o);
    o.clock = bergdb_test_clock_time;
    o.clock_ctx = &clock;
    memcpy(o.id, bergdb_test_id, BERGDB_ID_SIZE);
    o.mem = &m;
    bergdb_test_clock_set(&clock, 1000);
    uint8_t *longKey = long_key("/d/", 200 * 1000);
    uint8_t *longer = long_key("/d/", 210 * 1000);
    uint8_t shortKey[8];
    size_t shortLen;
    k("/a", shortKey, &shortLen);
    REQUIRE(longKey != NULL && longer != NULL);
    REQUIRE(bergdb_open(dir, &o, &db, NULL, NULL) == BERGDB_OK);
    CHECK_EQ(put_one(db, longKey, 200 * 1000, "long"), BERGDB_OK);
    CHECK_EQ(put_one(db, shortKey, shortLen, "short"), BERGDB_OK);
    CHECK_EQ(bergdb_sync(db, 0, BERGDB_SYNC_ORDINARY), BERGDB_OK);
    CHECK_EQ(bergdb_debug_check(db), BERGDB_OK);
    CHECK_EQ(bergdb_close(db), BERGDB_OK);
    REQUIRE(bergdb_open(dir, &o, &db, NULL, NULL) == BERGDB_OK);
    CHECK(value_is(db, longKey, 200 * 1000, "long"));
    CHECK(value_is(db, shortKey, shortLen, "short"));
    CHECK(scan_is(db, true, shortKey, shortLen, longKey, 200 * 1000));
    CHECK(scan_is(db, false, longKey, 200 * 1000, shortKey, shortLen));
    CHECK_EQ(bergdb_debug_check(db), BERGDB_OK);
    CHECK_EQ(put_one(db, longer, 210 * 1000, "longer"), BERGDB_OK);
    CHECK(value_is(db, longer, 210 * 1000, "longer"));
    CHECK(value_is(db, longKey, 200 * 1000, "long"));
    CHECK_EQ(bergdb_close(db), BERGDB_OK);
    CHECK_EQ(m.live_total, 0);
    free(longKey);
    free(longer);

    uint8_t *first = long_key("/d/", 100 * 1000);
    uint8_t *second = long_key("/d/", 1000 * 1000);
    REQUIRE(first != NULL && second != NULL);
    o.startup_distance = 200 * 1000 * 1000;
    REQUIRE(bergdb_open(NULL, &o, &db, NULL, NULL) == BERGDB_OK);
    CHECK_EQ(put_one(db, first, 100 * 1000, "first"), BERGDB_OK);
    CHECK_EQ(put_one(db, second, 1000 * 1000, "second"), BERGDB_OK);
    CHECK(value_is(db, first, 100 * 1000, "first"));
    CHECK(value_is(db, second, 1000 * 1000, "second"));
    CHECK_EQ(put_one(db, k("/x", shortKey, &shortLen), shortLen, "x"), BERGDB_OK);
    CHECK(value_is(db, shortKey, shortLen, "x"));
    CHECK_EQ(bergdb_close(db), BERGDB_OK);
    CHECK_EQ(m.live_total, 0);
    free(first);
    free(second);
    remove_dir(dir);
}

/* The keys of a getMany are keys[idx[0]] to keys[idx[n - 1]], in that order. */
static bool many_is(const struct bergdb_many *many, const char *const *keys, const int *idx,
        int n) {
    if (many->count != (size_t) n) {
        return false;
    }
    for (int i = 0; i < n; i++) {
        size_t len = strlen(keys[idx[i]]);
        if (many->kvts[i].key_len != len
                || (len > 0 && memcmp(many->kvts[i].key, keys[idx[i]], len) != 0)) {
            return false;
        }
    }
    return true;
}

/* DbTesterGetMany.testPrefixHasThePrefixKey (bergdb 021-18) through the API:
 * bergdb_range's prefix (Prefix), with max_count (PrefixN's count), adds
 * the prefix's own key, as it starts with the prefix; a key equal to the
 * prefix stopped the read before, so that a range from the prefix,
 * inclusive, gave no pair when the prefix was a key, and a backward one left
 * it out. Keys around a segment of 7 bytes, and the empty key, in memory. */
TEST(api_prefix_has_the_prefix_key) {
    static const char *const keys[] = { "", "a", "ab", "abc", "abcdefg", "abcdefgh",
            "abcdefghi", "abd", "b" };
    static const char *const prefixes[] = { "", "a", "ab", "abc", "abcdefg", "abcdefgh",
            "abcdefghi", "abd", "b", "abcd", "abcdefgx", "c" };
    struct bergdb_mem m = {0};
    struct bergdb_test_clock clock = {0};
    struct bergdb_options o;
    options(&o, &clock, &m);
    bergdb_test_clock_set(&clock, 1000);
    bergdb_db *db;
    REQUIRE(bergdb_open(NULL, &o, &db, NULL, NULL) == BERGDB_OK);
    bergdb_trans *t;
    REQUIRE(bergdb_trans_new(db, &t) == BERGDB_OK);
    for (int i = 0; i < 9; i++) {
        CHECK_EQ(bergdb_trans_put(t, (const uint8_t *) keys[i], strlen(keys[i]),
                (const uint8_t *) "\1", 1), BERGDB_OK);
    }
    bergdb_test_clock_set(&clock, 1001);
    CHECK_EQ(bergdb_execute(db, t, NULL), BERGDB_OK);
    bergdb_trans_free(t);
    bergdb_read *rd;
    REQUIRE(bergdb_read_new(db, &rd) == BERGDB_OK);
    for (int pi = 0; pi < 12; pi++) {
        const char *p = prefixes[pi];
        size_t plen = strlen(p);
        int expected[9], reversed[9], ne = 0;
        for (int i = 0; i < 9; i++) {
            if (strncmp(keys[i], p, plen) == 0) {       /* startsWith */
                expected[ne++] = i;
            }
        }
        for (int i = 0; i < ne; i++) {
            reversed[i] = expected[ne - 1 - i];
        }
        int skip = ne > 0 && strcmp(keys[expected[0]], p) == 0 ? 1 : 0;
        struct bergdb_range r;
        struct bergdb_many many;
        bergdb_range_init(&r);
        r.prefix = (const uint8_t *) p;
        r.prefix_len = plen;
        r.start_key = r.prefix;
        r.start_key_len = plen;
        CHECK_EQ(bergdb_get_many(db, rd, &r, &many), BERGDB_OK);
        CHECK(many_is(&many, keys, expected, ne));
        r.max_count = 100;
        CHECK_EQ(bergdb_get_many(db, rd, &r, &many), BERGDB_OK);
        CHECK(many_is(&many, keys, expected, ne));
        r.max_count = 1;
        CHECK_EQ(bergdb_get_many(db, rd, &r, &many), BERGDB_OK);
        CHECK(many_is(&many, keys, expected, ne < 1 ? ne : 1));
        r.max_count = 0;
        r.inclusive = false;
        CHECK_EQ(bergdb_get_many(db, rd, &r, &many), BERGDB_OK);
        CHECK(many_is(&many, keys, expected + skip, ne - skip));
        if (ne > 0) {
            r.inclusive = true;
            r.forward = false;
            r.start_key = (const uint8_t *) keys[expected[ne - 1]];
            r.start_key_len = strlen(keys[expected[ne - 1]]);
            CHECK_EQ(bergdb_get_many(db, rd, &r, &many), BERGDB_OK);
            CHECK(many_is(&many, keys, reversed, ne));
            r.max_count = 100;
            CHECK_EQ(bergdb_get_many(db, rd, &r, &many), BERGDB_OK);
            CHECK(many_is(&many, keys, reversed, ne));
        }
    }
    bergdb_read_free(rd);
    CHECK_EQ(bergdb_close(db), BERGDB_OK);
    CHECK_EQ(m.live_total, 0);
}

/* DbTesterJavadoc.testKvTimeIsTheEntrysTime (bergdb 021-19) through the API:
 * a pair's time, bergdb_kvt.time and bergdb_one.time, is the time of its key
 * node's entry, not of its write. T1 puts 27 keys, and T2 a 28th, which
 * replaces their full key node (a space split, at the node size 30 of
 * Java's testSetup), so that T1's keys read T2's time; at or after the
 * write's time and at or before the lookup time; a read before T2 gives
 * T1's; the write's time is bergdb_get_trans of the tpos. It passes on the
 * code as it is, as Java's: if the time becomes the write's, the last check
 * fails, and bergdb.h's words are to change. */
TEST(api_kv_time_is_the_entrys_time) {
    struct bergdb_mem m = {0};
    struct bergdb_test_clock clock = {0};
    struct bergdb_options o;
    bergdb_options_init(&o);
    o.clock = bergdb_test_clock_time;
    o.clock_ctx = &clock;
    memcpy(o.id, bergdb_test_id, BERGDB_ID_SIZE);
    o.cache_size_indicator = BERGDB_NO_EVICT;
    o.mem = &m;
    bergdb_test_clock_set(&clock, 1000);
    bergdb_db *db;
    REQUIRE(bergdb_open(NULL, &o, &db, NULL, NULL) == BERGDB_OK);
    struct bergdb_executed x1, x2;
    bergdb_trans *t;
    REQUIRE(bergdb_trans_new(db, &t) == BERGDB_OK);
    for (int i = 0; i < 27; i++) {
        uint8_t key = (uint8_t) (2 * i);
        CHECK_EQ(bergdb_trans_put(t, &key, 1, (const uint8_t *) "\1", 1), BERGDB_OK);
    }
    bergdb_test_clock_set(&clock, 1010);
    CHECK_EQ(bergdb_execute(db, t, &x1), BERGDB_OK);
    bergdb_trans_free(t);
    REQUIRE(bergdb_trans_new(db, &t) == BERGDB_OK);
    const uint8_t key55 = 55;
    CHECK_EQ(bergdb_trans_put(t, &key55, 1, (const uint8_t *) "\2", 1), BERGDB_OK);
    bergdb_test_clock_set(&clock, 1020);
    CHECK_EQ(bergdb_execute(db, t, &x2), BERGDB_OK);
    bergdb_trans_free(t);

    bergdb_read *rd, *rd1;
    REQUIRE(bergdb_read_new(db, &rd) == BERGDB_OK);
    REQUIRE(bergdb_read_new(db, &rd1) == BERGDB_OK);
    struct bergdb_range r;
    struct bergdb_many many;
    bergdb_range_init(&r);
    CHECK_EQ(bergdb_get_many(db, rd, &r, &many), BERGDB_OK);
    CHECK_EQ((int64_t) many.count, 28);
    int later = 0;
    for (size_t i = 0; i < many.count; i++) {
        const struct bergdb_kvt *kvt = &many.kvts[i];
        bool ofT2 = kvt->key_len == 1 && kvt->key[0] == 55;
        int64_t written = ofT2 ? x2.tt : x1.tt;
        CHECK(kvt->time >= written);                            /* at or after the write's time */
        CHECK(kvt->time <= many.actual_lookup_time);            /* at or before the lookup time */
        struct bergdb_one one;
        CHECK_EQ(bergdb_get_one(db, rd1, many.actual_lookup_time, kvt->key, kvt->key_len,
                &one), BERGDB_OK);
        CHECK(one.value != NULL);
        CHECK_EQ(one.time, kvt->time);
        struct bergdb_stored st;
        CHECK_EQ(bergdb_get_trans(db, rd1, one.tpos, &st), BERGDB_OK);
        CHECK_EQ(st.tt, written);                               /* the write's time */
        if (!ofT2) {
            CHECK_EQ(bergdb_get_one(db, rd1, x2.tt - 1, kvt->key, kvt->key_len, &one),
                    BERGDB_OK);
            CHECK(one.value != NULL);
            CHECK_EQ(one.time, x1.tt);                          /* before T2 */
        }
        later += kvt->time != written ? 1 : 0;
    }
    CHECK_EQ(later, 27);                                        /* T1's keys with T2's time */
    bergdb_read_free(rd1);
    bergdb_read_free(rd);
    CHECK_EQ(bergdb_close(db), BERGDB_OK);
    CHECK_EQ(m.live_total, 0);
}

/* DbBuilder.testSetup() in memory: the test clock at 1000, the test id, no
 * eviction, the builder's other defaults. */
static bergdb_db *test_setup(struct bergdb_test_clock *clock, struct bergdb_mem *m) {
    struct bergdb_options o;
    bergdb_options_init(&o);
    o.clock = bergdb_test_clock_time;
    o.clock_ctx = clock;
    memcpy(o.id, bergdb_test_id, BERGDB_ID_SIZE);
    o.cache_size_indicator = BERGDB_NO_EVICT;
    o.mem = m;
    bergdb_test_clock_set(clock, 1000);
    bergdb_db *db;
    return bergdb_open(NULL, &o, &db, NULL, NULL) == BERGDB_OK ? db : NULL;
}

/* The bytes' order of getMany: unsigned, a shorter key before a longer one
 * with its start (Arrays.compareUnsigned). */
struct bytes_key {
    const uint8_t *b;
    size_t n;
};

static int compare_unsigned(const void *x, const void *y) {
    const struct bytes_key *a = x, *b = y;
    size_t n = a->n < b->n ? a->n : b->n;
    int c = n == 0 ? 0 : memcmp(a->b, b->b, n);
    return c != 0 ? c : a->n < b->n ? -1 : a->n > b->n ? 1 : 0;
}

/* DbTesterJavadoc.testKeysAndValues (bergdb 020-24-09, U9-5; Db's "Keys and
 * values", which bergdb.h's section E says): any bytes make a key, the
 * empty key too; getMany gives the keys in the unsigned order of their
 * bytes, forward and backward; a key of 3,000 bytes works; the empty value
 * is a value, not a delete; a put of a NULL value is refused (BERGDB_ARG,
 * Java's IllegalArgumentException). Passes on the code as it is, as
 * Java's. */
TEST(api_keys_and_values) {
    static uint8_t longKey[3000];
    static const struct { uint8_t b[8]; size_t n; } shortKeys[] = {
        { {0}, 0 }, { {0}, 1 }, { {0, 0}, 2 }, { {1}, 1 }, { {0x61}, 1 }, { {0x61, 0}, 2 },
        { {0x61, 0, 0}, 3 }, { {0x61, 1}, 2 }, { {0x61, 0x61}, 2 }, { {0x62}, 1 },
        { {0x7f}, 1 }, { {0x80}, 1 }, { {0xfe, 0}, 2 }, { {0xff}, 1 }, { {0xff, 0xff}, 2 },
        { {1, 2, 3, 4, 5, 6, 7}, 7 }, { {1, 2, 3, 4, 5, 6, 7, 8}, 8 },
        { {1, 2, 3, 4, 5, 6, 7, 0x90}, 8 },
    };
    enum { NK = 19 };
    struct bytes_key keys[NK], sorted[NK];
    for (int i = 0; i < NK - 1; i++) {
        keys[i].b = shortKeys[i].b;
        keys[i].n = shortKeys[i].n;
    }
    longKey[2999] = 5;
    keys[NK - 1].b = longKey;
    keys[NK - 1].n = sizeof longKey;
    struct bergdb_mem m = {0};
    struct bergdb_test_clock clock = {0};
    bergdb_db *db = test_setup(&clock, &m);
    REQUIRE(db != NULL);
    bergdb_trans *t;
    REQUIRE(bergdb_trans_new(db, &t) == BERGDB_OK);
    for (int i = 0; i < NK; i++) {
        uint8_t v = (uint8_t) i;
        CHECK_EQ(bergdb_trans_put(t, keys[i].b, keys[i].n, &v, i == 3 ? 0 : 1), BERGDB_OK);
    }
    bergdb_test_clock_set(&clock, 1010);
    CHECK_EQ(bergdb_execute(db, t, NULL), BERGDB_OK);
    CHECK_EQ(bergdb_trans_put(t, keys[1].b, 1, NULL, 0), BERGDB_ARG);  /* a NULL value */
    bergdb_trans_free(t);

    memcpy(sorted, keys, sizeof keys);
    qsort(sorted, NK, sizeof sorted[0], compare_unsigned);
    bergdb_read *rd;
    REQUIRE(bergdb_read_new(db, &rd) == BERGDB_OK);
    struct bergdb_range r;
    struct bergdb_many many;
    for (int forward = 1; forward >= 0; forward--) {
        bergdb_range_init(&r);
        r.forward = forward;
        CHECK_EQ(bergdb_get_many(db, rd, &r, &many), BERGDB_OK);
        CHECK_EQ((int64_t) many.count, NK);
        for (int i = 0; i < NK && i < (int) many.count; i++) {
            const struct bytes_key *e = &sorted[forward ? i : NK - 1 - i];
            CHECK(many.kvts[i].key_len == e->n
                    && (e->n == 0 || memcmp(many.kvts[i].key, e->b, e->n) == 0));
        }
    }
    struct bergdb_one one;
    CHECK_EQ(bergdb_get_one(db, rd, BERGDB_LATEST, keys[0].b, 0, &one), BERGDB_OK);
    CHECK(one.value != NULL && one.value_len == 1 && one.value[0] == 0);   /* the empty key */
    CHECK_EQ(bergdb_get_one(db, rd, BERGDB_LATEST, keys[3].b, 1, &one), BERGDB_OK);
    CHECK(one.value != NULL && one.value_len == 0);         /* the empty value is a value */
    CHECK_EQ(bergdb_get_one(db, rd, BERGDB_LATEST, longKey, sizeof longKey, &one), BERGDB_OK);
    CHECK(one.value != NULL && one.value_len == 1 && one.value[0] == NK - 1);
    bergdb_read_free(rd);
    CHECK_EQ(bergdb_close(db), BERGDB_OK);
    CHECK_EQ(m.live_total, 0);
}

/* The stop function of api_core_writes_bergdbs_keys: CONTINUE for BergDB's
 * keys, those that start with 01 25 ("/#"), else ADD. */
static int skip_bergdbs(void *ctx, const struct bergdb_kvt *kvt) {
    (void) ctx;
    return kvt->key_len >= 2 && kvt->key[0] == 1 && kvt->key[1] == 0x25 ? BERGDB_CONTINUE
            : BERGDB_ADD;
}

/* DbTesterJavadoc.testCoreWritesBergDbsKeys (bergdb 020-24-09, U9-4; Db's
 * "Keys and the layers above", which bergdb.h's section E says): the Core
 * writes BergDB's keys itself, with no Pub API: a new database has none;
 * bergdb_set_startup_distance puts a value of 200 kB at "/#i/-dummy",
 * bergdb_set_retain_duration reclaim's settings at
 * "/#i/dreclaim/-settings.txt"; a scan returns them, transaction_count
 * counts their transactions, and a stop function that returns CONTINUE for
 * the keys that start with 01 25 leaves the user's keys, those around 01 25
 * too. Passes on the code as it is, as Java's. */
TEST(api_core_writes_bergdbs_keys) {
    static const struct { uint8_t b[3]; size_t n; } mine[] = {
        { {0}, 1 }, { {1, 0x24}, 2 }, { {1, 0x24, 0xff}, 3 }, { {1, 0x26}, 2 }, { {0xff}, 1 },
    };
    static const uint8_t dummy[] = { 1, 0x25, 0x6b, 1, 0x2f, 0x66, 0x77, 0x6f, 0x6f, 0x7b };
    uint8_t settings[64];
    size_t settingsLen;
    k("/#i/dreclaim/-settings.txt", settings, &settingsLen);
    struct bergdb_mem m = {0};
    struct bergdb_test_clock clock = {0};
    bergdb_db *db = test_setup(&clock, &m);
    REQUIRE(db != NULL);
    bergdb_trans *t;
    REQUIRE(bergdb_trans_new(db, &t) == BERGDB_OK);
    for (int i = 0; i < 5; i++) {
        CHECK_EQ(bergdb_trans_put(t, mine[i].b, mine[i].n, (const uint8_t *) "\7", 1),
                BERGDB_OK);
    }
    bergdb_test_clock_set(&clock, 1010);
    CHECK_EQ(bergdb_execute(db, t, NULL), BERGDB_OK);
    bergdb_trans_free(t);
    bergdb_read *rd;
    REQUIRE(bergdb_read_new(db, &rd) == BERGDB_OK);
    struct bergdb_range r;
    struct bergdb_many many;
    bergdb_range_init(&r);
    CHECK_EQ(bergdb_get_many(db, rd, &r, &many), BERGDB_OK);
    CHECK_EQ((int64_t) many.count, 5);                          /* a new database */

    bergdb_test_clock_set(&clock, 1020);
    CHECK_EQ(bergdb_set_startup_distance(db, 500 * 1000), BERGDB_OK);
    bergdb_test_clock_set(&clock, 1030);
    CHECK_EQ(bergdb_set_retain_duration(db, 3600 * BERGDB_UNITS_PER_SEC), BERGDB_OK);
    struct bergdb_stats s;
    CHECK_EQ(bergdb_stats(db, &s), BERGDB_OK);
    CHECK_EQ(s.transaction_count, 3);
    CHECK_EQ(bergdb_get_many(db, rd, &r, &many), BERGDB_OK);
    int bergdbs = 0;
    for (size_t i = 0; i < many.count; i++) {
        const struct bergdb_kvt *kvt = &many.kvts[i];
        if (kvt->key_len >= 2 && kvt->key[0] == 1 && kvt->key[1] == 0x25) {
            if (bergdbs == 0) {
                CHECK(kvt->key_len == sizeof dummy && memcmp(kvt->key, dummy, sizeof dummy) == 0);
                CHECK_EQ((int64_t) kvt->value_len, 200 * 1000);  /* the dummy's value */
            } else if (bergdbs == 1) {
                CHECK(kvt->key_len == settingsLen
                        && memcmp(kvt->key, settings, settingsLen) == 0);
            }
            bergdbs++;
        }
    }
    CHECK_EQ(bergdbs, 2);                                       /* BergDB's keys */
    r.stop = skip_bergdbs;
    CHECK_EQ(bergdb_get_many(db, rd, &r, &many), BERGDB_OK);
    CHECK_EQ((int64_t) many.count, 5);                          /* the user's keys */
    for (int i = 0; i < 5 && i < (int) many.count; i++) {
        CHECK(many.kvts[i].key_len == mine[i].n
                && memcmp(many.kvts[i].key, mine[i].b, mine[i].n) == 0);
    }
    bergdb_read_free(rd);
    CHECK_EQ(bergdb_close(db), BERGDB_OK);
    CHECK_EQ(m.live_total, 0);
}

/* DbTesterJavadoc.testCountersAndListedDeletes (bergdb 020-24-09, U9-9 and
 * U9-10): transaction_count and kv_count count since the open, each
 * transaction's pairs, a delete of a key without a value too, and 0 after
 * an open; bergdb_get_trans lists a delete of a key with a value, not one
 * of a key that had none. The restart through a directory, where Java's
 * copies its MemoryStream. Passes on the code as it is, as Java's. */
TEST(api_counters_and_listed_deletes) {
    char dir[1024];
    temp_dir(dir, sizeof dir);
    REQUIRE(dir[0] != '\0');
    struct bergdb_mem m = {0};
    struct bergdb_test_clock clock = {0};
    struct bergdb_options o;
    options(&o, &clock, &m);
    bergdb_test_clock_set(&clock, 1000);
    bergdb_db *db;
    REQUIRE(bergdb_open(dir, &o, &db, NULL, NULL) == BERGDB_OK);
    uint8_t a[4], b[4], c[4], never[8];
    size_t al, bl, cl, nl;
    k("a", a, &al);
    k("b", b, &bl);
    k("c", c, &cl);
    k("never", never, &nl);
    bergdb_trans *t;
    REQUIRE(bergdb_trans_new(db, &t) == BERGDB_OK);
    CHECK_EQ(bergdb_trans_put(t, a, al, (const uint8_t *) "1", 1), BERGDB_OK);
    CHECK_EQ(bergdb_trans_put(t, b, bl, (const uint8_t *) "2", 1), BERGDB_OK);
    bergdb_test_clock_set(&clock, 1010);
    CHECK_EQ(bergdb_execute(db, t, NULL), BERGDB_OK);
    bergdb_trans_free(t);
    REQUIRE(bergdb_trans_new(db, &t) == BERGDB_OK);
    CHECK_EQ(bergdb_trans_delete(t, a, al), BERGDB_OK);
    CHECK_EQ(bergdb_trans_delete(t, never, nl), BERGDB_OK);
    CHECK_EQ(bergdb_trans_put(t, c, cl, (const uint8_t *) "3", 1), BERGDB_OK);
    struct bergdb_executed x;
    bergdb_test_clock_set(&clock, 1020);
    CHECK_EQ(bergdb_execute(db, t, &x), BERGDB_OK);
    bergdb_trans_free(t);
    struct bergdb_stats s;
    CHECK_EQ(bergdb_stats(db, &s), BERGDB_OK);
    CHECK_EQ(s.transaction_count, 2);
    CHECK_EQ(s.kv_count, 5);
    bergdb_read *rd;
    REQUIRE(bergdb_read_new(db, &rd) == BERGDB_OK);
    struct bergdb_stored st;
    CHECK_EQ(bergdb_get_trans(db, rd, x.tpos, &st), BERGDB_OK);
    CHECK_EQ((int64_t) st.count, 2);                            /* listed: a and c */
    if (st.count == 2) {
        CHECK(st.values[0].key_len == al && memcmp(st.values[0].key, a, al) == 0);
        CHECK(st.values[0].value == NULL);                      /* the delete of a */
        CHECK(st.values[1].key_len == cl && memcmp(st.values[1].key, c, cl) == 0);
    }
    bergdb_read_free(rd);
    CHECK_EQ(bergdb_close(db), BERGDB_OK);
    REQUIRE(bergdb_open(dir, &o, &db, NULL, NULL) == BERGDB_OK);
    CHECK_EQ(bergdb_stats(db, &s), BERGDB_OK);
    CHECK_EQ(s.transaction_count, 0);                           /* after a start */
    CHECK_EQ(s.kv_count, 0);
    CHECK(value_is(db, c, cl, "3"));
    CHECK_EQ(bergdb_close(db), BERGDB_OK);
    CHECK_EQ(m.live_total, 0);
    remove_dir(dir);
}

/* DbTesterJavadoc.testOptimisticTransactions (bergdb 020-24-09, U9-7): a
 * transaction whose key read, with a value or without, a later transaction
 * wrote after its read time is refused with BERGDB_RERUN, nothing changed,
 * and runs at a new read time; the default read time checks nothing. Its
 * virtual write hash has no counterpart: C's API has no addReadHash or
 * addVirtualWriteHash. Passes on the code as it is, as Java's. */
TEST(api_optimistic_transactions) {
    struct bergdb_mem m = {0};
    struct bergdb_test_clock clock = {0};
    bergdb_db *db = test_setup(&clock, &m);
    REQUIRE(db != NULL);
    const uint8_t key[] = { 9 }, other[] = { 8 }, absent[] = { 7 };
    int64_t t1, t2, t3;
    bergdb_trans *t;
    CHECK_EQ(bergdb_current_time(db, &t1), BERGDB_OK);
    bergdb_test_clock_set(&clock, 1010);
    CHECK_EQ(put_one(db, key, 1, "\1"), BERGDB_OK);
    REQUIRE(bergdb_trans_new(db, &t) == BERGDB_OK);
    CHECK_EQ(bergdb_trans_lookup_time(t, t1), BERGDB_OK);
    CHECK_EQ(bergdb_trans_key_read(t, key, 1), BERGDB_OK);
    CHECK_EQ(bergdb_trans_put(t, other, 1, (const uint8_t *) "\2", 1), BERGDB_OK);
    bergdb_test_clock_set(&clock, 1020);
    CHECK_EQ(bergdb_execute(db, t, NULL), BERGDB_RERUN);       /* the key read, written after t1 */
    bergdb_trans_free(t);
    bergdb_read *rd;
    REQUIRE(bergdb_read_new(db, &rd) == BERGDB_OK);
    struct bergdb_one one;
    CHECK_EQ(bergdb_get_one(db, rd, BERGDB_LATEST, other, 1, &one), BERGDB_OK);
    CHECK(one.value == NULL);                                   /* nothing changed */
    CHECK_EQ(bergdb_current_time(db, &t2), BERGDB_OK);
    REQUIRE(bergdb_trans_new(db, &t) == BERGDB_OK);
    CHECK_EQ(bergdb_trans_lookup_time(t, t2), BERGDB_OK);
    CHECK_EQ(bergdb_trans_key_read(t, key, 1), BERGDB_OK);
    CHECK_EQ(bergdb_trans_put(t, other, 1, (const uint8_t *) "\2", 1), BERGDB_OK);
    bergdb_test_clock_set(&clock, 1030);
    CHECK_EQ(bergdb_execute(db, t, NULL), BERGDB_OK);          /* ran */
    bergdb_trans_free(t);
    CHECK(value_is(db, other, 1, "\2"));

    CHECK_EQ(bergdb_current_time(db, &t3), BERGDB_OK);
    bergdb_test_clock_set(&clock, 1040);
    CHECK_EQ(put_one(db, absent, 1, "\3"), BERGDB_OK);
    REQUIRE(bergdb_trans_new(db, &t) == BERGDB_OK);
    CHECK_EQ(bergdb_trans_lookup_time(t, t3), BERGDB_OK);
    CHECK_EQ(bergdb_trans_key_read(t, absent, 1), BERGDB_OK);
    CHECK_EQ(bergdb_trans_put(t, other, 1, (const uint8_t *) "\4", 1), BERGDB_OK);
    bergdb_test_clock_set(&clock, 1050);
    CHECK_EQ(bergdb_execute(db, t, NULL), BERGDB_RERUN);       /* read without a value, then put */
    bergdb_trans_free(t);
    REQUIRE(bergdb_trans_new(db, &t) == BERGDB_OK);
    CHECK_EQ(bergdb_trans_key_read(t, absent, 1), BERGDB_OK);  /* the default read time */
    CHECK_EQ(bergdb_trans_put(t, other, 1, (const uint8_t *) "\5", 1), BERGDB_OK);
    bergdb_test_clock_set(&clock, 1060);
    CHECK_EQ(bergdb_execute(db, t, NULL), BERGDB_OK);
    bergdb_trans_free(t);
    CHECK(value_is(db, other, 1, "\5"));                        /* the last that ran */
    bergdb_read_free(rd);
    CHECK_EQ(bergdb_close(db), BERGDB_OK);
    CHECK_EQ(m.live_total, 0);
}

static const struct test api_tests[] = {
    TEST_ENTRY(api_stm_after_restart),
    TEST_ENTRY(api_create_and_read),
    TEST_ENTRY(api_refusals),
    TEST_ENTRY(api_transformations),
    TEST_ENTRY(api_alloc_failures),
    TEST_ENTRY(api_read_nomem),
    TEST_ENTRY(api_any_bkey),
    TEST_ENTRY(api_long_keys),
    TEST_ENTRY(api_prefix_has_the_prefix_key),
    TEST_ENTRY(api_kv_time_is_the_entrys_time),
    TEST_ENTRY(api_keys_and_values),
    TEST_ENTRY(api_core_writes_bergdbs_keys),
    TEST_ENTRY(api_counters_and_listed_deletes),
    TEST_ENTRY(api_optimistic_transactions),
    TEST_END
};

extern const struct test start_tests[];     /* f_start.c (012-10) */
extern const struct test reclaim_func_tests[];      /* f_reclaim.c (012-11) */
extern const struct test budget_tests[];    /* f_budget.c (012-12) */
extern const struct test settings_tests[];  /* f_settings.c (012-13) */
extern const struct test durable_tests[];   /* f_durable.c (012-13) */
int durable_child(int argc, char **argv);   /* f_durable.c: func --child ... */
const char *func_program;                   /* argv[0], for f_durable.c's children */

int main(int argc, char **argv) {
    func_program = argv[0];
    if (argc >= 2 && strcmp(argv[1], "--child") == 0) {
        return durable_child(argc, argv);
    }
    const struct test *const tables[] = { api_tests, start_tests, reclaim_func_tests,
            budget_tests, settings_tests, durable_tests, NULL };
    return test_main(argc, argv, "FUNC", tables);
}
