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
    CHECK_EQ(info.startup_distance, -1);

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
    CHECK(bergdb_sync(db, 0, BERGDB_SYNC_STRONG) == BERGDB_OK);
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
                CHECK(bergdb_sync(db, 0, BERGDB_SYNC_STRONG) == BERGDB_OK);
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

static const struct test api_tests[] = {
    TEST_ENTRY(api_create_and_read),
    TEST_ENTRY(api_refusals),
    TEST_ENTRY(api_transformations),
    TEST_ENTRY(api_alloc_failures),
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
