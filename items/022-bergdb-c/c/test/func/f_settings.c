/* Functional tests of the API's settings, status, errors, keys, clocks, sync,
 * debug calls and close (bergdb 012-13), through include/bergdb.h only. The
 * status against Java's: settings_and_status_as_java runs the sequence of
 * test/func/java/StatsProbe.java and compares Db's getters, line by line,
 * with what that program printed on Java's Db. Each test ends with the
 * allocator's count 0. */
#include <math.h>
#include <stdlib.h>
#include <sys/stat.h>
#include <unistd.h>
#include "test.h"
#include "bergdb.h"

static void se_temp_dir(char *out, size_t cap) {
    const char *t = getenv("TMPDIR");
    snprintf(out, cap, "%s/bergdb-func-XXXXXX", t != NULL ? t : "/tmp");
    if (mkdtemp(out) == NULL) {
        out[0] = '\0';
    }
}

static void se_remove_dir(const char *dir) {
    char cmd[1200];
    snprintf(cmd, sizeof cmd, "rm -rf '%s'", dir);
    if (system(cmd) != 0) {
        printf("could not remove %s\n", dir);
    }
}

static const uint8_t *se_key(const char *ikey, uint8_t *buf, size_t *len) {
    *len = strlen(ikey);
    bergdb_ikey_to_bkey((const uint8_t *) ikey, *len, buf);
    return buf;
}

/* ======== The status as Java's ======== */

/* Java's Double.toString for the values used here: the shortest decimal
 * that reads back to d, with ".0" for an integer. */
static void java_double(double d, char *out, size_t cap) {
    if (isnan(d)) {
        snprintf(out, cap, "NaN");
        return;
    }
    for (int p = 1; p <= 17; p++) {
        snprintf(out, cap, "%.*g", p, d);
        if (strtod(out, NULL) == d) {
            break;
        }
    }
    if (strpbrk(out, ".e") == NULL) {
        strncat(out, ".0", cap - strlen(out) - 1);
    }
}

/* StatsProbe.print: Db's getters as one line, appended to text. */
static void stats_line(bergdb_db *db, const char *at, bool durable, char *text, size_t cap) {
    struct bergdb_stats s;
    char line[600], d[40], f[40];
    if (bergdb_stats(db, &s) != BERGDB_OK) {
        strncat(text, "stats failed\n", cap - strlen(text) - 1);
        return;
    }
    d[0] = '\0';
    if (durable) {
        snprintf(d, sizeof d, " durable=%lld", (long long) s.durable_length);
    }
    java_double(s.internal_fraction, f, sizeof f);
    snprintf(line, sizeof line, "at=%s length=%lld%s lastMeta=%lld firstTime=%lld firstPos=%lld "
            "sd=%d cache=%lld retain=%lld fraction=%s iterations=%lld trans=%lld kvs=%lld "
            "gets=%lld\n", at, (long long) s.stream_length, d,
            (long long) s.last_trans_pos_of_last_valid_meta_block,
            (long long) s.first_available_lookup_time, (long long) s.first_available_pos,
            (int) s.startup_distance, (long long) s.cache_size_indicator,
            (long long) s.retain_duration, f, (long long) s.reclaim_iteration_count,
            (long long) s.transaction_count, (long long) s.kv_count, (long long) s.get_op_count);
    strncat(text, line, cap - strlen(text) - 1);
}

/* StatsProbe's lines on Java's Db (release 2026.3, bergdb 022-01, step 1:
 * the retain duration set after the creation and kept in the stream, the
 * settings' records, a get more at each start as initFromDb reads the
 * settings, 015-87; the fraction 0.1 is kept as 6,554 units of 2^-16,
 * 005-79). */
static const char java_stats[] =
    "at=open length=264 durable=0 lastMeta=-1 firstTime=0 firstPos=0 sd=1000 cache=9223372036854775807 retain=9223372036854775807 fraction=0.25 iterations=0 trans=0 kvs=0 gets=2\n"
    "at=setretain length=480 lastMeta=-1 firstTime=0 firstPos=0 sd=1000 cache=9223372036854775807 retain=10000000 fraction=0.25 iterations=0 trans=1 kvs=1 gets=3\n"
    "at=t50 length=58376 lastMeta=-1 firstTime=0 firstPos=0 sd=1000 cache=9223372036854775807 retain=10000000 fraction=0.25 iterations=1 trans=57 kvs=118 gets=175\n"
    "at=setsd length=272816 lastMeta=68592 firstTime=45000001 firstPos=2024 sd=400000 cache=9223372036854775807 retain=10000000 fraction=0.25 iterations=2 trans=71 kvs=144 gets=307\n"
    "at=setsd-same length=272816 lastMeta=68592 firstTime=45000001 firstPos=2024 sd=400000 cache=9223372036854775807 retain=10000000 fraction=0.25 iterations=2 trans=71 kvs=144 gets=307\n"
    "at=setters length=276440 lastMeta=68592 firstTime=45000001 firstPos=2024 sd=400000 cache=150000000 retain=20000000 fraction=0.100006103515625 iterations=2 trans=83 kvs=168 gets=338\n"
    "at=sync length=286416 durable=286416 lastMeta=68592 firstTime=45000001 firstPos=2024 sd=400000 cache=150000000 retain=20000000 fraction=0.100006103515625 iterations=2 trans=113 kvs=232 gets=423\n"
    "at=end length=303576 lastMeta=68592 firstTime=45000001 firstPos=2024 sd=400000 cache=150000000 retain=20000000 fraction=0.100006103515625 iterations=2 trans=162 kvs=338 gets=557\n"
    "at=reopen length=303576 durable=303576 lastMeta=68592 firstTime=45000001 firstPos=2024 sd=400000 cache=9223372036854775807 retain=20000000 fraction=0.100006103515625 iterations=0 trans=0 kvs=0 gets=3\n"
    "at=reopen-sync length=303784 durable=303784 lastMeta=68592 firstTime=45000001 firstPos=2024 sd=400000 cache=9223372036854775807 retain=20000000 fraction=0.100006103515625 iterations=0 trans=2 kvs=2 gets=5\n";

static void probe_options(struct bergdb_options *o, struct bergdb_test_clock *clock,
        struct bergdb_mem *m) {
    bergdb_options_init(o);
    o->clock = bergdb_test_clock_time;
    o->clock_ctx = clock;
    memcpy(o->id, bergdb_test_id, BERGDB_ID_SIZE);
    o->cache_size_indicator = BERGDB_NO_EVICT;      /* testSetupExceptStream */
    o->max_node_size = 8;
    o->startup_distance = 1000;
    o->mem = m;
}

static void probe_value(int i, int n, uint8_t *v) {
    for (int j = 0; j < n; j++) {
        v[j] = (uint8_t) (i * 31 + j);
    }
}

/* One of StatsProbe's transactions; false on an error. */
static bool probe_trans(bergdb_db *db, int i, bool restarted) {
    bergdb_trans *t;
    char ikey[32], x[32];
    uint8_t b[32], v[400];
    size_t kl;
    bool ok = bergdb_trans_new(db, &t) == BERGDB_OK;
    if (restarted) {
        snprintf(ikey, sizeof ikey, "/k/%d", i);
        probe_value(i, 10, v);
        ok = ok && bergdb_trans_put(t, se_key(ikey, b, &kl), kl, v, 10) == BERGDB_OK;
    } else {
        snprintf(ikey, sizeof ikey, "/k/%d", i * 7 % 50);
        probe_value(i, 100 + (i % 7) * 30, v);
        ok = ok && bergdb_trans_put(t, se_key(ikey, b, &kl), kl, v,
                (size_t) (100 + (i % 7) * 30)) == BERGDB_OK;
        snprintf(ikey, sizeof ikey, "/k/%d", (i * 7 + 1) % 50);
        snprintf(x, sizeof x, "x%d", i);
        ok = ok && bergdb_trans_put(t, se_key(ikey, b, &kl), kl, (const uint8_t *) x,
                strlen(x)) == BERGDB_OK;
        if (i % 5 == 0) {
            snprintf(ikey, sizeof ikey, "/k/%d", i * 3 % 50);
            ok = ok && bergdb_trans_delete(t, se_key(ikey, b, &kl), kl) == BERGDB_OK;
        }
    }
    ok = ok && bergdb_execute(db, t, NULL) == BERGDB_OK;
    bergdb_trans_free(t);
    return ok;
}

/* StatsProbe.main through bergdb.h: Db's getters at the same points equal
 * Java's (012-13, done item 2): the stream length, the durable length after
 * a sync and a start, the last valid meta block's transaction, the first
 * available time and position, reclaim's iterations, the counts, the
 * startup distance with Java's clamp and dummy transaction, the cache size
 * indicator, the retain duration and the internal fraction. */
TEST(settings_and_status_as_java) {
    char dir[1024];
    se_temp_dir(dir, sizeof dir);
    REQUIRE(dir[0] != '\0');
    struct bergdb_mem m = {0};
    struct bergdb_test_clock clock = {0};
    struct bergdb_options o;
    bergdb_db *db;
    static char text[8000];
    text[0] = '\0';
    probe_options(&o, &clock, &m);
    bergdb_test_clock_set(&clock, 1000);
    REQUIRE(bergdb_open(dir, &o, &db, NULL, NULL) == BERGDB_OK);
    stats_line(db, "open", true, text, sizeof text);
    /* The retain duration once, after the creation: the stream keeps it
     * (015-87; 022-01, D3). */
    CHECK(bergdb_set_retain_duration(db, 10000000) == BERGDB_OK);
    stats_line(db, "setretain", false, text, sizeof text);
    bergdb_read *rd;
    REQUIRE(bergdb_read_new(db, &rd) == BERGDB_OK);
    for (int i = 0; i < 150; i++) {
        bergdb_test_clock_set(&clock, 2000000 + (int64_t) i * 1000000);
        CHECK(probe_trans(db, i, false));
        if (i % 10 == 0) {
            struct bergdb_one one;
            struct bergdb_range r;
            struct bergdb_many many;
            char ikey[32];
            uint8_t b[32];
            size_t kl;
            snprintf(ikey, sizeof ikey, "/k/%d", i % 50);
            CHECK(bergdb_get_one(db, rd, BERGDB_LATEST, se_key(ikey, b, &kl), kl, &one)
                    == BERGDB_OK);
            snprintf(ikey, sizeof ikey, "/k/%d", (i + 1) % 50);
            int rc = bergdb_get_one(db, rd, 2000000 + (int64_t) (i - 1) * 1000000,
                    se_key(ikey, b, &kl), kl, &one);
            CHECK(rc == BERGDB_OK);     /* Java's run printed no "unavailable" */
            bergdb_range_init(&r);
            r.max_count = 5;
            CHECK(bergdb_get_many(db, rd, &r, &many) == BERGDB_OK);
        }
        if (i == 50) {
            stats_line(db, "t50", false, text, sizeof text);
        }
        if (i == 60) {
            CHECK(bergdb_set_startup_distance(db, 10) == BERGDB_OK);
            stats_line(db, "setsd", false, text, sizeof text);
            CHECK(bergdb_set_startup_distance(db, 400000) == BERGDB_OK);
            stats_line(db, "setsd-same", false, text, sizeof text);
        }
        if (i == 70) {
            CHECK(bergdb_set_retain_duration(db, 20000000) == BERGDB_OK);
            CHECK(bergdb_set_reclaim_internal_fraction(db, 0.1) == BERGDB_OK);
            CHECK(bergdb_set_cache_size_indicator(db, 150000000) == BERGDB_OK);
            stats_line(db, "setters", false, text, sizeof text);
        }
        if (i == 100) {
            CHECK(bergdb_sync(db, 0, BERGDB_SYNC_ORDINARY) == BERGDB_OK);
            stats_line(db, "sync", true, text, sizeof text);
        }
    }
    stats_line(db, "end", false, text, sizeof text);
    bergdb_read_free(rd);
    CHECK(bergdb_close(db) == BERGDB_OK);
    CHECK_EQ(m.live_total, 0);
    REQUIRE(bergdb_open(dir, &o, &db, NULL, NULL) == BERGDB_OK);
    stats_line(db, "reopen", true, text, sizeof text);
    for (int i = 150; i < 152; i++) {
        bergdb_test_clock_set(&clock, 2000000 + (int64_t) i * 1000000);
        CHECK(probe_trans(db, i, true));
    }
    CHECK(bergdb_sync(db, 0, BERGDB_SYNC_ORDINARY) == BERGDB_OK);
    stats_line(db, "reopen-sync", true, text, sizeof text);
    CHECK(bergdb_close(db) == BERGDB_OK);
    CHECK_EQ(m.live_total, 0);

    const char *out = getenv("BERGDB_STATS_OUT");
    if (out != NULL) {
        FILE *f = fopen(out, "w");
        if (f != NULL) {
            fputs(text, f);
            fclose(f);
        }
    }
    if (strcmp(text, java_stats) != 0) {
        printf("C's lines:\n%sJava's:\n%s", text, java_stats);
    }
    CHECK(strcmp(text, java_stats) == 0);
    if (out != NULL) {
        printf("  settings_and_status_as_java: the lines in %s, the database kept in %s\n", out,
                dir);
    } else {
        se_remove_dir(dir);
    }
}

/* ======== The setters ======== */

static void small_options(struct bergdb_options *o, struct bergdb_test_clock *clock,
        struct bergdb_mem *m) {
    bergdb_options_init(o);
    o->clock = bergdb_test_clock_time;
    o->clock_ctx = clock;
    memcpy(o->id, bergdb_test_id, BERGDB_ID_SIZE);
    o->max_node_size = 8;
    o->startup_distance = 1000;
    o->mem = m;
}

static int put1(bergdb_db *db, struct bergdb_test_clock *clock, int64_t tt, const char *ikey,
        const char *value) {
    bergdb_trans *t;
    uint8_t b[64];
    size_t kl;
    if (tt > clock->time) {
        bergdb_test_clock_set(clock, tt);
    }
    int rc = bergdb_trans_new(db, &t);
    if (rc == BERGDB_OK) {
        rc = bergdb_trans_put(t, se_key(ikey, b, &kl), kl, (const uint8_t *) value,
                strlen(value));
    }
    if (rc == BERGDB_OK) {
        rc = bergdb_execute(db, t, NULL);
    }
    bergdb_trans_free(t);
    return rc;
}

/* The four setters' checks, as Java's: a refusal changes nothing. */
TEST(settings_setters) {
    struct bergdb_mem m = {0};
    struct bergdb_test_clock clock = {0};
    struct bergdb_options o;
    struct bergdb_stats s0, s;
    bergdb_db *db;
    small_options(&o, &clock, &m);
    bergdb_test_clock_set(&clock, 1000);
    REQUIRE(bergdb_open(NULL, &o, &db, NULL, NULL) == BERGDB_OK);
    CHECK(put1(db, &clock, 2000, "/a", "1") == BERGDB_OK);

    /* setStartupDistance: negative refused; clamped to 400,000 to
     * 1,000,000,000; a dummy transaction of 200,000 bytes unless the value
     * is in force (005-53). */
    REQUIRE(bergdb_stats(db, &s0) == BERGDB_OK);
    CHECK_EQ(s0.startup_distance, 1000);
    CHECK(bergdb_set_startup_distance(db, -1) == BERGDB_ARG);
    CHECK(strncmp(bergdb_errmsg(db), "IllegalArgumentException: ", 26) == 0);
    CHECK(bergdb_set_startup_distance(db, 2000000000) == BERGDB_OK);
    REQUIRE(bergdb_stats(db, &s) == BERGDB_OK);
    CHECK_EQ(s.startup_distance, 1000000000);
    CHECK(s.stream_length >= s0.stream_length + 200000);
    CHECK_EQ(s.transaction_count, s0.transaction_count + 1);
    s0 = s;
    CHECK(bergdb_set_startup_distance(db, 1000000000) == BERGDB_OK);    /* in force */
    REQUIRE(bergdb_stats(db, &s) == BERGDB_OK);
    CHECK_EQ(s.stream_length, s0.stream_length);
    CHECK_EQ(s.transaction_count, s0.transaction_count);
    CHECK(bergdb_set_startup_distance(db, 0) == BERGDB_OK);
    REQUIRE(bergdb_stats(db, &s) == BERGDB_OK);
    CHECK_EQ(s.startup_distance, 400000);
    /* Refused by the clock (005-18): the setting stays as it was. */
    bergdb_test_clock_set(&clock, BERGDB_MAX_TIME + 1);
    s0 = s;
    CHECK(bergdb_set_startup_distance(db, 500000) == BERGDB_LIMIT);
    REQUIRE(bergdb_stats(db, &s) == BERGDB_OK);
    CHECK_EQ(s.startup_distance, 400000);
    CHECK_EQ(s.stream_length, s0.stream_length);
    /* So are the setters of reclaim's settings, which commit (015-87;
     * DbTesterRestart.testReclaimSettingRefusedAtGoPoint): nothing written,
     * the values in force stay, and the database goes on. */
    CHECK(bergdb_set_retain_duration(db, 5 * BERGDB_UNITS_PER_SEC) == BERGDB_LIMIT);
    CHECK(strstr(bergdb_errmsg(db), "outside the range") != NULL);
    CHECK(bergdb_set_reclaim_internal_fraction(db, 0.5) == BERGDB_LIMIT);
    CHECK(strstr(bergdb_errmsg(db), "outside the range") != NULL);
    REQUIRE(bergdb_stats(db, &s) == BERGDB_OK);
    CHECK_EQ(s.retain_duration, BERGDB_FOREVER);
    CHECK(s.internal_fraction == 0.25);
    CHECK_EQ(s.stream_length, s0.stream_length);
    clock.time = 3000;      /* back in range: a caller's clock may give anything */

    /* setCacheSizeIndicator: at least 1; for the run, no byte (the
     * eviction it starts is 012-12's, and not tested here). */
    CHECK(bergdb_set_cache_size_indicator(db, 0) == BERGDB_ARG);
    CHECK(bergdb_set_cache_size_indicator(db, -5) == BERGDB_ARG);
    CHECK(bergdb_set_cache_size_indicator(db, 300000000) == BERGDB_OK);
    REQUIRE(bergdb_stats(db, &s) == BERGDB_OK);
    CHECK_EQ(s.cache_size_indicator, 300000000);
    CHECK_EQ(s.stream_length, s0.stream_length);

    /* setRetainDuration: at least a second, or forever; kept in the stream
     * (015-87): a record of reclaim's settings when the value changes, none
     * when it is in force. */
    CHECK(bergdb_set_retain_duration(db, BERGDB_UNITS_PER_SEC - 1) == BERGDB_ARG);
    CHECK(strcmp(bergdb_errmsg(db), "IllegalArgumentException: retainDuration = 9999999 is "
            "too small, must be at least one second (10000000 time units).") == 0);
    REQUIRE(bergdb_stats(db, &s0) == BERGDB_OK);
    CHECK(bergdb_set_retain_duration(db, BERGDB_FOREVER) == BERGDB_OK);     /* in force */
    REQUIRE(bergdb_stats(db, &s) == BERGDB_OK);
    CHECK_EQ(s.stream_length, s0.stream_length);
    CHECK(bergdb_set_retain_duration(db, BERGDB_UNITS_PER_SEC) == BERGDB_OK);
    REQUIRE(bergdb_stats(db, &s) == BERGDB_OK);
    CHECK_EQ(s.retain_duration, BERGDB_UNITS_PER_SEC);
    CHECK(s.stream_length > s0.stream_length);
    CHECK_EQ(s.transaction_count, s0.transaction_count + 1);
    CHECK(bergdb_set_retain_duration(db, BERGDB_FOREVER) == BERGDB_OK);
    REQUIRE(bergdb_stats(db, &s) == BERGDB_OK);
    CHECK_EQ(s.retain_duration, BERGDB_FOREVER);
    CHECK_EQ(s.transaction_count, s0.transaction_count + 2);

    /* setReclaimInternalFraction: 0.001 to 0.90; NaN refused, and the
     * setting stays (bergdb 005-73, F4, as Java's since release 2026.2;
     * before, NaN passed, 012-03, 6.8). Kept as the nearest multiple of
     * 2^-16, which the getter gives (005-79): 0.5 exactly, 0.1 as 6,554 / 2^16,
     * the range's ends as 66 and 58,982 units. */
    CHECK(bergdb_set_reclaim_internal_fraction(db, 0.0009) == BERGDB_ARG);
    CHECK(bergdb_set_reclaim_internal_fraction(db, 0.91) == BERGDB_ARG);
    CHECK(bergdb_set_reclaim_internal_fraction(db, 0.5) == BERGDB_OK);
    REQUIRE(bergdb_stats(db, &s) == BERGDB_OK);
    CHECK(s.internal_fraction == 0.5);
    CHECK(bergdb_set_reclaim_internal_fraction(db, NAN) == BERGDB_ARG);
    REQUIRE(bergdb_stats(db, &s) == BERGDB_OK);
    CHECK(s.internal_fraction == 0.5);
    CHECK(bergdb_set_reclaim_internal_fraction(db, 0.1) == BERGDB_OK);
    REQUIRE(bergdb_stats(db, &s) == BERGDB_OK);
    CHECK(s.internal_fraction == 6554 / 65536.0);
    CHECK(bergdb_set_reclaim_internal_fraction(db, 0.001) == BERGDB_OK);
    REQUIRE(bergdb_stats(db, &s) == BERGDB_OK);
    CHECK(s.internal_fraction == 66 / 65536.0);
    CHECK(bergdb_set_reclaim_internal_fraction(db, 0.90) == BERGDB_OK);
    REQUIRE(bergdb_stats(db, &s) == BERGDB_OK);
    CHECK(s.internal_fraction == 58982 / 65536.0);
    CHECK(bergdb_set_reclaim_internal_fraction(db, 0.25) == BERGDB_OK);

    /* A NULL database. */
    CHECK(bergdb_set_startup_distance(NULL, 500000) == BERGDB_ARG);
    CHECK(bergdb_set_cache_size_indicator(NULL, 1) == BERGDB_ARG);
    CHECK(bergdb_set_retain_duration(NULL, BERGDB_FOREVER) == BERGDB_ARG);
    CHECK(bergdb_set_reclaim_internal_fraction(NULL, 0.25) == BERGDB_ARG);
    CHECK(bergdb_stats(NULL, &s) == BERGDB_ARG);
    CHECK(bergdb_stats(db, NULL) == BERGDB_ARG);

    /* On a failed database (P7): setStartupDistance, setRetainDuration and
     * setReclaimInternalFraction are refused as a transaction (FAILED;
     * the last two since 015-87); the cache size indicator sets its value
     * (bergdb.h, B). */
    bergdb_read *rd;
    struct bergdb_stored st;
    REQUIRE(bergdb_read_new(db, &rd) == BERGDB_OK);
    CHECK(bergdb_get_trans(db, rd, 264 + 8, &st) == BERGDB_FAILED);    /* corrupt: fails */
    bergdb_read_free(rd);
    CHECK(bergdb_set_startup_distance(db, 600000) == BERGDB_FAILED);
    CHECK(bergdb_set_cache_size_indicator(db, 123456789) == BERGDB_OK);
    CHECK(bergdb_set_retain_duration(db, 5 * BERGDB_UNITS_PER_SEC) == BERGDB_FAILED);
    CHECK(strncmp(bergdb_errmsg(db), "DbFailedException: Cannot call setRetainDuration()", 50)
            == 0);
    CHECK(bergdb_set_reclaim_internal_fraction(db, 0.2) == BERGDB_FAILED);
    CHECK(bergdb_set_retain_duration(db, 0) == BERGDB_ARG);    /* the argument first */
    REQUIRE(bergdb_stats(db, &s) == BERGDB_OK);
    CHECK_EQ(s.startup_distance, 400000);
    CHECK_EQ(s.cache_size_indicator, 123456789);
    CHECK_EQ(s.retain_duration, BERGDB_FOREVER);
    CHECK(s.internal_fraction == 0.25);
    CHECK(bergdb_close(db) == BERGDB_OK);
    CHECK_EQ(m.live_total, 0);
}

/* ======== The open's checks, errors, keys, the test clock ======== */

TEST(settings_open_checks) {
    char dir[1024], errbuf[BERGDB_ERRBUF_SIZE];
    se_temp_dir(dir, sizeof dir);
    REQUIRE(dir[0] != '\0');
    struct bergdb_mem m = {0};
    struct bergdb_test_clock clock = {0};
    struct bergdb_options o;
    bergdb_db *db = (bergdb_db *) &o;      /* not NULL: the open sets it */
    small_options(&o, &clock, &m);
    bergdb_test_clock_set(&clock, 1000);

    CHECK(bergdb_open(dir, &o, NULL, NULL, errbuf) == BERGDB_ARG);
    o.max_node_size = 16;
    CHECK(bergdb_open(dir, &o, &db, NULL, errbuf) == BERGDB_ARG);
    CHECK(db == NULL);
    CHECK(strncmp(errbuf, "IllegalArgumentException: ", 26) == 0);
    o.max_node_size = 8;
    o.startup_distance = 9;
    CHECK(bergdb_open(dir, &o, &db, NULL, errbuf) == BERGDB_ARG);
    o.startup_distance = 10;
    CHECK_EQ(m.live_total, 0);

    /* DbTesterJavadoc.testBuilderCacheSizeIndicatorBelowOneRefused (bergdb
     * 020-27, C3), in memory: a cache size indicator below 1 refused with
     * DbBuilder.cacheSizeIndicator's IllegalArgumentException and text (it
     * was Cache3's AssertionError); 1 taken, and the database works. */
    {
        static const int64_t bad[] = { 0, -1, INT64_MIN };
        static const char *const badText[] = {
            "IllegalArgumentException: Bad cacheSizeIndicator: 0.",
            "IllegalArgumentException: Bad cacheSizeIndicator: -1.",
            "IllegalArgumentException: Bad cacheSizeIndicator: -9223372036854775808." };
        struct bergdb_test_clock c2 = {0};
        struct bergdb_options o2 = o;
        o2.clock_ctx = &c2;
        bergdb_test_clock_set(&c2, 1000);
        for (int i = 0; i < 3; i++) {
            o2.cache_size_indicator = bad[i];
            db = (bergdb_db *) &o;
            CHECK(bergdb_open(NULL, &o2, &db, NULL, errbuf) == BERGDB_ARG);
            CHECK(db == NULL);
            CHECK(strcmp(errbuf, badText[i]) == 0);
            CHECK_EQ(m.live_total, 0);
        }
        o2.cache_size_indicator = 1;
        REQUIRE(bergdb_open(NULL, &o2, &db, NULL, errbuf) == BERGDB_OK);
        struct bergdb_stats cs;
        REQUIRE(bergdb_stats(db, &cs) == BERGDB_OK);
        CHECK_EQ(cs.cache_size_indicator, 1);
        CHECK(put1(db, &c2, 2000, "/k", "v") == BERGDB_OK);
        bergdb_read *rd;
        struct bergdb_one one;
        uint8_t kb[8];
        size_t kl;
        REQUIRE(bergdb_read_new(db, &rd) == BERGDB_OK);
        CHECK(bergdb_get_one(db, rd, BERGDB_LATEST, se_key("/k", kb, &kl), kl, &one)
                == BERGDB_OK);
        CHECK(one.value != NULL && one.value_len == 1 && one.value[0] == 'v');
        bergdb_read_free(rd);
        CHECK(bergdb_close(db) == BERGDB_OK);
        CHECK_EQ(m.live_total, 0);
    }

    /* Created with node size 8 and startup distance 10; opened again with
     * another node size: FORMAT (005-50); with another startup distance:
     * the stream's (a setting in the stream). */
    struct bergdb_start_info info;
    REQUIRE(bergdb_open(dir, &o, &db, &info, errbuf) == BERGDB_OK);
    CHECK(errbuf[0] == '\0');
    CHECK(put1(db, &clock, 2000, "/a", "1") == BERGDB_OK);
    CHECK(bergdb_close(db) == BERGDB_OK);
    o.max_node_size = 30;
    CHECK(bergdb_open(dir, &o, &db, NULL, errbuf) == BERGDB_FORMAT);
    CHECK(db == NULL);
    CHECK(strstr(errbuf, "Exception: ") != NULL);
    o.max_node_size = 8;
    o.startup_distance = 5000;
    REQUIRE(bergdb_open(dir, &o, &db, &info, errbuf) == BERGDB_OK);
    struct bergdb_stats s;
    REQUIRE(bergdb_stats(db, &s) == BERGDB_OK);
    CHECK_EQ(s.startup_distance, 10);
    CHECK_EQ(info.trans_count, 2);
    CHECK_EQ(info.startup_distance, 10);        /* the stream's, in force (005-73, F1) */
    CHECK(bergdb_close(db) == BERGDB_OK);
    CHECK_EQ(m.live_total, 0);

    /* The defaults: Java's DbBuilder's. */
    bergdb_options_init(&o);
    CHECK_EQ(o.max_node_size, 30);
    CHECK_EQ(o.startup_distance, 50000000);
    CHECK_EQ(o.cache_size_indicator, 200000000);
    CHECK(o.clock == NULL && o.clock_ctx == NULL && o.mem == NULL);
    se_remove_dir(dir);
}

TEST(settings_errors_and_keys) {
    static const char *const names[] = { "BERGDB_OK", "BERGDB_RERUN", "BERGDB_NOT_AVAILABLE",
        "BERGDB_FAILED", "BERGDB_IO", "BERGDB_FORMAT", "BERGDB_STATE", "BERGDB_ARG",
        "BERGDB_LIMIT", "BERGDB_NOT_CREATED", "BERGDB_IN_USE", "BERGDB_NOMEM" };
    for (int c = 0; c <= BERGDB_NOMEM; c++) {
        CHECK(strcmp(bergdb_errname(c), names[c]) == 0);
    }
    CHECK(strcmp(bergdb_errname(-1), "BERGDB_UNKNOWN") == 0);
    CHECK(strcmp(bergdb_errname(12), "BERGDB_UNKNOWN") == 0);
    CHECK(strcmp(bergdb_errmsg(NULL), "") == 0);

    /* Keys.toBytes and bkey2ikey: "/" is 1, every other byte + 2. */
    uint8_t b[16], i2[16];
    CHECK(bergdb_ikey_to_bkey((const uint8_t *) "/a/b", 4, b) == BERGDB_OK);
    CHECK(b[0] == 1 && b[1] == 'a' + 2 && b[2] == 1 && b[3] == 'b' + 2);
    CHECK(bergdb_bkey_to_ikey(b, 4, i2) == BERGDB_OK);
    CHECK(memcmp(i2, "/a/b", 4) == 0);
    memcpy(b, "x/y", 3);
    CHECK(bergdb_ikey_to_bkey(b, 3, b) == BERGDB_OK);       /* in place */
    CHECK(b[0] == 'x' + 2 && b[1] == 1);
    CHECK(bergdb_bkey_to_ikey(b, 3, b) == BERGDB_OK);
    CHECK(memcmp(b, "x/y", 3) == 0);
    CHECK(bergdb_ikey_to_bkey(b, 0, b) == BERGDB_ARG);      /* the empty ikey */
    const uint8_t bad[] = { 'a', 0xfe };
    CHECK(bergdb_ikey_to_bkey(bad, 2, b) == BERGDB_ARG);
    CHECK(bergdb_ikey_to_bkey(NULL, 1, b) == BERGDB_ARG);
    CHECK(bergdb_ikey_to_bkey(bad, 1, NULL) == BERGDB_ARG);
    const uint8_t hi[] = { 0x7f, 0xf4, 0x8f, 0xbf, 0xbf };  /* U+10FFFF, UTF-8's largest */
    CHECK(bergdb_ikey_to_bkey(hi, 5, b) == BERGDB_OK && b[0] == 0x81 && b[1] == 0xf6
            && b[2] == 0x91 && b[3] == 0xc1 && b[4] == 0xc1);
    CHECK(bergdb_bkey_to_ikey(b, 5, b) == BERGDB_OK);
    CHECK(memcmp(b, hi, 5) == 0);
    /* Bytes that are not well-formed UTF-8 are refused, with nothing written
     * (bergdb 021-05): 021-04's CK1 (a surrogate, ED A0 80) and CK4 (an
     * overlong NUL, C0 80), and 0xfd, which C took before 022-02. */
    const uint8_t ck1[] = { 'a', 0xed, 0xa0, 0x80 }, ck4[] = { 'a', 0xc0, 0x80 };
    const uint8_t fd[] = { 0x7f, 0xfd };
    memset(b, 0xab, sizeof b);
    CHECK(bergdb_ikey_to_bkey(ck1, 4, b) == BERGDB_ARG && b[0] == 0xab && b[3] == 0xab);
    CHECK(bergdb_ikey_to_bkey(ck4, 3, b) == BERGDB_ARG && b[0] == 0xab);
    CHECK(bergdb_ikey_to_bkey(fd, 2, b) == BERGDB_ARG && b[0] == 0xab);
    /* A bkey without an ikey (bergdb 021-06): CK1's bkey, the bytes 0x31 and
     * 0; NULL pointers. The empty bkey gives the empty ikey, as Java's "". */
    const uint8_t none1[] = { 'a' + 2, 0xef, 0xa2, 0x82 }, none2[] = { 0x31 },
            none3[] = { 'a' + 2, 0 };
    CHECK(bergdb_bkey_to_ikey(none1, 4, i2) == BERGDB_ARG);
    CHECK(bergdb_bkey_to_ikey(none2, 1, i2) == BERGDB_ARG);
    CHECK(bergdb_bkey_to_ikey(none3, 2, i2) == BERGDB_ARG);
    CHECK(bergdb_bkey_to_ikey(NULL, 1, i2) == BERGDB_ARG);
    CHECK(bergdb_bkey_to_ikey(none2, 1, NULL) == BERGDB_ARG);
    CHECK(bergdb_bkey_to_ikey(none2, 0, i2) == BERGDB_OK);

    /* The test clock: forward only. */
    struct bergdb_test_clock clock = {0};
    CHECK_EQ(bergdb_test_clock_time(&clock), 0);
    CHECK(bergdb_test_clock_set(&clock, 0) == BERGDB_ARG);
    CHECK(bergdb_test_clock_set(&clock, 5) == BERGDB_OK);
    CHECK(bergdb_test_clock_set(&clock, 5) == BERGDB_ARG);
    CHECK(bergdb_test_clock_set(&clock, 4) == BERGDB_ARG);
    CHECK_EQ(bergdb_test_clock_time(&clock), 5);

    /* The range's defaults: GetMany's. */
    struct bergdb_range r;
    bergdb_range_init(&r);
    CHECK(r.lookup_time == BERGDB_LATEST && r.start_key == NULL && r.inclusive && r.forward);
    CHECK(r.prefix == NULL && r.end_key == NULL && r.end_inclusive && r.max_count == 0);
    CHECK(r.stop == NULL);
}

/* ======== Sync, the clock's times ======== */

TEST(settings_sync_and_times) {
    char dir[1024];
    se_temp_dir(dir, sizeof dir);
    REQUIRE(dir[0] != '\0');
    struct bergdb_mem m = {0};
    struct bergdb_test_clock clock = {0};
    struct bergdb_options o;
    struct bergdb_stats s;
    struct bergdb_executed ex1, ex2;
    bergdb_db *db;
    small_options(&o, &clock, &m);
    bergdb_test_clock_set(&clock, 1000);
    REQUIRE(bergdb_open(dir, &o, &db, NULL, NULL) == BERGDB_OK);
    REQUIRE(bergdb_stats(db, &s) == BERGDB_OK);
    CHECK_EQ(s.durable_length, 0);          /* the creation, in the buffer: as Java's */
    CHECK_EQ(s.stream_length, 264);

    bergdb_trans *t;
    uint8_t b[16];
    size_t kl;
    bergdb_test_clock_set(&clock, 2000);
    REQUIRE(bergdb_trans_new(db, &t) == BERGDB_OK);
    CHECK(bergdb_trans_put(t, se_key("/a", b, &kl), kl, (const uint8_t *) "1", 1) == BERGDB_OK);
    CHECK(bergdb_execute(db, t, &ex1) == BERGDB_OK);
    bergdb_test_clock_set(&clock, 3000);
    CHECK(bergdb_execute(db, t, &ex2) == BERGDB_OK);         /* executed again */
    bergdb_trans_free(t);
    CHECK_EQ(ex2.tpos, ex1.next_pos);
    CHECK_EQ(ex2.tt, 3000);

    /* NONE does nothing; a negative position needs nothing; past the end:
     * ARG (D11); a bad level: ARG. */
    CHECK(bergdb_sync(db, 0, BERGDB_SYNC_NONE) == BERGDB_OK);
    REQUIRE(bergdb_stats(db, &s) == BERGDB_OK);
    CHECK_EQ(s.durable_length, 0);
    CHECK(bergdb_sync(db, -1, BERGDB_SYNC_ORDINARY) == BERGDB_OK);
    REQUIRE(bergdb_stats(db, &s) == BERGDB_OK);
    CHECK_EQ(s.durable_length, 0);
    CHECK(bergdb_sync(db, ex2.next_pos, BERGDB_SYNC_ORDINARY) == BERGDB_ARG);
    CHECK(bergdb_sync(db, 0, 25) == BERGDB_ARG);
    CHECK(bergdb_sync(NULL, 0, BERGDB_SYNC_ORDINARY) == BERGDB_ARG);
    /* A sync to the first transaction's last byte: the stream is one, and
     * written and forced whole. */
    CHECK(bergdb_sync(db, ex1.last_pos, BERGDB_SYNC_ORDINARY) == BERGDB_OK);
    REQUIRE(bergdb_stats(db, &s) == BERGDB_OK);
    CHECK(s.durable_length >= ex1.last_pos + 1);
    CHECK_EQ(s.durable_length, s.stream_length);
    CHECK(bergdb_sync(db, 0, 30) == BERGDB_ARG);    /* STRONG, gone as Java's (2026.3) */

    /* currentTime: the clock's time, not before the last transaction's;
     * lookupTime: at most the last transaction's time. */
    int64_t now, actual;
    CHECK(bergdb_current_time(db, &now) == BERGDB_OK);
    CHECK_EQ(now, 3000);
    bergdb_test_clock_set(&clock, 5000);
    CHECK(bergdb_current_time(db, &now) == BERGDB_OK);
    CHECK_EQ(now, 5000);
    CHECK(bergdb_lookup_time(db, BERGDB_LATEST, &actual) == BERGDB_OK);
    CHECK_EQ(actual, 3000);
    CHECK(bergdb_lookup_time(db, 2500, &actual) == BERGDB_OK);
    CHECK_EQ(actual, 2500);
    CHECK(bergdb_current_time(db, NULL) == BERGDB_ARG);
    CHECK(bergdb_lookup_time(db, 1, NULL) == BERGDB_ARG);
    CHECK(bergdb_current_time(NULL, &now) == BERGDB_ARG);
    CHECK(bergdb_close(db) == BERGDB_OK);
    CHECK_EQ(m.live_total, 0);

    /* The system clock (the default): milliseconds times 10,000, now; one
     * unit more than the last time when the millisecond has not passed
     * (bergdb 005-69), as after the creation's read here. */
    struct bergdb_mem m2 = {0};
    bergdb_options_init(&o);
    o.mem = &m2;
    REQUIRE(bergdb_open(NULL, &o, &db, NULL, NULL) == BERGDB_OK);
    CHECK(bergdb_current_time(db, &now) == BERGDB_OK);
    int64_t later;
    CHECK(bergdb_current_time(db, &later) == BERGDB_OK);
    CHECK(later > now);
    CHECK(now > INT64_C(17600000000000000) && now < INT64_C(40000000000000000));
    CHECK(bergdb_close(db) == BERGDB_OK);
    CHECK_EQ(m2.live_total, 0);
    se_remove_dir(dir);
}

/* A clock that the test sets to any time, back too. */
static int64_t se_now(void *ctx) {
    return *(const int64_t *) ctx;
}

/* A put of one key, its time in *tt; the call's code. */
static int se_put(bergdb_db *db, const char *ikey, const char *value, int64_t *tt) {
    bergdb_trans *t;
    struct bergdb_executed ex;
    uint8_t b[64];
    size_t kl;
    int rc = bergdb_trans_new(db, &t);
    if (rc == BERGDB_OK) {
        rc = bergdb_trans_put(t, se_key(ikey, b, &kl), kl, (const uint8_t *) value,
                strlen(value));
    }
    if (rc == BERGDB_OK) {
        rc = bergdb_execute(db, t, &ex);
    }
    if (rc == BERGDB_OK && tt != NULL) {
        *tt = ex.tt;
    }
    bergdb_trans_free(t);
    return rc;
}

/* True if the key's value at the lookup time is the text. */
static bool se_value_is(bergdb_db *db, int64_t time, const char *ikey, const char *text) {
    bergdb_read *rd;
    struct bergdb_one one;
    uint8_t b[64];
    size_t kl;
    if (bergdb_read_new(db, &rd) != BERGDB_OK) {
        return false;
    }
    bool is = bergdb_get_one(db, rd, time, se_key(ikey, b, &kl), kl, &one) == BERGDB_OK
            && one.value != NULL && one.value_len == strlen(text)
            && memcmp(one.value, text, one.value_len) == 0;
    bergdb_read_free(rd);
    return is;
}

/* PubTesterJavadocRest.testCurrentTimeWithAClockThatGoesBack (bergdb
 * 020-23, Z1): with a clock that goes back, the time bergdb_current_time
 * gives is before every later transaction's time, so a read at it gives
 * the same value after a later put; a later call does not give an earlier
 * time. The second call gave the clock's earlier time, and a put after it
 * took a time before the first one given, which then read the put's
 * value. */
TEST(settings_current_time_with_a_clock_that_goes_back) {
    struct bergdb_mem m = {0};
    struct bergdb_options o;
    int64_t now = 1000, first = -1, later = -1, written = -1;
    bergdb_db *db;
    bergdb_options_init(&o);
    o.clock = se_now;
    o.clock_ctx = &now;
    o.mem = &m;
    REQUIRE(bergdb_open(NULL, &o, &db, NULL, NULL) == BERGDB_OK);
    CHECK(se_put(db, "/a", "before", NULL) == BERGDB_OK);
    now = 2000;
    CHECK(bergdb_current_time(db, &first) == BERGDB_OK);
    CHECK_EQ(first, 2000);
    now = 1500;
    CHECK(bergdb_current_time(db, &later) == BERGDB_OK);
    CHECK_EQ(later, 2000);
    CHECK(se_put(db, "/a", "after", &written) == BERGDB_OK);
    CHECK(written > first);
    CHECK(se_value_is(db, first, "/a", "before"));
    CHECK(se_value_is(db, BERGDB_LATEST, "/a", "after"));
    CHECK(bergdb_close(db) == BERGDB_OK);
    CHECK_EQ(m.live_total, 0);
}

/* PubTesterJavadocRest.testStartWithTheClockOutOfRange (bergdb 020-23, Z3;
 * Clock's Javadoc since 2026.4): an open that creates a database with the
 * clock out of range is refused, as it writes the database's first
 * transaction; an open of an existing one does not read the clock and
 * succeeds, its reads work, and its transactions are refused (BERGDB_LIMIT,
 * the database going on) until the clock is back in the range. Each case
 * on a database of its own, created at 1000, as Java's on a copy. */
TEST(settings_open_with_the_clock_out_of_range) {
    char base[1024], dir[1100], errbuf[BERGDB_ERRBUF_SIZE];
    se_temp_dir(base, sizeof base);
    REQUIRE(base[0] != '\0');
    struct bergdb_mem m = {0};
    struct bergdb_options o;
    int64_t now = INT64_C(1) << 56, tt = -1;
    bergdb_db *db;
    bergdb_options_init(&o);
    o.clock = se_now;
    o.clock_ctx = &now;
    o.mem = &m;
    snprintf(dir, sizeof dir, "%s/creation", base);
    CHECK(bergdb_open(dir, &o, &db, NULL, errbuf) == BERGDB_LIMIT);
    CHECK(strstr(errbuf, "outside the range") != NULL);
    CHECK_EQ(m.live_total, 0);

    const int64_t times[] = { INT64_C(1) << 56, -1 };
    for (int i = 0; i < 2; i++) {
        snprintf(dir, sizeof dir, "%s/existing-%d", base, i);
        now = 1000;
        REQUIRE(bergdb_open(dir, &o, &db, NULL, NULL) == BERGDB_OK);
        CHECK(se_put(db, "/a", "a", NULL) == BERGDB_OK);
        CHECK(bergdb_close(db) == BERGDB_OK);
        now = times[i];
        REQUIRE(bergdb_open(dir, &o, &db, NULL, errbuf) == BERGDB_OK);
        CHECK(se_value_is(db, BERGDB_LATEST, "/a", "a"));
        CHECK_EQ(se_put(db, "/b", "b", NULL), BERGDB_LIMIT);
        now = 2000;
        CHECK(se_put(db, "/b", "b", &tt) == BERGDB_OK);
        CHECK_EQ(tt, 2000);
        CHECK(se_value_is(db, BERGDB_LATEST, "/b", "b"));
        CHECK(bergdb_close(db) == BERGDB_OK);
        CHECK_EQ(m.live_total, 0);
    }
    se_remove_dir(base);
}

/* ======== The debug calls ======== */

TEST(settings_debug) {
    struct bergdb_mem m = {0};
    struct bergdb_test_clock clock = {0};
    struct bergdb_options o;
    bergdb_db *db;
    small_options(&o, &clock, &m);
    bergdb_test_clock_set(&clock, 1000);
    REQUIRE(bergdb_open(NULL, &o, &db, NULL, NULL) == BERGDB_OK);
    for (int i = 0; i < 300; i++) {
        char ikey[32];
        snprintf(ikey, sizeof ikey, "/k/%d", i * 37 % 211);
        CHECK(put1(db, &clock, 2000 + i, ikey, "value") == BERGDB_OK);
        if (i % 50 == 0) {
            CHECK(bergdb_debug_check(db) == BERGDB_OK);
        }
    }
    CHECK(bergdb_debug_check(db) == BERGDB_OK);
    char *text = NULL;
    size_t size = 0;
    FILE *f = open_memstream(&text, &size);
    REQUIRE(f != NULL);
    CHECK(bergdb_debug_print(db, f) == BERGDB_OK);
    fclose(f);
    CHECK(text != NULL && strncmp(text, "top ordinal=", 12) == 0);
    CHECK(text != NULL && strstr(text, "\nin memory: ") != NULL);
    CHECK(text != NULL && strstr(text, " key nodes, ") != NULL && strstr(text, "value spos=") != NULL);
    free(text);
    CHECK(bergdb_debug_print(db, NULL) == BERGDB_ARG);
    CHECK(bergdb_debug_check(NULL) == BERGDB_ARG);

    /* After a restart, with most of the index in the stream: the nodes in
     * memory only (stream pointers printed as "-> POS"). */
    /* On a failed database: FAILED (D14). */
    bergdb_read *rd;
    struct bergdb_stored st;
    REQUIRE(bergdb_read_new(db, &rd) == BERGDB_OK);
    CHECK(bergdb_get_trans(db, rd, 264 + 8, &st) == BERGDB_FAILED);
    bergdb_read_free(rd);
    CHECK(bergdb_debug_check(db) == BERGDB_FAILED);
    CHECK(bergdb_debug_print(db, stdout) == BERGDB_FAILED);
    CHECK(strstr(bergdb_errmsg(db), "DbFailedException") != NULL);
    CHECK(bergdb_close(db) == BERGDB_OK);
    CHECK_EQ(m.live_total, 0);
}

/* The debug calls on a started database, whose index is mostly in the
 * stream: the walk takes what is in memory. */
TEST(settings_debug_after_start) {
    char dir[1024];
    se_temp_dir(dir, sizeof dir);
    REQUIRE(dir[0] != '\0');
    struct bergdb_mem m = {0};
    struct bergdb_test_clock clock = {0};
    struct bergdb_options o;
    bergdb_db *db;
    small_options(&o, &clock, &m);
    bergdb_test_clock_set(&clock, 1000);
    REQUIRE(bergdb_open(dir, &o, &db, NULL, NULL) == BERGDB_OK);
    for (int i = 0; i < 400; i++) {
        char ikey[32];
        snprintf(ikey, sizeof ikey, "/k/%d", i * 37 % 311);
        CHECK(put1(db, &clock, 2000 + i, ikey, "value") == BERGDB_OK);
    }
    CHECK(bergdb_close(db) == BERGDB_OK);
    REQUIRE(bergdb_open(dir, &o, &db, NULL, NULL) == BERGDB_OK);
    CHECK(bergdb_debug_check(db) == BERGDB_OK);
    char *text = NULL;
    size_t size = 0;
    FILE *f = open_memstream(&text, &size);
    REQUIRE(f != NULL);
    CHECK(bergdb_debug_print(db, f) == BERGDB_OK);
    fclose(f);
    CHECK(text != NULL && strstr(text, "-> ") != NULL);
    free(text);
    CHECK(put1(db, &clock, 5000, "/k/1", "again") == BERGDB_OK);
    CHECK(bergdb_debug_check(db) == BERGDB_OK);
    CHECK(bergdb_close(db) == BERGDB_OK);
    CHECK_EQ(m.live_total, 0);
    se_remove_dir(dir);
}

/* ======== Close, and calls from a callback ======== */

struct cb_state {
    bergdb_db *db;
    bergdb_trans *t;
    bergdb_read *rd;
    int calls;
    int not_state;      /* calls that did not give BERGDB_STATE */
};

static void expect_state(struct cb_state *c, int rc) {
    c->calls++;
    if (rc != BERGDB_STATE) {
        c->not_state++;
    }
}

/* A stop condition that calls every function of its database: each gives
 * BERGDB_STATE and does nothing (bergdb.h, D), the close too. */
static int stop_calls_all(void *ctx, const struct bergdb_kvt *kvt) {
    (void) kvt;
    struct cb_state *c = ctx;
    bergdb_db *db = c->db;
    bergdb_trans *t2;
    bergdb_read *rd2;
    struct bergdb_one one;
    struct bergdb_range r;
    struct bergdb_many many;
    struct bergdb_stored st;
    struct bergdb_stats s;
    struct bergdb_executed ex;
    int64_t x;
    const uint8_t k[] = { 3 };
    bergdb_range_init(&r);
    expect_state(c, bergdb_close(db));
    expect_state(c, bergdb_trans_new(db, &t2));
    expect_state(c, bergdb_trans_put(c->t, k, 1, k, 1));
    expect_state(c, bergdb_trans_put_transformed(c->t, k, 1, k, 1, NULL));
    expect_state(c, bergdb_trans_delete(c->t, k, 1));
    expect_state(c, bergdb_trans_key_read(c->t, k, 1));
    expect_state(c, bergdb_trans_lookup_time(c->t, 5));
    expect_state(c, bergdb_execute(db, c->t, &ex));
    expect_state(c, bergdb_read_new(db, &rd2));
    expect_state(c, bergdb_get_one(db, c->rd, BERGDB_LATEST, k, 1, &one));
    expect_state(c, bergdb_get_many(db, c->rd, &r, &many));
    expect_state(c, bergdb_get_trans(db, c->rd, 264, &st));
    expect_state(c, bergdb_sync(db, 0, BERGDB_SYNC_ORDINARY));
    expect_state(c, bergdb_current_time(db, &x));
    expect_state(c, bergdb_lookup_time(db, 5, &x));
    expect_state(c, bergdb_set_startup_distance(db, 500000));
    expect_state(c, bergdb_set_cache_size_indicator(db, 5));
    expect_state(c, bergdb_set_retain_duration(db, BERGDB_FOREVER));
    expect_state(c, bergdb_set_reclaim_internal_fraction(db, 0.3));
    expect_state(c, bergdb_stats(db, &s));
    expect_state(c, bergdb_debug_print(db, stdout));
    expect_state(c, bergdb_debug_check(db));
    bergdb_trans_free(c->t);        /* does nothing */
    bergdb_read_free(c->rd);
    return BERGDB_ADD_AND_STOP;
}

TEST(settings_close_and_callbacks) {
    struct bergdb_mem m = {0};
    struct bergdb_test_clock clock = {0};
    struct bergdb_options o;
    bergdb_db *db;
    small_options(&o, &clock, &m);
    bergdb_test_clock_set(&clock, 1000);
    CHECK(bergdb_close(NULL) == BERGDB_OK);
    REQUIRE(bergdb_open(NULL, &o, &db, NULL, NULL) == BERGDB_OK);
    CHECK(put1(db, &clock, 2000, "/a", "1") == BERGDB_OK);
    struct cb_state c;
    memset(&c, 0, sizeof c);
    c.db = db;
    REQUIRE(bergdb_trans_new(db, &c.t) == BERGDB_OK);
    REQUIRE(bergdb_read_new(db, &c.rd) == BERGDB_OK);
    struct bergdb_range r;
    struct bergdb_many many;
    bergdb_range_init(&r);
    r.stop = stop_calls_all;
    r.stop_ctx = &c;
    CHECK(bergdb_get_many(db, c.rd, &r, &many) == BERGDB_OK);
    CHECK_EQ(c.calls, 22);
    CHECK_EQ(c.not_state, 0);
    CHECK_EQ((int64_t) many.count, 1);
    /* The transaction and the read context are still there, and work. */
    uint8_t b[16];
    size_t kl;
    CHECK(bergdb_trans_put(c.t, se_key("/b", b, &kl), kl, (const uint8_t *) "2", 1) == BERGDB_OK);
    bergdb_test_clock_set(&clock, 3000);
    CHECK(bergdb_execute(db, c.t, NULL) == BERGDB_OK);
    struct bergdb_one one;
    CHECK(bergdb_get_one(db, c.rd, BERGDB_LATEST, se_key("/b", b, &kl), kl, &one) == BERGDB_OK);
    CHECK(one.value != NULL && one.value_len == 1);
    /* Close with a transaction and a read context not freed: it frees them,
     * and every byte (D10). */
    CHECK(m.live_total > 0);
    CHECK(bergdb_close(db) == BERGDB_OK);
    CHECK_EQ(m.live_total, 0);
    CHECK_EQ(m.live_blocks, 0);
}

const struct test settings_tests[] = {
    TEST_ENTRY(settings_and_status_as_java),
    TEST_ENTRY(settings_setters),
    TEST_ENTRY(settings_open_checks),
    TEST_ENTRY(settings_errors_and_keys),
    TEST_ENTRY(settings_sync_and_times),
    TEST_ENTRY(settings_current_time_with_a_clock_that_goes_back),
    TEST_ENTRY(settings_open_with_the_clock_out_of_range),
    TEST_ENTRY(settings_debug),
    TEST_ENTRY(settings_debug_after_start),
    TEST_ENTRY(settings_close_and_callbacks),
    TEST_END
};
