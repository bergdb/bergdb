/* Functional tests of the memory budget (bergdb 012-12; Level 4), through
 * include/bergdb.h only: a database run with budgets from one byte up and
 * one without eviction, the same transactions with restarts: the same files
 * byte for byte, the same answers of getOne at many times and of getMany
 * both ways; a scan of the whole database from a cold start stays within
 * the budget as it goes (eviction between getMany's pairs), where without
 * one it loads the whole index; and the setter gives the memory back in its
 * call. Each test ends with the allocator's count 0. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include "test.h"
#include "bergdb.h"

static void bu_temp_dir(char *out, size_t cap) {
    const char *t = getenv("TMPDIR");
    snprintf(out, cap, "%s/bergdb-budget-XXXXXX", t != NULL ? t : "/tmp");
    if (mkdtemp(out) == NULL) {
        out[0] = '\0';
    }
}

static void bu_remove_dir(const char *dir) {
    char cmd[1200];
    snprintf(cmd, sizeof cmd, "rm -rf '%s'", dir);
    if (system(cmd) != 0) {
        printf("could not remove %s\n", dir);
    }
}

/* The two directories' files equal (cmp of every file, by the shell). */
static bool same_dirs(const char *a, const char *b) {
    char cmd[2600];
    snprintf(cmd, sizeof cmd, "diff -r '%s' '%s' > /dev/null", a, b);
    return system(cmd) == 0;
}

static void bu_options(struct bergdb_options *o, struct bergdb_test_clock *clock,
        struct bergdb_mem *m, int64_t budget) {
    bergdb_options_init(o);
    o->clock = bergdb_test_clock_time;
    o->clock_ctx = clock;
    memcpy(o->id, bergdb_test_id, BERGDB_ID_SIZE);
    o->max_node_size = 8;
    o->startup_distance = 2000;
    o->cache_size_indicator = budget;
    o->mem = m;
}

enum { KEYS = 3000 };

/* Transaction i: 12 puts and deletes of keys drawn from KEYS. */
static int trans_i(bergdb_db *db, struct bergdb_test_clock *clock, int i) {
    bergdb_test_clock_set(clock, 1000 + 10 * (int64_t) i);
    bergdb_trans *t;
    int rc = bergdb_trans_new(db, &t);
    if (rc != BERGDB_OK) {
        return rc;
    }
    uint32_t x = 2463534242u ^ (uint32_t) (i * 7919);
    for (int j = 0; j < 12 && rc == BERGDB_OK; j++) {
        x ^= x << 13;
        x ^= x >> 17;
        x ^= x << 5;
        char ikey[32], value[64];
        uint8_t bkey[32];
        snprintf(ikey, sizeof ikey, "/k/%u", x % KEYS);
        size_t kl = strlen(ikey);
        bergdb_ikey_to_bkey((const uint8_t *) ikey, kl, bkey);
        if (j == 11 && i % 4 == 0) {
            rc = bergdb_trans_delete(t, bkey, kl);
        } else {
            snprintf(value, sizeof value, "value %d of %d, %u", j, i, x);
            rc = bergdb_trans_put(t, bkey, kl, (const uint8_t *) value, strlen(value));
        }
    }
    if (rc == BERGDB_OK) {
        struct bergdb_executed ex;
        rc = bergdb_execute(db, t, &ex);
    }
    bergdb_trans_free(t);
    return rc;
}

static uint64_t fnv(uint64_t h, const uint8_t *p, size_t n) {
    for (size_t j = 0; j < n; j++) {
        h = (h ^ p[j]) * 1099511628211u;
    }
    return (h ^ 0xff) * 1099511628211u;
}

/* A digest of getMany at time t, forward or backward. */
static uint64_t many_digest(bergdb_db *db, int64_t t, bool forward, int64_t *count) {
    bergdb_read *rd;
    uint64_t h = 1469598103934665603u;
    *count = -1;
    if (bergdb_read_new(db, &rd) != BERGDB_OK) {
        return 0;
    }
    struct bergdb_range r;
    struct bergdb_many many;
    bergdb_range_init(&r);
    r.lookup_time = t;
    r.forward = forward;
    if (bergdb_get_many(db, rd, &r, &many) == BERGDB_OK) {
        *count = (int64_t) many.count;
        for (size_t i = 0; i < many.count; i++) {
            h = fnv(h, many.kvts[i].key, many.kvts[i].key_len);
            h = fnv(h, many.kvts[i].value, many.kvts[i].value_len);
            h = fnv(h, (const uint8_t *) &many.kvts[i].time, sizeof many.kvts[i].time);
        }
    }
    bergdb_read_free(rd);
    return h;
}

/* A scan's stop function that digests each pair and keeps none. */
struct scan_ctx {
    uint64_t h;
    int64_t n;
};

static int scan_fn(void *ctx, const struct bergdb_kvt *kv) {
    struct scan_ctx *c = ctx;
    c->h = fnv(c->h, kv->key, kv->key_len);
    c->h = fnv(c->h, kv->value, kv->value_len);
    c->n++;
    return BERGDB_CONTINUE;
}

/* A scan of the latest state that keeps no pair: its digest. */
static uint64_t scan_digest(bergdb_db *db, int64_t *count) {
    bergdb_read *rd;
    struct scan_ctx c = { 1469598103934665603u, 0 };
    *count = -1;
    if (bergdb_read_new(db, &rd) != BERGDB_OK) {
        return 0;
    }
    struct bergdb_range r;
    struct bergdb_many many;
    bergdb_range_init(&r);
    r.stop = scan_fn;
    r.stop_ctx = &c;
    if (bergdb_get_many(db, rd, &r, &many) == BERGDB_OK) {
        *count = c.n;
    }
    bergdb_read_free(rd);
    return c.h;
}

/* A digest of getOne of every 7th key at times through the history. */
static uint64_t gets_digest(bergdb_db *db, int n) {
    bergdb_read *rd;
    uint64_t h = 1469598103934665603u;
    if (bergdb_read_new(db, &rd) != BERGDB_OK) {
        return 0;
    }
    for (int i = 0; i < n; i += 37) {
        for (int k = i % 7; k < KEYS; k += 7) {
            char ikey[32];
            uint8_t bkey[32];
            snprintf(ikey, sizeof ikey, "/k/%d", k);
            size_t kl = strlen(ikey);
            bergdb_ikey_to_bkey((const uint8_t *) ikey, kl, bkey);
            struct bergdb_one one;
            if (bergdb_get_one(db, rd, 1000 + 10 * (int64_t) i - 3, bkey, kl, &one)
                    != BERGDB_OK) {
                bergdb_read_free(rd);
                return 0;
            }
            h = fnv(h, one.value == NULL ? (const uint8_t *) "-" : one.value,
                    one.value == NULL ? 1 : one.value_len);
        }
    }
    bergdb_read_free(rd);
    return h;
}

struct result {
    uint64_t gets, fwd, bwd, old, scan;
    int64_t nfwd, nbwd, nold, nscan;
    int64_t scan_growth;        /* the allocator's peak over its count during a cold scan */
    int64_t resident;           /* the resident bytes after the run */
    int64_t evicted;
};

/* The run: N transactions with a restart every 100, then a restart, a cold
 * scan (its memory measured), reads. */
static void run_budget(const char *dir, int64_t budget, struct result *out) {
    enum { N = 400 };
    struct bergdb_mem m = {0};
    struct bergdb_test_clock c = {0};
    struct bergdb_options o;
    bu_options(&o, &c, &m, budget);
    char errbuf[BERGDB_ERRBUF_SIZE];
    bergdb_db *db = NULL;
    bergdb_test_clock_set(&c, 500);
    for (int i = 0; i < N; i++) {
        if (i % 100 == 0) {
            if (db != NULL) {
                CHECK(bergdb_close(db) == BERGDB_OK);
            }
            REQUIRE(bergdb_open(dir, &o, &db, NULL, errbuf) == BERGDB_OK);
        }
        CHECK_EQ(trans_i(db, &c, i), BERGDB_OK);
    }
    CHECK(bergdb_close(db) == BERGDB_OK);
    REQUIRE(bergdb_open(dir, &o, &db, NULL, errbuf) == BERGDB_OK);
    m.peak_total = m.live_total;
    const int64_t before = m.live_total;
    out->scan = scan_digest(db, &out->nscan);
    out->scan_growth = m.peak_total - before;
    out->fwd = many_digest(db, INT64_MAX, true, &out->nfwd);
    out->bwd = many_digest(db, INT64_MAX, false, &out->nbwd);
    out->old = many_digest(db, 1000 + 10 * (N / 2), true, &out->nold);
    out->gets = gets_digest(db, N);
    struct bergdb_stats s;
    CHECK(bergdb_stats(db, &s) == BERGDB_OK);
    out->resident = s.resident_bytes;
    out->evicted = s.evicted;
    CHECK_EQ(s.cache_size_indicator, budget);
    CHECK(bergdb_close(db) == BERGDB_OK);
    CHECK_EQ(m.live_total, 0);
}

TEST(budget_invariance) {
    const int64_t budgets[] = {BERGDB_NO_EVICT, 1, 4000, 50000, 400000};
    char dirs[5][1024];
    struct result r[5];
    for (int b = 0; b < 5; b++) {
        bu_temp_dir(dirs[b], sizeof dirs[b]);
        REQUIRE(dirs[b][0] != '\0');
        run_budget(dirs[b], budgets[b], &r[b]);
    }
    CHECK(r[0].nfwd > 1000);
    CHECK_EQ(r[0].nscan, r[0].nfwd);
    CHECK_EQ(r[0].evicted, 0);
    for (int b = 1; b < 5; b++) {
        CHECK(same_dirs(dirs[0], dirs[b]));
        CHECK(r[b].fwd == r[0].fwd);
        CHECK(r[b].scan == r[0].scan);
        CHECK_EQ(r[b].nscan, r[0].nscan);
        CHECK(r[b].bwd == r[0].bwd);
        CHECK(r[b].old == r[0].old);
        CHECK(r[b].gets == r[0].gets);
        CHECK_EQ(r[b].nfwd, r[0].nfwd);
        CHECK_EQ(r[b].nbwd, r[0].nbwd);
        CHECK_EQ(r[b].nold, r[0].nold);
        CHECK(r[b].evicted > 0);
        CHECK(r[b].resident < r[0].resident);
    }
    /* A cold scan without a budget loads the whole index; with a budget of
     * one byte it keeps only a path and what must stay. */
    CHECK(r[1].scan_growth * 4 < r[0].scan_growth);
    printf("  budget_invariance: resident bytes after the run %lld (no budget), %lld (1), "
            "%lld (4000), %lld (50000), %lld (400000); a cold scan's growth %lld and %lld "
            "(1 byte)\n", (long long) r[0].resident, (long long) r[1].resident,
            (long long) r[2].resident, (long long) r[3].resident, (long long) r[4].resident,
            (long long) r[0].scan_growth, (long long) r[1].scan_growth);
    for (int b = 0; b < 5; b++) {
        bu_remove_dir(dirs[b]);
    }
}

/* setCacheSizeIndicator (005-52): a decrease evicts in the call, so an idle
 * database gives the memory back; an increase keeps what is there. */
TEST(budget_setter) {
    char dir[1024];
    bu_temp_dir(dir, sizeof dir);
    REQUIRE(dir[0] != '\0');
    struct bergdb_mem m = {0};
    struct bergdb_test_clock c = {0};
    struct bergdb_options o;
    bu_options(&o, &c, &m, BERGDB_NO_EVICT);
    char errbuf[BERGDB_ERRBUF_SIZE];
    bergdb_db *db;
    bergdb_test_clock_set(&c, 500);
    REQUIRE(bergdb_open(dir, &o, &db, NULL, errbuf) == BERGDB_OK);
    for (int i = 0; i < 300; i++) {
        CHECK_EQ(trans_i(db, &c, i), BERGDB_OK);
    }
    int64_t n;
    uint64_t d0 = many_digest(db, INT64_MAX, true, &n);
    struct bergdb_stats s0, s1, s2;
    CHECK(bergdb_stats(db, &s0) == BERGDB_OK);
    CHECK(bergdb_set_cache_size_indicator(db, 0) == BERGDB_ARG);
    CHECK(bergdb_set_cache_size_indicator(db, 20000) == BERGDB_OK);
    CHECK(bergdb_stats(db, &s1) == BERGDB_OK);
    CHECK_EQ(s1.cache_size_indicator, 20000);
    CHECK(s1.resident_bytes < s0.resident_bytes / 2);
    CHECK(s1.evicted > 0);
    CHECK(bergdb_set_cache_size_indicator(db, BERGDB_NO_EVICT) == BERGDB_OK);
    CHECK(bergdb_stats(db, &s2) == BERGDB_OK);
    CHECK_EQ(s2.resident_bytes, s1.resident_bytes);
    CHECK(many_digest(db, INT64_MAX, true, &n) == d0);
    CHECK(bergdb_close(db) == BERGDB_OK);
    CHECK_EQ(m.live_total, 0);
    printf("  budget_setter: resident bytes %lld, after setting 20000: %lld\n",
            (long long) s0.resident_bytes, (long long) s1.resident_bytes);
    bu_remove_dir(dir);
}

/* ======== CapacityTester's and Eviction's budgets under reads (022-05) ======== */

enum { CAP_VALUE = 300 };

static size_t cap_key(int i, uint8_t *bkey) {
    char ikey[32];
    snprintf(ikey, sizeof ikey, "/c/%d", i);
    size_t kl = strlen(ikey);
    bergdb_ikey_to_bkey((const uint8_t *) ikey, kl, bkey);
    return kl;
}

/* Key i's value: len bytes made of i. */
static void cap_value(int i, uint8_t *v, size_t len) {
    uint32_t x = 2463534242u ^ (uint32_t) (i * 7919 + 1);
    for (size_t j = 0; j < len; j++) {
        x ^= x << 13;
        x ^= x >> 17;
        x ^= x << 5;
        v[j] = (uint8_t) x;
    }
}

/* A new database in dir with n keys of CAP_VALUE bytes, 50 to a
 * transaction, and no eviction; closed. */
static void cap_fill(const char *dir, int n) {
    struct bergdb_mem m = {0};
    struct bergdb_test_clock c = {0};
    struct bergdb_options o;
    bu_options(&o, &c, &m, BERGDB_NO_EVICT);
    o.max_node_size = 30;
    char errbuf[BERGDB_ERRBUF_SIZE];
    bergdb_db *db;
    bergdb_test_clock_set(&c, 500);
    REQUIRE(bergdb_open(dir, &o, &db, NULL, errbuf) == BERGDB_OK);
    for (int i = 0; i < n; i += 50) {
        bergdb_trans *t;
        REQUIRE(bergdb_trans_new(db, &t) == BERGDB_OK);
        for (int j = i; j < i + 50 && j < n; j++) {
            uint8_t bkey[32], v[CAP_VALUE];
            size_t kl = cap_key(j, bkey);
            cap_value(j, v, sizeof v);
            CHECK(bergdb_trans_put(t, bkey, kl, v, sizeof v) == BERGDB_OK);
        }
        bergdb_test_clock_set(&c, 1000 + i);
        CHECK(bergdb_execute(db, t, NULL) == BERGDB_OK);
        bergdb_trans_free(t);
    }
    CHECK(bergdb_close(db) == BERGDB_OK);
    CHECK_EQ(m.live_total, 0);
}

/* getOne of key i: its value is right. */
static bool cap_get(bergdb_db *db, bergdb_read *rd, int i) {
    uint8_t bkey[32], v[CAP_VALUE];
    size_t kl = cap_key(i, bkey);
    struct bergdb_one one;
    cap_value(i, v, sizeof v);
    return bergdb_get_one(db, rd, BERGDB_LATEST, bkey, kl, &one) == BERGDB_OK
            && one.value != NULL && one.value_len == sizeof v
            && memcmp(one.value, v, sizeof v) == 0;
}

static int64_t cap_resident(bergdb_db *db, struct bergdb_stats *s) {
    CHECK(bergdb_stats(db, s) == BERGDB_OK);
    return s->resident_bytes;
}

/* CapacityTester.testReadsWithoutWrites and testSweepsStopNearLow: reads
 * with no writes, a database of 2,000 keys of 300 bytes (600 kB of values),
 * started cold with a budget of 100 kB; every key read in random order,
 * three times. After each read the resident bytes are at most the budget
 * (C evicts at the end of the call that loaded, where Java's thread allows
 * one load's worth more), and every value is right. And a sweep stops near
 * the low watermark (3/4 of the budget): once one has run, the resident
 * bytes, sampled after every read, stay above the low watermark less one
 * key node's worth (16 kB here), not down at the pinned state, as a sweep
 * that went on past the watermark would leave them. */
TEST(budget_reads_without_writes) {
    enum { N = 2000, BUDGET = 100000, SLACK = 16000 };
    char dir[1024];
    bu_temp_dir(dir, sizeof dir);
    REQUIRE(dir[0] != '\0');
    cap_fill(dir, N);
    struct bergdb_mem m = {0};
    struct bergdb_test_clock c = {0};
    struct bergdb_options o;
    bu_options(&o, &c, &m, BUDGET);
    o.max_node_size = 30;
    char errbuf[BERGDB_ERRBUF_SIZE];
    bergdb_db *db;
    bergdb_test_clock_set(&c, 500000);
    REQUIRE(bergdb_open(dir, &o, &db, NULL, errbuf) == BERGDB_OK);
    bergdb_read *rd;
    REQUIRE(bergdb_read_new(db, &rd) == BERGDB_OK);
    struct bergdb_stats s;
    int64_t most = 0, least_after = INT64_MAX;
    int wrong = 0, over = 0, low = 0;
    uint64_t rnd = 17;
    for (int round = 0; round < 3; round++) {
        for (int k = 0; k < N; k++) {
            int i = (int) ((uint64_t) (k * 7 + round) * 1031u % N);
            if (round == 2) {
                i = test_random_below(&rnd, N);
            }
            if (!cap_get(db, rd, i)) {
                wrong++;
            }
            int64_t r = cap_resident(db, &s);
            most = r > most ? r : most;
            if (r > BUDGET) {
                over++;
            }
            if (s.evicted > 0) {
                least_after = r < least_after ? r : least_after;
                if (r < BUDGET / 4 * 3 - SLACK) {
                    low++;
                }
            }
        }
    }
    CHECK_EQ(wrong, 0);
    CHECK_EQ(over, 0);
    CHECK_EQ(low, 0);
    CHECK(s.evicted > N / 30);
    CHECK(s.pinned_bytes < BUDGET / 2);
    printf("  budget_reads_without_writes: resident bytes at most %lld, at least %lld after "
            "the first sweep (budget %d, low watermark %d); %lld evicted\n", (long long) most,
            (long long) least_after, BUDGET, BUDGET / 4 * 3, (long long) s.evicted);
    bergdb_read_free(rd);
    CHECK(bergdb_close(db) == BERGDB_OK);
    CHECK_EQ(m.live_total, 0);
    bu_remove_dir(dir);
}

/* Eviction.testLoweredBudgetAfterReads and
 * CapacityTester.testBudgetLoweredAndRaisedUnderReads (and
 * testBudgetLoweredWhileIdle, 005-52): 2,000 keys of 300 bytes, started cold
 * with a budget of 10 MB, every key read twice, so that every value is
 * resident and every handle's CLOCK bit set; the budget lowered to 9/10 of
 * the resident bytes, with no other call: the setter's call brings them to
 * at most the budget, though its sweep's first round only clears the bits
 * (015-10: a first round that freed nothing ended Java's batches). Then a
 * quarter of the first resident bytes: at most that after the call, and
 * after every read of two rounds of random reads, the values right; the
 * budget raised again: the call keeps what is there, and the reads grow the
 * resident bytes past the low budget. */
TEST(budget_lowered_and_raised_under_reads) {
    enum { N = 2000 };
    char dir[1024];
    bu_temp_dir(dir, sizeof dir);
    REQUIRE(dir[0] != '\0');
    cap_fill(dir, N);
    struct bergdb_mem m = {0};
    struct bergdb_test_clock c = {0};
    struct bergdb_options o;
    bu_options(&o, &c, &m, 10 * 1000 * 1000);
    o.max_node_size = 30;
    char errbuf[BERGDB_ERRBUF_SIZE];
    bergdb_db *db;
    bergdb_test_clock_set(&c, 500000);
    REQUIRE(bergdb_open(dir, &o, &db, NULL, errbuf) == BERGDB_OK);
    bergdb_read *rd;
    REQUIRE(bergdb_read_new(db, &rd) == BERGDB_OK);
    struct bergdb_stats s;
    int wrong = 0;
    for (int twice = 0; twice < 2; twice++) {
        for (int i = 0; i < N; i++) {
            wrong += !cap_get(db, rd, i);
        }
    }
    const int64_t r0 = cap_resident(db, &s);
    CHECK_EQ(s.evicted, 0);
    CHECK(r0 > N * CAP_VALUE);
    const int64_t b1 = r0 / 10 * 9;
    CHECK(bergdb_set_cache_size_indicator(db, b1) == BERGDB_OK);
    const int64_t r1 = cap_resident(db, &s);
    CHECK(r1 <= b1);
    CHECK(s.evicted > 0);
    const int64_t b2 = r0 / 4;
    CHECK(bergdb_set_cache_size_indicator(db, b2) == BERGDB_OK);
    CHECK(cap_resident(db, &s) <= b2);
    uint64_t rnd = 5;
    int over = 0;
    for (int k = 0; k < 2 * N; k++) {
        wrong += !cap_get(db, rd, test_random_below(&rnd, N));
        over += cap_resident(db, &s) > b2;
    }
    CHECK_EQ(over, 0);
    const int64_t r2 = cap_resident(db, &s);
    CHECK(bergdb_set_cache_size_indicator(db, 10 * 1000 * 1000) == BERGDB_OK);
    CHECK_EQ(cap_resident(db, &s), r2);
    for (int i = 0; i < N; i++) {
        wrong += !cap_get(db, rd, i);
    }
    const int64_t r3 = cap_resident(db, &s);
    CHECK(r3 > b2);
    CHECK_EQ(wrong, 0);
    printf("  budget_lowered_and_raised_under_reads: resident bytes %lld; budget %lld: %lld; "
            "budget %lld: at most it; raised: %lld\n", (long long) r0, (long long) b1,
            (long long) r1, (long long) b2, (long long) r3);
    bergdb_read_free(rd);
    CHECK(bergdb_close(db) == BERGDB_OK);
    CHECK_EQ(m.live_total, 0);
    bu_remove_dir(dir);
}

/* CapacityTester.testLargePuts: values of 1.5 MiB, over the 1 MiB that a
 * read does not cache, with a budget of 4 MB, in a database in memory: after
 * every transaction the resident bytes are within the budget (the admission
 * takes the large values when their record is written), and every value
 * reads back right, also after a read of each (which does not keep it). */
TEST(budget_large_puts) {
    enum { N = 12, BIG = 3 * 1024 * 1024 / 2, BUDGET = 4 * 1000 * 1000 };
    struct bergdb_mem m = {0};
    struct bergdb_test_clock c = {0};
    struct bergdb_options o;
    bu_options(&o, &c, &m, BUDGET);
    char errbuf[BERGDB_ERRBUF_SIZE];
    bergdb_db *db;
    bergdb_test_clock_set(&c, 500);
    REQUIRE(bergdb_open(NULL, &o, &db, NULL, errbuf) == BERGDB_OK);
    uint8_t *v = malloc(BIG);
    REQUIRE(v != NULL);
    struct bergdb_stats s;
    int over = 0;
    for (int i = 0; i < N; i++) {
        bergdb_trans *t;
        REQUIRE(bergdb_trans_new(db, &t) == BERGDB_OK);
        uint8_t bkey[32];
        size_t kl = cap_key(i, bkey);
        cap_value(i, v, BIG);
        CHECK(bergdb_trans_put(t, bkey, kl, v, BIG) == BERGDB_OK);
        kl = cap_key(1000 + i, bkey);
        CHECK(bergdb_trans_put(t, bkey, kl, (const uint8_t *) "small", 5) == BERGDB_OK);
        bergdb_test_clock_set(&c, 1000 + i);
        CHECK(bergdb_execute(db, t, NULL) == BERGDB_OK);
        bergdb_trans_free(t);
        over += cap_resident(db, &s) > BUDGET;
    }
    CHECK_EQ(over, 0);
    bergdb_read *rd;
    REQUIRE(bergdb_read_new(db, &rd) == BERGDB_OK);
    int wrong = 0;
    for (int i = N - 1; i >= 0; i--) {
        uint8_t bkey[32];
        size_t kl = cap_key(i, bkey);
        struct bergdb_one one;
        cap_value(i, v, BIG);
        wrong += bergdb_get_one(db, rd, BERGDB_LATEST, bkey, kl, &one) != BERGDB_OK
                || one.value_len != BIG || memcmp(one.value, v, BIG) != 0;
        over += cap_resident(db, &s) > BUDGET;
    }
    CHECK_EQ(wrong, 0);
    CHECK_EQ(over, 0);
    bergdb_read_free(rd);
    free(v);
    CHECK(bergdb_close(db) == BERGDB_OK);
    CHECK_EQ(m.live_total, 0);
}

/* bergdb_stats' pinned bytes are of the resident bytes, those that must
 * stay (bergdb 022-06). Each object counted once (U2-13): a pinned node's
 * handle that its pinned parent holds was counted twice, so with the
 * smallest budget, where little but the pinned objects stays, the pinned
 * bytes exceeded the resident bytes (6,552 against 6,032 at node size 8).
 * And no written value (U1-5): a sweep lets the values of pinned key nodes
 * go, so after a committed transaction, whose values are all written, the
 * pinned bytes are at most the resident bytes less the values'; they
 * counted every value that a node of D held. */
TEST(budget_pinned_within_resident) {
    const int32_t sizes[] = {8, 14, 30};
    const int64_t budgets[] = {1, 4000, BERGDB_NO_EVICT};
    for (int n = 0; n < 3; n++) {
        for (int b = 0; b < 3; b++) {
            struct bergdb_mem m = {0};
            struct bergdb_test_clock c = {0};
            struct bergdb_options o;
            bu_options(&o, &c, &m, budgets[b]);
            o.max_node_size = sizes[n];
            o.startup_distance = 10;
            char errbuf[BERGDB_ERRBUF_SIZE];
            bergdb_db *db;
            bergdb_test_clock_set(&c, 500);
            REQUIRE(bergdb_open(NULL, &o, &db, NULL, errbuf) == BERGDB_OK);
            uint8_t v[40];
            memset(v, 1, sizeof v);
            int64_t bad = 0;
            struct bergdb_stats s;
            for (int i = 0; i < 3000; i += 10) {
                bergdb_test_clock_set(&c, 1000 + i);
                bergdb_trans *t;
                REQUIRE(bergdb_trans_new(db, &t) == BERGDB_OK);
                for (int j = i; j < i + 10; j++) {
                    char k[16];
                    int kn = snprintf(k, sizeof k, "k%07d", j);
                    CHECK(bergdb_trans_put(t, (const uint8_t *) k, (size_t) kn, v, sizeof v)
                            == BERGDB_OK);
                }
                CHECK(bergdb_execute(db, t, NULL) == BERGDB_OK);
                bergdb_trans_free(t);
                REQUIRE(bergdb_stats(db, &s) == BERGDB_OK);
                if (s.pinned_bytes > s.resident_bytes - m.live[BERGDB_MEM_VALUE]
                        || s.pinned_bytes <= 0) {
                    bad++;
                }
            }
            CHECK_EQ(bad, 0);
            if (bad != 0) {
                printf("  node size %d, budget %lld: resident %lld, values %lld, pinned "
                        "%lld\n", (int) sizes[n], (long long) budgets[b],
                        (long long) s.resident_bytes, (long long) m.live[BERGDB_MEM_VALUE],
                        (long long) s.pinned_bytes);
            }
            CHECK(bergdb_close(db) == BERGDB_OK);
            CHECK_EQ(m.live_total, 0);
        }
    }
}

const struct test budget_tests[] = {
    TEST_ENTRY(budget_invariance),
    TEST_ENTRY(budget_setter),
    TEST_ENTRY(budget_reads_without_writes),
    TEST_ENTRY(budget_lowered_and_raised_under_reads),
    TEST_ENTRY(budget_large_puts),
    TEST_ENTRY(budget_pinned_within_resident),
    TEST_END
};
