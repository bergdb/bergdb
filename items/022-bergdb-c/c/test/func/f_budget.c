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

const struct test budget_tests[] = {
    TEST_ENTRY(budget_invariance),
    TEST_ENTRY(budget_setter),
    TEST_END
};
