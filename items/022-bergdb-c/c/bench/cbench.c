/*
 * C's side of the benchmarks of bergdb 012-15: speed, memory and size of
 * the C clone against Java (JBench.java is Java's side, the same workloads
 * through Java's Db). Built by build.sh into build/release/bench-cbench
 * (and the test build). One caller, one thread.
 *
 * Usage:
 *   bench-cbench run DIR [NAME=VALUE ...]   the write and read workload
 *   bench-cbench start DIR [keys=N] [budget=BYTES]  times the open of a database
 *   bench-cbench mem DIR                    Props' MEM workload (006-02)
 *
 * run: a new database in DIR (empty or missing), node size 30, retain
 * forever, the test clock (+1/10,000 s a transaction) and the test id, so
 * that C and Java write the same bytes; no eviction (but in phase "low").
 * The phases, as StartupBench's make (007-05) for the first two:
 *   load     keys=N keys of 24 bytes ("/scale/key/" and 13 digits) in a
 *            random order (java.util.Random(1)'s shuffle), values of 8
 *            bytes, 1,000 puts a transaction
 *   batch    upd=N puts to random keys (java.util.Random(2)), 1,000 a
 *            transaction
 *   single   single=N transactions of one put to a random key
 *   syncone  syncs=N transactions of one put, each followed by a sync
 *            (BERGDB_SYNC_ORDINARY: F_FULLFSYNC)
 *   syncbatch  syncb=N transactions of 1,000 puts, each followed by a sync
 *   get      gets=N getOne of random keys, latest, rounds=R rounds
 *   hist     the same at the time just after the load (historical)
 *   many     scans=N getMany of 10,000 keys from a random key, R rounds
 *   close    the close (writes and forces the buffer)
 *   low      the open again with the budget low=BYTES (cache size
 *            indicator), then gets=N latest getOne, R rounds; then close
 * Also sd=BYTES (the startup distance, 50,000,000 by default), and
 * firstsync=1: one sync, timed alone (phase firstsync), before syncone.
 *
 * start: opens DIR (no eviction, or the budget), checks 2,000 random keys of keys=N
 * (10,000,000 by default; latest), and closes. mem: Props' Mem (006-02) in C: 1,000,000 keys "0" to "999999"
 * (ikeys), empty values, 100 puts a transaction, the test clock at 0 and
 * not moved, no eviction, in DIR (the stream in files, so that the
 * allocator's counts are the index's and not the stream's); the allocator's
 * live bytes after the puts minus before, per key, by kind.
 *
 * Output: lines "RESULT phase=P ..." with ops, seconds and ops a second;
 * "MEM ..." with the allocator's counts and the process's resident set.
 */
#include <inttypes.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <time.h>
#include <mach/mach.h>

#include "bergdb.h"

#define SEC BERGDB_UNITS_PER_SEC
#define TX 1000
#define SCAN 10000

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double) ts.tv_sec + (double) ts.tv_nsec / 1e9;
}

static void die(const char *what, int rc, bergdb_db *db) {
    fprintf(stderr, "FAILED: %s: %s %s\n", what, bergdb_errname(rc), db ? bergdb_errmsg(db) : "");
    exit(1);
}

/* java.util.Random, for the same keys as JBench's. */
struct jrand {
    int64_t seed;
};

static void jr_init(struct jrand *r, int64_t seed) {
    r->seed = (seed ^ INT64_C(0x5DEECE66D)) & ((INT64_C(1) << 48) - 1);
}

static int32_t jr_next31(struct jrand *r) {
    r->seed = (r->seed * INT64_C(0x5DEECE66D) + INT64_C(0xB)) & ((INT64_C(1) << 48) - 1);
    return (int32_t) (r->seed >> 17);
}

static int32_t jr_next_int(struct jrand *r, int32_t bound) {
    int32_t x = jr_next31(r);
    int32_t m = bound - 1;
    if ((bound & m) == 0) {
        return (int32_t) (((int64_t) bound * (int64_t) x) >> 31);
    }
    for (int32_t u = x; u - (x = u % bound) + m < 0; u = jr_next31(r)) {
    }
    return x;
}

/* StartupBench.key: 24 bytes, "/scale/key/" and k in 13 digits. */
static void key24(int32_t k, uint8_t *b) {
    memcpy(b, "/scale/key/", 11);
    int64_t v = k;
    for (int i = 23; i >= 11; i--) {
        b[i] = (uint8_t) ('0' + v % 10);
        v /= 10;
    }
}

/* StartupBench.value: k in the first four bytes, the version in the fifth. */
static void value8(int32_t k, int version, uint8_t *v) {
    memset(v, 0, 8);
    for (int i = 0; i < 4; i++) {
        v[i] = (uint8_t) ((uint32_t) k >> (24 - 8 * i));
    }
    v[4] = (uint8_t) version;
}

static int32_t value_key(const uint8_t *v) {
    return (int32_t) (((uint32_t) v[0] << 24) | ((uint32_t) v[1] << 16) | ((uint32_t) v[2] << 8) | v[3]);
}

/* The process's resident set now and at most, in bytes. */
static void rss(int64_t *cur, int64_t *max) {
    struct mach_task_basic_info info;
    mach_msg_type_number_t n = MACH_TASK_BASIC_INFO_COUNT;
    *cur = -1;
    if (task_info(mach_task_self(), MACH_TASK_BASIC_INFO, (task_info_t) &info, &n) == KERN_SUCCESS) {
        *cur = (int64_t) info.resident_size;
    }
    struct rusage ru;
    getrusage(RUSAGE_SELF, &ru);
    *max = (int64_t) ru.ru_maxrss;     /* bytes on macOS */
}

static void print_mem(const char *at, const struct bergdb_mem *m, bergdb_db *db, int64_t keys) {
    struct bergdb_stats st;
    int rc = bergdb_stats(db, &st);
    if (rc != BERGDB_OK) die("stats", rc, db);
    int64_t cur, max;
    rss(&cur, &max);
    printf("MEM at=%s keys=%" PRId64 " live=%" PRId64 " blocks=%" PRId64 " peak=%" PRId64 " index=%" PRId64
           " value=%" PRId64 " handle=%" PRId64 " table=%" PRId64 " buffer=%" PRId64
           " caller=%" PRId64 " state=%" PRId64 " resident=%" PRId64 " pinned=%" PRId64
           " evicted=%" PRId64 " rss=%" PRId64 " maxrss=%" PRId64 " stream=%" PRId64 "\n",
           at, keys, m->live_total, m->live_blocks, m->peak_total, m->live[BERGDB_MEM_INDEX],
           m->live[BERGDB_MEM_VALUE], m->live[BERGDB_MEM_HANDLE], m->live[BERGDB_MEM_TABLE],
           m->live[BERGDB_MEM_BUFFER], m->live[BERGDB_MEM_CALLER], m->live[BERGDB_MEM_STATE],
           st.resident_bytes, st.pinned_bytes, st.evicted, cur, max, st.stream_length);
    fflush(stdout);
}

static void result(const char *phase, int64_t ops, double sec, const char *extra) {
    printf("RESULT phase=%s ops=%" PRId64 " sec=%.6f per_sec=%.1f%s%s\n", phase, ops, sec,
           sec > 0 ? (double) ops / sec : 0.0, extra[0] ? " " : "", extra);
    fflush(stdout);
}

static int64_t stream_length(bergdb_db *db) {
    struct bergdb_stats st;
    int rc = bergdb_stats(db, &st);
    if (rc != BERGDB_OK) die("stats", rc, db);
    return st.stream_length;
}

/* ---- run ---- */

struct params {
    int32_t keys;
    int64_t upd, single, syncs, syncb, gets, scans, low;
    int32_t rounds, sd;
};

static int64_t param(int argc, char **argv, const char *name, int64_t def) {
    size_t n = strlen(name);
    for (int i = 3; i < argc; i++) {
        if (strncmp(argv[i], name, n) == 0 && argv[i][n] == '=') {
            return strtoll(argv[i] + n + 1, NULL, 10);
        }
    }
    return def;
}

struct ctx {
    bergdb_db *db;
    struct bergdb_test_clock clock;
    int64_t time;
    struct jrand upd_rnd;
};

/* One transaction of count puts: the keys from ord (if not NULL) or from
 * the random generator, the value's version v. */
static void put_trans(struct ctx *c, const int32_t *ord, int32_t keys, int64_t count, int version) {
    bergdb_trans *t;
    int rc = bergdb_trans_new(c->db, &t);
    if (rc != BERGDB_OK) die("trans_new", rc, c->db);
    uint8_t kb[24], vb[8];
    for (int64_t j = 0; j < count; j++) {
        int32_t k = ord != NULL ? ord[j] : jr_next_int(&c->upd_rnd, keys);
        key24(k, kb);
        value8(k, version, vb);
        rc = bergdb_trans_put(t, kb, 24, vb, 8);
        if (rc != BERGDB_OK) die("put", rc, c->db);
    }
    c->time += SEC / 10000;
    rc = bergdb_test_clock_set(&c->clock, c->time);
    if (rc != BERGDB_OK) die("clock", rc, c->db);
    struct bergdb_executed ex;
    rc = bergdb_execute(c->db, t, &ex);
    if (rc != BERGDB_OK) die("execute", rc, c->db);
    bergdb_trans_free(t);
}

static void get_round(bergdb_db *db, const char *phase, int32_t keys, int64_t n, int32_t rounds,
        int64_t lookup, int version) {
    bergdb_read *rd;
    int rc = bergdb_read_new(db, &rd);
    if (rc != BERGDB_OK) die("read_new", rc, db);
    uint8_t kb[24];
    for (int32_t r = 0; r < rounds; r++) {
        struct jrand rnd;
        jr_init(&rnd, 3 + r);
        int64_t found = 0, bad = 0;
        double a = now();
        for (int64_t i = 0; i < n; i++) {
            int32_t k = jr_next_int(&rnd, keys);
            key24(k, kb);
            struct bergdb_one one;
            rc = bergdb_get_one(db, rd, lookup, kb, 24, &one);
            if (rc != BERGDB_OK) die("get_one", rc, db);
            if (one.value != NULL && one.value_len == 8) {
                found++;
                if (value_key(one.value) != k || (version >= 0 && one.value[4] != version)) bad++;
            }
        }
        double sec = now() - a;
        char extra[100];
        snprintf(extra, sizeof extra, "round=%d found=%" PRId64 " bad=%" PRId64, r, found, bad);
        result(phase, n, sec, extra);
        if (bad != 0) {
            fprintf(stderr, "FAILED: %s: %" PRId64 " wrong values\n", phase, bad);
            exit(1);
        }
    }
    bergdb_read_free(rd);
}

static void scans(bergdb_db *db, int32_t keys, int64_t n, int32_t rounds) {
    bergdb_read *rd;
    int rc = bergdb_read_new(db, &rd);
    if (rc != BERGDB_OK) die("read_new", rc, db);
    uint8_t kb[24];
    for (int32_t r = 0; r < rounds; r++) {
        struct jrand rnd;
        jr_init(&rnd, 5 + r);
        int64_t total = 0;
        double a = now();
        for (int64_t i = 0; i < n; i++) {
            int32_t k = jr_next_int(&rnd, keys);
            key24(k, kb);
            struct bergdb_range range;
            bergdb_range_init(&range);
            range.start_key = kb;
            range.start_key_len = 24;
            range.max_count = SCAN;
            struct bergdb_many many;
            rc = bergdb_get_many(db, rd, &range, &many);
            if (rc != BERGDB_OK) die("get_many", rc, db);
            total += (int64_t) many.count;
        }
        double sec = now() - a;
        char extra[100];
        snprintf(extra, sizeof extra, "round=%d scans=%" PRId64, r, n);
        result("many", total, sec, extra);
    }
    bergdb_read_free(rd);
}

static int run(int argc, char **argv) {
    const char *dir = argv[2];
    struct params p;
    p.keys = (int32_t) param(argc, argv, "keys", 1000000);
    p.upd = param(argc, argv, "upd", 0);
    p.single = param(argc, argv, "single", 0);
    p.syncs = param(argc, argv, "syncs", 0);
    p.syncb = param(argc, argv, "syncb", 0);
    p.gets = param(argc, argv, "gets", 0);
    p.scans = param(argc, argv, "scans", 0);
    p.low = param(argc, argv, "low", 0);
    p.rounds = (int32_t) param(argc, argv, "rounds", 3);
    p.sd = (int32_t) param(argc, argv, "sd", 50000000);
    printf("RUN lang=c keys=%d upd=%" PRId64 " single=%" PRId64 " syncs=%" PRId64 " syncb=%" PRId64
           " gets=%" PRId64 " scans=%" PRId64 " low=%" PRId64 " rounds=%d sd=%d\n", p.keys, p.upd,
           p.single, p.syncs, p.syncb, p.gets, p.scans, p.low, p.rounds, p.sd);

    static struct ctx c;   /* static: a bench program, not the library */
    struct bergdb_mem mem;
    memset(&mem, 0, sizeof mem);
    struct bergdb_options opt;
    bergdb_options_init(&opt);
    opt.max_node_size = 30;
    opt.startup_distance = p.sd;
    opt.cache_size_indicator = BERGDB_NO_EVICT;
    c.clock.time = 0;
    c.time = SEC;
    bergdb_test_clock_set(&c.clock, c.time);
    opt.clock = bergdb_test_clock_time;
    opt.clock_ctx = &c.clock;
    memcpy(opt.id, bergdb_test_id, BERGDB_ID_SIZE);
    opt.mem = &mem;
    char err[BERGDB_ERRBUF_SIZE];
    double a = now();
    int rc = bergdb_open(dir, &opt, &c.db, NULL, err);
    if (rc != BERGDB_OK) {
        fprintf(stderr, "FAILED: open: %s\n", err);
        return 1;
    }
    result("create", 1, now() - a, "");
    print_mem("empty", &mem, c.db, 0);
    char extra[200];

    /* load */
    int32_t *ord = malloc(sizeof(int32_t) * (size_t) p.keys);
    if (ord == NULL) return 1;
    for (int32_t i = 0; i < p.keys; i++) ord[i] = i;
    struct jrand rnd;
    jr_init(&rnd, 1);
    for (int32_t i = p.keys - 1; i > 0; i--) {
        int32_t j = jr_next_int(&rnd, i + 1);
        int32_t x = ord[i];
        ord[i] = ord[j];
        ord[j] = x;
    }
    int64_t len0 = stream_length(c.db);
    a = now();
    int64_t trans = 0;
    for (int32_t i = 0; i < p.keys; i += TX) {
        int32_t e = p.keys - i < TX ? p.keys : i + TX;
        put_trans(&c, ord + i, p.keys, e - i, 0);
        trans++;
    }
    double sec = now() - a;
    free(ord);
    int64_t len1 = stream_length(c.db);
    snprintf(extra, sizeof extra, "trans=%" PRId64 " trans_per_sec=%.1f bytes=%" PRId64
             " bytes_per_put=%.2f stream=%" PRId64, trans, (double) trans / sec, len1 - len0,
             (double) (len1 - len0) / p.keys, len1);
    result("load", p.keys, sec, extra);
    int64_t t_load = c.time;
    print_mem("load", &mem, c.db, p.keys);

    jr_init(&c.upd_rnd, 2);
    /* batch updates */
    if (p.upd > 0) {
        len0 = len1;
        a = now();
        trans = 0;
        for (int64_t i = 0; i < p.upd; i += TX) {
            int64_t e = p.upd - i < TX ? p.upd : i + TX;
            put_trans(&c, NULL, p.keys, e - i, 1);
            trans++;
        }
        sec = now() - a;
        len1 = stream_length(c.db);
        snprintf(extra, sizeof extra, "trans=%" PRId64 " trans_per_sec=%.1f bytes=%" PRId64
                 " bytes_per_put=%.2f stream=%" PRId64, trans, (double) trans / sec, len1 - len0,
                 (double) (len1 - len0) / (double) p.upd, len1);
        result("batch", p.upd, sec, extra);
    }
    /* single puts */
    if (p.single > 0) {
        len0 = len1;
        a = now();
        for (int64_t i = 0; i < p.single; i++) put_trans(&c, NULL, p.keys, 1, 2);
        sec = now() - a;
        len1 = stream_length(c.db);
        snprintf(extra, sizeof extra, "trans=%" PRId64 " bytes=%" PRId64 " bytes_per_put=%.2f stream=%" PRId64,
                 p.single, len1 - len0, (double) (len1 - len0) / (double) p.single, len1);
        result("single", p.single, sec, extra);
    }
    /* with firstsync=1: one sync first, timed alone: the first force of a
     * stream written without one */
    if (param(argc, argv, "firstsync", 0) > 0) {
        a = now();
        rc = bergdb_sync(c.db, 0, BERGDB_SYNC_ORDINARY);
        if (rc != BERGDB_OK) die("sync", rc, c.db);
        result("firstsync", 1, now() - a, "");
    }
    /* single puts, each synced */
    if (p.syncs > 0) {
        len0 = len1;
        a = now();
        for (int64_t i = 0; i < p.syncs; i++) {
            put_trans(&c, NULL, p.keys, 1, 3);
            rc = bergdb_sync(c.db, 0, BERGDB_SYNC_ORDINARY);
            if (rc != BERGDB_OK) die("sync", rc, c.db);
        }
        sec = now() - a;
        len1 = stream_length(c.db);
        snprintf(extra, sizeof extra, "trans=%" PRId64 " bytes=%" PRId64 " bytes_per_put=%.2f stream=%" PRId64,
                 p.syncs, len1 - len0, (double) (len1 - len0) / (double) p.syncs, len1);
        result("syncone", p.syncs, sec, extra);
    }
    /* batches, each synced */
    if (p.syncb > 0) {
        len0 = len1;
        a = now();
        for (int64_t i = 0; i < p.syncb; i++) {
            put_trans(&c, NULL, p.keys, TX, 4);
            rc = bergdb_sync(c.db, 0, BERGDB_SYNC_ORDINARY);
            if (rc != BERGDB_OK) die("sync", rc, c.db);
        }
        sec = now() - a;
        len1 = stream_length(c.db);
        snprintf(extra, sizeof extra, "trans=%" PRId64 " puts=%" PRId64 " bytes=%" PRId64
                 " bytes_per_put=%.2f stream=%" PRId64, p.syncb, p.syncb * TX, len1 - len0,
                 (double) (len1 - len0) / (double) (p.syncb * TX), len1);
        result("syncbatch", p.syncb, sec, extra);
    }
    print_mem("writes", &mem, c.db, p.keys);

    /* reads, in memory */
    if (p.gets > 0) {
        get_round(c.db, "get", p.keys, p.gets, p.rounds, BERGDB_LATEST, -1);
        get_round(c.db, "hist", p.keys, p.gets, p.rounds, t_load, 0);
    }
    if (p.scans > 0) scans(c.db, p.keys, p.scans, p.rounds);
    print_mem("reads", &mem, c.db, p.keys);

    a = now();
    rc = bergdb_close(c.db);
    if (rc != BERGDB_OK) die("close", rc, NULL);
    snprintf(extra, sizeof extra, "stream=%" PRId64, len1);
    result("close", 1, now() - a, extra);

    /* reads with a small budget, after an open */
    if (p.low > 0 && dir != NULL) {
        opt.cache_size_indicator = p.low;
        a = now();
        rc = bergdb_open(dir, &opt, &c.db, NULL, err);
        if (rc != BERGDB_OK) {
            fprintf(stderr, "FAILED: open low: %s\n", err);
            return 1;
        }
        snprintf(extra, sizeof extra, "budget=%" PRId64, p.low);
        result("lowopen", 1, now() - a, extra);
        print_mem("lowopen", &mem, c.db, p.keys);
        get_round(c.db, "lowget", p.keys, p.gets, p.rounds, BERGDB_LATEST, -1);
        print_mem("lowget", &mem, c.db, p.keys);
        rc = bergdb_close(c.db);
        if (rc != BERGDB_OK) die("close", rc, NULL);
    }
    printf("DONE lang=c\n");
    return 0;
}

/* ---- start ---- */

static int start(int argc, char **argv) {
    const char *dir = argv[2];
    struct bergdb_mem mem;
    memset(&mem, 0, sizeof mem);
    struct bergdb_options opt;
    bergdb_options_init(&opt);
    int64_t budget = param(argc, argv, "budget", 0);
    opt.cache_size_indicator = budget > 0 ? budget : BERGDB_NO_EVICT;
    opt.mem = &mem;
    /* The test clock at a time after the database's: a start needs a time
     * at or after the last transaction's (the make's clock went to at most
     * a few hours of test time). */
    struct bergdb_test_clock clock = {0};
    bergdb_test_clock_set(&clock, INT64_C(1000000) * SEC);
    opt.clock = bergdb_test_clock_time;
    opt.clock_ctx = &clock;
    char err[BERGDB_ERRBUF_SIZE];
    bergdb_db *db;
    struct bergdb_start_info info;
    double a = now();
    int rc = bergdb_open(dir, &opt, &db, &info, err);
    double sec = now() - a;
    if (rc != BERGDB_OK) {
        fprintf(stderr, "FAILED: open: %s\n", err);
        return 1;
    }
    struct bergdb_stats st;
    bergdb_stats(db, &st);
    char extra[300];
    snprintf(extra, sizeof extra, "trans=%d start_pos=%" PRId64 " stream=%" PRId64
             " section=%" PRId64 " sd=%d", info.trans_count, info.start_pos, st.stream_length,
             st.stream_length - info.start_pos, st.startup_distance);
    result("start", 1, sec, extra);
    print_mem("start", &mem, db, 0);
    /* 2,000 random keys of the 10M (or of keys=N), latest */
    bergdb_read *rd;
    rc = bergdb_read_new(db, &rd);
    if (rc != BERGDB_OK) die("read_new", rc, db);
    struct jrand rnd;
    jr_init(&rnd, 7);
    int32_t keys = (int32_t) param(argc, argv, "keys", 10000000);
    int64_t found = 0;
    uint8_t kb[24];
    for (int i = 0; i < 2000; i++) {
        int32_t k = jr_next_int(&rnd, keys);
        key24(k, kb);
        struct bergdb_one one;
        rc = bergdb_get_one(db, rd, BERGDB_LATEST, kb, 24, &one);
        if (rc != BERGDB_OK) die("get_one", rc, db);
        if (one.value != NULL && one.value_len == 8 && value_key(one.value) == k) found++;
    }
    bergdb_read_free(rd);
    printf("CHECK found=%" PRId64 " of 2000\n", found);
    rc = bergdb_close(db);
    if (rc != BERGDB_OK) die("close", rc, NULL);
    return found == 2000 ? 0 : 1;
}

/* ---- mem: Props' Mem ---- */

static int memrun(const char *dir) {
    struct bergdb_mem mem;
    memset(&mem, 0, sizeof mem);
    struct bergdb_options opt;
    bergdb_options_init(&opt);
    opt.cache_size_indicator = BERGDB_NO_EVICT;
    struct bergdb_test_clock clock = {0};
    opt.clock = bergdb_test_clock_time;
    opt.clock_ctx = &clock;
    memcpy(opt.id, bergdb_test_id, BERGDB_ID_SIZE);
    opt.mem = &mem;
    char err[BERGDB_ERRBUF_SIZE];
    bergdb_db *db;
    int rc = bergdb_open(dir, &opt, &db, NULL, err);
    if (rc != BERGDB_OK) {
        fprintf(stderr, "FAILED: open: %s\n", err);
        return 1;
    }
    int n = 1000 * 1000, batch = 100;
    struct bergdb_mem before = mem;
    int64_t rss0, max0;
    rss(&rss0, &max0);
    print_mem("empty", &mem, db, 0);
    uint8_t ik[16], bk[16];
    uint8_t empty[1] = {0};
    for (int i = 0; i < n / batch; i++) {
        bergdb_trans *t;
        rc = bergdb_trans_new(db, &t);
        if (rc != BERGDB_OK) die("trans_new", rc, db);
        for (int j = 0; j < batch; j++) {
            int len = snprintf((char *) ik, sizeof ik, "%d", i * batch + j);
            bergdb_ikey_to_bkey(ik, (size_t) len, bk);
            rc = bergdb_trans_put(t, bk, (size_t) len, empty, 0);
            if (rc != BERGDB_OK) die("put", rc, db);
        }
        rc = bergdb_execute(db, t, NULL);
        if (rc != BERGDB_OK) die("execute", rc, db);
        bergdb_trans_free(t);
    }
    print_mem("full", &mem, db, n);
    int64_t rss1, max1;
    rss(&rss1, &max1);
    printf("MEMKV live_per_kv=%.1f index=%.1f value=%.1f handle=%.1f table=%.1f buffer=%.1f"
           " caller=%.1f state=%.1f rss_per_kv=%.1f\n",
           (double) (mem.live_total - before.live_total) / n,
           (double) (mem.live[BERGDB_MEM_INDEX] - before.live[BERGDB_MEM_INDEX]) / n,
           (double) (mem.live[BERGDB_MEM_VALUE] - before.live[BERGDB_MEM_VALUE]) / n,
           (double) (mem.live[BERGDB_MEM_HANDLE] - before.live[BERGDB_MEM_HANDLE]) / n,
           (double) (mem.live[BERGDB_MEM_TABLE] - before.live[BERGDB_MEM_TABLE]) / n,
           (double) (mem.live[BERGDB_MEM_BUFFER] - before.live[BERGDB_MEM_BUFFER]) / n,
           (double) (mem.live[BERGDB_MEM_CALLER] - before.live[BERGDB_MEM_CALLER]) / n,
           (double) (mem.live[BERGDB_MEM_STATE] - before.live[BERGDB_MEM_STATE]) / n,
           (double) (rss1 - rss0) / n);
    rc = bergdb_close(db);
    if (rc != BERGDB_OK) die("close", rc, NULL);
    return 0;
}

int main(int argc, char **argv) {
    if (argc >= 3 && strcmp(argv[1], "run") == 0) return run(argc, argv);
    if (argc >= 3 && strcmp(argv[1], "start") == 0) return start(argc, argv);
    if (argc >= 3 && strcmp(argv[1], "mem") == 0) return memrun(argv[2]);
    fprintf(stderr, "usage: bench-cbench run DIR [NAME=VALUE ...] | start DIR [keys=N] | mem DIR\n");
    return 2;
}
