/* Functional tests of the start (bergdb 012-10; 012-01, 6.4; 10-startup.md,
 * section 4), through include/bergdb.h only: a restart after every
 * transaction writes the bytes of the run without restarts (Java's
 * RestartInvariance), the reads the same; a crash cut at many positions of
 * a small stream (C alone, against C's own states): each copy started (its
 * recovery), read as the transactions that were whole, written after, and
 * started again; the refusals of a start (another node size, an incomplete
 * creation, bad magic bytes), which write nothing. Each test ends with the
 * allocator's count 0. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>
#include "test.h"
#include "bergdb.h"

static void st_temp_dir(char *out, size_t cap) {
    const char *t = getenv("TMPDIR");
    snprintf(out, cap, "%s/bergdb-start-XXXXXX", t != NULL ? t : "/tmp");
    if (mkdtemp(out) == NULL) {
        out[0] = '\0';
    }
}

static void st_remove_dir(const char *dir) {
    char cmd[1200];
    snprintf(cmd, sizeof cmd, "rm -rf '%s'", dir);
    if (system(cmd) != 0) {
        printf("could not remove %s\n", dir);
    }
}

/* The whole first file of a directory (the test streams are smaller than
 * 200 kB), into a new buffer; *len its length. */
static uint8_t *read_file(const char *dir, const char *name, int64_t *len) {
    char path[1200];
    snprintf(path, sizeof path, "%s/%s", dir, name);
    FILE *f = fopen(path, "rb");
    if (f == NULL) {
        *len = -1;
        return NULL;
    }
    fseek(f, 0, SEEK_END);
    long n = ftell(f);
    fseek(f, 0, SEEK_SET);
    uint8_t *b = malloc(n > 0 ? (size_t) n : 1);
    *len = (int64_t) fread(b, 1, (size_t) n, f);
    fclose(f);
    return b;
}

static void write_file(const char *dir, const char *name, const uint8_t *b, int64_t len) {
    char path[1200];
    snprintf(path, sizeof path, "%s/%s", dir, name);
    FILE *f = fopen(path, "wb");
    if (f != NULL) {
        if (len > 0) {
            fwrite(b, 1, (size_t) len, f);
        }
        fclose(f);
    }
}

#define FIRST_FILE "00000000000000.bergdb"

static void st_options(struct bergdb_options *o, struct bergdb_test_clock *clock,
        struct bergdb_mem *m, int32_t maxNode) {
    bergdb_options_init(o);
    o->clock = bergdb_test_clock_time;
    o->clock_ctx = clock;
    memcpy(o->id, bergdb_test_id, BERGDB_ID_SIZE);
    o->max_node_size = maxNode;
    o->startup_distance = 300;      /* small: the take and index writes come often */
    o->mem = m;
}

/* Transaction i of the tests' workload: a few puts and a delete of keys
 * drawn by a small generator, at time 1000 + 10 i. */
static int trans_i(bergdb_db *db, struct bergdb_test_clock *clock, int i,
        struct bergdb_executed *ex) {
    bergdb_test_clock_set(clock, 1000 + 10 * (int64_t) i);
    bergdb_trans *t;
    int rc = bergdb_trans_new(db, &t);
    if (rc != BERGDB_OK) {
        return rc;
    }
    uint32_t x = 2463534242u ^ (uint32_t) (i * 7919);
    for (int j = 0; j < 4 && rc == BERGDB_OK; j++) {
        x ^= x << 13;
        x ^= x >> 17;
        x ^= x << 5;
        char ikey[32], value[48];
        uint8_t bkey[32];
        snprintf(ikey, sizeof ikey, "/k/%u", x % 60);
        size_t kl = strlen(ikey);
        bergdb_ikey_to_bkey((const uint8_t *) ikey, kl, bkey);
        if (j == 3 && i % 3 == 0) {
            rc = bergdb_trans_delete(t, bkey, kl);
        } else {
            snprintf(value, sizeof value, "value %d of %d, %u", j, i, x);
            rc = bergdb_trans_put(t, bkey, kl, (const uint8_t *) value, strlen(value));
        }
    }
    if (rc == BERGDB_OK) {
        rc = bergdb_execute(db, t, ex);
    }
    bergdb_trans_free(t);
    return rc;
}

/* A digest of the latest state: the pairs' keys and values, FNV-1a. */
static uint64_t state_digest(bergdb_db *db, int64_t *count) {
    bergdb_read *rd;
    uint64_t h = 1469598103934665603u;
    *count = -1;
    if (bergdb_read_new(db, &rd) != BERGDB_OK) {
        return 0;
    }
    struct bergdb_range r;
    struct bergdb_many many;
    bergdb_range_init(&r);
    if (bergdb_get_many(db, rd, &r, &many) == BERGDB_OK) {
        *count = (int64_t) many.count;
        for (size_t i = 0; i < many.count; i++) {
            const struct bergdb_kvt *kv = &many.kvts[i];
            for (size_t j = 0; j < kv->key_len; j++) {
                h = (h ^ kv->key[j]) * 1099511628211u;
            }
            h = (h ^ 0xff) * 1099511628211u;
            for (size_t j = 0; j < kv->value_len; j++) {
                h = (h ^ kv->value[j]) * 1099511628211u;
            }
            h = (h ^ 0xfe) * 1099511628211u;
        }
    }
    bergdb_read_free(rd);
    return h;
}

/* A restart after every transaction: the files of the run without
 * restarts, byte for byte, and the same state. */
TEST(start_restart_every_transaction) {
    enum { N = 40 };
    char a[1024], b[1024];
    st_temp_dir(a, sizeof a);
    st_temp_dir(b, sizeof b);
    REQUIRE(a[0] != '\0' && b[0] != '\0');
    struct bergdb_mem m = {0};
    struct bergdb_test_clock ca = {0}, cb = {0};
    struct bergdb_options oa, ob;
    st_options(&oa, &ca, &m, 8);
    st_options(&ob, &cb, &m, 8);
    struct bergdb_executed ex;
    char errbuf[BERGDB_ERRBUF_SIZE];
    bergdb_db *db;

    bergdb_test_clock_set(&ca, 500);
    REQUIRE(bergdb_open(a, &oa, &db, NULL, errbuf) == BERGDB_OK);
    for (int i = 0; i < N; i++) {
        CHECK_EQ(trans_i(db, &ca, i, &ex), BERGDB_OK);
    }
    int64_t ca_count;
    uint64_t da = state_digest(db, &ca_count);
    CHECK(bergdb_close(db) == BERGDB_OK);

    bergdb_test_clock_set(&cb, 500);
    for (int i = 0; i < N; i++) {
        struct bergdb_start_info info;
        REQUIRE(bergdb_open(b, &ob, &db, &info, errbuf) == BERGDB_OK);
        CHECK_EQ(info.trans_count >= 1, true);
        CHECK_EQ(trans_i(db, &cb, i, &ex), BERGDB_OK);
        CHECK(bergdb_close(db) == BERGDB_OK);
    }
    REQUIRE(bergdb_open(b, &ob, &db, NULL, errbuf) == BERGDB_OK);
    int64_t cb_count;
    uint64_t dbg = state_digest(db, &cb_count);
    CHECK(bergdb_close(db) == BERGDB_OK);
    CHECK_EQ(cb_count, ca_count);
    CHECK(dbg == da);
    CHECK_EQ(m.live_total, 0);

    int64_t la, lb;
    uint8_t *fa = read_file(a, FIRST_FILE, &la);
    uint8_t *fb = read_file(b, FIRST_FILE, &lb);
    CHECK_EQ(la, lb);
    CHECK(la > 0 && la == lb && memcmp(fa, fb, (size_t) la) == 0);
    free(fa);
    free(fb);
    st_remove_dir(a);
    st_remove_dir(b);
}

/* A crash cut at many positions of a small stream: each copy starts (its
 * recovery), reads as the transactions that were whole, takes a
 * transaction after, and starts again with it. */
TEST(start_crash_cuts) {
    enum { N = 40 };
    char src[1024];
    st_temp_dir(src, sizeof src);
    REQUIRE(src[0] != '\0');
    struct bergdb_mem m = {0};
    struct bergdb_test_clock clock = {0};
    struct bergdb_options o;
    st_options(&o, &clock, &m, 8);
    char errbuf[BERGDB_ERRBUF_SIZE];
    bergdb_db *db;
    struct bergdb_executed ex;
    int64_t lastPos[N + 1];
    uint64_t expect[N + 1];
    int64_t expectCount[N + 1];

    bergdb_test_clock_set(&clock, 500);
    REQUIRE(bergdb_open(src, &o, &db, NULL, errbuf) == BERGDB_OK);
    lastPos[0] = 263;
    expect[0] = state_digest(db, &expectCount[0]);
    for (int i = 0; i < N; i++) {
        REQUIRE(trans_i(db, &clock, i, &ex) == BERGDB_OK);
        lastPos[i + 1] = ex.last_pos;
        expect[i + 1] = state_digest(db, &expectCount[i + 1]);
    }
    CHECK(bergdb_close(db) == BERGDB_OK);
    int64_t len;
    uint8_t *bytes = read_file(src, FIRST_FILE, &len);
    REQUIRE(bytes != NULL && len == lastPos[N] + 1);
    int64_t lockLen;
    uint8_t *lock = read_file(src, "bergdb.lock", &lockLen);

    /* The cuts: in four records, at each part of the record (the size field
     * cut after 1 to 4 bytes, the header, the middle, the last byte left
     * out, the record whole), and every 251st position elsewhere. Each start
     * forces at its close (F_FULLFSYNC), so the cuts are a sample. */
    int cuts = 0;
    for (int64_t cut = 264; cut <= len; cut++) {
        bool chosen = cut % 251 == 0;
        const int recs[] = { 1, 6, N / 2, N };
        for (size_t q = 0; q < sizeof recs / sizeof recs[0]; q++) {
            int64_t start = lastPos[recs[q] - 1] + 1, end = lastPos[recs[q]] + 1;
            int64_t off = cut - start;
            if (off == 1 || off == 2 || off == 3 || off == 4 || off == 5 || off == 17
                    || off == 31 || cut == start + (end - start) / 2 || cut == end - 1
                    || cut == end) {
                chosen = true;
            }
        }
        if (!chosen) {
            continue;
        }
        char dir[1024];
        st_temp_dir(dir, sizeof dir);
        REQUIRE(dir[0] != '\0');
        write_file(dir, FIRST_FILE, bytes, cut);
        write_file(dir, "bergdb.lock", lock, lockLen);
        struct bergdb_test_clock c2 = clock;
        struct bergdb_options o2;
        st_options(&o2, &c2, &m, 8);
        int whole = 0;
        for (int i = 0; i <= N; i++) {
            if (lastPos[i] < cut) {
                whole = i;
            }
        }
        REQUIRE(bergdb_open(dir, &o2, &db, NULL, errbuf) == BERGDB_OK);
        int64_t count;
        CHECK(state_digest(db, &count) == expect[whole]);
        CHECK_EQ(count, expectCount[whole]);
        /* a transaction after the crash, then a start again */
        CHECK_EQ(trans_i(db, &c2, N + 5, &ex), BERGDB_OK);
        int64_t countAfter;
        uint64_t after = state_digest(db, &countAfter);
        CHECK(bergdb_close(db) == BERGDB_OK);
        REQUIRE(bergdb_open(dir, &o2, &db, NULL, errbuf) == BERGDB_OK);
        int64_t count2;
        CHECK(state_digest(db, &count2) == after);
        CHECK_EQ(count2, countAfter);
        CHECK(bergdb_close(db) == BERGDB_OK);
        CHECK_EQ(m.live_total, 0);
        st_remove_dir(dir);
        cuts++;
    }
    CHECK(cuts > 40);
    free(bytes);
    free(lock);
    st_remove_dir(src);
}

/* The refusals of a start: nothing is written. */
TEST(start_refusals) {
    char src[1024];
    st_temp_dir(src, sizeof src);
    REQUIRE(src[0] != '\0');
    struct bergdb_mem m = {0};
    struct bergdb_test_clock clock = {0};
    struct bergdb_options o;
    st_options(&o, &clock, &m, 8);
    char errbuf[BERGDB_ERRBUF_SIZE];
    bergdb_db *db;
    struct bergdb_executed ex;
    bergdb_test_clock_set(&clock, 500);
    REQUIRE(bergdb_open(src, &o, &db, NULL, errbuf) == BERGDB_OK);
    for (int i = 0; i < 10; i++) {
        REQUIRE(trans_i(db, &clock, i, &ex) == BERGDB_OK);
    }
    CHECK(bergdb_close(db) == BERGDB_OK);
    int64_t len, lockLen;
    uint8_t *bytes = read_file(src, FIRST_FILE, &len);
    uint8_t *lock = read_file(src, "bergdb.lock", &lockLen);
    REQUIRE(bytes != NULL && lock != NULL);

    struct {
        const char *what;
        int64_t cut;            /* the bytes kept */
        int flip;               /* a byte flipped, or -1 */
        int32_t maxNode;
        int code;
        const char *name;       /* the start of the error's text: Java's exception */
    } cases[] = {
        { "another node size", -1, -1, 14, BERGDB_FORMAT, "StreamFormatException" },
        { "an incomplete creation", 200, -1, 8, BERGDB_NOT_CREATED,
            "DatabaseNotCreatedException" },
        { "a creation's block cut", 60, -1, 8, BERGDB_NOT_CREATED,
            "DatabaseNotCreatedException" },
        { "bad magic bytes", -1, 0, 8, BERGDB_FORMAT,       /* BadCryptoKey before 020-28 */
            "StreamFormatException: Invalid magic bytes in stream: the stream is not a" },
        { "another version", -1, 4, 8, BERGDB_FORMAT, "VersioningStreamException" },
    };
    for (size_t c = 0; c < sizeof cases / sizeof cases[0]; c++) {
        char dir[1024];
        st_temp_dir(dir, sizeof dir);
        REQUIRE(dir[0] != '\0');
        int64_t n = cases[c].cut < 0 ? len : cases[c].cut;
        uint8_t *copy = malloc((size_t) len);
        memcpy(copy, bytes, (size_t) len);
        if (cases[c].flip >= 0) {
            copy[cases[c].flip] ^= 1;
        }
        write_file(dir, FIRST_FILE, copy, n);
        write_file(dir, "bergdb.lock", lock, lockLen);
        struct bergdb_options o2;
        st_options(&o2, &clock, &m, cases[c].maxNode);
        int rc = bergdb_open(dir, &o2, &db, NULL, errbuf);
        CHECK_EQ(rc, cases[c].code);
        CHECK(db == NULL);
        CHECK(strncmp(errbuf, cases[c].name, strlen(cases[c].name)) == 0);
        if (rc != cases[c].code || strncmp(errbuf, cases[c].name, strlen(cases[c].name)) != 0) {
            printf("  %s: %d, %s\n", cases[c].what, rc, errbuf);
        }
        int64_t after;
        uint8_t *now = read_file(dir, FIRST_FILE, &after);
        CHECK_EQ(after, n);                         /* nothing written */
        CHECK(now != NULL && memcmp(now, copy, (size_t) n) == 0);
        free(now);
        free(copy);
        CHECK_EQ(m.live_total, 0);
        st_remove_dir(dir);
    }
    free(bytes);
    free(lock);
    st_remove_dir(src);
}

const struct test start_tests[] = {
    TEST_ENTRY(start_restart_every_transaction),
    TEST_ENTRY(start_crash_cuts),
    TEST_ENTRY(start_refusals),
    TEST_END
};
