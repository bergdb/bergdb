/* Reclaim, Level 3 (bergdb 012-11, part 1): the row's and the table's texts
 * (Java's IterationInfo tests, and the direct writer against StringMap's
 * HashMap order), the settings, and Reclaim.Tester's tests that need no
 * restart, ported on a memory stream (CutStream's exact cut): Java's bytes
 * from the decided cut with the default step reserve and with one that
 * splits the steps (reclaim.txt, Vectors.java); every live
 * value at or after pCut when an iteration is done, pCut the pStart of the
 * iteration before, values spared, iterations a quarter of the retention
 * apart and twice the startup distance apart (also after
 * setStartupDistance), lookups from the first available time equal to a
 * model and refused before it (getOne, getMany, getTrans of a removed
 * record), the step reserve splitting steps, and the allocation failures in
 * turn over iterations, steps, a table store and a cut. Since 022-05:
 * ReclaimRetentionTester's tests (the retain duration changed while the
 * database runs and across restarts) and Reclaim.Tester's with restarts
 * and a crash, in directories. */
#define _DARWIN_C_SOURCE        /* mkdtemp */
#include <dirent.h>
#include <errno.h>
#include <math.h>
#include <stdlib.h>
#include <sys/stat.h>
#include <unistd.h>
#include "test.h"
#include "../../tools/sha256.h"
#include "bergdb.h"
#include "db.h"
#include "jsem.h"
#include "keys.h"
#include "nstream.h"
#include "nwrite.h"
#include "reclaim.h"
#include "strmap.h"
#include "trans.h"

/* ======== The texts ======== */

/* The row through StringMap, put in IterationInfo.serialize's order. */
static char *row_by_strmap(struct mem *m, const struct rc_row *r, size_t *n) {
    struct sm sm;
    struct err e;
    char b[64];
    sm_init(&sm, m);
#define PUTL(k, v) snprintf(b, sizeof b, "%lld", (long long) (v)); sm_put(&sm, k, b, &e)
    PUTL("pStart", r->pStart);
    PUTL("pCut", r->pCut);
    PUTL("tStart", r->tStart);
    PUTL("tEnd", r->tEnd);
    PUTL("kvCount", r->kvCount);
    if (r->lastKeyNull) {
        sm_put(&sm, "lastKey", "null", &e);
    } else {
        char k[1024];
        size_t o = 0;
        k[0] = '\0';
        for (int32_t i = 0; i < r->lastKey_n; i++) {
            o += (size_t) snprintf(k + o, sizeof k - o, "%lld ", (long long) r->lastKey[i]);
        }
        if (o > 0) {
            k[o - 1] = '\0';        /* trim() */
        }
        sm_put(&sm, "lastKey", k, &e);
    }
    sm_put(&sm, "done", r->done ? "true" : "false", &e);
    sm_put(&sm, "cut", r->cut ? "true" : "false", &e);
    PUTL("rewritten", r->rewritten);
    PUTL("pEnd", r->pEnd);
    PUTL("pSafe", r->pSafe);
#undef PUTL
    char *out = NULL;
    sm_serialize(&sm, &out, n, &e);
    sm_free(&sm);
    return out;
}

TEST(reclaim_row_text) {
    struct mem m;
    mem_init(&m);
    int64_t k1[] = {123};
    int64_t k3[] = {INT64_MIN, -1, INT64_MAX};
    struct rc_row rows[4];
    memset(rows, 0, sizeof rows);
    rows[0].lastKeyNull = true;
    rows[0].pEnd = -1;
    rows[0].pSafe = -1;
    rows[0].pStart = rows[0].pCut = 5041560;
    rows[1] = rows[0];
    rows[1].lastKeyNull = false;
    rows[1].lastKey = k1;
    rows[1].lastKey_n = 1;
    rows[1].done = true;
    rows[1].cut = true;
    rows[1].tStart = 10000289400000;
    rows[1].tEnd = 10000289500000;
    rows[2] = rows[1];
    rows[2].lastKey = k3;
    rows[2].lastKey_n = 3;
    rows[2].kvCount = INT64_MAX;
    rows[2].rewritten = INT64_MIN;
    rows[2].pSafe = 7;
    rows[3] = rows[0];
    rows[3].lastKeyNull = false;
    rows[3].lastKey = k3;
    rows[3].lastKey_n = 0;          /* long[0]: "lastKey=" */
    for (int i = 0; i < 4; i++) {
        size_t n1, n2;
        char *want = row_by_strmap(&m, &rows[i], &n1);
        char buf[1024];
        n2 = rc_row_text(&rows[i], buf, sizeof buf);
        REQUIRE(want != NULL);
        CHECK_EQ((int64_t) n1, (int64_t) n2);
        CHECK(strcmp(want, buf) == 0);
        if (strcmp(want, buf) != 0) {
            printf("want:\n%s\ngot:\n%s\n", want, buf);
        }
        mem_free(&m, want, n1 + 1, MEM_BUFFER);
        CHECK(n2 < rc_row_text_cap(&rows[i]));
    }
    /* 012-02, 8.13's example */
    char buf[1024];
    struct rc_row x;
    memset(&x, 0, sizeof x);
    int64_t key[] = {26177508076421160};
    x.pCut = 5041560;
    x.pStart = 5574880;
    x.tStart = 10000289400000;
    x.lastKey = key;
    x.lastKey_n = 1;
    x.rewritten = 102488;
    x.pEnd = -1;
    x.pSafe = -1;
    x.kvCount = 466;
    rc_row_text(&x, buf, sizeof buf);
    CHECK(strcmp(buf, "pCut=5041560\ntEnd=0\ncut=false\npStart=5574880\ntStart=10000289400000\n"
            "lastKey=26177508076421160\nrewritten=102488\npEnd=-1\npSafe=-1\ndone=false\n"
            "kvCount=466\n") == 0);
    CHECK_MEM_ZERO(&m);
}

/* IterationInfo.testSerialize1, testSerialize2, testDeserializeWithBadString,
 * and the defaults of rows stored before 2026-10-13. */
TEST(reclaim_row_parse) {
    struct mem m;
    struct err e;
    mem_init(&m);
    for (int done = 1; done >= 0; done--) {
        int64_t key[] = {123};
        struct rc_row i1;
        memset(&i1, 0, sizeof i1);
        i1.done = done == 1;
        i1.kvCount = 10;
        i1.lastKey = key;
        i1.lastKey_n = 1;
        i1.pStart = 1000;
        i1.tEnd = 20 * 1000;
        i1.tStart = 10 * 1000;
        char s[1024];
        size_t n = rc_row_text(&i1, s, sizeof s);
        struct rc_row i2;
        REQUIRE(rc_row_parse(&m, s, n, &i2, &e) == ERR_OK);
        CHECK(i2.done == i1.done);
        CHECK_EQ(i2.kvCount, 10);
        CHECK(!i2.lastKeyNull && i2.lastKey_n == 1 && i2.lastKey[0] == 123);
        CHECK_EQ(i2.pStart, 1000);
        CHECK_EQ(i2.tEnd, 20000);
        CHECK_EQ(i2.tStart, 10000);
        char s2[1024];
        rc_row_text(&i2, s2, sizeof s2);
        CHECK(strcmp(s, s2) == 0);
        rc_row_free(&m, &i2);
        if (done == 0) {
            /* s.replace("false", "fALse") */
            char *p;
            while ((p = strstr(s, "false")) != NULL) {
                memcpy(p, "fALse", 5);
            }
            CHECK(rc_row_parse(&m, s, strlen(s), &i2, &e) == ERR_FORMAT);
            CHECK(strcmp(e.java, "InternalDataException") == 0);
        }
    }
    /* Missing and bad fields; old rows' defaults. */
    struct rc_row r;
    const char *missing = "pStart=1\ntStart=2\ntEnd=3\nlastKey=null\ndone=true\n";
    CHECK(rc_row_parse(&m, missing, strlen(missing), &r, &e) == ERR_FORMAT);   /* kvCount */
    const char *old = "pStart=100\ntStart=2\ntEnd=3\nkvCount=4\nlastKey=5 -6\ndone=true\n";
    REQUIRE(rc_row_parse(&m, old, strlen(old), &r, &e) == ERR_OK);
    CHECK(!r.cut && r.rewritten == 0 && r.pEnd == 100 && r.pSafe == -1 && r.pCut == 100);
    CHECK(r.lastKey_n == 2 && r.lastKey[0] == 5 && r.lastKey[1] == -6);
    rc_row_free(&m, &r);
    const char *badkey = "pStart=1\ntStart=2\ntEnd=3\nkvCount=4\nlastKey=5 x\ndone=true\n";
    CHECK(rc_row_parse(&m, badkey, strlen(badkey), &r, &e) == ERR_FORMAT);
    const char *nodone = "pStart=1\ntStart=2\ntEnd=3\nkvCount=4\nlastKey=null\n";
    CHECK(rc_row_parse(&m, nodone, strlen(nodone), &r, &e) == ERR_FORMAT);
    const char *nokey = "pStart=1\ntStart=2\ntEnd=3\nkvCount=4\ndone=false\n";
    CHECK(rc_row_parse(&m, nokey, strlen(nokey), &r, &e) == ERR_FORMAT);
    CHECK_MEM_ZERO(&m);
}

TEST(reclaim_table_text) {
    struct mem m;
    struct err e;
    mem_init(&m);
    struct reclaim r;
    rc_init(&r, &m);
    CHECK(rc_table_parse(&r, "", 0, &e) == ERR_FORMAT);         /* no rows */
    CHECK(rc_table_parse(&r, "----next----\n", 13, &e) == ERR_FORMAT);
    const char *t = "pCut=1\ntEnd=0\ncut=false\npStart=1\ntStart=5\nlastKey=null\nrewritten=0\n"
            "pEnd=-1\npSafe=-1\ndone=false\nkvCount=0\n----next----\n"
            "pCut=1\ntEnd=9\ncut=true\npStart=20\ntStart=6\nlastKey=1 2 3\nrewritten=7\n"
            "pEnd=30\npSafe=40\ndone=true\nkvCount=8\n----next----\n";
    REQUIRE(rc_table_parse(&r, t, strlen(t), &e) == ERR_OK);
    CHECK_EQ(r.nrows, 2);
    char *out;
    size_t n, cap;
    REQUIRE(rc_table_text(&r, &out, &n, &cap, &e) == ERR_OK);
    CHECK_EQ((int64_t) n, (int64_t) strlen(t));
    CHECK(strcmp(out, t) == 0);
    mem_free(&m, out, cap, MEM_BUFFER);
    rc_free(&r);
    CHECK_MEM_ZERO(&m);
}

/* The defaults, the checks of the settings (checkRetainDuration,
 * checkInternalFraction: 66 to 58,982, 0.001 and 0.90 rounded) with Java's
 * texts, and the settings' text (serializeSettings, 015-87). */
TEST(reclaim_settings) {
    struct mem m;
    struct err e;
    mem_init(&m);
    struct reclaim r;
    rc_init(&r, &m);
    CHECK_EQ(r.retainDuration, INT64_MAX);
    CHECK_EQ(r.internalFraction, 16384);       /* 0.25 in units of 2^-16 (005-79) */
    CHECK_EQ(r.stepReserve, INT64_C(4) << 20);
    CHECK(rc_check_retain_duration(CLK_UNITS_PER_SEC - 1, &e) == ERR_ARG);
    CHECK(strcmp(e.java, "IllegalArgumentException") == 0);
    CHECK(strcmp(e.text, "retainDuration = 9999999 is too small, must be at least one second "
            "(10000000 time units).") == 0);
    CHECK(rc_check_retain_duration(-1, &e) == ERR_ARG);
    CHECK(rc_check_retain_duration(CLK_UNITS_PER_SEC, &e) == ERR_OK);
    CHECK(rc_check_retain_duration(INT64_MAX, &e) == ERR_OK);
    CHECK(rc_check_internal_fraction(65, &e) == ERR_ARG);
    CHECK(strcmp(e.text, "Illegal internalFraction value, 65") == 0);
    CHECK(rc_check_internal_fraction(58983, &e) == ERR_ARG);
    CHECK(rc_check_internal_fraction(66, &e) == ERR_OK);
    CHECK(rc_check_internal_fraction(58982, &e) == ERR_OK);
    CHECK(rc_set_step_reserve(&r, 0, &e) == ERR_ARG);
    CHECK(rc_set_step_reserve(&r, 1, &e) == ERR_OK);
    char text[RC_SETTINGS_TEXT_CAP];
    CHECK_EQ((int64_t) rc_settings_text(INT64_MAX, 16384, text), 42);
    CHECK(strcmp(text, "retain=9223372036854775807\nfraction=16384\n") == 0);
    CHECK_EQ((int64_t) rc_settings_text(CLK_UNITS_PER_SEC, 6554, text), 30);
    CHECK(strcmp(text, "retain=10000000\nfraction=6554\n") == 0);
    rc_free(&r);
    CHECK_MEM_ZERO(&m);
}

/* The exact reference: clang's and gcc's 128-bit integers. */
__extension__ typedef __int128 i128;

static void check_fraction_of(int64_t g, int32_t f) {
    const i128 x = (i128) g * f;
    /* floor(g f / 2^16): >> of a negative __int128 is arithmetic on clang
     * and gcc, the floor. */
    CHECK_EQ(rc_fraction_of(g, f), (int64_t) (x >> 16));
}

/* Reclaim.Tester.testFractionOfExact (bergdb 005-79): floor(g f / 2^16)
 * for every int64_t g, against the exact product, on the edges and on
 * 10^5 random pairs; for the default fraction it is floor(g / 4). */
TEST(reclaim_fraction_of_exact) {
    const int64_t gs[] = {0, 1, 3, 4, 0xFFFF, 0x10000, INT64_C(1) << 47,
            (INT64_C(1) << 53) / 3, INT64_C(1) << 53, INT64_MAX - 1, INT64_MAX, -1, -0x10001,
            INT64_MIN};
    const int32_t fs[] = {0, 1, RC_MIN_INTERNAL_FRACTION, RC_DEFAULT_INTERNAL_FRACTION,
            RC_MAX_INTERNAL_FRACTION, RC_FRACTION_ONE - 1};
    for (size_t i = 0; i < sizeof gs / sizeof gs[0]; i++) {
        for (size_t j = 0; j < sizeof fs / sizeof fs[0]; j++) {
            check_fraction_of(gs[i], fs[j]);
        }
    }
    uint64_t z = 79;
    for (int i = 0; i < 100000; i++) {
        z += UINT64_C(0x9E3779B97F4A7C15);
        uint64_t x = (z ^ (z >> 30)) * UINT64_C(0xBF58476D1CE4E5B9);
        x = (x ^ (x >> 27)) * UINT64_C(0x94D049BB133111EB);
        x ^= x >> 31;
        const int64_t g = j_shr64((int64_t) x, (int) (x >> 58));
        check_fraction_of(g, (int32_t) (x & 0xFFFF));
    }
    CHECK_EQ(rc_fraction_of(1000003, RC_DEFAULT_INTERNAL_FRACTION), 1000003 / 4);
}

/* ======== A database in memory ======== */

struct rdb {
    struct mem m;
    struct db db;
    int64_t time;           /* the test clock */
};

static int64_t rdb_clock(void *ctx) {
    return *(int64_t *) ctx;
}

/* A new database in memory, and its retain duration set after the start, as
 * Java's tests do since release 2026.3 (setRetainDuration, 015-87): a record
 * of reclaim's settings unless it is forever. */
static enum err_code rdb_open(struct rdb *r, int32_t node, int32_t sd, int64_t reserve,
        int64_t retain) {
    struct db_config cfg;
    struct db_start_info info;
    struct err e;
    memset(&cfg, 0, sizeof cfg);
    cfg.max_node_size = node;
    cfg.startup_distance = sd;
    cfg.cache_size_indicator = INT64_MAX;
    cfg.clock = rdb_clock;
    cfg.clock_ctx = &r->time;
    cfg.step_reserve = reserve;
    memcpy(cfg.id, bergdb_test_id, sizeof cfg.id);      /* testSetup's DatabaseId.TEST_ID */
    enum err_code rc = db_open(&r->db, NULL, &cfg, &r->m, &info, &e);
    if (rc == ERR_OK) {
        rc = db_set_retain_duration(&r->db, retain, &e);
        if (rc != ERR_OK) {
            struct err e2;
            db_close(&r->db, &e2);
        }
    }
    return rc;
}

static void ikey_segments(const char *ikey, int64_t *seg, int32_t *n) {
    uint8_t b[256];
    int32_t len = (int32_t) strlen(ikey);
    keys_ikey_to_bkey((const uint8_t *) ikey, len, b);
    keys_to_segments(b, len, seg);
    *n = keys_segment_count(len);
}

/* A transaction of one put (len >= 0) or delete (len -1); t's fields set. */
static enum err_code rdb_put(struct rdb *r, const char *ikey, const uint8_t *v, int32_t len,
        struct trans *out) {
    struct tr_builder b;
    struct trans t;
    struct err e;
    int64_t seg[64];
    int32_t n;
    ikey_segments(ikey, seg, &n);
    tr_builder_init(&b, &r->m);
    tr_init(&t, &r->m);
    enum err_code rc = tr_put_segments(&b, seg, n, len < 0 ? NULL : (v == NULL ? (const uint8_t *) "" : v),
            len, &e);
    if (rc == ERR_OK) {
        rc = tr_build(&b, &t, &e);
    }
    if (rc == ERR_OK) {
        rc = db_execute(&r->db, &t, &e);
    }
    if (out != NULL) {
        *out = t;
    }
    tr_free(&t);
    tr_builder_free(&b);
    return rc;
}

/* getOne at time lt: *len -1 for none; ERR_NOT_AVAILABLE before the first
 * available time. tpos the value's record. */
static enum err_code rdb_get(struct rdb *r, int64_t lt, const char *ikey, uint8_t *v,
        int32_t *len, int64_t *tpos) {
    int64_t seg[64];
    int32_t n;
    struct err e;
    ikey_segments(ikey, seg, &n);
    struct getdata gd;
    db_new_get_data(&r->db, &gd);
    struct vnode *x;
    enum err_code rc = db_get_one(&r->db, lt, seg, n, &gd, &x, &e);
    *len = -1;
    if (rc == ERR_OK && x != NULL && x->len >= 0) {
        *len = x->len;
        if (v != NULL) {
            memcpy(v, x->value, (size_t) x->len);
        }
        if (tpos != NULL) {
            *tpos = gd.tpos;
        }
    }
    return rc;
}

static void close_rdb(struct rdb *r) {
    struct err e;
    CHECK(db_recount(&r->db) == 0);
    CHECK(db_close(&r->db, &e) == ERR_OK);
}

/* A done row, the last one, or NULL. */
static const struct rc_row *last_done_row(const struct reclaim *rc, int32_t *index) {
    const struct rc_row *result = NULL;
    for (int32_t i = 0; i < rc->nrows; i++) {
        if (rc->rows[i].done) {
            result = &rc->rows[i];
            *index = i;
        }
    }
    return result;
}

/* Reclaim.Tester.testIterationRewritesAllOldValues and testCutPointBeforeScan:
 * when an iteration is done, every live value is stored at or after its
 * pCut, which is the pStart of the iteration before (its own for the
 * first); some values between the two are spared. */
TEST(reclaim_iterations_rewrite_old_values) {
    struct rdb r;
    mem_init(&r.m);
    r.time = CLK_UNITS_PER_SEC;
    REQUIRE(rdb_open(&r, 8, 2000, 0, 1000 * CLK_UNITS_PER_SEC) == ERR_OK); /* no cut */
    uint64_t rnd = 5;
    char live[100];
    memset(live, 0, sizeof live);
    int64_t checked = 0;
    int spared = 0;
    for (int i = 0; i < 2000 && checked < 4; i++) {
        r.time += CLK_UNITS_PER_SEC;
        int k = test_random_below(&rnd, 100);
        char key[32];
        snprintf(key, sizeof key, "/k/%d", k);
        uint8_t v[32];
        int32_t len = 1 + test_random_below(&rnd, 30);
        for (int j = 0; j < len; j++) {
            v[j] = (uint8_t) test_random(&rnd);
        }
        REQUIRE(rdb_put(&r, key, v, len, NULL) == ERR_OK);
        live[k] = 1;
        if (r.db.reclaim.iterationCount > checked) {
            checked = r.db.reclaim.iterationCount;
            int32_t index = -1;
            const struct rc_row *done = last_done_row(&r.db.reclaim, &index);
            REQUIRE(done != NULL);
            CHECK_EQ(done->pCut, index == 0 ? done->pStart : r.db.reclaim.rows[index - 1].pStart);
            for (int j = 0; j < 100; j++) {
                if (!live[j]) {
                    continue;
                }
                snprintf(key, sizeof key, "/k/%d", j);
                int64_t tpos = -1;
                int32_t n;
                REQUIRE(rdb_get(&r, INT64_MAX, key, NULL, &n, &tpos) == ERR_OK);
                CHECK(n >= 0);
                CHECK(tpos >= done->pCut);
                if (tpos < done->pStart) {
                    spared++;
                }
            }
        }
    }
    CHECK(checked >= 4);
    CHECK(spared > 0);
    CHECK_EQ(r.db.reclaim.firstAvailablePos, 0);
    close_rdb(&r);
    CHECK_MEM_ZERO(&r.m);
}

/* Reclaim.Tester.testIterationsSpacedByRetention, with
 * testIterationsFollowSetStartupDistance's check: each iteration starts a
 * quarter of the retention after the one before, and more than twice the
 * startup distance in force after it. */
TEST(reclaim_iterations_spaced) {
    struct rdb r;
    mem_init(&r.m);
    r.time = CLK_UNITS_PER_SEC;
    const int64_t retain = 20 * CLK_UNITS_PER_SEC;
    REQUIRE(rdb_open(&r, 8, 2000, 0, retain) == ERR_OK);
    uint64_t rnd = 3;
    int64_t starts[64], pstarts[64];
    int nstarts = 0;
    struct err e;
    int64_t sdAt = -1;
    for (int i = 0; i < 4000; i++) {
        r.time += CLK_UNITS_PER_SEC / 10;
        if (i == 2000) {
            /* A larger startup distance spaces the iterations too (005-61). */
            REQUIRE(db_set_startup_distance(&r.db, 2 * 200000, &e) == ERR_OK);
            sdAt = nstarts;
        }
        char key[32];
        snprintf(key, sizeof key, "/k/%d", test_random_below(&rnd, 50));
        uint8_t v[32];
        int32_t len = 1 + test_random_below(&rnd, 30);
        memset(v, 7, sizeof v);
        REQUIRE(rdb_put(&r, key, v, len, NULL) == ERR_OK);
        const struct reclaim *rc = &r.db.reclaim;
        if (rc->nrows > 0) {
            int64_t tStart = rc->rows[rc->nrows - 1].tStart;
            if (nstarts == 0 || starts[nstarts - 1] != tStart) {
                REQUIRE(nstarts < 64);
                pstarts[nstarts] = rc->rows[rc->nrows - 1].pStart;
                starts[nstarts++] = tStart;
            }
        }
    }
    CHECK(nstarts >= 6);
    CHECK(r.db.reclaim.firstAvailablePos > 0);
    for (int i = 1; i < nstarts; i++) {
        CHECK(starts[i] - starts[i - 1] >= retain / 4);
        CHECK(pstarts[i] - pstarts[i - 1] > 2 * (i > sdAt ? 400000 : 2000));
    }
    close_rdb(&r);
    CHECK_MEM_ZERO(&r.m);
}

/* The model: each key's values by time. */
#define MK 50
#define MV 400
struct model {
    int64_t times[MK][MV];
    uint8_t vals[MK][MV][32];
    int32_t lens[MK][MV];
    int32_t n[MK];
};

/* floorEntry(lt) of key k, or -1. */
static int32_t model_floor(const struct model *mo, int k, int64_t lt) {
    int32_t r = -1;
    for (int32_t i = 0; i < mo->n[k] && mo->times[k][i] <= lt; i++) {
        r = i;
    }
    return r;
}

/* Lookups from the first available time on equal the model; before it,
 * getOne and getMany are refused, and so is getTrans of a record before the
 * cut. */
static void check_lookups(struct rdb *r, const struct model *mo, int64_t step) {
    struct err e;
    const int64_t first = db_first_available_time(&r->db);
    const int64_t firstPos = db_first_available_pos(&r->db);
    REQUIRE(first > 0 && firstPos > 0);
    /* The memory stream's cut is exact (CutStream): made when durable,
     * which a memory stream always is, at the transaction after the
     * decision at the latest. */
    CHECK(stream_first_pos(&r->db.stream) <= firstPos);
    for (int64_t lt = first; lt <= r->time; lt += step) {
        for (int k = 0; k < MK; k++) {
            char key[32];
            snprintf(key, sizeof key, "/k/%d", k);
            uint8_t v[64];
            int32_t len;
            REQUIRE(rdb_get(r, lt, key, v, &len, NULL) == ERR_OK);
            int32_t i = model_floor(mo, k, lt);
            if (i < 0) {
                CHECK_EQ(len, -1);
            } else {
                CHECK_EQ(len, mo->lens[k][i]);
                CHECK(len < 0 || memcmp(v, mo->vals[k][i], (size_t) len) == 0);
            }
        }
    }
    int32_t len;
    CHECK(rdb_get(r, first - 1, "/k/1", NULL, &len, NULL) == ERR_NOT_AVAILABLE);
    struct getmany g;
    db_new_get_many(&r->db, &g);
    g.lookup_time = first - 1;
    CHECK(db_get_many(&r->db, &g, &e) == ERR_NOT_AVAILABLE);
    CHECK(strcmp(e.java, "LookupTimeNotAvailableException") == 0);
    {   /* Java's text, its first parenthesis closed (bergdb 020-24, U1-12) */
        char text[ERR_TEXT], a[CLK_UTC_SIZE], b[CLK_UTC_SIZE];
        clk_time_to_utc(first - 1, a);
        clk_time_to_utc(first, b);
        snprintf(text, sizeof text, "Cannot lookup at time %lld (%s): the first time available "
                "for lookup is %lld (%s).", (long long) (first - 1), a, (long long) first, b);
        CHECK(strcmp(e.text, text) == 0);
        struct getdata gd;
        struct vnode *v;
        const int64_t key[1] = { 0 };
        db_new_get_data(&r->db, &gd);
        CHECK(db_get_one(&r->db, first - 1, key, 1, &gd, &v, &e) == ERR_NOT_AVAILABLE);
        CHECK(strcmp(e.text, text) == 0);
    }
    g.lookup_time = first;
    CHECK(db_get_many(&r->db, &g, &e) == ERR_OK);
}

/* Reclaim.Tester.testLookupsFromFirstAvailableTime, without its restarts
 * (part 2): after each of three cuts. */
TEST(reclaim_lookups_from_first_available_time) {
    struct rdb r;
    static struct model mo;
    memset(&mo, 0, sizeof mo);
    mem_init(&r.m);
    r.time = CLK_UNITS_PER_SEC;
    REQUIRE(rdb_open(&r, 8, 2000, 0, CLK_UNITS_PER_SEC) == ERR_OK);
    uint64_t rnd = 1;
    int cuts = 0;
    int64_t lastCut = 0;
    for (int i = 0; i < 6000 && cuts < 3; i++) {
        r.time += CLK_UNITS_PER_SEC / 20;
        int k = test_random_below(&rnd, MK);
        char key[32];
        snprintf(key, sizeof key, "/k/%d", k);
        uint8_t v[32];
        int32_t len = 1 + test_random_below(&rnd, 30);
        for (int j = 0; j < len; j++) {
            v[j] = (uint8_t) test_random(&rnd);
        }
        struct trans t;
        REQUIRE(rdb_put(&r, key, v, len, &t) == ERR_OK);
        REQUIRE(mo.n[k] < MV);
        mo.times[k][mo.n[k]] = t.tt;
        memcpy(mo.vals[k][mo.n[k]], v, (size_t) len);
        mo.lens[k][mo.n[k]] = len;
        mo.n[k]++;
        if (stream_first_pos(&r.db.stream) > lastCut) {
            cuts++;
            lastCut = stream_first_pos(&r.db.stream);
            CHECK_EQ(lastCut, db_first_available_pos(&r.db));
            check_lookups(&r, &mo, CLK_UNITS_PER_SEC / 40);
            /* getTrans of the record before the cut: the read below the
             * stream's first position. */
            struct ns_iter it;
            struct err e;
            bool has;
            ns_iter_init(&it, &r.db.stream, &r.m, META_BLOCK_SIZE, true);
            CHECK(ns_iter_next(&it, &has, &e) == ERR_NOT_AVAILABLE);
            ns_iter_free(&it);
        }
        /* keep the model's arrays small: drop what is before the cut */
        if (mo.n[k] == MV) {
            break;
        }
    }
    CHECK(cuts >= 3);
    close_rdb(&r);
    CHECK_MEM_ZERO(&r.m);
}

/* Reclaim.Tester.testStepReserveSplitsSteps, without eviction (012-12) and
 * restarts: with a reserve of four nodes, steps are split (more of them),
 * the iterations still end and cut, and the lookups from the first
 * available time on are right; with the default reserve none is split. */
TEST(reclaim_step_reserve_splits_steps) {
    int64_t steps[2];
    static struct model mo;
    for (int pass = 0; pass < 2; pass++) {
        bool small = pass == 1;
        struct rdb r;
        memset(&mo, 0, sizeof mo);
        mem_init(&r.m);
        r.time = CLK_UNITS_PER_SEC;
        REQUIRE(rdb_open(&r, 8, 2000, small ? 4 * (80 + 48 * 8) : 0, CLK_UNITS_PER_SEC)
                == ERR_OK);
        uint64_t rnd = 1;
        for (int i = 0; i < 3000 && stream_first_pos(&r.db.stream) == 0; i++) {
            r.time += CLK_UNITS_PER_SEC / 20;
            int k = test_random_below(&rnd, MK);
            char key[32];
            snprintf(key, sizeof key, "/k/%d", k);
            uint8_t v[32];
            int32_t len = 1 + test_random_below(&rnd, 30);
            for (int j = 0; j < len; j++) {
                v[j] = (uint8_t) test_random(&rnd);
            }
            struct trans t;
            REQUIRE(rdb_put(&r, key, v, len, &t) == ERR_OK);
            REQUIRE(mo.n[k] < MV);
            mo.times[k][mo.n[k]] = t.tt;
            memcpy(mo.vals[k][mo.n[k]], v, (size_t) len);
            mo.lens[k][mo.n[k]] = len;
            mo.n[k]++;
        }
        CHECK(stream_first_pos(&r.db.stream) > 0);
        if (small) {
            CHECK(r.db.reclaim.splitSteps > 0);
        } else {
            CHECK_EQ(r.db.reclaim.splitSteps, 0);
        }
        steps[pass] = r.db.reclaim.steps;
        check_lookups(&r, &mo, CLK_UNITS_PER_SEC / 4);
        close_rdb(&r);
        CHECK_MEM_ZERO(&r.m);
    }
    CHECK(steps[1] > steps[0]);
}

/* The table and the current row in the stream: what initFromDb reads back
 * equals the table in memory, the current row replacing its row. */
TEST(reclaim_table_in_stream) {
    struct rdb r;
    mem_init(&r.m);
    r.time = CLK_UNITS_PER_SEC;
    REQUIRE(rdb_open(&r, 8, 2000, 0, CLK_UNITS_PER_SEC) == ERR_OK);
    uint64_t rnd = 9;
    int checks = 0;
    for (int i = 0; i < 1500; i++) {
        r.time += CLK_UNITS_PER_SEC / 20;
        char key[32];
        snprintf(key, sizeof key, "/k/%d", test_random_below(&rnd, 300));
        REQUIRE(rdb_put(&r, key, (const uint8_t *) "value", 5, NULL) == ERR_OK);
        if (i % 50 != 49 || r.db.reclaim.nrows == 0) {
            continue;
        }
        /* initFromDb on a copy of the reclaim state's settings */
        struct reclaim saved = r.db.reclaim;
        rc_init(&r.db.reclaim, &r.m);
        struct err e;
        REQUIRE(rc_init_from_db(&r.db, &e) == ERR_OK);
        CHECK_EQ(r.db.reclaim.nrows, saved.nrows);
        for (int32_t k = 0; k < saved.nrows && k < r.db.reclaim.nrows; k++) {
            char a[2048], b[2048];
            rc_row_text(&saved.rows[k], a, sizeof a);
            rc_row_text(&r.db.reclaim.rows[k], b, sizeof b);
            CHECK(strcmp(a, b) == 0);
        }
        CHECK_EQ(r.db.reclaim.firstAvailablePos, saved.firstAvailablePos);
        CHECK_EQ(r.db.reclaim.firstAvailableLookupTime, saved.firstAvailableLookupTime);
        rc_free(&r.db.reclaim);
        r.db.reclaim = saved;
        checks++;
    }
    CHECK(checks > 10);
    CHECK(r.db.reclaim.firstAvailablePos > 0);
    close_rdb(&r);
    CHECK_MEM_ZERO(&r.m);
}

/* The allocation failures in turn (012-01, 4.5) over the transactions that
 * start the first iteration, make its steps, mark it done and safe, and cut:
 * each allocation in that window made to fail once (a stride keeps the runs
 * few), and each run gives NOMEM before the go point (the database as it
 * was) or a failed database after it, and the close frees everything. */
static int64_t reclaim_run(int64_t fail_at, int *refused, int *failed, int64_t *cutAt) {
    struct rdb r;
    mem_init(&r.m);
    r.time = CLK_UNITS_PER_SEC;
    if (rdb_open(&r, 8, 2000, 0, CLK_UNITS_PER_SEC) != ERR_OK) {
        CHECK(0);
        return 0;
    }
    int64_t base = r.m.allocs;
    r.m.fail_at = fail_at > 0 ? base + fail_at : 0;
    uint64_t rnd = 2;
    for (int i = 0; i < 400; i++) {
        r.time += CLK_UNITS_PER_SEC / 20;
        char key[32];
        snprintf(key, sizeof key, "/k/%d", test_random_below(&rnd, 40));
        enum err_code rc = rdb_put(&r, key, (const uint8_t *) "a value", 7, NULL);
        if (rc == ERR_NOMEM && r.db.state == DB_ACTIVE) {
            (*refused)++;
            CHECK(db_recount(&r.db) == 0);
            r.m.fail_at = 0;
            rc = rdb_put(&r, key, (const uint8_t *) "a value", 7, NULL);
            CHECK(rc == ERR_OK);
        } else if (rc != ERR_OK) {
            CHECK(rc == ERR_FAILED);
            CHECK(r.db.state == DB_FAILED);
            (*failed)++;
            break;
        }
        if (cutAt != NULL && *cutAt == 0 && stream_first_pos(&r.db.stream) > 0) {
            *cutAt = r.m.allocs - base;
        }
    }
    int64_t made = r.m.allocs - base;
    struct err e;
    db_close(&r.db, &e);
    CHECK_MEM_ZERO(&r.m);
    return made;
}

TEST(reclaim_alloc_failures) {
    int refused = 0, failed = 0;
    int64_t cutAt = 0;
    int64_t total = reclaim_run(0, &refused, &failed, &cutAt);
    REQUIRE(cutAt > 0);
    CHECK_EQ(refused + failed, 0);
    /* The window: the run up to the cut, and a little after. */
    int runs = 0;
    const int64_t stride = cutAt / 300 > 1 ? cutAt / 300 : 1;
    for (int64_t k = 1; k <= cutAt + 50 && k < total; k += stride) {
        int64_t before = refused + failed;
        reclaim_run(k, &refused, &failed, NULL);
        CHECK(refused + failed == before + 1);
        runs++;
    }
    printf("  reclaim_alloc_failures: %d runs: %d transactions refused (NOMEM), %d failed "
            "databases\n", runs, refused, failed);
    CHECK(failed > 0);
}

/* ======== Java's runs (reclaim.txt) ======== */

#ifndef VECTORS_DIR
#define VECTORS_DIR "test/unit/vectors"
#endif

/* Vectors.reclaim's run, in C: the same transactions, the same settings. */
TEST(reclaim_java_vectors) {
    char path[1024];
    const char *dir = getenv("BERGDB_VECTORS");
    snprintf(path, sizeof path, "%s/reclaim.txt", dir != NULL ? dir : VECTORS_DIR);
    FILE *f = fopen(path, "r");
    if (f == NULL) {
        printf("cannot open %s: %s\n", path, strerror(errno));
        CHECK(0);
        return;
    }
    char line[1024];
    int cases = 0;
    while (fgets(line, sizeof line, f) != NULL) {
        if (line[0] == '#') {
            continue;
        }
        long long reserve, n, length, firstPos, firstTime, iterations;
        char sha[65];
        if (sscanf(line, "reclaim reserve=%lld n=%lld length=%lld firstAvailablePos=%lld "
                "firstAvailableTime=%lld iterations=%lld sha256=%64s", &reserve, &n, &length,
                &firstPos, &firstTime, &iterations, sha) != 7) {
            printf("a line of reclaim.txt not known: %s", line);
            CHECK(0);
            continue;
        }
        struct rdb r;
        mem_init(&r.m);
        r.time = CLK_UNITS_PER_SEC;
        REQUIRE(rdb_open(&r, 8, 2000, reserve, CLK_UNITS_PER_SEC) == ERR_OK);
        for (int i = 0; i < n; i++) {
            r.time += CLK_UNITS_PER_SEC / 20;
            uint8_t v[32];
            int32_t len = 1 + (i * 31) % 30;
            for (int j = 0; j < len; j++) {
                v[j] = (uint8_t) (i + j);
            }
            char key[32];
            snprintf(key, sizeof key, "/k/%d", (i * 7919) % 200);
            REQUIRE(rdb_put(&r, key, v, len, NULL) == ERR_OK);
        }
        CHECK_EQ(db_stream_length(&r.db), length);
        CHECK_EQ(db_first_available_pos(&r.db), firstPos);
        CHECK_EQ(db_first_available_time(&r.db), firstTime);
        CHECK_EQ(r.db.reclaim.iterationCount, iterations);
        if (reserve < RC_DEFAULT_STEP_RESERVE) {
            CHECK(r.db.reclaim.splitSteps > 0);
        }
        struct sha256 h;
        sha256_init(&h);
        uint8_t buf[4096];
        struct err e;
        for (int64_t p = firstPos; p < db_stream_length(&r.db); ) {
            int64_t k = db_stream_length(&r.db) - p;
            int32_t m = (int32_t) (k < (int64_t) sizeof buf ? k : (int64_t) sizeof buf);
            REQUIRE(stream_read(&r.db.stream, p, buf, m, &e) == ERR_OK);
            sha256_update(&h, buf, (size_t) m);
            p += m;
        }
        uint8_t d[32];
        char hex[65];
        sha256_final(&h, d);
        for (int i = 0; i < 32; i++) {
            snprintf(hex + 2 * i, 3, "%02x", d[i]);
        }
        CHECK(strcmp(hex, sha) == 0);
        close_rdb(&r);
        CHECK_MEM_ZERO(&r.m);
        cases++;
    }
    fclose(f);
    CHECK_EQ(cases, 2);
}

/* ======== Reclaim's settings in the stream (015-87), and 015-54, 015-50, 015-55 ======== */

/* A temporary directory, for a database that restarts. */
static void rs_temp_dir(char *out, size_t cap) {
    const char *t = getenv("TMPDIR");
    snprintf(out, cap, "%s/bergdb-t_reclaim-XXXXXX", t != NULL ? t : "/tmp");
    if (mkdtemp(out) == NULL) {
        out[0] = '\0';
    }
}

static void rs_remove_dir(const char *dir) {
    char cmd[1200];
    snprintf(cmd, sizeof cmd, "rm -rf '%s'", dir);
    if (system(cmd) != 0) {
        printf("could not remove %s\n", dir);
    }
}

/* Opens r's database in dir (NULL: in memory) with no setter: a creation,
 * or a start of the database there (testSetup: the test id, no eviction). A
 * record limit of 0 is the default. */
static enum err_code rdb_start(struct rdb *r, const char *dir, int32_t node, int32_t sd,
        int64_t record_limit, struct err *e) {
    struct db_config cfg;
    struct db_start_info info;
    memset(&cfg, 0, sizeof cfg);
    cfg.max_node_size = node;
    cfg.startup_distance = sd;
    cfg.cache_size_indicator = INT64_MAX;
    cfg.clock = rdb_clock;
    cfg.clock_ctx = &r->time;
    cfg.record_limit = record_limit;
    memcpy(cfg.id, bergdb_test_id, sizeof cfg.id);
    return db_open(&r->db, dir, &cfg, &r->m, &info, e);
}

/* A restart: the close (which writes and forces all) and a start. */
static enum err_code rdb_restart(struct rdb *r, const char *dir, int32_t node, int32_t sd,
        int64_t record_limit, struct err *e) {
    enum err_code rc = db_close(&r->db, e);
    return rc != ERR_OK ? rc : rdb_start(r, dir, node, sd, record_limit, e);
}

/* An internal transaction of one put, as only the database writes reclaim's
 * KVs. */
static enum err_code rdb_put_internal(struct rdb *r, const char *ikey, const char *value) {
    struct tr_builder b;
    struct trans t;
    struct err e;
    int64_t seg[64];
    int32_t n;
    ikey_segments(ikey, seg, &n);
    tr_builder_init(&b, &r->m);
    tr_init(&t, &r->m);
    enum err_code rc = tr_put_segments(&b, seg, n, (const uint8_t *) value,
            (int32_t) strlen(value), &e);
    if (rc == ERR_OK) {
        rc = tr_build(&b, &t, &e);
    }
    if (rc == ERR_OK) {
        t.is_internal = true;
        rc = db_execute(&r->db, &t, &e);
    }
    tr_free(&t);
    tr_builder_free(&b);
    return rc;
}

/* The settings' KV as text, or "" for none. */
static void settings_kv(struct rdb *r, char *out, size_t cap) {
    uint8_t v[RC_SETTINGS_TEXT_CAP];
    int32_t len;
    out[0] = '\0';
    if (rdb_get(r, INT64_MAX, RC_SETTINGS_KEY_NAME, v, &len, NULL) == ERR_OK && len >= 0
            && (size_t) len < cap) {
        memcpy(out, v, (size_t) len);
        out[len] = '\0';
    }
}

/* SHA-256 of r's stream from pos to its end. */
static void stream_digest(struct rdb *r, int64_t pos, char hex[65]) {
    struct sha256 h;
    struct err e;
    uint8_t buf[4096];
    uint8_t d[32];
    sha256_init(&h);
    for (int64_t p = pos; p < db_stream_length(&r->db); ) {
        int64_t k = db_stream_length(&r->db) - p;
        int32_t m = (int32_t) (k < (int64_t) sizeof buf ? k : (int64_t) sizeof buf);
        CHECK(stream_read(&r->db.stream, p, buf, m, &e) == ERR_OK);
        sha256_update(&h, buf, (size_t) m);
        p += m;
    }
    sha256_final(&h, d);
    for (int i = 0; i < 32; i++) {
        snprintf(hex + 2 * i, 3, "%02x", d[i]);
    }
}

/* DbTesterRestart.testReclaimSettingsKeptOverRestarts' workload: 2000
 * commits, one every 0.1 s, the retain duration 1 s and the fraction 0.1
 * set once, after commit 100; with restarts, one every 50 commits from 100
 * on, the settings not set again. The decided cut, the length and the
 * stream's digest from the cut. */
static void settings_run(bool restarts, int64_t *cut, int64_t *length, char hex[65]) {
    struct rdb r;
    struct err e;
    char dir[1024];
    mem_init(&r.m);
    r.time = 0;
    *cut = -1;
    if (restarts) {
        rs_temp_dir(dir, sizeof dir);
        REQUIRE(dir[0] != '\0');
    }
    REQUIRE(rdb_start(&r, restarts ? dir : NULL, 8, 1000, 0, &e) == ERR_OK);
    uint64_t rnd = 1;
    for (int i = 1; i <= 2000; i++) {
        r.time = i * CLK_UNITS_PER_SEC / 10;
        uint8_t v[48];
        int32_t len = 1 + test_random_below(&rnd, 40);
        for (int j = 0; j < len; j++) {
            v[j] = (uint8_t) test_random(&rnd);
        }
        char key[32];
        snprintf(key, sizeof key, "/k/%d", test_random_below(&rnd, 500));
        REQUIRE(rdb_put(&r, key, v, len, NULL) == ERR_OK);
        if (i == 100) {
            REQUIRE(db_set_retain_duration(&r.db, CLK_UNITS_PER_SEC, &e) == ERR_OK);
            REQUIRE(db_set_reclaim_internal_fraction(&r.db, 0.1, &e) == ERR_OK);
        }
        if (restarts && i >= 100 && i % 50 == 0 && i < 2000) {
            REQUIRE(rdb_restart(&r, dir, 8, 1000, 0, &e) == ERR_OK);
            CHECK_EQ(r.db.reclaim.retainDuration, CLK_UNITS_PER_SEC);
            CHECK_EQ(r.db.reclaim.internalFraction, 6554);
        }
    }
    CHECK(db_first_available_pos(&r.db) > 0);
    *cut = stream_first_pos(&r.db.stream) > db_first_available_pos(&r.db)
            ? stream_first_pos(&r.db.stream) : db_first_available_pos(&r.db);
    *length = db_stream_length(&r.db);
    stream_digest(&r, *cut, hex);
    close_rdb(&r);
    CHECK_MEM_ZERO(&r.m);
    if (restarts) {
        rs_remove_dir(dir);
    }
}

/* DbTesterRestart.testReclaimSettingsKeptOverRestarts (015-87): the
 * settings, set once, are kept over restarts, so the stream from the
 * decided cut is the one of the run without restarts (010-P2). Before, a
 * start took the open's retain duration and the default fraction. */
TEST(reclaim_settings_kept_over_restarts) {
    int64_t cut1, length1, cut2, length2;
    char hex1[65], hex2[65];
    settings_run(false, &cut1, &length1, hex1);
    settings_run(true, &cut2, &length2, hex2);
    REQUIRE(cut1 > 0 && cut2 > 0);
    CHECK_EQ(cut1, cut2);
    CHECK_EQ(length1, length2);
    CHECK(strcmp(hex1, hex2) == 0);
}

/* DbTesterRestart.testRefusedReclaimSettingChangesNothing (015-87, F6): a
 * refused call writes nothing and changes nothing, also after a restart.
 * (C has no stop(); a failed database and a callback refuse the setters,
 * f_settings.c.) */
TEST(reclaim_settings_refused_change_nothing) {
    struct rdb r;
    struct err e;
    char dir[1024];
    mem_init(&r.m);
    rs_temp_dir(dir, sizeof dir);
    REQUIRE(dir[0] != '\0');
    r.time = 0;
    REQUIRE(rdb_start(&r, dir, 30, 50000000, 0, &e) == ERR_OK);
    r.time = 10;
    REQUIRE(rdb_put(&r, "/k", (const uint8_t *) "1", 1, NULL) == ERR_OK);
    REQUIRE(db_set_retain_duration(&r.db, 5 * CLK_UNITS_PER_SEC, &e) == ERR_OK);
    REQUIRE(db_set_reclaim_internal_fraction(&r.db, 0.5, &e) == ERR_OK);
    const int64_t length = db_stream_length(&r.db);
    CHECK(db_set_retain_duration(&r.db, CLK_UNITS_PER_SEC - 1, &e) == ERR_ARG);
    CHECK(db_set_retain_duration(&r.db, -1, &e) == ERR_ARG);
    CHECK(db_set_reclaim_internal_fraction(&r.db, 0.95, &e) == ERR_ARG);
    CHECK(db_set_reclaim_internal_fraction(&r.db, NAN, &e) == ERR_ARG);
    CHECK_EQ(db_stream_length(&r.db), length);
    CHECK_EQ(r.db.reclaim.retainDuration, 5 * CLK_UNITS_PER_SEC);
    CHECK_EQ(r.db.reclaim.internalFraction, 32768);
    REQUIRE(rdb_restart(&r, dir, 30, 50000000, 0, &e) == ERR_OK);
    CHECK_EQ(r.db.reclaim.retainDuration, 5 * CLK_UNITS_PER_SEC);
    CHECK_EQ(r.db.reclaim.internalFraction, 32768);
    close_rdb(&r);
    CHECK_MEM_ZERO(&r.m);
    rs_remove_dir(dir);
}

/* DbTesterRestart.testReclaimSettingInForceWritesNothing (015-87, F6): a
 * call with the value in force writes nothing; one with another value
 * writes one record, and the value is in force when it returns; the KV
 * holds both settings. */
TEST(reclaim_settings_in_force_write_nothing) {
    struct rdb r;
    struct err e;
    char kv[RC_SETTINGS_TEXT_CAP];
    mem_init(&r.m);
    r.time = 0;
    REQUIRE(rdb_start(&r, NULL, 30, 50000000, 0, &e) == ERR_OK);
    r.time = 10;
    REQUIRE(rdb_put(&r, "/k", (const uint8_t *) "1", 1, NULL) == ERR_OK);
    CHECK_EQ(r.db.reclaim.retainDuration, INT64_MAX);
    CHECK(db_internal_fraction(&r.db) == 0.25);
    int64_t length = db_stream_length(&r.db);
    CHECK(db_set_retain_duration(&r.db, INT64_MAX, &e) == ERR_OK);
    CHECK(db_set_reclaim_internal_fraction(&r.db, 0.25, &e) == ERR_OK);
    CHECK_EQ(db_stream_length(&r.db), length);
    settings_kv(&r, kv, sizeof kv);
    CHECK(strcmp(kv, "") == 0);

    CHECK(db_set_retain_duration(&r.db, 3 * CLK_UNITS_PER_SEC, &e) == ERR_OK);
    CHECK(db_stream_length(&r.db) > length);
    CHECK_EQ(r.db.reclaim.retainDuration, 3 * CLK_UNITS_PER_SEC);
    length = db_stream_length(&r.db);
    CHECK(db_set_retain_duration(&r.db, 3 * CLK_UNITS_PER_SEC, &e) == ERR_OK);
    CHECK_EQ(db_stream_length(&r.db), length);
    CHECK(db_set_reclaim_internal_fraction(&r.db, 0.1, &e) == ERR_OK);
    CHECK(db_stream_length(&r.db) > length);
    length = db_stream_length(&r.db);
    CHECK(db_set_reclaim_internal_fraction(&r.db, 0.1, &e) == ERR_OK);
    CHECK_EQ(db_stream_length(&r.db), length);
    settings_kv(&r, kv, sizeof kv);
    CHECK(strcmp(kv, "retain=30000000\nfraction=6554\n") == 0);
    close_rdb(&r);
    CHECK_MEM_ZERO(&r.m);
}

/* DbTesterRestart.testReclaimSettingsKeptAcrossRestart (015-87): the
 * fraction is kept across a restart, and so is the retain duration forever
 * after a finite one (the KV holds both, whatever was set last). */
TEST(reclaim_settings_kept_across_restart) {
    struct rdb r;
    struct err e;
    char dir[1024];
    mem_init(&r.m);
    rs_temp_dir(dir, sizeof dir);
    REQUIRE(dir[0] != '\0');
    r.time = 0;
    REQUIRE(rdb_start(&r, dir, 30, 50000000, 0, &e) == ERR_OK);
    r.time = 10;
    REQUIRE(db_set_reclaim_internal_fraction(&r.db, 0.001, &e) == ERR_OK);
    REQUIRE(rdb_restart(&r, dir, 30, 50000000, 0, &e) == ERR_OK);
    CHECK_EQ(r.db.reclaim.internalFraction, 66);
    CHECK_EQ(r.db.reclaim.retainDuration, INT64_MAX);
    REQUIRE(db_set_retain_duration(&r.db, 2 * CLK_UNITS_PER_SEC, &e) == ERR_OK);
    REQUIRE(db_set_retain_duration(&r.db, INT64_MAX, &e) == ERR_OK);
    REQUIRE(rdb_restart(&r, dir, 30, 50000000, 0, &e) == ERR_OK);
    CHECK_EQ(r.db.reclaim.internalFraction, 66);
    CHECK_EQ(r.db.reclaim.retainDuration, INT64_MAX);
    close_rdb(&r);
    CHECK_MEM_ZERO(&r.m);
    rs_remove_dir(dir);
}

/* DbTesterRestart.testReclaimSettingsSurviveCuts (015-87, 005-78 Q6): the
 * settings' KV, written once at the start of the stream, survives reclaim's
 * cuts (the steps rewrite it as any live value): found after three cuts or
 * more, past its record, and a restart on the cut stream finds it and goes
 * on cutting. The directory cuts whole files. */
TEST(reclaim_settings_survive_cuts) {
    struct rdb r;
    struct err e;
    char dir[1024];
    char kv[RC_SETTINGS_TEXT_CAP];
    mem_init(&r.m);
    rs_temp_dir(dir, sizeof dir);
    REQUIRE(dir[0] != '\0');
    r.time = CLK_UNITS_PER_SEC;
    REQUIRE(rdb_start(&r, dir, 8, 1000, 0, &e) == ERR_OK);
    REQUIRE(db_set_retain_duration(&r.db, CLK_UNITS_PER_SEC, &e) == ERR_OK);
    const int64_t settingsEnd = db_stream_length(&r.db);
    uint64_t rnd = 2;
    int i = 0;
    int cuts = 0;
    int64_t firstPos = stream_first_pos(&r.db.stream);
    while (cuts < 3 || firstPos <= settingsEnd || i < 1000) {
        REQUIRE(i < 20000);
        i++;
        r.time = CLK_UNITS_PER_SEC + i * CLK_UNITS_PER_SEC / 10;
        char key[32];
        char v[32];
        snprintf(key, sizeof key, "/k/%d", test_random_below(&rnd, 100));
        snprintf(v, sizeof v, "v%d", i);
        REQUIRE(rdb_put(&r, key, (const uint8_t *) v, (int32_t) strlen(v), NULL) == ERR_OK);
        if (stream_first_pos(&r.db.stream) != firstPos) {
            cuts++;
            firstPos = stream_first_pos(&r.db.stream);
        }
    }
    CHECK(stream_first_pos(&r.db.stream) > settingsEnd);
    settings_kv(&r, kv, sizeof kv);
    CHECK(strcmp(kv, "retain=10000000\nfraction=16384\n") == 0);
    REQUIRE(rdb_restart(&r, dir, 8, 1000, 0, &e) == ERR_OK);
    CHECK_EQ(r.db.reclaim.retainDuration, CLK_UNITS_PER_SEC);
    const int64_t firstPosAtRestart = stream_first_pos(&r.db.stream);
    for (int k = 0; k < 4000 && stream_first_pos(&r.db.stream) == firstPosAtRestart; k++) {
        i++;
        r.time = CLK_UNITS_PER_SEC + i * CLK_UNITS_PER_SEC / 10;
        char key[32];
        char v[32];
        snprintf(key, sizeof key, "/k/%d", test_random_below(&rnd, 100));
        snprintf(v, sizeof v, "v%d", i);
        REQUIRE(rdb_put(&r, key, (const uint8_t *) v, (int32_t) strlen(v), NULL) == ERR_OK);
    }
    CHECK(stream_first_pos(&r.db.stream) > firstPosAtRestart);
    settings_kv(&r, kv, sizeof kv);
    CHECK(strcmp(kv, "retain=10000000\nfraction=16384\n") == 0);
    close_rdb(&r);
    CHECK_MEM_ZERO(&r.m);
    rs_remove_dir(dir);
}

/* DbTesterRestart.testStreamWithoutSettingsHasDefaults (015-87, F5's option
 * 1): a database whose settings were never set has no settings' KV, and a
 * start on its stream runs with the defaults, forever and 16,384 units. */
TEST(reclaim_settings_none_defaults) {
    struct rdb r;
    struct err e;
    char dir[1024];
    char kv[RC_SETTINGS_TEXT_CAP];
    mem_init(&r.m);
    rs_temp_dir(dir, sizeof dir);
    REQUIRE(dir[0] != '\0');
    r.time = 0;
    REQUIRE(rdb_start(&r, dir, 30, 50000000, 0, &e) == ERR_OK);
    for (int i = 1; i <= 20; i++) {
        r.time = 10 * i;
        char key[32];
        snprintf(key, sizeof key, "/k/%d", i);
        REQUIRE(rdb_put(&r, key, (const uint8_t *) "v", 1, NULL) == ERR_OK);
    }
    settings_kv(&r, kv, sizeof kv);
    CHECK(strcmp(kv, "") == 0);
    REQUIRE(rdb_restart(&r, dir, 30, 50000000, 0, &e) == ERR_OK);
    settings_kv(&r, kv, sizeof kv);
    CHECK(strcmp(kv, "") == 0);
    CHECK_EQ(r.db.reclaim.retainDuration, INT64_MAX);
    CHECK_EQ(r.db.reclaim.internalFraction, RC_DEFAULT_INTERNAL_FRACTION);
    close_rdb(&r);
    CHECK_MEM_ZERO(&r.m);
    rs_remove_dir(dir);
}

/* DbTesterRestart.testMalformedSettingsRefusedAtStart (015-87): a start
 * refuses a settings' KV in another form than the one the setters write,
 * "InternalDataException" (ERR_FORMAT) naming the key, as it refuses a bad
 * table: a number that is not one, or out of range; a line missing, of its
 * own, or out of order; a sign, a leading zero, or no newline at the end.
 * The KV is put by an internal transaction; the well-formed value starts. */
TEST(reclaim_settings_malformed_refused_at_start) {
    static const char *const bad[] = {
        "retain=x\nfraction=16384\n",
        "retain=9999999\nfraction=16384\n",
        "retain=10000000\nfraction=65\n",
        "retain=10000000\nfraction=58983\n",
        "retain=10000000\n",
        "fraction=16384\n",
        "",
        "retain=10000000\nfraction=16384\nother=1\n",
        "fraction=16384\nretain=10000000\n",
        "retain=+10000000\nfraction=16384\n",
        "retain=010000000\nfraction=16384\n",
        "retain=10000000\nfraction=16384",
        "retain=10000000\r\nfraction=16384\r\n",
    };
    const char *good = "retain=10000000\nfraction=16384\n";
    const int nbad = (int) (sizeof bad / sizeof bad[0]);
    for (int i = -1; i < nbad; i++) {
        struct rdb r;
        struct err e;
        char dir[1024];
        mem_init(&r.m);
        rs_temp_dir(dir, sizeof dir);
        REQUIRE(dir[0] != '\0');
        r.time = 0;
        REQUIRE(rdb_start(&r, dir, 30, 50000000, 0, &e) == ERR_OK);
        r.time = 10;
        REQUIRE(rdb_put_internal(&r, RC_SETTINGS_KEY_NAME, i < 0 ? good : bad[i]) == ERR_OK);
        REQUIRE(db_close(&r.db, &e) == ERR_OK);
        enum err_code rc = rdb_start(&r, dir, 30, 50000000, 0, &e);
        if (i < 0) {
            CHECK_EQ(rc, ERR_OK);
            if (rc == ERR_OK) {
                CHECK_EQ(r.db.reclaim.retainDuration, CLK_UNITS_PER_SEC);
                close_rdb(&r);
            }
        } else {
            CHECK_EQ(rc, ERR_FORMAT);
            CHECK(strcmp(e.java, "InternalDataException") == 0);
            CHECK(strncmp(e.text, "Bad value of /#i/dreclaim/-settings.txt, reclaim's settings: "
                    "not the two lines retain=<time units> and fraction=<units of 2^-16>, in "
                    "range, that this version writes (bergdb 015-87): '", 177) == 0);
            if (rc == ERR_OK) {
                close_rdb(&r);
            }
        }
        CHECK_MEM_ZERO(&r.m);
        rs_remove_dir(dir);
    }
}

/* Reclaim.Tester.testSafePosAfterTheCallsRecords (015-54, 016-06 R7-F5):
 * pSafe is the stream length when it is set, after the internal records
 * that the same call appended before it (the table of an iteration
 * started, a step, the table of the iteration done): at least past the
 * user record's end when the call made such a record, and never past the
 * stream's length. Five markings in calls that made a step are checked. */
TEST(reclaim_safe_pos_after_the_calls_records) {
    struct rdb r;
    mem_init(&r.m);
    r.time = CLK_UNITS_PER_SEC;
    REQUIRE(rdb_open(&r, 30, 2000, 0, CLK_UNITS_PER_SEC) == ERR_OK);
    uint64_t rnd = 1;
    int64_t marked[512];            /* the pStart of each row marked, its identity */
    int nmarked = 0;
    int markings = 0, afterRecords = 0;
    for (int i = 0; i < 4000 && afterRecords < 5; i++) {
        r.time += CLK_UNITS_PER_SEC / 20;
        const int64_t steps = r.db.reclaim.steps;
        const int32_t rows = r.db.reclaim.nrows;
        uint8_t v[64];
        int32_t len = 1 + test_random_below(&rnd, 60);
        memset(v, 0, (size_t) len);
        char key[32];
        snprintf(key, sizeof key, "/k/%d", test_random_below(&rnd, 50));
        struct trans t;
        REQUIRE(rdb_put(&r, key, v, len, &t) == ERR_OK);
        /* The call's records before the marking: a step's, or the table of
         * an iteration it started. */
        const bool records = r.db.reclaim.steps > steps || r.db.reclaim.nrows > rows;
        const int64_t atLeast = t.next_pos + (records ? 1 : 0);
        for (int32_t k = 0; k < r.db.reclaim.nrows; k++) {
            const struct rc_row *row = &r.db.reclaim.rows[k];
            bool seen = false;
            for (int j = 0; j < nmarked && !seen; j++) {
                seen = marked[j] == row->pStart;
            }
            if (row->pSafe != -1 && !seen && nmarked < 512) {
                marked[nmarked++] = row->pStart;
                markings++;
                if (records) {
                    afterRecords++;
                }
                CHECK(row->pSafe >= atLeast);
                CHECK(row->pSafe <= db_stream_length(&r.db));
            }
        }
    }
    CHECK(afterRecords >= 5);
    CHECK(markings >= afterRecords);
    close_rdb(&r);
    CHECK_MEM_ZERO(&r.m);
}

/* Reclaim.Tester.testStepWithinValueLimit (015-50, 016-06 R7-F1), the
 * record limit lowered to 100 kB: ten old values of 4 kB, then /b, whose
 * node takes the value limit minus slack bytes (a step's scan takes the
 * last of the ten and /b), with slack 1000 and 0 (alone with the step's row
 * it passes the limit). The steps end before a value that would take them
 * past the limit, so the puts go on, reclaim cuts past /b's record three
 * times, and a restart reads every value. Before: "The transaction is too
 * large", the database failed. */
static void step_within_value_limit(int64_t slack) {
    struct rdb r;
    struct err e;
    char dir[1024];
    mem_init(&r.m);
    rs_temp_dir(dir, sizeof dir);
    REQUIRE(dir[0] != '\0');
    const int64_t recordLimit = 100 * 1000;
    r.time = CLK_UNITS_PER_SEC;
    REQUIRE(rdb_start(&r, dir, 30, 2000, recordLimit, &e) == ERR_OK);
    const int64_t limit = db_value_limit(&r.db);
    CHECK_EQ(limit, 87500);
    REQUIRE(db_set_retain_duration(&r.db, CLK_UNITS_PER_SEC, &e) == ERR_OK);
    static uint8_t zeros[100000];
    for (int i = 0; i < 10; i++) {
        r.time += CLK_UNITS_PER_SEC / 20;
        char key[32];
        snprintf(key, sizeof key, "/a/%d", i);
        REQUIRE(rdb_put(&r, key, zeros, 4000, NULL) == ERR_OK);
    }
    int64_t seg[8];
    int32_t key_n;
    ikey_segments("/b", seg, &key_n);
    int32_t n = (int32_t) (limit - slack);
    while (nw_value_byte_size_long(n, key_n) > limit - slack) {
        n--;
    }
    r.time += CLK_UNITS_PER_SEC / 20;
    REQUIRE(rdb_put(&r, "/b", zeros, n, NULL) == ERR_OK);
    const int64_t bEnd = db_stream_length(&r.db);
    uint64_t rnd = 1;
    int64_t cut = 0;
    int cuts = 0;
    for (int i = 0; i < 4000 && cuts < 3; i++) {
        r.time += CLK_UNITS_PER_SEC / 20;
        char key[32];
        snprintf(key, sizeof key, "/k/%d", test_random_below(&rnd, 50));
        REQUIRE(rdb_put(&r, key, zeros, 1 + test_random_below(&rnd, 60), NULL) == ERR_OK);
        if (db_first_available_pos(&r.db) > cut) {
            cut = db_first_available_pos(&r.db);
            cuts++;
        }
    }
    CHECK(cuts >= 3);
    CHECK(cut > bEnd);
    REQUIRE(rdb_restart(&r, dir, 30, 2000, recordLimit, &e) == ERR_OK);
    for (int j = 0; j < 20; j++) {
        r.time += CLK_UNITS_PER_SEC / 20;
        char key[32];
        snprintf(key, sizeof key, "/k/%d", j);
        REQUIRE(rdb_put(&r, key, zeros, 10, NULL) == ERR_OK);
    }
    int32_t len;
    CHECK(rdb_get(&r, INT64_MAX, "/b", NULL, &len, NULL) == ERR_OK);
    CHECK_EQ(len, n);
    for (int i = 0; i < 10; i++) {
        char key[32];
        snprintf(key, sizeof key, "/a/%d", i);
        CHECK(rdb_get(&r, INT64_MAX, key, NULL, &len, NULL) == ERR_OK);
        CHECK_EQ(len, 4000);
    }
    close_rdb(&r);
    CHECK_MEM_ZERO(&r.m);
    rs_remove_dir(dir);
}

TEST(reclaim_step_within_value_limit) {
    step_within_value_limit(1000);
    step_within_value_limit(0);
}

/* Reclaim.Tester.testUserTransactionLeavesTimesForReclaim (015-55, 016-06
 * R7-F6): a user transaction at the last database time was taken, and the
 * reclaim step it allowed found no time left, inside its go point: the
 * database failed. Now a user transaction after DBCLOCK_LAST_USER_TIME is
 * refused before its go point and the database goes on; one at it is
 * taken, and its step runs in the times kept for it. The clock can go
 * back, as CoreTestClock cannot. */
TEST(reclaim_user_transaction_leaves_times) {
    struct rdb r;
    struct err e;
    mem_init(&r.m);
    r.time = CLK_UNITS_PER_SEC;
    REQUIRE(rdb_start(&r, NULL, 30, 2000, 0, &e) == ERR_OK);
    REQUIRE(db_set_retain_duration(&r.db, CLK_UNITS_PER_SEC, &e) == ERR_OK);
    uint64_t rnd = 1;
    bool armed = false;
    uint8_t zeros[64];
    memset(zeros, 0, sizeof zeros);
    for (int i = 0; i < 4000 && !armed; i++) {
        r.time += CLK_UNITS_PER_SEC / 20;
        const struct reclaim *rc = &r.db.reclaim;
        const struct rc_row *cur = rc->nrows > 0 && !rc->rows[rc->nrows - 1].done
                ? &rc->rows[rc->nrows - 1] : NULL;
        armed = cur != NULL && rc_fraction_of(db_stream_length(&r.db) + 150 - cur->pStart,
                RC_DEFAULT_INTERNAL_FRACTION) - cur->rewritten > 10000;
        if (!armed) {
            char key[32];
            snprintf(key, sizeof key, "/k/%d", test_random_below(&rnd, 50));
            REQUIRE(rdb_put(&r, key, zeros, 1 + test_random_below(&rnd, 60), NULL) == ERR_OK);
        }
    }
    REQUIRE(armed);

    /* The next put makes a step. At Klong.MAX_TIME it is refused before its
     * go point, and the database goes on. */
    r.time = KL_MAX_TIME;
    int64_t length = db_stream_length(&r.db);
    CHECK_EQ(rdb_put(&r, "/last", (const uint8_t *) "a", 1, NULL), ERR_LIMIT);
    CHECK_EQ((int) r.db.state, (int) DB_ACTIVE);
    CHECK_EQ(db_stream_length(&r.db), length);
    int32_t len;
    CHECK(rdb_get(&r, INT64_MAX, "/last", NULL, &len, NULL) == ERR_OK);
    CHECK_EQ(len, -1);

    /* At the last user time it is taken, and its step has times after it. */
    r.time = DBCLOCK_LAST_USER_TIME;
    const int64_t count = r.db.transaction_count;
    struct trans t;
    CHECK_EQ(rdb_put(&r, "/last", (const uint8_t *) "b", 1, &t), ERR_OK);
    CHECK_EQ(t.tt, DBCLOCK_LAST_USER_TIME);
    CHECK(r.db.transaction_count > count + 1);
    uint8_t v[8];
    CHECK(rdb_get(&r, INT64_MAX, "/last", v, &len, NULL) == ERR_OK);
    CHECK(len == 1 && v[0] == 'b');
    close_rdb(&r);
    CHECK_MEM_ZERO(&r.m);
}

/* ======== ReclaimRetentionTester: the retain duration changed (011-04, W2) ======== */

/* What must hold whatever the changes (ReclaimRetentionTester's class
 * comment): (1) every cut keeps the guarantee of the retain duration in
 * force when it was decided, tEnd < the decision's time - retain; (2) the
 * first available lookup time never moves back, also not over a restart;
 * (3) every lookup from it on gives what the model says, before and after a
 * restart; (4) a lookup before it is refused. A run: a database in a
 * directory (for the restarts), node size 8, startup distance 2000, a put
 * of one of 50 keys every 1/20 s. Java syncs after one put in ten, so that
 * its storage thread makes the decided cuts; C forces and cuts in the call
 * that decides a cut (c/readme.md, section 9, point 9), so the run does not
 * sync. A cut is seen as a larger first available position after a put:
 * C decides cuts only there (pretruncate_if_possible, at the put's time). */
#define RR_CUTS 256

struct rrun {
    struct rdb r;
    char dir[1024];
    struct model *mo;
    uint64_t rnd;
    int64_t cutTEnd[RR_CUTS];       /* the decided cuts: tEnd, the time, the retain duration */
    int64_t cutTime[RR_CUTS];
    int64_t cutRetain[RR_CUTS];
    int ncuts;
    int sessionCuts;                /* decided since the last start (Java's stats.cuts) */
    int64_t lastFirstPos;
    int64_t maxFirst;               /* the largest first available time seen, over restarts */
};

/* Run.start: the database in run->dir started, the retain duration set, and
 * the first available time not before the largest seen. */
static bool rr_start(struct rrun *run, int64_t retain) {
    struct err e;
    if (rdb_start(&run->r, run->dir, 8, 2000, 0, &e) != ERR_OK) {
        return false;
    }
    if (db_set_retain_duration(&run->r.db, retain, &e) != ERR_OK) {
        return false;
    }
    CHECK(db_first_available_time(&run->r.db) >= run->maxFirst);
    run->sessionCuts = 0;
    run->lastFirstPos = db_first_available_pos(&run->r.db);
    return true;
}

static bool rr_open(struct rrun *run, uint64_t seed, int64_t retain) {
    static struct model mo;
    memset(run, 0, sizeof *run);
    memset(&mo, 0, sizeof mo);
    run->mo = &mo;
    run->rnd = seed;
    mem_init(&run->r.m);
    run->r.time = CLK_UNITS_PER_SEC;
    rs_temp_dir(run->dir, sizeof run->dir);
    return run->dir[0] != '\0' && rr_start(run, retain);
}

/* Run.restart: the close (which writes and forces all) and a start with
 * another retain duration. */
static bool rr_restart(struct rrun *run, int64_t retain) {
    struct err e;
    CHECK_EQ(db_recount(&run->r.db), 0);
    if (db_close(&run->r.db, &e) != ERR_OK) {
        return false;
    }
    return rr_start(run, retain);
}

/* Run.put: one put, in the model; a cut decided in its call noted. */
static bool rr_put(struct rrun *run) {
    struct rdb *r = &run->r;
    r->time += CLK_UNITS_PER_SEC / 20;
    int k = test_random_below(&run->rnd, MK);
    char key[32];
    snprintf(key, sizeof key, "/k/%d", k);
    uint8_t v[32];
    int32_t len = 1 + test_random_below(&run->rnd, 30);
    for (int j = 0; j < len; j++) {
        v[j] = (uint8_t) test_random(&run->rnd);
    }
    struct trans t;
    if (rdb_put(r, key, v, len, &t) != ERR_OK || run->mo->n[k] >= MV) {
        return false;
    }
    struct model *mo = run->mo;
    mo->times[k][mo->n[k]] = t.tt;
    memcpy(mo->vals[k][mo->n[k]], v, (size_t) len);
    mo->lens[k][mo->n[k]] = len;
    mo->n[k]++;
    if (db_first_available_pos(&r->db) > run->lastFirstPos && run->ncuts < RR_CUTS) {
        run->lastFirstPos = db_first_available_pos(&r->db);
        run->cutTEnd[run->ncuts] = db_first_available_time(&r->db);
        run->cutTime[run->ncuts] = t.tt;
        run->cutRetain[run->ncuts] = r->db.reclaim.retainDuration;
        run->ncuts++;
        run->sessionCuts++;
        CHECK_EQ(r->db.reclaim.pendingCut, -1);    /* made in the call (section 9, point 9) */
    }
    return true;
}

static bool rr_puts(struct rrun *run, int n) {
    for (int i = 0; i < n; i++) {
        if (!rr_put(run)) {
            return false;
        }
    }
    return true;
}

/* Run.putUntilCuts: puts until at least cuts cuts were decided since the
 * last start; at most max puts. */
static bool rr_put_until_cuts(struct rrun *run, int cuts, int max) {
    for (int i = 0; i < max && run->sessionCuts < cuts; i++) {
        if (!rr_put(run)) {
            return false;
        }
    }
    return run->sessionCuts >= cuts;
}

/* The iteration in progress (Reclaim.currentIteration), or NULL. */
static const struct rc_row *rr_current(const struct rrun *run) {
    const struct reclaim *rc = &run->r.db.reclaim;
    return rc->nrows > 0 && !rc->rows[rc->nrows - 1].done ? &rc->rows[rc->nrows - 1] : NULL;
}

/* Run.check: (1) to (4). The lookups at about 200 times from the first
 * available time on (Java: every 1/7 s). */
static void rr_check(struct rrun *run) {
    struct rdb *r = &run->r;
    for (int i = 0; i < run->ncuts; i++) {
        CHECK(run->cutRetain[i] != INT64_MAX);
        CHECK(run->cutTEnd[i] < run->cutTime[i] - run->cutRetain[i]);
    }
    const int64_t first = db_first_available_time(&r->db);
    CHECK(first >= run->maxFirst);
    run->maxFirst = first;
    const int64_t from = first > 1 ? first : 1;
    int64_t step = (r->time - from) / 200;
    if (step < CLK_UNITS_PER_SEC / 7) {
        step = CLK_UNITS_PER_SEC / 7;
    }
    for (int k = 0; k < MK; k++) {
        const struct model *mo = run->mo;
        if (mo->n[k] == 0) {
            continue;
        }
        char key[32];
        snprintf(key, sizeof key, "/k/%d", k);
        uint8_t v[64];
        int32_t len;
        REQUIRE(rdb_get(r, INT64_MAX, key, v, &len, NULL) == ERR_OK);
        const int32_t last = mo->n[k] - 1;
        CHECK_EQ(len, mo->lens[k][last]);
        CHECK(len < 0 || memcmp(v, mo->vals[k][last], (size_t) len) == 0);
        for (int64_t lt = from; lt <= r->time; lt += step) {
            REQUIRE(rdb_get(r, lt, key, v, &len, NULL) == ERR_OK);
            const int32_t i = model_floor(mo, k, lt);
            if (i < 0) {
                CHECK_EQ(len, -1);
            } else {
                CHECK_EQ(len, mo->lens[k][i]);
                CHECK(len < 0 || memcmp(v, mo->vals[k][i], (size_t) len) == 0);
            }
        }
    }
    if (first > 0) {
        int32_t len;
        CHECK(rdb_get(r, first - 1, "/k/0", NULL, &len, NULL) == ERR_NOT_AVAILABLE);
    }
}

static void rr_close(struct rrun *run) {
    close_rdb(&run->r);
    CHECK_MEM_ZERO(&run->r.m);
    rs_remove_dir(run->dir);
}

/* ReclaimRetentionTester.testShrinkDuringIteration: a smaller retain
 * duration while an iteration runs; the cut that follows is decided with
 * the new duration. */
TEST(reclaim_retention_shrink_during_iteration) {
    struct rrun run;
    REQUIRE(rr_open(&run, 1, 4 * CLK_UNITS_PER_SEC));
    for (int i = 0; i < 5000 && rr_current(&run) == NULL; i++) {
        REQUIRE(rr_put(&run));
    }
    REQUIRE(rr_current(&run) != NULL);
    CHECK_EQ(run.ncuts, 0);
    struct err e;
    REQUIRE(db_set_retain_duration(&run.r.db, CLK_UNITS_PER_SEC, &e) == ERR_OK);
    REQUIRE(rr_put_until_cuts(&run, 1, 20000));
    CHECK_EQ(run.cutRetain[0], CLK_UNITS_PER_SEC);
    rr_check(&run);
    REQUIRE(rr_restart(&run, CLK_UNITS_PER_SEC));
    rr_check(&run);
    rr_close(&run);
}

/* ReclaimRetentionTester.testShrinkMakesSeveralRowsCuttable: done
 * iterations wait for the cut under a long duration (40 s); a short one
 * makes them all cuttable at once. The newest is chosen, and its
 * conditions still hold: here the second of three done rows (the third
 * ended too recently and is not safe yet), not the first, and the rows
 * before it are gone. */
TEST(reclaim_retention_shrink_makes_rows_cuttable) {
    struct rrun run;
    REQUIRE(rr_open(&run, 2, 40 * CLK_UNITS_PER_SEC));
    for (int i = 0; i < 6000 && run.r.db.reclaim.iterationCount < 3; i++) {
        REQUIRE(rr_put(&run));
    }
    REQUIRE(run.r.db.reclaim.iterationCount >= 3);
    CHECK_EQ(run.ncuts, 0);
    const int64_t oldestDone = run.r.db.reclaim.rows[0].pStart;
    CHECK(run.r.db.reclaim.rows[0].done && run.r.db.reclaim.rows[1].done);
    struct err e;
    REQUIRE(db_set_retain_duration(&run.r.db, CLK_UNITS_PER_SEC, &e) == ERR_OK);
    REQUIRE(rr_put_until_cuts(&run, 1, 20000));
    REQUIRE(run.r.db.reclaim.nrows > 0);
    CHECK(run.r.db.reclaim.rows[0].cut);
    CHECK(run.r.db.reclaim.rows[0].pStart > oldestDone);
    rr_check(&run);
    REQUIRE(rr_restart(&run, CLK_UNITS_PER_SEC));
    REQUIRE(rr_puts(&run, 500));
    rr_check(&run);
    rr_close(&run);
}

/* ReclaimRetentionTester.testGrowWithPendingCut, in C's terms: a larger
 * retain duration (100 s) right after the call that decided a cut. Java's
 * cut is then pending, made at a later transaction once the stream is
 * durable; C made it in the deciding call (c/readme.md, section 9, point
 * 9; a cut pending at an open: f_reclaim.c's
 * api_reclaim_pending_cut_at_open). What Java checks holds: the first
 * available time does not move back, no new cut comes for a while with
 * the longer duration, and the data stays, also after a restart. */
TEST(reclaim_retention_grow_after_cut) {
    struct rrun run;
    REQUIRE(rr_open(&run, 3, CLK_UNITS_PER_SEC));
    REQUIRE(rr_put_until_cuts(&run, 2, 20000));
    const int64_t first = db_first_available_time(&run.r.db);
    const int64_t firstPos = db_first_available_pos(&run.r.db);
    struct err e;
    REQUIRE(db_set_retain_duration(&run.r.db, 100 * CLK_UNITS_PER_SEC, &e) == ERR_OK);
    CHECK_EQ(db_first_available_time(&run.r.db), first);
    rr_check(&run);
    const int cuts = run.ncuts;
    REQUIRE(rr_puts(&run, 500));
    CHECK_EQ(run.ncuts, cuts);
    CHECK_EQ(db_first_available_time(&run.r.db), first);
    CHECK_EQ(db_first_available_pos(&run.r.db), firstPos);
    rr_check(&run);
    REQUIRE(rr_restart(&run, 100 * CLK_UNITS_PER_SEC));
    CHECK_EQ(db_first_available_time(&run.r.db), first);
    rr_check(&run);
    rr_close(&run);
}

/* ReclaimRetentionTester.testRestartWithOtherRetention: a restart with
 * another retain duration is the same as changing it: after cuts, forever,
 * and then a short one again. */
TEST(reclaim_retention_restart_with_other) {
    struct rrun run;
    REQUIRE(rr_open(&run, 4, CLK_UNITS_PER_SEC));
    REQUIRE(rr_put_until_cuts(&run, 2, 20000));
    rr_check(&run);
    const int64_t first = db_first_available_time(&run.r.db);
    CHECK(first > 0);

    REQUIRE(rr_restart(&run, INT64_MAX));
    CHECK_EQ(db_first_available_time(&run.r.db), first);
    rr_check(&run);
    REQUIRE(rr_puts(&run, 1000));
    CHECK_EQ(run.sessionCuts, 0);
    CHECK_EQ(db_first_available_time(&run.r.db), first);
    rr_check(&run);

    REQUIRE(rr_restart(&run, 2 * CLK_UNITS_PER_SEC));
    CHECK_EQ(db_first_available_time(&run.r.db), first);
    REQUIRE(rr_put_until_cuts(&run, 1, 30000));
    CHECK(db_first_available_time(&run.r.db) > first);
    rr_check(&run);

    REQUIRE(rr_restart(&run, 5 * CLK_UNITS_PER_SEC));
    REQUIRE(rr_puts(&run, 300));
    rr_check(&run);
    rr_close(&run);
}

/* ReclaimRetentionTester.testForeverThenFinite: a long history made with
 * forever; then a finite duration starts reclaim. */
TEST(reclaim_retention_forever_then_finite) {
    struct rrun run;
    REQUIRE(rr_open(&run, 5, INT64_MAX));
    REQUIRE(rr_puts(&run, 3000));
    CHECK_EQ(db_first_available_time(&run.r.db), 0);
    CHECK_EQ(run.r.db.reclaim.iterationCount, 0);
    CHECK_EQ(run.r.db.reclaim.nrows, 0);
    struct err e;
    REQUIRE(db_set_retain_duration(&run.r.db, CLK_UNITS_PER_SEC, &e) == ERR_OK);
    REQUIRE(rr_put_until_cuts(&run, 1, 30000));
    rr_check(&run);
    REQUIRE(rr_restart(&run, CLK_UNITS_PER_SEC));
    rr_check(&run);
    rr_close(&run);
}

/* ReclaimRetentionTester.testFiniteThenForeverMidIteration: a finite
 * duration, then forever while an iteration runs: it ends, and no new one
 * starts. Back to a finite duration, the cuts go on. */
TEST(reclaim_retention_finite_then_forever_mid_iteration) {
    struct rrun run;
    REQUIRE(rr_open(&run, 6, 4 * CLK_UNITS_PER_SEC));
    for (int i = 0; i < 5000 && rr_current(&run) == NULL; i++) {
        REQUIRE(rr_put(&run));
    }
    REQUIRE(rr_current(&run) != NULL);
    struct err e;
    REQUIRE(db_set_retain_duration(&run.r.db, INT64_MAX, &e) == ERR_OK);
    REQUIRE(rr_puts(&run, 2000));
    const int64_t done = run.r.db.reclaim.iterationCount;
    CHECK(done >= 1);
    CHECK(rr_current(&run) == NULL);
    REQUIRE(rr_puts(&run, 2000));
    CHECK_EQ(run.r.db.reclaim.iterationCount, done);
    CHECK_EQ(run.ncuts, 0);
    rr_check(&run);
    REQUIRE(db_set_retain_duration(&run.r.db, CLK_UNITS_PER_SEC, &e) == ERR_OK);
    REQUIRE(rr_put_until_cuts(&run, 1, 30000));
    rr_check(&run);
    REQUIRE(rr_restart(&run, CLK_UNITS_PER_SEC));
    rr_check(&run);
    rr_close(&run);
}

/* ======== Reclaim.Tester's tests with restarts (startForCutTest) ======== */

/* Starts r's database in dir (NULL: in memory) as Reclaim.Tester's
 * startForCutTest: node size 8, startup distance 2000, and the retain
 * duration 1 s set after the start (a record only when not in force). */
static enum err_code cut_start(struct rdb *r, const char *dir) {
    struct err e;
    enum err_code rc = rdb_start(r, dir, 8, 2000, 0, &e);
    if (rc == ERR_OK) {
        rc = db_set_retain_duration(&r->db, CLK_UNITS_PER_SEC, &e);
    }
    return rc;
}

/* A restart as Java's tests make one on a copy of the stream: the close
 * (which writes and forces all) and cut_start. */
static enum err_code cut_restart(struct rdb *r, const char *dir) {
    struct err e;
    CHECK_EQ(db_recount(&r->db), 0);
    enum err_code rc = db_close(&r->db, &e);
    return rc != ERR_OK ? rc : cut_start(r, dir);
}

/* A put of a random value (1 to max bytes) to /k/N, N below nkeys, at the
 * clock 1/20 s later; the key's number and the value into *k, v, *len. */
static enum err_code cut_put(struct rdb *r, uint64_t *rnd, int nkeys, int max, int *k,
        uint8_t *v, int32_t *len) {
    r->time += CLK_UNITS_PER_SEC / 20;
    *k = test_random_below(rnd, nkeys);
    *len = 1 + test_random_below(rnd, max);
    for (int32_t j = 0; j < *len; j++) {
        v[j] = (uint8_t) test_random(rnd);
    }
    char key[32];
    snprintf(key, sizeof key, "/k/%d", *k);
    return rdb_put(r, key, v, *len, NULL);
}

/* Each live value of /k/0 to /k/n-1 reads back at the latest time. */
static void check_live(struct rdb *r, int n, uint8_t (*vals)[64], const int32_t *lens) {
    for (int k = 0; k < n; k++) {
        if (lens[k] <= 0) {
            continue;
        }
        char key[32];
        snprintf(key, sizeof key, "/k/%d", k);
        uint8_t v[64];
        int32_t len;
        CHECK(rdb_get(r, INT64_MAX, key, v, &len, NULL) == ERR_OK);
        CHECK_EQ(len, lens[k]);
        CHECK(len != lens[k] || memcmp(v, vals[k], (size_t) len) == 0);
    }
}

/* Reclaim.Tester.testRestartAfterCut and testWritesAfterCut (bugs found
 * 2026-10-13 by ReclaimStress): a start after a cut, whose meta block before
 * the last transaction was cut away (the search for a meta block went down
 * to position 0), reads every live value; and the writes after it, whose
 * index nodes have dead pointers to versions below the cut in their
 * history (NodeCollection.resolvePointers read their headers), go on: 500
 * more puts, every value read back, and again after a second restart. In a
 * directory, whose physical cut is by whole files; the decided cut is the
 * first available position. */
TEST(reclaim_restart_after_cut) {
    struct rdb r;
    char dir[1024];
    static uint8_t vals[50][64];
    int32_t lens[50];
    memset(lens, 0, sizeof lens);
    mem_init(&r.m);
    rs_temp_dir(dir, sizeof dir);
    REQUIRE(dir[0] != '\0');
    r.time = CLK_UNITS_PER_SEC;
    REQUIRE(cut_start(&r, dir) == ERR_OK);
    uint64_t rnd = 2;
    for (int i = 0; i < 3000 && db_first_available_pos(&r.db) == 0; i++) {
        int k;
        uint8_t v[64];
        int32_t len;
        REQUIRE(cut_put(&r, &rnd, 50, 30, &k, v, &len) == ERR_OK);
        memcpy(vals[k], v, (size_t) len);
        lens[k] = len;
    }
    REQUIRE(db_first_available_pos(&r.db) > 0);
    REQUIRE(cut_restart(&r, dir) == ERR_OK);
    check_live(&r, 50, vals, lens);
    const int64_t firstPos = db_first_available_pos(&r.db);
    for (int i = 0; i < 500; i++) {
        int k;
        uint8_t v[64];
        int32_t len;
        REQUIRE(cut_put(&r, &rnd, 50, 30, &k, v, &len) == ERR_OK);
        memcpy(vals[k], v, (size_t) len);
        lens[k] = len;
    }
    CHECK(db_first_available_pos(&r.db) > firstPos);       /* cuts after the restart */
    check_live(&r, 50, vals, lens);
    REQUIRE(cut_restart(&r, dir) == ERR_OK);
    check_live(&r, 50, vals, lens);
    close_rdb(&r);
    CHECK_MEM_ZERO(&r.m);
    rs_remove_dir(dir);
}

/* Reclaim.Tester.testFirstAvailableTimeAfterRestart (a bug found 2026-10-13
 * by ReclaimStress): after a restart the first available lookup time was
 * taken from the last completed iteration, also when the stream had not
 * been cut there yet, and lookups in the retention window failed. Five
 * restarts, each right after an iteration is done (it is not yet cut
 * there): the first available time is the one before the restart, a lookup
 * at it is answered and one before it refused. */
TEST(reclaim_first_available_time_after_restart) {
    struct rdb r;
    char dir[1024];
    mem_init(&r.m);
    rs_temp_dir(dir, sizeof dir);
    REQUIRE(dir[0] != '\0');
    r.time = CLK_UNITS_PER_SEC;
    REQUIRE(cut_start(&r, dir) == ERR_OK);
    uint64_t rnd = 3;
    int restarts = 0;
    for (int i = 1; i < 3000 && restarts < 5; i++) {
        int k;
        uint8_t v[64];
        int32_t len;
        REQUIRE(cut_put(&r, &rnd, 50, 30, &k, v, &len) == ERR_OK);
        if (r.db.reclaim.iterationCount > 0 && db_first_available_pos(&r.db) > 0) {
            const int64_t first = db_first_available_time(&r.db);
            const int64_t firstPos = db_first_available_pos(&r.db);
            REQUIRE(cut_restart(&r, dir) == ERR_OK);
            restarts++;
            CHECK_EQ(db_first_available_time(&r.db), first);
            CHECK_EQ(db_first_available_pos(&r.db), firstPos);
            CHECK(rdb_get(&r, first, "/k/1", NULL, &len, NULL) == ERR_OK);
            CHECK(rdb_get(&r, first - 1, "/k/1", NULL, &len, NULL) == ERR_NOT_AVAILABLE);
        }
    }
    CHECK(restarts >= 5);
    close_rdb(&r);
    CHECK_MEM_ZERO(&r.m);
    rs_remove_dir(dir);
}

/* A full scan at the latest time (DbUtil.checksum): the live values. */
static bool count_live(void *ctx, const struct kvt *kvt) {
    if (kvt->value->len >= 0) {
        (*(int *) ctx)++;
    }
    return true;
}

/* Reclaim.Tester.testDeletedKeysAfterCut (a bug found 2026-10-13 by
 * ReclaimStress, Q7 in 011-01): an iteration rewrote live values only, so
 * nodes that hold only deleted keys, and the segment subtrees of deleted
 * long keys, kept their versions below the cut, and lookups and scans still
 * passed through them. 100 keys and 100 long keys put and 60 of each
 * deleted, then puts to the others until three cuts; a scan and the gets of
 * the deleted keys. In memory, whose cut is exact (CutStream), and in a
 * directory with a restart from the cut stream. */
static void deleted_keys_after_cut(bool restart) {
    struct rdb r;
    char dir[1024] = "";
    mem_init(&r.m);
    if (restart) {
        rs_temp_dir(dir, sizeof dir);
        REQUIRE(dir[0] != '\0');
    }
    r.time = CLK_UNITS_PER_SEC;
    REQUIRE(cut_start(&r, restart ? dir : NULL) == ERR_OK);
    struct err e;
    for (int i = 0; i < 160; i++) {
        r.time += CLK_UNITS_PER_SEC / 20;
        char k1[32], k2[32];
        snprintf(k1, sizeof k1, "/k/%d", i % 100);
        snprintf(k2, sizeof k2, "/long/%d", i % 100);
        int64_t s1[8], s2[8];
        int32_t n1, n2;
        ikey_segments(k1, s1, &n1);
        ikey_segments(k2, s2, &n2);
        struct tr_builder b;
        struct trans t;
        tr_builder_init(&b, &r.m);
        tr_init(&t, &r.m);
        const uint8_t *v = i < 100 ? (const uint8_t *) "v" : NULL;     /* then deletes */
        const int32_t len = i < 100 ? 1 : -1;
        REQUIRE(tr_put_segments(&b, s1, n1, v, len, &e) == ERR_OK);
        REQUIRE(tr_put_segments(&b, s2, n2, v, len, &e) == ERR_OK);
        REQUIRE(tr_build(&b, &t, &e) == ERR_OK);
        REQUIRE(db_execute(&r.db, &t, &e) == ERR_OK);
        tr_free(&t);
        tr_builder_free(&b);
    }
    uint64_t rnd = 5;
    int64_t cut = 0;
    int cuts = 0;
    for (int i = 0; i < 4000 && cuts < 3; i++) {
        r.time += CLK_UNITS_PER_SEC / 20;
        char key[32], v[32];
        snprintf(key, sizeof key, "/k/%d", 60 + test_random_below(&rnd, 40));
        snprintf(v, sizeof v, "w%d", i);
        REQUIRE(rdb_put(&r, key, (const uint8_t *) v, (int32_t) strlen(v), NULL) == ERR_OK);
        if (db_first_available_pos(&r.db) > cut) {
            cut = db_first_available_pos(&r.db);
            cuts++;
        }
    }
    CHECK(cuts >= 3);
    if (!restart) {
        CHECK_EQ(stream_first_pos(&r.db.stream), cut);      /* the exact cut */
    } else {
        REQUIRE(cut_restart(&r, dir) == ERR_OK);
    }
    int live = 0;
    struct getmany g;
    db_new_get_many(&r.db, &g);
    g.result.add = count_live;
    g.result.ctx = &live;
    CHECK(db_get_many(&r.db, &g, &e) == ERR_OK);
    CHECK_EQ(live, 80 + 3);         /* and reclaim's table, current row and settings */
    for (int i = 0; i < 100; i++) {
        char k1[32], k2[32];
        snprintf(k1, sizeof k1, "/k/%d", i);
        snprintf(k2, sizeof k2, "/long/%d", i);
        int32_t len;
        CHECK(rdb_get(&r, INT64_MAX, k1, NULL, &len, NULL) == ERR_OK);
        CHECK(i < 60 ? len == -1 : len > 0);
        CHECK(rdb_get(&r, INT64_MAX, k2, NULL, &len, NULL) == ERR_OK);
        CHECK(i < 60 ? len == -1 : len == 1);
    }
    close_rdb(&r);
    CHECK_MEM_ZERO(&r.m);
    if (restart) {
        rs_remove_dir(dir);
    }
}

TEST(reclaim_deleted_keys_after_cut) {
    deleted_keys_after_cut(false);
    deleted_keys_after_cut(true);
}

/* Reclaim.Tester.testRestartResumesIteration (2026-10-13): steps store only
 * the row of the iteration (CURRENT_KEY_NAME), not the whole table, and a
 * restart resumes the iteration from that row. 3,000 keys loaded with
 * forever, so that the first iteration has steps; then the retain duration
 * 1 s and puts until three steps: the table's record stays the one that
 * started the iteration, and after a restart the iteration in progress is
 * the row as it was, byte for byte in its text. */
TEST(reclaim_restart_resumes_iteration) {
    struct rdb r;
    struct err e;
    char dir[1024];
    mem_init(&r.m);
    rs_temp_dir(dir, sizeof dir);
    REQUIRE(dir[0] != '\0');
    r.time = CLK_UNITS_PER_SEC;
    REQUIRE(cut_start(&r, dir) == ERR_OK);
    REQUIRE(db_set_retain_duration(&r.db, INT64_MAX, &e) == ERR_OK);
    static const uint8_t ten[10];
    for (int i = 0; i < 3000; i += 100) {
        r.time += CLK_UNITS_PER_SEC / 20;
        struct tr_builder b;
        struct trans t;
        tr_builder_init(&b, &r.m);
        tr_init(&t, &r.m);
        for (int j = i; j < i + 100; j++) {
            char key[32];
            int64_t seg[8];
            int32_t n;
            snprintf(key, sizeof key, "/k/%d", j);
            ikey_segments(key, seg, &n);
            REQUIRE(tr_put_segments(&b, seg, n, ten, 10, &e) == ERR_OK);
        }
        REQUIRE(tr_build(&b, &t, &e) == ERR_OK);
        REQUIRE(db_execute(&r.db, &t, &e) == ERR_OK);
        tr_free(&t);
        tr_builder_free(&b);
    }
    REQUIRE(db_set_retain_duration(&r.db, CLK_UNITS_PER_SEC, &e) == ERR_OK);
    uint64_t rnd = 4;
    int64_t tableTpos = -1;
    int steps = 0;
    static char before[4096];
    int64_t lastKey[64];
    int32_t lastKey_n = -1;
    before[0] = '\0';
    for (int i = 0; i < 5000 && steps < 3; i++) {
        int k;
        uint8_t v[64];
        int32_t len;
        REQUIRE(cut_put(&r, &rnd, 3000, 30, &k, v, &len) == ERR_OK);
        const struct reclaim *rc = &r.db.reclaim;
        const struct rc_row *cur = rc->nrows > 0 && !rc->rows[rc->nrows - 1].done
                ? &rc->rows[rc->nrows - 1] : NULL;
        if (cur == NULL) {
            /* The first iteration only: no other gets safe or cut (and stores
             * the table) while it runs. */
            CHECK_EQ(tableTpos, -1);
            continue;
        }
        int64_t tpos = -1;
        CHECK(rdb_get(&r, INT64_MAX, RC_TABLE_KEY_NAME, NULL, &len, &tpos) == ERR_OK);
        if (tableTpos == -1) {
            tableTpos = tpos;
        } else {
            CHECK_EQ(tpos, tableTpos);      /* the table was not stored by a step */
        }
        if (!cur->lastKeyNull && (cur->lastKey_n != lastKey_n
                || memcmp(cur->lastKey, lastKey, (size_t) lastKey_n * sizeof(int64_t)) != 0)) {
            steps++;
            REQUIRE(cur->lastKey_n <= 64);
            lastKey_n = cur->lastKey_n;
            memcpy(lastKey, cur->lastKey, (size_t) lastKey_n * sizeof(int64_t));
        }
        REQUIRE(rc_row_text_cap(cur) <= sizeof before);
        rc_row_text(cur, before, sizeof before);
    }
    CHECK(steps >= 3);
    REQUIRE(cut_restart(&r, dir) == ERR_OK);
    const struct reclaim *rc = &r.db.reclaim;
    REQUIRE(rc->nrows > 0 && !rc->rows[rc->nrows - 1].done);
    static char after[4096];
    REQUIRE(rc_row_text_cap(&rc->rows[rc->nrows - 1]) <= sizeof after);
    rc_row_text(&rc->rows[rc->nrows - 1], after, sizeof after);
    CHECK(strcmp(before, after) == 0);
    close_rdb(&r);
    CHECK_MEM_ZERO(&r.m);
    rs_remove_dir(dir);
}

/* Reclaim.Tester's distancePuts: the retain duration 1 s, count small puts
 * 1/20 s apart; each iteration that starts does so when the stream has grown
 * by more than twice the startup distance since the last one started.
 * Returns the iterations completed. */
static int64_t distance_puts(struct rdb *r, int count) {
    struct err e;
    if (db_set_retain_duration(&r->db, CLK_UNITS_PER_SEC, &e) != ERR_OK) {
        CHECK(0);
        return -1;
    }
    uint64_t rnd = 1;
    const int64_t before = r->db.reclaim.iterationCount;
    static const uint8_t zeros[64];
    for (int i = 0; i < count; i++) {
        r->time += CLK_UNITS_PER_SEC / 20;
        const struct reclaim *rc = &r->db.reclaim;
        const int64_t pStart = rc->nrows > 0 ? rc->rows[rc->nrows - 1].pStart : 0;
        char key[32];
        snprintf(key, sizeof key, "/k/%d", test_random_below(&rnd, 50));
        if (rdb_put(r, key, zeros, 1 + test_random_below(&rnd, 60), NULL) != ERR_OK) {
            CHECK(0);
            return -1;
        }
        const int64_t next = rc->nrows > 0 ? rc->rows[rc->nrows - 1].pStart : 0;
        if (next != pStart) {
            CHECK(next - pStart > INT64_C(2) * r->db.startup_distance);
        }
    }
    return r->db.reclaim.iterationCount - before;
}

/* Reclaim.Tester.testIterationsFollowTheStreamsStartupDistance (005-53,
 * question 3; fixed in 005-61): reclaim kept the builder's startup distance,
 * not the stream's that the start reads; a database made at 2000 bytes and
 * restarted with the default (50 MB) nearly stopped reclaiming. Restarted
 * with the default or with 2000, on copies of one directory, it reclaims
 * the same: the iterations and the stream's length from the first
 * available position. */
TEST(reclaim_iterations_follow_stream_distance) {
    struct rdb r;
    struct err e;
    char dir[1024], copy[1024], cmd[2200];
    mem_init(&r.m);
    rs_temp_dir(dir, sizeof dir);
    rs_temp_dir(copy, sizeof copy);
    REQUIRE(dir[0] != '\0' && copy[0] != '\0');
    r.time = CLK_UNITS_PER_SEC;
    REQUIRE(rdb_start(&r, dir, 30, 2000, 0, &e) == ERR_OK);
    distance_puts(&r, 300);
    REQUIRE(db_close(&r.db, &e) == ERR_OK);
    const int64_t t0 = r.time;
    int64_t iterations[2], length[2];
    for (int run = 0; run < 2; run++) {
        snprintf(cmd, sizeof cmd, "rm -rf '%s' && cp -R '%s' '%s'", copy, dir, copy);
        REQUIRE(system(cmd) == 0);
        r.time = t0;
        REQUIRE(rdb_start(&r, copy, 30, run == 0 ? 2000 : 50 * 1000 * 1000, 0, &e) == ERR_OK);
        CHECK_EQ(r.db.startup_distance, 2000);
        iterations[run] = distance_puts(&r, 800);
        length[run] = db_stream_length(&r.db) - db_first_available_pos(&r.db);
        close_rdb(&r);
    }
    printf("  reclaim_iterations_follow_stream_distance: %lld and %lld "
            "iterations\n", (long long) iterations[0], (long long) iterations[1]);
    CHECK(iterations[0] >= 10);
    CHECK_EQ(iterations[0], iterations[1]);
    CHECK_EQ(length[0], length[1]);
    CHECK_MEM_ZERO(&r.m);
    rs_remove_dir(dir);
    rs_remove_dir(copy);
}

/* Reclaim.Tester.testCutKeepsMetaBlockTransaction (a bug found 2026-10-13 by
 * ReclaimStress): a start after a cut failed when the last valid meta block
 * named a transaction before the cut, where recovery starts; the cut
 * checked only that the meta block itself came after the cut position.
 * Puts to five keys with a startup distance of 10,000 and a restart after
 * every cut; Java's f-test runs 20 seeds of 3,000 puts, here 3 seeds of
 * 1,500. */
TEST(reclaim_cut_keeps_meta_block_transaction) {
    int restarts = 0;
    for (uint64_t seed = 0; seed < 3; seed++) {
        struct rdb r;
        struct err e;
        char dir[1024];
        mem_init(&r.m);
        rs_temp_dir(dir, sizeof dir);
        REQUIRE(dir[0] != '\0');
        r.time = CLK_UNITS_PER_SEC;
        REQUIRE(rdb_start(&r, dir, 30, 10000, 0, &e) == ERR_OK);
        REQUIRE(db_set_retain_duration(&r.db, CLK_UNITS_PER_SEC, &e) == ERR_OK);
        uint64_t rnd = seed + 1;
        int64_t cut = 0;
        static const uint8_t zeros[64];
        for (int i = 0; i < 1500; i++) {
            r.time += CLK_UNITS_PER_SEC / 20;
            char key[32];
            snprintf(key, sizeof key, "/k/%d", test_random_below(&rnd, 5));
            REQUIRE(rdb_put(&r, key, zeros, 1 + test_random_below(&rnd, 60), NULL) == ERR_OK);
            if (db_first_available_pos(&r.db) > cut) {
                cut = db_first_available_pos(&r.db);
                REQUIRE(db_close(&r.db, &e) == ERR_OK);
                REQUIRE(rdb_start(&r, dir, 30, 10000, 0, &e) == ERR_OK);
                CHECK_EQ(db_first_available_pos(&r.db), cut);
                restarts++;
            }
        }
        CHECK(cut > 0);
        close_rdb(&r);
        CHECK_MEM_ZERO(&r.m);
        rs_remove_dir(dir);
    }
    CHECK(restarts >= 6);
}

/* Reclaim.Tester.testPretruncate: the same key put again and again with a
 * value of 100,000 bytes, a second apart, the retain duration 1 s and a
 * startup distance of 100,000: reclaim cuts the stream past the first
 * value (CutStream's exact cut, in memory). */
TEST(reclaim_pretruncate) {
    struct rdb r;
    mem_init(&r.m);
    r.time = 10;
    REQUIRE(rdb_open(&r, 30, 100 * 1000, 0, CLK_UNITS_PER_SEC) == ERR_OK);
    static uint8_t value[100000];
    for (int i = 0; i < 40; i++) {
        r.time = (i + 1) * CLK_UNITS_PER_SEC;
        REQUIRE(rdb_put(&r, "/k", value, (int32_t) sizeof value, NULL) == ERR_OK);
    }
    r.time = 40 * CLK_UNITS_PER_SEC + 1;
    REQUIRE(rdb_put(&r, "/k2", value, (int32_t) sizeof value, NULL) == ERR_OK);
    CHECK(stream_first_pos(&r.db.stream) > (int64_t) sizeof value);
    CHECK_EQ(stream_first_pos(&r.db.stream), db_first_available_pos(&r.db));
    int32_t len;
    CHECK(rdb_get(&r, INT64_MAX, "/k", NULL, &len, NULL) == ERR_OK);
    CHECK_EQ(len, (int32_t) sizeof value);
    close_rdb(&r);
    CHECK_MEM_ZERO(&r.m);
}

/* A crash of a closed directory's stream at pos, as a crash leaves it: the
 * files from pos on deleted, the one that holds pos cut there. */
static bool crash_dir(const char *dir, int64_t pos) {
    DIR *d = opendir(dir);
    struct dirent *x;
    bool ok = d != NULL;
    while (ok && (x = readdir(d)) != NULL) {
        size_t len = strlen(x->d_name);
        if (len != 21 || strcmp(x->d_name + 14, ".bergdb") != 0) {
            continue;
        }
        char path[1200];
        struct stat st;
        snprintf(path, sizeof path, "%s/%s", dir, x->d_name);
        const int64_t start = strtoll(x->d_name, NULL, 10) * STREAM_INDEX_UNIT;
        if (stat(path, &st) != 0) {
            ok = false;
        } else if (start >= pos) {
            ok = unlink(path) == 0;
        } else if (start + (int64_t) st.st_size > pos) {
            ok = truncate(path, (off_t) (pos - start)) == 0;
        }
    }
    if (d != NULL) {
        closedir(d);
    }
    return ok;
}

/* Reclaim.Tester.testCrashBeforeIterationEnd (a bug found 2026-10-13 by
 * CrashTest with reclaim): the last step of an iteration stored the row as
 * done, and tEnd and pEnd followed in the next record; after a crash between
 * the two, the row was done with tEnd 0, and the cut there made 0 the first
 * available lookup time. A put whose call ends an iteration, after a cut:
 * the stream crashed after the call's first record and before its second
 * (Java's crash position), unless the call forced past it (a cut it
 * decided: C forces in that call, so no crash can lose it; Java's CutStream
 * refuses such a crash too). After the restart every done row has its tEnd
 * and pEnd; from then on a cut always comes with a first available time
 * after it; reclaim cuts again, and the lookups from the first available
 * time on equal the model, 200 puts after that cut (Java's run goes on to
 * 2,500 puts). */
TEST(reclaim_crash_before_iteration_end) {
    struct rdb r;
    struct err e;
    char dir[1024];
    static struct model mo;
    memset(&mo, 0, sizeof mo);
    mem_init(&r.m);
    rs_temp_dir(dir, sizeof dir);
    REQUIRE(dir[0] != '\0');
    r.time = CLK_UNITS_PER_SEC;
    REQUIRE(cut_start(&r, dir) == ERR_OK);
    uint64_t rnd = 6;
    bool crashed = false;
    int64_t cutAtCrash = 0;
    int skipped = 0;
    int after = -1;         /* puts after the first cut after the crash; Java's run goes on */
    for (int i = 0; i < 2500 && after < 200; i++) {
        r.time += CLK_UNITS_PER_SEC / 20;
        const int k = test_random_below(&rnd, MK);
        char key[32];
        snprintf(key, sizeof key, "/k/%d", k);
        uint8_t v[32];
        const int32_t len = 1 + test_random_below(&rnd, 30);
        for (int j = 0; j < len; j++) {
            v[j] = (uint8_t) test_random(&rnd);
        }
        const int64_t count = r.db.reclaim.iterationCount;
        struct trans t;
        REQUIRE(rdb_put(&r, key, v, len, &t) == ERR_OK);
        REQUIRE(mo.n[k] < MV);
        mo.times[k][mo.n[k]] = t.tt;
        memcpy(mo.vals[k][mo.n[k]], v, (size_t) len);
        mo.lens[k][mo.n[k]] = len;
        mo.n[k]++;
        if (!crashed && r.db.reclaim.iterationCount > count && db_first_available_pos(&r.db) > 0) {
            /* After t come the iteration's last records; a crash between the
             * first and the second. */
            struct ns_iter it;
            bool has1 = false, has2 = false;
            ns_iter_init(&it, &r.db.stream, &r.m, t.next_pos, true);
            CHECK(ns_iter_next(&it, &has1, &e) == ERR_OK);
            CHECK(ns_iter_next(&it, &has2, &e) == ERR_OK);
            const int64_t crashPos = it.tpos;
            ns_iter_free(&it);
            if (!has1 || !has2 || crashPos < stream_durable_length(&r.db.stream)) {
                skipped++;
                continue;
            }
            REQUIRE(db_close(&r.db, &e) == ERR_OK);
            REQUIRE(crash_dir(dir, crashPos));
            REQUIRE(cut_start(&r, dir) == ERR_OK);
            crashed = true;
            cutAtCrash = db_first_available_pos(&r.db);
            for (int32_t q = 0; q < r.db.reclaim.nrows; q++) {
                const struct rc_row *row = &r.db.reclaim.rows[q];
                CHECK(!row->done || (row->tEnd >= row->tStart && row->pEnd >= row->pStart));
            }
        }
        /* A cut always comes with a first available lookup time after it. */
        if (db_first_available_pos(&r.db) > 0) {
            CHECK(db_first_available_time(&r.db) > 0);
        }
        if (after >= 0 || (crashed && db_first_available_pos(&r.db) > cutAtCrash)) {
            after++;
        }
    }
    CHECK(crashed);
    CHECK(db_first_available_pos(&r.db) > cutAtCrash);
    const int64_t first = db_first_available_time(&r.db);
    CHECK(first > 0);
    for (int64_t lt = first; lt <= r.time; lt += CLK_UNITS_PER_SEC / 4) {
        for (int k = 0; k < MK; k++) {
            char key[32];
            snprintf(key, sizeof key, "/k/%d", k);
            uint8_t v[64];
            int32_t len;
            REQUIRE(rdb_get(&r, lt, key, v, &len, NULL) == ERR_OK);
            const int32_t i = model_floor(&mo, k, lt);
            if (i < 0) {
                CHECK_EQ(len, -1);
            } else {
                CHECK_EQ(len, mo.lens[k][i]);
                CHECK(len < 0 || memcmp(v, mo.vals[k][i], (size_t) len) == 0);
            }
        }
    }
    printf("  reclaim_crash_before_iteration_end: crashed at an iteration's end after %d "
            "skipped (forced past)\n", skipped);
    close_rdb(&r);
    CHECK_MEM_ZERO(&r.m);
    rs_remove_dir(dir);
}

/* Counts the pairs of a getMany. */
static bool count_pairs(void *ctx, const struct kvt *kvt) {
    (void) kvt;
    (*(int *) ctx)++;
    return true;
}

/* Reclaim.Tester.test1: 40 values of 100,000 bytes put with a startup
 * distance of 100,000 (no reclaim: the retain duration forever), and a
 * getMany of all at the latest time gives the 40 (Java allows one more). */
TEST(reclaim_test1) {
    struct rdb r;
    struct err e;
    mem_init(&r.m);
    r.time = 10;
    REQUIRE(rdb_start(&r, NULL, 30, 100 * 1000, 0, &e) == ERR_OK);
    static uint8_t value[100000];
    for (int i = 0; i < 40; i++) {
        r.time = 1000 + i * 10;
        char key[16];
        snprintf(key, sizeof key, "%d", i);
        REQUIRE(rdb_put(&r, key, value, (int32_t) sizeof value, NULL) == ERR_OK);
    }
    int n = 0;
    struct getmany g;
    db_new_get_many(&r.db, &g);
    g.result.add = count_pairs;
    g.result.ctx = &n;
    CHECK(db_get_many(&r.db, &g, &e) == ERR_OK);
    CHECK_EQ(n, 40);
    close_rdb(&r);
    CHECK_MEM_ZERO(&r.m);
}

/* Reclaim.Tester.testCutIsMadeAfterDecisionIsDurable (011-04, W5c), in
 * C's terms: the cut is made only when the stream is durable up to the
 * decision (the table that marks it, the meta block that recovery starts
 * from). Java's storage thread makes it durable later, and the cut follows
 * at a later transaction; C forces in the call that decides the cut and
 * cuts there (c/readme.md, section 9, point 9). In a directory, with no
 * sync: after each call that decided a cut, none is pending, the stream is
 * durable past the length at the decision, and the files before the one
 * that holds the cut are gone (the first position at or before the cut,
 * past the files before it). Three cuts or more, until one has deleted a
 * file. */
TEST(reclaim_cut_made_when_durable) {
    struct rdb r;
    char dir[1024];
    mem_init(&r.m);
    rs_temp_dir(dir, sizeof dir);
    REQUIRE(dir[0] != '\0');
    r.time = CLK_UNITS_PER_SEC;
    REQUIRE(cut_start(&r, dir) == ERR_OK);
    uint64_t rnd = 8;
    int64_t lastCut = 0;
    int cuts = 0;
    int deleted = 0;
    static uint8_t value[4000];
    for (int i = 0; i < 30000 && (cuts < 3 || deleted == 0); i++) {
        r.time += CLK_UNITS_PER_SEC / 20;
        char key[32];
        snprintf(key, sizeof key, "/k/%d", test_random_below(&rnd, 50));
        const int64_t before = stream_durable_length(&r.db.stream);
        REQUIRE(rdb_put(&r, key, value, 1000 + test_random_below(&rnd, 3000), NULL) == ERR_OK);
        const int64_t cut = db_first_available_pos(&r.db);
        if (cut > lastCut) {
            lastCut = cut;
            cuts++;
            CHECK_EQ(r.db.reclaim.pendingCut, -1);
            CHECK(stream_durable_length(&r.db.stream) > before);
            CHECK(stream_durable_length(&r.db.stream) >= r.db.reclaim.pendingCutDurableAt);
            CHECK(stream_first_pos(&r.db.stream) <= cut);
            if (stream_first_pos(&r.db.stream) > 0) {
                deleted++;
            }
        } else {
            /* No sync and no cut decided: nothing forced. */
            CHECK_EQ(stream_durable_length(&r.db.stream), before);
        }
    }
    CHECK(cuts >= 3);
    CHECK(deleted > 0);
    printf("  reclaim_cut_made_when_durable: %d cuts, %d with files deleted\n", cuts, deleted);
    close_rdb(&r);
    CHECK_MEM_ZERO(&r.m);
    rs_remove_dir(dir);
}

const struct test reclaim_tests[] = {
    TEST_ENTRY(reclaim_row_text),
    TEST_ENTRY(reclaim_row_parse),
    TEST_ENTRY(reclaim_table_text),
    TEST_ENTRY(reclaim_settings),
    TEST_ENTRY(reclaim_fraction_of_exact),
    TEST_ENTRY(reclaim_iterations_rewrite_old_values),
    TEST_ENTRY(reclaim_iterations_spaced),
    TEST_ENTRY(reclaim_lookups_from_first_available_time),
    TEST_ENTRY(reclaim_step_reserve_splits_steps),
    TEST_ENTRY(reclaim_table_in_stream),
    TEST_ENTRY(reclaim_alloc_failures),
    TEST_ENTRY(reclaim_java_vectors),
    TEST_ENTRY(reclaim_settings_kept_over_restarts),
    TEST_ENTRY(reclaim_settings_refused_change_nothing),
    TEST_ENTRY(reclaim_settings_in_force_write_nothing),
    TEST_ENTRY(reclaim_settings_kept_across_restart),
    TEST_ENTRY(reclaim_settings_survive_cuts),
    TEST_ENTRY(reclaim_settings_none_defaults),
    TEST_ENTRY(reclaim_settings_malformed_refused_at_start),
    TEST_ENTRY(reclaim_safe_pos_after_the_calls_records),
    TEST_ENTRY(reclaim_step_within_value_limit),
    TEST_ENTRY(reclaim_user_transaction_leaves_times),
    TEST_ENTRY(reclaim_retention_shrink_during_iteration),
    TEST_ENTRY(reclaim_retention_shrink_makes_rows_cuttable),
    TEST_ENTRY(reclaim_retention_grow_after_cut),
    TEST_ENTRY(reclaim_retention_restart_with_other),
    TEST_ENTRY(reclaim_retention_forever_then_finite),
    TEST_ENTRY(reclaim_retention_finite_then_forever_mid_iteration),
    TEST_ENTRY(reclaim_restart_after_cut),
    TEST_ENTRY(reclaim_first_available_time_after_restart),
    TEST_ENTRY(reclaim_deleted_keys_after_cut),
    TEST_ENTRY(reclaim_restart_resumes_iteration),
    TEST_ENTRY(reclaim_iterations_follow_stream_distance),
    TEST_ENTRY(reclaim_cut_keeps_meta_block_transaction),
    TEST_ENTRY(reclaim_pretruncate),
    TEST_ENTRY(reclaim_crash_before_iteration_end),
    TEST_ENTRY(reclaim_test1),
    TEST_ENTRY(reclaim_cut_made_when_durable),
    TEST_END
};
