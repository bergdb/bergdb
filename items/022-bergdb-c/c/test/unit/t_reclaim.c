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
 * turn over iterations, steps, a table store and a cut. */
#include <errno.h>
#include <math.h>
#include <stdlib.h>
#include "test.h"
#include "../../tools/sha256.h"
#include "bergdb.h"
#include "db.h"
#include "jsem.h"
#include "keys.h"
#include "nstream.h"
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

TEST(reclaim_settings) {
    struct mem m;
    struct err e;
    mem_init(&m);
    struct reclaim r;
    rc_init(&r, &m);
    CHECK_EQ(r.retainDuration, INT64_MAX);
    CHECK_EQ(r.internalFraction, 16384);       /* 0.25 in units of 2^-16 (005-79) */
    CHECK_EQ(r.stepReserve, INT64_C(4) << 20);
    CHECK(rc_set_retain_duration(&r, CLK_UNITS_PER_SEC - 1, &e) == ERR_ARG);
    CHECK(rc_set_retain_duration(&r, CLK_UNITS_PER_SEC, &e) == ERR_OK);
    CHECK_EQ(r.retainDuration, CLK_UNITS_PER_SEC);
    /* Reclaim.setInternalFractionUnits: 66 to 58,982 (0.001 and 0.90
     * rounded); the setting stays after a refusal. */
    CHECK(rc_set_internal_fraction_units(&r, 65, &e) == ERR_ARG);
    CHECK(rc_set_internal_fraction_units(&r, 58983, &e) == ERR_ARG);
    CHECK_EQ(r.internalFraction, 16384);
    CHECK(rc_set_internal_fraction_units(&r, 66, &e) == ERR_OK);
    CHECK_EQ(r.internalFraction, 66);
    CHECK(rc_set_internal_fraction_units(&r, 58982, &e) == ERR_OK);
    CHECK_EQ(r.internalFraction, 58982);
    CHECK(rc_set_step_reserve(&r, 0, &e) == ERR_ARG);
    CHECK(rc_set_step_reserve(&r, 1, &e) == ERR_OK);
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

static enum err_code rdb_open(struct rdb *r, int32_t node, int32_t sd, int64_t reserve,
        int64_t retain) {
    struct db_config cfg;
    struct db_start_info info;
    struct err e;
    memset(&cfg, 0, sizeof cfg);
    cfg.max_node_size = node;
    cfg.startup_distance = sd;
    cfg.cache_size_indicator = INT64_MAX;
    cfg.retain_duration = retain;
    cfg.clock = rdb_clock;
    cfg.clock_ctx = &r->time;
    cfg.step_reserve = reserve;
    memcpy(cfg.id, bergdb_test_id, sizeof cfg.id);      /* testSetup's DatabaseId.TEST_ID */
    return db_open(&r->db, NULL, &cfg, &r->m, &info, &e);
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
    TEST_END
};
