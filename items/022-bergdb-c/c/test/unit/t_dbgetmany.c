/* Java's DbTesterGetMany (bergdb 012-08), the tests that C's Level 0 has
 * (the database in memory, mdb.h, as Java's Db without a restart): getMany
 * forward and backward, at times, from start keys, with Endpoint and a
 * caller's stop condition, keys of one and of several segments, the bugs of
 * 130606, and getOpCount. Left out: test4 (a restart: 012-10) and the
 * three with KeyFactory.crazyKey (java.util.Random's keys; the random tests
 * of t_getmany.c and Java's own Dag in t_dagvec.c cover what they cover).
 * A database without a test clock (Java's system clock) gets the times 10,
 * 20, ...; only their order matters there. */
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "getmany.h"
#include "keys.h"
#include "mdb.h"
#include "mem.h"
#include "test.h"

struct key {
    int64_t s[16];
    int32_t n;
};

/* Keys.toSegments(String): an ikey */
static struct key ik(const char *ikey) {
    struct key k;
    uint8_t b[112];
    int32_t len = (int32_t) strlen(ikey);
    if (len > 100 || !keys_ikey_to_bkey((const uint8_t *) ikey, len, b)) {
        CHECK(false);
        k.n = 1;
        k.s[0] = 0;
        return k;
    }
    k.n = keys_segment_count(len);
    keys_to_segments(b, len, k.s);
    return k;
}

/* Keys.toSegments(byte[]): a bkey */
static struct key bk(const uint8_t *b, int32_t len) {
    struct key k;
    k.n = keys_segment_count(len);
    keys_to_segments(b, len, k.s);
    return k;
}

static struct key hexkey(const char *hex) {
    uint8_t b[64];
    int32_t n = (int32_t) strlen(hex) / 2;
    for (int32_t i = 0; i < n; i++) {
        unsigned v;
        sscanf(hex + 2 * i, "%2x", &v);
        b[i] = (uint8_t) v;
    }
    return bk(b, n);
}

struct db {
    struct mem m;
    struct mdb d;
    int64_t time;
};

static void db_start(struct db *db) {
    mem_init(&db->m);
    CHECK(mdb_create(&db->d, &db->m, 1, 30));
    db->time = 1;
}

static void db_close(struct db *db) {
    CHECK_EQ(mdb_recount(&db->d), 0);
    mdb_free(&db->d);
    CHECK_MEM_ZERO(&db->m);
}

/* One transaction at time t of n pairs (keys sorted as Trans.Builder sorts
 * them). */
static void db_put_at(struct db *db, int64_t t, const struct key *keys, const char *const *values,
        int32_t n) {
    int32_t order[16];
    for (int32_t i = 0; i < n; i++) {
        order[i] = i;
    }
    for (int32_t i = 1; i < n; i++) {
        for (int32_t j = i; j > 0 && keys_compare_arrays(keys[order[j]].s, keys[order[j]].n,
                keys[order[j - 1]].s, keys[order[j - 1]].n) < 0; j--) {
            int32_t x = order[j];
            order[j] = order[j - 1];
            order[j - 1] = x;
        }
    }
    mdb_begin(&db->d, t);
    for (int32_t i = 0; i < n; i++) {
        const char *v = values[order[i]];
        CHECK(mdb_put(&db->d, keys[order[i]].s, keys[order[i]].n, (const uint8_t *) v,
                (int32_t) strlen(v)));
    }
    mdb_end(&db->d);
    db->time = t;
}

static void db_put(struct db *db, const char *ikey, const char *value) {
    struct key k = ik(ikey);
    db_put_at(db, db->time + 10 - db->time % 10, &k, &value, 1);
}

/* createDbWithKeys: (10 a 1), (20 b 2), ... the value from the key's first
 * letter. */
static void create_with_keys(struct db *db, const char *const *keys, int n) {
    db_start(db);
    for (int i = 0; i < n; i++) {
        char v[8];
        snprintf(v, sizeof v, "%d", keys[i][0] - 'a' + 1);
        struct key k = ik(keys[i]);
        const char *vp = v;
        db_put_at(db, 10 + i * 10, &k, &vp, 1);
    }
}

static void create_with_kvs(struct db *db, const char *const *kvs, int n) {
    db_start(db);
    for (int i = 0; i < n; i++) {
        struct key k = ik(kvs[2 * i]);
        db_put_at(db, 10 + i * 10, &k, &kvs[2 * i + 1], 1);
    }
}

/* The result of a getMany: the values as strings, the keys, the times. */
struct res {
    char v[128][16];
    struct key k[128];
    int64_t time[128];
    int32_t n;
    int32_t get_op_count;
};

static bool res_add(void *ctx, const struct kvt *kvt) {
    struct res *r = ctx;
    if (r->n < 128) {
        int32_t len = kvt->value->len < 15 ? kvt->value->len : 15;
        memcpy(r->v[r->n], kvt->value->value, (size_t) len);
        r->v[r->n][len] = '\0';
        memcpy(r->k[r->n].s, kvt->key, (size_t) kvt->key_n * sizeof(int64_t));
        r->k[r->n].n = kvt->key_n;
        r->time[r->n] = kvt->time;
    }
    r->n++;
    return true;
}

struct q {
    int64_t lookup_time;
    const struct key *start;
    bool inclusive;
    bool forward;
    struct gm_stop stop;
};

static struct q q_default(void) {
    struct q q = { INT64_MAX, NULL, true, true, gm_dont_stop() };
    return q;
}

static void run(struct db *db, const struct q *q, struct res *r) {
    struct getmany g;
    mdb_new_get_many(&db->d, &g);
    g.lookup_time = q->lookup_time;
    if (q->start != NULL) {
        g.start_key = q->start->s;
        g.start_key_n = q->start->n;
    }
    g.inclusive = q->inclusive;
    g.forward = q->forward;
    g.stop_condition = q->stop;
    memset(r, 0, sizeof *r);
    g.result.add = res_add;
    g.result.ctx = r;
    CHECK(mdb_get_many(&db->d, &g));
    r->get_op_count = g.get_op_count;
}

/* assertResultValues */
static void values(const struct res *r, int n, ...) {
    CHECK_EQ(r->n, n);
    va_list ap;
    va_start(ap, n);
    for (int i = 0; i < n; i++) {
        const char *want = va_arg(ap, const char *);
        CHECK(i < r->n && strcmp(r->v[i], want) == 0);
    }
    va_end(ap);
}

static bool same_key(const struct key *a, const struct key *b) {
    return keys_compare_keys(a->s, a->n, b->s, b->n) == 0;
}

static const char *const CBA[] = { "c", "b", "a" };
static const char *const ABC[] = { "a", "b", "c" };

TEST(dbgm_test1) {
    struct db db;
    create_with_keys(&db, CBA, 3);
    struct q q = q_default();
    q.lookup_time = 100;
    struct res r;
    run(&db, &q, &r);
    values(&r, 3, "1", "2", "3");
    db_close(&db);
}

TEST(dbgm_test1_backward) {
    struct db db;
    create_with_keys(&db, ABC, 3);
    struct q q = q_default();
    q.lookup_time = 100;
    q.forward = false;
    struct res r;
    run(&db, &q, &r);
    values(&r, 3, "3", "2", "1");
    struct key a = ik("a");
    CHECK(same_key(&r.k[2], &a));
    db_close(&db);
}

TEST(dbgm_test2) {
    const char *const kvs[] = { "c", "basedir/c", "b", "basedir/b", "a", "basedir/a" };
    struct db db;
    create_with_kvs(&db, kvs, 3);
    struct q q = q_default();
    q.lookup_time = 100;
    struct res r;
    run(&db, &q, &r);
    values(&r, 3, "basedir/a", "basedir/b", "basedir/c");
    struct key c = ik("c");
    CHECK(same_key(&r.k[2], &c));
    db_close(&db);
}

TEST(dbgm_test2_backward) {
    struct db db;
    create_with_keys(&db, CBA, 3);
    struct q q = q_default();
    q.lookup_time = 100;
    q.forward = false;
    struct res r;
    run(&db, &q, &r);
    values(&r, 3, "3", "2", "1");
    db_close(&db);
}

/* Historic lookups, both ways. */
TEST(dbgm_test3) {
    for (int fwd = 1; fwd >= 0; fwd--) {
        struct db db;
        create_with_keys(&db, CBA, 3);
        struct q q = q_default();
        q.forward = fwd == 1;
        struct res r;
        q.lookup_time = 1;
        run(&db, &q, &r);
        CHECK_EQ(r.n, 0);
        q.lookup_time = 25;
        run(&db, &q, &r);
        if (fwd) {
            values(&r, 2, "2", "3");
        } else {
            values(&r, 2, "3", "2");
        }
        q.lookup_time = INT64_MAX;
        run(&db, &q, &r);
        if (fwd) {
            values(&r, 3, "1", "2", "3");
        } else {
            values(&r, 3, "3", "2", "1");
        }
        db_close(&db);
    }
}

static int32_t stop_after_two(void *ctx, const struct kvt *kvt) {
    (void) kvt;
    int32_t *count = ctx;
    (*count)++;
    return *count > 2 ? GM_STOP : GM_ADD;
}

TEST(dbgm_stop_condition1) {
    struct db db;
    create_with_keys(&db, CBA, 3);
    struct q q = q_default();
    q.lookup_time = 100;
    int32_t count = 0;
    struct gm_stop s = { stop_after_two, NULL, &count };
    q.stop = s;
    struct res r;
    run(&db, &q, &r);
    values(&r, 2, "1", "2");
    db_close(&db);
}

TEST(dbgm_endpoint1) {
    const char *const keys[] = { "e", "c", "a" };
    struct db db;
    create_with_keys(&db, keys, 3);
    struct key c = ik("c");
    struct gm_endpoint ep;
    struct q q = q_default();
    q.lookup_time = 100;
    q.stop = gm_endpoint(&ep, c.s, c.n, true, false);
    struct res r;
    run(&db, &q, &r);
    values(&r, 2, "1", "3");
    q.stop = gm_endpoint(&ep, c.s, c.n, false, false);
    run(&db, &q, &r);
    values(&r, 1, "1");
    db_close(&db);
}

static const char *const ENDPOINT_KVS[] = { "segments/e", "3", "segment/c", "2", "a", "1", "z",
    "4" };

TEST(dbgm_endpoint2) {
    struct db db;
    create_with_kvs(&db, ENDPOINT_KVS, 4);
    struct key z = ik("z - should be the last");
    struct gm_endpoint ep;
    struct q q = q_default();
    q.stop = gm_endpoint(&ep, z.s, z.n, true, false);       /* Endpoint(key) */
    struct res r;
    run(&db, &q, &r);
    values(&r, 4, "1", "2", "3", "4");
    db_close(&db);
}

TEST(dbgm_endpoint3) {
    struct db db;
    create_with_kvs(&db, ENDPOINT_KVS, 4);
    struct key a = ik("a");
    struct gm_endpoint ep;
    struct q q = q_default();
    q.lookup_time = 100;
    q.stop = gm_endpoint(&ep, a.s, a.n, false, false);
    struct res r;
    run(&db, &q, &r);
    CHECK_EQ(r.n, 0);
    db_close(&db);
}

TEST(dbgm_endpoint_backward) {
    const char *const kvs[] = { "e", "3", "c", "2", "a", "1" };
    struct db db;
    create_with_kvs(&db, kvs, 3);
    struct key c = ik("c");
    struct gm_endpoint ep;
    struct q q = q_default();
    q.lookup_time = 100;
    q.forward = false;
    q.stop = gm_endpoint(&ep, c.s, c.n, true, true);
    struct res r;
    run(&db, &q, &r);
    values(&r, 2, "3", "2");
    q.stop = gm_endpoint(&ep, c.s, c.n, false, true);
    run(&db, &q, &r);
    values(&r, 1, "3");
    db_close(&db);
}

/* testDeepSegment: segment trees of depth > 1, keys added backwards. */
TEST(dbgm_deep_segment) {
    struct db db;
    db_start(&db);
    int64_t time = 100;
    int size = 100;
    for (int i = 0; i < size; i++) {
        uint8_t b[4];
        int32_t x = size - i;       /* KeyFactory.binaryIntKey: big-endian */
        b[0] = (uint8_t) (x >> 24);
        b[1] = (uint8_t) (x >> 16);
        b[2] = (uint8_t) (x >> 8);
        b[3] = (uint8_t) x;
        struct key k = bk(b, 4);
        char v[8];
        snprintf(v, sizeof v, "%d", x);
        const char *vp = v;
        db_put_at(&db, time, &k, &vp, 1);
        time += 10;
    }
    struct q q = q_default();
    q.lookup_time = time + 100;
    struct res r;
    run(&db, &q, &r);
    CHECK_EQ(r.n, size);
    for (int i = 0; i < size && i < r.n; i++) {
        char v[8];
        snprintf(v, sizeof v, "%d", i + 1);
        CHECK(strcmp(r.v[i], v) == 0);
    }
    db_close(&db);
}

TEST(dbgm_start1) {
    struct db db;
    create_with_keys(&db, CBA, 3);
    struct key b = ik("b");
    struct q q = q_default();
    q.start = &b;
    q.lookup_time = 100;
    struct res r;
    run(&db, &q, &r);
    values(&r, 2, "2", "3");
    q.forward = false;
    run(&db, &q, &r);
    values(&r, 2, "2", "1");
    db_close(&db);
}

TEST(dbgm_start2) {
    struct db db;
    create_with_keys(&db, CBA, 3);
    struct key bbb = ik("bbb"), aa = ik("aa");
    struct q q = q_default();
    q.lookup_time = 100;
    q.start = &bbb;
    struct res r;
    run(&db, &q, &r);
    values(&r, 1, "3");
    q.start = &aa;
    run(&db, &q, &r);
    values(&r, 2, "2", "3");
    db_close(&db);
}

TEST(dbgm_start3_and_4) {
    struct db db;
    create_with_keys(&db, CBA, 3);
    struct key zero = ik("0"), z = ik("z");
    struct q q = q_default();
    q.lookup_time = 100;
    q.start = &zero;        /* less than any key */
    struct res r;
    run(&db, &q, &r);
    CHECK_EQ(r.n, 3);
    q.start = &z;           /* greater than any key */
    run(&db, &q, &r);
    CHECK_EQ(r.n, 0);
    db_close(&db);
}

/* testStart5: two top nodes made. */
TEST(dbgm_start5) {
    struct db db;
    db_start(&db);
    char value[101];
    memset(value, 'x', 100);
    value[100] = '\0';
    for (int i = 0; i < 16; i++) {
        char key[8];
        snprintf(key, sizeof key, "%d", i);
        db_put(&db, key, value);
    }
    struct q q = q_default();
    struct res r;
    run(&db, &q, &r);
    CHECK_EQ(r.n, 16);
    struct key zero = ik("0");
    q.start = &zero;
    q.inclusive = false;
    run(&db, &q, &r);
    CHECK_EQ(r.n, 15);
    db_close(&db);
}

static void start_with_longer_keys(const char *second, const char *secondValue) {
    struct db db;
    db_start(&db);
    struct key keys[4] = { ik("directory/10"), ik(second), ik("directory/30"), ik("a40") };
    const char *const vals[4] = { "10", secondValue, "30", "40" };
    db_put_at(&db, 10, keys, vals, 4);
    struct key start = ik("directory/19");
    struct q q = q_default();
    q.start = &start;
    q.lookup_time = 100;
    struct res r;
    run(&db, &q, &r);
    values(&r, 2, secondValue, "30");
    CHECK(same_key(&r.k[0], &keys[1]));
    CHECK(same_key(&r.k[1], &keys[2]));
    db_close(&db);
}

TEST(dbgm_start_with_longer_keys) {
    start_with_longer_keys("directory/20", "20");
}

/* testStartWith7: a key of size % 7 == 0. */
TEST(dbgm_start_with_7) {
    start_with_longer_keys("directory/2000", "20");
}

TEST(dbgm_gt1) {
    struct db db;
    db_start(&db);
    char value[101];
    memset(value, 'x', 100);
    value[100] = '\0';
    for (int i = 0; i < 10; i++) {
        char key[8];
        snprintf(key, sizeof key, "%d", i);
        struct key k = ik(key);
        const char *vp = value;
        db_put_at(&db, 1000 + i * 10, &k, &vp, 1);
    }
    struct key zero = ik("0");
    struct q q = q_default();
    q.start = &zero;
    q.inclusive = true;
    struct res r;
    run(&db, &q, &r);
    CHECK_EQ(r.n, 10);
    q.inclusive = false;        /* C's addition */
    run(&db, &q, &r);
    CHECK_EQ(r.n, 9);
    db_close(&db);
}

/* testFromIndexing: a start key shorter than the keys. */
TEST(dbgm_from_indexing) {
    for (int fwd = 1; fwd >= 0; fwd--) {
        struct db db;
        db_start(&db);
        struct key keys[3] = { ik("001.object"), ik("002.object"), ik("003.object") };
        const char *const vals[3] = { "", "", "" };
        CHECK_EQ(keys[0].n, 2);
        db_put_at(&db, 10, keys, vals, 3);
        struct key start = ik("002");
        CHECK_EQ(start.n, 1);
        struct q q = q_default();
        q.start = &start;
        q.forward = fwd == 1;
        struct res r;
        run(&db, &q, &r);
        if (fwd) {
            CHECK_EQ(r.n, 2);
            CHECK(same_key(&r.k[0], &keys[1]));
            CHECK(same_key(&r.k[1], &keys[2]));
        } else {
            CHECK_EQ(r.n, 1);
            CHECK(same_key(&r.k[0], &keys[0]));
        }
        db_close(&db);
    }
}

/* bug130606, b, c and backwards: binary keys of 7 bytes and more. */
static void bug130606(const char *const *hex, int n, const char *startHex, bool forward,
        int want) {
    struct db db;
    db_start(&db);
    struct key keys[3];
    const char *const vals[3] = { "0", "1", "2" };
    for (int i = 0; i < n; i++) {
        keys[i] = hexkey(hex[i]);
    }
    db_put_at(&db, 10, keys, vals, n);
    struct key start = hexkey(startHex);
    struct q q = q_default();
    q.start = &start;
    q.forward = forward;
    struct res r;
    run(&db, &q, &r);
    CHECK_EQ(r.n, 1);
    CHECK(same_key(&r.k[0], &keys[want]));
    db_close(&db);
}

TEST(dbgm_bug130606) {
    const char *const two[] = { "00000000000000", "00000000000004" };
    const char *const three[] = { "0000000000000200012f633071646c",
        "0000000000000400012f643071646c", "0000000000000600012f653071646c" };
    bug130606(two, 2, "00000000000002", true, 1);
    bug130606(three, 3, "00000000000005", true, 2);
    bug130606(two, 2, "00000000000004", true, 1);
    bug130606(two, 2, "00000000000002", false, 0);
}

TEST(dbgm_get_op_count) {
    const char *const keys[] = { "a", "b", "c", "d" };
    struct db db;
    create_with_keys(&db, keys, 4);
    struct q q = q_default();
    q.lookup_time = 100;
    struct res r;
    run(&db, &q, &r);
    CHECK_EQ(r.get_op_count, 4);
    db_close(&db);
}

const struct test dbgetmany_tests[] = {
    TEST_ENTRY(dbgm_test1),
    TEST_ENTRY(dbgm_test1_backward),
    TEST_ENTRY(dbgm_test2),
    TEST_ENTRY(dbgm_test2_backward),
    TEST_ENTRY(dbgm_test3),
    TEST_ENTRY(dbgm_stop_condition1),
    TEST_ENTRY(dbgm_endpoint1),
    TEST_ENTRY(dbgm_endpoint2),
    TEST_ENTRY(dbgm_endpoint3),
    TEST_ENTRY(dbgm_endpoint_backward),
    TEST_ENTRY(dbgm_deep_segment),
    TEST_ENTRY(dbgm_start1),
    TEST_ENTRY(dbgm_start2),
    TEST_ENTRY(dbgm_start3_and_4),
    TEST_ENTRY(dbgm_start5),
    TEST_ENTRY(dbgm_start_with_longer_keys),
    TEST_ENTRY(dbgm_start_with_7),
    TEST_ENTRY(dbgm_gt1),
    TEST_ENTRY(dbgm_from_indexing),
    TEST_ENTRY(dbgm_bug130606),
    TEST_ENTRY(dbgm_get_op_count),
    TEST_END
};
