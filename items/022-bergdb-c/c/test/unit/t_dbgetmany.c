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

/* ======== The end key (bergdb 021-28; 023-07, section 5.7, SE) ========
 *
 * Java's DbTesterGetMany tests of GetMany.endKey, since release 2026.4
 * (022-07), on mdb with the Core's struct getmany. The C API's ranges do
 * not set it (its end_key is the Endpoint stop condition, as before). */

/* The keys of a result, in order (keysOf). */
struct keylist {
    struct key *k;
    int32_t n, cap;
    bool eod;
};

static bool keylist_add(void *ctx, const struct kvt *kvt) {
    struct keylist *l = ctx;
    if (l->n < l->cap) {
        memcpy(l->k[l->n].s, kvt->key, (size_t) kvt->key_n * sizeof(int64_t));
        l->k[l->n].n = kvt->key_n;
    }
    l->n++;
    return true;
}

static int32_t add_all(void *ctx, const struct kvt *kvt) {
    (void) ctx, (void) kvt;
    return GM_ADD;
}

static void keylist_eod(void *ctx) {
    ((struct keylist *) ctx)->eod = true;
}

/* abcKey: a key of 1 to 20 of the bytes 'a', 'b' and 'c'. */
static int32_t abc_key(uint64_t *rs, uint8_t *out) {
    int32_t length = 1 + test_random_below(rs, 20);
    for (int32_t i = 0; i < length; i++) {
        out[i] = (uint8_t) ('a' + test_random_below(rs, 3));
    }
    return length;
}

struct abc {
    uint8_t b[20];
    int32_t len;
    struct key k;
    bool deleted;
};

static int cmp_abc_bytes(const void *x, const void *y) {
    const struct abc *a = x, *b = y;
    int32_t n = a->len < b->len ? a->len : b->len;
    int c = memcmp(a->b, b->b, (size_t) n);
    return c != 0 ? c : a->len - b->len;
}

static int cmp_abc_ptr(const void *x, const void *y) {
    const struct abc *a = *(const struct abc *const *) x, *b = *(const struct abc *const *) y;
    return keys_compare_arrays(a->k.s, a->k.n, b->k.s, b->k.n);
}

/* One transaction at t of the keys list[from .. to), sorted, put or deleted. */
static void abc_trans(struct db *db, int64_t t, struct abc **list, int32_t from, int32_t to,
        bool del) {
    struct abc *chunk[100];
    int32_t n = to - from;
    memcpy(chunk, list + from, (size_t) n * sizeof *chunk);
    qsort(chunk, (size_t) n, sizeof *chunk, cmp_abc_ptr);
    static const uint8_t one[1] = { 1 };
    mdb_begin(&db->d, t);
    for (int32_t i = 0; i < n; i++) {
        CHECK(mdb_put(&db->d, chunk[i]->k.s, chunk[i]->k.n, del ? NULL : one, 1));
    }
    mdb_end(&db->d);
    db->time = t;
}

/* testEndKeyAsEndpoint: GetMany.endKey gives what the Endpoint stop
 * condition gives, inclusive or not, from any start, at any lookup time,
 * also where the keys after the end are deleted: random keys of 1 to 20
 * bytes of three letters, around the segments of 7 bytes, put in
 * transactions of 50, then deleted, the run of keys that start with "b" and
 * every third of the others, in transactions of 50; scans at times before,
 * between and after the deletes. The scan ends as at the end of the
 * database: eod() is called. A backward scan with an end key is refused. */
TEST(dbgm_end_key_as_endpoint) {
    enum { N = 2000 };
    uint64_t rs = 2128;
    struct db db;
    db_start(&db);
    struct abc *keys = calloc(N, sizeof *keys);
    struct abc **list = calloc(N, sizeof *list);
    int32_t n = 0;
    while (n < N) {
        struct abc c;
        memset(&c, 0, sizeof c);
        c.len = abc_key(&rs, c.b);
        bool dup = false;
        for (int32_t i = 0; i < n && !dup; i++) {
            dup = cmp_abc_bytes(&keys[i], &c) == 0;
        }
        if (!dup) {
            c.k = bk(c.b, c.len);
            keys[n++] = c;
        }
    }
    for (int32_t i = 0; i < N; i++) {
        list[i] = &keys[i];
    }
    for (int32_t i = N - 1; i > 0; i--) {       /* Collections.shuffle */
        int32_t j = test_random_below(&rs, i + 1);
        struct abc *tmp = list[i];
        list[i] = list[j];
        list[j] = tmp;
    }
    int64_t time = 10;
    int64_t times[200];
    int32_t ntimes = 0;
    for (int32_t i = 0; i < N; i += 50) {
        abc_trans(&db, time, list, i, i + 50 < N ? i + 50 : N, false);
        times[ntimes++] = time;
        time += 10;
    }
    struct abc **deleted = calloc(N, sizeof *deleted);
    int32_t nd = 0;
    for (int32_t i = 0; i < N; i++) {
        if (list[i]->b[0] == 'b' || i % 3 == 0) {
            deleted[nd++] = list[i];
        }
    }
    for (int32_t i = 0; i < nd; i += 50) {
        abc_trans(&db, time, deleted, i, i + 50 < nd ? i + 50 : nd, true);
        times[ntimes++] = time;
        time += 10;
    }

    struct keylist g = { calloc(N, sizeof(struct key)), 0, N, false };
    struct keylist h = { calloc(N, sizeof(struct key)), 0, N, false };
    int64_t pairs = 0;
    for (int i = 0; i < 1500; i++) {
        const int64_t lookupTime = i % 3 == 0 ? INT64_MAX
                : times[test_random_below(&rs, ntimes)];
        uint8_t sb[20], eb[20];
        const bool noStart = test_random_below(&rs, 10) == 0;
        struct key start = ik("a");
        if (!noStart) {
            int32_t len = abc_key(&rs, sb);
            start = bk(sb, len);
        }
        const bool inclusive = test_random_below(&rs, 2) == 0;
        int32_t elen = abc_key(&rs, eb);
        const struct key end = bk(eb, elen);
        const bool endInclusive = test_random_below(&rs, 2) == 0;

        struct getmany q;
        struct gm_endpoint ep;
        mdb_new_get_many(&db.d, &q);
        q.lookup_time = lookupTime;
        if (!noStart) {
            q.start_key = start.s;
            q.start_key_n = start.n;
        }
        q.inclusive = inclusive;
        q.stop_condition = gm_endpoint(&ep, end.s, end.n, endInclusive, false);
        g.n = 0;
        q.result.add = keylist_add;
        q.result.ctx = &g;
        CHECK(mdb_get_many(&db.d, &q));

        mdb_new_get_many(&db.d, &q);
        q.lookup_time = lookupTime;
        if (!noStart) {
            q.start_key = start.s;
            q.start_key_n = start.n;
        }
        q.inclusive = inclusive;
        q.end_key = end.s;
        q.end_key_n = end.n;
        q.end_inclusive = endInclusive;
        h.n = 0;
        h.eod = false;
        q.stop_condition.handle_kvt = add_all;
        q.stop_condition.eod = keylist_eod;
        q.stop_condition.ctx = &h;
        q.result.add = keylist_add;
        q.result.ctx = &h;
        CHECK(mdb_get_many(&db.d, &q));

        bool same = g.n == h.n;
        for (int32_t j = 0; same && j < g.n; j++) {
            same = same_key(&g.k[j], &h.k[j]);
        }
        CHECK(same);
        CHECK(h.eod);
        if (!same) {
            printf("  scan %d at %lld, %d, %d: %d and %d keys\n", i, (long long) lookupTime,
                    (int) inclusive, (int) endInclusive, (int) g.n, (int) h.n);
        }
        pairs += g.n;
    }
    CHECK(pairs > 1500);        /* the scans read pairs */

    struct getmany back;
    struct err e;
    err_clear(&e);
    mdb_new_get_many(&db.d, &back);
    gm_set_backward(&back);
    const struct key a = ik("a");
    back.end_key = a.s;
    back.end_key_n = a.n;
    back.gd.op.err = &e;
    CHECK(!mdb_get_many(&db.d, &back));     /* a backward scan with endKey refused */
    CHECK_EQ(e.code, ERR_ARG);
    CHECK(strcmp(e.java, "IllegalArgumentException") == 0);

    free(g.k);
    free(h.k);
    free(deleted);
    free(list);
    free(keys);
    db_close(&db);
}

/* A pointer listener that counts the key nodes followed. */
static bool count_key_nodes(void *ctx, struct node *pre, int32_t index, struct node *result,
        int32_t type) {
    (void) pre, (void) index, (void) type;
    if (result != NULL && result->o.kind == OBJ_KEY) {
        (*(int32_t *) ctx)++;
    }
    return true;
}

static bool count_super_root(void *ctx, struct tnode *superRoot) {
    (void) ctx, (void) superRoot;
    return true;
}

/* The scan from 'from' to 'to', not inclusive, by the Endpoint stop
 * condition, with the end key too if withEnd: its pairs, and the key nodes
 * it followed. */
static int32_t end_scan(struct db *db, const struct key *from, const struct key *to,
        bool withEnd, struct keylist *out) {
    struct getmany q;
    struct gm_endpoint ep;
    int32_t followed = 0;
    mdb_new_get_many(&db->d, &q);
    q.start_key = from->s;
    q.start_key_n = from->n;
    if (withEnd) {
        q.end_key = to->s;
        q.end_key_n = to->n;
        q.end_inclusive = false;
    }
    q.stop_condition = gm_endpoint(&ep, to->s, to->n, false, false);
    q.gd.op.pointer_listener.pointer_followed = count_key_nodes;
    q.gd.op.pointer_listener.super_root_accessed = count_super_root;
    q.gd.op.pointer_listener.ctx = &followed;
    out->n = 0;
    q.result.add = keylist_add;
    q.result.ctx = out;
    CHECK(mdb_get_many(&db->d, &q));
    return followed;
}

/* One transaction at the next time of count keys FORMAT % (first + i), put
 * or deleted; with extra, that key put too. */
static void fmt_trans(struct db *db, const char *format, int first, int count, bool del,
        const char *extra) {
    static struct abc keys[2001];
    static struct abc *list[2001];
    int32_t n = 0;
    char text[32];
    for (int i = 0; i < count; i++) {
        snprintf(text, sizeof text, format, first + i);
        keys[n].k = bk((const uint8_t *) text, (int32_t) strlen(text));
        list[n] = &keys[n];
        n++;
    }
    if (extra != NULL) {
        keys[n].k = bk((const uint8_t *) extra, (int32_t) strlen(extra));
        list[n] = &keys[n];
        n++;
    }
    qsort(list, (size_t) n, sizeof *list, cmp_abc_ptr);
    static const uint8_t one[1] = { 1 };
    mdb_begin(&db->d, db->time + 10);
    for (int32_t i = 0; i < n; i++) {
        CHECK(mdb_put(&db->d, list[i]->k.s, list[i]->k.n, del ? NULL : one, 1));
    }
    mdb_end(&db->d);
    db->time += 10;
}

/* testEndKeyPassesNoDeletedKeys: a scan that GetMany.endKey ends follows no
 * key node of the deleted keys after its range: 100 live keys "a0000" to
 * "a0099", then 5,000 keys "b00000" to "b04999" put and deleted, then "c".
 * The scan of [a0050, a0100) follows the key nodes on its path and no more.
 * Since release 2026.4 a delete unlinks the nodes it empties, so the stop
 * condition alone follows few key nodes too; the results of both are the
 * same. So this tests the unlink and the end key together (023-11, B3). */
TEST(dbgm_end_key_passes_no_deleted_keys) {
    struct db db;
    db_start(&db);
    fmt_trans(&db, "a%04d", 0, 100, false, "c");
    for (int i = 0; i < 5000; i += 100) {
        fmt_trans(&db, "b%05d", i, 100, false, NULL);
    }
    for (int i = 0; i < 5000; i += 100) {
        fmt_trans(&db, "b%05d", i, 100, true, NULL);
    }
    const struct key from = bk((const uint8_t *) "a0050", 5);
    const struct key to = bk((const uint8_t *) "a0100", 5);
    struct keylist g = { calloc(128, sizeof(struct key)), 0, 128, false };
    struct keylist h = { calloc(128, sizeof(struct key)), 0, 128, false };
    const int32_t withEnd = end_scan(&db, &from, &to, true, &g);
    const int32_t stopOnly = end_scan(&db, &from, &to, false, &h);
    CHECK_EQ(g.n, 50);
    CHECK_EQ(h.n, 50);
    for (int32_t i = 0; i < 50 && i < g.n && i < h.n; i++) {
        CHECK(same_key(&g.k[i], &h.k[i]));
    }
    CHECK(withEnd <= 20);       /* key nodes followed with endKey */
    CHECK(stopOnly <= 20);      /* by the stop condition alone */
    printf("  dbgm_end_key_passes_no_deleted_keys: %d key nodes followed with the end key, "
            "%d by the stop condition alone\n", (int) withEnd, (int) stopOnly);
    free(g.k);
    free(h.k);
    db_close(&db);
}

/* testEndKeyPassesNoDeletedLongKeys: as above, with long keys, each in a
 * segment tree of its own for its last segment: 100 live keys
 * "a000000xyzw" to "a000099xyzw", 2,000 keys "b000000xyzw" to "b001999xyzw"
 * put and deleted, then "c". The scan of the last five live keys, to the
 * end "b" not inclusive, follows few key nodes. */
TEST(dbgm_end_key_passes_no_deleted_long_keys) {
    struct db db;
    db_start(&db);
    fmt_trans(&db, "a%06dxyzw", 0, 100, false, "c");
    fmt_trans(&db, "b%06dxyzw", 0, 2000, false, NULL);
    fmt_trans(&db, "b%06dxyzw", 0, 2000, true, NULL);
    const struct key from = bk((const uint8_t *) "a000095xyzw", 11);
    const struct key to = bk((const uint8_t *) "b", 1);
    struct keylist g = { calloc(128, sizeof(struct key)), 0, 128, false };
    struct keylist h = { calloc(128, sizeof(struct key)), 0, 128, false };
    const int32_t withEnd = end_scan(&db, &from, &to, true, &g);
    const int32_t stopOnly = end_scan(&db, &from, &to, false, &h);
    CHECK_EQ(g.n, 5);
    CHECK_EQ(h.n, 5);
    for (int32_t i = 0; i < 5 && i < g.n && i < h.n; i++) {
        CHECK(same_key(&g.k[i], &h.k[i]));
    }
    CHECK(withEnd <= 30);
    CHECK(stopOnly <= 30);
    printf("  dbgm_end_key_passes_no_deleted_long_keys: %d key nodes followed with the end key, "
            "%d by the stop condition alone\n", (int) withEnd, (int) stopOnly);
    free(g.k);
    free(h.k);
    db_close(&db);
}

/* testEndKeyChainEdges, as far as C has the cases (the Chain is not driven
 * from outside getmany.c: dag_get_many ends at the first end, and the end
 * key leaves the chain without a link): with keys "pppppppa" and "pppppppb"
 * and the inclusive end "pppppppa", the scan gives "pppppppa" and eod, once;
 * a backward scan with an end key is refused with IllegalArgumentException
 * by Dag.getMany, also at a lookup time with no root. */
TEST(dbgm_end_key_chain_edges) {
    struct db db;
    db_start(&db);
    fmt_trans(&db, "ppppppp%c", 'a', 1, false, "pppppppb");
    const struct key end = bk((const uint8_t *) "pppppppa", 8);
    struct keylist g = { calloc(8, sizeof(struct key)), 0, 8, false };
    struct getmany q;
    mdb_new_get_many(&db.d, &q);
    q.end_key = end.s;
    q.end_key_n = end.n;
    q.stop_condition.handle_kvt = add_all;
    q.stop_condition.eod = keylist_eod;
    q.stop_condition.ctx = &g;
    q.result.add = keylist_add;
    q.result.ctx = &g;
    CHECK(mdb_get_many(&db.d, &q));
    CHECK_EQ(g.n, 1);
    CHECK(g.n == 1 && same_key(&g.k[0], &end));
    CHECK(g.eod);
    CHECK_EQ(q.get_op_count, 1);

    const int64_t times[] = { -1, mdb_lookup_time(&db.d, INT64_MAX) };
    const struct key a = bk((const uint8_t *) "a", 1);
    for (int i = 0; i < 2; i++) {
        struct err e;
        err_clear(&e);
        mdb_new_get_many(&db.d, &q);
        q.forward = false;
        q.end_key = a.s;
        q.end_key_n = a.n;
        q.lookup_time = times[i];
        q.actual_lookup_time = times[i];
        q.gd.op.err = &e;
        CHECK(!dag_get_many(&db.d.dag, &q));    /* Dag.getMany, backward */
        CHECK_EQ(e.code, ERR_ARG);
        CHECK(strcmp(e.java, "IllegalArgumentException") == 0);
    }
    free(g.k);
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
    TEST_ENTRY(dbgm_end_key_as_endpoint),
    TEST_ENTRY(dbgm_end_key_passes_no_deleted_keys),
    TEST_ENTRY(dbgm_end_key_passes_no_deleted_long_keys),
    TEST_ENTRY(dbgm_end_key_chain_edges),
    TEST_END
};
