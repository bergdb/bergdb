/* Eviction to a memory budget (bergdb 012-12; evict.h): the node table's
 * eviction, bytes and shrink; twins, a database without eviction and one
 * with a budget, the same transactions and reads: the same stream byte for
 * byte after every transaction, the same answers at every time, the counts
 * right (the recount), the pins in the node table, the resident bytes at
 * most the trigger; the setter's eviction in its call; the admission of a
 * large value; and the allocation failures in turn under a budget of one
 * byte. Each test ends with the allocator's count 0. */
#include <stdlib.h>
#include "test.h"
#include "bergdb.h"
#include "db.h"
#include "evict.h"
#include "handle.h"
#include "keys.h"
#include "knode.h"
#include "ntable.h"
#include "trans.h"
#include "vnode.h"

static void config(struct db_config *cfg, struct bergdb_test_clock *clock, int32_t maxNode,
        int32_t sd, int64_t budget) {
    memset(cfg, 0, sizeof *cfg);
    cfg->max_node_size = maxNode;
    cfg->startup_distance = sd;
    cfg->cache_size_indicator = budget;
    cfg->clock = bergdb_test_clock_time;
    cfg->clock_ctx = clock;
    memcpy(cfg->id, bergdb_test_id, 16);
}

/* "/k/N" as a bkey; returns its length. */
static int32_t bkey_of(int k, uint8_t *bkey) {
    char ikey[32];
    snprintf(ikey, sizeof ikey, "/k/%d", k);
    int32_t kl = (int32_t) strlen(ikey);
    keys_ikey_to_bkey((const uint8_t *) ikey, kl, bkey);
    return kl;
}

/* A transaction of nops random puts (values of 0 to 40 bytes, or big bytes
 * for the first put when big > 0) and deletes of keys 0 to nkeys - 1 at
 * clock time tt; the generator's state *rs. */
static enum err_code exec_random(struct db *db, struct mem *m, struct bergdb_test_clock *clock,
        int64_t tt, uint64_t *rs, int nkeys, int nops, int32_t big, struct err *e) {
    struct tr_builder b;
    struct trans t;
    tr_builder_init(&b, m);
    tr_init(&t, m);
    if (tt > clock->time) {
        bergdb_test_clock_set(clock, tt);
    }
    enum err_code rc = ERR_OK;
    for (int i = 0; i < nops && rc == ERR_OK; i++) {
        uint8_t bkey[32];
        int32_t kl = bkey_of(test_random_below(rs, nkeys), bkey);
        int32_t len = i == 0 && big > 0 ? big : test_random_below(rs, 41);
        if (test_random_below(rs, 6) == 0 && big == 0) {
            rc = tr_delete(&b, bkey, kl, e);
        } else {
            uint8_t *v = malloc((size_t) len + 1);
            for (int32_t j = 0; j < len; j++) {
                v[j] = (uint8_t) (tt + j);
            }
            rc = tr_put(&b, bkey, kl, v, len, NULL, e);
            free(v);
        }
    }
    if (rc == ERR_OK) {
        rc = tr_build(&b, &t, e);
    }
    if (rc == ERR_OK) {
        rc = db_execute(db, &t, e);
    }
    tr_free(&t);
    tr_builder_free(&b);
    return rc;
}

/* getOne of key k at time t: *len -2 if none, -1 a delete; the bytes into
 * out (cap bytes, the rest cut) and their sum into *sum. */
static enum err_code get_key(struct db *db, int64_t t, int k, int32_t *len, uint64_t *sum,
        struct err *e) {
    uint8_t bkey[32];
    int32_t kl = bkey_of(k, bkey);
    int64_t segs[8];
    keys_to_segments(bkey, kl, segs);
    struct getdata gd;
    db_new_get_data(db, &gd);
    struct vnode *v = NULL;
    enum err_code rc = db_get_one(db, t, segs, keys_segment_count(kl), &gd, &v, e);
    *len = v == NULL ? -2 : v->len;
    *sum = 0;
    for (int32_t i = 0; v != NULL && i < v->len; i++) {
        *sum = *sum * 31 + v->value[i];
    }
    return rc;
}

static struct ev_env env_of(struct db *db) {
    struct ev_env env = { &db->node_table, tds_get_super_root(&db->dag.top_ds),
            db->newest_written_top, &db->trans_seq };
    return env;
}

/* Cache3.evict and the table's bytes and shrink. */
TEST(evict_table) {
    struct mem m;
    struct obj_ctx cx;
    struct ntable t;
    mem_init(&m);
    obj_ctx_init(&cx, &m);
    nt_init(&t, &cx, &m);
    CHECK_EQ(nt_bytes(&t), 0);
    for (int64_t id = 1; id <= 3000; id++) {
        REQUIRE(nt_live_or_new_handle(&t, 2 * id + 1) != NULL);
    }
    CHECK_EQ(nt_size(&t), 3000);
    CHECK_EQ(nt_bytes(&t), nt_slots(&t) * 17);
    CHECK_EQ(m.live[MEM_TABLE], nt_bytes(&t));
    /* A canonical object at a stream position: its handle keeps the position. */
    struct handle *h = nt_live_handle(&t, 7);
    struct knode *k = kn_new(&cx, true);
    REQUIRE(k != NULL);
    k->n.id = 7;
    k->n.spos = 4096;
    node_set_canonical(&k->n, true);
    hd_set_obj(&cx, h, &k->n);
    obj_retain(&h->o);          /* a pointer that holds the handle */
    CHECK(nt_evict(&t, h));
    CHECK(hd_is_dead(h));
    CHECK(h->obj == NULL);
    CHECK_EQ(h->written_pos, 4096);
    CHECK(!node_is_canonical(&k->n));
    CHECK(nt_live_handle(&t, 7) == NULL);
    CHECK(!nt_evict(&t, h));    /* dead already */
    CHECK(nt_live_or_new_handle(&t, 7) != h);
    obj_release(&cx, &h->o);
    obj_collect(&cx);
    CHECK_EQ(cx.live[OBJ_KEY], 0);
    /* Eviction takes most handles; the table shrinks, and finds the rest. */
    for (int64_t id = 1; id <= 3000; id++) {
        if (id % 300 != 0 && id != 3) {
            struct handle *x = nt_live_handle(&t, 2 * id + 1);
            REQUIRE(x != NULL);
            CHECK(nt_evict(&t, x));
        }
    }
    obj_collect(&cx);
    int64_t before = nt_slots(&t);
    nt_shrink(&t);
    CHECK(nt_slots(&t) < before);
    CHECK_EQ(nt_size(&t), 11);
    for (int64_t id = 300; id <= 3000; id += 300) {
        CHECK(nt_live_handle(&t, 2 * id + 1) != NULL);
    }
    CHECK(nt_live_handle(&t, 7) != NULL);
    CHECK_EQ(m.live[MEM_TABLE], nt_bytes(&t));
    nt_free(&t, true);
    obj_collect(&cx);
    CHECK_MEM_ZERO(&m);
}

/* The floor after a sweep is measured after the node table's shrink
 * (14-robustness.md, 6.8): a sweep that empties a large table shrinks its
 * arrays; a floor that still counted them kept the trigger above the
 * resident bytes, and what was loaded next stayed unevicted (a budget of
 * one byte, up to 20 kB over in a long run). Here: 3,000 handles with no
 * object, a sweep drops them all; the floor is the resident bytes after it;
 * 200 more such handles, and the next ev_run drops them too. */
TEST(evict_floor_after_shrink) {
    struct mem m;
    struct obj_ctx cx;
    struct ntable t;
    struct ts_seq d;
    struct ev ev;
    mem_init(&m);
    obj_ctx_init(&cx, &m);
    nt_init(&t, &cx, &m);
    ts_init(&d, &m);
    ev_init(&ev, &cx, &m, 1);
    struct ev_env env = { &t, NULL, NULL, &d };
    for (int64_t id = 1; id <= 3000; id++) {
        REQUIRE(nt_live_or_new_handle(&t, 2 * id + 1) != NULL);
    }
    const int64_t big = ev_resident_bytes(&m, &t);
    ev_run(&ev, &env, false);
    CHECK_EQ(nt_size(&t), 0);
    const int64_t small = ev_resident_bytes(&m, &t);
    CHECK(small < big);
    CHECK_EQ(ev.floor, small);
    CHECK_EQ(ev.trigger, small + 1);
    for (int64_t id = 3001; id <= 3200; id++) {
        REQUIRE(nt_live_or_new_handle(&t, 2 * id + 1) != NULL);
    }
    CHECK(ev_resident_bytes(&m, &t) > small);
    ev_run(&ev, &env, false);
    CHECK_EQ(nt_size(&t), 0);
    CHECK_EQ(ev_resident_bytes(&m, &t), ev.floor);
    ev_free(&ev);
    nt_free(&t, true);
    obj_collect(&cx);
    CHECK_MEM_ZERO(&m);
}

/* Java's Eviction.detachable. */
TEST(evict_detachable) {
    struct mem m;
    struct obj_ctx cx;
    mem_init(&m);
    obj_ctx_init(&cx, &m);
    struct knode *k = kn_new(&cx, true);
    struct tnode *top = tn_new(&cx, 1, NULL, -1, 1000, 2048);
    REQUIRE(k != NULL && top != NULL);
    k->n.spos = 1001;               /* a vpos: not written */
    CHECK(!ev_detachable(&k->n, top, NULL));
    k->n.spos = 1024;
    CHECK(ev_detachable(&k->n, top, NULL));
    node_set_canonical(&k->n, true);
    CHECK(ev_detachable(&k->n, top, NULL));     /* canonical and clean */
    node_set_dirty(&k->n, true);
    CHECK(!ev_detachable(&k->n, top, NULL));    /* D */
    node_set_dirty(&k->n, false);
    node_set_in_trans_nodes(&k->n, true);
    CHECK(!ev_detachable(&k->n, top, NULL));    /* the record */
    node_set_in_trans_nodes(&k->n, false);
    CHECK(!ev_detachable(&top->n, top, NULL));  /* the super root */
    struct tnode *other = tn_new(&cx, 2, NULL, -1, 1000, 4096);
    REQUIRE(other != NULL);
    CHECK(ev_detachable(&other->n, top, NULL));
    CHECK(!ev_detachable(&other->n, top, other));   /* the newest written top node */
    struct vnode *v = vn_new(&cx, (const uint8_t *) "v", 1, 3000);
    REQUIRE(v != NULL);
    CHECK(ev_detachable(&v->n, top, NULL));
    node_set_in_trans_nodes(&v->n, true);
    CHECK(!ev_detachable(&v->n, top, NULL));
    obj_collect(&cx);
    CHECK_MEM_ZERO(&m);
}

/* One twin run: ref without eviction, sub with budget (or, with setter,
 * without one until transaction 150, then the budget by the setter, then
 * none again at 250). */
static void twin_run(int64_t budget, bool setter, int32_t maxNode, int32_t sd, uint64_t seed,
        int64_t *evicted) {
    struct mem m0, m1;
    struct err e;
    struct db ref, sub;
    struct db_config c0, c1;
    struct db_start_info info;
    struct bergdb_test_clock k0 = {0}, k1 = {0};
    mem_init(&m0);
    mem_init(&m1);
    config(&c0, &k0, maxNode, sd, INT64_MAX);
    config(&c1, &k1, maxNode, sd, setter ? INT64_MAX : budget);
    bergdb_test_clock_set(&k0, 500);
    bergdb_test_clock_set(&k1, 500);
    REQUIRE(db_open(&ref, NULL, &c0, &m0, &info, &e) == ERR_OK);
    REQUIRE(db_open(&sub, NULL, &c1, &m1, &info, &e) == ERR_OK);
    uint64_t r0 = seed, r1 = seed, rr = seed * 7;
    const int nkeys = 120;
    int64_t times[400];
    for (int i = 0; i < 300; i++) {
        int64_t tt = 1000 + 10 * i;
        times[i] = tt;
        if (setter && i == 150) {
            int64_t r = db_resident_bytes(&sub);
            CHECK(db_set_cache_size_indicator(&sub, budget, &e) == ERR_OK);
            CHECK(db_resident_bytes(&sub) <= sub.ev.trigger);
            CHECK(db_resident_bytes(&sub) < r || r <= sub.ev.trigger);
        }
        if (setter && i == 250) {
            CHECK(db_set_cache_size_indicator(&sub, INT64_MAX, &e) == ERR_OK);
        }
        CHECK(exec_random(&ref, &m0, &k0, tt, &r0, nkeys, 1 + i % 9, 0, &e) == ERR_OK);
        CHECK(exec_random(&sub, &m1, &k1, tt, &r1, nkeys, 1 + i % 9, 0, &e) == ERR_OK);
        CHECK_EQ(db_stream_length(&ref), db_stream_length(&sub));
        CHECK(memcmp(ref.stream.bytes, sub.stream.bytes, (size_t) db_stream_length(&ref)) == 0);
        CHECK_EQ(db_recount(&sub), 0);
        struct ev_env env = env_of(&sub);
        CHECK_EQ(ev_check_pins(&env), 0);
        CHECK(db_resident_bytes(&sub) <= sub.ev.trigger);
        /* At most the budget plus what is pinned (the budget may be INT64_MAX). */
        CHECK(db_resident_bytes(&sub) - db_pinned_bytes(&sub) <= sub.ev.high);
        if (i % 25 == 24) {
            /* Reads at past times, each followed by the end of an API call. */
            for (int j = 0; j < 60; j++) {
                int k = test_random_below(&rr, nkeys);
                int64_t t = times[test_random_below(&rr, i + 1)] - test_random_below(&rr, 2);
                int32_t l0, l1;
                uint64_t s0, s1;
                CHECK(get_key(&ref, t, k, &l0, &s0, &e) == ERR_OK);
                CHECK(get_key(&sub, t, k, &l1, &s1, &e) == ERR_OK);
                db_evict(&ref);
                db_evict(&sub);
                CHECK_EQ(l0, l1);
                CHECK(s0 == s1);
            }
            CHECK_EQ(db_recount(&sub), 0);
            CHECK(db_resident_bytes(&sub) <= sub.ev.trigger);
        }
    }
    *evicted += sub.ev.evicted;
    CHECK_EQ(ref.ev.evicted, 0);
    db_close(&ref, &e);
    db_close(&sub, &e);
    CHECK_MEM_ZERO(&m0);
    CHECK_MEM_ZERO(&m1);
}

/* Java's EvictionInvariance in C: budgets from one byte up give the bytes
 * and the answers of no eviction. */
TEST(evict_twins) {
    const int64_t budgets[] = {1, 2000, 20000, 200000};
    int64_t evicted = 0;
    for (int b = 0; b < 4; b++) {
        int64_t ev0 = evicted;
        twin_run(budgets[b], false, 8, 300, 11 + (uint64_t) b, &evicted);
        twin_run(budgets[b], false, 14, 100000, 21 + (uint64_t) b, &evicted);
        if (b < 3) {
            CHECK(evicted > ev0);
        }
    }
    twin_run(3000, true, 8, 200, 31, &evicted);
    printf("  evict_twins: %lld objects evicted\n", (long long) evicted);
}

/* Admission: a value over 1 MiB leaves memory when its record is written,
 * whatever the budget; a read loads it and does not keep it. */
TEST(evict_large_value) {
    struct mem m;
    struct err e;
    struct db db;
    struct db_config c;
    struct db_start_info info;
    struct bergdb_test_clock k = {0};
    mem_init(&m);
    config(&c, &k, 8, 300, INT64_MAX);
    bergdb_test_clock_set(&k, 500);
    REQUIRE(db_open(&db, NULL, &c, &m, &info, &e) == ERR_OK);
    uint64_t rs = 5;
    const int32_t big = 3 * 1024 * 1024 / 2;
    for (int i = 0; i < 4; i++) {
        CHECK(exec_random(&db, &m, &k, 1000 + 10 * i, &rs, 50, 5, 0, &e) == ERR_OK);
    }
    CHECK(exec_random(&db, &m, &k, 2000, &rs, 50, 1, big, &e) == ERR_OK);
    CHECK(db_resident_bytes(&db) < big);
    CHECK_EQ(db.ev.nlarge, 0);
    CHECK(db.ev.unswizzled > 0);
    /* The key of the big value: read it back. */
    uint64_t rs2 = 5;
    for (int i = 0; i < 4; i++) {
        for (int j = 0; j < 5; j++) {
            test_random(&rs2);
            test_random(&rs2);
            test_random(&rs2);
        }
    }
    int kbig = test_random_below(&rs2, 50);
    int32_t len;
    uint64_t sum;
    CHECK(get_key(&db, INT64_MAX, kbig, &len, &sum, &e) == ERR_OK);
    CHECK_EQ(len, big);
    db_evict(&db);
    CHECK(db_resident_bytes(&db) < big);
    CHECK(exec_random(&db, &m, &k, 3000, &rs, 50, 5, 0, &e) == ERR_OK);
    CHECK_EQ(db_recount(&db), 0);
    db_close(&db, &e);
    CHECK_MEM_ZERO(&m);
}

/* The allocation failures in turn under a budget of one byte, with reads:
 * each run's failure refuses (NOMEM: the database as it was, the
 * transaction again gives the bytes of a run without failures) or fails the
 * database; the close frees all. */
TEST(evict_alloc_failures) {
    struct mem mr;
    struct err e;
    struct db ref;
    struct db_config c;
    struct db_start_info info;
    struct bergdb_test_clock kr = {0};
    mem_init(&mr);
    config(&c, &kr, 8, 100, INT64_MAX);
    bergdb_test_clock_set(&kr, 500);
    REQUIRE(db_open(&ref, NULL, &c, &mr, &info, &e) == ERR_OK);
    uint64_t rr = 77;
    for (int i = 0; i < 30; i++) {
        CHECK(exec_random(&ref, &mr, &kr, 1000 + 10 * i, &rr, 40, 4, 0, &e) == ERR_OK);
    }
    const int64_t refLen = db_stream_length(&ref);
    int64_t runs = 0, refused = 0, failed = 0;
    for (int64_t at = 1; at < 200000; at++) {
        struct mem m;
        struct db db;
        struct bergdb_test_clock k = {0};
        mem_init(&m);
        m.fail_at = at;
        config(&c, &k, 8, 100, 1);
        bergdb_test_clock_set(&k, 500);
        enum err_code rc = db_open(&db, NULL, &c, &m, &info, &e);
        runs++;
        if (rc != ERR_OK) {
            CHECK_EQ(rc, ERR_NOMEM);
            CHECK_MEM_ZERO(&m);
            continue;
        }
        bool hit = false, dead = false;
        uint64_t rs = 77;
        for (int i = 0; i < 30 && !dead; i++) {
            uint64_t saved = rs;
            for (int attempt = 0; attempt < 2; attempt++) {
                rs = saved;
                rc = exec_random(&db, &m, &k, 1000 + 10 * i, &rs, 40, 4, 0, &e);
                if (rc == ERR_OK) {
                    break;
                }
                hit = true;
                m.fail_at = 0;
                if (rc == ERR_NOMEM && db.state == DB_ACTIVE) {
                    refused++;
                    CHECK_EQ(db_recount(&db), 0);
                    continue;
                }
                CHECK_EQ(rc, ERR_FAILED);
                failed++;
                dead = true;
                break;
            }
            if (!dead && i % 10 == 9) {
                int32_t len;
                uint64_t sum;
                rc = get_key(&db, 1000 + 5 * i, i, &len, &sum, &e);
                if (rc != ERR_OK) {
                    hit = true;
                    m.fail_at = 0;
                    if (rc == ERR_FAILED) {
                        dead = true;
                    }
                }
                db_evict(&db);
            }
        }
        if (!dead) {
            CHECK_EQ(db_stream_length(&db), refLen);
            CHECK(memcmp(db.stream.bytes, ref.stream.bytes, (size_t) refLen) == 0);
            CHECK_EQ(db_recount(&db), 0);
        }
        db_close(&db, &e);
        CHECK_MEM_ZERO(&m);
        if (!hit && m.allocs < at) {
            break;
        }
    }
    db_close(&ref, &e);
    CHECK_MEM_ZERO(&mr);
    CHECK(refused > 0);
    CHECK(failed > 0);
    printf("  evict_alloc_failures: %lld runs: %lld transactions refused (NOMEM), %lld failed "
            "databases\n", (long long) runs, (long long) refused, (long long) failed);
}

/* The exact reference: clang's and gcc's 128-bit integers. */
__extension__ typedef unsigned __int128 u128;

static void check_low_of(int64_t budget) {
    CHECK_EQ(ev_low_of(budget), (int64_t) ((u128) (uint64_t) budget * 3 >> 2));
}

/* Eviction.testLowOfExact (bergdb 005-79): floor(3 budget / 4) for every
 * budget from 1, without overflow, against the exact product; INT64_MAX for
 * none. */
TEST(evict_low_of_exact) {
    CHECK_EQ(ev_low_of(INT64_MAX), INT64_MAX);
    const int64_t edges[] = {1, 2, 3, 4, 5, 0xFFFF, INT64_C(1) << 47, (INT64_C(1) << 53) / 3,
            (INT64_C(1) << 53) / 3 + 1, INT64_C(1) << 53, INT64_MAX - 2, INT64_MAX - 1};
    for (size_t i = 0; i < sizeof edges / sizeof edges[0]; i++) {
        check_low_of(edges[i]);
    }
    uint64_t z = 79;
    for (int i = 0; i < 100000; i++) {
        z += UINT64_C(0x9E3779B97F4A7C15);
        uint64_t x = (z ^ (z >> 30)) * UINT64_C(0xBF58476D1CE4E5B9);
        x = (x ^ (x >> 27)) * UINT64_C(0x94D049BB133111EB);
        x ^= x >> 31;
        const int64_t b = (int64_t) ((x >> 1) >> (x & 63));
        if (b >= 1 && b < INT64_MAX) {
            check_low_of(b);
        }
    }
}

const struct test evict_tests[] = {
    TEST_ENTRY(evict_low_of_exact),
    TEST_ENTRY(evict_table),
    TEST_ENTRY(evict_floor_after_shrink),
    TEST_ENTRY(evict_detachable),
    TEST_ENTRY(evict_twins),
    TEST_ENTRY(evict_large_value),
    TEST_ENTRY(evict_alloc_failures),
    TEST_END
};
