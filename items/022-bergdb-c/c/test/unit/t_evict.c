/* Eviction to a memory budget (bergdb 012-12; evict.h): the node table's
 * eviction, bytes and shrink; twins, a database without eviction and one
 * with a budget, the same transactions and reads: the same stream byte for
 * byte after every transaction, the same answers at every time, the counts
 * right (the recount), the pins in the node table, the resident bytes at
 * most the trigger; the setter's eviction in its call; the admission of a
 * large value, also of a start's rerun (015-68) and of its section's first
 * transaction (019-47); a warmup that keeps no large value (019-22); a
 * lowered budget reached after the pins fell (015-70); the allocation
 * failures in turn under a budget of one byte; eviction after a refused
 * transaction (022-06, U1-3); and a scan under what must stay, linear in
 * its keys (022-06, U1-4). Each test ends with the allocator's count 0. */
#define _DARWIN_C_SOURCE        /* mkdtemp */
#include <dirent.h>
#include <stdlib.h>
#include <unistd.h>
#include "test.h"
#include "api.h"
#include "bergdb.h"
#include "db.h"
#include "evict.h"
#include "handle.h"
#include "keys.h"
#include "knode.h"
#include "ntable.h"
#include "plat.h"
#include "spos.h"
#include "stream.h"
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
        /* At most the budget plus what is pinned, or what is pinned plus the
         * node table's bytes, the margin over the floor of a budget under it
         * (022-06, U1-4; the budget may be INT64_MAX). While a floor raises
         * the trigger, what is pinned may be less than the floor by 'stale':
         * a transaction and its take can leave D with as many nodes as at
         * the floor's sweep (ev_run takes the floor as old only when D has
         * fewer) but with fewer bytes. Until 022-07 this check had no such
         * term and held on these seeds; the trees of release 2026.4's
         * deletes made one case of 120 bytes (budget 2,000, node size 8,
         * seed 12, transaction 226: D of 7 nodes before and after). */
        const int64_t table = nt_bytes(&sub.node_table);
        const int64_t pinned = db_pinned_bytes(&sub);
        const int64_t stale = sub.ev.trigger > sub.ev.high && sub.ev.floor > pinned
                ? sub.ev.floor - pinned : 0;
        CHECK(db_resident_bytes(&sub) - pinned
                <= (sub.ev.high > table ? sub.ev.high : table) + stale);
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

/* ======== The dead hand (bergdb 023-07, section 5.6; 022-07) ======== */

struct dead_twin {
    struct mem m0, m1;
    struct db ref, sub;
    struct bergdb_test_clock k0, k1;
    int64_t time;
    int32_t checks;
};

/* One transaction on both: n operations, ikeys[i] put with values[i], or
 * deleted if values[i] is NULL. */
static void dead_trans(struct dead_twin *w, const char *const *ikeys, const char *const *values,
        int n) {
    w->time += 5 * (CLK_UNITS_PER_SEC / 100);
    bergdb_test_clock_set(&w->k0, w->time);
    bergdb_test_clock_set(&w->k1, w->time);
    struct db *dbs[2] = { &w->ref, &w->sub };
    struct mem *mems[2] = { &w->m0, &w->m1 };
    for (int d = 0; d < 2; d++) {
        struct tr_builder b;
        struct trans t;
        struct err e;
        tr_builder_init(&b, mems[d]);
        tr_init(&t, mems[d]);
        enum err_code rc = ERR_OK;
        for (int i = 0; i < n && rc == ERR_OK; i++) {
            uint8_t bkey[64];
            int32_t kl = (int32_t) strlen(ikeys[i]);
            keys_ikey_to_bkey((const uint8_t *) ikeys[i], kl, bkey);
            rc = values[i] == NULL ? tr_delete(&b, bkey, kl, &e)
                    : tr_put(&b, bkey, kl, (const uint8_t *) values[i],
                            (int32_t) strlen(values[i]), NULL, &e);
        }
        if (rc == ERR_OK) {
            rc = tr_build(&b, &t, &e);
        }
        if (rc == ERR_OK) {
            rc = db_execute(dbs[d], &t, &e);
        }
        CHECK_EQ(rc, ERR_OK);
        tr_free(&t);
        tr_builder_free(&b);
    }
}

/* Twin.checkDead: the dead hand's guarantee, once its round for the decided
 * cut is done: no detachable object stored before the cut is in sub's node
 * table, and no key node there holds a value stored before it. */
static void dead_check(struct dead_twin *w) {
    struct db *db = &w->sub;
    const int64_t cut = db_first_available_pos(db);
    if (cut == 0 || cut != db->ev.dead_round_cut) {
        return;
    }
    int64_t bad = 0;
    for (int64_t i = 0; i < nt_slots(&db->node_table); i++) {
        struct handle *h = nt_slot(&db->node_table, i);
        struct node *o = h == NULL ? NULL : h->obj;
        if (o == NULL) {
            continue;
        }
        const int64_t spos = o->spos;
        if (spos_is_valid(spos) && !spos_is_vpos(spos) && spos < cut
                && ev_detachable(o, tds_get_super_root(&db->dag.top_ds),
                        db->newest_written_top)) {
            bad++;      /* stored before the cut and resident */
        }
        if (o->o.kind != OBJ_KEY) {
            continue;
        }
        const struct knode *x = (const struct knode *) o;
        for (int32_t j = 0; j < x->size; j++) {
            const struct obj *p = kn_get_pointee(x, j);
            if (p == NULL || p->kind != OBJ_VALUE) {
                continue;
            }
            const int64_t vpos = ((const struct vnode *) p)->n.spos;
            if (spos_is_valid(vpos) && !spos_is_vpos(vpos) && vpos < cut
                    && !node_is_in_trans_nodes((const struct node *) p)) {
                bad++;  /* a value stored before the cut, held by a key node */
            }
        }
    }
    CHECK_EQ(bad, 0);
    w->checks++;
}

/* The twins' streams are the same from the cut, and their answers. */
static void dead_compare(struct dead_twin *w, const char *const *ikeys, int n) {
    struct err e;
    CHECK_EQ(db_stream_length(&w->ref), db_stream_length(&w->sub));
    CHECK_EQ(db_first_available_pos(&w->ref), db_first_available_pos(&w->sub));
    int64_t from = stream_first_pos(&w->ref.stream);
    if (from < stream_first_pos(&w->sub.stream)) {
        from = stream_first_pos(&w->sub.stream);
    }
    const int64_t length = db_stream_length(&w->ref);
    uint8_t a[4096], b[4096];
    bool same = true;
    for (int64_t pos = from; same && pos < length; pos += 4096) {
        const int32_t len = (int32_t) (length - pos < 4096 ? length - pos : 4096);
        same = stream_read(&w->ref.stream, pos, a, len, &e) == ERR_OK
                && stream_read(&w->sub.stream, pos, b, len, &e) == ERR_OK
                && memcmp(a, b, (size_t) len) == 0;
    }
    CHECK(same);        /* the stream is the twin's without eviction */
    const int64_t first = db_first_available_time(&w->ref);
    const int64_t times[3] = { INT64_MAX, first, first + (w->time - first) / 2 };
    for (int t = 0; t < 3; t++) {
        for (int i = 0; i < n; i++) {
            uint8_t bkey[64];
            int32_t kl = (int32_t) strlen(ikeys[i]);
            keys_ikey_to_bkey((const uint8_t *) ikeys[i], kl, bkey);
            int64_t segs[16];
            keys_to_segments(bkey, kl, segs);
            struct getdata gd;
            struct vnode *v0 = NULL, *v1 = NULL;
            db_new_get_data(&w->ref, &gd);
            CHECK(db_get_one(&w->ref, times[t], segs, keys_segment_count(kl), &gd, &v0, &e)
                    == ERR_OK);
            const int32_t l0 = v0 == NULL ? -2 : v0->len;
            uint64_t s0 = 0;
            for (int32_t j = 0; v0 != NULL && j < v0->len; j++) {
                s0 = s0 * 31 + v0->value[j];
            }
            db_new_get_data(&w->sub, &gd);
            CHECK(db_get_one(&w->sub, times[t], segs, keys_segment_count(kl), &gd, &v1, &e)
                    == ERR_OK);
            const int32_t l1 = v1 == NULL ? -2 : v1->len;
            uint64_t s1 = 0;
            for (int32_t j = 0; v1 != NULL && j < v1->len; j++) {
                s1 = s1 * 31 + v1->value[j];
            }
            CHECK_EQ(l0, l1);
            CHECK(s0 == s1);
            db_evict(&w->ref);
            db_evict(&w->sub);
        }
    }
    CHECK_EQ(db_recount(&w->sub), 0);
}

/* Java's Eviction.testDeadHand, without its restarts (databases in memory):
 * with a budget far above what the database needs, so that the capacity
 * controller takes nothing, keys are put, most of them deleted, and one key
 * overwritten until reclaim has cut several times. After every transaction
 * whose round for the decided cut is done, no detachable object stored
 * before the cut is resident, and no resident key node holds a value stored
 * before it; the hand has taken objects and values; the stream is the
 * twin's without eviction, byte for byte, and the lookups are the same.
 * The twin without a budget (BERGDB_NO_EVICT) has no dead hand. */
TEST(evict_dead_hand) {
    struct dead_twin *w = calloc(1, sizeof *w);
    struct db_config c0, c1;
    struct db_start_info info;
    struct err e;
    mem_init(&w->m0);
    mem_init(&w->m1);
    config(&c0, &w->k0, 8, 300, INT64_MAX);
    config(&c1, &w->k1, 8, 300, INT64_C(1) << 30);
    w->time = 100 * (CLK_UNITS_PER_SEC / 100);
    bergdb_test_clock_set(&w->k0, w->time);
    bergdb_test_clock_set(&w->k1, w->time);
    REQUIRE(db_open(&w->ref, NULL, &c0, &w->m0, &info, &e) == ERR_OK);
    REQUIRE(db_open(&w->sub, NULL, &c1, &w->m1, &info, &e) == ERR_OK);
    REQUIRE(db_set_retain_duration(&w->ref, CLK_UNITS_PER_SEC, &e) == ERR_OK);
    REQUIRE(db_set_retain_duration(&w->sub, CLK_UNITS_PER_SEC, &e) == ERR_OK);

    char big[301];
    for (int i = 0; i < 300; i++) {
        big[i] = (char) ('a' + i % 26);
    }
    big[300] = '\0';
    enum { N = 120 };
    static char keys[N + 1][16];
    static char vals[10][320];
    const char *all[N + 1];
    for (int i = 0; i < N; i++) {
        snprintf(keys[i], sizeof keys[i], "k%d", 1000 + i);
        all[i] = keys[i];
    }
    snprintf(keys[N], sizeof keys[N], "a");
    all[N] = keys[N];
    for (int i = 0; i < N; i += 10) {
        const char *k[10], *v[10];
        for (int j = 0; j < 10; j++) {
            snprintf(vals[j], sizeof vals[j], "%d%s", i, big);
            k[j] = keys[i + j];
            v[j] = vals[j];
        }
        dead_trans(w, k, v, 10);
        dead_check(w);
    }
    dead_compare(w, all, N + 1);
    for (int i = 0; i < N; i += 10) {
        const char *k[10], *v[10];
        for (int j = 0; j < 10; j++) {
            k[j] = keys[i + j];
            v[j] = (i + j) % 37 == 0 ? "x" : NULL;
        }
        dead_trans(w, k, v, 10);
        dead_check(w);
    }
    dead_compare(w, all, N + 1);
    for (int i = 0; i < 300; i++) {
        const char *k = keys[N], *v = vals[0];
        snprintf(vals[0], sizeof vals[0], "%d%s", i, big);
        dead_trans(w, &k, &v, 1);
        dead_check(w);
        if (i % 100 == 99) {
            dead_compare(w, all, N + 1);
        }
    }
    dead_compare(w, all, N + 1);
    CHECK(db_first_available_pos(&w->sub) > 0);     /* a cut */
    CHECK(w->sub.ev.dead_rounds > 0);               /* rounds of the dead hand */
    CHECK(w->sub.ev.dead_objects > 0);              /* objects it took */
    CHECK(w->sub.ev.dead_values > 0);               /* values it took */
    CHECK(w->checks > 10);
    CHECK_EQ(w->ref.ev.dead_rounds, 0);             /* no budget: no dead hand */
    CHECK_EQ(w->ref.ev.evicted, 0);
    printf("  evict_dead_hand: %lld rounds, %lld objects, %lld values, %d checks; resident "
            "bytes %lld with the hand, %lld without\n", (long long) w->sub.ev.dead_rounds,
            (long long) w->sub.ev.dead_objects, (long long) w->sub.ev.dead_values,
            (int) w->checks, (long long) db_resident_bytes(&w->sub),
            (long long) db_resident_bytes(&w->ref));
    CHECK(db_resident_bytes(&w->sub) < db_resident_bytes(&w->ref));
    db_close(&w->ref, &e);
    db_close(&w->sub, &e);
    CHECK_MEM_ZERO(&w->m0);
    CHECK_MEM_ZERO(&w->m1);
    free(w);
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

/* A temporary directory, for a database that restarts. */
static bool temp_dir(char *out, size_t cap) {
    const char *t = getenv("TMPDIR");
    snprintf(out, cap, "%s/bergdb-t_evict-XXXXXX", t != NULL ? t : "/tmp");
    return mkdtemp(out) != NULL;
}

static void remove_dir(const char *dir) {
    DIR *d = opendir(dir);
    struct dirent *x;
    char path[512];
    if (d == NULL) {
        return;
    }
    while ((x = readdir(d)) != NULL) {
        if (x->d_name[0] != '.') {
            snprintf(path, sizeof path, "%s/%s", dir, x->d_name);
            unlink(path);
        }
    }
    closedir(d);
    rmdir(dir);
}

/* A transaction of puts of the ikeys, each with value (len bytes), at
 * clock time tt. */
static enum err_code exec_puts(struct db *db, struct mem *m, struct bergdb_test_clock *clock,
        int64_t tt, const char *const *ikeys, int n, const uint8_t *value, int32_t len,
        struct err *e) {
    struct tr_builder b;
    struct trans t;
    tr_builder_init(&b, m);
    tr_init(&t, m);
    bergdb_test_clock_set(clock, tt);
    enum err_code rc = ERR_OK;
    for (int i = 0; i < n && rc == ERR_OK; i++) {
        uint8_t bkey[64];
        const int32_t kl = (int32_t) strlen(ikeys[i]);
        keys_ikey_to_bkey((const uint8_t *) ikeys[i], kl, bkey);
        rc = tr_put(&b, bkey, kl, value, len, NULL, e);
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

/* Eviction's largeResident: the pointers of the node table's key nodes that
 * hold a value over 1 MiB. */
static int large_resident(const struct db *db) {
    int large = 0;
    for (int64_t s = 0; s < nt_slots(&db->node_table); s++) {
        const struct handle *h = nt_slot(&db->node_table, s);
        if (h == NULL || h->obj == NULL || h->obj->o.kind != OBJ_KEY) {
            continue;
        }
        const struct knode *x = (const struct knode *) h->obj;
        for (int32_t i = 0; i < x->size; i++) {
            const struct obj *p = kn_get_pointee(x, i);
            if (p != NULL && p->kind == OBJ_VALUE
                    && ((const struct vnode *) p)->len > EV_LARGE_VALUE) {
                large++;
            }
        }
    }
    return large;
}

/* Eviction.testStartAdmitsLargeValues (bergdb 015-68, as Java's since
 * release 2026.3): a start applies the admission to the large values that
 * its rerun of the transactions made. Three values of 1,200 KiB, over 1
 * MiB, in one transaction; the database restarted from its directory with a
 * budget of 100 MB, so that no sweep takes them. After the open the
 * admission list is empty, and no resident pointer holds a value over 1
 * MiB: they are stream pointers, as after the record of a transaction that
 * the open database writes (ev_record_written). Until 022-01, step 4, the
 * rerun's PutData had no pointer-created listener, so the three stayed in
 * their leaf, counted in the resident bytes, until a sweep took them. */
TEST(evict_start_admits_large_values) {
    char dir[256];
    REQUIRE(temp_dir(dir, sizeof dir));
    struct mem m;
    struct err e;
    struct db db;
    struct db_config c;
    struct db_start_info info;
    struct bergdb_test_clock k = {0};
    mem_init(&m);
    config(&c, &k, 30, 50000000, INT64_MAX);       /* testSetup: no eviction */
    bergdb_test_clock_set(&k, 500);
    REQUIRE(db_open(&db, dir, &c, &m, &info, &e) == ERR_OK);
    const int32_t len = 1200 * 1024;
    uint8_t *value = calloc((size_t) len, 1);
    REQUIRE(value != NULL);
    const char *const keys[] = {"a", "b", "c"};
    CHECK(exec_puts(&db, &m, &k, 1000, keys, 3, value, len, &e) == ERR_OK);
    CHECK(db_close(&db, &e) == ERR_OK);
    CHECK_MEM_ZERO(&m);

    config(&c, &k, 30, 50000000, 100000000);
    REQUIRE(db_open(&db, dir, &c, &m, &info, &e) == ERR_OK);
    CHECK_EQ(info.trans_count, 2);          /* the large values' record rerun */
    CHECK_EQ(db.ev.nlarge, 0);
    CHECK_EQ(large_resident(&db), 0);
    CHECK(db_resident_bytes(&db) < len);
    CHECK_EQ(db.ev.sweeps, 0);              /* the admission, not a sweep */
    uint8_t bkey[8];
    keys_ikey_to_bkey((const uint8_t *) "b", 1, bkey);
    int64_t segs[8];
    keys_to_segments(bkey, 1, segs);
    struct getdata gd;
    db_new_get_data(&db, &gd);
    struct vnode *v = NULL;
    CHECK(db_get_one(&db, INT64_MAX, segs, keys_segment_count(1), &gd, &v, &e) == ERR_OK);
    REQUIRE(v != NULL);
    CHECK_EQ(v->len, len);
    CHECK(memcmp(v->value, value, (size_t) len) == 0);
    db_evict(&db);
    CHECK_EQ(large_resident(&db), 0);
    CHECK_EQ(db_recount(&db), 0);
    CHECK(db_close(&db, &e) == ERR_OK);
    CHECK_MEM_ZERO(&m);
    free(value);

    /* The allocation failures in turn in the start, the list's growth in the
     * rerun among them: each open refuses (NOMEM) and leaves nothing, the
     * list's holds released, or opens with the list drained. */
    int64_t runs = 0, refused = 0;
    for (int64_t at = 1; at < 100000; at++) {
        struct mem mf;
        mem_init(&mf);
        mf.fail_at = at;
        enum err_code rc = db_open(&db, dir, &c, &mf, &info, &e);
        runs++;
        if (rc != ERR_OK) {
            CHECK_EQ(rc, ERR_NOMEM);
            CHECK_MEM_ZERO(&mf);
            refused++;
            continue;
        }
        CHECK_EQ(db.ev.nlarge, 0);
        CHECK_EQ(large_resident(&db), 0);
        db_close(&db, &e);
        CHECK_MEM_ZERO(&mf);
        if (mf.allocs < at) {
            break;
        }
    }
    CHECK(refused > 0);
    printf("  evict_start_admits_large_values: %lld starts, %lld refused (NOMEM)\n",
            (long long) runs, (long long) refused);
    remove_dir(dir);
}

/* A transaction of n puts, ikeys[i] with values[i] of lens[i] bytes, at
 * clock time tt; *tpos its record's position. */
static enum err_code exec_kvs(struct db *db, struct mem *m, struct bergdb_test_clock *clock,
        int64_t tt, int n, const char *const *ikeys, const uint8_t *const *values,
        const int32_t *lens, int64_t *tpos, struct err *e) {
    struct tr_builder b;
    struct trans t;
    tr_builder_init(&b, m);
    tr_init(&t, m);
    bergdb_test_clock_set(clock, tt);
    enum err_code rc = ERR_OK;
    for (int i = 0; i < n && rc == ERR_OK; i++) {
        uint8_t bkey[64];
        const int32_t kl = (int32_t) strlen(ikeys[i]);
        keys_ikey_to_bkey((const uint8_t *) ikeys[i], kl, bkey);
        rc = tr_put(&b, bkey, kl, values[i], lens[i], NULL, e);
    }
    if (rc == ERR_OK) {
        rc = tr_build(&b, &t, e);
    }
    if (rc == ERR_OK) {
        rc = db_execute(db, &t, e);
    }
    if (rc == ERR_OK) {
        *tpos = t.tpos;
    }
    tr_free(&t);
    tr_builder_free(&b);
    return rc;
}

/* getOne of ikey at the newest time: the value equals the len bytes of
 * expected. */
static bool value_is(struct db *db, const char *ikey, const uint8_t *expected, int32_t len) {
    uint8_t bkey[64];
    const int32_t kl = (int32_t) strlen(ikey);
    keys_ikey_to_bkey((const uint8_t *) ikey, kl, bkey);
    int64_t segs[16];
    keys_to_segments(bkey, kl, segs);
    struct getdata gd;
    db_new_get_data(db, &gd);
    struct vnode *v = NULL;
    struct err e;
    return db_get_one(db, INT64_MAX, segs, keys_segment_count(kl), &gd, &v, &e) == ERR_OK
            && v != NULL && v->len == len && memcmp(v->value, expected, (size_t) len) == 0;
}

/* Eviction.testStartAdmitsLargeValuesOfTheSectionsFirstTransaction (bergdb
 * 019-47, as Java's since release 2026.4): a start whose startup section
 * begins with the transaction of a large value does not keep that value
 * either. The section's first transaction is not rerun; its values are
 * linked into the section's node versions (starter.c's
 * create_memory_pointers), which the rerun's pointer-created listener does
 * not see, so 015-68's admission, of the list alone, left the value in its
 * leaf. A startup distance of 200 bytes; a large value ("a", with a small
 * "b") in one transaction, and with extra a second ("c") in a later one.
 * With extra, the next start's section begins with "a"'s transaction (264,
 * at "c"'s record), which is not rerun, and the start reruns "c"'s: the
 * admission takes "c" from its list, as before, and "a" only by the pass
 * over the resident key nodes. Without extra, the section begins with the
 * creation, the start reruns "a"'s transaction, and its list has the value
 * (015-68's case). Java's start gives the same sections (startPos 0 and
 * 264, two transactions each; checked with a probe on the candidate). The
 * restart with a budget of 100 MB, so that no sweep takes them. Before the
 * fix, with extra: 1 resident pointer to a value over 1 MiB after the
 * start, and after the reads, as Java's before 019-47. Then the allocation
 * failures in turn in that start: each open refuses (NOMEM) and leaves
 * nothing, or opens with no large value resident. */
TEST(evict_start_admits_first_transactions_large_values) {
    const int32_t len = 1200 * 1024;
    uint8_t *value = calloc((size_t) len, 1);
    REQUIRE(value != NULL);
    const uint8_t *small = (const uint8_t *) "small";
    for (int extra = 0; extra < 2; extra++) {
        char dir[256];
        REQUIRE(temp_dir(dir, sizeof dir));
        struct mem m;
        struct err e;
        struct db db;
        struct db_config c;
        struct db_start_info info;
        struct bergdb_test_clock k = {0};
        mem_init(&m);
        config(&c, &k, 30, 200, INT64_MAX);         /* testSetup: no eviction */
        bergdb_test_clock_set(&k, 500);
        REQUIRE(db_open(&db, dir, &c, &m, &info, &e) == ERR_OK);
        const char *const ab[] = {"a", "b"};
        const uint8_t *const abv[] = {value, small};
        const int32_t abl[] = {len, 5};
        int64_t tposA = -1, tposC = -1;
        CHECK(exec_kvs(&db, &m, &k, 1000, 2, ab, abv, abl, &tposA, &e) == ERR_OK);
        if (extra == 1) {
            const char *const cc[] = {"c"};
            const uint8_t *const cv[] = {value};
            CHECK(exec_kvs(&db, &m, &k, 1001, 1, cc, cv, &len, &tposC, &e) == ERR_OK);
        }
        CHECK(db_close(&db, &e) == ERR_OK);
        CHECK_MEM_ZERO(&m);

        config(&c, &k, 30, 200, 100000000);
        REQUIRE(db_open(&db, dir, &c, &m, &info, &e) == ERR_OK);
        CHECK_EQ(info.start_pos, extra == 1 ? tposA : 0);
        CHECK_EQ(tposA, 264);
        CHECK_EQ(info.trans_count, 2);
        CHECK_EQ(db.ev.nlarge, 0);
        CHECK_EQ(large_resident(&db), 0);
        CHECK(db_resident_bytes(&db) < len);
        CHECK_EQ(db.ev.sweeps, 0);              /* the admission, not a sweep */
        CHECK_EQ(db_recount(&db), 0);
        CHECK(value_is(&db, "a", value, len));
        CHECK(value_is(&db, "b", small, 5));
        if (extra == 1) {
            CHECK(value_is(&db, "c", value, len));
        }
        db_evict(&db);
        CHECK_EQ(large_resident(&db), 0);       /* after the reads */
        CHECK_EQ(db_recount(&db), 0);
        CHECK(db_close(&db, &e) == ERR_OK);
        CHECK_MEM_ZERO(&m);

        int64_t runs = 0, refused = 0;
        for (int64_t at = 1; at < 100000; at++) {
            struct mem mf;
            mem_init(&mf);
            mf.fail_at = at;
            enum err_code rc = db_open(&db, dir, &c, &mf, &info, &e);
            runs++;
            if (rc != ERR_OK) {
                CHECK_EQ(rc, ERR_NOMEM);
                CHECK_MEM_ZERO(&mf);
                refused++;
                continue;
            }
            CHECK_EQ(db.ev.nlarge, 0);
            CHECK_EQ(large_resident(&db), 0);
            db_close(&db, &e);
            CHECK_MEM_ZERO(&mf);
            if (mf.allocs < at) {
                break;
            }
        }
        CHECK(refused > 0);
        printf("  evict_start_admits_first_transactions_large_values (%d more): %lld starts, "
                "%lld refused (NOMEM)\n", extra, (long long) runs, (long long) refused);
        remove_dir(dir);
    }
    free(value);
}

/* Eviction.testWarmupKeepsNoLargeValue (bergdb 019-22, as Java's since
 * release 2026.3): a transaction's warmup keeps no value over 1 MiB. A
 * key's value of 1,200 KiB is written, and the admission takes it from its
 * pointer; a transaction then puts a small value for the key. Its warmup
 * (db.c's warmup, Db.warmup) reads the key first, and the old large value
 * is the latest; with a cache policy that keeps it, the read puts it back
 * into the leaf's pointer, where it stays, as the budget of 100 MB starts
 * no sweep (Java's warmup had Dag.CACHE_ALL until 019-22). C's warmup reads
 * with the get's policy, cache_all_except_large (dag_new_get_data), as
 * Java's since 019-22 (012-18, section 3.3): this test shows it. */
TEST(evict_warmup_keeps_no_large_value) {
    struct mem m;
    struct err e;
    struct db db;
    struct db_config c;
    struct db_start_info info;
    struct bergdb_test_clock k = {0};
    mem_init(&m);
    config(&c, &k, 30, 50000000, 100000000);
    bergdb_test_clock_set(&k, 500);
    REQUIRE(db_open(&db, NULL, &c, &m, &info, &e) == ERR_OK);
    const int32_t len = 1200 * 1024;
    uint8_t *value = calloc((size_t) len, 1);
    REQUIRE(value != NULL);
    const char *const keys[] = {"a"};
    CHECK(exec_puts(&db, &m, &k, 1000, keys, 1, value, len, &e) == ERR_OK);
    CHECK_EQ(large_resident(&db), 0);       /* after the large value's record */
    CHECK(exec_puts(&db, &m, &k, 1010, keys, 1, (const uint8_t *) "small", 5, &e) == ERR_OK);
    CHECK_EQ(large_resident(&db), 0);       /* after the transaction that replaces it */
    CHECK(db_resident_bytes(&db) < len);
    CHECK_EQ(db.ev.sweeps, 0);              /* no sweep took it */
    uint8_t bkey[8];
    keys_ikey_to_bkey((const uint8_t *) "a", 1, bkey);
    int64_t segs[8];
    keys_to_segments(bkey, 1, segs);
    struct getdata gd;
    db_new_get_data(&db, &gd);
    struct vnode *v = NULL;
    CHECK(db_get_one(&db, 1000, segs, keys_segment_count(1), &gd, &v, &e) == ERR_OK);
    REQUIRE(v != NULL);                     /* the old value read */
    CHECK_EQ(v->len, len);
    CHECK(memcmp(v->value, value, (size_t) len) == 0);
    db_new_get_data(&db, &gd);
    v = NULL;
    CHECK(db_get_one(&db, INT64_MAX, segs, keys_segment_count(1), &gd, &v, &e) == ERR_OK);
    REQUIRE(v != NULL);
    CHECK_EQ(v->len, 5);
    db_evict(&db);
    CHECK_EQ(large_resident(&db), 0);
    CHECK_EQ(db_recount(&db), 0);
    CHECK(db_close(&db, &e) == ERR_OK);
    CHECK_MEM_ZERO(&m);
    free(value);
}

/* Evicts the detachable objects of the node table, as a sweep does, until
 * the resident bytes are at most target. */
static void evict_down_to(struct db *db, int64_t target) {
    struct ntable *nt = &db->node_table;
    const struct tnode *superRoot = tds_get_super_root(&db->dag.top_ds);
    int64_t s = 0;
    while (s < nt_slots(nt) && db_resident_bytes(db) > target) {
        struct handle *h = nt_slot(nt, s);
        if (h != NULL && h->obj != NULL
                && ev_detachable(h->obj, superRoot, db->newest_written_top)) {
            nt_evict(nt, h);        /* a later entry may move into slot s */
            obj_collect(&db->cx);
            continue;
        }
        s++;
    }
}

/* Eviction.testLoweredBudgetAfterPinsFell (bergdb 015-70, as Java's since
 * release 2026.3; 016-06, R4-F5): a lowered budget is reached when the pins
 * have fallen since the last sweep of two rounds, whose floor (C's measure
 * of Java's pinnedOfLastRound) is then old. 500 transactions of one key,
 * nodes of at most 8 entries and a startup distance of 2,000 bytes, so
 * that much of the tree is dirty (pinned); the budget lowered to 1 byte:
 * the call's sweeps end with the floor P0, and it stays idle after (019-41:
 * few sweeps, none at the next call); the budget raised, and a transaction
 * whose take writes the dirty nodes, so that the pins fall to P1, below P0.
 * Then detachable objects are evicted, as a sweep does, until the resident
 * bytes are at most P0, and the budget is lowered to between P1 and P0,
 * with no other call. The call brings the resident bytes to at most the
 * budget: the pins fit. Then a budget of half P1, below the pins: the call's
 * sweeps end, and the next call sweeps nothing. Java's bug, a batch that
 * counted down to the old pins and a trigger made of them, was not C's:
 * ev_set_budget sets the trigger to the budget, and a sweep goes down to the
 * low watermark or over two rounds whatever the floor. */
TEST(evict_lowered_budget_after_pins_fell) {
    struct mem m;
    struct err e;
    struct db db;
    struct db_config c;
    struct db_start_info info;
    struct bergdb_test_clock k = {0};
    mem_init(&m);
    config(&c, &k, 8, 2000, INT64_MAX);
    bergdb_test_clock_set(&k, 500);
    REQUIRE(db_open(&db, NULL, &c, &m, &info, &e) == ERR_OK);
    uint8_t value[100] = {0};
    int64_t time = 1000;
    for (int i = 0; i < 500; i++) {
        char ikey[16];
        snprintf(ikey, sizeof ikey, "k%d", i);
        const char *const keys[] = {ikey};
        REQUIRE(exec_puts(&db, &m, &k, time += 10, keys, 1, value, 100, &e) == ERR_OK);
    }
    int64_t sweeps = db.ev.sweeps;
    const int64_t complete = db.ev.complete_sweeps;
    REQUIRE(db_set_cache_size_indicator(&db, 1, &e) == ERR_OK);
    CHECK(db.ev.complete_sweeps > complete);
    CHECK(db.ev.sweeps - sweeps < 100);         /* below the pins: few sweeps (019-41) */
    sweeps = db.ev.sweeps;
    db_evict(&db);
    CHECK_EQ(db.ev.sweeps, sweeps);             /* and idle after */
    const int64_t p0 = db.ev.floor;
    CHECK_EQ(db_resident_bytes(&db), p0);

    REQUIRE(db_set_cache_size_indicator(&db, INT64_MAX, &e) == ERR_OK);
    const char *const flush[] = {"flush"};
    REQUIRE(exec_puts(&db, &m, &k, time += 10, flush, 1, value, 100, &e) == ERR_OK);
    const int64_t p1 = db_pinned_bytes(&db);
    evict_down_to(&db, p0);
    int64_t bytes = db_resident_bytes(&db);
    CHECK_EQ(db.ev.floor, p0);                  /* no sweep of two rounds since */
    struct ev_env env = env_of(&db);
    CHECK_EQ(ev_check_pins(&env), 0);
    CHECK_EQ(db_recount(&db), 0);
    const int64_t budget = (p1 + p0) / 2;
    printf("  evict_lowered_budget_after_pins_fell: P0 %lld, P1 %lld, budget %lld, "
            "resident %lld\n", (long long) p0, (long long) p1, (long long) budget,
            (long long) bytes);
    CHECK(p1 < budget);                         /* the pins fell */
    CHECK(budget < bytes && bytes <= p0);       /* detachable objects resident */
    REQUIRE(db_set_cache_size_indicator(&db, budget, &e) == ERR_OK);
    bytes = db_resident_bytes(&db);
    CHECK(bytes <= budget);
    sweeps = db.ev.sweeps;
    db_evict(&db);
    CHECK_EQ(db.ev.sweeps, sweeps);             /* idle after */

    /* A budget below the pins: the sweeps end, and the next call sweeps
     * nothing. */
    REQUIRE(db_set_cache_size_indicator(&db, p1 / 2, &e) == ERR_OK);
    CHECK(db.ev.sweeps - sweeps < 100);
    sweeps = db.ev.sweeps;
    db_evict(&db);
    CHECK_EQ(db.ev.sweeps, sweeps);
    CHECK(db_resident_bytes(&db) > p1 / 2);
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
                    /* The refusal's end evicts what its warmup loaded
                     * (bergdb 022-06, U1-3). */
                    CHECK(db_resident_bytes(&db) <= db.ev.trigger);
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

/* A clock that refuses when told: -1, outside the clock's range. */
struct refusing_clock {
    int64_t time;
    bool refuse;
};

static int64_t refusing_clock_time(void *ctx) {
    const struct refusing_clock *c = ctx;
    return c->refuse ? -1 : c->time;
}

/* n puts of the keys {0x10, i >> 8, i}, i from 0, with values of len bytes,
 * each byte b. */
static void api_puts(bergdb_trans *t, int n, size_t len, uint8_t b) {
    uint8_t *v = malloc(len);
    REQUIRE(v != NULL);
    memset(v, b, len);
    for (int i = 0; i < n; i++) {
        const uint8_t k[3] = {0x10, (uint8_t) (i >> 8), (uint8_t) i};
        CHECK(bergdb_trans_put(t, k, 3, v, len) == BERGDB_OK);
    }
    free(v);
}

/* bergdb 022-06, U1-3 (the black-box user u1's budget_after_refusal.c): a
 * transaction refused before its go point leaves what its warmup loaded
 * resident, over the budget, until a later call evicts. The warmup reads
 * each put key's present value; Java's warmup loads wake its eviction
 * thread (Eviction.afterLoad, not paced), which evicts to the trigger
 * whatever the transaction's end; C evicts at the end of execute, refused
 * or not. A database in memory with a budget of 100,000 bytes and a
 * startup distance of 10 bytes (little is pinned), three transactions of
 * 400 puts of 2,000 bytes, then 400 such puts refused by the clock
 * (BERGDB_LIMIT) and by the STM (BERGDB_RERUN): after each refusal the
 * resident bytes are at most the trigger, and the stream is as it was.
 * Before the fix about 800 kB more stayed resident after each. */
TEST(evict_after_refused_transaction) {
    struct bergdb_mem m = {0};
    struct refusing_clock clk = {INT64_C(10000000000), false};
    struct bergdb_options o;
    bergdb_options_init(&o);
    o.clock = refusing_clock_time;
    o.clock_ctx = &clk;
    o.startup_distance = 10;
    o.cache_size_indicator = 100000;
    o.mem = &m;
    memcpy(o.id, bergdb_test_id, BERGDB_ID_SIZE);
    bergdb_db *db;
    REQUIRE(bergdb_open(NULL, &o, &db, NULL, NULL) == BERGDB_OK);
    const int n = 400;
    const size_t len = 2000;
    for (int r = 0; r < 3; r++) {
        bergdb_trans *t;
        REQUIRE(bergdb_trans_new(db, &t) == BERGDB_OK);
        api_puts(t, n, len, (uint8_t) r);
        clk.time += 1000;
        CHECK(bergdb_execute(db, t, NULL) == BERGDB_OK);
        bergdb_trans_free(t);
    }
    struct db *d = &db->db;
    const int64_t length = db_stream_length(d);
    const int64_t after_commits = db_resident_bytes(d);
    CHECK(after_commits <= d->ev.trigger);

    bergdb_trans *t;
    REQUIRE(bergdb_trans_new(db, &t) == BERGDB_OK);
    api_puts(t, n, len, 9);
    clk.refuse = true;
    CHECK_EQ(bergdb_execute(db, t, NULL), BERGDB_LIMIT);
    clk.refuse = false;
    bergdb_trans_free(t);
    const int64_t after_limit = db_resident_bytes(d);
    CHECK(after_limit <= d->ev.trigger);
    CHECK_EQ(db_stream_length(d), length);

    REQUIRE(bergdb_trans_new(db, &t) == BERGDB_OK);
    api_puts(t, n, len, 8);
    const uint8_t k0[3] = {0x10, 0, 0};
    CHECK(bergdb_trans_key_read(t, k0, 3) == BERGDB_OK);
    CHECK(bergdb_trans_lookup_time(t, 1) == BERGDB_OK);
    CHECK_EQ(bergdb_execute(db, t, NULL), BERGDB_RERUN);
    bergdb_trans_free(t);
    const int64_t after_rerun = db_resident_bytes(d);
    CHECK(after_rerun <= d->ev.trigger);
    CHECK_EQ(db_stream_length(d), length);
    CHECK_EQ(db_recount(d), 0);
    printf("  evict_after_refused_transaction: resident bytes %lld after the commits, "
            "%lld after LIMIT, %lld after RERUN; the trigger %lld\n",
            (long long) after_commits, (long long) after_limit, (long long) after_rerun,
            (long long) d->ev.trigger);
    CHECK(bergdb_close(db) == BERGDB_OK);
    CHECK_EQ(m.live_total, 0);
}

/* A stop function whose answer is out of range at a value of over 100 kB. */
static int bad_answer_at_big(void *ctx, const struct bergdb_kvt *kvt) {
    (void) ctx;
    return kvt->value_len > 100000 ? 99 : BERGDB_ADD;
}

/* U1-3's kind in the reads: a getMany or getOne refused at its end (a stop
 * function's answer out of range, BERGDB_ARG; NOMEM) evicts as one that
 * succeeds; before, the loads stayed until a later call. A database in
 * memory, the default startup distance (the leaves are D, pinned), a key a
 * with 10 bytes and b with 500,000; the budget then 100,000 bytes, so b's
 * value is out of memory. A getMany that loads b's value and is refused
 * there, and a getOne of b with each allocation failing in turn (a new read
 * context each time, whose buffer must grow for the value after its load):
 * after each refusal the resident bytes are at most the trigger (before:
 * b's value of 500 kB stayed in its pinned leaf). */
TEST(evict_after_refused_read) {
    struct bergdb_mem m = {0};
    struct bergdb_test_clock clock = {0};
    struct bergdb_options o;
    bergdb_options_init(&o);
    o.clock = bergdb_test_clock_time;
    o.clock_ctx = &clock;
    o.mem = &m;
    memcpy(o.id, bergdb_test_id, BERGDB_ID_SIZE);
    bergdb_test_clock_set(&clock, 500);
    bergdb_db *db;
    REQUIRE(bergdb_open(NULL, &o, &db, NULL, NULL) == BERGDB_OK);
    const size_t big = 500000;
    uint8_t *v = calloc(big, 1);
    REQUIRE(v != NULL);
    bergdb_trans *t;
    REQUIRE(bergdb_trans_new(db, &t) == BERGDB_OK);
    const uint8_t ka[2] = {0x30, 'a'}, kb[2] = {0x30, 'b'};
    CHECK(bergdb_trans_put(t, ka, 2, v, 10) == BERGDB_OK);
    CHECK(bergdb_trans_put(t, kb, 2, v, big) == BERGDB_OK);
    bergdb_test_clock_set(&clock, 1000);
    CHECK(bergdb_execute(db, t, NULL) == BERGDB_OK);
    bergdb_trans_free(t);
    free(v);
    CHECK(bergdb_set_cache_size_indicator(db, 100000) == BERGDB_OK);
    struct db *d = &db->db;
    CHECK(db_resident_bytes(d) <= d->ev.trigger);
    CHECK(db_resident_bytes(d) < (int64_t) big);

    bergdb_read *rd;
    REQUIRE(bergdb_read_new(db, &rd) == BERGDB_OK);
    struct bergdb_range r;
    bergdb_range_init(&r);
    r.stop = bad_answer_at_big;
    struct bergdb_many many;
    CHECK_EQ(bergdb_get_many(db, rd, &r, &many), BERGDB_ARG);
    const int64_t after_many = db_resident_bytes(d);
    CHECK(after_many <= d->ev.trigger);
    bergdb_read_free(rd);

    int refused = 0;
    for (int64_t k = 1; k < 1000; k++) {
        REQUIRE(bergdb_read_new(db, &rd) == BERGDB_OK);
        m.fail_at = m.allocs + k;
        struct bergdb_one one;
        const int rc = bergdb_get_one(db, rd, BERGDB_LATEST, kb, 2, &one);
        const bool hit = m.allocs >= m.fail_at;
        m.fail_at = 0;
        if (rc == BERGDB_NOMEM) {
            refused++;
            CHECK(db_resident_bytes(d) <= d->ev.trigger);
        } else {
            CHECK_EQ(rc, BERGDB_OK);
            CHECK(one.value_len == big);
        }
        bergdb_read_free(rd);
        if (!hit) {
            break;
        }
    }
    CHECK(refused > 0);
    CHECK_EQ(db_recount(d), 0);
    printf("  evict_after_refused_read: resident bytes %lld after the refused getMany, the "
            "trigger %lld; %d getOnes refused (NOMEM)\n", (long long) after_many,
            (long long) d->ev.trigger, refused);
    CHECK(bergdb_close(db) == BERGDB_OK);
    CHECK_EQ(m.live_total, 0);
}

/* One scan of evict_scan_is_linear: n keys of 4 bytes with values of 200
 * bytes in a database in memory, the default startup distance (50 MB: the
 * whole index is D, pinned), the budget then lowered to one byte, and a
 * getMany of every key through the API (a safe point after each pair). The
 * slots the hand looked at in the scan into *examined, its sweeps into
 * *sweeps. */
static void scan_at_one_byte(int n, int64_t *examined, int64_t *sweeps) {
    struct bergdb_mem m = {0};
    struct bergdb_test_clock clock = {0};
    struct bergdb_options o;
    bergdb_options_init(&o);
    o.clock = bergdb_test_clock_time;
    o.clock_ctx = &clock;
    o.mem = &m;
    memcpy(o.id, bergdb_test_id, BERGDB_ID_SIZE);
    bergdb_test_clock_set(&clock, 500);
    bergdb_db *db;
    REQUIRE(bergdb_open(NULL, &o, &db, NULL, NULL) == BERGDB_OK);
    uint8_t v[200];
    memset(v, 7, sizeof v);
    for (int i = 0; i < n; ) {
        bergdb_trans *t;
        REQUIRE(bergdb_trans_new(db, &t) == BERGDB_OK);
        for (int j = 0; j < 100 && i < n; j++, i++) {
            const uint8_t k[4] = {0x20, (uint8_t) (i >> 16), (uint8_t) (i >> 8), (uint8_t) i};
            CHECK(bergdb_trans_put(t, k, 4, v, sizeof v) == BERGDB_OK);
        }
        bergdb_test_clock_set(&clock, clock.time + 10);
        CHECK(bergdb_execute(db, t, NULL) == BERGDB_OK);
        bergdb_trans_free(t);
    }
    struct db *d = &db->db;
    CHECK(bergdb_set_cache_size_indicator(db, 1) == BERGDB_OK);
    CHECK(d->ev.floor > d->ev.high);            /* under what must stay */
    bergdb_read *rd;
    REQUIRE(bergdb_read_new(db, &rd) == BERGDB_OK);
    const int64_t e0 = d->ev.examined, s0 = d->ev.sweeps;
    struct bergdb_range r;
    bergdb_range_init(&r);
    struct bergdb_many many;
    CHECK(bergdb_get_many(db, rd, &r, &many) == BERGDB_OK);
    CHECK_EQ((int64_t) many.count, n);
    *examined = d->ev.examined - e0;
    *sweeps = d->ev.sweeps - s0;
    CHECK(db_resident_bytes(d) <= d->ev.trigger);
    CHECK_EQ(db_recount(d), 0);
    bergdb_read_free(rd);
    CHECK(bergdb_close(db) == BERGDB_OK);
    CHECK_EQ(m.live_total, 0);
}

/* bergdb 022-06, U1-4 (u1's evict_scan.c): with the budget under what must
 * stay (one byte, the gap between the watermarks one byte), each pair that
 * a full getMany loaded made a sweep of two rounds over the whole node
 * table, which grows with D: the scan's work was quadratic in its keys
 * (about 2 n slots per pair; 0.3 to 0.57 s for 8,000 keys against 0.001 s
 * at the default budget). A sweep that cannot reach the budget now comes
 * only after the calls have loaded the table's own bytes over the floor:
 * the scan's work is linear. Two scans, of 1,000 and 4,000 keys: the second
 * looks at most 8 times as many slots as the first (before: 16 times), and
 * at most 64 slots per key (before: 2,048). */
TEST(evict_scan_is_linear) {
    int64_t e1, s1, e4, s4;
    scan_at_one_byte(1000, &e1, &s1);
    scan_at_one_byte(4000, &e4, &s4);
    printf("  evict_scan_is_linear: 1,000 keys: %lld slots looked at in %lld sweeps; "
            "4,000 keys: %lld in %lld\n", (long long) e1, (long long) s1, (long long) e4,
            (long long) s4);
    CHECK(e4 <= 8 * e1);
    CHECK(e4 <= 64 * 4000);
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

/* ======== Harness 6.5, eviction's accounting, in C (022-05) ======== */

#define EA_LARGE (1100 * 1024)      /* a value over 1 MiB */

/* A version of a key: its time and value (len -1: deleted), and the older. */
struct ea_version {
    int64_t time;
    uint8_t *v;
    int32_t len;
    struct ea_version *older;
};

struct ea_run {
    uint64_t seed, r;
    struct mem m;
    struct db db;
    struct db_config cfg;
    struct bergdb_test_clock clock;
    char dir[512];
    int keys;
    struct ea_version **history;
    int64_t time, first;
    int64_t reads, restarts, larges, decreases, decreasesChecked, budgetSets, evictAlls,
            wrong;
    bool failed;
};

static void ea_fail(struct ea_run *run, int b, const char *what) {
    if (!run->failed) {
        printf("  evict_accounting, seed %llu, batch %d: %s\n", (unsigned long long) run->seed,
                b, what);
        test_checks_++;
        test_fail_(__FILE__, __LINE__, "a check of the run");
    }
    run->failed = true;
}

/* A random budget: from one byte to none. */
static int64_t ea_budget(struct ea_run *run) {
    static const int64_t budgets[] = {1, 2000, 20000, 200000, INT64_MAX};
    return budgets[test_random_below(&run->r, 5)];
}

/* Key k's ikey: "/k/K", or for the last tenth of the keys a long key of
 * about 300 bytes, whose segments make a subtree of their own (Eviction's
 * testHistoricalParentsAndLongKeys); returns its length. */
static int32_t ea_ikey(const struct ea_run *run, int k, char *ikey) {
    if (k < run->keys / 10 * 9) {
        return (int32_t) snprintf(ikey, 32, "/k/%d", k);
    }
    int32_t n = snprintf(ikey, 32, "/L/%d/", k);
    memset(ikey + n, 'a' + k % 26, 300);
    ikey[n + 300] = '\0';
    return n + 300;
}

/* getOne of key k at time t: the history's version at t (the newest at or
 * before it). */
static void ea_read(struct ea_run *run, int k, int64_t t) {
    char ikey[400];
    uint8_t bkey[400];
    int64_t segs[64];
    const int32_t kl = ea_ikey(run, k, ikey);
    keys_ikey_to_bkey((const uint8_t *) ikey, kl, bkey);
    keys_to_segments(bkey, kl, segs);
    struct getdata gd;
    struct vnode *v = NULL;
    struct err e;
    db_new_get_data(&run->db, &gd);
    enum err_code rc = db_get_one(&run->db, t, segs, keys_segment_count(kl), &gd, &v, &e);
    const struct ea_version *x = run->history[k];
    while (x != NULL && x->time > t) {
        x = x->older;
    }
    const int32_t expected = x == NULL ? -1 : x->len;
    const int32_t actual = v == NULL ? -1 : v->len;
    if (rc != ERR_OK || expected != actual
            || (actual > 0 && memcmp(v->value, x->v, (size_t) actual) != 0)) {
        run->wrong++;
    }
    run->reads++;
    db_evict(&run->db);         /* the end of the call */
}

static enum err_code ea_open(struct ea_run *run, int64_t budget) {
    struct db_start_info info;
    struct err e;
    run->cfg.cache_size_indicator = budget;
    return db_open(&run->db, run->dir, &run->cfg, &run->m, &info, &e);
}

/* One transaction of 1 to 5 puts (now and then a value over 1 MiB) and
 * deletes of random keys; large forces a large value of one key. */
static void ea_trans(struct ea_run *run, int b, int i, bool large) {
    struct tr_builder tb;
    struct trans t;
    struct err e;
    tr_builder_init(&tb, &run->m);
    tr_init(&t, &run->m);
    run->time += 100000;
    bergdb_test_clock_set(&run->clock, run->time);
    const int c = large ? 1 : 1 + test_random_below(&run->r, 5);
    int ks[5];
    uint8_t *vs[5];
    int32_t lens[5];
    int m = 0;
    for (int j = 0; j < c; j++) {
        int k = test_random_below(&run->r, run->keys);
        bool seen = false;
        for (int q = 0; q < m; q++) {
            seen = seen || ks[q] == k;
        }
        if (seen) {
            continue;
        }
        char ikey[400];
        uint8_t bkey[400];
        const int32_t kl = ea_ikey(run, k, ikey);
        keys_ikey_to_bkey((const uint8_t *) ikey, kl, bkey);
        uint8_t *v = NULL;
        int32_t len = -1;
        if (!large && test_random_below(&run->r, 20) == 0) {
            CHECK(tr_delete(&tb, bkey, kl, &e) == ERR_OK);
        } else {
            if (large || test_random_below(&run->r, 500) == 0) {
                len = EA_LARGE;
                run->larges++;
            } else {
                len = 12 + test_random_below(&run->r, 200);
            }
            v = malloc((size_t) len);
            for (int32_t q = 0; q < len; q++) {
                v[q] = (uint8_t) (q < 12 ? b * 31 + i * 7 + j : test_random(&run->r));
            }
            CHECK(tr_put(&tb, bkey, kl, v, len, NULL, &e) == ERR_OK);
        }
        ks[m] = k;
        vs[m] = v;
        lens[m++] = len;
    }
    CHECK(tr_build(&tb, &t, &e) == ERR_OK);
    enum err_code rc = db_execute(&run->db, &t, &e);
    if (rc != ERR_OK) {
        ea_fail(run, b, e.text);
    }
    for (int j = 0; j < m; j++) {
        struct ea_version *x = malloc(sizeof *x);
        *x = (struct ea_version) { t.tt, vs[j], lens[j], run->history[ks[j]] };
        run->history[ks[j]] = x;
    }
    tr_free(&t);
    tr_builder_free(&tb);
}

/* The checks after a batch: the recount (every object's holders), the pins
 * in the node table, no resident pointer to a value over 1 MiB (the
 * admission rule: 015-68, 019-47), the resident bytes at most the trigger
 * and, but for the pins, the budget, or the node table's bytes if more (the
 * margin over the floor of a budget under it, 022-06, U1-4); 40 keys'
 * answers right at the newest time; and now and then a decrease of the
 * budget with no write: if the pins fit it, the resident bytes are at most
 * it after the setter's call. */
static void ea_check(struct ea_run *run, int b) {
    struct err e;
    if (db_recount(&run->db) != 0) {
        ea_fail(run, b, "the recount");
    }
    struct ev_env env = env_of(&run->db);
    if (ev_check_pins(&env) != 0) {
        ea_fail(run, b, "a pinned object is not in the node table");
    }
    if (large_resident(&run->db) != 0) {
        ea_fail(run, b, "a resident pointer holds a value over 1 MiB");
    }
    const int64_t table = nt_bytes(&run->db.node_table);
    if (db_resident_bytes(&run->db) > run->db.ev.trigger
            || db_resident_bytes(&run->db) - db_pinned_bytes(&run->db)
                    > (run->db.ev.high > table ? run->db.ev.high : table)) {
        ea_fail(run, b, "the resident bytes over the trigger, or over the budget but for the pins");
    }
    for (int q = 0; q < 40; q++) {
        ea_read(run, test_random_below(&run->r, run->keys), INT64_MAX);
    }
    if (test_random_below(&run->r, 4) == 0) {
        const int64_t bytes = db_resident_bytes(&run->db);
        int64_t budget = bytes / 100 * (10 + test_random_below(&run->r, 86));
        budget = budget < run->db.ev.high - 1 ? budget : run->db.ev.high - 1;
        if (budget >= 1) {
            run->decreases++;
            run->budgetSets++;
            CHECK(db_set_cache_size_indicator(&run->db, budget, &e) == ERR_OK);
            if (db_pinned_bytes(&run->db) <= budget) {
                run->decreasesChecked++;
                if (db_resident_bytes(&run->db) > budget) {
                    ea_fail(run, b, "a decrease of the budget not reached, the pins fitting");
                }
            }
        }
    }
}

/* One run of the shape: keys, batches of up to maxTrans transactions, a
 * restart after one batch in restartOneIn. */
static void ea_run_seed(uint64_t seed, int keys, int batches, int maxTrans, int restartOneIn) {
    static struct ea_run run;
    memset(&run, 0, sizeof run);
    run.seed = seed;
    run.r = seed * UINT64_C(0x9E3779B97F4A7C15) + 7;
    run.keys = keys;
    run.history = calloc((size_t) keys, sizeof *run.history);
    mem_init(&run.m);
    REQUIRE(temp_dir(run.dir, sizeof run.dir));
    static const int32_t sds[] = {200, 2000, 20000, 200000};
    config(&run.cfg, &run.clock, 8, sds[test_random_below(&run.r, 4)], INT64_MAX);
    run.time = 1000000;
    bergdb_test_clock_set(&run.clock, run.time);
    REQUIRE(ea_open(&run, ea_budget(&run)) == ERR_OK);
    run.first = run.time;
    struct err e;
    for (int b = 0; b < batches && !run.failed; b++) {
        const int n = 1 + test_random_below(&run.r, maxTrans);
        for (int i = 0; i < n && !run.failed; i++) {
            ea_trans(&run, b, i, false);
            /* The readers: gets of random keys at random times of the history. */
            for (int q = test_random_below(&run.r, 5); q > 0; q--) {
                ea_read(&run, test_random_below(&run.r, keys), run.first
                        + (int64_t) ((uint64_t) test_random(&run.r)
                        % (uint64_t) (run.time - run.first + 1)));
            }
            const int x = test_random_below(&run.r, 40);
            if (x == 0) {
                evict_down_to(&run.db, 0);       /* Java's evictNow(EVERY) */
                run.evictAlls++;
            } else if (x == 1) {
                CHECK(db_set_cache_size_indicator(&run.db, ea_budget(&run), &e) == ERR_OK);
                run.budgetSets++;
            }
        }
        if (test_random_below(&run.r, restartOneIn) == 0) {
            if (test_random_below(&run.r, 2) == 0) {
                /* A large value just before the restart, so that the start's
                 * rerun makes it again (015-68). */
                ea_trans(&run, b, -1, true);
            }
            CHECK(db_close(&run.db, &e) == ERR_OK);
            REQUIRE(ea_open(&run, ea_budget(&run)) == ERR_OK);
            run.restarts++;
        }
        ea_check(&run, b);
    }
    CHECK_EQ(run.wrong, 0);
    printf("  evict_accounting seed %llu: %d batches, %lld reads, %lld wrong, %lld evictions of "
            "everything, %lld budget changes, %lld of %lld decreases checked, %lld restarts, "
            "%lld large values\n", (unsigned long long) seed, batches, (long long) run.reads,
            (long long) run.wrong, (long long) run.evictAlls, (long long) run.budgetSets,
            (long long) run.decreasesChecked, (long long) run.decreases,
            (long long) run.restarts, (long long) run.larges);
    db_close(&run.db, &e);
    CHECK_MEM_ZERO(&run.m);
    for (int k = 0; k < keys; k++) {
        while (run.history[k] != NULL) {
            struct ea_version *x = run.history[k];
            run.history[k] = x->older;
            free(x->v);
            free(x);
        }
    }
    free(run.history);
    remove_dir(run.dir);
}

/* EvictionAccountingTester.testAccounting (harness 6.5, 018-05; its faults
 * 015-67 to 015-71, 019-20, 019-21, 019-46, 019-47), in C's terms: one
 * caller, so its reader threads are reads between the transactions, at
 * random times of the history, each checked against the test's own record;
 * its test schedules' evictions are an eviction of every detachable object
 * (evict_down_to); a random budget from one byte to none, changed between
 * transactions; restarts in a directory with a new budget, half of them
 * right after a value over 1 MiB, so that the start's rerun makes it again;
 * after each batch the recount, the pins, the admission rule, the budget
 * and the answers, and now and then a decrease of the budget (ea_check). C's
 * resident bytes are the allocator's counts (012-12), so Java's comparison
 * of its estimates with a recount (Residents) is the recount of the holders
 * here; Java's handle limit of a batch (015-67) is not C's (section 11).
 * The keys are short, and a tenth of them long (300 bytes), whose deletes
 * leave subtrees cold (testHistoricalParentsAndLongKeys). Three seeds of
 * Java's unit shape (300 keys, 25 batches of up to 30 transactions);
 * BERGDB_ACCOUNTING_SEEDS=N runs N seeds by hand. */
#ifdef BERGDB_TEST
/* The test build's seam (plat.h): the forces are no-ops here, as what
 * reaches the disk is power.sh's part; in the release build they are real. */
static enum err_code ea_force(int fd, enum plat_force_why why, struct err *e) {
    (void) fd;
    (void) why;
    (void) e;
    return ERR_OK;
}

static enum err_code ea_force_dir(const char *dir, struct err *e) {
    (void) dir;
    (void) e;
    return ERR_OK;
}
#endif

TEST(evict_accounting) {
    int seeds = 3;
    const char *s = getenv("BERGDB_ACCOUNTING_SEEDS");
    if (s != NULL) {
        seeds = atoi(s);
    }
#ifdef BERGDB_TEST
    struct plat_io io = *plat_io_real();
    io.force = ea_force;
    io.force_dir = ea_force_dir;
    plat_io_set(&io);
#endif
    for (int i = 1; i <= seeds; i++) {
        ea_run_seed((uint64_t) i, 300, 25, 30, 25);
    }
#ifdef BERGDB_TEST
    plat_io_set(NULL);
#endif
}

/* EvictionAccountingTester.testAccountingManyRestarts (bergdb 019-47): many
 * small batches, so that restarts come one after another and a start's
 * section can begin with the transaction of a large value. Java's shape is
 * 300 keys and 300 batches of up to 4 transactions, a restart after one
 * batch in 25; here 100 batches and a restart after one in 5, about as many
 * restarts in a third of the time (seed 1070 of C's generator). */
TEST(evict_accounting_many_restarts) {
#ifdef BERGDB_TEST
    struct plat_io io = *plat_io_real();
    io.force = ea_force;
    io.force_dir = ea_force_dir;
    plat_io_set(&io);
#endif
    ea_run_seed(1070, 300, 100, 4, 5);
#ifdef BERGDB_TEST
    plat_io_set(NULL);
#endif
}

/* ======== A taken-back node leaves the node table (022-07) ======== */

/* The index objects of the node table that are at a vpos (never written)
 * and neither dirty nor in a record: none may be there. A node that its
 * transaction made is dirty until a take writes it; one that the
 * transaction made and took back (dag.c's take_back) is never written, and
 * leaves the table at the transaction's end (Cache3.dropNode). */
static int64_t unwritten_clean_objects(struct db *db) {
    int64_t n = 0;
    for (int64_t i = 0; i < nt_slots(&db->node_table); i++) {
        struct handle *h = nt_slot(&db->node_table, i);
        struct node *o = h == NULL ? NULL : h->obj;
        if (o != NULL && spos_is_vpos(o->spos) && !node_is_dirty(o)
                && !node_is_in_trans_nodes(o)) {
            n++;
        }
    }
    return n;
}

/* One transaction at tt: 40 puts "/p/Lnnn" of the letter put, and deletes
 * of the 40 keys of the letter del (0: none). */
static enum err_code swap_trans(struct db *db, struct mem *m, struct bergdb_test_clock *clock,
        int64_t tt, char put, char del, struct err *e) {
    struct tr_builder b;
    struct trans t;
    tr_builder_init(&b, m);
    tr_init(&t, m);
    bergdb_test_clock_set(clock, tt);
    enum err_code rc = ERR_OK;
    for (int i = 0; i < 80 && rc == ERR_OK; i++) {
        if (i >= 40 && del == 0) {
            break;
        }
        char ikey[16];
        uint8_t bkey[16];
        snprintf(ikey, sizeof ikey, "/p/%c%03d", i < 40 ? put : del, i % 40);
        const int32_t kl = (int32_t) strlen(ikey);
        keys_ikey_to_bkey((const uint8_t *) ikey, kl, bkey);
        rc = i < 40 ? tr_put(&b, bkey, kl, (const uint8_t *) "value", 5, NULL, e)
                : tr_delete(&b, bkey, kl, e);
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

/* Cache3.dropNode through the database (bergdb 023-07, section 5.1, fault
 * 3; Java's since release 2026.4): transactions that each put 40 keys
 * before the 40 live ones in key order and delete the live ones, so that
 * the puts split the nodes and the deletes empty what the splits made:
 * nodes are taken back. After each transaction, and after a restart, whose
 * rerun takes the same nodes back, no index object that was never written
 * is in the node table unless it is dirty; and the keys are the last ones
 * put. Without nt_drop_node the taken-back nodes stay in the table, at a
 * vpos, neither dirty nor ever written, until the close. */
TEST(evict_taken_back_nodes_leave_the_table) {
    struct mem m;
    struct err e;
    struct db db;
    struct db_config c;
    struct db_start_info info;
    struct bergdb_test_clock k = {0};
    char dir[256];
    REQUIRE(temp_dir(dir, sizeof dir));
    mem_init(&m);
    config(&c, &k, 8, 100, INT64_C(1) << 30);
    bergdb_test_clock_set(&k, 500);
    REQUIRE(db_open(&db, dir, &c, &m, &info, &e) == ERR_OK);
    int64_t tt = 1000, takenBack = 0;
    CHECK_EQ(swap_trans(&db, &m, &k, tt, 'm', 0, &e), ERR_OK);
    for (char letter = 'l'; letter >= 'a'; letter--) {
        tt += 10;
        CHECK_EQ(swap_trans(&db, &m, &k, tt, letter, (char) (letter + 1), &e), ERR_OK);
        CHECK_EQ(unwritten_clean_objects(&db), 0);
        CHECK_EQ(db_recount(&db), 0);
        if (letter == 'g' || letter == 'c') {
            takenBack += db.put_data.stat_taken_back;
            CHECK(db_close(&db, &e) == ERR_OK);
            CHECK_MEM_ZERO(&m);
            REQUIRE(db_open(&db, dir, &c, &m, &info, &e) == ERR_OK);
            CHECK_EQ(unwritten_clean_objects(&db), 0);
            CHECK_EQ(db_recount(&db), 0);
        }
    }
    takenBack += db.put_data.stat_taken_back;
    CHECK(takenBack > 0);       /* the transactions took nodes back */
    for (int i = 0; i < 40; i++) {
        char ikey[16];
        uint8_t bkey[16];
        int64_t segs[4];
        struct getdata gd;
        struct vnode *v;
        for (char letter = 'a'; letter <= 'b'; letter++) {
            snprintf(ikey, sizeof ikey, "/p/%c%03d", letter, i);
            const int32_t kl = (int32_t) strlen(ikey);
            keys_ikey_to_bkey((const uint8_t *) ikey, kl, bkey);
            keys_to_segments(bkey, kl, segs);
            db_new_get_data(&db, &gd);
            v = NULL;
            CHECK(db_get_one(&db, INT64_MAX, segs, keys_segment_count(kl), &gd, &v, &e)
                    == ERR_OK);
            CHECK_EQ(v != NULL, letter == 'a');
        }
    }
    printf("  evict_taken_back_nodes_leave_the_table: %lld nodes taken back\n",
            (long long) takenBack);
    CHECK(db_close(&db, &e) == ERR_OK);
    CHECK_MEM_ZERO(&m);
    remove_dir(dir);
}

const struct test evict_tests[] = {
    TEST_ENTRY(evict_low_of_exact),
    TEST_ENTRY(evict_table),
    TEST_ENTRY(evict_floor_after_shrink),
    TEST_ENTRY(evict_detachable),
    TEST_ENTRY(evict_twins),
    TEST_ENTRY(evict_dead_hand),
    TEST_ENTRY(evict_taken_back_nodes_leave_the_table),
    TEST_ENTRY(evict_large_value),
    TEST_ENTRY(evict_start_admits_large_values),
    TEST_ENTRY(evict_start_admits_first_transactions_large_values),
    TEST_ENTRY(evict_warmup_keeps_no_large_value),
    TEST_ENTRY(evict_lowered_budget_after_pins_fell),
    TEST_ENTRY(evict_alloc_failures),
    TEST_ENTRY(evict_accounting),
    TEST_ENTRY(evict_accounting_many_restarts),
    TEST_ENTRY(evict_after_refused_transaction),
    TEST_ENTRY(evict_after_refused_read),
    TEST_ENTRY(evict_scan_is_linear),
    TEST_END
};
