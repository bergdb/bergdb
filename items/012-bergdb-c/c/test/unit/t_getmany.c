/* The tests of GetMany and of the database of Level 0 (bergdb 012-08):
 * Java's DbTesterGetMany.testInclusiveStartKeyWithDeepTree and
 * testStartKeyRandom (with java.util.Random's draws), on mdb as Java's on
 * Db; a random test of the database against a model map (key to its
 * versions) with getOne and getMany at random times, both ways, from start
 * keys inclusive or not, with each stop condition; and the allocation
 * failures in turn. The counts are recounted, and nothing is left. */
#include <stdlib.h>
#include <string.h>
#include "getmany.h"
#include "keys.h"
#include "klong.h"
#include "mdb.h"
#include "mem.h"
#include "test.h"

/* ======== Helpers ======== */

struct key {
    int64_t s[24];
    int32_t n;
};

static struct key key_of(const char *ikey) {
    struct key k;
    uint8_t b[160];
    int32_t len = (int32_t) strlen(ikey);
    if (len > 150 || !keys_ikey_to_bkey((const uint8_t *) ikey, len, b)) {
        CHECK(false);   /* a bad key */
        k.n = 1;
        k.s[0] = 0;
        return k;
    }
    k.n = keys_segment_count(len);
    keys_to_segments(b, len, k.s);
    return k;
}

/* Java's java.util.Random */
struct jrandom {
    int64_t seed;
};

static void jr_init(struct jrandom *r, int64_t seed) {
    r->seed = (seed ^ INT64_C(0x5DEECE66D)) & ((INT64_C(1) << 48) - 1);
}

static int32_t jr_next(struct jrandom *r, int bits) {
    r->seed = (r->seed * INT64_C(0x5DEECE66D) + INT64_C(0xB)) & ((INT64_C(1) << 48) - 1);
    return (int32_t) ((uint64_t) r->seed >> (48 - bits));
}

static int32_t jr_next_int(struct jrandom *r, int32_t bound) {
    int32_t rr = jr_next(r, 31);
    int32_t m = bound - 1;
    if ((bound & m) == 0) {
        rr = (int32_t) ((bound * (int64_t) rr) >> 31);
    } else {
        for (int32_t u = rr; u - (rr = u % bound) + m < 0; u = jr_next(r, 31)) {
        }
    }
    return rr;
}

static bool jr_next_boolean(struct jrandom *r) {
    return jr_next(r, 1) != 0;
}

/* A sink that keeps the keys of the pairs (and checks their values). */
struct got {
    struct key k[64];
    int32_t vlen[64];
    uint8_t vfirst[64];
    int64_t time[64];
    int32_t n;
};

static bool got_add(void *ctx, const struct kvt *kvt) {
    struct got *g = ctx;
    if (g->n < 64) {
        memcpy(g->k[g->n].s, kvt->key, (size_t) kvt->key_n * sizeof(int64_t));
        g->k[g->n].n = kvt->key_n;
        g->vlen[g->n] = kvt->value->len;
        g->vfirst[g->n] = kvt->value->len > 0 ? kvt->value->value[0] : 0;
        g->time[g->n] = kvt->time;
    }
    g->n++;
    return true;
}

/* A getMany on db into *got: start NULL for none. */
static void many(struct mdb *db, int64_t time, const struct key *start, bool inclusive,
        bool forward, const struct gm_stop *stop, struct got *got) {
    struct getmany g;
    mdb_new_get_many(db, &g);
    g.lookup_time = time;
    if (start != NULL) {
        g.start_key = start->s;
        g.start_key_n = start->n;
    }
    g.inclusive = inclusive;
    g.forward = forward;
    if (stop != NULL) {
        g.stop_condition = *stop;
    }
    got->n = 0;
    g.result.add = got_add;
    g.result.ctx = got;
    CHECK(mdb_get_many(db, &g));
}

static void put(struct mdb *db, int64_t tt, const char *ikey, const uint8_t *v, int32_t len) {
    struct key k = key_of(ikey);
    mdb_begin(db, tt);
    CHECK(mdb_put(db, k.s, k.n, v, len));
    mdb_end(db);
}

static void end(struct mdb *db, struct mem *m) {
    CHECK_EQ(mdb_recount(db), 0);
    mdb_free(db);
    CHECK_MEM_ZERO(m);
}

static int cmp_keys(const void *a, const void *b) {
    const struct key *x = a, *y = b;
    return keys_compare_keys(x->s, x->n, y->s, y->n);
}

/* ======== DbTesterGetMany ======== */

/* DbTesterGetMany.testInclusiveStartKeyWithDeepTree */
TEST(gm_inclusive_start_key_with_deep_tree) {
    const int32_t maxNodes[] = { 30, 8, 14 };
    for (int mi = 0; mi < 3; mi++) {
        for (int longKeys = 0; longKeys < 2; longKeys++) {
            for (int fwd = 1; fwd >= 0; fwd--) {
                struct mem m;
                mem_init(&m);
                struct mdb db;
                REQUIRE(mdb_create(&db, &m, 1, maxNodes[mi]));
                int n = 120;
                uint8_t zeros[10] = { 0 };
                char key[40];
                for (int i = 0; i < n; i++) {
                    snprintf(key, sizeof key, longKeys ? "/long/key/%d" : "/k/%d", i);
                    put(&db, 1000 + i * 10, key, zeros, 10);
                }
                for (int i = 0; i < n; i++) {
                    snprintf(key, sizeof key, longKeys ? "/long/key/%d" : "/k/%d", i);
                    struct key start = key_of(key);
                    struct got got;
                    many(&db, INT64_MAX, &start, true, fwd == 1, NULL, &got);
                    CHECK(got.n > 0);
                    CHECK_EQ(keys_compare_keys(start.s, start.n, got.k[0].s, got.k[0].n), 0);
                    many(&db, INT64_MAX, &start, false, fwd == 1, NULL, &got);
                    if (got.n > 0) {
                        CHECK(keys_compare_keys(start.s, start.n, got.k[0].s, got.k[0].n) != 0);
                    }
                }
                end(&db, &m);
            }
        }
    }
}

/* DbTesterGetMany.randomKey */
static void random_key(struct jrandom *r, char *out, size_t cap) {
    static const char *const parts[] = { "a", "b", "ab", "abc", "k", "/k/", "/long/", "xyz",
        "q" };
    size_t o = 0;
    out[0] = '\0';
    int32_t count = 1 + jr_next_int(r, jr_next_int(r, 4) == 0 ? 6 : 2);
    for (int32_t i = 0; i < count; i++) {
        o += (size_t) snprintf(out + o, cap - o, "%s", parts[jr_next_int(r, 9)]);
        if (jr_next_boolean(r)) {
            o += (size_t) snprintf(out + o, cap - o, "%d", (int) jr_next_int(r, 100));
        }
    }
}

static int32_t at_most_5(void *ctx, const struct kvt *kvt) {
    (void) kvt;
    int32_t *count = ctx;
    return ++*count >= 5 ? GM_ADD_AND_STOP : GM_ADD;
}

/* DbTesterGetMany.testStartKeyRandom */
TEST(gm_start_key_random) {
    for (int seed = 0; seed < 12; seed++) {
        struct jrandom r;
        jr_init(&r, seed);
        const int32_t nodeSizes[] = { 30, 8, 14 };
        struct mem m;
        mem_init(&m);
        struct mdb db;
        REQUIRE(mdb_create(&db, &m, 1, nodeSizes[seed % 3]));

        struct key *keys = malloc(400 * sizeof *keys);
        int32_t nk = 0;
        int32_t n = 20 + jr_next_int(&r, 300);
        int64_t time = 1000;
        uint8_t five[5] = { 0 };
        for (int32_t i = 0; i < n; i++) {
            char key[200];
            random_key(&r, key, sizeof key);
            struct key segs = key_of(key);
            bool dup = false;
            for (int32_t j = 0; j < nk; j++) {
                dup = dup || keys_compare_keys(keys[j].s, keys[j].n, segs.s, segs.n) == 0;
            }
            if (dup) {
                continue;
            }
            keys[nk++] = segs;
            time += 10;
            put(&db, time, key, five, 5);
        }
        qsort(keys, (size_t) nk, sizeof *keys, cmp_keys);     /* a stable sort is not needed: distinct */

        for (int j = 0; j < 80; j++) {
            struct key start;
            if (jr_next_boolean(&r)) {
                start = keys[jr_next_int(&r, nk)];
            } else {
                char key[200];
                random_key(&r, key, sizeof key);
                start = key_of(key);
            }
            for (int mode = 0; mode < 4; mode++) {
                bool forward = mode < 2;
                bool inclusive = mode % 2 == 0;
                int32_t count = 0;
                struct gm_stop stop = { at_most_5, NULL, &count };
                struct got got;
                many(&db, INT64_MAX, &start, inclusive, forward, &stop, &got);

                int32_t ne = 0;
                const struct key *expected[5];
                for (int32_t i = 0; i < nk; i++) {
                    const struct key *k = &keys[forward ? i : nk - 1 - i];
                    int32_t c = keys_compare_keys(k->s, k->n, start.s, start.n);
                    bool ok = forward ? (inclusive ? c >= 0 : c > 0) : (inclusive ? c <= 0 : c < 0);
                    if (ok && ne < 5) {
                        expected[ne++] = k;
                    }
                }
                CHECK_EQ(got.n, ne);
                for (int32_t i = 0; i < ne && i < got.n; i++) {
                    CHECK_EQ(keys_compare_keys(expected[i]->s, expected[i]->n, got.k[i].s,
                            got.k[i].n), 0);
                }
            }
        }
        free(keys);
        end(&db, &m);
    }
}

/* ======== The database against a model ======== */

#define MKEYS 48
#define MTRANS 120

struct model {
    struct key keys[MKEYS];     /* sorted */
    /* value[t][k]: the version of key k after transaction t: -1 none, else
     * the value's first byte (its length is 1 + t % 7) */
    int32_t value[MTRANS + 1][MKEYS];
    int64_t time[MTRANS + 1];   /* transaction t's time; time[0] the creation's */
    int32_t ntrans;
};

/* The model's transaction at lookup time t (the last one at or before it). */
static int32_t model_trans_at(const struct model *mo, int64_t t) {
    int32_t i = 0;
    while (i + 1 <= mo->ntrans && mo->time[i + 1] <= t) {
        i++;
    }
    return i;
}

static void model_keys(struct model *mo, uint64_t *rs) {
    for (int32_t i = 0; i < MKEYS; i++) {
        char key[120];
        int kind = test_random_below(rs, 4);
        if (kind == 0) {
            snprintf(key, sizeof key, "/k/%d", (int) test_random_below(rs, 1000));
        } else if (kind == 1) {
            snprintf(key, sizeof key, "/a/longer/key/%d", (int) test_random_below(rs, 100));
        } else if (kind == 2) {
            snprintf(key, sizeof key, "/k/%d/x%d", (int) test_random_below(rs, 30),
                    (int) test_random_below(rs, 20000000));
        } else {
            snprintf(key, sizeof key, "/123456/%d", (int) test_random_below(rs, 50));
        }
        struct key k = key_of(key);
        bool dup = false;
        for (int32_t j = 0; j < i; j++) {
            dup = dup || keys_compare_keys(mo->keys[j].s, mo->keys[j].n, k.s, k.n) == 0;
        }
        if (dup) {
            i--;
            continue;
        }
        mo->keys[i] = k;
    }
    qsort(mo->keys, MKEYS, sizeof mo->keys[0], cmp_keys);
}

/* Every read at time t against the model. */
static void model_check_at(struct mdb *db, const struct model *mo, int64_t t, uint64_t *rs) {
    int32_t tr = model_trans_at(mo, t);
    const int32_t *st = mo->value[tr];
    struct getdata gd;
    mdb_new_get_data(db, &gd);
    for (int32_t k = 0; k < MKEYS; k++) {
        struct vnode *v;
        CHECK(mdb_get_one(db, t, mo->keys[k].s, mo->keys[k].n, &gd, &v));
        if (st[k] < 0) {
            CHECK(v == NULL);
        } else {
            REQUIRE(v != NULL);
            CHECK_EQ(v->value[0], st[k]);
        }
    }
    /* getMany: from a random start, both ways, inclusive or not, with a
     * random stop condition. */
    for (int j = 0; j < 6; j++) {
        int32_t sk = test_random_below(rs, MKEYS + 1);
        const struct key *start = sk == MKEYS ? NULL : &mo->keys[sk];
        bool forward = test_random_below(rs, 2) == 0;
        bool inclusive = test_random_below(rs, 2) == 0;
        int32_t kind = test_random_below(rs, 5);
        struct gm_get_n gn;
        struct gm_endpoint ep;
        struct gm_prefix px;
        struct gm_prefix_n pn;
        struct gm_stop stop = gm_dont_stop();
        int32_t ek = test_random_below(rs, MKEYS);
        int32_t maxCount = 1 + test_random_below(rs, 8);
        bool endIncl = test_random_below(rs, 2) == 0;
        struct key prefix;
        if (kind == 1) {
            stop = gm_get_n(&gn, maxCount);
        } else if (kind == 2) {
            stop = gm_endpoint(&ep, mo->keys[ek].s, mo->keys[ek].n, endIncl, !forward);
        } else if (kind == 3 || kind == 4) {
            prefix = key_of(test_random_below(rs, 2) == 0 ? "/k/" : "/k/1");
            stop = kind == 3 ? gm_prefix(&px, prefix.s, prefix.n)
                    : gm_prefix_n(&pn, prefix.s, prefix.n, maxCount);
        }
        struct got got;
        many(db, t, start, inclusive, forward, &stop, &got);

        /* The model's answer: the live keys from the start, the stop applied. */
        int32_t ne = 0, count = 0;
        int32_t expected[MKEYS];
        for (int32_t i = 0; i < MKEYS; i++) {
            int32_t k = forward ? i : MKEYS - 1 - i;
            if (st[k] < 0) {
                continue;
            }
            if (start != NULL) {
                int32_t c = keys_compare_keys(mo->keys[k].s, mo->keys[k].n, start->s, start->n);
                if (!(forward ? (inclusive ? c >= 0 : c > 0) : (inclusive ? c <= 0 : c < 0))) {
                    continue;
                }
            }
            count++;
            if (kind == 1) {
                expected[ne++] = k;
                if (count == maxCount) {
                    break;
                }
            } else if (kind == 2) {
                int32_t c = keys_compare_keys(mo->keys[k].s, mo->keys[k].n, mo->keys[ek].s,
                        mo->keys[ek].n);
                bool stopHere = !forward ? (endIncl ? c < 0 : c <= 0) : (endIncl ? c > 0 : c >= 0);
                if (stopHere) {
                    break;
                }
                expected[ne++] = k;
            } else if (kind == 3 || kind == 4) {
                if (!keys_is_prefix(prefix.s, prefix.n, mo->keys[k].s, mo->keys[k].n)) {
                    break;
                }
                expected[ne++] = k;
                if (kind == 4 && count == maxCount) {
                    break;
                }
            } else {
                expected[ne++] = k;
            }
        }
        CHECK_EQ(got.n, ne);
        for (int32_t i = 0; i < ne && i < got.n; i++) {
            const struct key *e = &mo->keys[expected[i]];
            CHECK_EQ(keys_compare_keys(e->s, e->n, got.k[i].s, got.k[i].n), 0);
            CHECK_EQ(got.vfirst[i], st[expected[i]]);
            CHECK(got.time[i] <= t);
        }
    }
}

static void model_run(uint64_t seed, int32_t maxNode) {
    uint64_t rs = seed;
    struct model *mo = calloc(1, sizeof *mo);
    model_keys(mo, &rs);
    for (int32_t k = 0; k < MKEYS; k++) {
        mo->value[0][k] = -1;
    }
    struct mem m;
    mem_init(&m);
    struct mdb db;
    mo->time[0] = 1 + test_random_below(&rs, 100);
    REQUIRE(mdb_create(&db, &m, mo->time[0], maxNode));
    int32_t ntrans = 20 + test_random_below(&rs, MTRANS - 20);
    for (int32_t t = 1; t <= ntrans; t++) {
        mo->time[t] = mo->time[t - 1] + 1 + test_random_below(&rs, 20);
        memcpy(mo->value[t], mo->value[t - 1], sizeof mo->value[t]);
        mdb_begin(&db, mo->time[t]);
        /* the pairs in key order, each key once (Trans.Builder.build) */
        int32_t ops = 1 + test_random_below(&rs, test_random_below(&rs, 4) == 0 ? 30 : 6);
        bool used[MKEYS] = { false };
        for (int32_t o = 0; o < ops; o++) {
            used[test_random_below(&rs, MKEYS)] = true;
        }
        for (int32_t k = 0; k < MKEYS; k++) {
            if (!used[k]) {
                continue;
            }
            bool del = test_random_below(&rs, 4) == 0;
            uint8_t v[8];
            int32_t len = 1 + t % 7;
            memset(v, (int) (t & 0x7f), sizeof v);
            CHECK(mdb_put(&db, mo->keys[k].s, mo->keys[k].n, del ? NULL : v, len));
            mo->value[t][k] = del ? -1 : (int32_t) (t & 0x7f);
        }
        mdb_end(&db);
        mo->ntrans = t;
        CHECK_EQ(mdb_recount(&db), 0);
        if (test_random_below(&rs, 8) == 0) {
            model_check_at(&db, mo, INT64_MAX, &rs);
        }
    }
    /* Reads at random times: before the first, at and between transactions. */
    for (int j = 0; j < 40; j++) {
        int64_t t = mo->time[0] + test_random_below(&rs,
                (int32_t) (mo->time[ntrans] - mo->time[0] + 30));
        model_check_at(&db, mo, t - 1, &rs);
    }
    model_check_at(&db, mo, INT64_MAX, &rs);
    end(&db, &m);
    free(mo);
}

TEST(mdb_model) {
    const int32_t sizes[] = { 8, 14, 30, 62 };
    for (uint64_t seed = 1; seed <= 120; seed++) {
        model_run(seed * 7919, sizes[seed % 4]);
    }
}

/* ======== Allocation failures in turn ======== */

/* A small workload: the creation, puts with splits of every kind (node
 * size 8), deletes, reads. false where an allocation failed. */
static bool workload(struct mdb *db, struct mem *m) {
    if (!mdb_create(db, m, 5, 8)) {
        return false;
    }
    bool ok = true;
    for (int32_t t = 1; t <= 12 && ok; t++) {
        mdb_begin(db, 10 * t);
        for (int32_t i = 0; i < 6 && ok; i++) {
            char key[40];
            snprintf(key, sizeof key, i % 2 == 0 ? "/k/%d" : "/a/longer/key/%d", (int) ((t * 7 + i * 3) % 40));
            struct key k = key_of(key);
            uint8_t v[3] = { 1, 2, 3 };
            ok = mdb_put(db, k.s, k.n, (t + i) % 5 == 0 ? NULL : v, 3);
        }
        mdb_end(db);
    }
    if (ok) {
        struct getmany g;
        mdb_new_get_many(db, &g);
        g.lookup_time = 70;
        ok = mdb_get_many(db, &g);
    }
    if (ok) {
        struct getmany g;
        mdb_new_get_many(db, &g);
        gm_set_backward(&g);
        ok = mdb_get_many(db, &g);
    }
    return ok;
}

TEST(mdb_allocation_failures) {
    int64_t runs = 0;
    for (int64_t failAt = 1; ; failAt++) {
        struct mem m;
        mem_init(&m);
        m.fail_at = failAt;
        struct mdb db;
        memset(&db, 0, sizeof db);
        bool ok = workload(&db, &m);
        bool made = db.mem != NULL && tds_get_super_root(&db.dag.top_ds) != NULL;
        if (made) {
            mdb_free(&db);
        }
        CHECK_MEM_ZERO(&m);
        runs++;
        if (ok) {
            CHECK(m.allocs < failAt);   /* no allocation failed: the end */
            break;
        }
        if (failAt > 100000) {
            CHECK(false);
            break;
        }
    }
    CHECK(runs > 50);
}

/* ======== Dag.dirtyNodeBound (005-31) ======== */

/* The key nodes that a transaction makes dirty or creates, as Db marks them
 * (Db.markAtEndOfOp, endOfOp): in each operation that changes something,
 * every key node that a pointer led to, made or changed. */
struct marks {
    struct mdb *db;
    struct op_pointer_listener inner;
    const void *op[4096];       /* the operation's */
    int32_t nop;
    bool changed;
    const void *trans[8192];    /* the transaction's, distinct */
    int32_t ntrans;
    const void *replaced[1024]; /* keyNodeReplaced: clean again at endOfTrans */
    int32_t nreplaced;
};

static void mark(struct marks *mk, const void *n) {
    if (mk->nop < 4096) {
        mk->op[mk->nop++] = n;
    }
}

static bool mk_followed(void *ctx, struct node *pre, int32_t index, struct node *result,
        int32_t type) {
    struct marks *mk = ctx;
    if (result != NULL && result->o.kind == OBJ_KEY) {
        mark(mk, result);
    }
    return mk->inner.pointer_followed(mk->inner.ctx, pre, index, result, type);
}

static bool mk_created(void *ctx, struct knode *n) {
    struct marks *mk = ctx;
    mark(mk, n);
    mk->changed = true;
    return true;
}

static bool mk_replaced(void *ctx, struct knode *n) {
    struct marks *mk = ctx;
    if (mk->nreplaced < 1024) {
        mk->replaced[mk->nreplaced++] = n;
    }
    return true;
}

/* endOfTrans: the replaced nodes leave the list (no touch here). */
static void end_of_trans(struct marks *mk) {
    int32_t w = 0;
    for (int32_t i = 0; i < mk->ntrans; i++) {
        bool replaced = false;
        for (int32_t j = 0; j < mk->nreplaced && !replaced; j++) {
            replaced = mk->replaced[j] == mk->trans[i];
        }
        if (!replaced) {
            mk->trans[w++] = mk->trans[i];
        }
    }
    mk->ntrans = w;
}

static bool mk_value(void *ctx, struct vnode *n, const int64_t *key, int32_t key_n) {
    (void) n, (void) key, (void) key_n;
    ((struct marks *) ctx)->changed = true;
    return true;
}

/* endOfOp: the operation's nodes into the transaction's, if it changed. */
static void end_of_op(struct marks *mk) {
    if (mk->changed) {
        for (int32_t i = 0; i < mk->nop; i++) {
            bool seen = false;
            for (int32_t j = 0; j < mk->ntrans && !seen; j++) {
                seen = mk->trans[j] == mk->op[i];
            }
            if (!seen && mk->ntrans < 8192) {
                mk->trans[mk->ntrans++] = mk->op[i];
            }
        }
    }
    mk->nop = 0;
    mk->changed = false;
}

/* The bound of each random transaction, computed before it at the last
 * transaction's time, is at least the key nodes it makes dirty or creates. */
TEST(dag_dirty_node_bound) {
    int64_t tested = 0, tight = 0;
    for (uint64_t seed = 1; seed <= 40; seed++) {
        uint64_t rs = seed * 104729;
        const int32_t sizes[] = { 8, 14, 30 };
        struct mem m;
        mem_init(&m);
        struct mdb db;
        REQUIRE(mdb_create(&db, &m, 1, sizes[seed % 3]));
        struct marks *mk = calloc(1, sizeof *mk);
        mk->db = &db;
        mk->inner = db.pd.op.pointer_listener;
        db.pd.op.pointer_listener.pointer_followed = mk_followed;
        db.pd.op.pointer_listener.ctx = mk;
        db.pd.node_change_listener.key_node_created = mk_created;
        db.pd.node_change_listener.key_node_changed = mk_created;
        db.pd.node_change_listener.value_node_created = mk_value;
        db.pd.node_change_listener.key_node_replaced = mk_replaced;
        db.pd.node_change_listener.ctx = mk;

        int64_t time = 10;
        for (int32_t t = 0; t < 60; t++) {
            /* the transaction: distinct keys in key order */
            struct key keys[40];
            bool deletes[40];
            int32_t nk = 1 + test_random_below(&rs, test_random_below(&rs, 5) == 0 ? 40 : 6);
            for (int32_t i = 0; i < nk; i++) {
                char key[80];
                int kind = test_random_below(&rs, 3);
                if (kind == 0) {
                    snprintf(key, sizeof key, "/k/%d", (int) test_random_below(&rs, 400));
                } else if (kind == 1) {
                    snprintf(key, sizeof key, "/a/longer/key/%d/%d",
                            (int) test_random_below(&rs, 20), (int) test_random_below(&rs, 50));
                } else {
                    snprintf(key, sizeof key, "/x%d/1234567/abcdefg/%d",
                            (int) test_random_below(&rs, 5), (int) test_random_below(&rs, 30));
                }
                keys[i] = key_of(key);
                deletes[i] = test_random_below(&rs, 5) == 0;
                for (int32_t j = 0; j < i; j++) {
                    if (keys_compare_keys(keys[j].s, keys[j].n, keys[i].s, keys[i].n) == 0) {
                        i--;
                        break;
                    }
                }
            }
            qsort(keys, (size_t) nk, sizeof keys[0], cmp_keys);
            const int64_t *kp[40];
            int32_t kn[40];
            for (int32_t i = 0; i < nk; i++) {
                kp[i] = keys[i].s;
                kn[i] = keys[i].n;
            }
            struct getdata gd;
            mdb_new_get_data(&db, &gd);
            int64_t bound;
            CHECK(dag_dirty_node_bound(&db.dag, mdb_lookup_time(&db, INT64_MAX), kp, kn,
                    deletes, nk, &gd, &m, &bound));

            time += 10;
            mdb_begin(&db, time);
            mk->ntrans = 0;
            mk->nreplaced = 0;
            for (int32_t i = 0; i < nk; i++) {
                uint8_t v[4] = { 1, 2, 3, 4 };
                CHECK(mdb_put(&db, keys[i].s, keys[i].n, deletes[i] ? NULL : v, 4));
                end_of_op(mk);
            }
            end_of_trans(mk);
            mdb_end(&db);
            CHECK(bound >= mk->ntrans);
            tested++;
            tight += bound == mk->ntrans;
        }
        free(mk);
        end(&db, &m);
    }
    CHECK(tested == 40 * 60);
    CHECK(tight > 0);
}

const struct test getmany_tests[] = {
    TEST_ENTRY(gm_inclusive_start_key_with_deep_tree),
    TEST_ENTRY(gm_start_key_random),
    TEST_ENTRY(mdb_model),
    TEST_ENTRY(mdb_allocation_failures),
    TEST_ENTRY(dag_dirty_node_bound),
    TEST_END
};
