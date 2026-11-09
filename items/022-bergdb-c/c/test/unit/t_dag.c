/* The tests of the Dag (bergdb 012-08): Java's DagTester, test by test, on
 * a Dag of memory pointers only (DagTester's DUMMY_POINTER_FOLLOWER); the
 * counts recounted and nothing left at each test's end. */
#include <stdlib.h>
#include <string.h>
#include "dag.h"
#include "getmany.h"
#include "handle.h"
#include "keys.h"
#include "klong.h"
#include "knode.h"
#include "nfix.h"
#include "spos.h"
#include "test.h"
#include "tnode.h"
#include "topds.h"
#include "vnode.h"

#define MAX_NODE_SIZE 30

/* DagTester.DUMMY_POINTER_FOLLOWER: memory pointers only. */
static struct node *dummy_follow(void *ctx, struct node *predecessor, int32_t pointerIndex,
        struct opdata *op) {
    (void) ctx;
    struct node *result = node_pointer_node(predecessor, pointerIndex);
    if (result == NULL) {
        CHECK(false);   /* "This NodeFollower does not support stream pointers." */
        return NULL;
    }
    if (!op->pointer_listener.pointer_followed(op->pointer_listener.ctx, predecessor,
            pointerIndex, result, PTR_TYPE_MEMORY)) {
        return NULL;
    }
    return result;
}

struct tdag {
    struct nfix f;
    struct dag dag;
    struct putdata pd;
    struct getdata gd;
};

/* Dag.createEmpty(time, maxNodeSize, DUMMY_POINTER_FOLLOWER, pcl), and pd(dag), gd(dag). */
static void tdag_init(struct tdag *t, int64_t time, int32_t maxNodeSize,
        const struct op_pointer_created_listener *pcl) {
    nfix_init(&t->f);
    bool ok = dag_create_empty(&t->dag, &t->f.cx, time, maxNodeSize,
            pcl == NULL ? &OP_DO_NOTHING_POINTER_CREATED_LISTENER : pcl);
    CHECK(ok);
    dag_new_put_data(&t->dag, &t->pd, &t->f.m);
    t->pd.op.pointer_follower.follow = dummy_follow;
    dag_new_get_data(&t->dag, &t->gd);
    t->gd.op.pointer_follower.follow = dummy_follow;
}

/* The test's end: the recount from the super root, everything freed. */
static void tdag_end(struct tdag *t) {
    struct obj *roots[1] = { &tds_get_super_root(&t->dag.top_ds)->n.o };
    NFIX_RECOUNT(&t->f, roots, 1);
    dag_free(&t->dag);
    pd_free(&t->pd);
    NFIX_END(&t->f);
}

/* Keys.toSegments(String): the ikey's bkey, as segments. */
struct key {
    int64_t s[16];
    int32_t n;
};

static struct key key_of(const char *ikey) {
    struct key k;
    uint8_t b[112];
    int32_t len = (int32_t) strlen(ikey);
    if (len > 100 || !keys_ikey_to_bkey((const uint8_t *) ikey, len, b)) {
        CHECK(false);   /* a bad key */
        k.n = 1;
        k.s[0] = 0;
        return k;
    }
    k.n = keys_segment_count(len);
    keys_to_segments(b, len, k.s);
    return k;
}

static bool put(struct tdag *t, const char *ikey, const char *value) {
    struct key k = key_of(ikey);
    return dag_put_kv(&t->dag, k.s, k.n, (const uint8_t *) value,
            value == NULL ? -1 : (int32_t) strlen(value), &t->pd);
}

/* dag.getOne as a string: NULL for none. */
static const char *get(struct tdag *t, int64_t time, const char *ikey, char *buf, size_t cap) {
    struct key k = key_of(ikey);
    struct vnode *v;
    bool ok = dag_get_one(&t->dag, time, k.s, k.n, &t->gd, &v);
    CHECK(ok);
    if (!ok || v == NULL) {
        return NULL;
    }
    size_t n = (size_t) v->len < cap - 1 ? (size_t) v->len : cap - 1;
    memcpy(buf, v->value, n);
    buf[n] = '\0';
    return buf;
}

static bool str_eq(const char *a, const char *b) {
    return a == b || (a != NULL && b != NULL && strcmp(a, b) == 0);
}

/* ======== Java's java.util.Random, for DagTester's seeds ======== */

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

/* Random.nextInt(bound) */
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

/* ======== A set of objects, by identity (Java's IdentityHashMap, small) ======== */

struct oset {
    const void **p;
    const void **v;             /* a map's values, or NULL */
    int64_t *t;                 /* a map's times */
    int32_t n, cap;
};

static int32_t oset_find(const struct oset *s, const void *x) {
    for (int32_t i = 0; i < s->n; i++) {
        if (s->p[i] == x) {
            return i;
        }
    }
    return -1;
}

/* Adds x (with value v and time t for a map); returns false if it was there
 * (and then sets its value). */
static bool oset_put(struct oset *s, const void *x, const void *v, int64_t t) {
    int32_t i = oset_find(s, x);
    if (i >= 0) {
        s->v[i] = v;
        s->t[i] = t;
        return false;
    }
    if (s->n == s->cap) {
        s->cap = s->cap == 0 ? 64 : 2 * s->cap;
        s->p = realloc(s->p, (size_t) s->cap * sizeof *s->p);
        s->v = realloc(s->v, (size_t) s->cap * sizeof *s->v);
        s->t = realloc(s->t, (size_t) s->cap * sizeof *s->t);
    }
    s->p[s->n] = x;
    s->v[s->n] = v;
    s->t[s->n] = t;
    s->n++;
    return true;
}

static void oset_remove(struct oset *s, const void *x) {
    int32_t i = oset_find(s, x);
    if (i >= 0) {
        s->n--;
        s->p[i] = s->p[s->n];
        s->v[i] = s->v[s->n];
        s->t[i] = s->t[s->n];
    }
}

static void oset_free(struct oset *s) {
    free(s->p);
    free(s->v);
    free(s->t);
    memset(s, 0, sizeof *s);
}

/* ======== The tests ======== */

TEST(dag_test0) {
    struct tdag t;
    tdag_init(&t, 0, MAX_NODE_SIZE, NULL);
    char buf[64];
    CHECK(get(&t, 0, "/-k1", buf, sizeof buf) == NULL);
    tdag_end(&t);
}

struct choices {
    int32_t c[16];
    int32_t n;
};

static bool record_choice(void *ctx, struct node *predecessor, int32_t pointerIndex,
        struct node *result, int32_t pointerType) {
    (void) predecessor, (void) result, (void) pointerType;
    struct choices *c = ctx;
    if (c->n < 16) {
        c->c[c->n] = pointerIndex;
    }
    c->n++;
    return true;
}

/* DagTester.test1: with choices */
TEST(dag_test1) {
    struct tdag t;
    tdag_init(&t, 0, MAX_NODE_SIZE, NULL);
    struct choices c = { { 0 }, 0 };
    t.gd.op.pointer_listener.pointer_followed = record_choice;
    t.gd.op.pointer_listener.ctx = &c;
    char buf[64];
    CHECK(get(&t, 0, "/-k1", buf, sizeof buf) == NULL);
    CHECK_EQ(c.n, 1);
    CHECK_EQ(c.c[0], 0);
    tdag_end(&t);
}

TEST(dag_put0) {
    struct tdag t;
    tdag_init(&t, 0, MAX_NODE_SIZE, NULL);
    t.pd.tt = 10;
    CHECK(put(&t, "/-key", "value"));
    char buf[64];
    CHECK(str_eq(get(&t, 20, "/-key", buf, sizeof buf), "value"));
    CHECK(get(&t, 9, "/-key", buf, sizeof buf) == NULL);
    tdag_end(&t);
}

TEST(dag_put1) {
    struct tdag t;
    tdag_init(&t, 0, MAX_NODE_SIZE, NULL);
    t.pd.tt = 10;
    CHECK(put(&t, "/longerKey1", "value"));
    pd_clear(&t.pd);    /* pd.keyAccessPath.clear() */
    CHECK(put(&t, "/longerKey2", "value"));
    char buf[64];
    CHECK(str_eq(get(&t, 20, "/longerKey1", buf, sizeof buf), "value"));
    CHECK(get(&t, 9, "/longerKey", buf, sizeof buf) == NULL);
    tdag_end(&t);
}

struct changes {
    int32_t n;
    int32_t top_created, key_created, value_created, key_changed, key_replaced;
};

static bool ch_top(void *ctx, struct tnode *n) {
    (void) n;
    struct changes *c = ctx;
    c->n++;
    c->top_created++;
    return true;
}
static bool ch_key_created(void *ctx, struct knode *n) {
    (void) n;
    struct changes *c = ctx;
    c->n++;
    c->key_created++;
    return true;
}
static bool ch_value(void *ctx, struct vnode *n, const int64_t *key, int32_t key_n) {
    (void) n, (void) key, (void) key_n;
    struct changes *c = ctx;
    c->n++;
    c->value_created++;
    return true;
}
static bool ch_key_changed(void *ctx, struct knode *n) {
    (void) n;
    struct changes *c = ctx;
    c->n++;
    c->key_changed++;
    return true;
}

/* DagTester.testDeleteMissingKey: a delete of a key that does not exist
 * creates and changes no node, for keys of one to three segments. */
TEST(dag_delete_missing_key) {
    struct tdag t;
    tdag_init(&t, 0, MAX_NODE_SIZE, NULL);
    t.pd.tt = 10;
    CHECK(put(&t, "/a", "value"));
    pd_clear_fast(&t.pd);
    CHECK(put(&t, "/abcdefXX", "value"));
    pd_clear_fast(&t.pd);

    struct changes c;
    memset(&c, 0, sizeof c);
    struct op_node_change_listener l = { ch_top, ch_key_created, ch_value, ch_key_changed, NULL,
        NULL, &c };
    t.pd.node_change_listener = l;

    const char *keys[] = { "/k/100", "/k/1000", "/k/10000000", "/abcdefgh12345" };
    t.pd.tt = 20;
    for (int i = 0; i < 4; i++) {
        CHECK(put(&t, keys[i], NULL));
        pd_clear_fast(&t.pd);
        CHECK_EQ(c.n, 0);
    }
    obj_collect(&t.f.cx);
    char buf[64];
    CHECK(str_eq(get(&t, 30, "/abcdefXX", buf, sizeof buf), "value"));
    tdag_end(&t);
}

/* DagTester.checkRandomTransactions: transactions of several keys each, with
 * java.util.Random's draws, against a model at every time. */
static void check_random_transactions(int32_t maxNodeSize, int32_t keyCount, int32_t maxOps,
        int32_t n, int64_t seed) {
    struct jrandom rnd;
    jr_init(&rnd, seed);
    struct tdag t;
    tdag_init(&t, 0, maxNodeSize, NULL);
    /* the model: values[key][i] at time 10 * i, i from 1 to n; -2 unset,
     * -1 a delete, else the value's transaction */
    int32_t *model = malloc((size_t) keyCount * (size_t) (n + 1) * sizeof *model);
    for (int32_t i = 0; i < keyCount * (n + 1); i++) {
        model[i] = -2;
    }

    for (int32_t i = 1; i <= n; i++) {
        int64_t tt = 10 * i;
        t.pd.tt = tt;
        int32_t ops = 1 + jr_next_int(&rnd, maxOps);
        int32_t keys[64];
        int32_t nkeys = 0;
        while (nkeys < ops) {           /* a LinkedHashSet<String> */
            int32_t k = jr_next_int(&rnd, keyCount);
            bool seen = false;
            for (int32_t j = 0; j < nkeys; j++) {
                seen = seen || keys[j] == k;
            }
            if (!seen) {
                keys[nkeys++] = k;
            }
        }
        for (int32_t j = 0; j < nkeys; j++) {
            char key[32], value[64];
            snprintf(key, sizeof key, "/k/%d", (int) keys[j]);
            bool del = jr_next_int(&rnd, 4) == 0;
            snprintf(value, sizeof value, "v%lld%s", (long long) tt, key);
            CHECK(put(&t, key, del ? NULL : value));
            pd_clear_fast(&t.pd);
            obj_collect(&t.f.cx);
            model[keys[j] * (n + 1) + i] = del ? -1 : i;
        }
        pd_clear(&t.pd);
    }

    for (int32_t k = 0; k < keyCount; k++) {
        char key[32];
        snprintf(key, sizeof key, "/k/%d", (int) k);
        int32_t last = -2;
        for (int32_t i = 0; i <= n; i++) {
            if (model[k * (n + 1) + i] != -2) {
                last = model[k * (n + 1) + i];
            }
            char expected[64], buf[64];
            snprintf(expected, sizeof expected, "v%lld%s", (long long) (10 * last), key);
            const char *actual = get(&t, 10 * i, key, buf, sizeof buf);
            if (last < 0) {
                CHECK(actual == NULL);
            } else {
                CHECK(str_eq(actual, expected));
            }
        }
    }
    free(model);
    tdag_end(&t);
}

/* DagTester.testTwoNewRootsInOneTransaction */
TEST(dag_two_new_roots_in_one_transaction) {
    check_random_transactions(8, 10, 4, 5, 923);
    check_random_transactions(14, 12, 12, 14, 1);
    check_random_transactions(30, 20, 20, 11, 37);
}

/* More seeds of the same, for the splits of every kind. */
TEST(dag_random_transactions) {
    for (int64_t seed = 1; seed <= 60; seed++) {
        check_random_transactions(8, 30, 12, 40, seed);
        check_random_transactions(14, 60, 20, 30, seed);
    }
}

/* DagTester.testSplit0: splits the space root, a new super root. */
TEST(dag_split0) {
    const char *kvs[] = { "/k1", "v1", "/k2", "v2", "/k3", "v3", "/k4", "v4", "/k0", "v0" };
    struct tdag t;
    tdag_init(&t, 0, 6, NULL);
    t.pd.tt = 10;
    for (int i = 0; i < 10; i += 2) {
        CHECK(put(&t, kvs[i], kvs[i + 1]));
        pd_clear_fast(&t.pd);
    }
    pd_clear(&t.pd);
    CHECK_EQ(t.pd.space_split_count, 1);
    char buf[64];
    for (int i = 0; i < 10; i += 2) {
        CHECK(str_eq(get(&t, 10, kvs[i], buf, sizeof buf), kvs[i + 1]));
    }
    for (int i = 0; i < 10; i += 2) {
        CHECK(get(&t, 9, kvs[i], buf, sizeof buf) == NULL);
    }
    tdag_end(&t);
}

/* DagTester.testTimeSplit1a: a time-split-1. */
TEST(dag_time_split1a) {
    struct tdag t;
    tdag_init(&t, 0, 6, NULL);
    for (int i = 0; i < 4; i++) {
        t.pd.tt = 1 + i;
        char value[32];
        snprintf(value, sizeof value, "v at %lld", (long long) t.pd.tt);
        CHECK(put(&t, "account-id-0", value));
        pd_clear_fast(&t.pd);
        obj_collect(&t.f.cx);
    }
    CHECK_EQ(t.pd.time_split_count, 1);

    const int32_t choices[] = { 0, 3 };
    struct node *node;
    REQUIRE(dag_find_node(&t.dag, choices, 2, &t.gd, &node));
    REQUIRE(node->o.kind == OBJ_KEY);
    struct kwp kwi;
    uint8_t b[8];
    CHECK(keys_ikey_to_bkey((const uint8_t *) "-id-0", 5, b));
    kn_search_eq((struct knode *) node, INT64_MAX, kl_create_compare_value(b, 5), &kwi);
    CHECK_EQ(kwi.klong_time, 4);
    tdag_end(&t);
}

/* Dag.visitMemoryNodes's counts (StatsNodeVisitor): the objects reachable
 * by memory pointers from the super root, each once. */
static void count_memory_nodes(struct dag *d, int32_t counts[3]) {
    struct oset seen = { 0 };
    const struct node *stack[4096];
    int32_t top = 0;
    stack[top++] = &tds_get_super_root(&d->top_ds)->n;
    counts[0] = counts[1] = counts[2] = 0;
    while (top > 0) {
        const struct node *n = stack[--top];
        if (!oset_put(&seen, n, NULL, 0)) {
            continue;
        }
        counts[n->o.kind == OBJ_TOP ? 0 : n->o.kind == OBJ_KEY ? 1 : 2]++;
        int32_t size = node_size(n);
        for (int32_t i = 0; i < size; i++) {
            struct node *c = node_pointer_node(n, i);
            if (c != NULL && top < 4096) {
                stack[top++] = c;
            }
        }
    }
    oset_free(&seen);
}

TEST(dag_visit0) {
    struct tdag t;
    tdag_init(&t, 10, MAX_NODE_SIZE, NULL);
    int32_t c[3];
    count_memory_nodes(&t.dag, c);
    CHECK_EQ(c[0], 1);
    CHECK_EQ(c[1], 1);
    CHECK_EQ(c[2], 0);
    tdag_end(&t);
}

TEST(dag_visit1) {
    struct tdag t;
    tdag_init(&t, 10, MAX_NODE_SIZE, NULL);
    t.pd.tt = 20;
    for (int i = 0; i < 4; i++) {
        char key[32], value[32];
        snprintf(key, sizeof key, "/prefix-%d", i);
        snprintf(value, sizeof value, "v%d", i);
        CHECK(put(&t, key, value));     /* no clearFast, as Java's test */
    }
    int32_t c[3];
    count_memory_nodes(&t.dag, c);
    CHECK_EQ(c[0], 1);
    CHECK_EQ(c[1], 2);
    CHECK_EQ(c[2], 4);
    pd_clear(&t.pd);
    tdag_end(&t);
}

/* DagTester.testPointerCreationListener: the last pointer reported for a
 * node is its last memory pointer, unless the transaction that reported it
 * replaced the node by a split. */
struct pcl {
    struct oset map1;           /* node to its last reported pointee, and its time */
    struct oset earlier;        /* the last pointer reported in an earlier transaction */
    int64_t now;
};

static bool pcl_created(void *ctx, struct node *from, int32_t index, struct node *to) {
    (void) index;
    struct pcl *p = ctx;
    int32_t i = oset_find(&p->map1, from);
    if (i >= 0 && p->map1.t[i] < p->now) {
        oset_put(&p->earlier, from, p->map1.v[i], 0);
    }
    oset_put(&p->map1, from, to, p->now);
    return true;
}

static bool pcl_replaced(void *ctx, struct knode *node) {
    struct pcl *p = ctx;
    int32_t i = oset_find(&p->map1, node);
    if (i >= 0 && p->map1.t[i] == p->now) {
        int32_t j = oset_find(&p->earlier, node);
        if (j < 0) {
            oset_remove(&p->map1, node);
        } else {
            oset_put(&p->map1, node, p->earlier.v[j], p->map1.t[i]);
        }
    }
    return true;
}

static void pointer_creation_listener(int32_t n) {
    struct pcl p;
    memset(&p, 0, sizeof p);
    p.now = 10;
    struct op_pointer_created_listener listener = { pcl_created, &p };
    struct tdag t;
    tdag_init(&t, 10, MAX_NODE_SIZE, &listener);
    t.pd.tt = 20;
    p.now = t.pd.tt;
    t.pd.pointer_created_listener = listener;
    struct op_node_change_listener ncl = OP_DO_NOTHING_NODE_CHANGE_LISTENER;
    ncl.key_node_replaced = pcl_replaced;
    ncl.ctx = &p;
    t.pd.node_change_listener = ncl;

    for (int32_t i = 0; i < n; i++) {
        char key[32], value[32];
        snprintf(key, sizeof key, "/prefix-%d", (int) i);
        snprintf(value, sizeof value, "v%d", (int) i);
        CHECK(put(&t, key, value));
        if (i % 10 == 9) {
            t.pd.tt += 10;
            p.now = t.pd.tt;
        }
    }
    pd_clear(&t.pd);
    {
        int32_t missing = 0;
        char buf[64];
        for (int32_t i = 0; i < n; i++) {
            char key[32], value[32];
            snprintf(key, sizeof key, "/prefix-%d", (int) i);
            snprintf(value, sizeof value, "v%d", (int) i);
            missing += !str_eq(get(&t, INT64_MAX, key, buf, sizeof buf), value);
        }
        CHECK_EQ(missing, 0);      /* C's own check: every key read back */
    }

    /* Dag.visitMemoryPointersOnce: map2, each node's last memory pointer. */
    struct oset seen = { 0 }, map2 = { 0 };
    const struct node **stack = malloc(100000 * sizeof *stack);
    int32_t top = 0;
    stack[top++] = &tds_get_super_root(&t.dag.top_ds)->n;
    while (top > 0) {
        const struct node *x = stack[--top];
        if (!oset_put(&seen, x, NULL, 0)) {
            continue;
        }
        int32_t size = node_size(x);
        for (int32_t i = 0; i < size; i++) {
            struct node *c = node_pointer_node(x, i);
            if (c != NULL) {
                oset_put(&map2, x, c, 0);
                if (top < 100000) {
                    stack[top++] = c;
                }
            }
        }
    }
    CHECK(p.map1.n > 0);
    CHECK_EQ(p.map1.n, map2.n);
    int32_t diff = 0;
    for (int32_t i = 0; i < p.map1.n; i++) {
        int32_t j = oset_find(&map2, p.map1.p[i]);
        if (j < 0 || map2.v[j] != p.map1.v[i]) {
            diff++;
        }
    }
    CHECK_EQ(diff, 0);
    free(stack);
    oset_free(&seen);
    oset_free(&map2);
    oset_free(&p.map1);
    oset_free(&p.earlier);
    tdag_end(&t);
}

TEST(dag_pointer_creation_listener1) {
    pointer_creation_listener(200);
}

TEST(dag_pointer_creation_listener2) {
    pointer_creation_listener(10 * 1000);
}

/* DagTester.testTransactionLeavesNoUnreachableNode */
struct reach {
    struct oset created, changed, replaced;
    int32_t top_nodes;
};

static bool r_top(void *ctx, struct tnode *n) {
    struct reach *r = ctx;
    oset_put(&r->created, n, NULL, 0);
    r->top_nodes++;
    return true;
}
static bool r_key_created(void *ctx, struct knode *n) {
    oset_put(&((struct reach *) ctx)->created, n, NULL, 0);
    return true;
}
static bool r_key_changed(void *ctx, struct knode *n) {
    oset_put(&((struct reach *) ctx)->changed, n, NULL, 0);
    return true;
}
static bool r_key_replaced(void *ctx, struct knode *n) {
    oset_put(&((struct reach *) ctx)->replaced, n, NULL, 0);
    return true;
}

static bool has_time_klong(const struct knode *k, int64_t t) {
    for (int32_t i = 0; i < k->size; i++) {
        if (kl_is_time(k->klongs[i]) && kl_get_time(k->klongs[i]) == t) {
            return true;
        }
    }
    return false;
}

/* DagTester.reachableAt: the super root at t, its root, and the live
 * children at t. */
static void reachable_at(struct tdag *t, int64_t time, struct oset *r) {
    struct tnode *top;
    CHECK(tds_find_super_root_at_time(&t->dag.top_ds, time, &t->gd.op, &top));
    if (top == NULL) {
        return;
    }
    oset_put(r, top, NULL, 0);
    const struct node *stack[4096];
    int32_t sp = 0;
    stack[sp++] = tn_get_pointer_node(top, 0);
    while (sp > 0) {
        const struct node *x = stack[--sp];
        if (!oset_put(r, x, NULL, 0) || x->o.kind != OBJ_KEY) {
            continue;
        }
        const struct knode *k = (const struct knode *) x;
        int32_t sz = k->size;
        int64_t del = kn_get_delete_bitmap_at_time(k, time, sz);
        int64_t lastCv[64];
        int32_t lastIdx[64];
        int32_t nl = 0;
        for (int32_t i = 0; i < sz; i++) {
            int64_t klong = k->klongs[i];
            if (kl_is_time(klong)) {
                if (kl_get_time(klong) > time) {
                    break;
                }
                continue;
            }
            if (kl_get_type(klong) == KL_TYPE_KEY && !kl_is_deleted(del, i)) {
                int64_t cv = kl_get_compare_value(klong);
                int32_t j = 0;
                while (j < nl && lastCv[j] != cv) {
                    j++;
                }
                if (j == nl) {
                    lastCv[nl] = cv;
                    nl++;
                }
                lastIdx[j] = i;
            }
        }
        for (int32_t j = 0; j < nl; j++) {
            struct node *c = kn_get_pointer_node(k, lastIdx[j]);
            if (c != NULL && sp < 4096) {
                stack[sp++] = c;
            }
        }
    }
}

TEST(dag_transaction_leaves_no_unreachable_node) {
    struct tdag t;
    tdag_init(&t, 10, 8, NULL);
    struct reach r;
    memset(&r, 0, sizeof r);
    struct op_node_change_listener l = { r_top, r_key_created, NULL, r_key_changed,
        r_key_replaced, NULL, &r };
    t.pd.node_change_listener = l;

    for (int round = 0; round < 2; round++) {
        r.created.n = r.changed.n = r.replaced.n = 0;
        r.top_nodes = 0;
        t.pd.tt = 20 + 10 * round;
        for (int i = 0; i < 40; i++) {
            char key[32], value[40];
            snprintf(key, sizeof key, "/k/%d", 1000 + 2 * i + round);
            snprintf(value, sizeof value, "v%s", key);
            CHECK(put(&t, key, value));
            pd_clear_fast(&t.pd);
        }
        pd_clear(&t.pd);

        struct oset now = { 0 };
        reachable_at(&t, t.pd.tt, &now);
        for (int32_t i = 0; i < r.created.n; i++) {
            CHECK(oset_find(&now, r.created.p[i]) >= 0);
        }
        for (int32_t i = 0; i < r.changed.n; i++) {
            if (oset_find(&now, r.changed.p[i]) < 0) {
                CHECK(oset_find(&r.replaced, r.changed.p[i]) >= 0);
                CHECK(!has_time_klong(r.changed.p[i], t.pd.tt));
            }
        }
        if (round == 0) {
            CHECK_EQ(r.top_nodes, 1);
        }
        oset_free(&now);
        obj_collect(&t.f.cx);
    }

    char buf[64];
    for (int round = 0; round < 2; round++) {
        for (int i = 0; i < 40; i++) {
            char key[32], value[40];
            snprintf(key, sizeof key, "/k/%d", 1000 + 2 * i + round);
            snprintf(value, sizeof value, "v%s", key);
            CHECK(str_eq(get(&t, 30, key, buf, sizeof buf), value));
        }
    }
    oset_free(&r.created);
    oset_free(&r.changed);
    oset_free(&r.replaced);
    tdag_end(&t);
}

/* The root key node of t's Dag, through the super root's pointer 0. */
static struct knode *root_of(struct tdag *t) {
    struct node *root = node_pointer_node(&tds_get_super_root(&t->dag.top_ds)->n, 0);
    CHECK(root != NULL && root->o.kind == OBJ_KEY);
    return root != NULL && root->o.kind == OBJ_KEY ? (struct knode *) root : NULL;
}

static void check_err(const struct err *e, const char *java, const char *text) {
    bool same = strcmp(e->java, java) == 0 && strcmp(e->text, text) == 0;
    CHECK(same);
    if (!same) {
        printf("    got %s: %s\n", e->java, e->text);
    }
}

#define CCE(from, to) "class bergdb.dag." from " cannot be cast to class bergdb.dag." to \
        " (bergdb.dag." from " and bergdb.dag." to " are in unnamed module of loader 'app')"

/* Dag.checkFound (bergdb 019-32, as Java's since release 2026.3): a put meets a key node
 * that is not a segment leaf and has no klong at or below the key (a damaged node, its leaf
 * flag changed and its checksum right, as harness 6.1's "first key node made a non-leaf"):
 * refused with a DbException, where C aborted on Java's assert. A klong found there whose
 * pointer holds a value: Java's ClassCastException (C's check of the cast, where C read the
 * value as a key node). The Dag's errors go to the op's err (C's). */
TEST(dag_check_found) {
    struct tdag t;
    tdag_init(&t, 0, MAX_NODE_SIZE, NULL);
    struct err e;
    err_clear(&e);
    t.pd.op.err = &e;
    t.pd.tt = 10;
    CHECK(put(&t, "/b", "1"));
    pd_clear(&t.pd);
    struct knode *root = root_of(&t);
    REQUIRE(root != NULL);
    root->n.o.flags = (uint16_t) (root->n.o.flags & ~OBJ_LEAF);
    t.pd.tt = 20;
    CHECK(!put(&t, "/a", "2"));
    char want[200];
    snprintf(want, sizeof want, "Key node %lld, not a segment leaf, has no klong at or below "
            "the key at time 20: corrupt data.", (long long) root->n.id);
    check_err(&e, "DbException", want);
    pd_clear(&t.pd);
    err_clear(&e);
    CHECK(!put(&t, "/c", "3"));
    check_err(&e, "ClassCastException", CCE("ValueNode", "KeyNode"));
    pd_clear(&t.pd);
    root->n.o.flags = (uint16_t) (root->n.o.flags | OBJ_LEAF);
    tdag_end(&t);
}

/* A key node's pointer that holds a node of another type than the code casts it to (in
 * Java, linkToCanonical and resolvePointers link a pointer by the node id at its position
 * without checking the type): Java's exception at each cast or assert, as C's checks give
 * it, where C read the node as the type it expected or aborted (bergdb 019-32's class). A
 * non-leaf root whose klong "/b" holds the super root's handle: a put (setValue's cast), a
 * dirty-node bound (its cast), a getOne (its assert on the klong's node), a getMany (its
 * assert); and a top node whose root pointer holds a top node (TopDs.findRoot's cast). */
TEST(dag_wrong_pointee_type) {
    struct tdag t;
    tdag_init(&t, 0, MAX_NODE_SIZE, NULL);
    struct err e;
    err_clear(&e);
    t.pd.op.err = &e;
    t.gd.op.err = &e;
    t.pd.tt = 10;
    CHECK(put(&t, "/b", "1"));
    pd_clear(&t.pd);
    struct knode *root = root_of(&t);
    REQUIRE(root != NULL);
    struct tnode *super = tds_get_super_root(&t.dag.top_ds);
    node_set_canonical(&super->n, true);
    struct handle *h = hd_of(&t.f.cx, &super->n);
    REQUIRE(h != NULL);
    REQUIRE(root->size == 2 && kl_is_key(root->klongs[1]));
    struct obj *value = root->pointers[1];
    obj_retain(value);
    const int64_t pos = root->pos[1];
    node_set_pointer(&t.f.cx, &root->n, 1, &h->o, 1000);
    root->n.o.flags = (uint16_t) (root->n.o.flags & ~OBJ_LEAF);

    t.pd.tt = 20;
    CHECK(!put(&t, "/c", "3"));
    check_err(&e, "ClassCastException", CCE("TopNode", "KeyNode"));
    pd_clear(&t.pd);

    err_clear(&e);
    struct key k = key_of("/c");
    const int64_t *keys[1] = { k.s };
    const int32_t keyN[1] = { k.n };
    const bool deletes[1] = { false };
    int64_t bound = 0;
    CHECK(!dag_dirty_node_bound(&t.dag, 20, keys, keyN, deletes, 1, &t.gd, &t.f.m, &bound));
    check_err(&e, "ClassCastException", CCE("TopNode", "KeyNode"));

    err_clear(&e);
    struct vnode *v = NULL;
    CHECK(!dag_get_one(&t.dag, 20, k.s, k.n, &t.gd, &v));
    CHECK(strcmp(e.java, "AssertionError") == 0);
    CHECK(strncmp(e.text, "Expected a KeyNode, got TopNode, id ", 36) == 0);

    err_clear(&e);
    struct getmany g;
    gm_init(&g, &t.dag, &t.f.m);
    g.gd.op.pointer_follower.follow = dummy_follow;
    g.gd.op.err = &e;
    g.actual_lookup_time = 20;
    CHECK(!dag_get_many(&t.dag, &g));
    CHECK(strcmp(e.java, "AssertionError") == 0);
    CHECK(strncmp(e.text, "TopNode, id ", 12) == 0);

    root->n.o.flags = (uint16_t) (root->n.o.flags | OBJ_LEAF);
    node_set_pointer(&t.f.cx, &root->n, 1, value, pos);
    obj_release(&t.f.cx, value);

    /* TopDs.findRoot: a top node whose root pointer holds a top node's handle. */
    struct tnode *a = tn_new(&t.f.cx, 0, NULL, 500, 1, 100);
    struct tnode *b = tn_new(&t.f.cx, 0, NULL, 600, 1, 200);
    REQUIRE(a != NULL && b != NULL);
    node_set_canonical(&b->n, true);
    struct handle *hb = hd_of(&t.f.cx, &b->n);
    REQUIRE(hb != NULL);
    tn_set_pointer(&t.f.cx, a, 0, &hb->o, 200);
    struct topds ds;
    tds_init(&ds, a);
    struct knode *found = NULL;
    err_clear(&e);
    CHECK(!tds_find_root(&ds, 5, &t.gd.op, &found));
    check_err(&e, "ClassCastException", CCE("TopNode", "KeyNode"));
    tds_free(&t.f.cx, &ds);
    tdag_end(&t);
}

const struct test dag_tests[] = {
    TEST_ENTRY(dag_test0),
    TEST_ENTRY(dag_test1),
    TEST_ENTRY(dag_put0),
    TEST_ENTRY(dag_put1),
    TEST_ENTRY(dag_delete_missing_key),
    TEST_ENTRY(dag_two_new_roots_in_one_transaction),
    TEST_ENTRY(dag_random_transactions),
    TEST_ENTRY(dag_split0),
    TEST_ENTRY(dag_time_split1a),
    TEST_ENTRY(dag_visit0),
    TEST_ENTRY(dag_visit1),
    TEST_ENTRY(dag_pointer_creation_listener1),
    TEST_ENTRY(dag_pointer_creation_listener2),
    TEST_ENTRY(dag_transaction_leaves_no_unreachable_node),
    TEST_ENTRY(dag_check_found),
    TEST_ENTRY(dag_wrong_pointee_type),
    TEST_END
};
