/* The delete path of release 2026.4 in the Dag (bergdb 022-07; 023-07,
 * section 5: the upward unlink, the take-back, the empty key first, root
 * collapse, and dirtyNodeBound's count of a delete): Java's DagTester tests
 * that release 2026.4 added, on mdb as Java's on a Dag without a Db:
 * testNoKlongNamesATakenBackNode (fault 12), testDeleteEveryKeyAfterTheRootSplit,
 * testDirtyNodeBoundOfDeletes and testDirtyNodeBoundSumsCollapsesOverTrees
 * (023-11, B1). Where Java draws with java.util.Random, test_random draws
 * the same kind of input. The counts are recounted, and nothing is left. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "dag.h"
#include "err.h"
#include "getmany.h"
#include "handle.h"
#include "keys.h"
#include "klong.h"
#include "mdb.h"
#include "mem.h"
#include "node.h"
#include "opdata.h"
#include "test.h"
#include "topds.h"

/* ======== Helpers ======== */

struct dkey {
    int64_t s[8];
    int32_t n;
};

static struct dkey dkey_of(const char *ikey) {
    struct dkey k;
    uint8_t b[64];
    int32_t len = (int32_t) strlen(ikey);
    memset(&k, 0, sizeof k);
    if (len > 56 || !keys_ikey_to_bkey((const uint8_t *) ikey, len, b)) {
        CHECK(false);   /* a bad key */
        k.n = 1;
        return k;
    }
    k.n = keys_segment_count(len);
    keys_to_segments(b, len, k.s);
    return k;
}

static int cmp_dkeys(const void *a, const void *b) {
    const struct dkey *x = a, *y = b;
    return keys_compare_arrays(x->s, x->n, y->s, y->n);
}

/* DagTester.putAll: one transaction at tt, the pairs in the order given;
 * del[i] true for a delete. */
static bool put_all(struct mdb *db, int64_t tt, const struct dkey *keys, const bool *del,
        int32_t n) {
    static const uint8_t v[2] = { 'v', '1' };
    mdb_begin(db, tt);
    for (int32_t i = 0; i < n; i++) {
        if (!mdb_put(db, keys[i].s, keys[i].n, del[i] ? NULL : v, 2)) {
            return false;
        }
    }
    mdb_end(db);
    return true;
}

static void end(struct mdb *db, struct mem *m) {
    CHECK_EQ(mdb_recount(db), 0);
    mdb_free(db);
    CHECK_MEM_ZERO(m);
}

static struct knode *root_at(struct mdb *db, int64_t time) {
    struct getdata gd;
    mdb_new_get_data(db, &gd);
    struct knode *root = NULL;
    CHECK(tds_find_root(dag_get_top_ds(&db->dag), time, &gd.op, &root));
    return root;
}

static bool has_value(struct mdb *db, int64_t time, const struct dkey *k) {
    struct getdata gd;
    mdb_new_get_data(db, &gd);
    struct vnode *v = NULL;
    CHECK(mdb_get_one(db, time, k->s, k->n, &gd, &v));
    return v != NULL;
}

/* A set of nodes, by address (Java's identity set): open addressing. */
struct nset {
    const void **slot;
    int32_t cap;        /* a power of 2 */
    int32_t n;          /* the members */
    int32_t used;       /* the slots not NULL (members and removed ones) */
};

#define NSET_REMOVED ((const void *) (uintptr_t) 1)

static uint32_t nset_hash(const void *p) {
    uint64_t x = (uint64_t) (uintptr_t) p;
    x ^= x >> 33;
    x *= UINT64_C(0xff51afd7ed558ccd);
    x ^= x >> 33;
    return (uint32_t) x;
}

static void nset_clear(struct nset *s) {
    free(s->slot);
    memset(s, 0, sizeof *s);
}

static bool nset_has(const struct nset *s, const void *p) {
    if (s->cap == 0) {
        return false;
    }
    uint32_t h = nset_hash(p) & (uint32_t) (s->cap - 1);
    while (s->slot[h] != NULL) {
        if (s->slot[h] == p) {
            return true;
        }
        h = (h + 1) & (uint32_t) (s->cap - 1);
    }
    return false;
}

static void nset_add(struct nset *s, const void *p) {
    if (nset_has(s, p)) {
        return;
    }
    if (2 * (s->used + 1) > s->cap) {
        int32_t cap = s->cap == 0 ? 64 : 2 * s->cap;
        const void **slot = calloc((size_t) cap, sizeof *slot);
        for (int32_t i = 0; i < s->cap; i++) {
            const void *q = s->slot[i];
            if (q != NULL && q != NSET_REMOVED) {
                uint32_t h = nset_hash(q) & (uint32_t) (cap - 1);
                while (slot[h] != NULL) {
                    h = (h + 1) & (uint32_t) (cap - 1);
                }
                slot[h] = q;
            }
        }
        free(s->slot);
        s->slot = slot;
        s->cap = cap;
        s->used = s->n;
    }
    uint32_t h = nset_hash(p) & (uint32_t) (s->cap - 1);
    while (s->slot[h] != NULL) {
        h = (h + 1) & (uint32_t) (s->cap - 1);
    }
    s->slot[h] = p;
    s->n++;
    s->used++;
}

static void nset_remove(struct nset *s, const void *p) {
    if (s->cap == 0) {
        return;
    }
    uint32_t h = nset_hash(p) & (uint32_t) (s->cap - 1);
    while (s->slot[h] != NULL) {
        if (s->slot[h] == p) {
            s->slot[h] = NSET_REMOVED;
            s->n--;
            return;
        }
        h = (h + 1) & (uint32_t) (s->cap - 1);
    }
}

/* ======== testNoKlongNamesATakenBackNode ======== */

/* The taken-back nodes, each held (counted) so that its address stays its
 * own until the test has looked: Java's identity set holds them too. */
struct taken {
    struct mdb *db;
    struct knode *node[8192];
    int32_t n;
};

static bool taken_back(void *ctx, struct knode *node) {
    struct taken *t = ctx;
    if (t->n < 8192) {
        obj_retain(&node->n.o);
        t->node[t->n++] = node;
    }
    return true;
}

static bool is_taken(const struct taken *t, const void *node) {
    for (int32_t i = 0; i < t->n; i++) {
        if (t->node[i] == node) {
            return true;
        }
    }
    return false;
}

/* Fault 12 (bergdb 023-08, review C): one transaction puts z keys after a
 * history of b keys in one segment tree, then deletes every b key, in that
 * order, out of key order, as a key transformation could give them to the
 * Dag before Db sorted the transformed keys. The segment root that the
 * transaction made is split in place under a new root, and the deletes
 * empty and take it back. No klong of a node reachable at any time, live,
 * deleted or shadowed, may name a node taken back: such a node is never
 * written. Fails without the in-place repoint of space_split_in_place. */
TEST(delete_no_klong_names_a_taken_back_node) {
    uint64_t rs = 20261111;
    int64_t takenInAll = 0;
    for (int iter = 0; iter < 40; iter++) {
        const int32_t b = 4 + test_random_below(&rs, 5);
        struct mem m;
        mem_init(&m);
        struct mdb db;
        REQUIRE(mdb_create(&db, &m, 0, b));
        struct taken *tk = calloc(1, sizeof *tk);
        tk->db = &db;
        db.pd.node_change_listener.key_node_taken_back = taken_back;
        db.pd.node_change_listener.value_node_created = NULL;
        db.pd.node_change_listener.ctx = tk;
        const int32_t nb = 1 + test_random_below(&rs, 60);
        const int32_t hist = 1 + test_random_below(&rs, 4);
        struct dkey keys[200];
        bool del[200];
        int64_t t = 1;
        char text[40];
        for (int h = 0; h < hist; h++, t++) {
            int32_t n = 0;
            for (int i = 0; i < nb; i++) {
                if (h == 0 || test_random_below(&rs, 3) == 0) {
                    snprintf(text, sizeof text, "/prefix/b%04d", i);
                    keys[n] = dkey_of(text);
                    del[n++] = false;
                }
            }
            REQUIRE(put_all(&db, t, keys, del, n));
        }
        const int32_t nz = 1 + test_random_below(&rs, 120);
        int32_t n = 0;
        for (int i = 0; i < nz; i++) {
            snprintf(text, sizeof text, "/prefix/z%04d", i);
            keys[n] = dkey_of(text);
            del[n++] = false;
        }
        for (int i = 0; i < nb; i++) {
            snprintf(text, sizeof text, "/prefix/b%04d", i);
            keys[n] = dkey_of(text);
            del[n++] = true;
        }
        REQUIRE(put_all(&db, t, keys, del, n));

        struct nset seen;
        memset(&seen, 0, sizeof seen);
        struct knode **todo = malloc(65536 * sizeof *todo);
        int32_t ntodo = 0;
        for (int64_t u = 0; u <= t; u++) {
            struct knode *root = root_at(&db, u);
            if (root != NULL && !nset_has(&seen, root)) {
                nset_add(&seen, root);
                todo[ntodo++] = root;
            }
        }
        bool reachable = false, named = false;
        while (ntodo > 0) {
            struct knode *node = todo[--ntodo];
            reachable = reachable || is_taken(tk, node);
            for (int32_t i = 0; i < node->size; i++) {
                if (kl_get_int_type(node->klongs[i]) != KL_INT_TYPE_KEY) {
                    continue;
                }
                struct node *c = kn_get_pointer_node(node, i);
                named = named || (c != NULL && is_taken(tk, c));
                if (c != NULL && c->o.kind == OBJ_KEY && !nset_has(&seen, c) && ntodo < 65536) {
                    nset_add(&seen, c);
                    todo[ntodo++] = (struct knode *) c;
                }
            }
        }
        CHECK(!reachable);      /* a taken-back node is reachable */
        CHECK(!named);          /* a klong names a taken-back node */
        if (reachable || named) {
            printf("  iter %d, b %d, nb %d, hist %d, nz %d\n", iter, (int) b, (int) nb, hist,
                    (int) nz);
        }
        for (int32_t i = 0; i < n; i++) {
            CHECK_EQ(has_value(&db, t, &keys[i]), !del[i]);
        }
        takenInAll += tk->n;
        free(todo);
        nset_clear(&seen);
        for (int32_t i = 0; i < tk->n; i++) {
            obj_release(&db.cx, &tk->node[i]->n.o);
        }
        free(tk);
        obj_collect(&db.cx);
        end(&db, &m);
    }
    CHECK(takenInAll > 0);      /* the case was reached */
}

/* ======== testDeleteEveryKeyAfterTheRootSplit ======== */

/* Every key deleted, after a transaction that split the space root: one
 * transaction puts keys between those of an earlier one, so that the space
 * root and its nodes are split by it, and deletes every old key, one
 * operation a key; the next deletes the new keys. Root collapse lowers the
 * space root as it loses its children: at the last time it is a segment
 * leaf, empty, and every key is gone; at the times before, the keys put
 * then are there. Node sizes 4 and 8, keys of one segment and of two. */
TEST(delete_every_key_after_the_root_split) {
    const int32_t sizes[] = { 4, 8 };
    const char *const prefixes[] = { "/k", "/key/prefix/" };
    int64_t collapses = 0;
    for (int bi = 0; bi < 2; bi++) {
        for (int pi = 0; pi < 2; pi++) {
            struct mem m;
            mem_init(&m);
            struct mdb db;
            REQUIRE(mdb_create(&db, &m, 0, sizes[bi]));
            struct dkey all[60], keys[60];
            bool del[60];
            char text[40];
            for (int i = 0; i < 60; i++) {
                snprintf(text, sizeof text, "%s%d", prefixes[pi], 100 + i);
                all[i] = dkey_of(text);
            }
            int32_t n = 0;
            for (int i = 0; i < 60; i += 2) {
                keys[n] = all[i];
                del[n++] = false;
            }
            REQUIRE(put_all(&db, 1, keys, del, n));
            for (int i = 0; i < 60; i++) {
                keys[i] = all[i];
                del[i] = i % 2 == 0;    /* the old keys deleted, new ones put */
            }
            REQUIRE(put_all(&db, 2, keys, del, 60));
            n = 0;
            for (int i = 1; i < 60; i += 2) {
                keys[n] = all[i];
                del[n++] = true;
            }
            REQUIRE(put_all(&db, 3, keys, del, n));

            struct knode *root = root_at(&db, 3);
            REQUIRE(root != NULL);
            CHECK(kn_is_segment_leaf(root));    /* the root is a segment leaf */
            for (int i = 0; i < 60; i++) {
                CHECK(!has_value(&db, 3, &all[i]));
                CHECK_EQ(has_value(&db, 2, &all[i]), i % 2 != 0);
                CHECK_EQ(has_value(&db, 1, &all[i]), i % 2 == 0);
            }
            collapses += db.pd.stat_collapses;
            end(&db, &m);
        }
    }
    CHECK(collapses > 0);       /* root collapses */
}

/* ======== testDirtyNodeBoundOfDeletes ======== */

/* DagTester.BoundCase: a Dag and the key nodes a transaction makes dirty:
 * those the writer follows, makes or changes, less those it replaces,
 * unlinks or takes back. */
struct bound_case {
    struct mem m;
    struct mdb db;
    struct op_pointer_listener inner;
    struct nset dirty;
    int64_t t;
};

static bool bc_followed(void *ctx, struct node *pre, int32_t index, struct node *result,
        int32_t type) {
    struct bound_case *c = ctx;
    if (result != NULL && result->o.kind == OBJ_KEY) {
        nset_add(&c->dirty, result);
    }
    return c->inner.pointer_followed(c->inner.ctx, pre, index, result, type);
}

static bool bc_accessed(void *ctx, struct tnode *superRoot) {
    (void) ctx, (void) superRoot;
    return true;
}

static bool bc_dirty(void *ctx, struct knode *n) {
    nset_add(&((struct bound_case *) ctx)->dirty, n);
    return true;
}

static bool bc_replaced(void *ctx, struct knode *n) {
    nset_remove(&((struct bound_case *) ctx)->dirty, n);
    return true;
}

static bool bc_init(struct bound_case *c, int32_t b) {
    memset(c, 0, sizeof *c);
    mem_init(&c->m);
    if (!mdb_create(&c->db, &c->m, 0, b)) {
        return false;
    }
    c->inner = c->db.pd.op.pointer_listener;
    c->db.pd.op.pointer_listener.pointer_followed = bc_followed;
    c->db.pd.op.pointer_listener.super_root_accessed = bc_accessed;
    c->db.pd.op.pointer_listener.ctx = c;
    c->db.pd.node_change_listener.top_node_created = NULL;
    c->db.pd.node_change_listener.key_node_created = bc_dirty;
    c->db.pd.node_change_listener.value_node_created = NULL;
    c->db.pd.node_change_listener.key_node_changed = bc_dirty;
    c->db.pd.node_change_listener.key_node_replaced = bc_replaced;
    c->db.pd.node_change_listener.key_node_taken_back = NULL;   /* key_node_replaced */
    c->db.pd.node_change_listener.top_node_replaced = NULL;
    c->db.pd.node_change_listener.ctx = c;
    c->t = 1;
    return true;
}

static void bc_free(struct bound_case *c) {
    nset_clear(&c->dirty);
    end(&c->db, &c->m);
}

/* BoundCase.run: one transaction: the puts, then the deletes; with check,
 * against the bound. */
static void bc_run(struct bound_case *c, const struct dkey *puts, int32_t nputs,
        const struct dkey *dels, int32_t ndels, bool check) {
    const int32_t n = nputs + ndels;
    int64_t bound = -1;
    if (check) {
        const int64_t **kp = malloc((size_t) (n > 0 ? n : 1) * sizeof *kp);
        int32_t *kn = malloc((size_t) (n > 0 ? n : 1) * sizeof *kn);
        bool *del = malloc((size_t) (n > 0 ? n : 1) * sizeof *del);
        for (int32_t i = 0; i < n; i++) {
            const struct dkey *k = i < nputs ? &puts[i] : &dels[i - nputs];
            kp[i] = k->s;
            kn[i] = k->n;
            del[i] = i >= nputs;
        }
        struct getdata gd;
        mdb_new_get_data(&c->db, &gd);
        CHECK(dag_dirty_node_bound(&c->db.dag, c->t - 1, kp, kn, del, n, &gd, &c->m, &bound));
        free(kp);
        free(kn);
        free(del);
    }
    nset_clear(&c->dirty);
    static const uint8_t v[2] = { 'v', '1' };
    mdb_begin(&c->db, c->t);
    for (int32_t i = 0; i < n; i++) {
        const struct dkey *k = i < nputs ? &puts[i] : &dels[i - nputs];
        if (!mdb_put(&c->db, k->s, k->n, i < nputs ? v : NULL, 2)) {
            CHECK(false);       /* a put failed */
            break;
        }
    }
    mdb_end(&c->db);
    if (check) {
        CHECK(c->dirty.n <= bound);
        if (c->dirty.n > bound) {
            printf("  t %lld, %d puts, %d keys: %d dirty key nodes, bound %lld\n",
                    (long long) c->t, (int) nputs, (int) n, (int) c->dirty.n, (long long) bound);
        }
    }
    c->t++;
}

/* Dag.dirtyNodeBound for transactions with deletes (bergdb 023-07, section
 * 5.4, K4; 023-08, reviews B and C, 2.5) against the key nodes that the
 * transaction makes dirty. At node sizes 8, 14 and 30: (1) random
 * histories, thinned out to leave chains of single children, and a
 * transaction of deletes and some puts; (2) a chain that root collapse takes
 * in one delete, several levels, each a klong in the segment leaf above,
 * and the same below a segment leaf filled to one klong short of full;
 * (3) transactions of 1,000 deletes, and one of 100,000 at node size 30. */
TEST(delete_dirty_node_bound_of_deletes) {
    uint64_t rs = 5;
    const int32_t sizes[] = { 8, 14, 30 };
    struct bound_case *c = malloc(sizeof *c);
    struct dkey *keys = malloc(100000 * sizeof *keys);
    struct dkey *puts = malloc(100000 * sizeof *puts);
    struct dkey *dels = malloc(100000 * sizeof *dels);
    bool *live = malloc(100000 * sizeof *live);
    char text[80];
    for (int bi = 0; bi < 3; bi++) {
        const int32_t b = sizes[bi];
        for (int iter = 0; iter < 40; iter++) {
            REQUIRE(bc_init(c, b));
            const int32_t nk = 20 + test_random_below(&rs, b * b * 3);
            const int32_t shape = test_random_below(&rs, 4);
            for (int32_t i = 0; i < nk; i++) {
                switch (shape) {
                case 0:
                    snprintf(text, sizeof text, "/k/%05d", (int) i);
                    break;
                case 1:
                    snprintf(text, sizeof text, "/prefix/%c/%05d", 'a' + (int) (i % 3), (int) i);
                    break;
                case 2:
                    snprintf(text, sizeof text, "/p%05d/x%05d", (int) (i % 5), (int) i);
                    break;
                default:
                    snprintf(text, sizeof text, "/longprefix/abcdefgh/%05d%s", (int) i,
                            i % 2 == 0 ? "/tail/more" : "");
                    break;
                }
                keys[i] = dkey_of(text);
                live[i] = false;
            }
            qsort(keys, (size_t) nk, sizeof keys[0], cmp_dkeys);
            const int32_t hist = 1 + test_random_below(&rs, 4);
            for (int h = 0; h < hist; h++) {
                int32_t np = 0;
                for (int32_t i = 0; i < nk; i++) {
                    if (h == 0 || test_random_below(&rs, 4) == 0) {
                        puts[np++] = keys[i];
                        live[i] = true;
                    }
                }
                bc_run(c, puts, np, NULL, 0, false);
            }
            if (test_random_below(&rs, 2) == 0) {
                const int32_t k = 2 + test_random_below(&rs, b);
                int32_t nd = 0;
                for (int32_t i = 0; i < nk; i++) {
                    if (i % k != 0 && live[i]) {
                        live[i] = false;
                        dels[nd++] = keys[i];
                    }
                }
                bc_run(c, NULL, 0, dels, nd, false);
            }
            const int32_t lo = test_random_below(&rs, nk);
            const int32_t hi = lo + test_random_below(&rs, nk - lo + 1);
            const int32_t pdel = test_random_below(&rs, 101);
            const bool range = test_random_below(&rs, 2) == 0;
            int32_t np = 0, nd = 0;
            for (int32_t i = 0; i < nk; i++) {
                const bool del = range ? i >= lo && i < hi : test_random_below(&rs, 100) < pdel;
                if (del && live[i]) {
                    dels[nd++] = keys[i];
                } else if (test_random_below(&rs, 50) == 0) {
                    puts[np++] = keys[i];
                }
            }
            bc_run(c, puts, np, dels, nd, true);
            bc_free(c);
        }

        /* (2) A chain: keep the first and the last key of a segment tree of
         * three or more levels; then a delete of the first leaves the root
         * one child, a chain of single children down to the last key's leaf,
         * which root collapse takes in one delete. */
        const int32_t n = b * b * 2;
        for (int32_t i = 0; i < n; i++) {
            snprintf(text, sizeof text, "/prefix/%05d", (int) i);
            keys[i] = dkey_of(text);
        }
        REQUIRE(bc_init(c, b));
        bc_run(c, keys, n, NULL, 0, false);
        bc_run(c, NULL, 0, keys + 1, n - 2, true);
        int64_t collapses0 = c->db.pd.stat_collapses;
        bc_run(c, NULL, 0, keys, 1, true);
        CHECK(c->db.pd.stat_collapses - collapses0 >= 2);   /* several levels in one delete */
        bc_free(c);

        /* (2b) The same chain below a segment leaf filled with live klongs to
         * one klong short of full, so that the collapses' klongs overflow it. */
        for (int extra = 0; extra < 3; extra++) {
            REQUIRE(bc_init(c, b));
            bc_run(c, keys, n, NULL, 0, false);
            bc_run(c, NULL, 0, keys + 1, n - 2, false);
            struct knode *leaf = root_at(&c->db, c->t - 1);
            REQUIRE(leaf != NULL);
            CHECK(kn_is_segment_leaf(leaf));    /* the space root is a segment leaf */
            int32_t nf = 0;
            for (int i = 0; i < b - 2 - leaf->size + extra && i < 20; i++) {
                snprintf(text, sizeof text, "/%caaaaa/x", 'a' + i);
                puts[nf++] = dkey_of(text);
            }
            bc_run(c, puts, nf, NULL, 0, false);
            collapses0 = c->db.pd.stat_collapses;
            bc_run(c, NULL, 0, keys, 1, true);
            CHECK(c->db.pd.stat_collapses - collapses0 >= 2);
            bc_free(c);
        }

        /* (3) 1,000 deletes, of every key and of every third. */
        for (int step = 1; step <= 3; step += 2) {
            REQUIRE(bc_init(c, b));
            const int32_t total = 1000 * step;
            for (int32_t i = 0; i < total; i++) {
                snprintf(text, sizeof text, "/k/%06d", (int) i);
                keys[i] = dkey_of(text);
            }
            bc_run(c, keys, total, NULL, 0, false);
            int32_t nd = 0;
            for (int32_t i = 0; i < total; i += step) {
                dels[nd++] = keys[i];
            }
            bc_run(c, NULL, 0, dels, nd, true);
            bc_free(c);
        }
    }
    REQUIRE(bc_init(c, 30));
    for (int32_t i = 0; i < 100000; i++) {
        snprintf(text, sizeof text, "/big/%06d", (int) i);
        keys[i] = dkey_of(text);
    }
    bc_run(c, keys, 100000, NULL, 0, false);
    bc_run(c, NULL, 0, keys, 100000, true);
    bc_free(c);
    free(c);
    free(keys);
    free(puts);
    free(dels);
    free(live);
}

/* Dag.dirtyNodeBound sums the klongs that root collapse gives a segment
 * leaf over the trees below it (bergdb 023-11, review B, B1): the space
 * root, a segment leaf, names three trees of 1,024 keys at node size 8; a
 * transaction deletes every key of each but its first and last, so each
 * root has two chains of single children; the next deletes the first key of
 * each tree, and root collapse lowers each root five levels, a klong in the
 * space root for each: 15. The count gives the space root at least the
 * collapses and two klongs a delete; with the most of one tree instead of
 * the sum it is 2 x 3 + 5 = 11. The bound also covers the dirty key nodes. */
TEST(delete_dirty_node_bound_sums_collapses_over_trees) {
    struct bound_case *c = malloc(sizeof *c);
    struct dkey *all = malloc(3 * 1024 * sizeof *all);
    struct dkey *thin = malloc(3 * 1024 * sizeof *thin);
    struct dkey firsts[3];
    int32_t nall = 0, nthin = 0;
    char text[40];
    REQUIRE(bc_init(c, 8));
    for (int m = 0; m < 3; m++) {
        for (int i = 0; i < 1024; i++) {
            snprintf(text, sizeof text, "/pref0%d/k%04d", m, i);
            all[nall] = dkey_of(text);
            if (i == 0) {
                firsts[m] = all[nall];
            } else if (i < 1023) {
                thin[nthin++] = all[nall];
            }
            nall++;
        }
    }
    bc_run(c, all, nall, NULL, 0, false);
    bc_run(c, NULL, 0, thin, nthin, false);
    struct knode *leaf = root_at(&c->db, c->t - 1);
    REQUIRE(leaf != NULL);
    CHECK(kn_is_segment_leaf(leaf));    /* the space root is a segment leaf */
    const int64_t *kp[3];
    int32_t kn[3];
    bool del[3];
    for (int i = 0; i < 3; i++) {
        kp[i] = firsts[i].s;
        kn[i] = firsts[i].n;
        del[i] = true;
    }
    struct getdata gd;
    mdb_new_get_data(&c->db, &gd);
    int64_t bound, klongs = -1;
    CHECK(dag_dirty_node_bound_klongs(&c->db.dag, c->t - 1, kp, kn, del, 3, &gd, &c->m, &bound,
            leaf, &klongs));
    const int64_t collapses0 = c->db.pd.stat_collapses;
    bc_run(c, NULL, 0, firsts, 3, true);
    const int64_t collapses = c->db.pd.stat_collapses - collapses0;
    CHECK_EQ(collapses, 15);            /* five in each tree */
    CHECK(klongs >= collapses + 2 * 3); /* the klongs counted for the space root */
    if (klongs < collapses + 2 * 3) {
        printf("  klongs counted for the space root: %lld\n", (long long) klongs);
    }
    bc_free(c);
    free(c);
    free(all);
    free(thin);
}

/* ======== A cycle (bergdb 020-32) ======== */

/* OpData.descentFrom and descentTo: Brent's cycle detection on node ids. A
 * path of distinct ids never fails; a path of p nodes into a cycle of c
 * nodes is found within a few times p + c steps; ids of -1 (no id) are not
 * compared. Java's text. */
TEST(delete_descent_cycle_check) {
    struct opdata op;
    struct err e;
    struct node n;
    op_init(&op);
    err_clear(&e);
    op.err = &e;
    memset(&n, 0, sizeof n);
    n.id = 3;
    op_descent_from(&op, &n);
    bool ok = true;
    for (int i = 1; i <= 100000 && ok; i++) {
        n.id = 3 + 2 * i;
        ok = op_descent_to(&op, &n);
    }
    CHECK(ok);                  /* distinct ids: a valid tree's path */
    CHECK_EQ(e.code, ERR_OK);

    const int paths[] = { 0, 1, 2, 5, 17, 100 }, cycles[] = { 1, 2, 3, 7, 64, 1000 };
    for (int pi = 0; pi < 6; pi++) {
        for (int ci = 0; ci < 6; ci++) {
            const int p = paths[pi], c = cycles[ci];
            err_clear(&e);
            n.id = p > 0 ? 10 : 100000;
            op_descent_from(&op, &n);
            int steps = 0;
            bool found = false;
            for (int j = 1; j <= 8 * (p + c) + 8 && !found; j++) {
                n.id = j < p ? 10 + j : 100000 + (j - p) % c;
                steps = j;
                found = !op_descent_to(&op, &n);
            }
            CHECK(found);
            CHECK(steps <= 4 * (p + c) + 4);
            CHECK_EQ(e.code, ERR_FORMAT);
            CHECK(strcmp(e.java, "StreamFormatException") == 0);
            char want[120];
            snprintf(want, sizeof want, "A descent came back to key node %lld, which it "
                    "passed: the pointers make a cycle.", (long long) n.id);
            CHECK(strcmp(e.text, want) == 0);
        }
    }

    err_clear(&e);
    n.id = -1;
    op_descent_from(&op, &n);
    ok = true;
    for (int i = 0; i < 100 && ok; i++) {
        ok = op_descent_to(&op, &n);
    }
    CHECK(ok);                  /* nodes without an id are not compared */
}

/* A cycle in the Dag, as the damaged stream of 020-32 made one (a key
 * node's pointer to its child became a pointer to the node itself): a get,
 * a scan, the bound of a transaction and a put that meet it fail with
 * Java's StreamFormatException, where each went round without end. */
TEST(delete_cycle_in_the_dag) {
    struct mem m;
    mem_init(&m);
    struct mdb db;
    REQUIRE(mdb_create(&db, &m, 0, 8));
    struct dkey keys[200];
    bool del[200];
    char text[16];
    for (int i = 0; i < 200; i++) {
        snprintf(text, sizeof text, "/k%03d", i);
        keys[i] = dkey_of(text);
        del[i] = false;
    }
    REQUIRE(put_all(&db, 1, keys, del, 200));
    struct knode *root = root_at(&db, 1);
    REQUIRE(root != NULL && !kn_is_segment_leaf(root));
    root->n.id = 1001;
    int32_t idx = -1;
    for (int32_t i = 0; i < root->size && idx < 0; i++) {
        if (kl_get_int_type(root->klongs[i]) == KL_INT_TYPE_KEY
                && kl_get_compare_value(root->klongs[i]) == 0) {
            idx = i;
        }
    }
    REQUIRE(idx >= 0);
    struct obj *old = kn_get_pointee(root, idx);
    const int64_t ref = kn_get_pointer_pos(root, idx);
    obj_retain(old);
    struct handle *self = hd_of(&db.cx, &root->n);
    REQUIRE(self != NULL);
    kn_set_pointer(&db.cx, root, idx, &self->o, ref);
    REQUIRE(kn_get_pointer_node(root, idx) == &root->n);

    const char *const descent = "A descent came back to key node 1001, which it passed: the "
            "pointers make a cycle.";
    struct err e;
    struct getdata gd;
    struct vnode *v = NULL;
    err_clear(&e);
    mdb_new_get_data(&db, &gd);
    gd.op.err = &e;
    CHECK(!mdb_get_one(&db, INT64_MAX, keys[0].s, keys[0].n, &gd, &v));    /* a get */
    CHECK(strcmp(e.java, "StreamFormatException") == 0);
    CHECK(strcmp(e.text, descent) == 0);

    struct getmany g;
    err_clear(&e);
    mdb_new_get_many(&db, &g);
    g.gd.op.err = &e;
    CHECK(!mdb_get_many(&db, &g));                                          /* a scan */
    CHECK(strcmp(e.java, "StreamFormatException") == 0);
    CHECK(strcmp(e.text, "A scan came back to key node 1001, which it passed: the pointers "
            "make a cycle.") == 0);

    const int64_t *kp[1] = { keys[0].s };
    const int32_t kn[1] = { keys[0].n };
    const bool dl[1] = { true };
    int64_t bound;
    err_clear(&e);
    mdb_new_get_data(&db, &gd);
    gd.op.err = &e;
    CHECK(!dag_dirty_node_bound(&db.dag, 1, kp, kn, dl, 1, &gd, &m, &bound));  /* the bound */
    CHECK(strcmp(e.text, descent) == 0);

    err_clear(&e);
    db.pd.op.err = &e;
    mdb_begin(&db, 2);
    CHECK(!mdb_put(&db, keys[0].s, keys[0].n, NULL, 0));                    /* a delete */
    CHECK(strcmp(e.java, "StreamFormatException") == 0);
    CHECK(strcmp(e.text, descent) == 0);

    /* The pointer as it was, so that the counts are right at the free. */
    kn_set_pointer(&db.cx, root, idx, old, ref);
    obj_release(&db.cx, old);
    mdb_free(&db);
    CHECK_MEM_ZERO(&m);
}

const struct test delete_tests[] = {
    TEST_ENTRY(delete_no_klong_names_a_taken_back_node),
    TEST_ENTRY(delete_every_key_after_the_root_split),
    TEST_ENTRY(delete_dirty_node_bound_of_deletes),
    TEST_ENTRY(delete_dirty_node_bound_sums_collapses_over_trees),
    TEST_ENTRY(delete_descent_cycle_check),
    TEST_ENTRY(delete_cycle_in_the_dag),
    TEST_END
};
