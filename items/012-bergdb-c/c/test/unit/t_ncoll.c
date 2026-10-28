/* The tests of ncoll (bergdb 012-10, part 1): Java's NodeCollection tests
 * that C has the behaviour of (testFollowNewerVersion, testFollowRuleR,
 * testLoaderTakesTheHandlesObject, testNoCutBackAfterReconstruction,
 * testResolvePointers without its record, testResolvePointersUnpinned,
 * testLinkToCanonical, testLinkToCanonicalByPosition,
 * testLinkToCanonicalTopNode, testLinkToCanonicalCheck), on a source of
 * nodes as Java's TestStream (a map from positions to node objects, each
 * read giving the same object); and the node table's rules (Cache3's
 * register, install, makeCanonical, dropIfEmpty). Left out:
 * testMaintenanceFollower (reclaim's follower, 012-11) and testAccessData
 * (the access clock, eviction's, 012-12; the CLOCK bit is checked here). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "handle.h"
#include "keys.h"
#include "klong.h"
#include "knode.h"
#include "lmap.h"
#include "mem.h"
#include "ncoll.h"
#include "ntable.h"
#include "obj.h"
#include "opdata.h"
#include "spos.h"
#include "stream.h"
#include "test.h"
#include "tnode.h"

/* TestStream: nodes by position. */
struct tstream {
    int64_t pos[8];
    struct node *node[8];
    int32_t n;
    int32_t reads;
    int32_t header_reads;
};

static enum err_code ts_read_node(void *ctx, int64_t pos, struct node **out, struct err *e) {
    struct tstream *t = ctx;
    t->reads++;
    for (int32_t i = 0; i < t->n; i++) {
        if (t->pos[i] == pos) {
            *out = t->node[i];
            return ERR_OK;
        }
    }
    return err_set(e, ERR_IO, "IOException", "no node at %lld", (long long) pos);
}

static enum err_code ts_read_header(void *ctx, int64_t pos, int32_t *type, int64_t *id,
        struct err *e) {
    struct tstream *t = ctx;
    t->header_reads++;
    for (int32_t i = 0; i < t->n; i++) {
        if (t->pos[i] == pos) {
            *type = node_type(t->node[i]);
            *id = t->node[i]->id;
            return ERR_OK;
        }
    }
    return err_set(e, ERR_IO, "IOException", "no node at %lld", (long long) pos);
}

/* The test's world: an object context, a node table, a collection on a
 * memory stream (unused: the source serves the nodes), the test stream. */
struct world {
    struct mem m;
    struct obj_ctx cx;
    struct stream s;
    struct ntable nt;
    struct ncoll nc;
    struct tstream ts;
    struct obj *held[32];       /* the test's own holds (the parents, the stream's nodes) */
    int32_t nheld;
};

static void world_init(struct world *w) {
    memset(w, 0, sizeof *w);
    mem_init(&w->m);
    obj_ctx_init(&w->cx, &w->m);
    stream_open_memory(&w->s, &w->m);
    nt_init(&w->nt, &w->cx, &w->m);
    nc_init(&w->nc, &w->cx, &w->m, &w->s, &w->nt);
    w->nc.source.read_node = ts_read_node;
    w->nc.source.read_header = ts_read_header;
    w->nc.source.ctx = &w->ts;
}

static void hold(struct world *w, struct node *n) {
    obj_retain(&n->o);
    w->held[w->nheld++] = &n->o;
}

static void world_free(struct world *w) {
    struct obj *roots[64];
    int32_t k = 0;
    for (int32_t i = 0; i < w->nheld; i++) {
        roots[k++] = w->held[i];
    }
    for (int64_t i = 0; i < nt_slots(&w->nt) && k < 64; i++) {
        struct handle *h = nt_slot(&w->nt, i);
        if (h != NULL) {
            roots[k++] = &h->o;
        }
    }
    CHECK_EQ(obj_recount(&w->cx, roots, k, NULL), 0);
    obj_free_all(&w->cx, roots, k);
    nt_free(&w->nt, false);
    nc_free(&w->nc);
    stream_close(&w->s);
    CHECK_MEM_ZERO(&w->m);
}

static void stream_put(struct world *w, int64_t pos, struct node *n) {
    w->ts.pos[w->ts.n] = pos;
    w->ts.node[w->ts.n] = n;
    w->ts.n++;
    hold(w, n);
}

/* Keys.toSegments("k" + suffix)[0] as a key klong. */
static int64_t key_klong(const char *ikey) {
    uint8_t b[32];
    int32_t len = (int32_t) strlen(ikey);
    CHECK(keys_ikey_to_bkey((const uint8_t *) ikey, len, b));
    int64_t segs[4];
    keys_to_segments(b, len, segs);
    return kl_compare_value_to_key_klong(segs[0]);
}

/* testKeyNode: a key node version, id, position, and one key klong at each
 * of the given times (a TIME klong, then a key "k<time>" to 1000 + 8 time). */
static struct knode *test_key_node(struct world *w, int64_t id, int64_t pos, int32_t n,
        const int64_t *times) {
    struct knode *k = kn_new(&w->cx, true);
    for (int32_t i = 0; i < n; i++) {
        char name[32];
        snprintf(name, sizeof name, "k%lld", (long long) times[i]);
        CHECK(kn_add_to_end(&w->cx, k, kl_create_time(times[i]), NULL, -1));
        CHECK(kn_add_to_end(&w->cx, k, key_klong(name), NULL, 1000 + times[i] * 8));
    }
    k->n.id = id;
    k->n.spos = pos;
    return k;
}

/* testParent: a top node whose pointer 0 is a stream pointer to pos. */
static struct tnode *test_parent(struct world *w, int64_t id, int64_t pos) {
    struct tnode *t = tn_new(&w->cx, 0, NULL, pos, 1, id - 1);
    t->n.id = id;
    hold(w, &t->n);
    return t;
}

/* testNodeOfD: a canonical key node with a key klong at time 10 for each
 * pointer. */
static struct knode *test_node_of_d(struct world *w, int64_t id, int32_t n,
        const int64_t *pointers) {
    struct knode *k = kn_new(&w->cx, false);
    CHECK(kn_add_to_end(&w->cx, k, kl_create_time(10), NULL, -1));
    for (int32_t i = 0; i < n; i++) {
        char name[32];
        snprintf(name, sizeof name, "k%d", (int) i);
        CHECK(kn_add_to_end(&w->cx, k, key_klong(name), NULL, pointers[i]));
    }
    k->n.id = id;
    node_set_canonical(&k->n, true);
    hold(w, &k->n);
    return k;
}

/* testGetData: Dag.CACHE_ALL and a listener that counts. */
static bool cache_all(void *ctx, const struct node *node) {
    (void) ctx;
    (void) node;
    return true;
}

static bool count_followed(void *ctx, struct node *pred, int32_t index, struct node *result,
        int32_t type) {
    (void) pred;
    (void) index;
    (void) result;
    (void) type;
    (*(int32_t *) ctx)++;
    return true;
}

static bool nothing_accessed(void *ctx, struct tnode *superRoot) {
    (void) ctx;
    (void) superRoot;
    return true;
}

static void test_op(struct opdata *op, int32_t *calls) {
    op_init(op);
    op->access_data = ACCESS_DATA_DEFAULT;
    op->cache_policy.should_cache = cache_all;
    op->pointer_listener.pointer_followed = count_followed;
    op->pointer_listener.super_root_accessed = nothing_accessed;
    op->pointer_listener.ctx = calls;
}

static struct node *reg(struct world *w, struct node *n) {
    struct node *out;
    CHECK(nt_register(&w->nt, n, &out));
    return out;
}

TEST(ncoll_follow_newer_version) {
    struct world w;
    world_init(&w);
    const int64_t t10[] = { 10 }, t1020[] = { 10, 20 };
    stream_put(&w, 100, &test_key_node(&w, 101, 100, 1, t10)->n);
    stream_put(&w, 200, &test_key_node(&w, 101, 200, 2, t1020)->n);
    int32_t calls = 0;
    struct opdata op;
    test_op(&op, &calls);
    struct tnode *parent1 = test_parent(&w, 301, 100);
    struct tnode *parent2 = test_parent(&w, 401, 200);
    struct node *a = nc_follow_reader(&w.nc, &parent1->n, 0, &op);
    struct node *b = nc_follow_reader(&w.nc, &parent2->n, 0, &op);
    REQUIRE(a != NULL && b != NULL);
    CHECK_EQ(a->spos, 100);
    CHECK_EQ(b->spos, 200);         /* the version followed */
    CHECK_EQ(calls, 2);             /* the listener's calls */
    CHECK(node_pointer_node(&parent2->n, 0) == b);     /* a memory pointer */
    obj_collect(&w.cx);
    world_free(&w);
}

TEST(ncoll_follow_rule_r) {
    struct world w;
    world_init(&w);
    const int64_t t10[] = { 10 }, t3[] = { 10, 20, 30 };
    stream_put(&w, 100, &test_key_node(&w, 101, 100, 1, t10)->n);
    stream_put(&w, 300, &test_key_node(&w, 101, 300, 3, t3)->n);
    struct lmap newById;
    lmap_init(&newById, &w.m);
    CHECK(lmap_put(&newById, 101, 300));
    nc_set_startup_section(&w.nc, &newById, 250, 25);
    int32_t calls = 0;
    struct opdata op;
    test_op(&op, &calls);
    struct tnode *parent = test_parent(&w, 401, 100);
    struct node *a = nc_follow_reader(&w.nc, &parent->n, 0, &op);
    REQUIRE(a != NULL);
    CHECK_EQ(a->spos, 300);         /* old version followed to the newest */
    CHECK_EQ(node_size(a), 4);      /* cut at startup time 25 */
    CHECK_EQ(node_pointer_pos(&parent->n, 0), 300);    /* the reference after Rule R */
    CHECK(nt_get_node(&w.nt, 101) == NULL);            /* not in the node's handle */
    struct node *b = nc_follow_reader(&w.nc, &test_parent(&w, 501, 101)->n, 0, &op);
    REQUIRE(b != NULL);
    CHECK_EQ(b->spos, 300);         /* vpos followed to the same version */
    CHECK_EQ(w.ts.reads, 2);        /* read again */
    obj_collect(&w.cx);
    world_free(&w);
}

TEST(ncoll_loader_takes_the_handles_object) {
    struct world w;
    world_init(&w);
    const int64_t t10[] = { 10 }, t3[] = { 10, 20, 30 }, t2[] = { 10, 20 };
    stream_put(&w, 100, &test_key_node(&w, 101, 100, 1, t10)->n);
    stream_put(&w, 300, &test_key_node(&w, 101, 300, 3, t3)->n);
    struct knode *snapshot = test_key_node(&w, 101, 200, 2, t2);
    reg(&w, &snapshot->n);
    node_set_canonical(&snapshot->n, false);
    int32_t calls = 0;
    struct opdata op;
    test_op(&op, &calls);

    struct tnode *parent = test_parent(&w, 301, 100);
    struct node *a = nc_follow_reader(&w.nc, &parent->n, 0, &op);
    CHECK(a == &snapshot->n);       /* the newer version in the handle */
    CHECK_EQ(w.ts.reads, 0);        /* no read */
    CHECK(node_pointer_node(&parent->n, 0) == a);      /* swizzled */
    CHECK_EQ(node_pointer_pos(&parent->n, 0), 100);    /* the reference kept */

    /* A pointer to a newer version reads it, and the handle takes it. */
    struct node *b = nc_follow_reader(&w.nc, &test_parent(&w, 401, 300)->n, 0, &op);
    REQUIRE(b != NULL);
    CHECK_EQ(b->spos, 300);
    CHECK_EQ(w.ts.reads, 1);
    CHECK(nt_get_node(&w.nt, 101) == b);
    CHECK(node_pointer_node(&parent->n, 0) == b);      /* the first pointer gets it too */

    /* A canonical object serves every pointer. */
    node_set_canonical(b, true);
    struct node *d = nc_follow_reader(&w.nc, &test_parent(&w, 501, 300)->n, 0, &op);
    CHECK(d == b);
    CHECK_EQ(w.ts.reads, 1);
    /* the CLOCK bit, in the handle */
    struct obj *h = node_pointee(&parent->n, 0);
    CHECK(h != NULL && h->kind == OBJ_HANDLE && (h->flags & OBJ_REF) != 0);
    obj_collect(&w.cx);
    world_free(&w);
}

TEST(ncoll_no_cut_back_after_reconstruction) {
    struct world w;
    world_init(&w);
    const int64_t t10[] = { 10 }, t3[] = { 10, 20, 30 };
    stream_put(&w, 100, &test_key_node(&w, 101, 100, 1, t10)->n);
    stream_put(&w, 300, &test_key_node(&w, 101, 300, 3, t3)->n);
    struct lmap newById;
    lmap_init(&newById, &w.m);
    CHECK(lmap_put(&newById, 101, 300));
    nc_set_startup_section(&w.nc, &newById, 250, 25);
    nc_end_reconstruction(&w.nc);
    int32_t calls = 0;
    struct opdata op;
    test_op(&op, &calls);
    struct node *a = nc_follow_reader(&w.nc, &test_parent(&w, 401, 100)->n, 0, &op);
    REQUIRE(a != NULL);
    CHECK_EQ(a->spos, 300);
    CHECK_EQ(node_size(a), 6);      /* not cut back */
    obj_collect(&w.cx);
    world_free(&w);
}

/* The writer's follower makes what it reaches canonical (makeCanonical),
 * and a version cut back during the reconstruction is kept, canonical. */
TEST(ncoll_writer_follower) {
    struct world w;
    world_init(&w);
    const int64_t t3[] = { 10, 20, 30 };
    stream_put(&w, 300, &test_key_node(&w, 101, 300, 3, t3)->n);
    struct lmap newById;
    lmap_init(&newById, &w.m);
    CHECK(lmap_put(&newById, 101, 300));
    nc_set_startup_section(&w.nc, &newById, 250, 25);
    int32_t calls = 0;
    struct opdata op;
    test_op(&op, &calls);
    struct tnode *parent = test_parent(&w, 401, 101);  /* a vpos */
    struct node *a = nc_follow_writer(&w.nc, &parent->n, 0, &op);
    REQUIRE(a != NULL);
    CHECK_EQ(a->spos, 300);
    CHECK_EQ(node_size(a), 4);      /* cut back: the rerun's */
    CHECK(node_is_canonical(a));
    CHECK(nt_get_node(&w.nt, 101) == a);
    CHECK(node_pointer_node(&parent->n, 0) == a);
    CHECK_EQ(node_pointer_pos(&parent->n, 0), 300);
    /* again: from memory, no read */
    CHECK(nc_follow_writer(&w.nc, &parent->n, 0, &op) == a);
    CHECK_EQ(w.ts.reads, 1);
    obj_collect(&w.cx);
    world_free(&w);
}

TEST(ncoll_resolve_pointers) {
    struct world w;
    world_init(&w);
    const int64_t t10[] = { 10 }, t2[] = { 10, 20 };
    stream_put(&w, 100, &test_key_node(&w, 101, 100, 1, t10)->n);
    /* The child's canonical object, with a change since its version at 100. */
    struct knode *child = test_key_node(&w, 101, 100, 2, t2);
    node_set_canonical(&child->n, true);
    node_set_dirty(&child->n, true);
    reg(&w, &child->n);
    /* An internal node whose pointer is a stream pointer to the child's version at 100. */
    struct knode *parent = kn_new(&w.cx, false);
    CHECK(kn_add_to_end(&w.cx, parent, kl_create_time(10), NULL, -1));
    CHECK(kn_add_to_end(&w.cx, parent, key_klong("k"), NULL, 100));
    parent->n.id = 103;
    parent->n.spos = 200;
    node_set_canonical(&parent->n, true);
    hold(&w, &parent->n);
    struct err e;
    CHECK_EQ(nc_resolve_pointers(&w.nc, &parent->n, &e), ERR_OK);
    CHECK(node_pointer_node(&parent->n, 1) == &child->n);   /* memory pointer to the child */
    CHECK_EQ(w.ts.header_reads, 1);
    obj_collect(&w.cx);
    world_free(&w);
}

TEST(ncoll_resolve_pointers_unpinned) {
    struct world w;
    world_init(&w);
    const int64_t t10[] = { 10 }, t2[] = { 10, 20 };
    stream_put(&w, 100, &test_key_node(&w, 101, 100, 1, t10)->n);
    stream_put(&w, 150, &test_key_node(&w, 104, 150, 1, t10)->n);
    struct knode *snapshot = test_key_node(&w, 101, 200, 2, t2);
    reg(&w, &snapshot->n);
    struct knode *clean = test_key_node(&w, 104, 150, 1, t10);
    node_set_canonical(&clean->n, true);
    reg(&w, &clean->n);
    struct knode *parent = kn_new(&w.cx, false);
    CHECK(kn_add_to_end(&w.cx, parent, kl_create_time(10), NULL, -1));
    CHECK(kn_add_to_end(&w.cx, parent, key_klong("k"), NULL, 100));
    CHECK(kn_add_to_end(&w.cx, parent, key_klong("m"), NULL, 150));
    parent->n.id = 103;
    parent->n.spos = 300;
    node_set_canonical(&parent->n, true);
    hold(&w, &parent->n);
    struct err e;
    CHECK_EQ(nc_resolve_pointers(&w.nc, &parent->n, &e), ERR_OK);
    CHECK(node_pointer_node(&parent->n, 1) == NULL);   /* no snapshot taken */
    CHECK_EQ(node_pointer_pos(&parent->n, 1), 100);
    CHECK(node_pointer_node(&parent->n, 2) == NULL);   /* no clean canonical object taken */
    CHECK_EQ(node_pointer_pos(&parent->n, 2), 150);
    obj_collect(&w.cx);
    world_free(&w);
}

/* byPos: the node table's canonical objects by position. */
static void test_by_pos(struct world *w, struct lmap *byPos) {
    lmap_init(byPos, &w->m);
    for (int64_t i = 0; i < nt_slots(&w->nt); i++) {
        struct handle *h = nt_slot(&w->nt, i);
        if (h != NULL && h->obj != NULL && node_is_canonical(h->obj)) {
            CHECK(lmap_put(byPos, h->obj->spos, (int64_t) (intptr_t) h));
        }
    }
}

TEST(ncoll_link_to_canonical) {
    struct world w;
    world_init(&w);
    const int64_t t10[] = { 10 }, t2[] = { 10, 20 };
    stream_put(&w, 100, &test_key_node(&w, 101, 100, 1, t10)->n);
    stream_put(&w, 150, &test_key_node(&w, 104, 150, 1, t10)->n);
    struct knode *canonical = test_key_node(&w, 101, 200, 2, t2);
    node_set_canonical(&canonical->n, true);
    reg(&w, &canonical->n);
    struct lmap ids, byPos;
    lmap_init(&ids, &w.m);
    CHECK(lmap_put(&ids, 200, 101));
    CHECK(lmap_put(&ids, 100, 101));
    const int64_t ptrs[] = { 100, 150 };
    struct knode *parent = test_node_of_d(&w, 103, 2, ptrs);
    test_by_pos(&w, &byPos);
    struct err e;
    CHECK_EQ(nc_link_to_canonical(&w.nc, &parent->n, &ids, &byPos, &e), ERR_OK);
    CHECK(node_pointer_node(&parent->n, 1) == &canonical->n);
    CHECK(node_pointer_node(&parent->n, 2) == NULL);   /* no canonical object */
    CHECK_EQ(node_pointer_pos(&parent->n, 2), 150);
    CHECK_EQ(w.ts.header_reads + w.ts.reads, 0);       /* no read */
    lmap_free(&ids);
    lmap_free(&byPos);
    world_free(&w);
}

TEST(ncoll_link_to_canonical_by_position) {
    struct world w;
    world_init(&w);
    const int64_t t10[] = { 10 }, t30[] = { 30 };
    stream_put(&w, 150, &test_key_node(&w, 104, 150, 1, t10)->n);   /* for the check */
    struct knode *loaded = test_key_node(&w, 104, 150, 1, t10);
    node_set_canonical(&loaded->n, true);
    reg(&w, &loaded->n);
    struct knode *created = test_key_node(&w, 1001, 1001, 1, t30);
    node_set_canonical(&created->n, true);
    reg(&w, &created->n);
    const int64_t ptrs[] = { 150, 1001 };
    struct knode *parent = test_node_of_d(&w, 103, 2, ptrs);
    struct lmap ids, byPos;
    lmap_init(&ids, &w.m);
    test_by_pos(&w, &byPos);
    w.nc.check_link = true;
    struct err e;
    CHECK_EQ(nc_link_to_canonical(&w.nc, &parent->n, &ids, &byPos, &e), ERR_OK);
    CHECK(node_pointer_node(&parent->n, 1) == &loaded->n);
    CHECK(node_pointer_node(&parent->n, 2) == &created->n);
    lmap_free(&ids);
    lmap_free(&byPos);
    world_free(&w);
}

TEST(ncoll_link_to_canonical_top_node) {
    struct world w;
    world_init(&w);
    const int64_t t10[] = { 10 }, t2[] = { 10, 20 };
    stream_put(&w, 100, &test_key_node(&w, 101, 100, 1, t10)->n);
    struct knode *canonical = test_key_node(&w, 101, 200, 2, t2);
    node_set_canonical(&canonical->n, true);
    reg(&w, &canonical->n);
    struct lmap ids, byPos;
    lmap_init(&ids, &w.m);
    CHECK(lmap_put(&ids, 200, 101));
    struct tnode *top = test_parent(&w, 301, 100);
    test_by_pos(&w, &byPos);
    struct err e;
    CHECK_EQ(nc_link_to_canonical(&w.nc, &top->n, &ids, &byPos, &e), ERR_OK);
    CHECK(node_pointer_node(&top->n, 0) == &canonical->n);     /* by node id */
    CHECK_EQ(w.ts.header_reads, 1);
    lmap_free(&ids);
    lmap_free(&byPos);
    world_free(&w);
}

TEST(ncoll_link_to_canonical_check) {
    struct world w;
    world_init(&w);
    const int64_t t10[] = { 10 }, t2[] = { 10, 20 };
    stream_put(&w, 100, &test_key_node(&w, 101, 100, 1, t10)->n);
    struct knode *canonical = test_key_node(&w, 101, 200, 2, t2);
    node_set_canonical(&canonical->n, true);
    reg(&w, &canonical->n);
    struct lmap ids, byPos;
    lmap_init(&ids, &w.m);
    CHECK(lmap_put(&ids, 200, 101));
    const int64_t ptrs[] = { 100 };
    struct knode *parent = test_node_of_d(&w, 103, 1, ptrs);
    test_by_pos(&w, &byPos);
    w.nc.check_link = true;
    struct err e;
    CHECK_EQ(nc_link_to_canonical(&w.nc, &parent->n, &ids, &byPos, &e), ERR_FORMAT);
    CHECK(strcmp(e.java, "AssertionError") == 0);      /* the check found the missing link */
    lmap_free(&ids);
    lmap_free(&byPos);
    world_free(&w);
}

/* Cache3's rules: register keeps a canonical object, takes a better one;
 * install takes a newer version, never over a canonical one; makeCanonical;
 * dropIfEmpty; liveOrNewHandle. */
TEST(ntable_rules) {
    struct world w;
    world_init(&w);
    const int64_t t10[] = { 10 }, t2[] = { 10, 20 };
    struct knode *v100 = test_key_node(&w, 7, 100, 1, t10);
    struct knode *v200 = test_key_node(&w, 7, 200, 2, t2);
    struct knode *v50 = test_key_node(&w, 7, 50, 1, t10);
    CHECK(reg(&w, &v100->n) == &v100->n);
    struct handle *h = nt_live_handle(&w.nt, 7);
    REQUIRE(h != NULL);
    CHECK(v100->handle == h);
    CHECK(reg(&w, &v50->n) == &v100->n);        /* an older version: kept out */
    CHECK(nt_install(&w.nt, h, &v200->n) == &v200->n);  /* a newer one taken */
    CHECK(v100->handle == NULL && (v100->n.o.flags & OBJ_LEFT) != 0);
    node_set_canonical(&v100->n, true);
    CHECK(nt_make_canonical(&w.nt, h, &v100->n) == &v200->n);  /* the newer one */
    CHECK(node_is_canonical(&v200->n));
    node_set_canonical(&v100->n, false);
    CHECK(nt_install(&w.nt, h, &v100->n) == &v200->n);  /* never over a canonical one */
    /* an empty handle is dropped; one with an object is not */
    struct handle *h2 = nt_live_or_new_handle(&w.nt, 9);
    REQUIRE(h2 != NULL);
    CHECK(nt_live_or_new_handle(&w.nt, 9) == h2);
    CHECK_EQ(nt_size(&w.nt), 2);
    nt_drop_if_empty(&w.nt, h2);
    CHECK(hd_is_dead(h2));
    CHECK(nt_live_handle(&w.nt, 9) == NULL);
    nt_drop_if_empty(&w.nt, h);
    CHECK(nt_live_handle(&w.nt, 7) == h);
    CHECK_EQ(nt_size(&w.nt), 1);
    obj_collect(&w.cx);
    world_free(&w);
}

/* lmap: puts, gets, removes against a plain array, many keys. */
TEST(lmap_model) {
    struct mem m;
    mem_init(&m);
    struct lmap map;
    lmap_init(&map, &m);
    enum { N = 3000 };
    static int64_t vals[N];
    static bool in[N];
    memset(in, 0, sizeof in);
    uint64_t x = 88172645463325252u;
    for (int32_t step = 0; step < 40000; step++) {
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        int32_t k = (int32_t) (x % N);
        int64_t key = (int64_t) k * 1000003 - 7;
        int op = (int) ((x >> 20) % 3);
        if (op == 0) {
            CHECK(lmap_put(&map, key, step));
            vals[k] = step;
            in[k] = true;
        } else if (op == 1) {
            CHECK_EQ(lmap_remove(&map, key), in[k]);
            in[k] = false;
        } else {
            int64_t v = -1;
            CHECK_EQ(lmap_get(&map, key, &v), in[k]);
            if (in[k]) {
                CHECK_EQ(v, vals[k]);
            }
        }
    }
    int64_t count = 0;
    for (int32_t k = 0; k < N; k++) {
        count += in[k] ? 1 : 0;
    }
    CHECK_EQ(map.size, count);
    lmap_free(&map);
    CHECK_MEM_ZERO(&m);
}

const struct test ncoll_tests[] = {
    TEST_ENTRY(ncoll_follow_newer_version),
    TEST_ENTRY(ncoll_follow_rule_r),
    TEST_ENTRY(ncoll_loader_takes_the_handles_object),
    TEST_ENTRY(ncoll_no_cut_back_after_reconstruction),
    TEST_ENTRY(ncoll_writer_follower),
    TEST_ENTRY(ncoll_resolve_pointers),
    TEST_ENTRY(ncoll_resolve_pointers_unpinned),
    TEST_ENTRY(ncoll_link_to_canonical),
    TEST_ENTRY(ncoll_link_to_canonical_by_position),
    TEST_ENTRY(ncoll_link_to_canonical_top_node),
    TEST_ENTRY(ncoll_link_to_canonical_check),
    TEST_ENTRY(ntable_rules),
    TEST_ENTRY(lmap_model),
    TEST_END
};
