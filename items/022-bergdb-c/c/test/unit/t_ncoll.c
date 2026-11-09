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
#include "bytes.h"
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
#include "vnode.h"

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
    struct node *out = NULL;
    struct err e;
    CHECK_EQ(nt_register(&w->nt, n, &out, &e), ERR_OK);
    return out;
}

/* nt_install's result, NULL if refused. */
static struct node *install(struct world *w, struct handle *h, struct node *n) {
    struct node *out = NULL;
    struct err e;
    return nt_install(&w->nt, h, n, &out, &e) == ERR_OK ? out : NULL;
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
    CHECK(strcmp(e.text, "rule 4 by position is not rule 4 by node id (bergdb 005-57): "
            "pointer 1 of node 103 names 100; by position no canonical object, by node id "
            "node 101's, at 200") == 0);               /* Java's text (before 021-11, C's own) */
    lmap_free(&ids);
    lmap_free(&byPos);
    world_free(&w);
}

/* A top node of the test stream: id, at pos, its root pointer a stream pointer. */
static struct tnode *test_top_node(struct world *w, int64_t id, int64_t pos) {
    struct tnode *t = tn_new(&w->cx, 0, NULL, 5000, 1, pos);
    t->n.id = id;
    return t;
}

/* A follow of pointer i of 'from' by the readers' follower: refused with a
 * StreamFormatException whose text is 'text'. */
static void follow_refused(struct world *w, struct node *from, int32_t i, const char *text) {
    int32_t calls = 0;
    struct opdata op;
    test_op(&op, &calls);
    err_clear(&w->nc.err);
    struct node *got = nc_follow_reader(&w->nc, from, i, &op);
    CHECK(got == NULL);
    bool same = strcmp(w->nc.err.java, "StreamFormatException") == 0
            && strcmp(w->nc.err.text, text) == 0;
    CHECK(same);
    if (!same) {
        printf("    got %s: %s: %s\n", got == NULL ? "none" : "a node", w->nc.err.java,
                w->nc.err.text);
    }
}

/* NodeCollection.checkPointeeType and Cache3.checkType (bergdb 019-32, as Java's since
 * release 2026.3): a pointer that names a node of another type than it points to is refused
 * with a StreamFormatException, where C read the node as the type it expected (Java threw a
 * ClassCastException): a top node's root pointer naming a top node; a non-leaf key node's
 * pointer naming a value; a segment leaf's value pointer naming a key node; a handle whose
 * object is of another type (a damaged node's id names another node). And a version read
 * into a handle whose object is of another type, not usable, is not installed. */
TEST(ncoll_pointee_type) {
    struct world w;
    world_init(&w);
    const int64_t t10[] = { 10 };

    /* A top node's root pointer: a key node expected, a top node there. */
    stream_put(&w, 100, &test_top_node(&w, 101, 100)->n);
    follow_refused(&w, &test_parent(&w, 301, 100)->n, 0,
            "Pointer 0 of node 301 names a node of type 10 at 100, not 20.");

    /* A non-leaf key node's pointer: a key node expected, a value there. */
    struct vnode *v = vn_new_stored(&w.cx, (const uint8_t *) "v", 1, 200, 201, 160);
    REQUIRE(v != NULL);
    stream_put(&w, 200, &v->n);
    const int64_t p200[] = { 200 };
    follow_refused(&w, &test_node_of_d(&w, 103, 1, p200)->n, 1,
            "Pointer 1 of node 103 names a node of type 30 at 200, not 20.");

    /* A segment leaf's value pointer (its key "k10" is shorter than 7): a value expected,
     * a key node there (the leaf's pointer is 1000 + 8 * 10). */
    stream_put(&w, 1080, &test_key_node(&w, 105, 1080, 1, t10)->n);
    struct knode *leaf = test_key_node(&w, 104, 300, 1, t10);
    hold(&w, &leaf->n);
    follow_refused(&w, &leaf->n, 1,
            "Pointer 1 of node 104 names a node of type 20 at 1080, not 30.");

    /* The live handle of the id at the pointer's position holds a canonical top node: a
     * key node expected. */
    struct tnode *top = test_top_node(&w, 107, 50);
    node_set_canonical(&top->n, true);
    reg(&w, &top->n);
    stream_put(&w, 400, &test_key_node(&w, 107, 400, 1, t10)->n);
    const int64_t p400[] = { 400 };
    follow_refused(&w, &test_node_of_d(&w, 108, 1, p400)->n, 1,
            "Pointer 1 of node 108 names a node of type 10 at 400, not 20.");

    /* The handle holds a top node that is not usable (not canonical, older): the key node
     * read is of the type the pointer names, but not installed (Cache3.install). */
    struct tnode *old = test_top_node(&w, 109, 50);
    reg(&w, &old->n);
    stream_put(&w, 600, &test_key_node(&w, 109, 600, 1, t10)->n);
    const int64_t p600[] = { 600 };
    follow_refused(&w, &test_node_of_d(&w, 110, 1, p600)->n, 1,
            "Two nodes with the id 109: of type 10 at 50, and of type 20 at 600.");
    CHECK(nt_get_node(&w.nt, 109) == &old->n);

    obj_collect(&w.cx);
    world_free(&w);
}

/* A link by node id refused, with Java's StreamFormatException (CHECK'd text); the
 * pointer left without a handle. */
static void link_refused(struct world *w, struct node *node, const struct lmap *ids,
        const struct lmap *byPos, int32_t i, const char *text) {
    struct err e;
    err_clear(&e);
    CHECK_EQ(nc_link_to_canonical(&w->nc, node, ids, byPos, &e), ERR_FORMAT);
    bool same = strcmp(e.java, "StreamFormatException") == 0 && strcmp(e.text, text) == 0;
    CHECK(same);
    if (!same) {
        printf("    got %s: %s\n", e.java, e.text);
    }
    CHECK(node_pointee(node, i) == NULL);
}

/* NodeCollection.linkToCanonical (bergdb 021-11, as Java's since release 2026.4): a pointer
 * that the start links by node id is checked for its node's type, as a follow checks it
 * (019-32). A damaged pointer (its node's checksum right) that named a version of a node of
 * another type got that node's handle (C refused it later, where the Dag cast the node:
 * t_dag.c, dag_wrong_pointee_type; Java threw a ClassCastException), or, under the check by
 * node id (Java's -ea), gave 005-57's AssertionError. The three ways of
 * CorruptStreamTester.testFound021_11, on nodes: (1) a key node's pointer whose position
 * posToId gives to a top node; (2) a top node's skip pointer in neither map, by the node's
 * header, to a key node; (3) a key node's pointer in neither map, not linked, whose header
 * names a top node: the check refuses it, and without the check nothing is linked. On
 * streams: t_sdb.c, sdb_found_021_11. */
TEST(ncoll_link_to_canonical_another_type) {
    const int64_t t10[] = { 10 }, t2[] = { 10, 20 };
    struct world w;
    struct lmap ids, byPos;

    /* (1) By posToId: top node 131's version at 700. */
    world_init(&w);
    stream_put(&w, 700, &test_top_node(&w, 131, 700)->n);     /* for the check */
    struct tnode *top = test_top_node(&w, 131, 700);
    node_set_canonical(&top->n, true);
    reg(&w, &top->n);
    lmap_init(&ids, &w.m);
    CHECK(lmap_put(&ids, 700, 131));
    const int64_t p700[] = { 700 };
    struct knode *parent = test_node_of_d(&w, 132, 1, p700);
    test_by_pos(&w, &byPos);
    link_refused(&w, &parent->n, &ids, &byPos, 1,
            "Pointer 1 of node 132 names a node of type 10 at 700, not 20.");
    w.nc.check_link = true;     /* the check's own read names the same node */
    link_refused(&w, &parent->n, &ids, &byPos, 1,
            "Pointer 1 of node 132 names a node of type 10 at 700, not 20.");
    lmap_free(&ids);
    lmap_free(&byPos);
    world_free(&w);

    /* (2) A top node's skip pointer 0 (pointer 1) by the header at 800: key node 133, whose
     * canonical object is at 900. The root pointer is null, skipped. */
    world_init(&w);
    stream_put(&w, 800, &test_key_node(&w, 133, 800, 1, t10)->n);
    struct knode *k133 = test_key_node(&w, 133, 900, 2, t2);
    node_set_canonical(&k133->n, true);
    reg(&w, &k133->n);
    uint8_t skips[16];
    bytes_put_long_le(800, skips);
    bytes_put_long_le(5, skips + 8);
    struct tnode *t135 = tn_new_stored(&w.cx, 1, SPOS_NULL, 10, 1000, 135, 1, skips);
    REQUIRE(t135 != NULL);
    hold(&w, &t135->n);
    lmap_init(&ids, &w.m);
    test_by_pos(&w, &byPos);
    link_refused(&w, &t135->n, &ids, &byPos, 1,
            "Pointer 1 of node 135 names a node of type 20 at 800, not 10.");
    CHECK_EQ(w.ts.header_reads, 1);
    lmap_free(&ids);
    lmap_free(&byPos);
    world_free(&w);

    /* (3) A key node's pointer to 750, an older version of top node 131 (canonical at 700):
     * in neither map, so rule 4 by position links nothing. */
    world_init(&w);
    stream_put(&w, 750, &test_top_node(&w, 131, 750)->n);
    top = test_top_node(&w, 131, 700);
    node_set_canonical(&top->n, true);
    reg(&w, &top->n);
    lmap_init(&ids, &w.m);
    const int64_t p750[] = { 750 };
    parent = test_node_of_d(&w, 134, 1, p750);
    test_by_pos(&w, &byPos);
    struct err e;
    CHECK_EQ(nc_link_to_canonical(&w.nc, &parent->n, &ids, &byPos, &e), ERR_OK);
    CHECK(node_pointee(&parent->n, 1) == NULL);         /* without the check: not linked */
    w.nc.check_link = true;
    link_refused(&w, &parent->n, &ids, &byPos, 1,
            "Pointer 1 of node 134 names a node of type 10 at 750, not 20.");
    lmap_free(&ids);
    lmap_free(&byPos);
    world_free(&w);
}

/* NodeCollection.testLinkToCanonicalChecksTheType (bergdb 020-23, V2-1, as Java's since
 * release 2026.4): rule 4 at startup without the check by node id, as with Java's assertions
 * off (DbStarter.linkD; C's db_open, and bergdb-dump without -check): a key node's pointer
 * whose position the section's ids give as a version of a top node with a canonical object
 * is refused, and gets no handle (021-11). With the check, the check refuses it first, so a
 * test with the check does not pin nc_link_to_canonical's own check of the type; case (1) of
 * ncoll_link_to_canonical_another_type pins it too, on other nodes. */
TEST(ncoll_link_to_canonical_checks_the_type) {
    struct world w;
    world_init(&w);
    stream_put(&w, 100, &test_top_node(&w, 301, 100)->n);      /* a version of top node 301 */
    struct tnode *top = test_top_node(&w, 301, 50);             /* its canonical object */
    node_set_canonical(&top->n, true);
    reg(&w, &top->n);
    struct lmap ids, byPos;
    lmap_init(&ids, &w.m);
    CHECK(lmap_put(&ids, 100, 301));                            /* the section's id of 100 */
    const int64_t p100[] = { 100 };
    struct knode *parent = test_node_of_d(&w, 103, 1, p100);
    test_by_pos(&w, &byPos);
    CHECK(!w.nc.check_link);
    link_refused(&w, &parent->n, &ids, &byPos, 1,
            "Pointer 1 of node 103 names a node of type 10 at 100, not 20.");
    lmap_free(&ids);
    lmap_free(&byPos);
    world_free(&w);
}

/* NodeCollection.testResolvePointersChecksTheType (bergdb 021-11, as Java's since release
 * 2026.4): before a node is written, a stream pointer that names, by damage (the node's
 * checksum right), a version of a pinned node of another type is refused, as a follow
 * refuses it (019-32). Before, it got that node's handle: here a key node's pointer got a
 * top node's. */
TEST(ncoll_resolve_pointers_checks_the_type) {
    struct world w;
    world_init(&w);
    stream_put(&w, 100, &test_top_node(&w, 301, 100)->n);      /* a version of top node 301 */
    struct tnode *top = test_top_node(&w, 301, 50);             /* its canonical object, dirty */
    node_set_canonical(&top->n, true);
    node_set_dirty(&top->n, true);
    reg(&w, &top->n);
    const int64_t p100[] = { 100 };
    struct knode *parent = test_node_of_d(&w, 103, 1, p100);
    struct err e;
    err_clear(&e);
    CHECK_EQ(nc_resolve_pointers(&w.nc, &parent->n, &e), ERR_FORMAT);
    CHECK(strcmp(e.java, "StreamFormatException") == 0);
    CHECK(strcmp(e.text, "Pointer 1 of node 103 names a node of type 10 at 100, not 20.") == 0);
    CHECK(node_pointee(&parent->n, 1) == NULL);         /* no handle */
    world_free(&w);
}

/* NodeCollection.testWriterKeepsTheNodeWhateverItsPolicy (bergdb 019-46, as Java's since
 * release 2026.4): the writer keeps every index node it follows to in the node's handle,
 * whatever its op's cache policy, so makeCanonical (step 6) never fills an empty handle that
 * the follow's drop took from the table. C's writer caches every index node (dag.c's
 * cache_all_except_large), so nothing changes for it; with a policy that cached none, the
 * follow dropped its own empty handle and made the version canonical in that dead handle,
 * out of the table. */
static bool cache_nothing(void *ctx, const struct node *node) {
    (void) ctx;
    (void) node;
    return false;
}

TEST(ncoll_writer_keeps_the_node_whatever_its_policy) {
    struct world w;
    world_init(&w);
    const int64_t t10[] = { 10 };
    stream_put(&w, 100, &test_key_node(&w, 101, 100, 1, t10)->n);
    struct tnode *parent = test_parent(&w, 301, 100);
    int32_t calls = 0;
    struct opdata op;
    test_op(&op, &calls);
    op.cache_policy.should_cache = cache_nothing;
    struct node *o = nc_follow_writer(&w.nc, &parent->n, 0, &op);
    REQUIRE(o != NULL);
    CHECK_EQ(o->id, 101);                               /* the writer followed to the node */
    CHECK(node_is_canonical(o));
    struct handle *h = nt_live_handle(&w.nt, 101);
    CHECK(h != NULL && !hd_is_dead(h));                 /* a live handle in the table */
    CHECK(h != NULL && h->obj == o);                    /* holding the canonical object */
    CHECK(nt_get_node(&w.nt, 101) == o);
    CHECK(h != NULL && node_pointee(&parent->n, 0) == &h->o);  /* the parent's pointer */
    obj_collect(&w.cx);
    world_free(&w);
}

/* Checks, not asserts (bergdb 019-32, as Java's since release 2026.3): a pointer to an index
 * node that is negative, and a value pointer that is negative or a vpos, are refused with a
 * StreamFormatException; before, C aborted on an assert. */
TEST(ncoll_bad_pointers) {
    struct world w;
    world_init(&w);
    follow_refused(&w, &test_parent(&w, 311, -8)->n, 0, "Bad pointer -8, index 0 of node 311.");
    const int64_t bad[2] = { -8, 1001 };
    for (int i = 0; i < 2; i++) {
        struct knode *leaf = kn_new(&w.cx, true);
        CHECK(kn_add_to_end(&w.cx, leaf, kl_create_time(10), NULL, -1));
        CHECK(kn_add_to_end(&w.cx, leaf, key_klong("k"), NULL, bad[i]));
        leaf->n.id = 120 + i;
        leaf->n.spos = 300;
        hold(&w, &leaf->n);
        char want[100];
        snprintf(want, sizeof want, "Bad value pointer %lld, index 1 of node %d.",
                (long long) bad[i], 120 + i);
        follow_refused(&w, &leaf->n, 1, want);
    }
    obj_collect(&w.cx);
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
    CHECK(install(&w, h, &v200->n) == &v200->n);       /* a newer one taken */
    CHECK(v100->handle == NULL && (v100->n.o.flags & OBJ_LEFT) != 0);
    node_set_canonical(&v100->n, true);
    CHECK(nt_make_canonical(&w.nt, h, &v100->n) == &v200->n);  /* the newer one */
    CHECK(node_is_canonical(&v200->n));
    node_set_canonical(&v100->n, false);
    CHECK(install(&w, h, &v100->n) == &v200->n);       /* never over a canonical one */
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
    /* One id, one type (Cache3.checkType, bergdb 019-32, as Java's since release 2026.3):
     * a top node registered or installed where a key node is, refused, the key node kept;
     * and the reverse. */
    struct tnode *t7 = tn_new(&w.cx, 0, NULL, 5000, 1, 300);
    t7->n.id = 7;
    node_set_canonical(&t7->n, true);
    struct node *out = NULL;
    struct err e;
    CHECK_EQ(nt_register(&w.nt, &t7->n, &out, &e), ERR_FORMAT);
    CHECK(strcmp(e.java, "StreamFormatException") == 0);
    CHECK(strcmp(e.text, "Two nodes with the id 7: of type 20 at 200, and of type 10 at 300.")
            == 0);
    CHECK_EQ(nt_install(&w.nt, h, &t7->n, &out, &e), ERR_FORMAT);
    CHECK(strcmp(e.text, "Two nodes with the id 7: of type 20 at 200, and of type 10 at 300.")
            == 0);
    CHECK(nt_get_node(&w.nt, 7) == &v200->n);
    t7->n.id = 11;
    CHECK(reg(&w, &t7->n) == &t7->n);
    struct knode *k11 = test_key_node(&w, 11, 400, 1, t10);
    CHECK_EQ(nt_register(&w.nt, &k11->n, &out, &e), ERR_FORMAT);
    CHECK(strcmp(e.text, "Two nodes with the id 11: of type 10 at 300, and of type 20 at 400.")
            == 0);
    CHECK(nt_get_node(&w.nt, 11) == &t7->n);
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
    TEST_ENTRY(ncoll_pointee_type),
    TEST_ENTRY(ncoll_bad_pointers),
    TEST_ENTRY(ncoll_link_to_canonical_another_type),
    TEST_ENTRY(ncoll_link_to_canonical_checks_the_type),
    TEST_ENTRY(ncoll_resolve_pointers_checks_the_type),
    TEST_ENTRY(ncoll_writer_keeps_the_node_whatever_its_policy),
    TEST_ENTRY(ntable_rules),
    TEST_ENTRY(lmap_model),
    TEST_END
};
