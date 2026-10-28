/* Unit tests of tnode, topds and the top node's writer (bergdb 012-07):
 * Java's @Nano tests of TopNode, TopTester's and StoredTopNode's that C has
 * the behaviour of, ported; the parser's own checks are 012-06's (snode).
 * A test-local reader of a written top node's fields stands in for the
 * parser and makes the object with tn_new_stored, as the parse does. */
#include <assert.h>
#include "bytes.h"
#include "jsem.h"
#include "knode.h"
#include "nfix.h"
#include "nwrite.h"
#include "opdata.h"
#include "spos.h"
#include "test.h"
#include "tnode.h"
#include "topds.h"

TEST(tnode_height1) {
    CHECK_EQ(tn_height(0), 0);
    CHECK_EQ(tn_height(1), 1);
    CHECK_EQ(tn_height(2), 2);
    CHECK_EQ(tn_height(3), 2);
    CHECK_EQ(tn_height(4), 3);
    CHECK_EQ(tn_height(5), 3);
    CHECK_EQ(tn_height(6), 3);
    CHECK_EQ(tn_height(7), 3);
    CHECK_EQ(tn_height(8), 4);
    CHECK_EQ(tn_height(9), 4);
    CHECK_EQ(tn_height(10), 4);
}

TEST(tnode_height2) {
    CHECK_EQ(tn_height(1024 * 1024 * 1024 / 2), 30);
    CHECK_EQ(tn_height(INT64_C(1) << 30), 31);
    CHECK_EQ(tn_height(INT64_C(1) << 32), 33);
    CHECK_EQ(tn_height(INT64_C(1) << 47), 48);
    CHECK_EQ(tn_height(TN_MAX_TOP_NODE_ID_VALUE), 48);
    /* Java's refusal above the bound (IllegalStateException) is an assert
     * in C: the ordinals are checked before (005-02). */
}

/* TopTester's DUMMY_POINTER_FOLLOWER: memory pointers only. */
static struct node *mem_follow(void *ctx, struct node *predecessor, int32_t index,
        struct opdata *op) {
    (void) ctx;
    struct node *result = node_pointer_node(predecessor, index);
    assert(result != NULL && "This NodeFollower does not support stream pointers.");
    if (!op->pointer_listener.pointer_followed(op->pointer_listener.ctx, predecessor, index,
            result, PTR_TYPE_MEMORY)) {
        return NULL;
    }
    return result;
}

/* TopTester.findRoot */
static struct knode *find_root(struct topds *ds, int64_t time) {
    struct opdata gd;
    op_init(&gd);
    gd.pointer_follower.follow = mem_follow;
    gd.pointer_listener = OP_DO_NOTHING_POINTER_LISTENER;
    struct knode *root = NULL;
    bool ok = tds_find_root(ds, time, &gd, &root);
    CHECK(ok);
    return root;
}

/* TopTester.createTestData: ds1 to ds4, with roots n1 to n4 at 5, 10, 20
 * and 30. */
struct top_tester {
    struct knode *n1, *n2, *n3, *n4;
    struct topds ds1, ds2, ds3, ds4;
};

static void create_test_data(struct nfix *f, struct top_tester *t) {
    const struct op_pointer_created_listener *N1 = &OP_DO_NOTHING_POINTER_CREATED_LISTENER;
    const struct op_node_change_listener *N2 = &OP_DO_NOTHING_NODE_CHANGE_LISTENER;
    struct obj_ctx *cx = &f->cx;
    int64_t firstTime = 5;

    t->n1 = kn_new(cx, true);
    t->n1->n.spos = 100;
    CHECK(tds_create_from_first_root(cx, &t->ds1, firstTime, t->n1, 0, N1));

    t->n2 = kn_new(cx, true);
    t->n2->n.spos = 200;
    CHECK(tds_create_from_first_root(cx, &t->ds2, firstTime, t->n1, 0, N1));
    CHECK(tds_new_super_root(cx, &t->ds2, 10, t->n2, 0, N1, N2));

    t->n3 = kn_new(cx, true);
    t->n3->n.spos = 300;
    CHECK(tds_create_from_first_root(cx, &t->ds3, firstTime, t->n1, 0, N1));
    CHECK(tds_new_super_root(cx, &t->ds3, 10, t->n2, 0, N1, N2));
    CHECK(tds_new_super_root(cx, &t->ds3, 20, t->n3, 0, N1, N2));

    t->n4 = kn_new(cx, true);
    t->n4->n.spos = 400;
    CHECK(tds_create_from_first_root(cx, &t->ds4, firstTime, t->n1, 0, N1));
    CHECK(tds_new_super_root(cx, &t->ds4, 10, t->n2, 0, N1, N2));
    CHECK(tds_new_super_root(cx, &t->ds4, 20, t->n3, 0, N1, N2));
    CHECK(tds_new_super_root(cx, &t->ds4, 30, t->n4, 0, N1, N2));
}

static void free_test_data(struct nfix *f, struct top_tester *t) {
    struct obj *roots[4] = {&t->ds1.super_root->n.o, &t->ds2.super_root->n.o,
            &t->ds3.super_root->n.o, &t->ds4.super_root->n.o};
    NFIX_RECOUNT(f, roots, 4);
    tds_free(&f->cx, &t->ds1);
    tds_free(&f->cx, &t->ds2);
    tds_free(&f->cx, &t->ds3);
    tds_free(&f->cx, &t->ds4);
}

TEST(tnode_top_tester1) {
    struct nfix f;
    nfix_init(&f);
    struct top_tester t;
    create_test_data(&f, &t);
    obj_collect(&f.cx);         /* the super roots hold the rest */
    CHECK_EQ(f.cx.live[OBJ_TOP], 10);
    free_test_data(&f, &t);
    NFIX_END(&f);
}

TEST(tnode_before_first) {
    struct nfix f;
    nfix_init(&f);
    struct top_tester t;
    create_test_data(&f, &t);
    CHECK(find_root(&t.ds1, 1) == NULL);
    CHECK(find_root(&t.ds2, 1) == NULL);
    CHECK(find_root(&t.ds3, 1) == NULL);
    free_test_data(&f, &t);
    NFIX_END(&f);
}

TEST(tnode_find_first_node) {
    struct nfix f;
    nfix_init(&f);
    struct top_tester t;
    create_test_data(&f, &t);
    CHECK(find_root(&t.ds1, 7) == t.n1);
    CHECK(find_root(&t.ds2, 7) == t.n1);
    CHECK(find_root(&t.ds3, 7) == t.n1);
    free_test_data(&f, &t);
    NFIX_END(&f);
}

TEST(tnode_ds3) {
    struct nfix f;
    nfix_init(&f);
    struct top_tester t;
    create_test_data(&f, &t);
    CHECK(find_root(&t.ds3, 99) == t.n3);
    CHECK(find_root(&t.ds3, 10) == t.n2);
    CHECK(find_root(&t.ds3, 19) == t.n2);
    CHECK(find_root(&t.ds3, 20) == t.n3);
    free_test_data(&f, &t);
    NFIX_END(&f);
}

TEST(tnode_ds4) {
    struct nfix f;
    nfix_init(&f);
    struct top_tester t;
    create_test_data(&f, &t);
    CHECK(find_root(&t.ds4, 99) == t.n4);
    CHECK(find_root(&t.ds4, 10) == t.n2);
    CHECK(find_root(&t.ds4, 19) == t.n2);
    CHECK(find_root(&t.ds4, 29) == t.n3);
    CHECK(find_root(&t.ds4, 30) == t.n4);
    free_test_data(&f, &t);
    NFIX_END(&f);
}

/* TopTester.testNewSuperRootFromStreamPointers: a new super root gets the
 * same skip pointers whether the old super root's are memory pointers or
 * stream pointers, as after a restart. */
TEST(tnode_new_super_root_from_stream_pointers) {
    struct nfix f;
    nfix_init(&f);
    struct obj_ctx *cx = &f.cx;
    const struct op_pointer_created_listener *N1 = &OP_DO_NOTHING_POINTER_CREATED_LISTENER;
    const struct op_node_change_listener *N2 = &OP_DO_NOTHING_NODE_CHANGE_LISTENER;

    struct topds memDs;
    CHECK(tds_create_from_first_root(cx, &memDs, 10, kn_new(cx, true), 0, N1));
    tds_get_super_root(&memDs)->n.spos = 100;
    CHECK(tds_new_super_root(cx, &memDs, 20, kn_new(cx, true), 0, N1, N2));
    tds_get_super_root(&memDs)->n.spos = 200;
    CHECK(tds_new_super_root(cx, &memDs, 30, kn_new(cx, true), 0, N1, N2));
    struct tnode *top2 = tds_get_super_root(&memDs);
    top2->n.spos = 300;

    struct tnode *streamTop2 = tn_new(cx, top2->top_node_id, (struct knode *) top2->root_pointer->obj,
            top2->root_pointer_pos, top2->root_time, top2->n.spos);
    REQUIRE(streamTop2 != NULL);
    for (int32_t i = 0; i < top2->pointers_length; i++) {
        struct handle *p = top2->skip[i].p;
        tn_set_pointer(cx, streamTop2, i + 1, NULL, p == NULL ? top2->skip[i].pos : p->obj->spos);
        streamTop2->skip[i].time = top2->skip[i].time;
    }
    struct topds streamDs;
    tds_init(&streamDs, streamTop2);

    CHECK(tds_new_super_root(cx, &memDs, 40, kn_new(cx, true), 0, N1, N2));
    CHECK(tds_new_super_root(cx, &streamDs, 40, kn_new(cx, true), 0, N1, N2));
    struct tnode *a = tds_get_super_root(&memDs);
    struct tnode *b = tds_get_super_root(&streamDs);

    CHECK_EQ(a->pointers_length, b->pointers_length);
    for (int32_t i = 0; i < a->pointers_length; i++) {
        CHECK_EQ(tn_get_serialized_ref(a, i + 1), tn_get_serialized_ref(b, i + 1));
        CHECK_EQ(a->skip[i].time, b->skip[i].time);
    }
    struct obj *roots[2] = {&a->n.o, &b->n.o};
    NFIX_RECOUNT(&f, roots, 2);
    tds_free(cx, &memDs);
    tds_free(cx, &streamDs);
    NFIX_END(&f);
}

/* Writes a top node and makes it again from its bytes, as the parse does:
 * StoredTopNode's writeAndRead. */
static struct tnode *write_and_read(struct nfix *f, const struct tnode *node, int64_t spos) {
    int64_t longs[(40 + 16 * 48) / 8];
    int32_t n = nw_top_to_longs(node, longs, 0);
    CHECK_EQ(n * 8, nw_top_byte_size(node));
    uint8_t bytes[40 + 16 * 48];
    bytes_longs_to_le(longs, n, bytes);
    int32_t h = j_l2b(bytes[8]);
    int64_t ordinal = j_ushr64(bytes_get_long_le(bytes + 8), 16);
    return tn_new_stored(&f->cx, ordinal, bytes_get_long_le(bytes + 32),
            bytes_get_long_le(bytes + 24), spos, bytes_get_long_le(bytes + 16), h, bytes + 40);
}

TEST(tnode_stream_pointer_times_kept) {
    struct nfix f;
    nfix_init(&f);
    struct obj_ctx *cx = &f.cx;
    struct knode *root = kn_new(cx, true);
    root->n.spos = 80;
    struct tnode *top1 = tn_new(cx, 1, root, 80, 20, 100);
    struct tnode *top2 = tn_new(cx, 2, root, 80, 30, 200);
    struct tnode *top3 = tn_new(cx, 3, root, 80, 40, 300);
    tn_set_pointer(cx, top3, 1, &hd_of(cx, &top2->n)->o, top2->n.spos);
    top3->skip[0].time = 30;
    tn_set_pointer(cx, top3, 2, &hd_of(cx, &top1->n)->o, top1->n.spos);
    top3->skip[1].time = 20;

    struct tnode *read1 = write_and_read(&f, top3, 400);     /* memory pointers written */
    struct tnode *read2 = write_and_read(&f, read1, 500);    /* stream pointers written */

    CHECK_EQ(read1->skip[0].pos, 200);
    CHECK_EQ(read1->skip[1].pos, 100);
    CHECK_EQ(read1->skip[0].time, 30);
    CHECK_EQ(read1->skip[1].time, 20);
    CHECK_EQ(read2->skip[0].pos, 200);
    CHECK_EQ(read2->skip[1].pos, 100);
    CHECK_EQ(read2->skip[0].time, 30);
    CHECK_EQ(read2->skip[1].time, 20);
    NFIX_END(&f);
}

static int64_t pos_of(int64_t ordinal) { return 1024 + 64 * ordinal; }
static int64_t root_pos_of(int64_t ordinal) { return 1032 + 64 * ordinal; }
static int64_t time_of(int64_t ordinal) { return 1000 + 3 * ordinal; }

/* StoredTopNode.topOfLayout: ordinal n with the slots of the layout, as
 * stream pointers. */
static struct tnode *top_of_layout(struct nfix *f, int64_t n) {
    struct tnode *t = tn_new(&f->cx, n, NULL, root_pos_of(n), time_of(n), pos_of(n));
    if (t == NULL) {
        return NULL;
    }
    t->n.id = pos_of(n);
    for (int32_t k = 0; k < t->pointers_length; k++) {
        if ((n & j_shl64(1, k)) != 0) {
            int64_t target = j_shl64(j_ushr64(n, k), k) - 1;
            t->skip[k].pos = pos_of(target);
            t->skip[k].time = time_of(target);
        }
    }
    return t;
}

/* StoredTopNode.checkRoundTrip */
static void check_round_trip(struct nfix *f, struct tnode *top) {
    struct tnode *read = write_and_read(f, top, top->n.spos);
    REQUIRE(read != NULL);
    CHECK_EQ(read->top_node_id, top->top_node_id);
    CHECK_EQ(read->pointers_length, top->pointers_length);
    CHECK_EQ(read->root_time, top->root_time);
    CHECK_EQ(read->n.id, top->n.id);
    struct pointer p;
    for (int32_t i = 0; i < tn_get_size(top); i++) {
        tn_get_pointer(top, i, &p);
        int64_t pos = ptr_spos_for_stream(&p);
        CHECK_EQ(tn_get_pointer_pos(read, i), pos);
        if (i > 0) {
            bool set = (top->top_node_id & j_shl64(1, i - 1)) != 0;
            CHECK(set == (pos != SPOS_NULL));
            CHECK_EQ(read->skip[i - 1].time, set ? top->skip[i - 1].time : -1);
        }
    }
}

TEST(tnode_ordinals_round_trip) {
    static const int64_t ordinals[] = {1, 2, 3, 32767, 32768, 32769, 65535, 65536, 98303,
            1 << 20, (INT64_C(1) << 30) - 1, INT64_C(1) << 30, (INT64_C(1) << 31) - 1,
            INT64_C(1) << 31, (INT64_C(1) << 32) - 1, INT64_C(1) << 32, (INT64_C(1) << 32) + 5,
            INT64_C(1) << 40, (INT64_C(1) << 47) - 1, INT64_C(1) << 47, (INT64_C(1) << 48) - 2};
    struct nfix f;
    nfix_init(&f);
    for (size_t j = 0; j < sizeof ordinals / sizeof ordinals[0]; j++) {
        int64_t n = ordinals[j];
        struct topds ds;
        tds_init(&ds, top_of_layout(&f, n - 1));
        struct knode *root = kn_new(&f.cx, true);
        root->n.spos = root_pos_of(n);
        root->n.id = root_pos_of(n);
        CHECK(tds_new_super_root(&f.cx, &ds, time_of(n), root, ACCESS_DATA_DEFAULT,
                &OP_DO_NOTHING_POINTER_CREATED_LISTENER, &OP_DO_NOTHING_NODE_CHANGE_LISTENER));
        struct tnode *top = tds_get_super_root(&ds);
        CHECK_EQ(top->top_node_id, n);
        top->n.spos = pos_of(n);
        top->n.id = pos_of(n);
        check_round_trip(&f, top);
        tds_free(&f.cx, &ds);
        obj_collect(&f.cx);
    }
    check_round_trip(&f, top_of_layout(&f, 0));
    check_round_trip(&f, top_of_layout(&f, TN_MAX_TOP_NODE_ID_VALUE));
    NFIX_END(&f);
}

/* StoredTopNode.testOrdinalField: bytes 10 to 15 hold the ordinal, byte 9
 * zero, byte 8 h. */
TEST(tnode_ordinal_field) {
    static const int64_t ordinals[] = {0, 1, 32768, 98303, (INT64_C(1) << 30) - 1,
            INT64_C(1) << 30, (INT64_C(1) << 32) + 5, (INT64_C(1) << 40) + 3,
            TN_MAX_TOP_NODE_ID_VALUE};
    struct nfix f;
    nfix_init(&f);
    for (size_t j = 0; j < sizeof ordinals / sizeof ordinals[0]; j++) {
        int64_t n = ordinals[j];
        struct tnode *top = top_of_layout(&f, n);
        REQUIRE(top != NULL);
        int64_t longs[(40 + 16 * 48) / 8];
        uint8_t bytes[40 + 16 * 48];
        int32_t count = nw_top_to_longs(top, longs, 0);
        bytes_longs_to_le(longs, count, bytes);
        CHECK_EQ(j_l2b(bytes[8]), top->pointers_length);
        CHECK_EQ(bytes[9], 0);
        for (int b = 0; b < 6; b++) {
            CHECK_EQ(j_l2b(bytes[10 + b]), j_l2b(j_ushr64(n, 8 * b)));
        }
        if (n < (INT64_C(1) << 30)) {
            CHECK_EQ(bytes_get_int_le(bytes + 10), n);
            CHECK_EQ(bytes[14], 0);
            CHECK_EQ(bytes[15], 0);
        }
    }
    NFIX_END(&f);
}

/* StoredTopNode.testTopNodeToLongs1 and 2, over TopTester's data. */
TEST(tnode_to_longs) {
    struct nfix f;
    nfix_init(&f);
    struct top_tester t;
    create_test_data(&f, &t);

    struct tnode *top1 = tds_get_super_root(&t.ds1);
    struct tnode *read = write_and_read(&f, top1, SPOS_NULL);
    CHECK_EQ(read->top_node_id, top1->top_node_id);
    CHECK_EQ(read->root_time, top1->root_time);

    struct tnode *top4 = tds_get_super_root(&t.ds4);
    for (int32_t i = 0; i < top4->pointers_length; i++) {
        struct tnode *older = top4->skip[i].p == NULL ? NULL : (struct tnode *) top4->skip[i].p->obj;
        if (older != NULL && older->n.spos == SPOS_NULL) {
            older->n.spos = pos_of(older->top_node_id);
        }
        if (older != NULL) {
            node_set_canonical(&older->n, true);
        }
    }
    read = write_and_read(&f, top4, SPOS_NULL);
    CHECK_EQ(read->top_node_id, top4->top_node_id);
    CHECK_EQ(read->root_time, top4->root_time);
    CHECK_EQ(read->skip[0].pos, pos_of(2));
    CHECK_EQ(read->skip[1].pos, pos_of(1));
    free_test_data(&f, &t);
    NFIX_END(&f);
}

/* TopNode.createDummy: skip pointers at the ordinal's set bits. */
TEST(tnode_create_dummy) {
    struct nfix f;
    nfix_init(&f);
    struct tnode *t = tn_create_dummy(&f.cx, 5);
    REQUIRE(t != NULL);
    CHECK_EQ(t->pointers_length, 3);
    CHECK_EQ(t->skip[0].pos, 16);
    CHECK_EQ(t->skip[1].pos, SPOS_NULL);
    CHECK_EQ(t->skip[2].pos, 48);
    CHECK_EQ(t->n.id, 103);
    CHECK_EQ(t->root_pointer_pos, 100);
    CHECK_EQ(tn_get_mem_size(t), 112 + 3 * 24);
    NFIX_END(&f);
}

const struct test tnode_tests[] = {
    TEST_ENTRY(tnode_height1),
    TEST_ENTRY(tnode_height2),
    TEST_ENTRY(tnode_top_tester1),
    TEST_ENTRY(tnode_before_first),
    TEST_ENTRY(tnode_find_first_node),
    TEST_ENTRY(tnode_ds3),
    TEST_ENTRY(tnode_ds4),
    TEST_ENTRY(tnode_new_super_root_from_stream_pointers),
    TEST_ENTRY(tnode_stream_pointer_times_kept),
    TEST_ENTRY(tnode_ordinals_round_trip),
    TEST_ENTRY(tnode_ordinal_field),
    TEST_ENTRY(tnode_to_longs),
    TEST_ENTRY(tnode_create_dummy),
    TEST_END
};
