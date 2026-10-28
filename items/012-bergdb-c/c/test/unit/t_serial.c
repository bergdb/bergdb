/* The record writer (bergdb 012-09): Java's tests of StoredTrans.Serializer
 * (its @Nano tests that C has: the records parsed back by 012-06's parser),
 * and TransNodes'. */
#include "test.h"
#include "bytes.h"
#include "meta.h"
#include "rstream.h"
#include "spos.h"
#include "keys.h"
#include "klong.h"
#include "knode.h"
#include "node.h"
#include "obj.h"
#include "serial.h"
#include "snode.h"
#include "strans.h"
#include "tnode.h"
#include "transnodes.h"
#include "transseq.h"
#include "vnode.h"

/* Keys.toSegments(String): an ikey's segments into seg; their number. */
static int32_t segs(const char *ikey, int64_t *seg) {
    uint8_t b[64];
    int32_t n = (int32_t) strlen(ikey);
    keys_ikey_to_bkey((const uint8_t *) ikey, n, b);
    keys_to_segments(b, n, seg);
    return keys_segment_count(n);
}

struct fx {
    struct mem m;
    struct obj_ctx cx;
    struct transnodes tn;
    struct serial s;
    struct st_record r;
    struct err e;
};

static void fx_init(struct fx *f) {
    mem_init(&f->m);
    obj_ctx_init(&f->cx, &f->m);
    tns_init(&f->tn, &f->cx, &f->m);
    ser_init(&f->s, &f->m);
    st_init(&f->r);
}

/* Parses the serialized record at tpos. */
static enum err_code fx_parse(struct fx *f, int64_t tpos) {
    return st_parse(&f->r, tpos, f->s.byte_buffer, f->s.total_size, &f->m, &f->e);
}

static void fx_free(struct fx *f) {
    tns_clear(&f->tn);
    tns_free(&f->tn);
    ser_free(&f->s);
    st_free(&f->r, &f->m);
    obj_free_all(&f->cx, NULL, 0);
    CHECK_MEM_ZERO(&f->m);
}

static struct vnode *value(struct fx *f, const uint8_t *v, int32_t len, int64_t id) {
    struct vnode *n = vn_new(&f->cx, v, len, SPOS_NULL);
    n->n.id = id;
    return n;
}

/* transWithValue: a record of one value node of key "a". */
static int64_t key_a[4];
static int32_t key_a_n;

static void trans_with_value(struct fx *f, const uint8_t *v, int32_t len) {
    tns_clear(&f->tn);
    key_a_n = segs("a", key_a);
    tns_add_value_node(&f->tn, value(f, v, len, 1001), key_a, key_a_n);
}

TEST(serial_serialize1) {
    struct fx f;
    fx_init(&f);
    CHECK(ser_serialize(&f.s, &f.tn, 100, 200, -1, NULL, NULL, ST_MAX_RECORD_SIZE, &f.e)
            == ERR_OK);
    REQUIRE(fx_parse(&f, 200) == ERR_OK);
    CHECK_EQ(f.r.nnodes, 0);
    CHECK_EQ(f.r.tt, 100);
    CHECK_EQ(f.r.tpos, 200);
    CHECK_EQ(f.r.size, 48);
    CHECK_EQ(f.r.top_pos, -1);
    fx_free(&f);
}

TEST(serial_serialize2) {
    struct fx f;
    fx_init(&f);
    const uint8_t b12[] = {12}, b1314[] = {13, 14};
    struct vnode *v0 = value(&f, b12, 0, 11), *v1 = value(&f, b12, 1, 13),
            *v2 = value(&f, b1314, 2, 15);
    struct knode *n = kn_new(&f.cx, true);
    n->n.id = 101;
    kn_add_klong(&f.cx, n, 10, kl_create_key((const uint8_t *) "a", 1), &v0->n, ACCESS_DATA_DEFAULT);
    kn_add_klong(&f.cx, n, 20, kl_create_key((const uint8_t *) "b", 1), &v1->n, ACCESS_DATA_DEFAULT);
    kn_add_klong(&f.cx, n, 30, kl_create_key((const uint8_t *) "c", 1), &v2->n, ACCESS_DATA_DEFAULT);
    int64_t ka[4], kb[4], kc[4];
    int32_t na = segs("a", ka), nb = segs("b", kb), nc = segs("c", kc);
    tns_add_value_node(&f.tn, v0, ka, na);
    tns_add_value_node(&f.tn, v1, kb, nb);
    tns_add_value_node(&f.tn, v2, kc, nc);
    tns_add_key_node(&f.tn, n);
    CHECK(ser_serialize(&f.s, &f.tn, 100, 200, -1, NULL, NULL, ST_MAX_RECORD_SIZE, &f.e)
            == ERR_OK);
    REQUIRE(fx_parse(&f, 200) == ERR_OK);
    REQUIRE(f.r.nnodes == 4);
    CHECK_EQ(f.r.nodes[0].type, NODE_KEY);
    CHECK_EQ(f.r.nodes[1].type, NODE_VALUE);
    CHECK_EQ(f.r.nodes[2].type, NODE_VALUE);
    CHECK_EQ(f.r.nodes[3].type, NODE_VALUE);
    CHECK(f.r.nodes[2].value_len == 1 && f.r.nodes[2].value[0] == 12);
    CHECK(f.r.nodes[3].value_len == 2 && f.r.nodes[3].value[1] == 14);
    /* prepareToSerialize: the key node's position, its prevPos the one before. */
    CHECK_EQ(n->n.spos, 232);
    CHECK_EQ(f.r.nodes[0].prev_pos, -1);
    CHECK_EQ(f.r.nodes[0].spos, 232);
    CHECK_EQ(f.r.nodes[1].spos, v0->n.spos);
    CHECK_EQ(sn_ref(&f.r.nodes[0], 1), v0->n.spos);     /* the reference: the new position */
    fx_free(&f);
}

/* testCorruptGotDirtyCount (005-21) */
TEST(serial_corrupt_got_dirty_count) {
    struct fx f;
    fx_init(&f);
    CHECK(ser_serialize(&f.s, &f.tn, 100, 200, -1, NULL, NULL, ST_MAX_RECORD_SIZE, &f.e)
            == ERR_OK);
    bytes_put_int_le(INT32_MAX, f.s.byte_buffer + 36);     /* after the header and the end */
    CHECK(fx_parse(&f, 200) == ERR_FORMAT);
    CHECK(strcmp(f.e.java, "StreamFormatException") == 0);
    fx_free(&f);
}

/* testRecordAboveLimit (005-17) */
TEST(serial_record_above_limit) {
    struct fx f;
    fx_init(&f);
    static uint8_t big[100 * 1000];
    trans_with_value(&f, big, 90 * 1000);
    CHECK(ser_serialize(&f.s, &f.tn, 100, 200, -1, NULL, NULL, 100 * 1000, &f.e) == ERR_OK);
    trans_with_value(&f, big, 100 * 1000);
    CHECK(ser_serialize(&f.s, &f.tn, 100, 200, -1, NULL, NULL, 100 * 1000, &f.e) == ERR_LIMIT);
    CHECK(strstr(f.e.text, "limit") != NULL);
    CHECK(strcmp(f.e.java, "DbException") == 0);
    fx_free(&f);
}

/* testTopPosOfTopNodeInTransaction, testTopPosOfEarlierTopNode */
TEST(serial_top_pos) {
    struct fx f;
    fx_init(&f);
    struct tnode *top = tn_create_dummy(&f.cx, 7);
    tns_add_top_node(&f.tn, top);
    CHECK(ser_serialize(&f.s, &f.tn, 100, 200, -1, NULL, top, ST_MAX_RECORD_SIZE, &f.e)
            == ERR_OK);
    REQUIRE(fx_parse(&f, 200) == ERR_OK);
    CHECK_EQ(f.r.top_pos, top->n.spos);
    CHECK_EQ(f.r.nodes[0].spos, f.r.top_pos);
    tns_clear(&f.tn);
    top->n.spos = 128;
    CHECK(ser_serialize(&f.s, &f.tn, 100, 200, -1, NULL, top, ST_MAX_RECORD_SIZE, &f.e)
            == ERR_OK);
    REQUIRE(fx_parse(&f, 200) == ERR_OK);
    CHECK_EQ(f.r.top_pos, 128);
    CHECK_EQ(f.r.nnodes, 0);
    fx_free(&f);
}

/* testRefusesOldFormat, testRefusesNewerFormat: the parser's (012-06),
 * on the serializer's record. */
TEST(serial_refuses_other_formats) {
    struct fx f;
    fx_init(&f);
    CHECK(ser_serialize(&f.s, &f.tn, 100, 200, -1, NULL, NULL, ST_MAX_RECORD_SIZE, &f.e)
            == ERR_OK);
    CHECK_EQ(f.s.byte_buffer[4], ST_RECORD_FORMAT);
    const int formats[] = {2, 6, 200};
    for (int i = 0; i < 3; i++) {
        f.s.byte_buffer[4] = (uint8_t) formats[i];
        CHECK(fx_parse(&f, 200) == ERR_FORMAT);
        CHECK(strcmp(f.e.java, "VersioningStreamException") == 0);
    }
    fx_free(&f);
}

/* testSerializeWithGotDirtyIds: each got-dirty node's id and position. */
TEST(serial_got_dirty_ids) {
    struct fx f;
    fx_init(&f);
    struct knode *n1 = kn_new(&f.cx, true), *n2 = kn_new(&f.cx, true);
    n1->n.id = 1000;
    n2->n.id = 2000;
    n2->n.spos = 4000;
    struct ts_info *info = ts_info_new(&f.m);
    ts_info_add_node(info, &f.m, n1, 1000, NODE_KEY, &f.e);
    ts_info_add_node(info, &f.m, n2, 2000, NODE_KEY, &f.e);
    CHECK(ser_serialize(&f.s, &f.tn, 100, 200, -1, info, NULL, ST_MAX_RECORD_SIZE, &f.e)
            == ERR_OK);
    REQUIRE(fx_parse(&f, 200) == ERR_OK);
    REQUIRE(f.r.got_dirty_count == 2);
    CHECK_EQ(st_got_dirty_id(&f.r, 0), 1000);
    CHECK_EQ(st_got_dirty_pos(&f.r, 0), -1);
    CHECK_EQ(st_got_dirty_id(&f.r, 1), 2000);
    CHECK_EQ(st_got_dirty_pos(&f.r, 1), 4000);
    ts_info_free(info, &f.m);
    fx_free(&f);
}

/* testSerializeTransWithDelete, testSerializeWithNewStartupPos1 and 2,
 * testSerializeAndCheckKey and 2 */
TEST(serial_delete_startup_pos_keys) {
    struct fx f;
    fx_init(&f);
    int64_t k1[4];
    int32_t n1 = segs("key1", k1);
    struct vnode *d = vn_create_delete(&f.cx);
    d->n.id = 7;
    tns_add_value_node(&f.tn, d, k1, n1);
    CHECK(ser_serialize(&f.s, &f.tn, 100, 200, 12345, NULL, NULL, ST_MAX_RECORD_SIZE, &f.e)
            == ERR_OK);
    REQUIRE(fx_parse(&f, 200) == ERR_OK);
    REQUIRE(f.r.nnodes == 1);
    CHECK_EQ(f.r.nodes[0].type, NODE_DELETE);
    CHECK_EQ(f.r.startup_pos, 12345);
    CHECK_EQ(f.r.nodes[0].key_n, n1);
    CHECK_EQ(sn_seg(&f.r.nodes[0], 0), k1[0]);

    trans_with_value(&f, (const uint8_t *) "", 0);
    CHECK(ser_serialize(&f.s, &f.tn, 120, META_BLOCK_SIZE, -1, NULL, NULL,
            ST_MAX_RECORD_SIZE, &f.e) == ERR_OK);
    REQUIRE(fx_parse(&f, META_BLOCK_SIZE) == ERR_OK);
    REQUIRE(f.r.nnodes == 1);
    CHECK_EQ(f.r.startup_pos, -1);
    CHECK_EQ(f.r.nodes[0].type, NODE_VALUE);
    CHECK_EQ(f.r.nodes[0].key_n, key_a_n);
    CHECK_EQ(sn_seg(&f.r.nodes[0], 0), key_a[0]);
    fx_free(&f);
}

/* testSameBytesFromReusedSerializer: a record's bytes do not depend on what
 * the serializer wrote before (the value node's padding is written). */
TEST(serial_same_bytes_reused) {
    struct fx f, g;
    fx_init(&f);
    fx_init(&g);
    uint8_t earlier[64];
    memset(earlier, 99, sizeof earlier);
    trans_with_value(&f, earlier, 64);
    CHECK(ser_serialize(&f.s, &f.tn, 10, 1024, 128, NULL, NULL, ST_MAX_RECORD_SIZE, &f.e)
            == ERR_OK);
    const uint8_t one[] = {42};
    trans_with_value(&f, one, 1);
    CHECK(ser_serialize(&f.s, &f.tn, 20, 2048, 128, NULL, NULL, ST_MAX_RECORD_SIZE, &f.e)
            == ERR_OK);
    trans_with_value(&g, one, 1);
    CHECK(ser_serialize(&g.s, &g.tn, 20, 2048, 128, NULL, NULL, ST_MAX_RECORD_SIZE, &g.e)
            == ERR_OK);
    REQUIRE(f.s.total_size == g.s.total_size);
    CHECK_BYTES(f.s.byte_buffer, g.s.byte_buffer, (size_t) f.s.total_size);
    fx_free(&f);
    fx_free(&g);
}

/* A record across a meta block: positions skip the block, the value node's
 * stored offset counts record bytes only (005-34). */
TEST(serial_across_meta_block) {
    struct fx f;
    fx_init(&f);
    static uint8_t v[600];
    trans_with_value(&f, v, 600);
    const int64_t tpos = META_BLOCK_DISTANCE - 64;
    CHECK(ser_serialize(&f.s, &f.tn, 100, tpos, 0, NULL, NULL, ST_MAX_RECORD_SIZE, &f.e)
            == ERR_OK);
    struct vnode *node = f.tn.value_nodes[0];
    CHECK_EQ(node->n.spos, tpos + 32);
    CHECK_EQ(f.s.trans_last_spos, rs_get_spos(tpos, f.s.total_size - 1));
    CHECK(f.s.trans_last_spos > META_BLOCK_DISTANCE + META_BLOCK_SIZE);
    fx_free(&f);
}

/* TransNodes: each node once, in the order of addition; clean; clear. */
TEST(transnodes_basics) {
    struct fx f;
    fx_init(&f);
    struct knode *a = kn_new(&f.cx, true), *b = kn_new(&f.cx, false);
    a->n.id = 1;
    b->n.id = 3;
    struct tnode *t = tn_create_dummy(&f.cx, 2);
    CHECK(tns_add_key_node(&f.tn, a));
    CHECK(tns_add_key_node(&f.tn, b));
    CHECK(tns_add_key_node(&f.tn, a));      /* again: not added */
    CHECK(tns_add_top_node(&f.tn, t));
    CHECK_EQ(tns_size(&f.tn), 3);
    CHECK(tns_get(&f.tn, 0) == &t->n);      /* the top nodes first */
    CHECK(tns_get(&f.tn, 1) == &a->n);
    CHECK(tns_get(&f.tn, 2) == &b->n);
    node_set_dirty(&a->n, true);
    tns_clean(&f.tn);
    CHECK(!node_is_dirty(&a->n));
    for (int i = 0; i < 200; i++) {         /* testLarge: the arrays grow */
        struct knode *k = kn_new(&f.cx, true);
        k->n.id = 100 + 2 * i;
        CHECK(tns_add_key_node(&f.tn, k));
    }
    CHECK_EQ(tns_size(&f.tn), 203);
    tns_clear(&f.tn);
    CHECK_EQ(tns_size(&f.tn), 0);
    CHECK(!node_is_in_trans_nodes(&a->n));
    CHECK(tns_add_key_node(&f.tn, a));      /* after clear, added again */
    CHECK_EQ(tns_size(&f.tn), 1);
    fx_free(&f);
}

const struct test serial_tests[] = {
    TEST_ENTRY(serial_serialize1),
    TEST_ENTRY(serial_serialize2),
    TEST_ENTRY(serial_corrupt_got_dirty_count),
    TEST_ENTRY(serial_record_above_limit),
    TEST_ENTRY(serial_top_pos),
    TEST_ENTRY(serial_refuses_other_formats),
    TEST_ENTRY(serial_got_dirty_ids),
    TEST_ENTRY(serial_delete_startup_pos_keys),
    TEST_ENTRY(serial_same_bytes_reused),
    TEST_ENTRY(serial_across_meta_block),
    TEST_ENTRY(transnodes_basics),
    TEST_END
};
