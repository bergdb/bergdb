/* Unit tests of nwrite and vnode (bergdb 012-07): the writers against
 * Java's bytes (the creation's record of 012-02, section 8.2), Java's
 * @Nano tests of StoredKeyNode, StoredValueNode and ValueNode that C has
 * the behaviour of. A test-local reader of a written node's fields stands
 * in for 012-06's parser and makes the object as the parse does. */
#include "bytes.h"
#include "checksum.h"
#include "keys.h"
#include "klong.h"
#include "knode.h"
#include "nfix.h"
#include "nwrite.h"
#include "opdata.h"
#include "spos.h"
#include "test.h"
#include "tnode.h"
#include "topds.h"
#include "vnode.h"

/* 012-02, section 8.2: the creation's top node at 160 and root key node at
 * 200, with the time T0 = 10,000,000,000,000, as Java writes them (the
 * stream "fresh"). */
static const uint8_t CREATION_TOP[40] = {
    0x28, 0x00, 0x00, 0x00, 0x0a, 0x02, 0x80, 0x7e,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0xa0, 0x72, 0x4e, 0x18, 0x09, 0x00, 0x00,
    0xc8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
};

static const uint8_t CREATION_KEY[48] = {
    0x30, 0x00, 0x00, 0x00, 0x14, 0x02, 0xca, 0x3c,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x01, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
    0x00, 0xa0, 0x72, 0x4e, 0x18, 0x09, 0x00, 0x00,
    0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
};

/* Db.writePrimordialTransaction's two nodes, and the serializer's
 * positions (prepareToSerialize), written as StoredTrans.Serializer writes
 * them. */
TEST(nwrite_creation_bytes) {
    struct nfix f;
    nfix_init(&f);
    const int64_t tt = INT64_C(10000000000000);

    struct knode *root = kn_new_with_time(&f.cx, tt);
    REQUIRE(root != NULL);
    root->n.id = 0;             /* setIdOfNode: x.nextVpos starts at 0 */
    root->n.spos = 0;
    node_set_canonical(&root->n, true);
    struct tnode *superRoot = tds_create_super_root_from_first_key_node(&f.cx, tt, root,
            ACCESS_DATA_DEFAULT, &OP_DO_NOTHING_POINTER_CREATED_LISTENER);
    REQUIRE(superRoot != NULL);
    superRoot->n.id = spos_next_vpos(0);
    superRoot->n.spos = superRoot->n.id;

    /* prepareToSerialize: the top node first, then the key node. */
    superRoot->n.spos = 160;
    int64_t prevPos = root->n.spos;
    root->n.spos = 160 + nw_top_byte_size(superRoot);
    CHECK_EQ(root->n.spos, 200);

    int64_t longs[11];
    int32_t n = nw_top_to_longs(superRoot, longs, 0);
    n += nw_key_to_longs(root, longs, n, prevPos);
    CHECK_EQ(n, 11);
    uint8_t bytes[88];
    bytes_longs_to_le(longs, n, bytes);
    CHECK_BYTES(bytes, CREATION_TOP, 40);
    CHECK_BYTES(bytes + 40, CREATION_KEY, 48);
    /* The checksums as a reader checks them. */
    CHECK_EQ(cks_sum_with_zero_replace(bytes, 0, 40, 6), bytes_get_ushort_le(bytes + 6));
    CHECK_EQ(cks_sum_with_zero_replace(bytes, 40, 48, 46), bytes_get_ushort_le(bytes + 46));
    NFIX_END(&f);
}

/* StoredKeyNode.testSerialize: a key node written and made again. */
TEST(nwrite_key_serialize) {
    struct nfix f;
    nfix_init(&f);
    struct knode *node = kn_new(&f.cx, true);
    int64_t k0 = kl_create_time(5000);
    int64_t k1 = kl_create_key((const uint8_t *) "key", 3);
    CHECK(kn_add_to_end(&f.cx, node, k0, NULL, SPOS_NULL));
    CHECK(kn_add_to_end(&f.cx, node, k1, NULL, 1234));

    int32_t byteSize = nw_key_byte_size(node);
    CHECK_EQ(byteSize, 64);
    int64_t longBuffer[8];
    int32_t offset = nw_key_to_longs(node, longBuffer, 0, 200);
    CHECK_EQ(offset, byteSize / 8);
    uint8_t b[64];
    bytes_longs_to_le(longBuffer, offset, b);

    /* The fields as StoredKeyNode.parse reads them. */
    CHECK_EQ(bytes_get_int_le(b), 64);
    CHECK_EQ(b[4], NODE_TYPE_KEY_NODE);
    CHECK_EQ(b[5], 2);
    CHECK_EQ(bytes_get_long_le(b + 8), 200);
    CHECK_EQ(b[16], 1);
    CHECK_EQ(bytes_get_short_le(b + 17), 2);
    struct knode *stored = kn_new_stored(&f.cx, b[16] == 1, 0, bytes_get_long_le(b + 24),
            bytes_get_short_le(b + 17), b + 32, b + 32 + 8 * 2);
    REQUIRE(stored != NULL);
    CHECK_EQ(stored->size, node->size);
    CHECK_EQ(kn_get_klong(stored, 0), kn_get_klong(node, 0));
    CHECK_EQ(kn_get_klong(stored, 1), kn_get_klong(node, 1));
    CHECK_EQ(kn_get_pointer_pos(stored, 1), 1234);
    CHECK_EQ(stored->last_time_index, 0);
    /* Written again: the same bytes. */
    int64_t again[8];
    uint8_t b2[64];
    bytes_longs_to_le(again, nw_key_to_longs(stored, again, 0, 200), b2);
    CHECK_BYTES(b, b2, 64);
    NFIX_END(&f);
}

/* The fields of a written value node, as StoredValueNode.parse reads them,
 * made into an object (the parser's checks are 012-06's). */
static struct vnode *read_value(struct nfix *f, const uint8_t *buffer, int32_t offset,
        int64_t spos, int64_t *key, int32_t *key_n) {
    const uint8_t *b = buffer + offset;
    int32_t type = b[4];
    int64_t id = bytes_get_long_le(b + 8);
    int32_t offsetFromTrans = bytes_get_int_le(b + 16);
    int32_t o = 20;
    const uint8_t *value = NULL;
    int32_t len = -1;
    if (type == NODE_TYPE_VALUE) {
        len = bytes_get_int_le(b + o);
        o += 4;
        value = b + o;
        o += len;
    }
    int32_t keySize = bytes_get_int_le(b + o);
    o += 4;
    *key_n = keySize / 8;
    for (int32_t i = 0; i < *key_n; i++) {
        key[i] = bytes_get_long_le(b + o + 8 * i);
    }
    /* RecoverableStream.getStartSpos(spos, offsetFromTrans), without a meta
     * block between (the test's records are small). */
    int64_t tpos = spos - offsetFromTrans;
    return vn_new_stored(&f->cx, value, len, spos, id, tpos);
}

/* StoredValueNode.testToBytesAndBack, with the key checked
 * (testToBytesAndBackAndCheckKey). */
TEST(nwrite_value_to_bytes_and_back) {
    struct nfix f;
    nfix_init(&f);
    uint8_t value[10] = {0};
    value[3] = 3;
    value[9] = (uint8_t) -2;
    const char *ikey = "/-mykey.txt";
    uint8_t bkey[16];
    CHECK(keys_ikey_to_bkey((const uint8_t *) ikey, 11, bkey));
    int64_t key[4];
    int32_t key_n = keys_segment_count(11);
    keys_to_segments(bkey, 11, key);

    struct vnode *node = vn_new(&f.cx, value, 10, SPOS_NULL);
    int32_t size = nw_value_byte_size(node, key_n);
    CHECK_EQ(size, 8 + 8 + 4 + 4 + 10 + 4 + 16 + 2);
    CHECK_EQ(nw_value_byte_size_long(10, key_n), size);
    uint8_t buffer[64];
    memset(buffer, 0xee, sizeof buffer);    /* the padding must be zeroed */
    CHECK_EQ(nw_value_to_bytes(node, key, key_n, buffer, 0), size);
    CHECK_EQ(buffer[size - 1], 0);
    CHECK_EQ(buffer[size - 2], 0);
    CHECK_EQ(cks_sum_with_zero_replace(buffer, 0, size, 6), bytes_get_ushort_le(buffer + 6));

    int64_t key2[4];
    int32_t key2_n;
    struct vnode *node2 = read_value(&f, buffer, 0, 128, key2, &key2_n);
    REQUIRE(node2 != NULL);
    CHECK_EQ(nw_value_byte_size(node2, key2_n), size);
    CHECK_EQ(node2->len, 10);
    CHECK_BYTES(node2->value, value, 10);
    CHECK_EQ(key2_n, key_n);
    CHECK_EQ(key2[0], key[0]);
    CHECK_EQ(key2[1], key[1]);
    CHECK_EQ(node2->n.spos, 128);       /* testThatSposIsSetWhenParsedFromBytes */
    NFIX_END(&f);
}

/* A delete node: no value, type 40, 24 + 8 k bytes. */
TEST(nwrite_delete_node) {
    struct nfix f;
    nfix_init(&f);
    int64_t key[1] = {kl_create_compare_value((const uint8_t *) "\x01\x63", 2)};
    struct vnode *node = vn_create_delete(&f.cx);
    node->n.id = 571;
    CHECK(vn_is_delete(node));
    CHECK_EQ(vn_get_type(node), NODE_TYPE_DELETE);
    int32_t size = nw_value_byte_size(node, 1);
    CHECK_EQ(size, 32);
    CHECK_EQ(nw_value_byte_size_long(-1, 1), 32);
    uint8_t buffer[64];
    CHECK_EQ(nw_value_to_bytes(node, key, 1, buffer, 8), 32);
    CHECK_EQ(buffer[8 + 4], NODE_TYPE_DELETE);
    CHECK_EQ(buffer[8 + 5], 4);
    CHECK_EQ(bytes_get_long_le(buffer + 8 + 8), 571);
    CHECK_EQ(bytes_get_int_le(buffer + 8 + 16), 8);         /* the offset, as given */
    CHECK_EQ(bytes_get_int_le(buffer + 8 + 20), 8);         /* the key size */
    CHECK_EQ(bytes_get_long_le(buffer + 8 + 24), key[0]);
    int64_t key2[1];
    int32_t key2_n;
    struct vnode *node2 = read_value(&f, buffer, 8, 136, key2, &key2_n);
    CHECK(vn_is_delete(node2));
    CHECK_EQ(vn_get_tpos(node2), 128);
    NFIX_END(&f);
}

/* StoredValueNode.testOffsetFromTrans */
TEST(nwrite_offset_from_trans) {
    struct nfix f;
    nfix_init(&f);
    uint8_t value[10] = {0};
    int64_t key[2];
    uint8_t bkey[16];
    CHECK(keys_ikey_to_bkey((const uint8_t *) "/-mykey.txt", 11, bkey));
    keys_to_segments(bkey, 11, key);
    struct vnode *node = vn_new(&f.cx, value, 10, SPOS_NULL);
    uint8_t buffer[200];
    nw_value_to_bytes(node, key, 2, buffer, 120);
    int64_t key2[2];
    int32_t key2_n;
    struct vnode *stored = read_value(&f, buffer, 120, 128 + 120, key2, &key2_n);
    CHECK_EQ(vn_get_offset_from_trans(stored), 120);
    CHECK_EQ(vn_get_tpos(stored), 128);
    NFIX_END(&f);
}

/* StoredValueNode.testOffsetFromTransAcrossMetaBlock's second half:
 * offsetFromTrans is an unsigned int, also above 2^31; a vpos or -1 has no
 * record. */
TEST(nwrite_tpos_unsigned) {
    struct nfix f;
    nfix_init(&f);
    const int64_t d = 200000, m = 128;
    int64_t far = 7 * d + 1000;
    /* RecoverableStream.getSpos(far, Integer.MAX_VALUE - 101), 012-02, 2.3. */
    int64_t size = INT32_MAX - 101;
    int64_t blocks = size / (d - m);
    int64_t left = size - blocks * (d - m);
    if (far % d + left >= d) {
        blocks++;
    }
    int64_t farSpos = far + size + blocks * m;
    CHECK(farSpos - far > INT32_MAX);
    struct vnode *n = vn_new(&f.cx, NULL, 0, SPOS_NULL);
    n->offset_from_trans = (uint32_t) j_l2i(farSpos - far);
    n->n.spos = farSpos;
    CHECK_EQ(vn_get_tpos(n), far);
    n->n.spos = farSpos + 1;            /* A vpos: not written yet. */
    CHECK_EQ(vn_get_tpos(n), SPOS_NULL);
    n->n.spos = SPOS_NULL;
    CHECK_EQ(vn_get_tpos(n), SPOS_NULL);
    NFIX_END(&f);
}

/* ValueNode.testDummy: a delete node has no pointers, is never dirty. */
TEST(nwrite_value_node_dummy) {
    struct nfix f;
    nfix_init(&f);
    struct vnode *v = vn_create_delete(&f.cx);
    CHECK_EQ(node_size(&v->n), 0);
    CHECK_EQ(node_memory_pointer_count(&v->n), 0);
    CHECK(vn_is_delete(v));
    CHECK(!node_is_dirty(&v->n));
    CHECK(node_is_canonical(&v->n));
    node_set_canonical(&v->n, false);   /* no effect */
    CHECK(node_is_canonical(&v->n));
    CHECK_EQ(vn_get_mem_size(v), 36);
    struct vnode *w = vn_new(&f.cx, (const uint8_t *) "abc", 3, 8);
    CHECK_EQ(vn_get_mem_size(w), 59);
    CHECK_EQ(vn_get_type(w), NODE_TYPE_VALUE);
    NFIX_END(&f);
}

const struct test nwrite_tests[] = {
    TEST_ENTRY(nwrite_creation_bytes),
    TEST_ENTRY(nwrite_key_serialize),
    TEST_ENTRY(nwrite_value_to_bytes_and_back),
    TEST_ENTRY(nwrite_delete_node),
    TEST_ENTRY(nwrite_offset_from_trans),
    TEST_ENTRY(nwrite_tpos_unsigned),
    TEST_ENTRY(nwrite_value_node_dummy),
    TEST_END
};
