/*
 * The node parsers' refusals of a damaged node whose checksum is right
 * (bergdb 019-32, as Java's since release 2026.3): StoredKeyNode's
 * testRefusesBadKlongs and StoredValueNode's testRefusesBadKey, each node
 * given its checksum and parsed as NodeStream.bytesToNode does
 * (StoredValueNode.parseWithRightChecksum). Before, each was parsed, and a
 * start or a read met an assert of the Core (harness 6.1, bergdb 018-07),
 * which in C aborts.
 */
#include "test.h"
#include "nfix.h"
#include "bytes.h"
#include "checksum.h"
#include "keys.h"
#include "nwrite.h"
#include "snode.h"
#include "spos.h"

/* StoredValueNode.parseWithRightChecksum: the node at buffer[0], of 'size' bytes, given its
 * checksum and parsed at 128 as NodeStream.bytesToNode does. ERR_OK if it is parsed; else
 * the refusal in e, which must not be a checksum's. */
static enum err_code parse_with_right_checksum(uint8_t *buffer, int32_t size, struct err *e) {
    int32_t sum = cks_sum_with_zero_replace(buffer, 0, size, 6);
    buffer[6] = (uint8_t) sum;
    buffer[7] = (uint8_t) (sum >> 8);
    struct sn_node n;
    err_clear(e);
    enum err_code rc = sn_bytes_to_node(128, buffer, size, 0, size, &n, e);
    CHECK(rc == ERR_OK || strcmp(e->java, "StreamChecksumException") != 0);
    return rc;
}

/* testRefusesBadKlongs: a klong of type 2 (klong 0's top byte xor 0x80), a key klong's
 * pointer of -8, a key count one below what the node's size holds (the pointers read from
 * the wrong bytes). Klong i is at 32 + 8 i, its pointer at 48 + 8 i, the count at 17. */
TEST(snode_refuses_bad_klongs) {
    struct nfix f;
    struct err e;
    nfix_init(&f);
    struct knode *node = kn_new(&f.cx, true);
    REQUIRE(node != NULL);
    CHECK(kn_add_to_end(&f.cx, node, kl_create_time(5000), NULL, SPOS_NULL));
    CHECK(kn_add_to_end(&f.cx, node, nfix_key("key"), NULL, 1234));
    const int32_t size = nw_key_byte_size(node);
    REQUIRE(size == 64);
    int64_t longs[8];
    nw_key_to_longs(node, longs, 0, 200);
    uint8_t buffer[64];

    bytes_longs_to_le(longs, 8, buffer);
    CHECK_EQ(parse_with_right_checksum(buffer, size, &e), ERR_OK);      /* as it is: taken */

    bytes_longs_to_le(longs, 8, buffer);
    buffer[39] ^= 0x80;
    CHECK_EQ(parse_with_right_checksum(buffer, size, &e), ERR_FORMAT);
    CHECK(strcmp(e.java, "StreamFormatException") == 0);
    CHECK(strcmp(e.text, "Bad klong type, 2, of klong 0 of key node at spos 128.") == 0);

    bytes_longs_to_le(longs, 8, buffer);
    bytes_put_long_le(-8, buffer + 56);
    CHECK_EQ(parse_with_right_checksum(buffer, size, &e), ERR_FORMAT);
    CHECK(strcmp(e.java, "StreamFormatException") == 0);
    CHECK(strcmp(e.text, "Bad pointer, -8, of klong 1 of key node at spos 128.") == 0);

    bytes_longs_to_le(longs, 8, buffer);
    buffer[17] ^= 3;
    CHECK_EQ(parse_with_right_checksum(buffer, size, &e), ERR_FORMAT);
    CHECK(strcmp(e.java, "StreamFormatException") == 0);
    CHECK(strcmp(e.text, "Bad key count, 1, of key node at spos 128, size 64.") == 0);

    /* A time klong's pointer is not a key klong's: SPOS_NULL or anything (Java checks only a
     * key klong's); a delete bitmap klong (type 3) is a klong. */
    bytes_longs_to_le(longs, 8, buffer);
    bytes_put_long_le(-8, buffer + 48);
    CHECK_EQ(parse_with_right_checksum(buffer, size, &e), ERR_OK);
    bytes_longs_to_le(longs, 8, buffer);
    bytes_put_long_le(kl_create_delete(), buffer + 40);
    CHECK_EQ(parse_with_right_checksum(buffer, size, &e), ERR_OK);
    NFIX_END(&f);
}

/* testRefusesBadKey: a value node whose key is not one that Keys.toSegments makes: a segment
 * with bit 63 (a klong's type) or bit 0 set, a last segment of length 7, a segment of
 * length 6 before the last. The key as it is: taken. */
TEST(snode_refuses_bad_key) {
    struct nfix f;
    struct err e;
    nfix_init(&f);
    uint8_t bkey[16];
    CHECK(keys_ikey_to_bkey((const uint8_t *) "/-mykey.txt", 11, bkey));
    int64_t key[2];
    REQUIRE(keys_segment_count(11) == 2);       /* two segments, of 7 and 4 bytes */
    keys_to_segments(bkey, 11, key);
    uint8_t value[10] = {0};
    struct vnode *node = vn_new(&f.cx, value, 10, SPOS_NULL);
    REQUIRE(node != NULL);
    const int32_t size = nw_value_byte_size(node, 2);
    const int32_t keyAt = 24 + 10 + 4;
    const int64_t bad[4][2] = {
        { key[0], key[1] ^ INT64_MIN },
        { key[0], key[1] | 1 },
        { key[0], key[1] | (7 << 3) },
        { key[0] & ~(INT64_C(1) << 3), key[1] },
    };
    uint8_t buffer[64];
    REQUIRE(size <= 64);
    for (int i = 0; i < 4; i++) {
        memset(buffer, 0, sizeof buffer);
        nw_value_to_bytes(node, key, 2, buffer, 0);
        bytes_put_long_le(bad[i][0], buffer + keyAt);
        bytes_put_long_le(bad[i][1], buffer + keyAt + 8);
        CHECK_EQ(parse_with_right_checksum(buffer, size, &e), ERR_FORMAT);
        CHECK(strcmp(e.java, "StreamFormatException") == 0);
        CHECK(strcmp(e.text, "Bad key of value node at spos 128.") == 0);
    }
    memset(buffer, 0, sizeof buffer);
    nw_value_to_bytes(node, key, 2, buffer, 0);
    CHECK_EQ(parse_with_right_checksum(buffer, size, &e), ERR_OK);      /* the key as it is */
    NFIX_END(&f);
}

const struct test snode_tests[] = {
    TEST_ENTRY(snode_refuses_bad_klongs),
    TEST_ENTRY(snode_refuses_bad_key),
    TEST_END
};
