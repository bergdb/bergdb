/*
 * The node parsers' refusals of a damaged node whose checksum is right
 * (bergdb 019-32, as Java's since release 2026.3): StoredKeyNode's
 * testRefusesBadKlongs and StoredValueNode's testRefusesBadKey, each node
 * given its checksum and parsed as NodeStream.bytesToNode does
 * (StoredValueNode.parseWithRightChecksum). Before, each was parsed, and a
 * start or a read met an assert of the Core (harness 6.1, bergdb 018-07),
 * which in C aborts. And the three Stored*Node classes' other refusals
 * (022-05): another format version, a top node's pointer count and
 * ordinal, a key count and the value node's sizes beyond the node
 * (015-07), with Java's exceptions and the starts of their texts.
 */
#include "test.h"
#include "nfix.h"
#include "bytes.h"
#include "checksum.h"
#include "keys.h"
#include "nwrite.h"
#include "snode.h"
#include "jsem.h"
#include "spos.h"
#include "tnode.h"

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

/* parse_with_right_checksum of a node of 'size' bytes in a buffer of len bytes, which
 * holds bytes after the node, as a load's buffer does (Java's tests' size + 64). */
static enum err_code parse_in_buffer(uint8_t *buffer, int32_t len, int32_t size, struct err *e) {
    int32_t sum = cks_sum_with_zero_replace(buffer, 0, size, 6);
    buffer[6] = (uint8_t) sum;
    buffer[7] = (uint8_t) (sum >> 8);
    struct sn_node n;
    err_clear(e);
    enum err_code rc = sn_bytes_to_node(128, buffer, len, 0, size, &n, e);
    CHECK(rc == ERR_OK || strcmp(e->java, "StreamChecksumException") != 0);
    return rc;
}

static bool starts_with(const char *s, const char *prefix) {
    return strncmp(s, prefix, strlen(prefix)) == 0;
}

static int64_t sl_pos_of(int64_t ordinal) { return 1024 + 64 * ordinal; }
static int64_t sl_time_of(int64_t ordinal) { return 1000 + 3 * ordinal; }

/* StoredTopNode.topOfLayout: ordinal n with the slots of the layout, as stream
 * pointers (t_tnode.c's). */
static struct tnode *sl_top_of_layout(struct nfix *f, int64_t n) {
    struct tnode *t = tn_new(&f->cx, n, NULL, 1032 + 64 * n, sl_time_of(n), sl_pos_of(n));
    if (t == NULL) {
        return NULL;
    }
    t->n.id = sl_pos_of(n);
    for (int32_t k = 0; k < t->pointers_length; k++) {
        if ((n & j_shl64(1, k)) != 0) {
            int64_t target = j_shl64(j_ushr64(n, k), k) - 1;
            t->skip[k].pos = sl_pos_of(target);
            t->skip[k].time = sl_time_of(target);
        }
    }
    return t;
}

/* A top node's bytes, from StoredTopNode.toLongs; its size. */
static int32_t top_bytes(const struct tnode *top, uint8_t *bytes) {
    int64_t longs[(40 + 16 * 48) / 8];
    const int32_t size = nw_top_byte_size(top);
    const int32_t count = nw_top_to_longs(top, longs, 0);
    CHECK_EQ(count * 8, size);
    bytes_longs_to_le(longs, count, bytes);
    return size;
}

/* StoredTopNode's refusals: testNegativePointerCount (h -3), testRefusesOtherVersion
 * (format 3: a VersioningStreamException), testParserRefusesSlotsThatDoNotFit (the
 * ordinal field set to one whose slots are not the node's: WP A3) and
 * testRefusesPointerCountBeyondTheNode (h one more than the node holds, and 127, its
 * checksum right: 015-07). Each with Java's exception and the start of its text. */
TEST(snode_top_refusals) {
    struct nfix f;
    struct err e;
    struct sn_node n;
    nfix_init(&f);
    uint8_t bytes[40 + 16 * 48 + 64];

    struct tnode *dummy = tn_create_dummy(&f.cx, 5);
    REQUIRE(dummy != NULL);
    int32_t size = top_bytes(dummy, bytes);
    CHECK_EQ(sn_parse_top(bytes, size, 0, 1000, &n, &e), ERR_OK);
    bytes[8] = (uint8_t) -3;
    CHECK_EQ(sn_parse_top(bytes, size, 0, 1000, &n, &e), ERR_FORMAT);
    CHECK(strcmp(e.java, "StreamFormatException") == 0);
    CHECK(strcmp(e.text, "TopNode at 1000 with -3 skip pointers.") == 0);

    top_bytes(dummy, bytes);
    CHECK_EQ(bytes[5], 2);
    bytes[5] = 3;
    CHECK_EQ(sn_parse_top(bytes, size, 0, 1000, &n, &e), ERR_FORMAT);
    CHECK(strcmp(e.java, "VersioningStreamException") == 0);
    CHECK(strstr(e.text, "format version 3") != NULL);

    const int64_t cases[6][2] = { { 65536, 0 }, { 98303, 32767 }, { 5, 4 }, { 6, 5 },
            { (INT64_C(1) << 32) + 5, 5 }, { (INT64_C(1) << 40) + 3, 3 } };
    for (int i = 0; i < 6; i++) {
        struct tnode *top = sl_top_of_layout(&f, cases[i][0]);
        REQUIRE(top != NULL);
        size = top_bytes(top, bytes);
        CHECK_EQ(sn_parse_top(bytes, size, 0, sl_pos_of(cases[i][0]), &n, &e), ERR_OK);
        for (int b = 0; b < 6; b++) {
            bytes[10 + b] = (uint8_t) j_ushr64(cases[i][1], 8 * b);
        }
        CHECK_EQ(sn_parse_top(bytes, size, 0, sl_pos_of(cases[i][0]), &n, &e), ERR_FORMAT);
        CHECK(strcmp(e.java, "StreamFormatException") == 0);
        CHECK(starts_with(e.text, "TopNode at "));
    }

    struct tnode *top = sl_top_of_layout(&f, 5);
    REQUIRE(top != NULL);
    const int32_t counts[2] = { top->pointers_length + 1, 127 };
    for (int i = 0; i < 2; i++) {
        memset(bytes, 0, sizeof bytes);
        size = top_bytes(top, bytes);
        bytes[8] = (uint8_t) counts[i];
        CHECK_EQ(parse_in_buffer(bytes, size + 64, size, &e), ERR_FORMAT);
        CHECK(strcmp(e.java, "StreamFormatException") == 0);
        CHECK(starts_with(e.text, "TopNode at") && strstr(e.text, "has the size") != NULL);
    }
    NFIX_END(&f);
}

/* StoredKeyNode.testRefusesOtherVersion (format 3: a VersioningStreamException) and
 * testRefusesKeyCountBeyondTheNode (a count of 32,767 and of 3, one more than the
 * node holds, its checksum right, the buffer longer than the node: 015-07). */
TEST(snode_key_refusals) {
    struct nfix f;
    struct err e;
    struct sn_node n;
    nfix_init(&f);
    struct knode *node = kn_new(&f.cx, true);
    REQUIRE(node != NULL);
    CHECK(kn_add_to_end(&f.cx, node, kl_create_time(5000), NULL, SPOS_NULL));
    int64_t longs[8];
    uint8_t buffer[64 + 64];
    int32_t size = nw_key_byte_size(node);
    REQUIRE(size == 48);
    nw_key_to_longs(node, longs, 0, 200);
    bytes_longs_to_le(longs, size / 8, buffer);
    CHECK_EQ(sn_parse_key(buffer, size, 0, 0, &n, &e), ERR_OK);
    CHECK_EQ(buffer[5], 2);
    buffer[5] = 3;
    CHECK_EQ(sn_parse_key(buffer, size, 0, 0, &n, &e), ERR_FORMAT);
    CHECK(strcmp(e.java, "VersioningStreamException") == 0);
    CHECK(strstr(e.text, "format version 3") != NULL);

    CHECK(kn_add_to_end(&f.cx, node, nfix_key("key"), NULL, 1234));
    size = nw_key_byte_size(node);
    REQUIRE(size == 64);
    nw_key_to_longs(node, longs, 0, 200);
    const int32_t counts[2] = { 32767, 3 };
    for (int i = 0; i < 2; i++) {
        memset(buffer, 0, sizeof buffer);
        bytes_longs_to_le(longs, 8, buffer);
        buffer[17] = (uint8_t) counts[i];
        buffer[18] = (uint8_t) (counts[i] >> 8);
        CHECK_EQ(parse_in_buffer(buffer, size + 64, size, &e), ERR_FORMAT);
        CHECK(strcmp(e.java, "StreamFormatException") == 0);
        CHECK(starts_with(e.text, "Bad key count"));
    }
    NFIX_END(&f);
}

/* StoredValueNode.testRefusesOtherVersion (format 5: a VersioningStreamException) and
 * testRefusesSizesBeyondTheNode: the value's size -1 and 1,000, the key's 8,000 and 16
 * more than the key, the node's 20, each with its checksum right, in a buffer longer
 * than the node (015-07). */
TEST(snode_value_refusals) {
    struct nfix f;
    struct err e;
    struct sn_node n;
    nfix_init(&f);
    uint8_t bkey[16];
    int64_t key[2];
    uint8_t buffer[64 + 64];
    CHECK(keys_ikey_to_bkey((const uint8_t *) "a", 1, bkey));
    keys_to_segments(bkey, 1, key);
    uint8_t value[10] = {0};
    struct vnode *three = vn_new(&f.cx, value, 3, SPOS_NULL);
    REQUIRE(three != NULL);
    int32_t size = nw_value_byte_size(three, 1);
    REQUIRE(size <= 64);
    memset(buffer, 0, sizeof buffer);
    nw_value_to_bytes(three, key, 1, buffer, 0);
    CHECK_EQ(sn_parse_value(buffer, size, 0, 128, &n, &e), ERR_OK);
    CHECK_EQ(buffer[5], 4);
    buffer[5] = 5;
    CHECK_EQ(sn_parse_value(buffer, size, 0, 128, &n, &e), ERR_FORMAT);
    CHECK(strcmp(e.java, "VersioningStreamException") == 0);
    CHECK(strstr(e.text, "format version 5") != NULL);

    CHECK(keys_ikey_to_bkey((const uint8_t *) "/-mykey.txt", 11, bkey));
    REQUIRE(keys_segment_count(11) == 2);
    keys_to_segments(bkey, 11, key);
    struct vnode *node = vn_new(&f.cx, value, 10, SPOS_NULL);
    REQUIRE(node != NULL);
    size = nw_value_byte_size(node, 2);
    REQUIRE(size <= 64);
    const int32_t valueAt = 20, keyAt = 24 + 10;
    const struct { int32_t at; int32_t v; const char *start; } cases[5] = {
        { valueAt, -1, "Bad value size" },
        { valueAt, 1000, "Bad value size" },
        { keyAt, 8000, "Bad key size" },
        { keyAt, 8 * 2 + 16, "Bad key size" },
        { 0, 20, "Bad value node size" },
    };
    for (int i = 0; i < 5; i++) {
        memset(buffer, 0, sizeof buffer);
        nw_value_to_bytes(node, key, 2, buffer, 0);
        bytes_put_int_le(cases[i].v, buffer + cases[i].at);
        const int32_t nsize = cases[i].at == 0 ? cases[i].v : size;
        CHECK_EQ(parse_in_buffer(buffer, size + 64, nsize, &e), ERR_FORMAT);
        CHECK(strcmp(e.java, "StreamFormatException") == 0);
        CHECK(starts_with(e.text, cases[i].start));
        if (!starts_with(e.text, cases[i].start)) {
            printf("    at %d, %d: %s\n", (int) cases[i].at, (int) cases[i].v, e.text);
        }
    }
    NFIX_END(&f);
}

const struct test snode_tests[] = {
    TEST_ENTRY(snode_refuses_bad_klongs),
    TEST_ENTRY(snode_refuses_bad_key),
    TEST_ENTRY(snode_top_refusals),
    TEST_ENTRY(snode_key_refusals),
    TEST_ENTRY(snode_value_refusals),
    TEST_END
};
