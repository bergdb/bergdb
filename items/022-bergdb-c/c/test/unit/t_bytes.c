/* Unit tests of bytes (bergdb 012-04): Java's @Nano tests of Bytes, ported,
 * and edge cases. Java's exact outputs are in t_vectors.c. */
#include <float.h>
#include <math.h>
#include "test.h"
#include "bytes.h"
#include "jsem.h"

/* Bytes.testFloatLE: written at offset i and read back, NaN too. */
TEST(bytes_float_le) {
    const float values[] = { 1.0f, 0.0f, FLT_TRUE_MIN, FLT_MAX, NAN, 123.45f, -0.0012f };
    const int n = (int) (sizeof values / sizeof values[0]);
    uint8_t array[10 + 7] = { 0 };
    for (int i = 0; i < n; i++) {
        bytes_put_float_le(values[i], array + i);
        CHECK_EQ(j_float_bits(bytes_get_float_le(array + i)), j_float_bits(values[i]));
    }
}

/* Bytes.testDoubleLE. */
TEST(bytes_double_le) {
    const double values[] = { 1.0, 0.0, DBL_TRUE_MIN, DBL_MAX, NAN, 123.45, -0.0012 };
    const int n = (int) (sizeof values / sizeof values[0]);
    uint8_t array[10 + 7] = { 0 };
    for (int i = 0; i < n; i++) {
        bytes_put_double_le(values[i], array + i);
        CHECK_EQ(j_double_bits(bytes_get_double_le(array + i)), j_double_bits(values[i]));
    }
}

/* Bytes.testShortLE. */
TEST(bytes_short_le) {
    const int16_t shorts[] = { 0, INT16_MIN, INT16_MAX, 12345, -1, -32000, 32000 };
    uint8_t array[10 + 7] = { 0 };
    for (int i = 0; i < 7; i++) {
        bytes_put_short_le(shorts[i], array + i);
        CHECK_EQ(bytes_get_short_le(array + i), shorts[i]);
    }
}

/* Java's ByteBuffer, little-endian or big-endian, as the reference. */
static void ref_long(int64_t v, uint8_t *p, int big_endian) {
    for (int k = 0; k < 8; k++) {
        p[big_endian ? 7 - k : k] = (uint8_t) ((uint64_t) v >> (8 * k));
    }
}

/* Bytes.testLongsToBytesLE. */
TEST(bytes_longs_to_le) {
    const int64_t longs[] = { 123, INT64_C(111222333444), -1000 };
    uint8_t bytes1[24], bytes2[24];
    for (int i = 0; i < 3; i++) {
        ref_long(longs[i], bytes1 + 8 * i, 0);
    }
    bytes_longs_to_le(longs, 3, bytes2);
    CHECK_BYTES(bytes1, bytes2, 24);
}

/* Bytes.testLongsToBytesLE2: longsToBytesLE(longs, 1, 2, bytes, 19). */
TEST(bytes_longs_to_le2) {
    const int64_t longs[] = { 123, INT64_C(111222333444), -1000 };
    uint8_t bytes[40] = { 0 };
    bytes_longs_to_le(longs + 1, 2, bytes + 19);
    CHECK_EQ(bytes_get_long_le(bytes + 19), INT64_C(111222333444));
    CHECK_EQ(bytes_get_long_le(bytes + 19 + 8), -1000);
    CHECK(bytes[18] == 0 && bytes[35] == 0);
}

/* Bytes.testLongToBytesBE and testLongToBytesLE: offset 3 of 12 bytes, as
 * ByteBuffer.putLong writes them, and nothing else written. */
TEST(bytes_long_vs_bytebuffer) {
    uint64_t r = 1;
    for (int i = 0; i < 100; i++) {
        int64_t v = test_random(&r);
        for (int be = 0; be <= 1; be++) {
            uint8_t bytes1[12] = { 0 }, bytes2[12] = { 0 };
            if (be) {
                bytes_put_long_be(v, bytes1 + 3);
            } else {
                bytes_put_long_le(v, bytes1 + 3);
            }
            ref_long(v, bytes2 + 3, be);
            CHECK_BYTES(bytes1, bytes2, 12);
        }
    }
}

/* Bytes.testLongBE. */
TEST(bytes_long_be) {
    int64_t long3 = INT64_MAX - 1000;
    uint8_t temp[16];
    bytes_put_long_be(28000000, temp);
    bytes_put_long_be(long3, temp + 8);
    CHECK_EQ(bytes_get_long_be(temp + 8), long3);
    CHECK_EQ(bytes_get_long_be(temp), 28000000);
}

/* Bytes.testLongBE2, testLongLE and testLongLE2: random longs at offsets. */
TEST(bytes_long_round_trip) {
    uint64_t r = 2;
    uint8_t bytes[110];
    for (int i = 0; i < 100; i++) {
        int offset = i % (110 - 10);
        int64_t v = test_random(&r);
        bytes_put_long_le(v, bytes + offset);
        CHECK_EQ(bytes_get_long_le(bytes + offset), v);
        bytes_put_long_be(v, bytes + offset);
        CHECK_EQ(bytes_get_long_be(bytes + offset), v);
    }
}

/* Bytes.testIntLE and testIntBE. */
TEST(bytes_int_round_trip) {
    uint64_t r = 3;
    uint8_t buffer[110];
    for (int i = 0; i < 100; i++) {
        int32_t v = j_l2i(test_random(&r));
        int offset = i % 100;
        bytes_put_int_le(v, buffer + offset);
        CHECK_EQ(bytes_get_int_le(buffer + offset), v);
        bytes_put_int_be(v, buffer + offset);
        CHECK_EQ(bytes_get_int_be(buffer + offset), v);
    }
}

/* Bytes.testUShortLE and testUShortLE2: values in 0 to 65535 at offset 1. */
TEST(bytes_ushort_le) {
    uint64_t r = 4;
    uint8_t bytes[5];
    for (int i = 0; i < 20; i++) {
        int32_t value = test_random_below(&r, 1 << 16);
        CHECK(bytes_put_ushort_le(value, bytes + 1));
        CHECK_EQ(bytes_get_ushort_le(bytes + 1), value);
    }
    for (int32_t value = 0; value < 65536; value += 257) {
        CHECK(bytes_put_ushort_le(value, bytes));
        CHECK_EQ(bytes_get_ushort_le(bytes), value);
    }
}

/* Out of range: refused, as Java throws IllegalArgumentException, and
 * nothing written. */
TEST(bytes_ushort_refused) {
    const int32_t bad[] = { -1, 65536, INT32_MIN, INT32_MAX, -65536 };
    uint8_t bytes[2] = { 0x5a, 0xa5 };
    for (int i = 0; i < 5; i++) {
        CHECK(!bytes_put_ushort_le(bad[i], bytes));
        CHECK(bytes[0] == 0x5a && bytes[1] == 0xa5);
    }
}

/* Bytes.testUnsigned: Java's unsigned(byte) is C's uint8_t; a Java byte
 * read from a buffer is j_l2b of it. */
TEST(bytes_unsigned) {
    const uint8_t b[] = { 123, 0xff, 127, 0x80 };
    CHECK_EQ(b[0], 123);
    CHECK_EQ(b[1], 255);
    CHECK_EQ(b[2], 127);
    CHECK_EQ(b[3], 128);
    CHECK_EQ(j_l2b(b[1]), -1);
    CHECK_EQ(j_l2b(b[3]), -128);
    CHECK_EQ((uint8_t) j_l2b(-128), 128);
}

/* The edge bytes 0, 1, 0x7f, 0x80 and 0xff in each position: read as
 * unsigned bytes, never sign-extended into the next. */
TEST(bytes_edge_bytes) {
    const uint8_t edges[] = { 0, 1, 0x7f, 0x80, 0xff };
    for (int e = 0; e < 5; e++) {
        for (int pos = 0; pos < 8; pos++) {
            uint8_t b[8] = { 0 };
            b[pos] = edges[e];
            CHECK_EQ(bytes_get_long_le(b), (int64_t) ((uint64_t) edges[e] << (8 * pos)));
            CHECK_EQ(bytes_get_long_be(b), (int64_t) ((uint64_t) edges[e] << (8 * (7 - pos))));
            if (pos < 4) {
                CHECK_EQ(bytes_get_int_le(b), (int32_t) ((uint32_t) edges[e] << (8 * pos)));
                CHECK_EQ(bytes_get_int_be(b),
                        (int32_t) ((uint32_t) edges[e] << (8 * (3 - pos))));
            }
            if (pos < 2) {
                CHECK_EQ(bytes_get_ushort_le(b), edges[e] << (8 * pos));
                CHECK_EQ(bytes_get_short_le(b), (int16_t) (uint16_t) (edges[e] << (8 * pos)));
            }
        }
    }
}

/* shortToBytesLE takes a long and writes its low 16 bits. */
TEST(bytes_short_of_long) {
    uint8_t b[3] = { 0, 0, 0x77 };
    bytes_put_short_le(INT64_C(0x123456789abc), b);
    CHECK(b[0] == 0xbc && b[1] == 0x9a && b[2] == 0x77);
    CHECK_EQ(bytes_get_short_le(b), (int16_t) (uint16_t) 0x9abc);
}

const struct test bytes_tests[] = {
    TEST_ENTRY(bytes_float_le),
    TEST_ENTRY(bytes_double_le),
    TEST_ENTRY(bytes_short_le),
    TEST_ENTRY(bytes_longs_to_le),
    TEST_ENTRY(bytes_longs_to_le2),
    TEST_ENTRY(bytes_long_vs_bytebuffer),
    TEST_ENTRY(bytes_long_be),
    TEST_ENTRY(bytes_long_round_trip),
    TEST_ENTRY(bytes_int_round_trip),
    TEST_ENTRY(bytes_ushort_le),
    TEST_ENTRY(bytes_ushort_refused),
    TEST_ENTRY(bytes_unsigned),
    TEST_ENTRY(bytes_edge_bytes),
    TEST_ENTRY(bytes_short_of_long),
    TEST_END
};
