/* Unit tests of checksum (bergdb 012-04): Java's @Nano tests of
 * NodeChecksum, ported, and edge cases. Java's exact outputs are in
 * t_vectors.c. */
#include "test.h"
#include "bytes.h"
#include "checksum.h"

/* NodeChecksum.test0: the example of Wikipedia's "Fletcher's checksum". */
TEST(checksum_example) {
    const uint8_t data[] = { 0x01, 0x02 };
    CHECK_EQ(cks_sum(data, 0, 2), 0x0403);
}

/* NodeChecksum.testWithLongArray1. */
TEST(checksum_with_long_array1) {
    const uint8_t data[] = { 0x01, 0x02, 0xff, 0x10, 0x00, 0x01, 0x02, 0x03 };
    int64_t l = bytes_get_long_le(data);
    CHECK_EQ(cks_sum_longs(&l, 0, 1), cks_sum(data, 0, 8));
}

/* NodeChecksum.testWithLongArray2. */
TEST(checksum_with_long_array2) {
    const uint8_t data[] = {
        0x01, 0x02, 0xff, 0x10, 0x20, 0x21, 0x23, 0x24,
        0xff, 0xff, 0xff, 0xff, 0x0f, 0x0f, 0x0f, 0x0f
    };
    int64_t longs[2] = { bytes_get_long_le(data), bytes_get_long_le(data + 8) };
    CHECK_EQ(cks_sum_longs(longs, 0, 2), cks_sum(data, 0, 16));
}

/* NodeChecksum.testZeroReplace. */
TEST(checksum_zero_replace) {
    const uint8_t data1[] = { 0x01, 0x02, 0xff, 0x10, 0x00, 0x01, 0x02, 0x03 };
    const uint8_t data2[] = { 0x01, 0x00, 0x00, 0x10, 0x00, 0x01, 0x02, 0x03 };
    CHECK_EQ(cks_sum_with_zero_replace(data1, 0, 8, 1), cks_sum(data2, 0, 8));
}

/* Nothing: 0. A byte 0xff adds 0 modulo 255, and so does a run of them. */
TEST(checksum_edges) {
    const uint8_t ff[4] = { 0xff, 0xff, 0xff, 0xff };
    const uint8_t one[1] = { 1 };
    CHECK_EQ(cks_sum(ff, 0, 0), 0);
    CHECK_EQ(cks_sum(ff, 0, 4), 0);
    CHECK_EQ(cks_sum(one, 0, 1), 0x0101);
    CHECK_EQ(cks_sum_longs(NULL, 0, 0), 0);
    int64_t minus1 = -1;
    CHECK_EQ(cks_sum_longs(&minus1, 0, 1), 0);
}

/* The range: sum(data, off, len) is the sum of those bytes alone; a
 * replacement outside the range changes nothing, and one at its last byte
 * zeroes only that byte. */
TEST(checksum_ranges) {
    uint8_t data[64];
    uint8_t copy[64];
    uint64_t r = 5;
    for (int i = 0; i < 64; i++) {
        data[i] = (uint8_t) test_random(&r);
    }
    for (int32_t off = 0; off < 10; off++) {
        for (int32_t len = 0; off + len <= 64; len += 7) {
            int32_t sum = cks_sum(data, off, len);
            CHECK_EQ(cks_sum(data + off, 0, len), sum);
            CHECK_EQ(cks_sum_with_zero_replace(data, off, len, off + len), sum);
            CHECK_EQ(cks_sum_with_zero_replace(data, off, len, off - 2), sum);
            if (len >= 2) {
                memcpy(copy, data, 64);
                copy[off + len - 1] = 0;
                CHECK_EQ(cks_sum_with_zero_replace(data, off, len, off + len - 1),
                        cks_sum(copy, off, len));
                memcpy(copy, data, 64);
                copy[off] = 0;
                CHECK_EQ(cks_sum_with_zero_replace(data, off, len, off - 1),
                        cks_sum(copy, off, len));
            }
        }
    }
}

/* A long run stays below 255 in each half: no overflow of the int sums. */
TEST(checksum_long_run) {
    static uint8_t data[1 << 20];
    memset(data, 0xfe, sizeof data);
    int32_t sum = cks_sum(data, 0, (int32_t) sizeof data);
    CHECK((sum & 0xff) < 255 && (sum >> 8) < 255);
    /* 2^20 bytes of 254: sum1 = 2^20 * 254 mod 255. */
    int64_t s1 = ((int64_t) 1 << 20) * 254 % 255;
    CHECK_EQ(sum & 0xff, s1);
}

const struct test checksum_tests[] = {
    TEST_ENTRY(checksum_example),
    TEST_ENTRY(checksum_with_long_array1),
    TEST_ENTRY(checksum_with_long_array2),
    TEST_ENTRY(checksum_zero_replace),
    TEST_ENTRY(checksum_edges),
    TEST_ENTRY(checksum_ranges),
    TEST_ENTRY(checksum_long_run),
    TEST_END
};
