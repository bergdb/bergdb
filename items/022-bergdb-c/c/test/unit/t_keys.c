/* Unit tests of keys (bergdb 012-04): Java's @Nano tests of Keys, ported,
 * and the edge cases of 012-04, section 4. Java's exact outputs are in
 * t_vectors.c. */
#include "test.h"
#include "keys.h"
#include "klong.h"

#define MAXSEG 16

/* Java's Keys.toSegments(String): the ikey's bkey's segments; their number,
 * or -1 if the ikey is refused. */
static int32_t segments_of(const char *ikey, int64_t *seg) {
    uint8_t b[MAXSEG * KL_MAX_SIZE];
    int32_t n = (int32_t) strlen(ikey);
    if (n >= MAXSEG * KL_MAX_SIZE || !keys_ikey_to_bkey((const uint8_t *) ikey, n, b)) {
        return -1;
    }
    keys_to_segments(b, n, seg);
    return keys_segment_count(n);
}

/* Keys.testByteSize0. */
TEST(keys_byte_size) {
    const int32_t sizes[] = { 0, 1, 6, 7, 8, 40, 27, 28, 29 };
    uint8_t bytes[40] = { 0 };
    int64_t seg[MAXSEG];
    for (int i = 0; i < 9; i++) {
        keys_to_segments(bytes, sizes[i], seg);
        CHECK_EQ(keys_byte_size(seg, keys_segment_count(sizes[i])), sizes[i]);
    }
}

/* Keys.testConversion0: ikey to segments and back. */
TEST(keys_conversion) {
    const char *const strings[] = { "a", "dir/f1.txt", " ", "Stange\n\r  next line" };
    int64_t seg[MAXSEG];
    uint8_t bkey[MAXSEG * KL_MAX_SIZE];
    char ikey[MAXSEG * KL_MAX_SIZE + 1];
    for (int i = 0; i < 4; i++) {
        int32_t ns = segments_of(strings[i], seg);
        REQUIRE(ns > 0);
        int32_t n = keys_to_bytes(seg, ns, bkey);
        keys_bkey_to_ikey(bkey, n, (uint8_t *) ikey);
        ikey[n] = '\0';
        CHECK(strcmp(ikey, strings[i]) == 0);
    }
}

/* Keys.testConversion1: the empty key is refused. And the bytes 0xfe and
 * 0xff, which UTF-8 never has, at any position. */
TEST(keys_refused) {
    uint8_t out[8];
    int64_t seg[MAXSEG];
    CHECK_EQ(segments_of("", seg), -1);
    CHECK(!keys_ikey_to_bkey((const uint8_t *) "x", 0, out));
    for (int pos = 0; pos < 3; pos++) {
        uint8_t k[3] = { 'a', 'b', 'c' };
        k[pos] = 0xfe;
        CHECK(!keys_ikey_to_bkey(k, 3, out));
        k[pos] = 0xff;
        CHECK(!keys_ikey_to_bkey(k, 3, out));
        k[pos] = 0xfd;                      /* the largest byte allowed: bkey 0xff */
        CHECK(keys_ikey_to_bkey(k, 3, out));
        CHECK(out[pos] == 0xff);
    }
}

/* ikey bytes to bkey bytes and back: '/' is 1, every other byte plus 2. */
TEST(keys_bkey_bytes) {
    const uint8_t ikey[] = { 0, 1, 0x7f, 0x80, 0xfd, '/', '.', '0' };
    const uint8_t bkey[] = { 2, 3, 0x81, 0x82, 0xff, 1, '0', '2' };
    uint8_t out[8];
    CHECK(keys_ikey_to_bkey(ikey, 8, out));
    CHECK_BYTES(out, bkey, 8);
    keys_bkey_to_ikey(bkey, 8, out);
    CHECK_BYTES(out, ikey, 8);
    /* A bkey byte 0 has no ikey byte; Java gives (byte) -2, as C does. */
    const uint8_t zero[1] = { 0 };
    keys_bkey_to_ikey(zero, 1, out);
    CHECK(out[0] == 0xfe);
}

/* Keys.testLongs: compareUnsignedLongs, through compareArrays of one long. */
TEST(keys_compare_unsigned) {
    int64_t a, b;
#define CU(x, y) (a = (x), b = (y), keys_compare_arrays(&a, 1, &b, 1))
    CHECK(CU(3, 1) > 0);
    CHECK(CU(INT64_C(111222333444), INT64_C(111222333444)) == 0);
    CHECK(CU(-1, -1) == 0);
    CHECK(CU(0, 0) == 0);
    CHECK(CU(-1, INT64_C(111222333444)) > 0);
    CHECK(CU(INT64_C(111222333444), -1) < 0);
    CHECK(CU(1, 44) < 0);
    CHECK(CU(INT64_MIN, INT64_MAX) > 0);
    CHECK(CU(0, INT64_MIN) < 0);
#undef CU
}

/* Keys.testArrays. */
TEST(keys_compare_arrays) {
    const int64_t e[1] = { 0 };
    const int64_t a123[] = { 1, 2, 3 }, a124[] = { 1, 2, 4 }, a1234[] = { 1, 2, 3, 4 };
    const int64_t x = INT64_C(123), y = INT64_C(-111222333444), one = 1, zero = 0;
    CHECK(keys_compare_arrays(e, 0, e, 0) == 0);
    CHECK(keys_compare_arrays(&x, 1, &x, 1) == 0);
    CHECK(keys_compare_arrays(&y, 1, &y, 1) == 0);
    CHECK(keys_compare_arrays(e, 0, &one, 1) < 0);
    CHECK(keys_compare_arrays(&one, 1, &zero, 1) > 0);
    CHECK(keys_compare_arrays(&zero, 1, &one, 1) < 0);
    CHECK(keys_compare_arrays(a123, 3, a124, 3) < 0);
    CHECK(keys_compare_arrays(a124, 3, a123, 3) > 0);
    CHECK(keys_compare_arrays(a123, 3, a1234, 4) < 0);
    CHECK(keys_compare_arrays(a1234, 4, a123, 3) > 0);
    /* compareKeys compares signed: the difference with a negative long. */
    const int64_t m = -1;
    CHECK(keys_compare_arrays(&m, 1, &one, 1) > 0);
    CHECK(keys_compare_keys(&m, 1, &one, 1) < 0);
}

/* Keys.testPrefix1. */
TEST(keys_prefix1) {
    int64_t k1[MAXSEG], k2[MAXSEG];
    int32_t n1 = segments_of("dir/customers/", k1);
    int32_t n2 = segments_of("dir/customers/anna", k2);
    CHECK(keys_is_prefix(k1, n1, k2, n2));
    CHECK(!keys_is_prefix(k2, n2, k1, n1));
}

/* Keys.testPrefix2. */
TEST(keys_prefix2) {
    int64_t k1[MAXSEG], k2[MAXSEG], k3[MAXSEG], k4[MAXSEG];
    int32_t n1 = segments_of("dir/customers/", k1);
    int32_t n2 = segments_of("dir/customers/anna", k2);
    int32_t n3 = segments_of("dir/customers/", k3);
    int32_t n4 = segments_of("dir/cust", k4);
    CHECK(keys_is_prefix(k1, n1, k2, n2));
    CHECK(keys_is_prefix(k4, n4, k1, n1));
    CHECK(keys_is_prefix(k4, n4, k2, n2));
    CHECK(!keys_is_prefix(k1, n1, k3, n3));
    CHECK(!keys_is_prefix(k2, n2, k1, n1));
    CHECK(!keys_is_prefix(k1, n1, k4, n4));
    CHECK(!keys_is_prefix(k2, n2, k4, n4));
}

/* Keys of 6, 7, 8, 13 and 14 bytes, and more: the segments' number and
 * lengths (a key of 7 bytes has two segments, the second of length 0), and
 * the bytes back, with each edge byte. */
TEST(keys_segment_lengths) {
    const int32_t sizes[] = { 1, 6, 7, 8, 13, 14, 15, 20, 21, 22 };
    const int32_t counts[] = { 1, 1, 2, 2, 2, 3, 3, 3, 4, 4 };
    const int32_t last[] = { 1, 6, 0, 1, 6, 0, 1, 6, 0, 1 };
    const uint8_t edges[] = { 0, 1, 0x7f, 0x80, 0xff };
    for (int i = 0; i < 10; i++) {
        for (int e = 0; e < 5; e++) {
            uint8_t key[32], out[33];
            int64_t seg[MAXSEG];
            int32_t n = sizes[i];
            for (int32_t j = 0; j < n; j++) {
                key[j] = (j % 3 == 1) ? edges[e] : (uint8_t) (j + 0x30);
            }
            CHECK_EQ(keys_segment_count(n), counts[i]);
            keys_to_segments(key, n, seg);
            CHECK_EQ(kl_get_length(seg[counts[i] - 1]), last[i]);
            for (int32_t s = 0; s < counts[i] - 1; s++) {
                CHECK_EQ(kl_get_length(seg[s]), 7);
            }
            for (int32_t s = 0; s < counts[i]; s++) {
                CHECK(seg[s] >= 0 && !kl_is_key(seg[s]));   /* compare values: no type bits */
            }
            CHECK_EQ(keys_byte_size(seg, counts[i]), n);
            memset(out, 0xab, sizeof out);
            CHECK_EQ(keys_to_bytes(seg, counts[i], out), n);
            CHECK_BYTES(out, key, (size_t) n);
            CHECK(out[n] == 0xab);
        }
    }
}

/* The empty bkey (the empty ikey is refused, but Java's toSegments takes an
 * empty byte array): one segment of length 0, the compare value 0. */
TEST(keys_empty_bkey) {
    const uint8_t b[1] = { 0 };
    int64_t seg[1] = { -1 };
    CHECK_EQ(keys_segment_count(0), 1);
    keys_to_segments(b, 0, seg);
    CHECK_EQ(seg[0], 0);
    CHECK_EQ(keys_byte_size(seg, 1), 0);
    CHECK_EQ(keys_hash(seg, 1), 37 * 37);
}

/* Java's ByteArrayComparator, as -1, 0 or 1. */
static int32_t compare_bytes(const uint8_t *a, int32_t na, const uint8_t *b, int32_t nb) {
    int32_t n = na < nb ? na : nb;
    for (int32_t i = 0; i < n; i++) {
        if (a[i] != b[i]) {
            return a[i] < b[i] ? -1 : 1;
        }
    }
    return na == nb ? 0 : (na < nb ? -1 : 1);
}

/* The segments order the keys as their bytes do, unsigned and then by
 * length, both compareKeys and compareArrays: random keys of 0 to 30 bytes
 * of the edge bytes and others, many with common prefixes. */
TEST(keys_order) {
    uint64_t r = 7;
    const uint8_t pool[] = { 0, 1, 2, 0x7f, 0x80, 0xfe, 0xff, 'a' };
    for (int i = 0; i < 3000; i++) {
        uint8_t a[30], b[30];
        int64_t sa[MAXSEG], sb[MAXSEG];
        int32_t na = test_random_below(&r, 31);
        int32_t nb = test_random_below(&r, 31);
        for (int32_t j = 0; j < na; j++) {
            a[j] = pool[test_random_below(&r, 8)];
        }
        /* b: a's prefix of a random length, then random bytes. */
        int32_t common = test_random_below(&r, (na < nb ? na : nb) + 1);
        for (int32_t j = 0; j < nb; j++) {
            b[j] = j < common ? a[j] : pool[test_random_below(&r, 8)];
        }
        keys_to_segments(a, na, sa);
        keys_to_segments(b, nb, sb);
        int32_t expected = compare_bytes(a, na, b, nb);
        int32_t ns_a = keys_segment_count(na), ns_b = keys_segment_count(nb);
        CHECK_EQ(keys_compare_keys(sa, ns_a, sb, ns_b), expected);
        CHECK_EQ(keys_compare_arrays(sa, ns_a, sb, ns_b), expected);
        CHECK(keys_are_equal(sa, ns_a, sb, ns_b) == (expected == 0));
        /* isPrefix: a strict prefix, by bytes. */
        bool prefix = na < nb && memcmp(a, b, (size_t) na) == 0;
        CHECK(keys_is_prefix(sa, ns_a, sb, ns_b) == prefix);
    }
}

/* hash: 37 for no segments, Effective Java's sum, never negative: also
 * where the sum is Long.MIN_VALUE (bergdb 005-21), which -sum leaves
 * negative and the mask makes 0. */
TEST(keys_hash_edges) {
    CHECK_EQ(keys_hash(NULL, 0), 37);
    const int64_t s1[] = { 5 };
    CHECK_EQ(keys_hash(s1, 1), 37 * 37 + 5);
    const int64_t s2[] = { 5, 7 };
    CHECK_EQ(keys_hash(s2, 2), (37 * 37 + 5) * 37 + 7);
    const int64_t min[] = { INT64_MAX - 37 * 37 + 1 };  /* the sum wraps to MIN */
    CHECK_EQ(keys_hash(min, 1), 0);
    const int64_t neg[] = { -(37 * 37) - 10 };         /* the sum is -10 */
    CHECK_EQ(keys_hash(neg, 1), 10);
    const int64_t m[] = { INT64_MIN };
    CHECK_EQ(keys_hash(m, 1), INT64_MAX - 37 * 37 + 1);
    uint64_t r = 8;
    for (int i = 0; i < 1000; i++) {
        int64_t seg[4];
        for (int j = 0; j < 4; j++) {
            seg[j] = test_random(&r);
        }
        CHECK(keys_hash(seg, 1 + i % 4) >= 0);
    }
}

const struct test keys_tests[] = {
    TEST_ENTRY(keys_byte_size),
    TEST_ENTRY(keys_conversion),
    TEST_ENTRY(keys_refused),
    TEST_ENTRY(keys_bkey_bytes),
    TEST_ENTRY(keys_compare_unsigned),
    TEST_ENTRY(keys_compare_arrays),
    TEST_ENTRY(keys_prefix1),
    TEST_ENTRY(keys_prefix2),
    TEST_ENTRY(keys_segment_lengths),
    TEST_ENTRY(keys_empty_bkey),
    TEST_ENTRY(keys_order),
    TEST_ENTRY(keys_hash_edges),
    TEST_END
};
