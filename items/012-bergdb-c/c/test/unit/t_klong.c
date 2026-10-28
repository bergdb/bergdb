/* Unit tests of klong (bergdb 012-04): Java's @Nano tests of Klong, ported,
 * and edge cases. Java's exact outputs are in t_vectors.c. */
#include <stdlib.h>
#include "test.h"
#include "keys.h"
#include "klong.h"

/* Java's createKey(byte[]) of StringUtil.toBytes(s): the UTF-8 bytes. */
static int64_t key_of(const char *s) {
    return kl_create_key((const uint8_t *) s, (int32_t) strlen(s));
}

/* Java's private Klong.createKey(String): of the ikey's bkey. */
static int64_t key_of_ikey(const char *s) {
    uint8_t b[KL_MAX_SIZE];
    int32_t n = (int32_t) strlen(s);
    if (n > KL_MAX_SIZE || !keys_ikey_to_bkey((const uint8_t *) s, n, b)) {
        test_fail_(__FILE__, __LINE__, "key_of_ikey: bad key");
        return 0;
    }
    return kl_create_key(b, n);
}

/* Java's getKeyString: the klong's bkey as an ikey, into s. */
static void key_string(int64_t klong, char *s) {
    uint8_t b[KL_MAX_SIZE];
    int32_t n = kl_get_key(klong, b);
    keys_bkey_to_ikey(b, n, (uint8_t *) s);
    s[n] = '\0';
}

/* Klong.testPrefixLength1. */
TEST(klong_prefix_length1) {
    int64_t k1 = key_of("ab1");
    int64_t k2 = key_of("ab2");
    CHECK_EQ(kl_prefix_length(k1, k2), 2);
    CHECK_EQ(kl_prefix_length(k2, k1), 2);
}

/* Klong.testPrefixLength2. */
TEST(klong_prefix_length2) {
    int64_t k1 = key_of("abc");
    int64_t k2 = key_of("abcd11");
    int64_t k3 = key_of("");
    int64_t k4 = key_of("abcdefg");
    int64_t k5 = key_of("abcdefg");
    int64_t k6 = key_of("Prag");
    CHECK_EQ(kl_prefix_length(k1, k2), 3);
    CHECK_EQ(kl_prefix_length(k2, k1), 3);
    CHECK_EQ(kl_prefix_length(k1, k3), 0);
    CHECK_EQ(kl_prefix_length(k3, k1), 0);
    CHECK_EQ(kl_prefix_length(k1, k6), 0);
    CHECK_EQ(kl_prefix_length(k4, k5), 7);
    CHECK_EQ(kl_prefix_length(k2, k4), 4);
}

/* Klong.testPrefixLength3. */
TEST(klong_prefix_length3) {
    int64_t k1 = key_of("a1");
    int64_t k2 = key_of("a2");
    CHECK_EQ(kl_prefix_length(k1, k2), 1);
    CHECK_EQ(kl_prefix_length(k2, k1), 1);
}

/* Each length of a common prefix, 0 to 7, of keys of 7 bytes, and of a
 * shorter key: never more than its length. */
TEST(klong_prefix_length_each) {
    for (int32_t p = 0; p <= 7; p++) {
        uint8_t a[7] = { 1, 2, 3, 4, 5, 6, 7 };
        uint8_t b[7] = { 1, 2, 3, 4, 5, 6, 7 };
        if (p < 7) {
            b[p] = 0xff;
        }
        CHECK_EQ(kl_prefix_length(kl_create_key(a, 7), kl_create_key(b, 7)), p);
        for (int32_t n = 0; n <= 7; n++) {
            int32_t expected = p < n ? p : n;
            CHECK_EQ(kl_prefix_length(kl_create_key(a, n), kl_create_key(b, 7)), expected);
        }
    }
}

/* Klong.testTime, and the ends of the range. */
TEST(klong_time) {
    const int64_t times[] = { 1, 123, INT64_C(123456789012345), INT64_C(2222222233333),
        KL_MIN_TIME, KL_MAX_TIME };
    for (int i = 0; i < 6; i++) {
        int64_t value = kl_create_time(times[i]);
        CHECK_EQ(kl_get_time(value), times[i]);
        CHECK_EQ(kl_get_type(value), KL_TYPE_TIME);
        CHECK_EQ(value, times[i]);          /* the type bits are 0 */
    }
    /* NULL is one beyond the times: a TIME klong of KL_MAX_TIME + 1. */
    CHECK_EQ(KL_NULL, KL_MAX_TIME + 1);
    CHECK(kl_is_time(KL_NULL));
}

/* Klong.testLength. */
TEST(klong_length) {
    int64_t v = 0;
    v = kl_set_header(v, KL_TYPE_KEY, 4);
    CHECK_EQ(kl_get_length(v), 4);
    v = kl_set_header(v, KL_TYPE_KEY, 1);
    CHECK_EQ(kl_get_length(v), 1);
    v = kl_set_header(v, KL_TYPE_KEY, 7);
    CHECK_EQ(kl_get_length(v), 7);
}

/* Klong.testHeader. */
TEST(klong_header) {
    int64_t v = key_of_ikey("abc");
    CHECK_EQ(kl_get_length(v), 3);
    CHECK_EQ(kl_get_type(v), KL_TYPE_KEY);
    v = key_of_ikey("a");
    CHECK_EQ(kl_get_length(v), 1);
    CHECK_EQ(kl_get_type(v), KL_TYPE_KEY);
    v = key_of_ikey("1234567");
    CHECK_EQ(kl_get_length(v), 7);
}

/* Klong.testIntType. */
TEST(klong_int_type) {
    CHECK_EQ(kl_get_int_type(key_of_ikey("abc")), KL_INT_TYPE_KEY);
    CHECK_EQ(kl_get_int_type(kl_create_time(1)), KL_INT_TYPE_TIME);
    CHECK_EQ(kl_get_int_type(kl_create_delete()), KL_INT_TYPE_DELETE_BITMAP);
}

/* Klong.testKey1, testKey2, testKey3: getKeyString of createKey(String). */
TEST(klong_key_string) {
    const char *const keys[] = { "aaa", "z", "1234567" };
    char s[KL_MAX_SIZE + 1];
    for (int i = 0; i < 3; i++) {
        key_string(key_of_ikey(keys[i]), s);
        CHECK(strcmp(s, keys[i]) == 0);
    }
}

/* Klong.testKey4. */
TEST(klong_key4) {
    const uint8_t bytes[] = { 0, 1, 3, 127, 200, 255 };
    uint8_t output[6];
    int64_t v = kl_create_key(bytes, 6);
    CHECK_EQ(kl_get_key(v, output), 6);
    CHECK_BYTES(output, bytes, 6);
}

/* Klong.testKey5. */
TEST(klong_key5) {
    const uint8_t bytes[] = { 3 };
    uint8_t output[1];
    int64_t v = kl_create_key(bytes, 1);
    CHECK_EQ(kl_get_key(v, output), 1);
    CHECK_BYTES(output, bytes, 1);
}

/* Bytes 0, 1, 0x7f, 0x80 and 0xff at every position of keys of 1 to 7
 * bytes: they come back, and the length is kept apart from them. */
TEST(klong_key_edge_bytes) {
    const uint8_t edges[] = { 0, 1, 0x7f, 0x80, 0xff };
    for (int e = 0; e < 5; e++) {
        for (int32_t n = 1; n <= 7; n++) {
            for (int32_t pos = 0; pos < n; pos++) {
                uint8_t key[7] = { 0x55, 0x55, 0x55, 0x55, 0x55, 0x55, 0x55 };
                uint8_t out[7];
                key[pos] = edges[e];
                int64_t v = kl_create_key(key, n);
                CHECK_EQ(kl_get_length(v), n);
                CHECK(kl_is_key(v));
                CHECK_EQ(kl_get_key(v, out), n);
                CHECK_BYTES(out, key, (size_t) n);
            }
        }
    }
}

/* Java's ByteArrayComparator: unsigned bytes, then the length. */
static int compare_bytes(const uint8_t *a, int32_t na, const uint8_t *b, int32_t nb) {
    int32_t n = na < nb ? na : nb;
    for (int32_t i = 0; i < n; i++) {
        if (a[i] != b[i]) {
            return a[i] < b[i] ? -1 : 1;
        }
    }
    return na == nb ? 0 : (na < nb ? -1 : 1);
}

struct bkey {
    uint8_t b[KL_MAX_SIZE];
    int32_t n;
};

static int cmp_by_bytes(const void *x, const void *y) {
    const struct bkey *a = x;
    const struct bkey *b = y;
    return compare_bytes(a->b, a->n, b->b, b->n);
}

/* Klong.testSortOrder1's second comparator: by compare values. */
static int cmp_by_compare_value(const void *x, const void *y) {
    const struct bkey *a = x;
    const struct bkey *b = y;
    int64_t v1 = kl_get_compare_value(kl_create_key(a->b, a->n));
    int64_t v2 = kl_get_compare_value(kl_create_key(b->b, b->n));
    int64_t diff = v1 - v2;
    return diff > 0 ? 1 : (diff < 0 ? -1 : 0);
}

/* Klong.testSortOrder1: two sorts agree, with the edge keys too. */
TEST(klong_sort_order) {
    struct bkey keys1[40], keys2[40];
    const char *const strings[] = { "gust", "", "bertil", "abc", "frasse", "gustav", "a", "gu" };
    int n = 0;
    memset(keys1, 0, sizeof keys1);
    for (int i = 0; i < 8; i++, n++) {
        keys1[n].n = (int32_t) strlen(strings[i]);
        memcpy(keys1[n].b, strings[i], (size_t) keys1[n].n);
    }
    keys1[n].b[0] = 'a';
    keys1[n++].n = 3;                       /* {'a', 0, 0} */
    keys1[n].b[0] = 'a';
    keys1[n++].n = 2;                       /* {'a', 0} */
    keys1[n].b[1] = 1;
    keys1[n++].n = 2;                       /* {0, 1} */
    const uint8_t edges[] = { 0, 1, 0x7f, 0x80, 0xff };
    for (int e = 0; e < 5; e++) {
        keys1[n].b[0] = edges[e];
        keys1[n++].n = 1;
        keys1[n].b[0] = 'a';
        keys1[n].b[1] = edges[e];
        keys1[n++].n = 2;
        memset(keys1[n].b, edges[e], 7);
        keys1[n++].n = 7;
    }
    memcpy(keys2, keys1, sizeof keys1);
    qsort(keys1, (size_t) n, sizeof keys1[0], cmp_by_bytes);
    qsort(keys2, (size_t) n, sizeof keys2[0], cmp_by_compare_value);
    for (int i = 0; i < n; i++) {
        CHECK_EQ(keys1[i].n, keys2[i].n);
        CHECK_BYTES(keys1[i].b, keys2[i].b, (size_t) keys1[i].n);
    }
}

/* Klong.testCreateKlongs. */
TEST(klong_create_klongs) {
    const uint8_t bytes0[2] = { 0, 0 };
    const uint8_t bytes1[2] = { 1, 0 };
    int64_t k0 = kl_create_key(bytes0, 2);
    int64_t k1 = kl_create_key(bytes1, 2);
    CHECK(k0 != k1);
    CHECK(kl_get_compare_value(k1) > kl_get_compare_value(k0));
}

/* Klong.testCreateCompareValueTwoWays: random keys of 1 to 6 bytes; with 0
 * and 7 too. */
TEST(klong_compare_value_two_ways) {
    uint64_t r = 6;
    for (int i = 0; i < 200; i++) {
        uint8_t buffer[7];
        int32_t length = i < 100 ? test_random_below(&r, 6) + 1 : test_random_below(&r, 8);
        for (int32_t j = 0; j < length; j++) {
            buffer[j] = (uint8_t) test_random(&r);
        }
        int64_t c1 = kl_create_compare_value(buffer, length);
        int64_t c2 = kl_get_compare_value(kl_create_key(buffer, length));
        CHECK_EQ(c1, c2);
        CHECK(c1 >= 0);                     /* compare values are non-negative */
        CHECK_EQ(kl_compare_value_to_key_klong(c1), kl_create_key(buffer, length));
    }
}

/* Klong.tDeleteBits: Java's DELETE_BITS[i] is 2^i, what kl_delete sets. */
TEST(klong_delete_bits) {
    CHECK_EQ(kl_delete(0, 15), INT64_C(1) << 15);
    CHECK_EQ(kl_delete(0, 61), INT64_C(1) << 61);
    CHECK_EQ(kl_delete(0, 0), 1);
}

/* Klong.tDelete1. */
TEST(klong_delete1) {
    int64_t k = kl_create_delete();
    k = kl_delete(k, 5);
    k = kl_delete(k, 33);
    CHECK(!kl_is_deleted(k, 0));
    CHECK(!kl_is_deleted(k, 4));
    CHECK(kl_is_deleted(k, 5));
    CHECK(!kl_is_deleted(k, 20));
    CHECK(kl_is_deleted(k, 33));
    CHECK(!kl_is_deleted(k, 34));
    CHECK(!kl_is_deleted(k, 61));
}

/* All 62 bits: DELETE_ALL_BITMAP, still a delete bitmap. */
TEST(klong_delete_all) {
    int64_t k = kl_create_delete();
    CHECK_EQ(k, KL_DELETE_NONE_BITMAP);
    for (int32_t i = 0; i < 62; i++) {
        CHECK(!kl_is_deleted(k, i));
        k = kl_delete(k, i);
        CHECK(kl_is_deleted(k, i));
    }
    CHECK_EQ(k, KL_DELETE_ALL_BITMAP);
    CHECK_EQ(kl_get_int_type(k), KL_INT_TYPE_DELETE_BITMAP);
    CHECK(!kl_is_key(k) && !kl_is_time(k));
}

/* Klong.testIsKey. */
TEST(klong_is_key) {
    const uint8_t b[3] = { 1, 2, 3 };
    CHECK(kl_is_key(kl_create_key(b, 3)));
    CHECK(!kl_is_key(kl_create_time(1000)));
}

/* The empty key: a KEY klong of length 0, EMPTY_KEY. */
TEST(klong_empty_key) {
    const uint8_t b[1] = { 0 };
    int64_t k = kl_create_key(b, 0);
    CHECK_EQ(k, KL_EMPTY_KEY);
    CHECK_EQ(kl_get_length(k), 0);
    CHECK_EQ(kl_get_compare_value(k), 0);
    CHECK(kl_is_key(k));
}

const struct test klong_tests[] = {
    TEST_ENTRY(klong_prefix_length1),
    TEST_ENTRY(klong_prefix_length2),
    TEST_ENTRY(klong_prefix_length3),
    TEST_ENTRY(klong_prefix_length_each),
    TEST_ENTRY(klong_time),
    TEST_ENTRY(klong_length),
    TEST_ENTRY(klong_header),
    TEST_ENTRY(klong_int_type),
    TEST_ENTRY(klong_key_string),
    TEST_ENTRY(klong_key4),
    TEST_ENTRY(klong_key5),
    TEST_ENTRY(klong_key_edge_bytes),
    TEST_ENTRY(klong_sort_order),
    TEST_ENTRY(klong_create_klongs),
    TEST_ENTRY(klong_compare_value_two_ways),
    TEST_ENTRY(klong_delete_bits),
    TEST_ENTRY(klong_delete1),
    TEST_ENTRY(klong_delete_all),
    TEST_ENTRY(klong_is_key),
    TEST_ENTRY(klong_empty_key),
    TEST_END
};
