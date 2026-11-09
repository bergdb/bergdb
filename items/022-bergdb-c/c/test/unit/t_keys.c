/* Unit tests of keys (bergdb 012-04): Java's @Nano tests of Keys, ported,
 * and the edge cases of 012-04, section 4; since 022-02, 021-05's and
 * 021-06's (an ikey well-formed UTF-8, a bkey without an ikey). Java's exact
 * outputs are in t_vectors.c. */
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
        CHECK(keys_bkey_to_ikey(bkey, n, (uint8_t *) ikey));
        ikey[n] = '\0';
        CHECK(strcmp(ikey, strings[i]) == 0);
    }
}

/* Keys.testConversion1: the empty key is refused. And the bytes 0xfe and
 * 0xff, which UTF-8 never has, at any position, and since 022-02 (021-05)
 * 0xfd and 0xf5, which it never has either; the largest bytes it has are
 * those of U+10FFFF, F4 8F BF BF. */
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
        k[pos] = 0xfd;
        CHECK(!keys_ikey_to_bkey(k, 3, out));
        k[pos] = 0xf5;
        CHECK(!keys_ikey_to_bkey(k, 3, out));
        k[pos] = 0x7f;                      /* the largest byte alone: bkey 0x81 */
        CHECK(keys_ikey_to_bkey(k, 3, out));
        CHECK(out[pos] == 0x81);
    }
    const uint8_t max[] = { 'a', 0xf4, 0x8f, 0xbf, 0xbf };
    const uint8_t max_bkey[] = { 'a' + 2, 0xf6, 0x91, 0xc1, 0xc1 };
    CHECK(keys_ikey_to_bkey(max, 5, out));
    CHECK_BYTES(out, max_bkey, 5);
}

/* ikey bytes to bkey bytes and back: '/' is 1, every other byte plus 2. */
TEST(keys_bkey_bytes) {
    const uint8_t ikey[] = { 0, 1, 0x7f, 0xc2, 0x80, '/', '.', '0' };
    const uint8_t bkey[] = { 2, 3, 0x81, 0xc4, 0x82, 1, '0', '2' };
    uint8_t out[8];
    CHECK(keys_ikey_to_bkey(ikey, 8, out));
    CHECK_BYTES(out, bkey, 8);
    CHECK(keys_bkey_to_ikey(bkey, 8, out));
    CHECK_BYTES(out, ikey, 8);
    /* A bkey byte 0 has no ikey byte: no ikey (021-06; before, Java decoded
     * (byte) -2 as U+FFFD, and C gave 0xfe). */
    const uint8_t zero[1] = { 0 };
    CHECK(!keys_bkey_to_ikey(zero, 1, out));
    /* The empty bkey gives the empty ikey, as Java's "", which
     * keys_ikey_to_bkey refuses. */
    CHECK(keys_bkey_to_ikey(zero, 0, out));
}

/* An ikey: the given bytes after a start, ikey the start's C string; its
 * length. */
static int32_t ikey_of(const char *start, const uint8_t *more, int32_t nmore, uint8_t *out) {
    int32_t n = (int32_t) strlen(start);
    memcpy(out, start, (size_t) n);
    memcpy(out + n, more, (size_t) nmore);
    return n + nmore;
}

/* Keys.testLoneSurrogate (bergdb 021-05), in bytes: an ikey that is not
 * well-formed UTF-8 is refused, with nothing written, as Java refuses a
 * String with a lone surrogate (its encoding wrote '?'): the WTF-8 bytes of
 * Java's four refused Strings, ED A0 80 for U+D800 among them, and
 * 021-04's CK1 to CK5 after "/dd/-a", the ikey of the Pub key "/d/a": CK1
 * ED A0 80 and CK4 C0 80 (an overlong NUL) refused, which C took before
 * 022-02; CK2 EF BF BD (U+FFFD) and CK3 '?' taken; CK5 FF refused. */
TEST(keys_lone_surrogate) {
    static const uint8_t refused[][8] = {
        { 0x61, 0xed, 0xa0, 0x80 },                           /* "a\uD800" */
        { 0xed, 0xb0, 0x80 },                                 /* "\uDC00" */
        { 0x3f, 0xed, 0xa0, 0xbd },                           /* "?\uD83D" */
        { 0xed, 0xb8, 0x80, 0xf0, 0x9f, 0x98, 0x80 },         /* "\uDE00\uD83D\uDE00" */
    };
    static const int32_t refused_n[] = { 4, 3, 4, 7 };
    uint8_t out[16], ik[16];
    for (int i = 0; i < 4; i++) {
        memset(out, 0xab, sizeof out);
        CHECK(!keys_ikey_to_bkey(refused[i], refused_n[i], out));
        CHECK(out[0] == 0xab && out[refused_n[i] - 1] == 0xab);     /* nothing written */
    }
    /* "a?\uD83D\uDE00": a '?' and a pair, taken, and its ikey back. */
    const uint8_t pair[] = { 0x61, 0x3f, 0xf0, 0x9f, 0x98, 0x80 };
    CHECK(keys_ikey_to_bkey(pair, 6, out));
    CHECK(keys_bkey_to_ikey(out, 6, ik));
    CHECK_BYTES(ik, pair, 6);

    static const uint8_t ck1[] = { 0xed, 0xa0, 0x80 }, ck2[] = { 0xef, 0xbf, 0xbd },
            ck3[] = { '?' }, ck4[] = { 0xc0, 0x80 }, ck5[] = { 0xff };
    const uint8_t ck2_bkey[] = { 1, 'd' + 2, 'd' + 2, 1, '-' + 2, 'a' + 2, 0xf1, 0xc1, 0xbf };
    int32_t n;
    n = ikey_of("/dd/-a", ck1, 3, ik);
    CHECK(!keys_ikey_to_bkey(ik, n, out));
    n = ikey_of("/dd/-a", ck2, 3, ik);
    CHECK(keys_ikey_to_bkey(ik, n, out));
    CHECK_BYTES(out, ck2_bkey, 9);
    n = ikey_of("/dd/-a", ck3, 1, ik);
    CHECK(keys_ikey_to_bkey(ik, n, out));
    CHECK(out[6] == '?' + 2);
    n = ikey_of("/dd/-a", ck4, 2, ik);
    CHECK(!keys_ikey_to_bkey(ik, n, out));
    n = ikey_of("/dd/-a", ck5, 1, ik);
    CHECK(!keys_ikey_to_bkey(ik, n, out));
}

/* The bkey of the ikey start, then the given bytes; its length. */
static int32_t bkey_of(const char *start, const uint8_t *more, int32_t nmore, uint8_t *out) {
    int32_t n = (int32_t) strlen(start);
    if (n > 0 && !keys_ikey_to_bkey((const uint8_t *) start, n, out)) {
        test_fail_(__FILE__, __LINE__, "bkey_of: bad ikey");
    }
    memcpy(out + n, more, (size_t) nmore);
    return n + nmore;
}

/* An ikey, back from the bkey's segments: Java's Keys.toString(long[]);
 * false where it throws, for a bkey without an ikey. */
static bool ikey_of_segments(const uint8_t *bkey, int32_t n, uint8_t *ikey) {
    int64_t seg[MAXSEG];
    uint8_t b[MAXSEG * KL_MAX_SIZE];
    keys_to_segments(bkey, n, seg);
    int32_t m = keys_to_bytes(seg, keys_segment_count(n), b);
    return m == n && keys_bkey_to_ikey(b, m, ikey);
}

/* Keys.testBkeyWithoutIkey (bergdb 021-06): CK1 of 021-04, the bkey of the
 * ikey "/dd/-a" ED A0 80 (U+D800 in WTF-8), has no ikey; before, C gave its
 * ikey bytes, and Java read it as CK2, the ikey with EF BF BD (U+FFFD): two
 * keys as one String. No ikey either: an overlong form, a cut sequence, a
 * value above U+10FFFF, the byte 0 or 0x31 ('/' + 2, which no ikey gives),
 * 0xfe or 0xff. */
TEST(keys_bkey_without_ikey) {
    static const uint8_t ck1[] = { 0xef, 0xa2, 0x82 }, ck2[] = { 0xf1, 0xc1, 0xbf };
    static const uint8_t ck2_ikey[] = { '/', 'd', 'd', '/', '-', 'a', 0xef, 0xbf, 0xbd };
    uint8_t b[16], ik[16], back[16];
    int32_t n = bkey_of("/dd/-a", ck2, 3, b);
    REQUIRE(ikey_of("/dd/-a", (const uint8_t *) "\xef\xbf\xbd", 3, ik) == n);
    CHECK(keys_ikey_to_bkey(ik, n, back));          /* toBytes("/dd/-a\uFFFD") */
    CHECK_BYTES(back, b, (size_t) n);
    CHECK(keys_bkey_to_ikey(b, n, ik));
    CHECK_BYTES(ik, ck2_ikey, 9);
    memset(ik, 0, sizeof ik);
    CHECK(ikey_of_segments(b, n, ik));
    CHECK_BYTES(ik, ck2_ikey, 9);

    static const struct { const char *start; uint8_t more[4]; int32_t n; } none[] = {
        { "/dd/-a", { 0xef, 0xa2, 0x82 }, 3 },              /* CK1 */
        { "/dd/-a", { 0xc2, 0x82 }, 2 },                    /* C0 80, overlong */
        { "/dd/-a", { 0xe4, 0x84 }, 2 },                    /* E2 82, cut */
        { "/dd/-a", { 0xf6, 0x92, 0x82, 0x82 }, 4 },        /* F4 90 80 80, above U+10FFFF */
        { "/dd/-a", { 0x00 }, 1 },
        { "/dd/-a", { 0x31 }, 1 },
        { "/dd/-a", { 0xfe }, 1 },
        { "/dd/-a", { 0xff }, 1 },
        { "", { 0xe4, 0x84, 0x63 }, 3 },                    /* E2 82 61, cut */
    };
    CHECK(memcmp(none[0].more, ck1, 3) == 0);
    for (int i = 0; i < 9; i++) {
        n = bkey_of(none[i].start, none[i].more, none[i].n, b);
        CHECK(!keys_bkey_to_ikey(b, n, ik));
        CHECK(!ikey_of_segments(b, n, ik));
    }
}

/* Keys.testBkeyIkeyRoundTrip (bergdb 021-06): two bkeys never give one
 * ikey. Random bkeys of 1 to 6 bytes near UTF-8's edges: each has no ikey,
 * or its ikey's bkey is itself. Before 022-02 a bkey with 0x31 gave '/',
 * whose bkey is 1. */
TEST(keys_bkey_ikey_round_trip) {
    static const uint8_t near[] = { 0x00, 0x01, 0x02, 0x03, 0x31, 0x33, 0x63, 0x81, 0x82,
        0x91, 0x92, 0xa1, 0xa2, 0xc1, 0xc2, 0xc3, 0xc4, 0xe1, 0xe2, 0xe3, 0xee, 0xef, 0xf0,
        0xf1, 0xf2, 0xf3, 0xf5, 0xf6, 0xf7, 0xfe, 0xff };
    const int32_t nnear = (int32_t) sizeof near;
    uint64_t r = 2106;
    int32_t with_ikey = 0;
    for (int i = 0; i < 100000; i++) {
        uint8_t b[6], ik[6], back[6];
        int32_t n = 1 + test_random_below(&r, 6);
        for (int32_t j = 0; j < n; j++) {
            b[j] = near[test_random_below(&r, nnear)];
        }
        if (keys_bkey_to_ikey(b, n, ik)) {
            with_ikey++;
            CHECK(keys_ikey_to_bkey(ik, n, back));
            CHECK_BYTES(back, b, (size_t) n);
        }
    }
    CHECK(with_ikey > 2000);
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
    TEST_ENTRY(keys_lone_surrogate),
    TEST_ENTRY(keys_bkey_without_ikey),
    TEST_ENTRY(keys_bkey_ikey_round_trip),
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
