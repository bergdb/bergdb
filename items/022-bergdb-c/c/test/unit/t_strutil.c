/* Unit tests of strutil (bergdb 022-02): Java's @Nano test of
 * StringUtil.isWellFormedUtf8 (bergdb 021-06), ported. Java checks it
 * against the JDK's UTF-8 decoder set to report malformed input; here
 * against a decoder of this file, written apart from the port: it decodes
 * each sequence by its first byte's length and then checks the value's
 * range, as the JDK's and tools/run.c's valid_utf8 do. Java's own answers
 * are in vectors/strutil.txt (t_vectors.c). */
#include "test.h"
#include "strutil.h"

/* Strict UTF-8 by decoding: a first byte 0xxxxxxx, 110xxxxx, 1110xxxx or
 * 11110xxx and its continuation bytes 10xxxxxx; the value no overlong form
 * (at least 0x80, 0x800 or 0x10000 by its length), no surrogate (U+D800 to
 * U+DFFF), at most U+10FFFF. */
static bool reference(const uint8_t *p, int32_t n) {
    int32_t i = 0;
    while (i < n) {
        uint32_t c = p[i];
        int32_t k;
        uint32_t cp, min;
        if ((c & 0x80u) == 0) {
            i++;
            continue;
        } else if ((c & 0xe0u) == 0xc0u) {
            k = 1;
            cp = c & 0x1fu;
            min = 0x80;
        } else if ((c & 0xf0u) == 0xe0u) {
            k = 2;
            cp = c & 0x0fu;
            min = 0x800;
        } else if ((c & 0xf8u) == 0xf0u) {
            k = 3;
            cp = c & 0x07u;
            min = 0x10000;
        } else {
            return false;
        }
        for (int32_t j = 1; j <= k; j++) {
            if (i + j >= n || (p[i + j] & 0xc0u) != 0x80u) {
                return false;
            }
            cp = cp << 6 | (p[i + j] & 0x3fu);
        }
        if (cp < min || (cp >= 0xd800 && cp <= 0xdfff) || cp > 0x10ffff) {
            return false;
        }
        i += k + 1;
    }
    return true;
}

static void check_well_formed(const uint8_t *b, int32_t n) {
    bool expected = reference(b, n);
    if (su_is_well_formed_utf8(b, n) != expected) {
        test_fail_(__FILE__, __LINE__, "su_is_well_formed_utf8 differs from the decoder");
        printf("    bytes:");
        for (int32_t i = 0; i < n; i++) {
            printf(" %02x", b[i]);
        }
        printf(", the decoder says %s\n", expected ? "true" : "false");
    }
}

/* StringUtil.testIsWellFormedUtf8: every sequence of 1 and 2 bytes, the
 * edges, and random sequences of up to 8 bytes from bytes near the edges;
 * and here every sequence of 3 bytes that starts with C0 to FF. */
TEST(strutil_is_well_formed_utf8) {
    long failed = test_failed_checks_;
    uint8_t b[8];
    for (int32_t a = 0; a < 256; a++) {
        b[0] = (uint8_t) a;
        check_well_formed(b, 1);
        for (int32_t c = 0; c < 256; c++) {
            b[1] = (uint8_t) c;
            check_well_formed(b, 2);
        }
    }
    for (int32_t a = 0xc0; a < 256 && test_failed_checks_ - failed < 10; a++) {
        b[0] = (uint8_t) a;
        for (int32_t c = 0; c < 256; c++) {
            b[1] = (uint8_t) c;
            for (int32_t d = 0; d < 256; d++) {
                b[2] = (uint8_t) d;
                check_well_formed(b, 3);
            }
        }
    }
    static const struct { uint8_t b[5]; int32_t n; } edges[] = {
        { { 0xed, 0x9f, 0xbf }, 3 }, { { 0xed, 0xa0, 0x80 }, 3 }, { { 0xee, 0x80, 0x80 }, 3 },
        { { 0xe0, 0x9f, 0xbf }, 3 }, { { 0xe0, 0xa0, 0x80 }, 3 }, { { 0xc0, 0x80 }, 2 },
        { { 0xc1, 0xbf }, 2 }, { { 0xc2, 0x80 }, 2 }, { { 0xf0, 0x8f, 0xbf, 0xbf }, 4 },
        { { 0xf0, 0x90, 0x80, 0x80 }, 4 }, { { 0xf4, 0x8f, 0xbf, 0xbf }, 4 },
        { { 0xf4, 0x90, 0x80, 0x80 }, 4 }, { { 0xf5, 0x80, 0x80, 0x80 }, 4 },
        { { 0xef, 0xbf, 0xbd }, 3 }, { { 0xe2, 0x82 }, 2 },
        { { 0x61, 0xe2, 0x82, 0xac, 0x62 }, 5 }, { { 0 }, 0 },
    };
    static const bool edge_results[] = { true, false, true, false, true, false, false, true,
        false, true, true, false, false, true, false, true, true };
    for (int i = 0; i < 17; i++) {
        check_well_formed(edges[i].b, edges[i].n);
        CHECK(su_is_well_formed_utf8(edges[i].b, edges[i].n) == edge_results[i]);
    }
    const uint8_t ed[] = { 0xed, 0xa0, 0x80 }, fffd[] = { 0xef, 0xbf, 0xbd };
    CHECK(!su_is_well_formed_utf8(ed, 3));
    CHECK(su_is_well_formed_utf8(fffd, 3));
    const uint8_t xaby[] = { 'x', 'a', 'b', 'y' }, euro[] = { 'x', 0xe2, 0x82, 0xac };
    CHECK(su_is_well_formed_utf8(xaby + 1, 2));             /* Java's (b, 1, 2) */
    CHECK(!su_is_well_formed_utf8(euro, 3));                /* Java's (b, 0, 3): cut */
    CHECK(su_is_well_formed_utf8(euro, 4));

    static const uint8_t near[] = { 0x00, 0x41, 0x7f, 0x80, 0x8f, 0x90, 0x9f, 0xa0, 0xbf,
        0xc0, 0xc1, 0xc2, 0xdf, 0xe0, 0xe1, 0xec, 0xed, 0xee, 0xef, 0xf0, 0xf1, 0xf3, 0xf4,
        0xf5, 0xff };
    uint64_t r = 2106;
    int32_t well = 0;
    for (int i = 0; i < 50000; i++) {
        int32_t n = 1 + test_random_below(&r, 8);
        for (int32_t j = 0; j < n; j++) {
            b[j] = near[test_random_below(&r, (int32_t) sizeof near)];
        }
        check_well_formed(b, n);
        well += su_is_well_formed_utf8(b, n);
    }
    CHECK(well > 500);          /* both answers met: 1,091 well-formed */
}

const struct test strutil_tests[] = {
    TEST_ENTRY(strutil_is_well_formed_utf8),
    TEST_END
};
