/*
 * Java's vectors (bergdb 012-04): the files in test/unit/vectors/, written
 * by test/cross/java/Vectors.java from Java's own classes, read here and
 * compared with what the C modules give. The format is in Vectors.java: one
 * case per line, its kind first, fields separated by one space, '#' starts
 * a comment line.
 *
 * Each file's test checks every line, fails on a kind it does not know (so
 * a new kind in Vectors.java shows), and checks that each known kind had a
 * line. A failed line is printed with its file and line number after the
 * failed checks. The directory is VECTORS_DIR (build.sh), or the
 * environment's BERGDB_VECTORS, as for vectors that Java has just written.
 */
#include <errno.h>
#include <stdbool.h>
#include <stdlib.h>
#include "test.h"
#include "bytes.h"
#include "checksum.h"
#include "jsem.h"
#include "keys.h"
#include "klong.h"

#ifndef VECTORS_DIR
#define VECTORS_DIR "test/unit/vectors"
#endif

#define V_LINE 4096
#define V_TOKENS 12
#define V_KINDS 16
#define V_BYTES 1024
#define V_LONGS 16

/* A vector file being read: the line, its fields, and the counts by kind. */
struct vfile {
    FILE *f;
    const char *name;
    int line_no;
    char line[V_LINE];
    char copy[V_LINE];          /* the line as read, for a failure's report */
    char *tok[V_TOKENS];
    int ntok;
    long failed_before;         /* test_failed_checks_ when the line began */
    const char *kinds[V_KINDS];
    int counts[V_KINDS];
};

/* One file at a time, so one static struct: no large stack frame. */
static struct vfile vf;

/* Opens the file, with the kinds it should have; NULL-terminated. */
static bool v_open(struct vfile *v, const char *name, const char *const *kinds) {
    char path[1024];
    const char *dir = getenv("BERGDB_VECTORS");
    memset(v, 0, sizeof *v);
    v->name = name;
    snprintf(path, sizeof path, "%s/%s", dir != NULL ? dir : VECTORS_DIR, name);
    v->f = fopen(path, "r");
    if (v->f == NULL) {
        printf("cannot open %s: %s\n", path, strerror(errno));
        return false;
    }
    for (int k = 0; k < V_KINDS && kinds[k] != NULL; k++) {
        v->kinds[k] = kinds[k];
    }
    return true;
}

/* Reports the last line if a check failed on it. */
static void v_report(struct vfile *v) {
    if (v->line_no > 0 && test_failed_checks_ != v->failed_before) {
        printf("    at vectors/%s:%d: %.160s\n", v->name, v->line_no, v->copy);
    }
}

/* The next case: true with its fields in tok[0..ntok-1]; false at the end.
 * A line too long, or of a kind not given to v_open, is a failed check. */
static bool v_next(struct vfile *v) {
    v_report(v);
    for (;;) {
        if (fgets(v->line, sizeof v->line, v->f) == NULL) {
            fclose(v->f);
            v->f = NULL;
            v->line_no = 0;
            return false;
        }
        v->line_no++;
        v->failed_before = test_failed_checks_;
        size_t len = strlen(v->line);
        if (len == 0 || v->line[len - 1] != '\n') {
            test_fail_(__FILE__, __LINE__, "a vector line too long, or without its newline");
            v_report(v);
            continue;
        }
        v->line[len - 1] = '\0';
        if (v->line[0] == '#' || v->line[0] == '\0') {
            continue;
        }
        memcpy(v->copy, v->line, len);
        v->ntok = 0;
        for (char *s = strtok(v->line, " "); s != NULL; s = strtok(NULL, " ")) {
            if (v->ntok == V_TOKENS) {
                break;
            }
            v->tok[v->ntok++] = s;
        }
        int k = 0;
        while (k < V_KINDS && v->kinds[k] != NULL && strcmp(v->kinds[k], v->tok[0]) != 0) {
            k++;
        }
        if (k == V_KINDS || v->kinds[k] == NULL) {
            test_fail_(__FILE__, __LINE__, "a vector of a kind this test does not know");
            v_report(v);
            continue;
        }
        v->counts[k]++;
        return true;
    }
}

/* True if the case is of the kind and has n fields after it; a failed check
 * if the kind matches but the number of fields does not. */
static bool v_is(struct vfile *v, const char *kind, int n) {
    if (strcmp(v->tok[0], kind) != 0) {
        return false;
    }
    test_checks_++;
    if (v->ntok != n + 1) {
        test_fail_(__FILE__, __LINE__, "a vector line with the wrong number of fields");
        return false;
    }
    return true;
}

/* Checks that each kind had a case. */
static void v_end(struct vfile *v) {
    for (int k = 0; k < V_KINDS && v->kinds[k] != NULL; k++) {
        test_checks_++;
        if (v->counts[k] == 0) {
            printf("vectors/%s: no case of kind %s\n", v->name, v->kinds[k]);
            test_fail_(__FILE__, __LINE__, "a kind without cases");
        }
    }
}

static int hexval(char c) {
    if (c >= '0' && c <= '9') {
        return c - '0';
    }
    if (c >= 'a' && c <= 'f') {
        return c - 'a' + 10;
    }
    return -1;
}

/* Hex bytes ("-" for none) into out; the number of bytes, -1 if bad. */
static int v_bytes(const char *s, uint8_t *out, int max) {
    if (strcmp(s, "-") == 0) {
        return 0;
    }
    int n = 0;
    while (s[0] != '\0') {
        int hi = hexval(s[0]);
        int lo = hi < 0 ? -1 : hexval(s[1]);
        if (lo < 0 || n == max) {
            test_fail_(__FILE__, __LINE__, "bad hex bytes in a vector");
            return -1;
        }
        out[n++] = (uint8_t) (hi * 16 + lo);
        s += 2;
    }
    return n;
}

/* A long as hex digits, its bits. */
static int64_t v_hex(const char *s) {
    char *end;
    errno = 0;
    uint64_t u = strtoull(s, &end, 16);
    if (errno != 0 || *end != '\0' || end == s) {
        test_fail_(__FILE__, __LINE__, "bad hex long in a vector");
    }
    return (int64_t) u;
}

/* A decimal long. */
static int64_t v_dec(const char *s) {
    char *end;
    errno = 0;
    long long v = strtoll(s, &end, 10);
    if (errno != 0 || *end != '\0' || end == s) {
        test_fail_(__FILE__, __LINE__, "bad decimal in a vector");
    }
    return (int64_t) v;
}

/* Hex longs separated by commas ("-" for none); their number, -1 if bad. */
static int v_longs(const char *s, int64_t *out, int max) {
    if (strcmp(s, "-") == 0) {
        return 0;
    }
    int n = 0;
    char buf[V_LINE];
    snprintf(buf, sizeof buf, "%s", s);
    for (char *p = buf, *q; p != NULL; p = q) {
        q = strchr(p, ',');
        if (q != NULL) {
            *q++ = '\0';
        }
        if (n == max) {
            test_fail_(__FILE__, __LINE__, "too many longs in a vector");
            return -1;
        }
        out[n++] = v_hex(p);
    }
    return n;
}

static bool v_bool(const char *s) {
    if (strcmp(s, "true") != 0 && strcmp(s, "false") != 0) {
        test_fail_(__FILE__, __LINE__, "bad boolean in a vector");
    }
    return strcmp(s, "true") == 0;
}

/* ---- bytes.txt: Bytes ---- */

TEST(vectors_bytes) {
    static const char *const kinds[] = {
        "long", "int", "short", "ushort", "double", "float", "longs", NULL
    };
    struct vfile *v = &vf;
    uint8_t le[V_BYTES], be[V_BYTES], b[V_BYTES];
    int64_t longs[V_LONGS];
    REQUIRE(v_open(v, "bytes.txt", kinds));

    while (v_next(v)) {
        if (v_is(v, "long", 3)) {
            int64_t x = v_dec(v->tok[1]);
            REQUIRE(v_bytes(v->tok[2], le, 8) == 8 && v_bytes(v->tok[3], be, 8) == 8);
            bytes_put_long_le(x, b);
            CHECK_BYTES(b, le, 8);
            CHECK_EQ(bytes_get_long_le(le), x);
            bytes_put_long_be(x, b);
            CHECK_BYTES(b, be, 8);
            CHECK_EQ(bytes_get_long_be(be), x);
        } else if (v_is(v, "int", 3)) {
            int32_t x = j_l2i(v_dec(v->tok[1]));
            REQUIRE(v_bytes(v->tok[2], le, 4) == 4 && v_bytes(v->tok[3], be, 4) == 4);
            bytes_put_int_le(x, b);
            CHECK_BYTES(b, le, 4);
            CHECK_EQ(bytes_get_int_le(le), x);
            bytes_put_int_be(x, b);
            CHECK_BYTES(b, be, 4);
            CHECK_EQ(bytes_get_int_be(be), x);
        } else if (v_is(v, "short", 3)) {
            int64_t x = v_dec(v->tok[1]);
            REQUIRE(v_bytes(v->tok[2], le, 2) == 2);
            bytes_put_short_le(x, b);
            CHECK_BYTES(b, le, 2);
            CHECK_EQ(bytes_get_short_le(le), v_dec(v->tok[3]));
        } else if (v_is(v, "ushort", 2)) {
            int32_t x = j_l2i(v_dec(v->tok[1]));
            memset(b, 0xab, 2);
            if (strcmp(v->tok[2], "refused") == 0) {
                CHECK(!bytes_put_ushort_le(x, b));
                CHECK(b[0] == 0xab && b[1] == 0xab);       /* nothing written */
            } else {
                REQUIRE(v_bytes(v->tok[2], le, 2) == 2);
                CHECK(bytes_put_ushort_le(x, b));
                CHECK_BYTES(b, le, 2);
                CHECK_EQ(bytes_get_ushort_le(le), x);
            }
        } else if (v_is(v, "double", 2)) {
            int64_t bits = v_hex(v->tok[1]);
            REQUIRE(v_bytes(v->tok[2], le, 8) == 8);
            bytes_put_double_le(j_bits_double(bits), b);
            CHECK_BYTES(b, le, 8);
            CHECK_EQ(j_double_bits(bytes_get_double_le(le)), bits);
        } else if (v_is(v, "float", 2)) {
            int32_t bits = j_l2i(v_hex(v->tok[1]));
            REQUIRE(v_bytes(v->tok[2], le, 4) == 4);
            bytes_put_float_le(j_bits_float(bits), b);
            CHECK_BYTES(b, le, 4);
            CHECK_EQ(j_float_bits(bytes_get_float_le(le)), bits);
        } else if (v_is(v, "longs", 2)) {
            int n = v_longs(v->tok[1], longs, V_LONGS);
            REQUIRE(n >= 0 && v_bytes(v->tok[2], le, V_BYTES) == 8 * n);
            bytes_longs_to_le(longs, n, b);
            CHECK_BYTES(b, le, (size_t) (8 * n));
        }
    }
    v_end(v);
}

/* ---- checksum.txt: NodeChecksum ---- */

TEST(vectors_checksum) {
    static const char *const kinds[] = { "sum", "zr", "longs", NULL };
    struct vfile *v = &vf;
    uint8_t data[V_BYTES];
    int64_t longs[V_LONGS];
    REQUIRE(v_open(v, "checksum.txt", kinds));

    while (v_next(v)) {
        if (v_is(v, "sum", 4)) {
            int n = v_bytes(v->tok[1], data, V_BYTES);
            int32_t off = j_l2i(v_dec(v->tok[2]));
            int32_t len = j_l2i(v_dec(v->tok[3]));
            REQUIRE(n >= 0 && off >= 0 && len >= 0 && off + len <= n);
            CHECK_EQ(cks_sum(data, off, len), v_dec(v->tok[4]));
        } else if (v_is(v, "zr", 5)) {
            int n = v_bytes(v->tok[1], data, V_BYTES);
            int32_t off = j_l2i(v_dec(v->tok[2]));
            int32_t len = j_l2i(v_dec(v->tok[3]));
            REQUIRE(n >= 0 && off >= 0 && len >= 0 && off + len <= n);
            CHECK_EQ(cks_sum_with_zero_replace(data, off, len, j_l2i(v_dec(v->tok[4]))),
                    v_dec(v->tok[5]));
        } else if (v_is(v, "longs", 4)) {
            int n = v_longs(v->tok[1], longs, V_LONGS);
            int32_t off = j_l2i(v_dec(v->tok[2]));
            int32_t len = j_l2i(v_dec(v->tok[3]));
            REQUIRE(n >= 0 && off >= 0 && len >= 0 && off + len <= n);
            int64_t sum = v_dec(v->tok[4]);
            CHECK_EQ(cks_sum_longs(longs, off, len), sum);
            /* The same as the sum of their little-endian bytes. */
            bytes_longs_to_le(longs, n, data);
            CHECK_EQ(cks_sum(data, 8 * off, 8 * len), sum);
        }
    }
    v_end(v);
}

/* ---- klong.txt: Klong ---- */

static int64_t klong_const(const char *name) {
    static const struct { const char *name; int64_t value; } c[] = {
        { "NULL", KL_NULL },
        { "EMPTY_KEY", KL_EMPTY_KEY },
        { "DELETE_NONE_BITMAP", KL_DELETE_NONE_BITMAP },
        { "DELETE_ALL_BITMAP", KL_DELETE_ALL_BITMAP },
        { "TYPE_KEY", KL_TYPE_KEY },
        { "TYPE_DELETE_BITMAP", KL_TYPE_DELETE_BITMAP },
    };
    for (size_t i = 0; i < sizeof c / sizeof c[0]; i++) {
        if (strcmp(c[i].name, name) == 0) {
            return c[i].value;
        }
    }
    test_fail_(__FILE__, __LINE__, "a Klong constant that C does not have");
    return 0;
}

TEST(vectors_klong) {
    static const char *const kinds[] = { "const", "key", "time", "delete", "prefix", NULL };
    struct vfile *v = &vf;
    uint8_t k1[V_BYTES], k2[V_BYTES], out[8];
    REQUIRE(v_open(v, "klong.txt", kinds));

    while (v_next(v)) {
        if (v_is(v, "const", 2)) {
            CHECK_EQ(klong_const(v->tok[1]), v_hex(v->tok[2]));
        } else if (v_is(v, "key", 6)) {
            int n = v_bytes(v->tok[1], k1, 7);
            REQUIRE(n >= 0);
            int64_t klong = v_hex(v->tok[2]);
            int64_t cv = v_hex(v->tok[3]);
            CHECK_EQ(kl_create_key(k1, n), klong);
            CHECK_EQ(kl_get_compare_value(klong), cv);
            CHECK_EQ(kl_create_compare_value(k1, n), cv);
            CHECK_EQ(kl_compare_value_to_key_klong(cv), klong);
            CHECK_EQ(kl_get_key_value(klong), v_hex(v->tok[4]));
            CHECK_EQ(kl_get_length(klong), v_dec(v->tok[5]));
            CHECK_EQ(kl_get_int_type(klong), v_dec(v->tok[6]));
            CHECK(kl_is_key(klong) && !kl_is_time(klong));
            memset(out, 0xab, sizeof out);
            CHECK_EQ(kl_get_key(klong, out), n);
            CHECK_BYTES(out, k1, (size_t) n);
            CHECK(out[n] == 0xab);                  /* nothing written after the key */
        } else if (v_is(v, "time", 2)) {
            int64_t t = v_dec(v->tok[1]);
            int64_t klong = v_hex(v->tok[2]);
            CHECK_EQ(kl_create_time(t), klong);
            CHECK_EQ(kl_get_time(klong), t);
            CHECK(kl_is_time(klong) && !kl_is_key(klong));
            CHECK_EQ(kl_get_int_type(klong), KL_INT_TYPE_TIME);
        } else if (v_is(v, "delete", 2)) {
            int64_t klong = v_hex(v->tok[2]);
            int64_t k = kl_create_delete();
            bool set[62] = { false };
            char buf[V_LINE];
            snprintf(buf, sizeof buf, "%s", v->tok[1]);
            for (char *s = strtok(buf, ","); s != NULL; s = strtok(NULL, ",")) {
                int32_t bit = j_l2i(v_dec(s));
                REQUIRE(bit >= 0 && bit < 62);
                k = kl_delete(k, bit);
                set[bit] = true;
            }
            CHECK_EQ(k, klong);
            CHECK_EQ(kl_get_int_type(k), KL_INT_TYPE_DELETE_BITMAP);
            for (int32_t i = 0; i < 62; i++) {
                CHECK(kl_is_deleted(klong, i) == set[i]);
            }
        } else if (v_is(v, "prefix", 3)) {
            int n1 = v_bytes(v->tok[1], k1, 7);
            int n2 = v_bytes(v->tok[2], k2, 7);
            REQUIRE(n1 >= 0 && n2 >= 0);
            CHECK_EQ(kl_prefix_length(kl_create_key(k1, n1), kl_create_key(k2, n2)),
                    v_dec(v->tok[3]));
        }
    }
    v_end(v);
}

/* ---- keys.txt: Keys ---- */

TEST(vectors_keys) {
    static const char *const kinds[] = { "ikey", "seg", "hash", "cmp", "isprefix", NULL };
    struct vfile *v = &vf;
    uint8_t k1[V_BYTES], k2[V_BYTES], out[V_BYTES];
    int64_t s1[V_LONGS], s2[V_LONGS], seg[V_LONGS];
    REQUIRE(v_open(v, "keys.txt", kinds));

    while (v_next(v)) {
        if (v_is(v, "ikey", 2)) {
            int n = v_bytes(v->tok[1], k1, V_BYTES);
            REQUIRE(n >= 0);
            if (strcmp(v->tok[2], "refused") == 0) {
                CHECK(!keys_ikey_to_bkey(k1, n, out));
            } else {
                int m = v_bytes(v->tok[2], k2, V_BYTES);
                REQUIRE(m == n);
                CHECK(keys_ikey_to_bkey(k1, n, out));
                CHECK_BYTES(out, k2, (size_t) n);
                keys_bkey_to_ikey(k2, n, out);      /* and back */
                CHECK_BYTES(out, k1, (size_t) n);
            }
        } else if (v_is(v, "seg", 4)) {
            int n = v_bytes(v->tok[1], k1, V_BYTES);
            int ns = v_longs(v->tok[2], s1, V_LONGS);
            REQUIRE(n >= 0 && ns > 0);
            CHECK_EQ(keys_segment_count(n), ns);
            REQUIRE(keys_segment_count(n) == ns);
            keys_to_segments(k1, n, seg);
            for (int i = 0; i < ns; i++) {
                CHECK_EQ(seg[i], s1[i]);
            }
            CHECK_EQ(keys_byte_size(s1, ns), v_dec(v->tok[3]));
            CHECK_EQ(keys_byte_size(s1, ns), n);
            CHECK_EQ(keys_hash(s1, ns), v_dec(v->tok[4]));
            memset(out, 0xab, (size_t) n + 1);
            CHECK_EQ(keys_to_bytes(s1, ns, out), n);
            CHECK_BYTES(out, k1, (size_t) n);
            CHECK(out[n] == 0xab);
        } else if (v_is(v, "hash", 2)) {
            int ns = v_longs(v->tok[1], s1, V_LONGS);
            REQUIRE(ns >= 0);
            CHECK_EQ(keys_hash(s1, ns), v_dec(v->tok[2]));
        } else if (v_is(v, "cmp", 4)) {
            int n1 = v_longs(v->tok[1], s1, V_LONGS);
            int n2 = v_longs(v->tok[2], s2, V_LONGS);
            REQUIRE(n1 >= 0 && n2 >= 0);
            int64_t keys = v_dec(v->tok[3]);
            CHECK_EQ(keys_compare_keys(s1, n1, s2, n2), keys);
            CHECK_EQ(keys_compare_arrays(s1, n1, s2, n2), v_dec(v->tok[4]));
            CHECK(keys_are_equal(s1, n1, s2, n2) == (keys == 0));
        } else if (v_is(v, "isprefix", 3)) {
            int n1 = v_bytes(v->tok[1], k1, V_BYTES);
            int n2 = v_bytes(v->tok[2], k2, V_BYTES);
            REQUIRE(n1 > 0 && n2 > 0 && keys_segment_count(n1) <= V_LONGS
                    && keys_segment_count(n2) <= V_LONGS);
            keys_to_segments(k1, n1, s1);
            keys_to_segments(k2, n2, s2);
            CHECK(keys_is_prefix(s1, keys_segment_count(n1), s2, keys_segment_count(n2))
                    == v_bool(v->tok[3]));
        }
    }
    v_end(v);
}

/* ---- jsem.txt: Java's arithmetic ---- */

/* TransSeq.dither (bergdb 005-49), line for line: wrapping products with
 * Java's negative long literals, >>>, and a long times a double. A test of
 * the rules here; the module that ports TransSeq (012-09) has its own. */
static double dither(int64_t pos) {
    int64_t z = pos * J64(0x9E3779B97F4A7C15);
    z = (z ^ j_ushr64(z, 30)) * J64(0xBF58476D1CE4E5B9);
    z = (z ^ j_ushr64(z, 27)) * J64(0x94D049BB133111EB);
    return (double) j_ushr64(z ^ j_ushr64(z, 31), 11) * 0x1.0p-53;
}

TEST(vectors_jsem) {
    static const char *const kinds[] = {
        "d2", "l2d", "narrow", "sh64", "sh32", "div", "idiv", "cmp", "nlz", "share", "dither",
        NULL
    };
    struct vfile *v = &vf;
    REQUIRE(v_open(v, "jsem.txt", kinds));

    while (v_next(v)) {
        if (v_is(v, "d2", 3)) {
            double d = j_bits_double(v_hex(v->tok[1]));
            CHECK_EQ(j_d2l(d), v_dec(v->tok[2]));
            CHECK_EQ(j_d2i(d), v_dec(v->tok[3]));
        } else if (v_is(v, "l2d", 2)) {
            CHECK_EQ(j_double_bits((double) v_dec(v->tok[1])), v_hex(v->tok[2]));
        } else if (v_is(v, "narrow", 4)) {
            int64_t x = v_dec(v->tok[1]);
            CHECK_EQ(j_l2i(x), v_dec(v->tok[2]));
            CHECK_EQ(j_l2s(x), v_dec(v->tok[3]));
            CHECK_EQ(j_l2b(x), v_dec(v->tok[4]));
        } else if (v_is(v, "sh64", 5)) {
            int64_t x = v_hex(v->tok[1]);
            int n = j_l2i(v_dec(v->tok[2]));
            CHECK_EQ(j_shl64(x, n), v_hex(v->tok[3]));
            CHECK_EQ(j_shr64(x, n), v_hex(v->tok[4]));
            CHECK_EQ(j_ushr64(x, n), v_hex(v->tok[5]));
        } else if (v_is(v, "sh32", 5)) {
            int32_t x = j_l2i(v_hex(v->tok[1]));
            int n = j_l2i(v_dec(v->tok[2]));
            CHECK_EQ(j_shl32(x, n), j_l2i(v_hex(v->tok[3])));
            CHECK_EQ(j_shr32(x, n), j_l2i(v_hex(v->tok[4])));
            CHECK_EQ(j_ushr32(x, n), j_l2i(v_hex(v->tok[5])));
        } else if (v_is(v, "div", 5)) {
            int64_t n = v_dec(v->tok[1]);
            int64_t d = v_dec(v->tok[2]);
            REQUIRE(d != 0);
            CHECK_EQ(j_div64(n, d), v_dec(v->tok[3]));
            CHECK_EQ(j_rem64(n, d), v_dec(v->tok[4]));
            CHECK_EQ(j_floor_div64(n, d), v_dec(v->tok[5]));
        } else if (v_is(v, "idiv", 4)) {
            int32_t n = j_l2i(v_dec(v->tok[1]));
            int32_t d = j_l2i(v_dec(v->tok[2]));
            REQUIRE(d != 0);
            CHECK_EQ(j_div32(n, d), v_dec(v->tok[3]));
            CHECK_EQ(j_rem32(n, d), v_dec(v->tok[4]));
        } else if (v_is(v, "cmp", 4)) {
            int64_t a = v_dec(v->tok[1]);
            int64_t b = v_dec(v->tok[2]);
            CHECK_EQ(j_cmp64(a, b), v_dec(v->tok[3]));
            CHECK_EQ(j_cmpu64(a, b), v_dec(v->tok[4]));
        } else if (v_is(v, "nlz", 2)) {
            CHECK_EQ(j_nlz64(v_dec(v->tok[1])), v_dec(v->tok[2]));
        } else if (v_is(v, "share", 6)) {
            /* As TransSeq.take writes it: (double) dirtyCount * recordOwnBytes / ownBytes
             * * (streamLength - currentSp) / startupDistance. */
            int64_t dirtyCount = v_dec(v->tok[1]);
            int64_t recordOwnBytes = v_dec(v->tok[2]);
            int64_t ownBytes = v_dec(v->tok[3]);
            int64_t distance = v_dec(v->tok[4]);
            int32_t startupDistance = j_l2i(v_dec(v->tok[5]));
            const double share = (double) dirtyCount * (double) recordOwnBytes
                    / (double) ownBytes * (double) distance / startupDistance;
            CHECK_EQ(j_double_bits(share), v_hex(v->tok[6]));
        } else if (v_is(v, "dither", 2)) {
            CHECK_EQ(j_double_bits(dither(v_dec(v->tok[1]))), v_hex(v->tok[2]));
        }
    }
    v_end(v);
}

const struct test vectors_tests[] = {
    TEST_ENTRY(vectors_bytes),
    TEST_ENTRY(vectors_checksum),
    TEST_ENTRY(vectors_klong),
    TEST_ENTRY(vectors_keys),
    TEST_ENTRY(vectors_jsem),
    TEST_END
};
