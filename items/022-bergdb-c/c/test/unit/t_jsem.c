/* Unit tests of jsem.h (bergdb 012-04), beside Java's own results in
 * t_vectors.c (jsem.txt): the build's flags that Java's semantics need, and
 * what the vectors do not cover. */
#include <math.h>
#include "test.h"
#include "jsem.h"

/* Values the optimizer cannot see, so that the operations run. */
static volatile int64_t v_max = INT64_MAX;
static volatile int64_t v_min = INT64_MIN;
static volatile int32_t v_imax = INT32_MAX;
static volatile double v_one_up = 1.0 + 0x1.0p-30;
static volatile double v_one_down = 1.0 - 0x1.0p-30;
static volatile double v_minus_one = -1.0;

/* -fwrapv: signed overflow wraps as Java's long and int. Without it, the
 * test build's UndefinedBehaviorSanitizer stops here. */
TEST(jsem_wrapv) {
    int64_t max = v_max;
    int64_t min = v_min;
    int32_t imax = v_imax;
    CHECK_EQ(max + 1, INT64_MIN);
    CHECK_EQ(min - 1, INT64_MAX);
    CHECK_EQ(-min, INT64_MIN);
    CHECK_EQ(max * 2, -2);
    CHECK_EQ(imax + 1, INT32_MIN);
    CHECK_EQ(min << 1, 0);                  /* a left shift of a negative value */
    CHECK_EQ((int64_t) -1 << 63, INT64_MIN);
}

/* -ffp-contract=off: a * b + c is two roundings, as in Java, not one fused
 * multiply-add. With 1 + 2^-30 and 1 - 2^-30 the product 1 - 2^-60 rounds
 * to 1, so Java gives 0; a fused multiply-add gives -2^-60. */
TEST(jsem_no_fma) {
    double a = v_one_up;
    double b = v_one_down;
    double c = v_minus_one;
    double r = a * b + c;
    CHECK_EQ(j_double_bits(r), j_double_bits(0.0));
    CHECK_EQ(j_double_bits(fma(a, b, c)), j_double_bits(-0x1.0p-60));
}

/* J64: Java's long literals with the high bit set. */
TEST(jsem_j64) {
    CHECK_EQ(J64(0xc000000000000000), -INT64_C(0x4000000000000000));
    CHECK_EQ(J64(0x8000000000000000), INT64_MIN);
    CHECK_EQ(J64(0xffffffffffffffff), -1);
    CHECK_EQ(J64(0x7fffffffffffffff), INT64_MAX);
    CHECK(J64(0x9E3779B97F4A7C15) < 0);
}

/* Shift counts are masked: n and n + 64 (or + 32) shift alike. */
TEST(jsem_shift_masks) {
    const int64_t x = J64(0x8123456789abcdef);
    const int32_t y = (int32_t) 0x81234567;
    for (int n = -70; n < 140; n++) {
        CHECK_EQ(j_shl64(x, n), j_shl64(x, n & 63));
        CHECK_EQ(j_shr64(x, n), j_shr64(x, n & 63));
        CHECK_EQ(j_ushr64(x, n), j_ushr64(x, n & 63));
        CHECK_EQ(j_shl32(y, n), j_shl32(y, n & 31));
        CHECK_EQ(j_shr32(y, n), j_shr32(y, n & 31));
        CHECK_EQ(j_ushr32(y, n), j_ushr32(y, n & 31));
    }
    CHECK_EQ(j_ushr64(-1, 1), INT64_MAX);
    CHECK_EQ(j_shr64(-1, 1), -1);
    CHECK_EQ(j_ushr32(-1, 1), INT32_MAX);
}

/* The bits of floats and doubles, NaN payloads too, as Java's raw bits. */
TEST(jsem_bits) {
    const int64_t d[] = { 0, J64(0x8000000000000000), J64(0x7ff0000000000001),
        J64(0xfff8000000000001), J64(0x7ff8000000000000), 1 };
    for (int i = 0; i < 6; i++) {
        CHECK_EQ(j_double_bits(j_bits_double(d[i])), d[i]);
    }
    const int32_t f[] = { 0, INT32_MIN, 0x7f800001, (int32_t) 0xffc00001, 0x7fc00000, 1 };
    for (int i = 0; i < 6; i++) {
        CHECK_EQ(j_float_bits(j_bits_float(f[i])), f[i]);
    }
}

/* numberOfLeadingZeros of each power of two and its predecessor. */
TEST(jsem_nlz) {
    CHECK_EQ(j_nlz64(0), 64);
    for (int n = 0; n < 64; n++) {
        int64_t p = j_shl64(1, n);
        CHECK_EQ(j_nlz64(p), 63 - n);
        if (n > 0) {
            CHECK_EQ(j_nlz64(p - 1), 64 - n);
        }
    }
}

/* Division by -1 and of MIN, as Java: no trap, MIN / -1 is MIN. */
TEST(jsem_division) {
    CHECK_EQ(j_div64(INT64_MIN, -1), INT64_MIN);
    CHECK_EQ(j_rem64(INT64_MIN, -1), 0);
    CHECK_EQ(j_div32(INT32_MIN, -1), INT32_MIN);
    CHECK_EQ(j_rem32(INT32_MIN, -1), 0);
    CHECK_EQ(j_floor_div64(INT64_MIN, -1), INT64_MIN);
    CHECK_EQ(j_div64(-7, 2), -3);
    CHECK_EQ(j_rem64(-7, 2), -1);
    CHECK_EQ(j_floor_div64(-7, 2), -4);
    CHECK_EQ(j_floor_div64(-1, 255), -1);
}

/* Java's casts from double, at the edges the vectors have, and between. */
TEST(jsem_d2l) {
    CHECK_EQ(j_d2l(NAN), 0);
    CHECK_EQ(j_d2l(INFINITY), INT64_MAX);
    CHECK_EQ(j_d2l(-INFINITY), INT64_MIN);
    CHECK_EQ(j_d2l(0x1.0p63), INT64_MAX);
    CHECK_EQ(j_d2l(-0x1.0p63), INT64_MIN);
    CHECK_EQ(j_d2l(-2.9), -2);
    CHECK_EQ(j_d2i(NAN), 0);
    CHECK_EQ(j_d2i(1e10), INT32_MAX);
    CHECK_EQ(j_d2i(-1e10), INT32_MIN);
    CHECK_EQ(j_d2i(-2147483648.9), INT32_MIN);
    CHECK_EQ(j_d2i(2147483647.9), INT32_MAX);
    /* StoredTrans: (long) (totalSize * 1.20). */
    CHECK_EQ(j_d2l(1000 * 1.20), 1200);
}

const struct test jsem_tests[] = {
    TEST_ENTRY(jsem_wrapv),
    TEST_ENTRY(jsem_no_fma),
    TEST_ENTRY(jsem_j64),
    TEST_ENTRY(jsem_shift_masks),
    TEST_ENTRY(jsem_bits),
    TEST_ENTRY(jsem_nlz),
    TEST_ENTRY(jsem_division),
    TEST_ENTRY(jsem_d2l),
    TEST_END
};
