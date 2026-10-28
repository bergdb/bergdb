/*
 * jsem.h: Java's semantics in C, the helpers (bergdb 012-01, section 6.2;
 * the rules in c/readme.md, section 3). Header only: small static inline
 * functions, prefix j_.
 *
 * The build gives -fwrapv, so int64_t and int32_t arithmetic (+, -, *, unary
 * -) wraps as Java's long and int do, and a left shift of a negative value
 * is defined. What -fwrapv does not give, these helpers do: Java's shift
 * counts (masked), Java's >>>, Java's narrowing casts, Java's cast from
 * double, division with Java's results, and Java's comparisons.
 */
#ifndef BERGDB_JSEM_H
#define BERGDB_JSEM_H

#include <stdint.h>
#include <math.h>

/* A Java long literal with the high bit set, as Java writes it: Java's
 * 0xc000000000000000L is a negative long, while C's 0xc000000000000000 is
 * unsigned. J64(0xc000000000000000) is the int64_t with those bits. The cast
 * of an unsigned value above INT64_MAX is implementation-defined in C17;
 * every compiler of interest wraps it, which the static_assert checks. */
#define J64(hex) ((int64_t) UINT64_C(hex))
_Static_assert(J64(0xffffffffffffffff) == -1 && J64(0x8000000000000000) == INT64_MIN,
        "J64 needs the two's complement cast");

/* Java's long << n: the count masked with 63. */
static inline int64_t j_shl64(int64_t v, int n) {
    return (int64_t) ((uint64_t) v << (n & 63));
}

/* Java's long >> n: arithmetic; the count masked with 63. Clang shifts a
 * negative int64_t arithmetically (implementation-defined in C17). */
static inline int64_t j_shr64(int64_t v, int n) {
    return v >> (n & 63);
}

/* Java's long >>> n: logical; the count masked with 63. */
static inline int64_t j_ushr64(int64_t v, int n) {
    return (int64_t) ((uint64_t) v >> (n & 63));
}

/* Java's int << n: the count masked with 31. */
static inline int32_t j_shl32(int32_t v, int n) {
    return (int32_t) ((uint32_t) v << (n & 31));
}

/* Java's int >> n. */
static inline int32_t j_shr32(int32_t v, int n) {
    return v >> (n & 31);
}

/* Java's int >>> n. */
static inline int32_t j_ushr32(int32_t v, int n) {
    return (int32_t) ((uint32_t) v >> (n & 31));
}

/* Java's (int) of a long: the low 32 bits. */
static inline int32_t j_l2i(int64_t v) {
    return (int32_t) (uint32_t) (uint64_t) v;
}

/* Java's (short) of an int or a long: the low 16 bits. */
static inline int16_t j_l2s(int64_t v) {
    return (int16_t) (uint16_t) (uint64_t) v;
}

/* Java's (byte) of an int or a long: the low 8 bits, signed. */
static inline int8_t j_l2b(int64_t v) {
    return (int8_t) (uint8_t) (uint64_t) v;
}

/* Java's (long) of a double: NaN gives 0, values beyond the range give
 * Long.MIN_VALUE or Long.MAX_VALUE, others are truncated toward 0. */
static inline int64_t j_d2l(double d) {
    if (isnan(d)) {
        return 0;
    }
    if (d >= 9223372036854775808.0) {          /* 2^63 */
        return INT64_MAX;
    }
    if (d <= -9223372036854775808.0) {
        return INT64_MIN;
    }
    return (int64_t) d;
}

/* Java's (int) of a double, likewise. */
static inline int32_t j_d2i(double d) {
    if (isnan(d)) {
        return 0;
    }
    if (d >= 2147483648.0) {                   /* 2^31 */
        return INT32_MAX;
    }
    if (d <= -2147483648.0) {
        return INT32_MIN;
    }
    return (int32_t) d;
}

/* Java's long / long, for d != 0 (Java throws for 0; the caller checks):
 * truncates toward 0, and Long.MIN_VALUE / -1 is Long.MIN_VALUE. */
static inline int64_t j_div64(int64_t n, int64_t d) {
    return d == -1 ? (int64_t) (0 - (uint64_t) n) : n / d;
}

/* Java's long % long, for d != 0: the sign of n; x % -1 is 0. */
static inline int64_t j_rem64(int64_t n, int64_t d) {
    return d == -1 ? 0 : n % d;
}

/* Java's int / int and int % int, for d != 0: Integer.MIN_VALUE / -1 is
 * Integer.MIN_VALUE, and x % -1 is 0. */
static inline int32_t j_div32(int32_t n, int32_t d) {
    return d == -1 ? (int32_t) (0 - (uint32_t) n) : n / d;
}

static inline int32_t j_rem32(int32_t n, int32_t d) {
    return d == -1 ? 0 : n % d;
}

/* Java's Math.floorDiv(long, long), for d != 0. */
static inline int64_t j_floor_div64(int64_t n, int64_t d) {
    int64_t q = j_div64(n, d);
    if (j_rem64(n, d) != 0 && (n < 0) != (d < 0)) {
        q--;
    }
    return q;
}

/* Java's Long.compare: -1, 0 or 1, signed. */
static inline int j_cmp64(int64_t a, int64_t b) {
    return a < b ? -1 : (a == b ? 0 : 1);
}

/* Java's Long.compareUnsigned: -1, 0 or 1. */
static inline int j_cmpu64(int64_t a, int64_t b) {
    uint64_t ua = (uint64_t) a;
    uint64_t ub = (uint64_t) b;
    return ua < ub ? -1 : (ua == ub ? 0 : 1);
}

/* Java's Long.numberOfLeadingZeros: 64 for 0. */
static inline int j_nlz64(int64_t v) {
    uint64_t u = (uint64_t) v;
    int n = 0;
    if (u == 0) {
        return 64;
    }
    while ((u & UINT64_C(0x8000000000000000)) == 0) {
        u <<= 1;
        n++;
    }
    return n;
}

/* Java's Double.doubleToRawLongBits and Double.longBitsToDouble. */
static inline int64_t j_double_bits(double d) {
    union { double d; int64_t l; } u;
    u.d = d;
    return u.l;
}

static inline double j_bits_double(int64_t l) {
    union { double d; int64_t l; } u;
    u.l = l;
    return u.d;
}

/* Java's Float.floatToRawIntBits and Float.intBitsToFloat. */
static inline int32_t j_float_bits(float f) {
    union { float f; int32_t i; } u;
    u.f = f;
    return u.i;
}

static inline float j_bits_float(int32_t i) {
    union { float f; int32_t i; } u;
    u.i = i;
    return u.f;
}

#endif
