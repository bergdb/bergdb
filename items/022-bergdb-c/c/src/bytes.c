/* bytes: ported from Java's bergdb.common.Bytes, line for line. */
#include "bytes.h"
#include "jsem.h"

/* Java's (arr[i] & 0x000000ffL). */
static int64_t ub(const uint8_t *p, int i) {
    return (int64_t) (p[i] & 0xff);
}

int64_t bytes_get_long_le(const uint8_t *p) {
    int i = 0;
    int64_t result = ub(p, i++);
    result |= j_shl64(ub(p, i++), 8);
    result |= j_shl64(ub(p, i++), 16);
    result |= j_shl64(ub(p, i++), 24);
    result |= j_shl64(ub(p, i++), 32);
    result |= j_shl64(ub(p, i++), 40);
    result |= j_shl64(ub(p, i++), 48);
    result |= j_shl64(ub(p, i), 56);
    return result;
}

void bytes_put_long_le(int64_t value, uint8_t *p) {
    int i = 0;
    p[i++] = (uint8_t) value;
    p[i++] = (uint8_t) j_ushr64(value, 8);
    p[i++] = (uint8_t) j_ushr64(value, 16);
    p[i++] = (uint8_t) j_ushr64(value, 24);
    p[i++] = (uint8_t) j_ushr64(value, 32);
    p[i++] = (uint8_t) j_ushr64(value, 40);
    p[i++] = (uint8_t) j_ushr64(value, 48);
    p[i] = (uint8_t) j_ushr64(value, 56);
}

int64_t bytes_get_long_be(const uint8_t *p) {
    int i = 0;
    int64_t result = j_shl64(ub(p, i++), 56);
    result |= j_shl64(ub(p, i++), 48);
    result |= j_shl64(ub(p, i++), 40);
    result |= j_shl64(ub(p, i++), 32);
    result |= j_shl64(ub(p, i++), 24);
    result |= j_shl64(ub(p, i++), 16);
    result |= j_shl64(ub(p, i++), 8);
    result |= ub(p, i);
    return result;
}

void bytes_put_long_be(int64_t v, uint8_t *p) {
    int i = 0;
    p[i++] = (uint8_t) j_ushr64(v, 56);
    p[i++] = (uint8_t) j_ushr64(v, 48);
    p[i++] = (uint8_t) j_ushr64(v, 40);
    p[i++] = (uint8_t) j_ushr64(v, 32);
    p[i++] = (uint8_t) j_ushr64(v, 24);
    p[i++] = (uint8_t) j_ushr64(v, 16);
    p[i++] = (uint8_t) j_ushr64(v, 8);
    p[i] = (uint8_t) v;
}

/* Java's (arr[i] & 0x00ff), an int. */
static int32_t ubi(const uint8_t *p, int i) {
    return p[i] & 0xff;
}

int32_t bytes_get_int_le(const uint8_t *p) {
    int i = 0;
    int32_t result = ubi(p, i++);
    result |= j_shl32(ubi(p, i++), 8);
    result |= j_shl32(ubi(p, i++), 16);
    result |= j_shl32(ubi(p, i), 24);
    return result;
}

void bytes_put_int_le(int32_t value, uint8_t *p) {
    int i = 0;
    p[i++] = (uint8_t) value;
    p[i++] = (uint8_t) j_ushr32(value, 8);
    p[i++] = (uint8_t) j_ushr32(value, 16);
    p[i] = (uint8_t) j_ushr32(value, 24);
}

int32_t bytes_get_int_be(const uint8_t *p) {
    int i = 0;
    int32_t result = j_shl32(ubi(p, i++), 24);
    result |= j_shl32(ubi(p, i++), 16);
    result |= j_shl32(ubi(p, i++), 8);
    result |= ubi(p, i);
    return result;
}

void bytes_put_int_be(int32_t v, uint8_t *p) {
    int i = 0;
    p[i++] = (uint8_t) j_ushr32(v, 24);
    p[i++] = (uint8_t) j_ushr32(v, 16);
    p[i++] = (uint8_t) j_ushr32(v, 8);
    p[i] = (uint8_t) v;
}

int16_t bytes_get_short_le(const uint8_t *p) {
    int i = 0;
    int32_t result = ubi(p, i++);
    result |= j_shl32(ubi(p, i), 8);
    return j_l2s(result);
}

void bytes_put_short_le(int64_t value, uint8_t *p) {
    int i = 0;
    p[i++] = (uint8_t) value;
    p[i] = (uint8_t) j_ushr64(value, 8);
}

int32_t bytes_get_ushort_le(const uint8_t *p) {
    /* Java adds 256 to a negative byte: the same as reading it unsigned. */
    int32_t b0 = p[0];
    int32_t b1 = p[1];
    return b0 + 256 * b1;
}

bool bytes_put_ushort_le(int32_t value, uint8_t *p) {
    if (value < 0 || value >= 65536) {
        return false;
    }
    p[0] = (uint8_t) (value % 256);
    p[1] = (uint8_t) (value / 256);
    return true;
}

float bytes_get_float_le(const uint8_t *p) {
    return j_bits_float(bytes_get_int_le(p));
}

void bytes_put_float_le(float v, uint8_t *p) {
    bytes_put_int_le(j_float_bits(v), p);
}

double bytes_get_double_le(const uint8_t *p) {
    return j_bits_double(bytes_get_long_le(p));
}

void bytes_put_double_le(double v, uint8_t *p) {
    bytes_put_long_le(j_double_bits(v), p);
}

void bytes_longs_to_le(const int64_t *longs, int32_t n, uint8_t *p) {
    for (int32_t i = 0; i < n; i++) {
        bytes_put_long_le(longs[i], p + 8 * i);
    }
}
