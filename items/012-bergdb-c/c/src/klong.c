/* klong: ported from Java's bergdb.dag.Klong, line for line. */
#include "klong.h"
#include "jsem.h"
#include <assert.h>

int64_t kl_create_time(int64_t time) {
    assert(time >= KL_MIN_TIME);
    assert(time <= KL_MAX_TIME);
    int64_t klong = kl_set_type(time, KL_TYPE_TIME);
    return klong;
}

int64_t kl_create_delete(void) {
    return KL_DELETE_NONE_BITMAP;
}

/* Java's DELETE_BITS[bitIndex]: 2^bitIndex. */
static int64_t delete_bit(int32_t bitIndex) {
    return j_shl64(1, bitIndex);
}

int64_t kl_delete(int64_t klong, int32_t bitIndex) {
    assert(bitIndex >= 0 && bitIndex < 62);
    return klong | delete_bit(bitIndex);
}

bool kl_is_deleted(int64_t klong, int32_t bitIndex) {
    assert(bitIndex >= 0 && bitIndex < 62);
    return (klong & delete_bit(bitIndex)) != 0;
}

int64_t kl_create_key(const uint8_t *key, int32_t keyLength) {
    int64_t value = 0;
    int shift = 6*8 + 6;
    int32_t keyOffset = 0;
    assert(keyLength >= 0 && keyLength < 8);

    for (int32_t i = 0; i < keyLength; i++) {
        value |= j_shl64(0x00ff & key[keyOffset++], shift);
        shift -= 8;   /* shifts 54, 46, 38, 30, 22, 14, 6 bits. */
    }

    value = (KL_TYPE_KEY | ((int64_t) keyLength << 3)) | (value & INT64_C(0x3fffffffffffffc0));
    return value;
}

int64_t kl_get_time(int64_t value) {
    assert(kl_get_type(value) == KL_TYPE_TIME);
    return value & INT64_C(0x00ffffffffffffff);
}

int64_t kl_set_header(int64_t klong, int64_t type, int64_t length) {
    return (type | (length << 3)) | (klong & INT64_C(0x3fffffffffffffc0));
}

int64_t kl_get_type(int64_t value) {
    return value & J64(0xc000000000000000);  /* Byte 7: 1100 0000 = c0 */
}

int64_t kl_set_type(int64_t klong, int64_t type) {
    return (klong & INT64_C(0x3fffffffffffffff)) | type;
}

bool kl_is_key(int64_t klong) {
    return kl_get_type(klong) == KL_TYPE_KEY;
}

bool kl_is_time(int64_t klong) {
    return kl_get_type(klong) == KL_TYPE_TIME;
}

int32_t kl_get_int_type(int64_t value) {
    return j_l2i(j_ushr64(value & J64(0xc000000000000000), 7*8 + 6));
}

int32_t kl_get_length(int64_t value) {
    return j_l2i(j_ushr64(value & INT64_C(0x0000000000000038), 3));
}

int32_t kl_get_key(int64_t value, uint8_t *output) {
    int32_t length = kl_get_length(value);
    int shift = 6*8 + 6;
    int64_t b;

    for (int32_t i = 0; i < length; i++) {
        b = j_ushr64(value, shift) & 0x00000000000000ff;
        shift -= 8;
        output[i] = (uint8_t) b;
    }

    return length;
}

int64_t kl_get_key_value(int64_t klong) {
    return j_ushr64(klong & INT64_C(0x3fffffffffffffc0), 6);
}

int64_t kl_get_compare_value(int64_t value) {
    return value & INT64_C(0x3ffffffffffffff8);
}

int64_t kl_create_compare_value(const uint8_t *key, int32_t length) {
    int64_t value = 0;
    int shift = 6*8 + 6;
    int32_t offset = 0;
    assert(length >= 0 && length < 8);

    for (int32_t i = 0; i < length; i++) {
        value |= j_shl64(0x00ff & key[offset++], shift);
        shift -= 8;   /* shifts 54, 46, 38, 30, 22, 14, 6 bits. */
    }
    return value | (length << 3);
}

int64_t kl_compare_value_to_key_klong(int64_t compareValue) {
    return compareValue | KL_TYPE_KEY;
}

int32_t kl_prefix_length(int64_t k1, int64_t k2) {
    int32_t length1 = kl_get_length(k1);
    int32_t length2 = kl_get_length(k2);
    int32_t length = length2 > length1 ? length1 : length2;

    int64_t v1 = kl_get_key_value(k1);
    int64_t v2 = kl_get_key_value(k2);
    int32_t result = 0;

    /* If prefix length at least 3 */
    if (length >= 3 && ((v1 & INT64_C(0x00ffffff00000000)) == (v2 & INT64_C(0x00ffffff00000000)))) {
        result = 3;
        result += (v1 & INT64_C(0x00ffffffff000000)) == (v2 & INT64_C(0x00ffffffff000000)) ? 1 : 0;
        result += (v1 & INT64_C(0x00ffffffffff0000)) == (v2 & INT64_C(0x00ffffffffff0000)) ? 1 : 0;
        result += (v1 & INT64_C(0x00ffffffffffff00)) == (v2 & INT64_C(0x00ffffffffffff00)) ? 1 : 0;
        result += (v1 & INT64_C(0x00ffffffffffffff)) == (v2 & INT64_C(0x00ffffffffffffff)) ? 1 : 0;
    } else {
        result =  (v1 & INT64_C(0x00ff000000000000)) == (v2 & INT64_C(0x00ff000000000000)) ? 1 : 0;
        result += (v1 & INT64_C(0x00ffff0000000000)) == (v2 & INT64_C(0x00ffff0000000000)) ? 1 : 0;
    }
    result = result > length ? length : result;

    return result;
}
