/* keys: ported from Java's bergdb.dag.Keys, line for line. */
#include "keys.h"
#include "jsem.h"
#include "klong.h"
#include <assert.h>

int64_t keys_hash(const int64_t *keySegments, int32_t n) {
    int64_t value = 37;
    for (int32_t i = 0; i < n; i++) {
        value = value * 37 + keySegments[i];        /* wraps, as Java's long */
    }
    value = value < 0 ? -value : value;
    value &= INT64_MAX;     /* always non-negative, also for Long.MIN_VALUE (005-21) */
    assert(value >= 0);
    return value;
}

bool keys_ikey_to_bkey(const uint8_t *s, int32_t n, uint8_t *bytes) {
    if (n == 0) {
        return false;       /* Java: "The empty string is not a valid key." */
    }

    for (int32_t i = 0; i < n; i++) {
        uint8_t b = s[i];
        if (b == 0xff || b == 0xfe) {
            return false;
        }

        if (b == '/') {
            b = 0x01;
        } else {
            b++;
            b++;
        }
        bytes[i] = b;
    }

    return true;
}

void keys_bkey_to_ikey(const uint8_t *bytes, int32_t n, uint8_t *result) {
    for (int32_t i = 0; i < n; i++) {
        uint8_t b = bytes[i];
        if (b == 1) {
            b = '/';
        } else {
            b--;
            b--;
        }
        result[i] = b;
    }
}

int32_t keys_segment_count(int32_t length) {
    return (length + KL_MAX_SIZE) / KL_MAX_SIZE;
}

void keys_to_segments(const uint8_t *key, int32_t keyLength, int64_t *segments) {
    int32_t size = keys_segment_count(keyLength);
    int32_t offset = 0;
    int32_t length;

    for (int32_t i = 0; i < size; i++) {
        length = keyLength - offset;
        length = length > KL_MAX_SIZE ? KL_MAX_SIZE : length;
        segments[i] = kl_create_compare_value(key + offset, length);
        offset += KL_MAX_SIZE;
    }
}

int32_t keys_byte_size(const int64_t *segments, int32_t n) {
    assert(n > 0);          /* Java: segments[segments.length - 1] throws for none */
    return KL_MAX_SIZE * (n - 1) + kl_get_length(segments[n - 1]);
}

int32_t keys_to_bytes(const int64_t *segments, int32_t n, uint8_t *result) {
    assert(n > 0);
    assert(kl_get_length(segments[n - 1]) < 7);

    int32_t length = kl_get_length(segments[n - 1]);
    length += KL_MAX_SIZE * (n - 1);

    int32_t offset = 0;
    for (int32_t i = 0; i < n; i++) {
        kl_get_key(segments[i], result + offset);
        offset += kl_get_length(segments[i]);
    }

    return length;
}

static int32_t compareLongs(int64_t n1, int64_t n2) {
    return n1 == n2 ? 0 : n1 < n2 ? -1 : +1;
}

static int32_t compareUnsignedLongs(int64_t n1, int64_t n2) {
    return n1 == n2 ? 0 : (((n1 < n2) ^ ((n1 < 0) != (n2 < 0))) ? -1 : +1);
}

int32_t keys_compare_arrays(const int64_t *arr1, int32_t n1, const int64_t *arr2, int32_t n2) {
    int32_t result = 0;
    int32_t length = n1 < n2 ? n1 : n2;

    for (int32_t i = 0; i < length; i++) {
        result = compareUnsignedLongs(arr1[i], arr2[i]);
        if (result != 0) {
            break;
        }
    }

    if (result == 0 && n1 != n2) {
        result = n1 < n2 ? -1 : +1;
    }

    return result;
}

int32_t keys_compare_keys(const int64_t *key1, int32_t n1, const int64_t *key2, int32_t n2) {
    int32_t result = 0;
    int32_t length = n1 < n2 ? n1 : n2;

    for (int32_t i = 0; i < length; i++) {
        result = compareLongs(key1[i], key2[i]);
        if (result != 0) {
            break;
        }
    }

    if (result == 0 && n1 != n2) {
        result = n1 < n2 ? -1 : +1;
    }

    return result;
}

bool keys_are_equal(const int64_t *k1, int32_t n1, const int64_t *k2, int32_t n2) {
    return keys_compare_keys(k1, n1, k2, n2) == 0;
}

bool keys_is_prefix(const int64_t *prefix, int32_t nPrefix, const int64_t *key, int32_t nKey) {
    assert(prefix != 0);
    assert(key != 0);
    assert(nPrefix > 0);
    assert(nKey > 0);

    const int64_t lastPrefixKlong = prefix[nPrefix - 1];
    const int64_t lastKeyKlong = key[nKey - 1];
    const int32_t prefixLength = KL_MAX_SIZE * (nPrefix - 1) + kl_get_length(lastPrefixKlong);
    const int32_t keyLength = KL_MAX_SIZE * (nKey - 1) + kl_get_length(lastKeyKlong);

    if (keyLength <= prefixLength) {
        return false;
    }

    for (int32_t i = 0; i < nPrefix - 1; i++) {
        if (key[i] != prefix[i]) {
            return false;
        }
    }

    const int32_t length = kl_get_length(lastPrefixKlong);
    const int32_t prefixLen = kl_prefix_length(lastPrefixKlong, key[nPrefix - 1]);
    assert(prefixLen <= length);
    bool result = prefixLen == length;
    return result;
}
