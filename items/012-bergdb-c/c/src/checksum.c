/* checksum: ported from Java's bergdb.core.NodeChecksum, line for line. */
#include "checksum.h"
#include "jsem.h"

int32_t cks_sum(const uint8_t *data, int32_t offset, int32_t length) {
    int32_t sum1 = 0;
    int32_t sum2 = 0;
    int32_t end = offset + length;

    for (int32_t i = offset; i < end; i++) {
        int32_t dataValue = data[i] & 0x000000ff;

        sum1 = (sum1 + dataValue) % 255;
        sum2 = (sum1 + sum2) % 255;
    }

    return sum1 | (sum2 << 8);
}

int32_t cks_sum_with_zero_replace(const uint8_t *data, int32_t offset, int32_t length,
        int32_t replaceOffset) {
    int32_t sum1 = 0;
    int32_t sum2 = 0;
    int32_t dataValue;
    const int32_t end = offset + length;
    const int32_t replaceOffset2 = replaceOffset + 1;

    for (int32_t i = offset; i < end; i++) {
        dataValue = data[i] & 0x000000ff;

        if (i == replaceOffset || i == replaceOffset2) {
            dataValue = 0;
        }

        sum1 = (sum1 + dataValue) % 255;
        sum2 = (sum1 + sum2) % 255;
    }

    return sum1 | (sum2 << 8);
}

int32_t cks_sum_longs(const int64_t *data, int32_t offset, int32_t length) {
    int32_t sum1 = 0;
    int32_t sum2 = 0;
    int32_t end = offset + length;

    for (int32_t i = offset; i < end; i++) {
        int64_t l = data[i];

        for (int j = 0; j < 8; j++) {
            int32_t dataValue = j_l2i(l & 0x000000ff);
            sum1 = (sum1 + dataValue) % 255;
            sum2 = (sum1 + sum2) % 255;
            l = j_ushr64(l, 8);
        }
    }

    return sum1 | (sum2 << 8);
}
