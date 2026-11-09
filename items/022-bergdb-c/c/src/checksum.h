/*
 * checksum: the 16-bit Fletcher checksums of stored nodes; ported from
 * Java's bergdb.core.NodeChecksum. Prefix cks_.
 *
 * Java's (data, offset, length) is kept, since sumWithZeroReplace's
 * replaceOffset counts from the start of data, as in Java.
 */
#ifndef BERGDB_CHECKSUM_H
#define BERGDB_CHECKSUM_H

#include <stdint.h>

/* Fletcher-16 of data[offset] to data[offset + length - 1]:
 * sum1 | (sum2 << 8). */
int32_t cks_sum(const uint8_t *data, int32_t offset, int32_t length);

/* As cks_sum, with the two bytes at data[replace_offset] and
 * data[replace_offset + 1] taken as 0. */
int32_t cks_sum_with_zero_replace(const uint8_t *data, int32_t offset, int32_t length,
        int32_t replace_offset);

/* Fletcher-16 of longs, each as 8 little-endian bytes. */
int32_t cks_sum_longs(const int64_t *data, int32_t offset, int32_t length);

#endif
