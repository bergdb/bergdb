/*
 * bytes: numbers in byte arrays, little-endian and big-endian; ported from
 * Java's bergdb.common.Bytes. Prefix bytes_.
 *
 * Java's (byte[] arr, int offset) is a pointer here: Java's
 * Bytes.bytesToLongLE(buf, off) is bytes_get_long_le(buf + off). Bytes in
 * buffers are uint8_t, so Java's Bytes.unsigned(b) is the byte itself.
 * Left out: stringToBytes (a C string is its bytes already).
 */
#ifndef BERGDB_BYTES_H
#define BERGDB_BYTES_H

#include <stdbool.h>
#include <stdint.h>

int64_t bytes_get_long_le(const uint8_t *p);
void bytes_put_long_le(int64_t v, uint8_t *p);
int64_t bytes_get_long_be(const uint8_t *p);
void bytes_put_long_be(int64_t v, uint8_t *p);

int32_t bytes_get_int_le(const uint8_t *p);
void bytes_put_int_le(int32_t v, uint8_t *p);
int32_t bytes_get_int_be(const uint8_t *p);
void bytes_put_int_be(int32_t v, uint8_t *p);

int16_t bytes_get_short_le(const uint8_t *p);
/* Java's shortToBytesLE takes a long and writes its low 16 bits. */
void bytes_put_short_le(int64_t v, uint8_t *p);

/* An unsigned short, 0 to 65535. */
int32_t bytes_get_ushort_le(const uint8_t *p);
/* Refuses (returns false, writes nothing) a value outside 0 to 65535, where
 * Java throws IllegalArgumentException. */
bool bytes_put_ushort_le(int32_t v, uint8_t *p);

float bytes_get_float_le(const uint8_t *p);
void bytes_put_float_le(float v, uint8_t *p);
double bytes_get_double_le(const uint8_t *p);
void bytes_put_double_le(double v, uint8_t *p);

/* Java's longsToBytesLE(longs, longOffset, n, bytes, byteOffset), with the
 * offsets in the pointers: n longs, 8 bytes each. */
void bytes_longs_to_le(const int64_t *longs, int32_t n, uint8_t *p);

#endif
