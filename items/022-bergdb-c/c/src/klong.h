/*
 * klong: the 64-bit words of the index nodes, "klongs"; ported from Java's
 * bergdb.dag.Klong, whose comment has the format. In short, bit 0 is the
 * least significant:
 *
 *   bits 0-2    version, always 0;
 *   bits 3-5    LENGTH, the key bytes in this klong, 0 to 7;
 *   bits 6-61   DATA, up to 7 key bytes, the first in bits 54-61;
 *   bits 62-63  TYPE: 0 time, 1 key, 3 delete bitmap.
 *
 * A TIME klong has the time in its low 56 bits (0 to KL_MAX_TIME). A compare
 * value is a key klong without its type bits: the bytes and the length, a
 * non-negative long, ordered as the keys. Prefix kl_.
 *
 * Java's (byte[] key, int offset, int length) is (key + offset, length).
 * Left out for now: toString and getKeyString (Java's debug text; the
 * dumper of 012-05 and 012-06 decides its own).
 */
#ifndef BERGDB_KLONG_H
#define BERGDB_KLONG_H

#include <stdbool.h>
#include <stdint.h>
#include "jsem.h"

#define KL_MIN_TIME INT64_C(0)
#define KL_MAX_TIME INT64_C(0x00ffffffffffffff)

#define KL_TYPE_TIME INT64_C(0)
#define KL_TYPE_KEY INT64_C(0x4000000000000000)
#define KL_TYPE_DELETE_BITMAP J64(0xc000000000000000)

#define KL_INT_TYPE_TIME 0
#define KL_INT_TYPE_KEY 1
#define KL_INT_TYPE_DELETE_BITMAP 3

/* The maximum number of key bytes in one klong. */
#define KL_MAX_SIZE 7

/* Marker klong for "no klong": a TIME klong of KL_MAX_TIME + 1. */
#define KL_NULL INT64_C(0x0100000000000000)

/* A KEY klong of the empty key. */
#define KL_EMPTY_KEY KL_TYPE_KEY

/* Delete bitmaps with no bit set and with all 62 bits set. */
#define KL_DELETE_NONE_BITMAP KL_TYPE_DELETE_BITMAP
#define KL_DELETE_ALL_BITMAP (KL_TYPE_DELETE_BITMAP | INT64_C(0x3fffffffffffffff))

/* A TIME klong; time in KL_MIN_TIME to KL_MAX_TIME (asserted). */
int64_t kl_create_time(int64_t time);

/* A KEY klong of key[0] to key[length - 1]; length 0 to 7 (asserted). */
int64_t kl_create_key(const uint8_t *key, int32_t length);

/* An empty delete bitmap; kl_delete sets bit i (0 to 61), kl_is_deleted
 * reads it. */
int64_t kl_create_delete(void);
int64_t kl_delete(int64_t klong, int32_t bit_index);
/* Klong.DELETE_BITS[bit_index]: 2^bit_index, bit_index 0 to 61 (asserted,
 * where Java's array index throws). */
int64_t kl_delete_bit(int32_t bit_index);
bool kl_is_deleted(int64_t klong, int32_t bit_index);

/* The time of a TIME klong (asserted). */
int64_t kl_get_time(int64_t value);

int64_t kl_set_header(int64_t klong, int64_t type, int64_t length);
int64_t kl_get_type(int64_t value);
int64_t kl_set_type(int64_t klong, int64_t type);
bool kl_is_key(int64_t klong);
bool kl_is_time(int64_t klong);
/* The type as 0, 1 or 3. */
int32_t kl_get_int_type(int64_t value);
int32_t kl_get_length(int64_t value);

/* Writes the key bytes to output[0..]; returns their number, 0 to 7. */
int32_t kl_get_key(int64_t value, uint8_t *output);

/* The key data, bits 6 to 61, shifted down by 6. */
int64_t kl_get_key_value(int64_t klong);

/* The compare value of a key klong: the bytes and the length. */
int64_t kl_get_compare_value(int64_t value);

/* The compare value of key[0] to key[length - 1]; length 0 to 7. */
int64_t kl_create_compare_value(const uint8_t *key, int32_t length);

int64_t kl_compare_value_to_key_klong(int64_t compare_value);

/* The length of the common prefix of two KEY klongs, 0 to 7. */
int32_t kl_prefix_length(int64_t k1, int64_t k2);

#endif
