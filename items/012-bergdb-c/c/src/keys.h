/*
 * keys: database keys in their three forms; ported from Java's
 * bergdb.dag.Keys. Prefix keys_.
 *
 *   ikey      the user's key, a UTF-8 string in Java, its bytes here;
 *   bkey      the bytes the database stores: '/' is 1, every other byte
 *             is the ikey's byte plus 2;
 *   segments  the bkey as compare values (klong.h), 7 bytes each, in
 *             (length + 7) / 7 segments: the last has 0 to 6 bytes, so a
 *             bkey of 7 bytes has two segments, the second of length 0.
 *
 * Left out for now: isPrintableAscii, toDisplayString and
 * toStringWithSubstitute (display text; the dumper decides its own).
 */
#ifndef BERGDB_KEYS_H
#define BERGDB_KEYS_H

#include <stdbool.h>
#include <stdint.h>

/* The hash of a key's segments, as used by KeyModSet: always non-negative,
 * also where Java's sum is Long.MIN_VALUE (bergdb 005-21). */
int64_t keys_hash(const int64_t *segments, int32_t n);

/* Java's toBytes(String): the ikey's n bytes to bkey bytes in out[0..n-1].
 * Refuses (returns false) the empty key, as Java throws
 * IllegalArgumentException, and a byte 0xfe or 0xff, which UTF-8 never has
 * (Java throws an Error; a C caller can give any bytes); out is then
 * partly written. */
bool keys_ikey_to_bkey(const uint8_t *ikey, int32_t n, uint8_t *out);

/* Java's toStringBytes, used by bkey2ikey: the bkey's n bytes to ikey bytes
 * in out[0..n-1]. Java then decodes them as UTF-8. */
void keys_bkey_to_ikey(const uint8_t *bkey, int32_t n, uint8_t *out);

/* The number of segments of a bkey of length bytes: (length + 7) / 7. */
int32_t keys_segment_count(int32_t length);

/* Java's toSegments(byte[]): the bkey's segments, keys_segment_count(length)
 * of them, in segments[]. */
void keys_to_segments(const uint8_t *key, int32_t length, int64_t *segments);

/* Java's getByteSize: the bkey's length. */
int32_t keys_byte_size(const int64_t *segments, int32_t n);

/* Java's toBytes(long[]): the bkey, keys_byte_size bytes, in out[];
 * returns its length. n > 0 and the last segment shorter than 7
 * (asserted). */
int32_t keys_to_bytes(const int64_t *segments, int32_t n, uint8_t *out);

/* Java's compareArrays: the longs compared unsigned, then the lengths;
 * -1, 0 or 1. */
int32_t keys_compare_arrays(const int64_t *a1, int32_t n1, const int64_t *a2, int32_t n2);

/* Java's compareKeys: the segments compared signed (compare values are
 * non-negative), then the lengths; -1, 0 or 1. */
int32_t keys_compare_keys(const int64_t *k1, int32_t n1, const int64_t *k2, int32_t n2);

bool keys_are_equal(const int64_t *k1, int32_t n1, const int64_t *k2, int32_t n2);

/* True if prefix is a strict prefix of key (n_prefix, n_key > 0). */
bool keys_is_prefix(const int64_t *prefix, int32_t n_prefix, const int64_t *key, int32_t n_key);

#endif
