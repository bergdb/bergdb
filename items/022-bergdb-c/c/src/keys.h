/*
 * keys: database keys in their three forms; ported from Java's
 * bergdb.dag.Keys. Prefix keys_.
 *
 *   ikey      the user's key, a UTF-8 string in Java, its bytes here:
 *             well-formed UTF-8, as every string BergDB stores (bergdb
 *             021-04);
 *   bkey      the bytes the database stores: '/' is 1, every other byte
 *             is the ikey's byte plus 2. The Core takes any bkey; one that
 *             is not an ikey's has no ikey (021-06);
 *   segments  the bkey as compare values (klong.h), 7 bytes each, in
 *             (length + 7) / 7 segments: the last has 0 to 6 bytes, so a
 *             bkey of 7 bytes has two segments, the second of length 0.
 *
 * Left out for now: isPrintableAscii (with toStringBytes, its map of any
 * bkey), toDisplayString and toStringWithSubstitute (display text; the
 * dumper decides its own).
 */
#ifndef BERGDB_KEYS_H
#define BERGDB_KEYS_H

#include <stdbool.h>
#include <stdint.h>

/* The hash of a key's segments, as used by KeyModSet: always non-negative,
 * also where Java's sum is Long.MIN_VALUE (bergdb 005-21). */
int64_t keys_hash(const int64_t *segments, int32_t n);

/* Java's toBytes(String): the ikey's n bytes to bkey bytes in out[0..n-1];
 * ikey and out may be the same. Refuses (returns false), with nothing
 * written, the empty key, as Java throws IllegalArgumentException, and
 * bytes that are not well-formed UTF-8 (su_is_well_formed_utf8), as Java
 * throws it for a String with a lone surrogate, whose UTF-8 would be '?'
 * (bergdb 021-05); a C caller can give any bytes, Java's String has no
 * other. */
bool keys_ikey_to_bkey(const uint8_t *ikey, int32_t n, uint8_t *out);

/* Java's bkey2ikeyOrNull (bergdb 021-06), before its UTF-8 decoding: the
 * bkey's n bytes to the ikey's bytes in out[0..n-1], the byte 1 as '/' and
 * every other less 2; bkey and out may be the same. Refuses (returns
 * false, where Java returns null) a bkey without an ikey: one with the
 * byte 0 or 0x31 ('/' + 2, which no ikey gives, '/' being 1), or whose
 * bytes so mapped are not well-formed UTF-8; out is then partly written.
 * So two bkeys never give one ikey: keys_ikey_to_bkey of the ikey gives
 * the bkey. The empty bkey gives the empty ikey (Java's ""), which
 * keys_ikey_to_bkey refuses. */
bool keys_bkey_to_ikey(const uint8_t *bkey, int32_t n, uint8_t *out);

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
