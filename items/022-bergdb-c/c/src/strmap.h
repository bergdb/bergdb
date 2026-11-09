/*
 * strmap: a string-to-string map that is written as text, ported from
 * Java's bergdb.common.StringMap (bergdb 012-09, part 1; 012-02, 8.13):
 * reclaim's table and its current row are StringMap texts in the stream
 * (Reclaim.IterationInfo.serialize), one "key=value\n" line a pair, in the
 * order of Java's HashMap<String, String>. Prefix sm_.
 *
 * The order (sm_serialize) is HashMap's iteration order, reproduced: the
 * table's buckets in order, and in a bucket the keys in the order they were
 * first put. A key's bucket is (n - 1) & (h ^ (h >>> 16)), h its
 * String.hashCode() (over its UTF-16 code units, decoded from the key's
 * UTF-8) and n the table's size: 16 at the first put, doubled when the
 * pairs exceed three quarters of it, or when a bucket gets its ninth key
 * while the table is smaller than 64 (HashMap.treeifyBin). A bucket of nine
 * keys in a table of 64 or more, which Java makes a tree, is refused
 * (ERR_ARG): its order is not ported, and reclaim's rows have 11 keys.
 * Since the map has no removal, splits at a resize keep each bucket's
 * order, and so this order is HashMap's. For reclaim's 11 names it is
 * pCut, tEnd, cut, pStart, tStart, lastKey, rewritten, pEnd, pSafe, done,
 * kvCount.
 *
 * Keys and values are C strings (UTF-8, as Java's text in the stream), and
 * copies of them are kept (MEM_STATE).
 */
#ifndef BERGDB_STRMAP_H
#define BERGDB_STRMAP_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include "err.h"
#include "mem.h"

struct sm_entry {
    char *key;
    char *value;
    size_t key_size;        /* the allocations, with their NULs */
    size_t value_size;
    int32_t hash;           /* HashMap.hash(key) */
    int32_t order;          /* when the key was first put */
};

struct sm {
    struct mem *mem;
    struct sm_entry *entries;
    int32_t n;
    int32_t cap;
    int32_t tableSize;      /* HashMap's table: 0 before the first put */
    int32_t threshold;
};

/* new StringMap(): an empty map. */
void sm_init(struct sm *m, struct mem *mem);

/* Frees the pairs. */
void sm_free(struct sm *m);

/* String.hashCode() of a UTF-8 text of n bytes: s[0]*31^(k-1) + ... over
 * its k UTF-16 code units (a 4-byte sequence is two; a byte that is not
 * valid UTF-8 counts as U+FFFD, as Java's decoder gives). */
int32_t sm_string_hash(const char *s, size_t n);

/* StringMap.put: the key (not empty, asserted) gets the value; a new key
 * goes last in its bucket. ERR_NOMEM, and the map as it was; ERR_ARG for a
 * bucket that Java would make a tree. */
enum err_code sm_put(struct sm *m, const char *key, const char *value, struct err *e);

/* StringMap.get: the key's value, or NULL. */
const char *sm_get(const struct sm *m, const char *key);

/* StringMap.hasLong: the key has a value that Long.parseLong takes. */
bool sm_has_long(const struct sm *m, const char *key);

/* StringMap.getLong: the value as Long.parseLong parses it (an optional
 * sign, decimal digits, in the long's range). ERR_FORMAT,
 * "NumberFormatException", for no value ("No value for key K") or another
 * text. */
enum err_code sm_get_long(const struct sm *m, const char *key, int64_t *out, struct err *e);

/* Long.parseLong of n bytes, ASCII digits: false where it throws. */
bool sm_parse_long(const char *s, size_t n, int64_t *out);

/* StringMap.parse: the text's lines (split at '\n'), each trimmed (the
 * bytes up to ' ' at both ends, String.trim()), and those with a '='
 * after their first character put, the key before the first '=' and the
 * value after it. The pairs are put in the text's order. Errors as
 * sm_put's. */
enum err_code sm_parse(struct sm *m, const char *s, size_t n, struct err *e);

/* StringMap.serialize: "key=value\n" for each pair, in HashMap's order,
 * into *out, a NUL-terminated text of *n bytes allocated through the map's
 * mem (MEM_BUFFER, *n + 1 bytes), which the caller frees. ERR_NOMEM. */
enum err_code sm_serialize(const struct sm *m, char **out, size_t *n, struct err *e);

#endif
