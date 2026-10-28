/*
 * spos: stream positions; ported from Java's bergdb.dag.Spos. A valid
 * position is non-negative; SPOS_NULL is "no position"; an odd position of
 * an index node is a vpos (a virtual position, bergdb item 009).
 * Prefix spos_.
 */
#ifndef BERGDB_SPOS_H
#define BERGDB_SPOS_H

#include <stdbool.h>
#include <stdint.h>

#define SPOS_NULL INT64_C(-1)

bool spos_is_valid(int64_t spos);
/* The next vpos: always odd and greater than vpos. */
int64_t spos_next_vpos(int64_t vpos);
/* True if pos is newer than ref: a position is newer than a vpos, whatever
 * their numbers, and than a smaller position (bergdb item 009, rule R). */
bool spos_newer(int64_t pos, int64_t ref);
bool spos_is_vpos(int64_t spos);
bool spos_is_valid_or_null(int64_t spos);
bool spos_is_null(int64_t spos);
/* What to add to a so that (a + result) % mod == 0. */
int32_t spos_add_to_align(int32_t a, int32_t mod);

#endif
