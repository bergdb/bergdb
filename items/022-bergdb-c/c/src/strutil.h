/*
 * strutil: text helpers, ported from Java's bergdb.common.StringUtil
 * (bergdb 022-02). Prefix su_.
 *
 * Only isWellFormedUtf8 (bergdb 021-06), which the keys need: BergDB
 * stores every string as well-formed UTF-8 (021-04), so an ikey's bytes
 * must be (keys_ikey_to_bkey, 021-05) and a bkey whose ikey bytes are not
 * has no ikey (keys_bkey_to_ikey, 021-06). Left out: the rest of the class
 * (the decimals, toBytes and utf8Size of a String, isPrintableAscii,
 * hasLoneSurrogate, which takes Java's UTF-16 chars: C's text is bytes).
 */
#ifndef BERGDB_STRUTIL_H
#define BERGDB_STRUTIL_H

#include <stdbool.h>
#include <stdint.h>

/* Java's isWellFormedUtf8(b, offset, length), with b + offset as b: true
 * if the length bytes of b are well-formed UTF-8 (RFC 3629; the Unicode
 * Standard, chapter 3, table 3-7): Unicode scalar values only, each in its
 * shortest form. Not well-formed: a cut sequence, an overlong form (C0
 * 80), a surrogate (ED A0 80), a value above U+10FFFF, and the bytes C0,
 * C1 and F5 to FF. No bytes (length 0) are well-formed. */
bool su_is_well_formed_utf8(const uint8_t *b, int32_t length);

#endif
