005-26. Fix: a string with a lone surrogate cannot be stored in an array
========================================================================

Status: open. Kind: fix. Created 2026-10-21.

Found on 2026-10-21 in the review of the Java code for overflow (a size
computation, not an overflow), by Claude (Opus 5.5, Claude Code), at
Frans's request; checked with a probe.


The issue
---------

`StringUtil.utf8Size` counts a high surrogate as 4 bytes and skips the next
char, and a low surrogate as 3 bytes, also when they are not a pair; Java's
UTF-8 encoder writes a lone surrogate as `?`, one byte. `DbString` sizes
its bytes with `utf8Size` and writes the encoder's bytes, so the two
disagree. In a `DbObject` field the extra bytes are padding; in a `DbArray`
the next element is read at the wrong place: a put of an object whose
`String[]` holds `"x\uD800"` fails with "BadFormatException: Bad type".


The fix
-------

`utf8Size` counts as the encoder writes: 4 bytes for a surrogate pair, 1
byte for a lone surrogate.


Done when
---------

* A unit test: `utf8Size` equals the encoder's length for strings with
  lone and paired surrogates, and an object with such strings in an array
  is stored and read back.
* `java/before-commit.sh` prints `BEFORE COMMIT OK`.
