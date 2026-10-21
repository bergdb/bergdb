005-26. Fix: a string with a lone surrogate cannot be stored in an array
========================================================================

Status: done (2026-10-21). Kind: fix. Created 2026-10-21.

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


Outcome
-------

2026-10-21, by Claude (Opus 5.5, Claude Code). `StringUtil.utf8Size`
counts 4 bytes for a high surrogate followed by a low one, and 1 byte for
any other surrogate, as Java's UTF-8 encoder writes. Data stored before is
read as before: in a `DbObject` the old sizes left padding, and arrays with
such strings could not be stored at all.

Tests: `StringUtil.testUtf8Size` with seven more strings (lone, reversed
and paired surrogates), and `DbObjectTester.testLoneSurrogates` (an
object whose `String[]` and `String` fields have lone surrogates is
stored and read back, with `?` for each). `before-commit.sh`: BEFORE
COMMIT OK (961 unit tests, 62 f-tests).
