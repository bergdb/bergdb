005-15. Fix: long-index range scans skip or add entries
======================================================

Status: done (2026-10-21). Kind: fix. Created 2026-10-21.

Found on 2026-10-21 in a review of the Java code for overflow, by Claude
(Opus 5.5, Claude Code), at Frans's request; checked with a probe through the
public API.


The issue
---------

`UseIndexBuilderImp.plusOne` makes "the smallest key that is greater than all
keys with this prefix". It adds one to the last byte that is not `0xff`, but
leaves the `0xff` bytes after it as they are: `{.., 0x00, 0xff}` becomes
`{.., 0x01, 0xff}`, not `{.., 0x01, 0x00}`. It is used for the start key of
a secondary index scan with `inclusive(false)` forward, and with `backward()`.

A long index stores a value v as the big-endian bytes of v ^ 2^63, so every
value whose low byte is `0xff` (255, 511, -1, -257, ...) ends in `0xff`.
With values from -300 to 600:

* `startAt(255).inclusive(false)` returned 511, 512, 600; 256 to 510 were
  missing.
* `startAt(-1).inclusive(false)` returned nothing; it skips every value up
  to 2^56 − 1.
* `startAt(255).backward()` returned 510, 300, 257, 256 before 255.
* `eq(255).backward()` and `eq(-1).backward()` returned nothing.

Double indexes are hit when the sort bytes end in `0xff`, which is rare.
String sort bytes end with 0, so string indexes are not. `plusOneArray`, in
the same class, carries correctly, but only tests use it. The code is from
the 2017 import.


The fix
-------

`plusOne` sets the bytes after the one it increments to 0, as
`plusOneArray` does.


Done when
---------

* A unit test with long values around 255 and -1, forward with
  `inclusive(false)`, backward, and `eq` backward, fails before and passes
  after.
* `java/before-commit.sh` prints `BEFORE COMMIT OK`.


Outcome
-------

2026-10-21, by Claude (Opus 5.5, Claude Code). `plusOne` sets the bytes
after the one it increments to 0. New tests: `UseIndexBuilderImp.testPlusOneCarry`
and `PubTesterIndex.testStartKeyCarry` (long values around 255, -1 and -257:
exclusive forward, backward, backward exclusive, `eq` backward); the second
failed without the fix ("Expected '[256, 257, 300, 510, 511, 512]', got
'[511, 512]'"). `before-commit.sh`: BEFORE COMMIT OK (940 unit tests, 59
f-tests).
