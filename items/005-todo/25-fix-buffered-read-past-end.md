005-25. Fix: a BufferedStream read one byte past the end returns a stale byte
=============================================================================

Status: done (2026-10-21). Kind: fix. Created 2026-10-21.

Found on 2026-10-21 in the review of the Java code for overflow (not an
overflow), by Claude (Opus 5.5, Claude Code), at Frans's request; checked
with a probe.


The issue
---------

`BufferedStream.read` refuses a read when its last byte `pos2 >
totalLength`; it should be `>=`. A read of the byte just after the end
returns a byte from the ring buffer (stale data) instead of an
`IOException`.


The fix
-------

`pos2 >= totalLength`.


Done when
---------

* A unit test: a read that ends one byte past the end throws.
* `java/before-commit.sh` prints `BEFORE COMMIT OK`.


Outcome
-------

2026-10-21, by Claude (Opus 5.5, Claude Code). `BufferedStream.read`
refuses a read whose last byte `pos2 >= totalLength`. A read of length 0 at
the end still passes. Test `BufferedStream.testReadOneBytePastEnd`.
`before-commit.sh`: BEFORE COMMIT OK (960 unit tests, 62 f-tests).
