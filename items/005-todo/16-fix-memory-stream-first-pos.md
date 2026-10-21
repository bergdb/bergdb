005-16. Fix: an in-memory database with a retain duration fails after 2^31 bytes
================================================================================

Status: open. Kind: fix. Created 2026-10-21.

Found on 2026-10-21 in a review of the Java code for overflow, by Claude
(Opus 5.5, Claude Code), at Frans's request; checked with a probe.


The issue
---------

`MemoryStream.pretruncate` sets `firstValidPos = firstArrayIndex *
ARRAY_SIZE`, two `int`s. After a cut past 2^31 bytes (2.15 GB written in
all; reclaim never resets positions) `getFirstPos()` is negative:
-2,133,967,296 after a cut at 2,161 MB in the probe. Then:

* `MemoryStream.read` no longer throws `ReadBelowFirstPosException` for a
  read below the cut, but a plain `IOException`. A read admitted before the
  cut that reaches the cut part (docs/levels.md, W1) is then a storage
  failure to `StorageManager.read`: the main stream is closed, and every
  later transaction throws "Main storage not active". At 200 MB the same
  read fails alone and the database goes on.
* The checks that leave stream pointers below the cut alone
  (`NodeCollection.resolvePointers` and `linkToCanonical`) no longer see
  them; not triggered in the probe.

`DatabaseBuilder.memory()` (Pub API) and `DbBuilder.testSetup()` use
`MemoryStream`. Tests use `CutStream`, whose `Math.max` hides it.


The fix
-------

Compute in `long`: `(long) firstArrayIndex * ARRAY_SIZE`.


Done when
---------

* A unit test that cuts a `MemoryStream` past 2^31 bytes and checks
  `getFirstPos()` and the exception of a read below the cut.
* `java/before-commit.sh` prints `BEFORE COMMIT OK`.
