015-31. Fix: a cut at the stream's length throws an internal Bug
================================================================

Status: done 2026-11-05, night 006-12. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: `FileStream.pretruncate` at `pos == getLength()` throws `Bug` ("Unexpected newSize: 0"). Internal only: reclaim cuts behind its tail. No data lost on `main`; 2026.1 deleted the files before it threw.

Source: review R2, R2-F2 (items/016-release-2026-2/06-reviews/R2.md),
confirmed by verify-2 (items/016-release-2026-2/06-reviews/verify-2.md,
section R2-F2), with its probe, the reach and the effect.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: the probe of R2-F2, made a test.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-05. The harness of 018-02 (the stream contract, 018-01, section
6.3) catches it: `StreamContractTester.testFileStream`, checks "a cut at
the length", 0 and 3, fail and name 015-31. Its fix removes the skip line
"015-31" from `StreamContract.SKIP`.

2026-11-05. Done in night 006-12. Harness 6.3 is the test: with the line
"015-31" removed from `StreamContract.SKIP`,
`StreamContractTester.testFileStream` failed before the fix ("a cut at the
length", 0 and 3: `Bug: Unexpected newSize: 0`) and passes after it.

* Fix: `FileStream.pretruncate` keeps the last file, as it keeps a file
  that the cut ends in: its loop that picks the files to take off stops
  before the last one, R2's proposal. At the length, the files before the
  last are taken off and the first position is the last file's start; the
  `Bug` check, now unreachable, went.
* Reach: internal; `BufferedStream` passes on a cut at its flushed length,
  and a kept cut equal to it, which failed the storage with this `Bug`;
  Db's reclaim cuts behind its tail. 010-01: no setting, thread or format
  change; the stream's bytes are unchanged (the files on disk differ only
  for a cut that threw before).
