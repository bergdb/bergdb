015-33. Fix: setMax2G(true) still allows files over two billion bytes
=====================================================================

Status: done 2026-11-05, night 006-12. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: `FileStream.setMax2G(true)` can still make a file larger than 2^31 bytes. Internal only: nothing in `java/src` calls it.

Source: review R2, R2-F4 (items/016-release-2026-2/06-reviews/R2.md),
confirmed by verify-2 (items/016-release-2026-2/06-reviews/verify-2.md,
section R2-F4), with its probe, the reach and the effect.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: the probe of R2-F4, made a test.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-05. The harness of 018-02 (the stream contract, 018-01, section
6.3) catches it: `StreamContractTester.testFileStreamSizeLimit` makes
R2-F4's directory directly, with sparse files, in 0.07 s, and fails and
names 015-33 (a file of 2,100,000,000 bytes). Its fix removes the skip
line "015-33" from `StreamContract.SKIP`.

2026-11-05, night 006-12. Done. With the line "015-33" removed from
`StreamContract.SKIP`, `StreamContractTester.testFileStreamSizeLimit` failed
before the fix, "with setMax2G(true), the file 00000000400000.bergdb has
2100000000 bytes, more than 2 GB", and passes after it (0.2 s, sparse files).

* Fix: `FileStream.determineFileSizeIndex` caps its result at `INDEX_2G` when
  max2G is on, as R2-F4 proposed; it capped only when the current index was
  above it, so a start that chose 100 MB files from the last two could jump to
  the size rule's 10 GB. One change in behaviour besides the cap: a stream
  whose current size is above 2 GB (files written without the limit) now
  takes a smaller size when the rule says so, where it took 2 GB; both are
  within the cap.
* Javadoc of `setMax2G`: the cap holds for the files that the stream creates
  after the call; a stream written without it can have larger files, and its
  last file can still grow to the size chosen at the start (its size limit is
  set when the stream opens it). Nothing in `java/src` calls `setMax2G`; the
  harness calls it right after the constructor.
* Test: harness 6.3's `testFileStreamSizeLimit`; the skip line is removed.
  `FileStream.testFileSizeRules1` (the max2G rules) passes unchanged.
* 010-01: no setting, no state, no thread (P3, P9, P10). Only the sizes of the
  files with max2G on change, never the stream's bytes; no database of BergDB
  sets it (P2).
* Gate: `before-commit.sh`: `BEFORE COMMIT OK (108 s)`, unit 1177, f 83.
