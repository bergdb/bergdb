015-26. Fix: a negative append length corrupts FileStream's length bookkeeping
==============================================================================

Status: done 2026-11-05, night 006-12. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

After the release (internal; in 2026.1 too).

What: `FileStream.append` with a negative length lowers the stream's length; later reads and appends fail. Internal only: no path from `bergdb.pub` gives a negative length.

Source: review R2, R2-F5 (016-06/R2, items/016-release-2026-2/06-reviews/R2.md),
confirmed by verify-1 (items/016-release-2026-2/06-reviews/verify-1.md,
section R2-F5), with its probe and the reach.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`; or the entry is a known issue
in 2026.2's notes.

First step: the probe of R2-F5, made a test.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-04. Review R5 found the same, or its counterpart in StorageManager (R5-F4, items/016-release-2026-2/06-reviews/R5.md).

2026-11-05. The harness of 018-02 (the stream contract, 018-01, section
6.3) catches it: `StreamContractTester.testFileStream`, check "a negative
append", fails and names 015-26. Its fix removes the skip line "015-26"
from `StreamContract.SKIP`.

2026-11-05, night 006-12. Done. Verified with the harness: with the line
"015-26" removed from `StreamContract.SKIP`, `StreamContractTester.testFileStream`
failed before the fix, "FileStream, a negative append: append(byte[1], 0, -1)
threw java.lang.AssertionError: 2 != 3, expected IllegalArgumentException" (the
assert in `DbFile.append`, after the length had changed), and passes after it.

* Fix: `FileStream.append` throws `IllegalArgumentException` for a negative
  length at its top, after the stream's own failure check and before it finds
  or changes any file, as `AppendOnlyStream.append`'s Javadoc says. The length,
  the bytes and the next append are as before the call (the harness checks all
  three). The other bad arguments (an offset or length beyond the array) are
  019-02's.
* Test: harness 6.3's check "a negative append" of FileStream; the skip line
  is removed.
* 010-01: no setting, no state, no thread (P3, P9, P10); a valid database never
  passes a negative length, so its bytes are unchanged (P2).
* Gate: `before-commit.sh`: `BEFORE COMMIT OK (106 s)`, unit 1177, f 83.
