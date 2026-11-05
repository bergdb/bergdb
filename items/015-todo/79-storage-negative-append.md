015-79. Fix: a negative append is accepted and decreases StorageManager's length
================================================================================

Status: done 2026-11-05, night 006-12. Kind: Fix. Created 2026-11-04 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: review R5's finding R5-F4 (items/016-release-2026-2/06-reviews/R5.md,
section R5-F4: where, intended, actual, effect, a proposed fix), shown by a
test or probe in 06-reviews/R5/. No second agent has checked it yet.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: verify it (016-06, section 2.6), then the probe made a test.


Log
---

2026-11-04. Registered by the coordinator of release 2026.2 (016-02).

2026-11-05. The harness of 018-02 (the stream contract, 018-01, section
6.3) catches it: `StorageContractTester.testBufferedStream` and
`testStorageManager`, check "a negative append", fail and name 015-79.
Its fix removes the skip line "015-79" from `StreamContract.SKIP`.

2026-11-05, night 006-12. Verified and done. With the line "015-79" removed
from `StreamContract.SKIP`, `StorageContractTester.testBufferedStream` and
`testStorageManager` failed before the fix, each "a negative append:
append(byte[1], 0, -1) returned, expected IllegalArgumentException" (R5-F4
confirmed: the append returned and changed nothing in the buffer, and
StorageManager lowered its length), and pass after it.

* Fix: `BufferedStream.append` throws `IllegalArgumentException` for a
  negative length, after its stored failure check and before the buffer
  changes; `StorageManager.append` does the same before it forwards the append
  and adds to its length, so its counter does not depend on the stream under
  it. It is not an `IOException`, so the storage does not fail. The other bad
  arguments (an offset or length beyond the array) are 019-02's.
* Test: harness 6.3's check "a negative append" of BufferedStream and
  StorageManager; the skip line is removed.
* 010-01: no setting, no state, no thread (P3, P9, P10); `Db` never appends a
  negative length, so a valid database's bytes are unchanged (P2).
* Gate: `before-commit.sh`: `BEFORE COMMIT OK (106 s)`, unit 1177, f 83.
