015-80. Fix: the buffer issues concurrent writes to a single-writer underlying stream
=====================================================================================

Status: open. Kind: Fix. Created 2026-11-04 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: review R5's finding R5-F5 (items/016-release-2026-2/06-reviews/R5.md,
section R5-F5: where, intended, actual, effect, a proposed fix), shown by a
test or probe in 06-reviews/R5/. No second agent has checked it yet.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: verify it (016-06, section 2.6), then the probe made a test.


Log
---

2026-11-04. Registered by the coordinator of release 2026.2 (016-02).

2026-11-05. The harness of 018-02 (the stream contract, 018-01, section
6.3) catches it: `StorageContractTester.testOneWriterBufferedStream` and
`testOneWriterStorageManager` force R5-F5's order on a `StrictStream` and
fail and name 015-80, and so do the workloads, most runs. The harness
also counts `getFirstPos()`, which the Javadoc puts under the write lock
too: `BufferedStream.getFirstPos()` calls the stream below beside the
thread's append, the same fault; a fix that leaves it still fails the
harness, under 015-80. Its fix removes the skip line "015-80" from
`StreamContract.SKIP`.
