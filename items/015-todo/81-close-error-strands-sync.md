015-81. Fix: an unchecked close error can kill the consumer before publishing a failed append
=============================================================================================

Status: done 2026-11-05, night 006-12. Kind: Fix. Created 2026-11-04 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: review R5's finding R5-F6 (items/016-release-2026-2/06-reviews/R5.md,
section R5-F6: where, intended, actual, effect, a proposed fix), shown by a
test or probe in 06-reviews/R5/. No second agent has checked it yet.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: verify it (016-06, section 2.6), then the probe made a test.


Log
---

2026-11-04. Registered by the coordinator of release 2026.2 (016-02).

2026-11-05. Done in night 006-12, with 015-35. Verified with R5's probe
(R5/R5CloseErrorProbe.java), made a test with `DbTesterFailure`'s
`FaultStream` (a new `errorInClose`):
`testUncheckedCloseErrorAfterFailedWriteFailsSync`. A put's background
write fails and the stream's close then throws an
`IllegalStateException`; before the fix the sync hung ("HUNG: still
running after 5000 ms") and the storage thread died of the close's
exception.

* Fix: `StorageManager.handleStreamException` sets the storage's error and
  failure before it closes the stream, and keeps what the close throws
  (`IOException`, unchecked or `Error`) as suppressed on the failure; the
  close's own rethrow of the same failure (`BufferedStream.close()` throws
  a failed flush again) is skipped. So a waiting sync throws, and with
  015-35 the database fails at its next call.
* The storage thread's own last close (`BufferedStream.runConsumer`) still
  ends the thread with such an unchecked exception, after everything is
  published: 015-78's change.
* 010-01: P7 holds; no setting, thread or format change; the stream's
  bytes are unchanged.

Review R1, night 006-12
-----------------------

2026-11-05. Review R1 of the night (`/Users/f/fl/bench/006-12/review-r1.md`,
findings B1, C1, C2) on this fix and 015-35's; B1 is in 015-35's entry.

* C1: `testUncheckedCloseErrorAfterFailedWriteFailsSync` passes without
  this entry's change, since 015-78's `BufferedStream.closeStream()`
  catches the unchecked close error (R1 ran it with the old
  `handleStreamException`). The test now says so: it fails only without
  both fixes. This entry's order (the error before the close) is pinned by
  015-35's new `testCloseWaitsForTheFailedStreamsClose`, which waits for
  the storage's failure while the close is held: with the old order it
  fails ("the storage did not fail"), checked by a run.
* C2: the close's failure was not kept as suppressed, as the Javadoc and
  this entry said: after 015-78, `BufferedStream.close()` keeps a failed
  close in `closeFailure` and throws the flush's failure, which is `e`
  itself, so nothing was added. Now `BufferedStream.closeStream()` adds the
  first close failure to the flush's failure as suppressed, once. Test
  `BufferedStream.testCloseFailureKeptOnFlushFailure` (a failed flush, a
  close that throws an `IllegalStateException`, `close()` twice): before
  "the close's failure, once: [], expected 1, got 0", passes after; R1's
  `R1SuppressedProbe` shows it on the database's failure chain.
