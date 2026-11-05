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
