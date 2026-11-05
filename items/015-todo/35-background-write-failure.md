015-35. Fix: a failed background write does not fail the database until a caller touches storage
================================================================================================

Status: done 2026-11-05, night 006-12. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: When the buffer's consumer fails to write (a disk error), the database does not fail until a caller's call meets storage; a workload of reads served from memory goes on, and returns a transaction that a restart will not have. Against 010-01, P7; docs/levels.md, section 3 lists only failures met by a call. Normal use.

Source: review R3, R3-F10 (items/016-release-2026-2/07-concurrency/r3.md),
confirmed by verify-2 (items/016-release-2026-2/06-reviews/verify-2.md,
section R3-F10), with its probe, the reach and the effect.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: the probe of R3-F10, made a test.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-04. Review R5 found the same, or its counterpart in StorageManager (R5-F3, items/016-release-2026-2/06-reviews/R5.md).

2026-11-05. Done in night 006-12, with 015-81 (the same path). R5-F3's test
made `DbTesterFailure.testBackgroundWriteFailureFailsReads`: a put synced,
the next put's background write fails, and a get served from memory then
returns its value: before the fix "a get from memory after the failed
write: a1".

* Fix: `Db.assertDbStateIsActive`, the admission of every transaction,
  read and setter, fails the database (`setFailed`) when it finds the
  storage failed (`StorageManager.hasFailed()`, a volatile read), with a
  `StreamIoException` of the storage's failure as the cause; the call and
  every later one throw `DbFailedException`. `StorageManager` keeps the
  failure (`getFailure()`). R5's other option, a callback from the storage
  thread into `Db`, was not taken: it would take `readSync` on that thread.
* A sync already failed the database (its wait sees the storage's error
  within 500 ms); a call admitted before the failure ends as before.
* 010-01: P7 now holds for a failure that no call meets. No setting,
  thread, global state or format change; the stream's bytes are unchanged
  (nothing that writes changed). The get's cost: one more volatile read.
* `docs/levels.md`, section 3, has a line on it.

Review R1, night 006-12
-----------------------

2026-11-05. Review R1 of the night (`/Users/f/fl/bench/006-12/review-r1.md`,
findings B1, C1 and C2 on this fix and 015-81's) found a regression and two
smaller faults; fixed in the night, in one change with 015-81's entry.

* B1, a regression: `Db.close()` could return before the failed storage had
  closed its stream. `StorageManager.closeInner` skipped the close of a
  failed main stream ("handleStreamException closed it"); since 015-81 the
  failure is set before that close, and since this entry the database fails
  at once on it, so an application closed and restarted while the thread
  that met the failure was still closing (for a failed read, the reader's
  `BufferedStream.close()`, which first writes all that is buffered): the
  stream open, a `FileStream`'s directory locked, `DirectoryInUseException`
  for a start in the same JVM. Before tonight the window was there only for
  a close that had not seen the failure, as one after a failed concurrent
  append.
* Test first: `DbTesterFailure.testCloseWaitsForTheFailedStreamsClose`,
  R1's probe made a test: a write held in the stream's append, a read that
  fails (the reader's close waits for the write), a get that fails, and a
  `close()` on another thread must not return while the write is held, and
  the stream is closed when it returns. Before the fix: "close() waits for
  the stream's close; the stream closed: false". After: passes.
* Fix: `closeInner` closes the main stream also when it has failed, and
  returns no failure for it (the storage's failure is reported by the call
  that met it, with the close's as suppressed). Corrected by 019-09 (R1's
  re-review, B2): when no call met the failure, as for a failed write of
  the storage thread followed by `close()`, nothing reported it; now
  `closeInner` returns the storage's failure, and `Db.close()` throws it
  unless the database has already failed (Frans's option (a)). `BufferedStream.close()` is
  safe from several threads at once and returns when its thread has ended,
  and the thread closes the underlying stream as it ends (015-34's
  `finally`); so `close()` returns after the stream's close, whichever
  thread made it. That also closes the older window above. `stop()` is as
  before.
* Not taken: the old order in `handleStreamException` (close, then
  publish), which the night's coordinator considered. It brings back the
  window of 2026.2 (a failed concurrent append fails the database during
  the close) and delays the failure that this entry makes visible at once.
  Nor R1's suggestion, a latch that `handleStreamException` counts down
  after its close and `closeInner` waits for: not needed, as `closeInner`
  now closes the stream itself and that close waits. (Corrected after R1's
  re-review, C3: this point named the old order as R1's suggestion.)
* Checks: 015-35's and 015-81's tests pass, unchanged in what they assert;
  R1's probes `R1ReadFailCloseProbe` ("Db.close() returned after 1923 ms;
  stream closed: true") and `R1CloseRaceProbe` ("stream closed: true",
  no consumer thread left) against the fix.
* 010-01: no setting, thread, global state or format change; the stream's
  bytes are unchanged. `releases/next.md`: a sentence in this entry's
  note (Reliability).
