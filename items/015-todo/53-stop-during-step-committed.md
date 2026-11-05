015-53. Fix: a transaction that runs when `stop()` comes is committed, but `execute()` throws `DbStoppingException` from reclaim's step
=======================================================================================================================================

Status: done 2026-11-05, night 006-12. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: review R7's finding R7-F4 (items/016-release-2026-2/06-reviews/R7.md,
section R7-F4: where, intended, actual, effect, a proposed fix), shown by a
probe in 06-reviews/R7/. No second agent has checked it yet.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: verify it (016-06, section 2.6), then the probe made a test.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-05. Done in night 006-12. Verified with R7's probe
(`R7StopDuringStepProbe`, run as it is on the base): "put 196 of /k/34
threw bergdb.core.DbStoppingException: Cannot call getMany() while DB is
stopping.", and after a restart the put's value is there. The probe made
`Reclaim.Tester.testStopDuringStepCommits`, which fails before the fix with
that exception and passes after it.

* Fix, R7's proposal: in `Db.executeInner`, a `DbStoppingException` from
  `reclaimTransactionListener.transactionCompleted(t)` ends reclaim's work
  for the transaction, and the call returns: the transaction is committed
  (its record was appended in `store()`, and the close writes it). Any
  other exception from reclaim still fails the database (`fail()`).
* Why nothing is half done: `DbStoppingException` is thrown only by
  `assertDbStateIsActive`, at the entry of a read or of an internal
  transaction (before its go point); the close (`closeStorage`) only
  writes what is buffered and closes the storage, so reclaim's in-memory
  table, which the refused step or table write may leave ahead of the
  stream, is never used or written again. Reclaim goes on at the next
  start from the stored table, as after a crash at that point
  (`testCrashBeforeIterationEnd`).
* `setStartupDistance`'s dummy transaction (R7's note, not probed) is a
  user transaction too: it now returns, and keeps the new distance in
  memory as in its committed meta block.
* 010-01: no setting, method, thread or global state; P7 kept (any other
  failure fails the database). The stream's bytes are unchanged (P2): the
  same records are appended as before; only the call's outcome changed.
* Tests: the new test; `Reclaim.Tester`, `DbTester`, `DbTesterFailure` pass
  (before-commit.sh).
