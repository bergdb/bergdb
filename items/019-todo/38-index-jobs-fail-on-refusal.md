019-38. Fix: index jobs fail the database on an interrupt, an expired read or a refusal
=======================================================================================

Status: done. Kind: Fix. Frans: none.
Created 2026-11-06 by Frans Lundberg.

What: 019-10's change (01b0493) gave the index build's thread
(`IndexBuilderImp`, about line 337) and the index deletion's thread
(`DatabaseImp`, about line 313) a `catch (Throwable)` that fails the
database on everything but `StreamIoException`, `DbStoppingException` and
`DbFailedException`. That includes what is not a failure: the
`DbException` of an interrupt while a step waits to rerun after a conflict
(`RwTransaction`, about line 150), a `LookupTimeNotAvailableException` of
the step's `getMany` when a cut overtakes it, and a refusal of the step's
transaction. Before 019-10 each ended the thread silently and the index
work stopped until a restart (also wrong).

Why: review R6 of 006-13 (`/Users/f/fl/bench/006-13/review-r6.md`, B1),
shown by a probe (an interrupt during a build's rerun: the next put throws
`DbFailedException`). docs/levels.md, section 3: everything but a failure
fails only that call and the database goes on, and an interrupt never
fails the database (005-46). A regression of today's change.

Frans: none. The rule of docs/levels.md, section 3 decides it.

Done when: in both threads, an `Error` or an unexpected
`RuntimeException` (a bug) fails the database; a refusal or an expiry
waits as after a conflict and takes the step again; an interrupt goes on
with the flag set (as `sleepFiftyPercentOfDuration` does); a test in
`PubTesterIndexJobs` with R6's probe's shape (and an expiry by a hook)
fails before the fix and passes after; one sentence in levels.md, section
3 (an index job's refusal or expiry is retried, not a failure);
`BEFORE COMMIT OK`.

First step: R6's B1 and its probe (`R6Probe`, in R6's clone
`/Users/f/fl/bench/006-13/r6`).


Log
---

2026-11-06. Registered by coord-1106 from review R6.

2026-11-06. Done by coord-1106's agent i38. Both threads, the build's
(`IndexBuilderImp.createInThread`) and the deletion's
(`DatabaseImp.deleteIndexInternal`), now catch a `DbException` (a
refusal; the interrupted wait to rerun after a conflict is one) and a
`LookupTimeNotAvailableException` (an expired read) after their catches of
the stops and the failure, wait as an rw-transaction after a conflict
(`IndexBuilderImp.waitToRetry`: 10, 20, ... 640 ms, `RwTransaction.nextSleep`;
reset after a step that works) and take the step, or the deletion's work,
again. Anything else, an `Error` or another `RuntimeException`, still fails
the database. A new catch of `IllegalDbStateException` ends the thread
when the database has stopped (before, `fail()` did nothing then, and the
thread ended; without it, the retry would loop on a stopped database). The
deletion's hook "start" moved into the loop's `try`, so that a test can
throw there. On the interrupt: the wait clears the flag, as
`sleepFiftyPercentOfDuration` does, and the thread goes on; with the flag
kept set, every later wait of the thread would end at once. A refusal that
lasts (the top node ordinals used up, 005-02) makes the job retry every
640 ms; the application's own transactions are refused too. Tests in
`PubTesterIndexJobs`: `testInterruptInBuildIsNotAFailure` (R6's probe),
`testExpiryOrRefusalInBuildIsNotAFailure` (a hook throws once),
`testExpiryInDeletionIsNotAFailure`, `testBugInDeletionFailsTheDatabase`,
and `testErrorInBuildFailsTheDatabase` with a `RuntimeException` too; the
first three build and deletion tests fail on the code before (the
database failed, or the deletion's thread ended). docs/levels.md, section
3: one sentence; releases/next.md: 019-10's bullet. `BEFORE COMMIT OK`.
