019-40. Fix: review R6's C findings: tests, words, small faults of the error model's change
==========================================================================================

Status: done. Kind: Fix. Frans: none.
Created 2026-11-06 by Frans Lundberg.

What: review R6 of 006-13 (`/Users/f/fl/bench/006-13/review-r6.md`,
C1 to C9) found, beside its B findings (019-38, 019-39):

* C1: an `Error` under the write lock before the go point is recorded
  after the lock is released, unlike 015-66's order.
* C2: five new paths of de95869 have no test; with all five taken out,
  `before-commit.sh` still printed OK.
* C3: `DbTesterFailure.assertRefused`'s message does not name the case.
* C4: words: where an `Error` does not fail the database (the Pub API's
  conversion, setters), "any call" in `releases/next.md` and 010-P7,
  "began" undefined, and the cut's thread fails the stream, not the
  database at once.
* C5: the index deletion job says "Done!" after a failure.
* C6: `Db.getOneInternal` is public.
* C7: harness 6.2 counts only the fault's own `Error` as a failure.
* C8: 019-34's check could be the invariant it relies on (`firstPos <=
  spos < block.getPos()`), and its `< META_BLOCK_SIZE` branch is
  untested.
* C9: a comment line of 137 characters (`Residents.java`, about line
  191).

Why: the error model is part of the interface (Frans, 2026-11-06:
"Important that the database user understands the error model."), and a
path without a test can break unseen.

Frans: none. Each as R6 suggests, the simplest way (KISS, 010-P13); C6
only if making it non-public is a small change (else words); C5 may
overlap 015-61 (experimental), then a line there.

Done when: each C finding fixed or answered in this entry with a reason;
the five paths of C2 tested (each test fails with its hunk taken out);
`BEFORE COMMIT OK`.

First step: R6's C1 to C9. After 019-38 and 019-39 have landed (the same
files).


Log
---

2026-11-06. Registered by coord-1106 from review R6.

2026-11-06. Done by coord-1106's agent i40, each finding as R6
suggests, the simplest way:

* C1, fixed: `Db.executeInner` catches an `Error` of the steps before
  the go point inside `synchronized (writeLock)` and calls `failed(e)`
  there, so the failure is recorded before the lock is released, as
  `fail()` does after the go point; the edge in `execute()` stays for
  the warm-up. No test: the window is a race that a test cannot hold
  open without a hook (R6: "Read").
* C2, tested, each test failing with its hunk taken out (run):
  `DbTesterFailure.testErrorInSyncOrCacheSizeFailsTheDatabase` (sync's
  edge: "refused, sync(), 0: null"; `setCacheSizeIndicator`'s edge:
  "refused, setCacheSizeIndicator(), 0: null"), with a test hook
  `StorageManager.testHookSync` and `Eviction.wake` starting its thread
  with `Util.start` (019-39's `testHookStart`);
  `BufferedStream.testListenerErrorFailsTheStream` (the listener is not
  told); `StorageManagerTester.testReadFailureRecordedFirst` (an
  `IOException` whose `toString()` throws an `OutOfMemoryError`: with
  the old order the read throws that, and the failure is lost); the
  index deletion's catch: 019-38's `testBugInDeletionFailsTheDatabase`
  ("the database failed: null").
* C3, fixed: `assertRefused(db, cause, what)` names the case, the call
  and what was thrown; `testUncheckedReadFailsTheDatabase` passes it.
* C4, words: `Database`'s Javadoc ("after a transaction's checks, once
  it changes the database"; "refused by its checks"; the conversion of
  a read value to the application's object fails only that call),
  `DbFailedException`, docs/levels.md, section 3 (the conversion; the
  cut's file deletion fails the stream, and the database at the
  storage's next use of it), releases/next.md and 010-01, P7 ("in a
  read, a transaction or a sync", not "any call").
* C5, fixed with 015-61 (R8-F6, the same fault): the deletion's job sets
  a done flag after its last sync; a job whose thread ended without it
  says progress 100 and "Stopped: ...", as a build does. Tests:
  `testBugInDeletionFailsTheDatabase` checks it, and
  `PubTesterIndexJobs.testDeletionEndedByCloseIsStopped` (R8's probe);
  both fail with the flag taken out ("Done! Deleted 'by-field', 0 index
  entries were deleted."). releases/next.md, Pub API.
* C6, fixed: `Db.getOneInternal` is package-private, not private: item
  004's ScaleBench and IndexCensus (package `bergdb.core`) call it.
* C7, fixed: harness 6.2 counts any `Error` as the failure, and one that
  is not the fault's is a finding, "bug".
* C8, fixed: the check is the invariant, `max(META_BLOCK_SIZE,
  firstPos) <= spos < block.getPos()`. No stream that started before is
  refused now: a position below the first position failed the start
  anyway (a read below it), and a valid block names a record appended
  before it. `testMetaBlockLastTransPosRefused` also patches the second
  meta block (a 200 KB value puts it in the stream) to name 10 and a
  position after itself; each fails with its bound taken out.
* C9, fixed: `Residents.handleIn`'s Javadoc wrapped at 100.
