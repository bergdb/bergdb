015-25. Fix: an exception in the evictor strands its requests on a dead worker
==============================================================================

Status: done. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

For 2026.2 if it fits (new in this release; internal trigger only).

What: An exception or Error in an eviction batch ends the evictor thread without failing the database; reads go on, nothing evicts any more (memory grows past the budget; `setCacheSizeInMb` has no effect), and loads park up to 2 ms each. New in 2026.2 (the evictor thread, 009).

Source: review R3, R3-F3 (016-06/R3, items/016-release-2026-2/07-concurrency/r3.md),
confirmed by verify-1 (items/016-release-2026-2/06-reviews/verify-1.md,
section R3-F3), with its probe and the reach.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`; or the entry is a known issue
in 2026.2's notes.

First step: the probe of R3-F3, made a test.

**State** (2026-11-03, 20:55): the fix, its test, two mutations and
`before-commit.sh` done in `/Users/f/fl/bench/016/015-25/repo` (`main`
at `0b739f3`); handed off for review in
`/Users/f/fl/bench/016/015-25/handoff/`. Open: the review (016-05,
section 5).


The decision and the fix
------------------------

**The behaviour, from the contracts**: a batch of the eviction thread
that throws fails the database, as any internal error does. Not a design
choice left open, so no stop for Frans:

* 010-01, P7: a database that has a bug, or whose JVM fails, does not run
  on; it fails every later transaction and read.
* `Db.execute`'s Javadoc and `Db.fail` (005-01): after the go point an
  exception means the storage, the JVM or memory failed, or a bug; nothing
  is undone and the database refuses every later transaction and read
  with a `DbFailedException` whose cause is the first failure; `stop()`,
  `close()` and `sync()` still work. The writer's own batch
  (`afterTransaction`) runs within its transaction's go point, so a throw
  there fails the database already; the thread's batch is the same work,
  under the same write lock, and leaves the same partly changed memory.
* `failOnStorage` (005-30): a reader's failure fails the database too,
  rather than serving around it.
* `wake`'s Javadoc, point 3, recorded the gap ("unless an error ended the
  thread ... stops the loads' eviction"), and `setCacheSizeIndicator`'s
  promises that a decrease is reached; both are kept only if the database
  stops being used when the thread cannot work.
* BufferedStream's consumer (005-32) is the precedent for a thread of the
  database's own: it catches `RuntimeException | Error`, stops, and makes
  it the failure that later calls see, without rethrowing.

**The fix** (what, when, by whom, how checked):

* `Eviction.EvictorRun.run` catches `RuntimeException | Error` from its
  batches (`sweep`, and the waits for writers between them), calls
  `Db.Internal.failByEviction(x)`, new, which is `Db.setFailed(x)`: the
  first failure is kept and the state is FAILED, under `readSync`, as for
  the writer's and the readers' failures; nothing while the database
  stops. Then, under `evictorLock`, it clears `evictor` and `wanted`, and
  its `finally` clears `running` and notifies: `awaitBatch` returns, a
  load's wait in `afterLoad` ends (the database is no longer active),
  `afterLoad` and `setBudget(Db, long)` make no new request, and a wake
  that raced the failure starts a thread that ends at once, as after a
  close (`wake`, point 3).
* Not rethrown: the Error is the database's failure, the cause of every
  later `DbFailedException`, as in BufferedStream's consumer. (R3's probe
  waits for an uncaught exception, which no longer comes: on the fix it
  ends with "batch did not fail".)
* Comments: `wake`'s point 3, `EvictorRun`'s Javadoc, and the catch.
  Files: `java/src/bergdb/core/Eviction.java`, `java/src/bergdb/core/Db.java`
  (the one method in `Db.Internal`). No stream byte, no Pub API change.
* Checked by `Eviction.testBatchFailureFailsTheDatabase` (unit, about 0.04
  s): an Error from the existing hook `testBeforeTrigger`, in the thread
  only, in the first batch that a lower budget wakes; within 2 s the
  database has failed; a read and a transaction get a `DbFailedException`
  whose cause is the Error; the thread has ended with no request pending
  and no thread named; a later `setCacheSizeIndicator` starts none;
  `close()` works.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-03, 20:46 to 20:55, by agent F1-b (016-05), in
`/Users/f/fl/bench/016/015-25/repo` (a clone of `main` at `0b739f3`,
after 015-13):

* **Read**: R3-F3 (016-07), its verification (016-06, verify-1, R3-F3),
  `EvictorRun.run`, `wake`, `Db.fail`, `setFailed`, `failOnStorage`,
  `closeStorage`, BufferedStream's `stopAfterFailure` (005-32). R3's
  reading holds: only the `finally` for `running`; a throw leaves
  `evictor` naming the dead thread, and the next `wake` sets `wanted` for
  good. The decision: the section above.
* **The test first, on `main`'s code**:
  `Eviction.testBatchFailureFailsTheDatabase` failed 2 of 2 (`the database
  failed, expected false, but was true`, after its 2 s; the thread died
  with the uncaught Error).
* **Mutations** (`/Users/f/fl/bench/016/015-25/mut/mutate.py`, in
  `java/`): M1, no `failByEviction` call: the test fails (`the database
  failed`). M2, `evictor` and `wanted` not cleared: it fails (`the thread
  ended, no request pending`). With the fix it passes, 3 of 3.
* **The gate**: `java/before-commit.sh`, 20:50:01 to 20:51:48: `BEFORE
  COMMIT OK (107 s)`, 1,137 unit tests, 79 f-tests. Then the unit tests of
  `Eviction`, `CapacityTester` and `EvictionReaderTester` 3 times alone
  (32 tests, SUCCESS each), and the f-tests of those and `DbTesterFailure`
  (18, SUCCESS). Not run: `level4.sh` (the coordinator's call).

2026-11-03, 20:55, by the coordinator (016-05, H5): reviewed, no fault.
The batch's Error leaves its `synchronized` block, so the write lock is
free when the database fails; the `finally` still clears `running` and
notifies; a wake after the failure starts a thread that ends at once.
Committed after the combined gate.
