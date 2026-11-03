015-10. Fix: the eviction thread stops after a batch that frees nothing, above the budget
=========================================================================================

Status: done. Kind: Fix (was Investigate: CapacityTester's
lowered budget failed under load on s1). Created 2026-11-03 by Frans
Lundberg.

For release 2026.2: the test is in `bergdb.dev.Unit`, which W6 runs on
the release's jar on s1 (016-09, R5).

What: in two of three full runs of `bergdb.dev.Unit` on s1 (Linux, 2
cores) on the jar of `f2cb23b` with BuildInfo set to 2026.2, with JDK 27
and 17, on 2026-11-03 at 16:29 and 16:30, the test failed: "at most 924984
bytes, budget 231246 of 924984" (nothing was evicted after the budget was
lowered); then `NanotestForBergDB.databasesStopped` failed, as the failed
assert leaves its database running. A third run passed; the class alone
passed 3 of 3; on F53 it passes. s1 was not idle then: 016-08's runs were
on it. Between `323a54a`, whose jar passed on s1, and `f2cb23b` in `java/`:
`dde82e8` (005-79 A, the integer watermark), `b281d39` (005-69) and
`522b645` (005-80, Eviction's test hook).

Questions: does the test depend on timing (the eviction thread's wake on
a loaded machine), or did one of the three commits change it?

First step: the base's jar and main's, full Unit in turns on s1 under the
same load (`/opt/bergdb-bench/016/h4/cap-check.sh`, from 16:36).

Done when: the cause is known, and the test is fixed (Fix) or the change
is.

**State** (2026-11-03, 20:00): the cause confirmed, a fault of the
eviction thread's stop rule (product code), not of the test; the fix, two
unit tests (both fail on `main`'s code), the mutations and
`before-commit.sh` done in `/Users/f/fl/bench/016/015-10b/repo` (`main`
at `b9ba427`, rebased on `c657764`); handed off for review in
`/Users/f/fl/bench/016/015-10/handoff/`. Open: the review (016-05,
section 5); `level4.sh`, if the coordinator wants it for a change to
Level 4's mechanism (not run here).


The cause
---------

`Eviction.EvictorRun` ran batches while the resident bytes were over the
trigger, and stopped after the first batch that freed nothing (`if (freed
== 0) break;`, since `66c8f3a`, 009 step 3d, 2026-10-25; not one of the
three commits of the question, and not in 2026.1, which had no handles).
That rule meant "every object in use, or pinned", but a batch is bounded
three ways (009-02, section 4.7; `Eviction.BATCH`): its handles (4,096,
or 65,536 under pressure), two rounds of the hand over the 4,096 maps, and
2 ms (`BATCH_NANOS`). In the hand's first round over objects that were
all just read, a batch only clears CLOCK bits: one cut short by its time
or its handles before the second round frees nothing, and the thread
stopped. Nothing started it again when every value was resident, as a read
that loads nothing does not call `afterLoad`; a commit would have. The
resident bytes then stayed above the lowered budget, against 005-52's "a
decrease is reached also when no transaction or load follows".

* On s1 under load (the failure of the What): the budget lowered to a
  quarter, so under pressure (65,536 handles a batch; two rounds of the
  test's 1,025 handles fit), and nothing freed, every sample 924,984
  bytes. With no writer, the only bound that ends such a batch in its
  first round is its 2 ms: the thread was off the CPU, or slow, then (not
  observed, inferred). `awaitBatch` returned at once, as no request was
  pending. Timing only; F53 did not show it in 20 runs (17:30 in the Log).
* Without load or timing: a table of more handles than a batch examines,
  every bit set, and a budget lowered a little (not under pressure, 4,096
  handles a batch): the first batch is in the first round and frees
  nothing, every time. A database of more than about 4,096 resident index
  nodes, all read since the hand last passed, gets there when its budget
  is lowered a little and no load or commit follows; the new test
  `Eviction.testLoweredBudgetAfterReads` makes it with 10,000 keys (about
  5,000 index nodes).


The fix and why
---------------

The thread's batches end when the resident bytes are at most the
trigger, as before, or when the hand has gone over the maps twice (2
`Cache3.maps()`, 8,192 maps) since the request or since the last batch
that freed something: after two whole rounds without a free, nothing can
go (every object in use, held by a loader, or pinned), as the first
round may only clear the bits and the second takes what is still clear.
This is the earlier agent's proposed rule (Log, 17:17), with the count
reset at each request the thread takes, so that a new request (a load, a
commit's end, `setCacheSizeIndicator`) always buys up to two rounds; a
count kept across requests would stop a new request's first batch at
once again, and the fault would come back after a stop. A batch that took
no map (a writer waited for the write lock as it began, or its 2 ms were
gone before its first map) counts none, and the next batch goes on.

* **What, when, by whom, how checked.** `EvictorRun` counts the maps
  that the thread's batches take without freeing (`idleMaps`, a local
  variable, reset when it takes a request and after a batch that freed
  something); `sweep` now returns its maps with the bytes freed (`long[]
  {freed, maps}`). Checked by `testLoweredBudgetAfterReads` (the budget
  is reached) and `testNothingToFree` (the thread stops after two rounds
  and stays idle).
* **005-51 and 010-P3 kept**: the thread still runs only on a request and
  waits with no timeout when it stops; when nothing can go it stops after
  at most two rounds of the hand (`testNothingToFree`: idle within 2 s, no
  batch in the next 20 ms; `testEvictionThreadIdleUntilClose` and
  `testNoLostRequest` unchanged and passing).
* **No spin**: each batch is bounded as before (2 ms, its handles, a
  waiting writer first), and the batches of a request without a free are
  bounded by two rounds of the hand, 8,192 map steps: two visits of each
  handle in the table, so work in proportion to the resident index nodes,
  in batches of at most 2 ms (not measured at a large table; in
  `testNothingToFree`, about 5,000 handles, it is 3 batches). Before, a
  request without a free bought one batch. A batch can take no map only
  when a writer waits or the thread was off the CPU for 2 ms; neither
  spins, and a writer's commit runs a batch of its own.
* **Not changed**: the stream (no record changes; eviction never writes
  one), the Pub API, `sweep`'s batch (its bounds, its trigger), the
  writer's batch at a transaction's end, `afterLoad`, the read path. Only
  `java/src/bergdb/core/Eviction.java`.
* **Not chosen**: a hook in `sweep` that ends a batch early (the earlier
  agent's idea for the test): the handle limit makes the stuck state with
  data alone, without test code in the product; and stopping only after a
  batch that took its two whole rounds without freeing, which would spin
  when batches are cut short by their handles or time and nothing can go.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-03, 16:43. The first step: six full runs of `bergdb.dev.Unit` on
s1, the base's jar (`6f932f0`) and main's (`3e32f02`) in turns, the first
two rounds beside the night tests (load about 3): all SUCCESS, the test
passed each time. Unit took 29 to 90 s with the base's jar and 42 to 57 s
with main's, so the doubled time follows the load, not the commits. Not
reproduced; most likely the test waits too briefly for the eviction
thread on a loaded 2-core machine. Next: read the test's wait against
005-51's and 005-65's wake, and make the wait a bounded poll if it is a
fixed sleep.

2026-11-03, 17:17 to 17:27, by F1 (016-05), in
`/Users/f/fl/bench/016/015-10/repo` (a clone of `main` at `a46a597`, no
change made), the test read against the eviction thread:

* **The wait is a bounded poll already**: each sample, `bytes(db)`, calls
  `Eviction.awaitBatch()`, which waits up to 1 s while a request is
  pending or a batch runs (`wanted || running`). So the failure ("at most
  924984 bytes, budget 231246 of 924984": nothing evicted) is not a short
  wait.
* **Why it can fail, most likely** (from the code; not reproduced yet):
  after `setCacheSizeIndicator(low)` the eviction thread, woken by the
  call (005-52), runs batches until the resident bytes are at most the
  trigger, and stops after a batch that freed nothing
  (`EvictorRun.run`: `if (freed == 0) break;`, 005-51: "every object in
  use, or pinned"). Every value was just read, so every CLOCK bit is set:
  a batch's first round over the maps only clears them, and it frees only
  in its second round (`sweep`, `maxMaps = 2 * all`). A batch also ends
  after `BATCH_NANOS`, 2 ms of wall time. On a loaded machine (s1, 2
  cores, other runs) the thread can be descheduled within its first batch,
  so that the 2 ms pass in the first round: the batch frees nothing, the
  thread stops, and no new request comes, as the test's reads find every
  value resident and load nothing (no `afterLoad`). `awaitBatch` then
  returns at once, and every sample is the full 924,984 bytes.
* **So it is a fault of the eviction thread's stop rule, not only of the
  test**: under load a lowered budget may not be reached until the next
  load or commit, against 005-52's "a decrease is reached also when no
  transaction or load follows". Proposed fix (product code, for the
  coordinator to decide; then `level4.sh`): stop only after the hand has
  gone over the maps twice without freeing anything (a count of maps
  examined since the last batch that freed), not after one batch that
  freed nothing; a batch cut short by its time then lets the next one go
  on. A test could force it with a hook in `sweep` that spends the batch's
  time in its first round.

Result of the runs on `main`'s jar (17:30:03 to 17:30:24, load about 29 to 33 on F53's 10 cores): 20 passed, 0 failed of 20: not reproduced on F53; the cause in the Log stays the likely one, from the code, and a hook test would be needed to show it.

2026-11-03, 19:34 to 20:00, by agent F1-b (016-05), in
`/Users/f/fl/bench/016/015-10b/repo` (a clone of `main` at `b9ba427`,
this entry copied from `/Users/f/fl/bench/016/015-10/repo`):

* **The analysis checked against `main`'s code**: `EvictorRun.run`,
  `sweep`, `Cache3.clockStep` (a set bit is cleared and the handle
  skipped; only a clear bit lets a detachable object go), `setBudget(Db,
  long)` (wakes the thread once), `afterLoad` (called only after a load,
  `NodeCollection`'s slow path), `awaitBatch` (`wanted || running`). As
  the Log of 17:17 says; the section "The cause" above adds the handle
  limit, which makes it without load.
* **The test first, on `main`'s code**:
  `Eviction.testLoweredBudgetAfterReads` (unit, about 0.17 s) failed 5 of
  5: `at most 1812934 bytes, budget 1631637 of 1812934, after 1 batches`.
  Its setup, `everyKeyReadTwice`:
  10,000 keys with short values, written with a startup distance of 2,000
  bytes and started cold with a budget of 100 MB; every key read twice.
  Two things the setup does by hand, found by probes: the reads left 2 of
  5,065 handles with a clear bit (canonical key nodes reachable from the
  top, that no read at the latest time follows, as history versions are
  not; not a fault), and the 40 pinned key nodes of D held 60 values that
  the reads loaded, which any batch takes whatever the bits. With either
  left, `main`'s first batch can free something and go on. So the setup
  sets every live handle's bit, as a follow does, and takes the pinned
  key nodes' values first (`unswizzleValues`); it checks that there are
  more detachable objects than `BATCH` (5,024).
* **The fix**: section "The fix and why". `Eviction.java` only: the stop
  rule in `EvictorRun.run` and its comments, `sweep` returning `{freed,
  maps}` (its callers that ignore the result unchanged), and the comment
  of `testNoLostRequest` on the rule.
* **The second test**, `Eviction.testNothingToFree` (unit, about 0.11 s):
  the same setup, every handle that holds an object set to `LOADING` (as
  a loader holds it), the budget lowered to 9/10: nothing can go and
  nothing is pinned for it. The thread must be idle within 2 s (waiting,
  no request pending, its last batch freeing nothing), run no batch in
  the next 20 ms, have freed nothing, and have ended a round of the hand
  in at least two batches.
* **Mutations** (Python replacements of the two new lines, then the
  tests): M1, `main`'s rule back (`if (fm[0] == 0) break;`): both tests
  fail (`at most 1812934 bytes ... after 1 batches`; `the hand went over
  the maps twice: 0 of 1 batches ended a round`). M2, no stop rule (the
  count kept, the `break` on it removed): `testNothingToFree` fails
  (`idle: ... batches running true, the thread RUNNABLE`) and
  `testLoweredBudgetAfterReads` passes. With the fix both pass.
* **Runs** with the fix: the unit tests of `Eviction`, `CapacityTester`
  and `EvictionReaderTester` 3 times alone (30 tests, SUCCESS each) and 20
  times in 4 JVMs at once (SUCCESS each, 3.3 to 4.2 s); their f-tests
  twice (17 tests, SUCCESS, 15 s). `testBudgetLoweredAndRaisedUnderReads`
  unchanged: with the fix a batch cut short by its time no longer stops
  the thread.
* **The gate**: `java/before-commit.sh`, 19:48:04 to 19:49:49: `BEFORE
  COMMIT OK (105 s)`, 1,125 unit tests, 78 f-tests. Then the clone
  rebased on `main` at `c657764` (`java/` had changed in
  `FileStreamPowerLossTester.java` and `Reclaim.java`, 015-16 and 015-09),
  and again, 19:53:34 to 19:55:21: `BEFORE COMMIT OK (107 s)`, 1,125 unit
  tests, 78 f-tests. Not run: `level4.sh` (no Lean step changes: the stop
  rule only decides when the thread runs batches, and each batch is as
  before).

2026-11-03, 20:00, by the coordinator (016-05, H5): reviewed, no faults.
The stop rule ends a request's batches after two rounds of the hand
without freeing (a batch that frees resets the count), so the thread
stays calm when nothing can go (005-51, 010-P3) and goes on from the
hand when the first round only cleared CLOCK bits. A batch that takes no
map adds nothing; it ends early only on a waiting writer or its 2 ms, and
the hand moves on in the next. The cost: when nothing can be freed, a
request may take two rounds over the maps where it took one batch;
bounded, and only above the trigger. `level4.sh` was not run by the
author: `night.sh` runs it on commit A at 02:10.
