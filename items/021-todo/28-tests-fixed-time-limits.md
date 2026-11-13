021-28. Fix: unit tests with fixed time limits fail under load
==============================================================

Status: done. Kind: Fix. Frans: none.
Created 2026-11-13 by Frans Lundberg.

What: some unit tests of `java/before-commit.sh` wait for a condition, or
measure, against a fixed wall-clock limit, and fail when the machine is
loaded. The known one is `bergdb.core.Eviction.testInterruptedWhileAWriterWaits`
(`java/src/bergdb/core/Eviction.java`, the last test): it gives the writer
and the eviction thread 2 s together to reach their waits, then asserts
that the interrupted thread takes less than 25 ms of CPU time in 50 ms.
It failed once at load 19 on 2026-11-09 (020-21; 020-11, "Test gaps")
and once under load on 2026-11-13 at 05:16, during the release morning of
2026.5 (coord-1112, 006-23, section 6, point 3); which assertion failed
at 05:16 was not recorded. It passed when run again both times.

Why: a gate that fails on a loaded machine sends a session after a fault
that is not there, or teaches it to rerun until green. The coordinators
run gates while other work loads F53 (013-02), so the load is normal.

Frans: none.

Done when: every unit test of before-commit.sh with a fixed time limit
is listed in this entry, each changed so that load alone does not fail it
(wait for the condition with a generous limit, such as 30 s, and fail
only then; or measure in a way that load does not change), or kept with
a reason; `java/before-commit.sh` prints `BEFORE COMMIT OK`; and three
runs of before-commit.sh, each beside a CPU load of twice the cores
(such as `yes > /dev/null` in 2 x cores processes), pass, or each failure
is a fault of its own that gets an entry.

First step: reproduce the Eviction test's failure under load (the test
alone, in a loop, beside the CPU load) and note which assertion fails;
then grep the tests for `System.nanoTime()` and `currentTimeMillis()`
deadlines, `Thread.sleep` before an assertion, and timed `join(ms)` or
`await(ms)` whose limit is under about 10 s.


Log
---

2026-11-13. Registered by coord-1113 (Frans, 06:38: "Yes, register them"),
from coord-1112's handover (006-23, section 6, point 3).

2026-11-13. Done by coord-1113's agent "limits": commit "021-28" in
`/Users/f/fl/bench/2026-11-13/limits/clone`, branch `021-28-time-limits`,
on main's 6239e245, to land. Tests only; no product code changed
(`bergdb.common.EventToWaitFor` is used by tests only).

* The first step. `Eviction.testInterruptedWhileAWriterWaits` alone, in a
  loop, on main's code: 0 failures in 40 runs beside 20 processes of
  `yes > /dev/null` (2 x 10 cores), then 1 in 60 runs beside 60: "the
  thread parks for the writer, expected true", 0.3 s into the test. Not
  the 2 s deadline: the loop broke when it saw the eviction thread
  TIMED_WAITING, and the assertion read the state again. The thread parks
  100 us at a time and is RUNNABLE between its parks, so a test stopped
  by load between the two reads saw RUNNABLE. Now the assertion takes the
  state the loop saw. The CPU check had a fixed window too: less than
  25 ms of CPU time in a sleep of 50 ms, while the thread's checks (one
  each 100 us) take CPU time for as long as the sleep lasts, longer under
  load; now less than half the window's measured wall time (its Javadoc's
  "less than half the CPU time"). With both changes: 0 failures in 100
  runs beside 60 processes.
* The grep (`nanoTime()`, `currentTimeMillis()`, `Thread.sleep`, timed
  `join`, `await`, `waitForEvent`, `poll`, `wait`) over the 158 classes
  whose tests before-commit.sh runs (unit and f) found 539 lines; the
  ones that bound a wait or a time in a test are below. A wait for a
  condition that ends at once when the condition holds now waits up to
  30 s (021-29's joins wait 60 s); a bound on a time that only a fault
  makes long is set under the time the fault would take, with room for
  load. Lines and limits of 6239e245, old -> new:
  - `core/Eviction.java`: 1842 (testEvictionThreadIdleUntilClose) 2 s ->
    30 s; `settled(e, db, 2000)` at 1940, 2074, 2080, 2192, 2224, 2659,
    2691, 2699 (testNoLostRequestF's bursts, testInterruptWithRequestPending,
    testLoweredBudgetAfterReads, testNothingToFree,
    testLoweredBudgetAfterPinsFell) 2 s -> 30 s; testSetBudgetAtBatchEnd
    2025, 2039 2 s -> 30 s; testInterruptWithRequestPending 2083 2 s ->
    30 s; testLoweredBudgetAfterReads 2185 2 s -> 30 s;
    testBatchFailureFailsTheDatabase 2273, 2292 2 s -> 30 s;
    testBatchFailureBeforeTheLockGoes 2369, 2375, 2384, 2391 2 s -> 30 s,
    2403, 2417 5 s -> 30 s; testInterruptedWhileAWriterWaits 2733 2 s ->
    30 s, 2746 the state seen (above), 2750-2753 25 ms of 50 ms -> half of
    the measured window, 2755, 2758 5 s -> 30 s; the Javadocs' "within
    2 s" with them.
  - `core/CapacityTester.java` 184 (testBudgetLoweredWhileIdle), 728
    (testCountsWithHandles) 2 s -> 30 s.
  - `core/DbTesterFailure.java` 1411
    (testUncheckedCloseErrorAfterFailedWriteFailsSync) 5 s -> 30 s.
  - `core/DbTesterJavadoc.java` 227 (testOwnThreadsAreDaemons) 2 s -> 30 s.
  - `core/DbTesterStream.java` 727-740
    (testSyncAfterOneCommitWaitsForOneForce): the sync under 250 ms, with
    a buffer time of 4 s -> under 5 s, with a buffer time of 60 s (the
    fault, a sync that waits for the timer, takes 15 s or more).
  - `core/EvictionAccountingTester.java` 413, 445 (check, settle) 5 s ->
    30 s, and the messages.
  - `core/EvictionReaderTester.java` 381 (readerPausedInsideAFollow): a
    fixed `paused.await(5 s)` -> until the reader pauses or ends, at most
    30 s (a reader that ends without a pause no longer costs 5 s);
    testAuditWithReaderCleanup 617, 639, 645, 651, 652 and blockedIn 659
    5 s -> 30 s.
  - `core/FileStreamPowerLossTester.java` 425, 436, 464, 483 5 s -> 30 s.
  - `core/InterruptTester.java` 261 (testStorageThreadInterrupted) and 273
    (sleepingMonitor) 5 s -> 30 s.
  - `core/Residents.java` 483, 493 (testResyncWithConcurrentLoad) 5 s ->
    30 s.
  - `core/StorageFaultTester.java` 147 (waitUntilClosed, for
    testStopWhileReading) 2 s -> 30 s; 769 (checkThreads, every run) 1 s
    -> 30 s.
  - `pubimp/IndexJobsHarness.java` CLEANUP_MS 5 s -> 30 s, THREADS_MS
    2 s -> 30 s, 1269 (alive, the wait for a failure after an Error) 2 s
    -> 30 s.
  - `pubimp/PubTester.java` 2123 (testLoweredCacheSizeWhileIdleF) 5 s ->
    30 s; 4248 (testWSyncLevelWaitsForItsOwn) 5 s -> 30 s.
  - `pubimp/PubTesterIndexRaces.java` awaitCleanups 469 5 s -> 30 s,
    await 485 2 s -> 30 s, join 499 5 s -> 30 s.
  - `storage/BufferedStream.java`: testQuarterWakesConsumer 996 2 s ->
    30 s, 1006 2 s -> 10 s (the fault waits for the timer, 15 s);
    testCloseDuringAFlushDoesNotWaitForTheTimer and
    testAppendWaitingForRoomWhenCloseBeginsThrows 1031, 1048, 1059, 1108,
    1118, 1132 2 or 5 s -> 30 s, the joins 1071, 1144, 1145 10 s -> 30 s,
    "close() took" 1074, 1150 under 5 s -> under 10 s (the fault: 15 s);
    testQuarterBacklogDoesNotWait 1178, 1198 2 s -> 30 s, 1202 2 s ->
    10 s; test1 1250-1260: buffer time 20 ms and sleeps of 30 and 60 ms ->
    buffer time 1 s and a wait up to 30 s (its first assertion, nothing
    written yet, failed if load stopped the test 20 ms); testPendingCutDuringACut
    1378, 1397, 1401 2 s -> 30 s; writerCutBeside 1437, 1460, 1471 5 s ->
    30 s; testIdleConsumerWaitsForAppend 1535, awaitIdle 1610,
    testConsumerIgnoresInterrupt 2047 2 s -> 30 s;
    testStopAndCloseEndIdleConsumer 1559, testStopWhileInterruptedClosesStream
    2081 2 s -> 30 s; testClose 1618: buffer time 20 ms -> 60 s (as
    test1's first assertion); testCloseAfterFailedFlush 1792,
    testAppendWaitIgnoresInterrupt 1966, 1984, testCloseIgnoresInterrupt
    2007 5 s -> 30 s.
  - `storage/StorageContractTester.java` 93, 112 (oneWriter) 5 s -> 30 s.
  - `storage/StorageManagerTester.java`: testWait1 72, sync(0) under 50 ms
    -> under 400 ms (the fault, a wait for the next check, takes 500 ms);
    testWait2 117 under 0.30 s -> under 5 s (a bound for a hang: the
    timer it once waited for, 25 to 100 ms, was under 0.30 s too);
    testSyncStartsTheFlush 133, 146: buffer time 4 s and under 1 s ->
    60 s and under 5 s; testSyncWokenByAFailure 168, 189, 190, 196, 202
    5 s -> 30 s, 199 under 50 ms -> under 250 ms (the release comes as
    the sync begins its wait of 500 ms, so a sync that waits for its next
    check throws about 500 ms after it).
  - `stream/FileStream.java`: HeldIo.hold 2546 10 s -> 30 s;
    testReadOfLastFileDuringForce 2710, testReadDuringNewFile 2735,
    testCutOnItsOwnThread 2762 under 2 s -> under 10 s (the fault waits
    for the hold, now 30 s).
  - `stream/StreamContractTester.java` 114 (testStrictCaller) 5 s -> 30 s.
  - `common/EventToWaitFor.java`: `waitForEvent(long)` waits on to its
    deadline after a spurious wakeup (021-29's caution); test2's thread
    waits for a latch before its sleep of 10 ms, as its second
    `assertFalse` failed if load stopped the test 10 ms.
  - `src-dev/bergdb/dev/NanotestForBergDB.java` StoppedCheck.WAIT_MILLIS
    (databasesStopped) 5 s -> 30 s.
* Kept, with the reason:
  - limits of 10 s or more (the entry's line), such as
    DbTesterFailure's and NodeCollection's 10 s, Eviction's barriers of
    10 s, IndexJobsHarness's JOIN_MS, PubTesterIndexJobs's builds of 10 s;
  - waits that show that something does not happen, which load only
    lengthens: DbTesterFailure 1474 (`closer.join(300)`, then alive),
    InterruptTester 299, PubTesterIndexJobs 842, BufferedStream 1981 and
    FileStream 2771 (`sleep(100)`, then alive), Eviction 2228 and
    BufferedStream 1575 (no batch, few wakes, in 20 or 50 ms);
  - waits that only choose what a run checks, so load weakens the check
    and cannot fail it: StorageFaultTester 384 (0.5 s for the storage's
    failure) and 722 (50 ms for a background flush, both paths checked),
    StorageContractTester 125 (200 ms for the writer's call beside the
    held append), KillRestartHarness 2034 (8 s marks a kill late),
    IndexJobsHarness 1244 (50 ms after a RUNTIME fault in the cleanup,
    whose thread returns and leaves the marker for good, IndexManager);
  - lower bounds (PubTesterIndexJobs 866, DbTesterStream 740's 50 ms);
  - bounds far above the time: StoredTrans.testFindNode 1414 (2 s; the
    test takes under 0.1 s, the fault seconds), FormatFuzzer.measure
    (20 ms + 200 ns a byte, the least of three), DbTester 2899
    (`stop()` returns in under 1 s);
  - InterruptTester 145 (testCommitThatWaitsForRoom: forces held for
    300 ms, in which 5 commits of 20 KB fill the buffer) and
    BufferedStream 1216-1235 (testQuarterAvoidsRoomWaits: a writer of
    1 KB a ms must not fill 256 KB): both could fail on a machine loaded
    far more than the runs below; neither failed in them.

Gate on this commit's Java, 2026-11-13: `BEFORE COMMIT OK (62 s)` (unit
1700, f 89, demos 14), log `/Users/f/fl/bench/2026-11-13/limits/gate2.txt`.
The three runs beside 20 processes of `yes > /dev/null` (2 x 10 cores),
both slots held, 07:49 to 07:55: each `BEFORE COMMIT OK` (116, 116 and
114 s; unit about 83 s, f about 89 s, against 37 and 51 s unloaded); logs
`/Users/f/fl/bench/2026-11-13/limits/load-gate1.txt` to `load-gate3.txt`,
with each run's `build/before-commit/` in `load-gate1-logs/` to
`load-gate3-logs/`. The Eviction loops: `limits/evloop.txt`; the scripts
`limits/load.sh` and `limits/evloop.sh`.


State
-----

Done: commit "021-28" on branch `021-28-time-limits` in
`/Users/f/fl/bench/2026-11-13/limits/clone` (main 6239e245 below it),
with this entry and its row in the readme; to land by the coordinator.
Nothing open.

