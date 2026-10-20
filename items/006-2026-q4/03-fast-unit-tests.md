006-03 Fast unit tests
======================

Created 2026-10-20 by Claude (Opus 5.5, Claude Code), at Frans's request.
Status: done.

The unit tests (`bergdb.dev.Unit`, group "unit") should be very fast: each test
normally at most 100 ms, as `Unit`'s comment of 2012 says, with reclaim and
eviction still tested. Slow tests got a small unit version and keep their full
version as an f-test (`bergdb.dev.F`, group "f"), named with an F at the end.
Only tests changed; the Java of BergDB did not. Then, at Frans's request, a
new check before a commit, `java/before-commit.sh`, the unit tests and the
f-tests, replaced the four level scripts as the commit gate.


Before
------

On F53, JDK 27, 2026-10-20, commit `c6ca623`, with another session's gates
running (load about 4 on 10 cores):

| Group | Tests | Time |
|---|---|---|
| Unit | 942 | 41.5 s (16.6 s on 17 October, before Level 4's tests) |
| F | 36 | 79.0 s |

`Eviction` alone took 21.2 s of the 41.5; `testReclaimWithMisses` 10.1 s.


Why the tests were slow
-----------------------

Wall time against CPU time, and stack samples, gave four causes.

1. **A sync waits for the storage thread's poll.** `BufferedStream` writes a
   small append after four waits of a quarter of the buffer time; the unit
   test setup's buffer time is 10 ms (`DbBuilder.testSetup`), so a sync waits
   up to about 10 ms, and a sync does not ask for a flush. The Eviction twins
   sync both databases after every transaction: `testReclaimWithMisses`, 10.1
   s of wall time and 1.5 s of CPU. The old tests that use the default buffer
   time, 100 ms, take 100 to 130 ms each for the same reason.
2. **No wake-up after a storage failure.** `StorageManager.setError` does not
   notify the threads waiting in `sync` and `syncStrong`; they see the error
   at their next poll, `wait(500)`. Five tests took 0.5 s each and 2 ms of
   CPU.
3. **Fixed windows.** `testPointerPairIsCoherent` reads for 1.5 s;
   `testReaderPausedInsideAFollow` gives the sweep 500 ms, in each of three
   tries.
4. **Work.** 131,000 transactions (`testRestartAfterManyTopNodes`), values of
   1.5 MiB through a 100 kB buffer (`testLargePuts`), two scans pausing at
   every KV (`testStalledReaders`), five schedules and the audit after every
   transaction (the twins).

An experiment in a scratch copy, not applied: a sync that asks for a flush,
and a wake-up on error, took Unit to 15 s. `StorageManagerTester.testWait2`
then fails, by design (it checks that a sync waits for the buffer time).
Frans: the buffering has its reasons, `sync(STRONG)` is unusual in practice,
and the buffer time is a setting (it could, and should, be one of the stream
storage). Not changed.


What changed
------------

Split into a unit test and an f-test (unit / f):

| Test | Unit | F |
|---|---|---|
| `Eviction`, the seven twin cases | one schedule (values, every or random, varied over the cases), `check(false)` skipped (`Twin.quick`); three cases with fewer transactions | every schedule, every check, as before |
| `EvictionReaderTester.testReaderPausedInsideAFollow` | one try, 50 ms for the sweep | three tries, 500 ms |
| `ReclaimReaderTester.testPointerPairIsCoherent` | reads for 50 ms | 1.5 s |
| `CapacityTester.testReadsWithoutWrites` | 1000 keys, budget 50 kB | 4000 keys, 200 kB |
| `CapacityTester.testSameRecordsAsWithoutEviction` | 300 transactions | 800 |
| `Reclaim.Tester.testCutIsMadeAfterDecisionIsDurable` | two cuts, no sync | three cuts, a sync every seventh transaction |

Moved to the f-tests, unchanged: `CapacityTester.testLargePuts`,
`testStalledReaders` and `testPinnedAboveBudget`;
`DbTesterRestart.testRestartAfterManyTopNodes`;
`ReclaimReaderTester.testReaderExpiresWhenCutOvertakesIt` and
`testLatestReaderExpiresWhenCutOvertakesIt`; and the five of cause 2,
`DbTester.testSyncAfterStreamFailure`, `DbTesterStream.testReadOnlyStream2`
and three of `FileStreamPowerLossTester`.

The level scripts: `level4.sh` runs the f-tests of the eviction classes after
the unit tests, and `level3.sh quick` those of reclaim and of
`FileStreamPowerLossTester` (`level3.sh` full runs all f-tests, as before), so
each runs the full versions it ran before through the unit tests.
`level1.sh` and `level2.sh` no longer run the three moved tests of their
levels (`testSyncAfterStreamFailure`, `testReadOnlyStream2`,
`testRestartAfterManyTopNodes`); `level3.sh` does.

The four level scripts pass, full, on `39ab4a8` with the change (141 s, 744 s,
466 s and 858 s).


The check before a commit
-------------------------

`java/before-commit.sh` builds, then runs the unit tests and the f-tests at
the same time, each in its own JVM, and prints `BEFORE COMMIT OK`. It is the
only requirement before a commit (AGENTS.md, README.md, docs/levels.md); the
level scripts are deeper checks, run after larger changes. No unit or f-test
writes to a fixed path, so the two JVMs do not meet. On `9d909cc` with the
change: unit 933 tests in 10.0 s, f 59 in 112.0 s, 116 s in all.

What the level scripts check and this does not: the random stress programs
at scale (RestartStress, CrashTest, RestartInvariance, ReclaimStress,
EvictionInvariance, LargerThanMemory), conformance with the Lean model, and
the MEM and SS limits of `level1.sh`. A few minutes of their quick
configurations, with fixed seeds, could join the check later, within a
budget of about 5 minutes; the rest belongs to nightly runs.


After
-----

| Group | Tests | Time |
|---|---|---|
| Unit | 931 | 10.3 s |
| F | 59 | 110.3 s |

Same machine and load. Each changed unit test passed 30 runs of 30 in a row
(`testCutIsMadeAfterDecisionIsDurable` 200 of 200), warm at 26 to 97 ms. The
`Eviction` class takes 0.5 s, `CapacityTester` 0.6 s.

The unit tests over 100 ms now: about 30 older tests at 100 to 130 ms that
wait for one default buffer time (cause 1: `PubTester`'s sync and encryption
tests, `StorageManagerTester`, `NodeStreamTester`'s restarts, the
`ScenarioTester` scenarios), and `DbTesterRestart.testOrdinalsWithReclaim`,
`PubTester.testBadStartReplica`, `PubTesterIndex.testDeleteIndex1` and `2`
(about 230 ms each), `FileStreamPowerLossTester.testRecoveryBetweenEveryPrefixDeletion`
(180), `Reclaim.Tester.testPretruncate`, `CapacityTester.testSweepsStopNearLow`
and `testScans` (130 to 145).


Open
----

* The wake-up after a storage failure (cause 2) looks like a fix rather than
  a design choice: the five moved tests would be unit tests again. For Frans
  to decide.
* The buffer time as a setting of the stream storage (Frans, above), and its
  default: [005-13](../005-todo/13-buffer-time.md).
* The rest of the unit tests over 100 ms, above; then running the test
  classes in parallel.
