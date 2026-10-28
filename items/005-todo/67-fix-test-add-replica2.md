005-67. Fix: `StorageManagerTester.testAddReplica2` fails about one run in twelve
=================================================================================

Status: done (2026-10-28; see Outcome). Kind: fix. Created 2026-10-28.

Registered at Frans's request (2026-10-28, through 006-10's session: the
test fails nights, and is to be fixed today), by Claude (Opus 5.5, Claude
Code).


The issue
---------

The unit test `StorageManagerTester.testAddReplica2`
(`java/src/bergdb/storage/`) fails now and then, "Expected 700, got 200."
It starts a `StorageManager` on a main `MemoryStream` of 700 bytes, adds a
replica, a `MemoryStream` of 200 bytes (`addReplica`, a buffer of 1,000
bytes and 10 ms), has a thread copy the main's bytes to it
(`syncReplica`), polls until the replica's status is `STATUS_ACTIVE`,
appends 100 bytes, asserts that both streams have 700 bytes, closes the
manager and asserts 800 for both.

Replication is experimental (005-11), but this is a unit test: it runs in
`java/before-commit.sh`, in the level scripts, and twice a night since
2026-10-28, in `before-commit.sh` (step 1 of `java/night.sh`) and in
`java/stress/core-build.sh unit f` (step 2, 005-56's follow-ups). A
failure fails a night step.

History:

* 2015-07-23: Frans's note in the test, "got non-reproducable unit test
  error, on Cissi": "Expected 800, got 1200", the replica's length after
  `close()`. In the same commit (`7c458d1` of the 2013 to 2017 history, the
  bundle in F1-007) he added the two assertions of 700 after the append.
* 2026-10-17, 001-02 (R8's change 2): `level3.sh` failed twice on it,
  "Expected 700, got 200", and "the storage tests fail 1 time in 12 also
  with `l34-base`'s jar"; R8's changes 3 and 4 (2026-10-17) and J6 and J7
  (2026-10-18) each had a gate run fail on it once, on a loaded machine.
  001-05, point 6: "four gates run it four times".
* 2026-10-22: the night's `before-commit.sh` failed on it, "Expected 700,
  got 200" (`java/build/night/2026-10-22-0200/`).
* 005-11's report (what the tests cover): the note of 2015 "records a
  failure on 2015-07-23 that was not reproduced".
* 2026-10-28: a run of `core-build.sh unit f` in 005-56's follow-ups
  failed on it.

The question is whether the test is wrong (it reads a length before the
asynchronous write it depends on, or assumes that a write has not happened
yet) or the code (a race in adding a replica: bytes lost or written twice,
a wrong confirmed length). 005-48's group commit (`e611709`: a sync starts
the flush) changed the timing of syncs; the test makes none.


Done when
---------

The cause is found and shown, with an instrumented copy or a forced
interleaving that makes the failure certain; the fault is fixed where it
is, in the code with a test that fails before if the code is wrong,
without weakening what the test checks; the test alone in a loop, at
least 10 times the runs that showed the failures before, has no failure,
also with the forced interleaving where it still applies;
`java/before-commit.sh`, `java/stress/core-build.sh unit f` and
`java/stress/level2.sh quick` pass; committed.


First step
----------

Run the test alone in a loop until it fails, to know the failure rate,
and read `StorageManager.addReplica`, `SynchingStorage.sync` and
`BufferedStream`'s flush against the test's assertions.


Findings
--------

2026-10-28, by Claude (Opus 5.5, Claude Code), in a clone of `main`. The
scripts, the probes and their output are in
[67-fix-test-add-replica2/](67-fix-test-add-replica2/) (see Files).

**The test is wrong; the code does what it promises.** The test's two
assertions of 700 right after the append read the `MemoryStream`s at a
moment that nothing in the code fixes:

* *Active is not written.* `SynchingStorage.sync` appends the main's last
  bytes to the replica's `BufferedStream` and makes the replica active
  (`makeActive`), both with the write lock. The buffer's thread writes the
  bytes to `m2` later: at the end of its current wait of 2 ms (a quarter of
  the replica's buffer time of 10 ms), as 500 bytes are more than a quarter
  of its 1,000, or 2 ms after the append wakes it if it was idle. Active
  says that appends now go to the replica (`StorageInfo`: "can be appended
  to and read from"); what has reached the stream is the confirmed length.
  The test polls the status every 10 ms, so it passes when the replica's
  write comes before the poll that sees the replica active, a margin of
  about 8 ms. A buffer thread late by about the poll interval, as on a busy
  machine, leaves 200 bytes in `m2`: "Expected 700, got 200", the failure
  of 001-02's gates and of the night.
* *An append is not unwritten.* The replica's buffer writes the 100 bytes
  appended 0 to 2 ms after the append (its thread is idle or ends its
  fourth wait), the main's 5 to 20 ms after. The assertions come
  microseconds after the append; a test thread that loses the processor
  there for a millisecond sees 800 in `m2`, for longer in `m1` too.

Forced interleavings make each failure certain. An instrumented copy
(`probe/forced.py`; its diff `probe/forced.diff`) adds sleeps set by system
properties, 0 by default: the replica's buffer written late, the writer
descheduled after its append. 100 runs each, in one JVM
(`probe/Loop67.java`), on the code before (`runs/forced-before.txt`) and
with the fix (`runs/forced-after.txt`):

| Sleep | Before | After |
|---|---|---|
| The replica's buffer written 2 or 5 ms late | 0 failures | 0 |
| ... 10 ms late | 97: "Expected 700, got 200" (m2) | 0 |
| ... 50 ms late | 100: the same | 0 |
| The writer descheduled 1 ms after its append | 40: "Expected 700, got 800" (m2) | 0 |
| ... 3 ms | 100: the same | 0 |
| ... 10 ms | 100: the same, 57 of them in m1 | 0 |
| ... 50 ms | 100: "Expected 700, got 800" (m1) | 0 |

With the fix the test asserts the same lengths once the writes are
confirmed, and it passes under every sleep: in these interleavings the
code writes each byte once to both streams.

The natural rate before, without instrumentation, on F53 with a load of
about 3 to 12 from other sessions (`runs/natural-before.txt`): 4 failures
in 40,000 runs, 5,000 in each of 8 JVMs at a time (`probe/Loop67.java`):
"Expected 700, got 200" once and "Expected 700, got 800" (m2) three times;
none in 1,500 runs in one JVM, in 50 runs alone in a JVM each (`loop.sh`:
`bergdb.dev.Unit` with a filter), in 30 runs of the class and in 61 runs
of all the unit tests (`unit-loop.sh`). The gates' one in twelve (001-02)
was on a machine with a load of 40 to 90; the night runs the unit tests
beside the f-tests.

005-48's group commit is not involved: `flushSoon` is called by syncs
only, and the test makes none.

**A second fault of the same kind: appends without the write lock.**
`StorageManager.append` requires the caller to hold the write lock, which
`SynchingStorage.sync` takes for its last step (read the lengths, copy the
rest, make the replica active), so that no append falls in between.
`testAddReplica2` and `testAddReplicaWhileAppending` appended without it.
In `testAddReplica2` that did no harm, as the sync was done. In
`testAddReplicaWhileAppending` a writer appends every 10 ms while the
replica is added; an append between the sync's reading of the lengths and
`makeActive` reaches the main only, so the replica lacks its bytes and
`syncStrong(750)` waits for ever (rule D2 needs the replica). Forced with
a pause of 30 ms there (`r67.syncPause`), the test hung in 5 runs of 5 on
the code before, and `probe/WhileAppending67.java` (its steps, with
`close()` for the `syncStrong`) left the replica 20 or 30 bytes short; with
the writer holding the lock, none (`runs/forced-before.txt`). The window
is a few microseconds in 10 ms, and no gate has met it. `Db` appends with
the write lock that its `StorageManager` was built with, so a database is
not affected.

**The note of 2015, "Expected 800, got 1200", was a fault of
`BufferedStream`, fixed by 005-14.** The test then had no assertions of
700 (they came with the note, in `7c458d1`), so the failure was the
replica's length after `close()`: 400 bytes too many. 2015's
`BufferedStream` flushed 0 bytes when its thread woke between `close()`'s
`flushAndClose` and `stop()`, and a flush of 0 bytes appended the whole
ring buffer, stale bytes; 005-14 found and fixed it on 2026-10-21 (its
finding 3; CloseRace gave lengths of 100 and 107 for 7 bytes appended). In
2015 the ring's positions started at 0, not at the stream's length (fixed
2026-10-13), so after 600 bytes the stale flush began at index 600 of
1,000: 400 bytes to the end of the ring, then 600 from its start, which
the `MemoryStream` refused, as `close()` had closed it in between: 800 +
400. Shown with 2015's `BufferedStream` (`probe/old2015.py`, two sleeps)
under today's `StorageManager` (its replica code is that of 2015) and the
test as it was before the note (`probe/Old2015.java`): no failure in 200
runs; with 5 ms between `close()`'s wait and its `stop()`, extra bytes in
20 runs of 20 (1,800, 2,800 or 3,800 bytes); with the second append of the
stale flush 20 ms late as well, "Expected 800, got 1200" in 20 of 20.
Today's `BufferedStream` with the same pause: 800 in 20 of 20
(`runs/old2015.txt`).

**Found on the way, for 005-11, not changed.** The slot of a replica being
added is null in the manager's array of streams until `makeActive` (005-11's
P3: a cut during the copy throws `NullPointerException`). So `close()`
during the copy does not close the replica's `BufferedStream`: its thread
stays, and since 005-63 its directory stays locked, until the JVM ends
(`probe/CloseDuringSync67.java`, `runs/close-during-sync.txt`).


Outcome
-------

2026-10-28, by Claude (Opus 5.5, Claude Code), as registered; the change
in `dad6bd2` (test code only, on `90153f2`). The forced runs are of
`dad6bd2`; the natural loops ran on the same test code before a rebase
onto `90153f2` and the comment on 2015's note, which changed comments
only.

* `StorageManagerTester.testAddReplica2` waits for the writes it asserts.
  Once the replica is active, it waits until the replica's confirmed
  length is 700 (`waitForConfirmedLength`, at most 10 s) and asserts 700
  for both streams, before the append instead of after it; it appends with
  the write lock; it waits until the confirmed lengths of the main and the
  replica are 800 and asserts 800 for both; then `close()` and 800 again,
  as before. It checks the same lengths, where they are determined, and
  more than before: that the replica gets an append while the manager runs,
  not only through `close()`, and that `close()` adds nothing (2015's
  fault). No retry and no longer timeout: the waits are for what the
  assertions need. A comment in the test says why, and one under the
  note of 2015 what it was.
* `testAddReplicaWhileAppending`'s writer appends with the write lock.
* No change to `StorageManager` or `BufferedStream`, and none that users
  can notice: `releases/next.md` unchanged.
* After the fix, without instrumentation (`runs/natural-after.txt`):
  400,000 runs, 50,000 in each of 8 JVMs at a time, 10 times the 40,000
  that gave 4 failures before: 0 failures; 1,000 runs alone in a JVM each
  (`loop.sh`): 0 failures. With the forced interleavings: 0 failures in
  each (the table above); `testAddReplicaWhileAppending` with the sync's
  pause: 50 runs, 0 failures, none hung (`runs/forced-after.txt`).
* Gates in the clone on `dad6bd2`, with `nice -n 10` (`runs/gates.txt`):
  `java/before-commit.sh` "BEFORE COMMIT OK (89 s)" (deps: 9 packages as
  `package.html` allows; unit 1,058 tests, f 74);
  `java/stress/core-build.sh unit f` "CORE BUILD OK" (unit 674, f 54);
  `java/stress/level2.sh quick` "LEVEL 2 OK" (conformance: 14 traces,
  TRACECHECK OK).

Files, in [67-fix-test-add-replica2/](67-fix-test-add-replica2/):

* `loop.sh`: the test alone, each run in a JVM of its own
  (`bergdb.dev.Unit -c -m`), N times; `unit-loop.sh`: all the unit tests
  N times; `forced-runs.sh`: the forced interleavings on an instrumented
  copy.
* `probe/`: `Loop67.java` (a test of `StorageManagerTester` N times in one
  JVM, each in a thread with a timeout), `forced.py` and `forced.diff`
  (the instrumented copy), `WhileAppending67.java`, `Old2015.java` and
  `old2015.py` (2015's `BufferedStream`, instrumented),
  `CloseDuringSync67.java`.
* `runs/`: `natural-before.txt`, `natural-after.txt`,
  `forced-before.txt`, `forced-after.txt`, `old2015.txt`,
  `close-during-sync.txt`, `gates.txt`.
