019-43. Fix: harness 6.2 on s1: a failed first read, "no call reported it, and close() returned normally"
========================================================================================================

Status: done 2026-11-06. Kind: Fix. Frans: none.
Created 2026-11-06 by Frans Lundberg.

What: the unit test `StorageFaultTester.testSample` (harness 6.2, 018-03)
fails now and then on s1 (2 CPUs), with JDK 17: 1 failure in the first 12
runs of `java -ea -cp JAR bergdb.core.StorageFaultTester SAMPLE` on a jar
of `main` at 2691750:

    019-09: close | STREAM STOP reopened | STREAM, READ, in thread
    StorageFaultTester-runner: STREAM STOP at 1, reopened: the storage had
    failed (the fault at STREAM call 1, READ), no call reported it, and
    close() returned normally (019-09)

A timing race: either a Core fault of 019-09's class (a close after a
failed read at the stream's first call reports nothing) or the harness's
oracle (it counts as failed what the database rightly did not see).

Why: found by agent r30 of 006-13 in the release's rehearsal (018-09):
the jar's tests on s1 (R5) and `night.sh large` may fail on it tonight.
The outputs are on s1 in `/opt/bergdb-bench/018/rel/probe/` (`loop.txt`,
`s-17-6.txt`). Today's changes on the same paths: 019-10 (01b0493),
019-39 (940e603), 019-41 (8f0d117).

Frans: none. If it is a Core fault, it is fixed (Frans, 2026-11-06, 12:31:
"If the bug is in Core, register it and fix it to your best ability.");
if it is the oracle, the harness is fixed.

Done when: the cause is found (a reproduction, on s1 or on F53 with the
timing forced by a hook); the fix with a test that fails before it;
`StorageFaultTester SAMPLE` in a loop on s1 with JDK 17 and 27 (say 100
runs each) without a failure; `BEFORE COMMIT OK`; landed before 20:15.

First step: the failure's output on s1, and the code of `close()` after a
failed read (019-09's fix, c5a93d1, and today's changes).


Log
---

2026-11-06. Registered by coord-1106 from agent r30's rehearsal.

2026-11-06, 12:46. Also on F53, with JDK 17 (r30's rehearsal, the jar's
night tests): `StorageFaultTester.testStreamLayerAll`, "019-09: close |
STREAM STOP reopened | STREAM, READ, in thread StorageFaultTester-runner:
STREAM STOP at 9, reopened: the storage had failed (the fault at STREAM
call 9, READ), no call reported it, and close() returned normally";
output in `/Users/f/fl/bench/018/release/rehearsal-run/jartest/17/Night.txt`.
JDK 27 on F53 passed all (unit 1,244, F 87, night 15). So not only the
first call, and not only s1: JDK 17's timing.

2026-11-06, 13:15. In progress: agent f43 of coord-1106 (clone
`/Users/f/fl/bench/006-13/f43`, branch `f43`).

2026-11-06. Done by agent f43 of coord-1106: the harness's oracle, not the
Core. See "Cause" and "Fix" below.


Cause
-----

The fault is a STOP: the harness calls `db.stop()` in the workload's
thread at a stream call, a READ here, and the read then goes on. `stop()`
does not wait: its closer thread takes the write lock (free: a get, or a
transaction's warm-up, reads without it), and closes the storage, the
`FileStream` too. When the closer is quick, as with JDK 17 now and then,
the read then meets the closed file: `FileStream` throws "File closed",
`StorageManager.read` records it as the main stream's failure
(`handleStreamException`), and the call throws `StreamIoException` with it
as the cause. The database is STOPPING, so `failOnStorage` does not fail
it, and the transactions after are refused by the stop. Nothing that
returned is lost, and `close()` returns normally.

The database is right: docs/levels.md, section 3, "A read or a sync while
the database stops throws as it did"; `close()` throws for a failure
before the close began, which none was (019-09, option (a)). The oracle
read `storageFailed()` just before `close()`, after the stop at the fault
had begun the close, and counted the read that the close overtook as a
failure that no call reported (check 7, 018-03, section 1).

Reproduced on F53 at will with a hook: after the STOP, the call waits
until the stop's close has ended (`Db.Internal.isClosed()`); STREAM STOP
at 1, 2, 3, 5 and 9, reopened, each gave the finding (the get 10 or the
warm-up of execute 20 threw `StreamIoException: File closed`), on JDK 27
too; and on s1 with JDK 17.

Is the recorded failure visible to a user? Checked, at the coordinator's
request: no. `StorageManager.hasFailed()` and `getFailure()` are read by
`Db.assertDbStateIsActive` (only while ACTIVE, and a stopped `Db` never is
again), `Db.closeStorage` (before the close, so false here), `Db.close()`'s
branch for a close within a transaction (not reached: a transaction that
takes the write lock after the closer sees STOPPING and is refused, and
the closer waits for one that holds it, so no read of a running
transaction can meet the closed stream), and `Db.Internal.storageFailed()`,
for tests. No JMX attribute, log line or status call reports it; a sync
while stopping throws "Storage is closing" whether or not it has the read's
failure as its cause; the stream's bytes are unchanged, and the next start
of the directory holds every returned transaction (check 9 passed in every
run). So the Core is left as it is.


Fix
---

* `StorageFaultTester.close` (check 7): the storage's state is taken
  before the close begins; for a STOP that fired, the stop at the fault
  began it, so a failure recorded after it is the close's, not one that no
  call reported.
* The hook: `StorageFaultTester.waitForCloseAtStop` (and, for runs by hand,
  `-Dbergdb.storagefault.waitclose=true`): after the STOP, the call waits
  up to 2 s until the stop's close has ended.
* The test `StorageFaultTester.testStopWhileReading` (unit): STREAM STOP
  at 1 (a warm-up) and 3 (a get), reopened, with the hook; it checks that
  the read met the closed stream (`StreamIoException`) and that no check
  fails. Before the fix: "019-09: close | STREAM STOP reopened | ... no
  call reported it, and close() returned normally" (2 runs); after:
  passes.
* 018-03, section 1, check 7, says so. Test code only; no Core change, so
  no line in releases/next.md.


Runs
----

On a jar of the fix (2026-11-06, 13:17 to 13:34):

* s1, `StorageFaultTester SAMPLE`, JDK 17 and 27 in turn: 100 runs each,
  all passed (before: 1 failure in 10 to 12 runs with JDK 17).
* F53, the same with JDK 17 (17.0.21): 100 runs, all passed; then the
  night tests of `StorageFaultTester` (`testStreamLayerAll` and
  `testIoLayerAll`) 3 times with JDK 17: passed, 3,477 to 3,488 STREAM
  runs and 1,187 IO runs each.
* F53, a sweep with the hook on for every STOP
  (`-Dbergdb.storagefault.waitclose=true ... StorageFaultTester STREAM
  13`): 1,362 runs, no finding. A STOP within a transaction's write lock
  waits the hook's 2 s, as the closer waits for the lock.
* `before-commit.sh`: BEFORE COMMIT OK, before and after the rebase onto
  `main` with 019-44.
