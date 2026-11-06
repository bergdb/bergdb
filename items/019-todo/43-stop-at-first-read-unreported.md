019-43. Fix: harness 6.2 on s1: a failed first read, "no call reported it, and close() returned normally"
========================================================================================================

Status: open. Kind: Fix. Frans: none.
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
