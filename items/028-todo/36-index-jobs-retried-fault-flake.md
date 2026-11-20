028-36. Investigate: IndexJobsHarness.testRetriedFaultThenDeletedDuringBuild under load
=======================================================================================

Status: done. Kind: Investigate. Frans: none.
Created 2026-11-20 by Frans Lundberg.

What: `IndexJobsHarness.testRetriedFaultThenDeletedDuringBuild` failed
once in the unit tests under load on 2026-11-20 (030-30's gates, a second
try of `week.sh short`), on a base before 028-29's fixes of the harness's
races (906f9854). It passed on rerun.

Why: the harness must fail only for the database's faults (020-15);
028-29 found four races of the harness's checks, and this may be one of
them or another.

Frans: none.

Done when: the failure is explained: one of 028-29's races (shown by the
test's message and the fixed code), or a new cause, found and fixed; if a
fault of the database, reported at once; `java/before-commit.sh` BEFORE
COMMIT OK; the test run under load (as 028-29's probe runs) with no
failure.

First step: find the failure's message in 030-30's logs (the week.sh
short run's report) and compare it with 028-29's findings.


Findings
--------

**One of 028-29's races; no fault of the database.** The failing run was
`week.sh short` 2026-11-20-1223, on 030-30's commit 9b0468be, whose
`IndexJobsHarness` is that of 9f6f7888, before 028-29's fixes (1c2ee58a,
16e8ff2a). Its unit tests printed:

    call made its change; INTERRUPT at BUILD_STEP (1 times), e.g.
    INTERRUPT at BUILD_STEP 1, 110 objects, seed 1, deleted during the
    build: creation 1 returned; memory has index "j" of "/j/",
    generation 5, building, levels long [n], the stream null

This is 028-29's second race, word for word: the deletion during build 1
(the harness's helper thread, at the build's third step call) committed
between the creation check's read of memory and its read of the stream.
The deletion commits and then changes memory under IndexManager's lock,
and `definition()` takes the lock, so a stream with no definition and
memory with one is a moment of that deletion. Since 1c2ee58a, `create()`
accepts the stream's null only if the deletion during build 1 has begun
and memory, read again after the stream, has no definition either; the
check is exact. 028-23's excuse (aeca1b32) covered only memory with no
definition at the first read.

**Probe runs** (the test's three runs, REFUSAL, EXPIRY and INTERRUPT at
BUILD_STEP 1 with a deletion during the build, repeated with new seeds,
each run checked as the test checks it, by a probe class in the package
`bergdb.pubimp`, not kept; 6 JVMs in parallel, with 3 KillEmpty parents
beside them for load; other sessions' runs shared the machine):

- the harness of 9f6f7888: 1 finding in 3,600 runs at a load of 6 to 12,
  the failure's message with seed 403602;
- the harness of main (c0b9683b): 0 findings in 9,000 runs at a load of 6
  to 18, and 0 in 36,000 runs with 12 JVMs (6 KillEmpty parents beside
  them) at a load of 11 to 48.

028-29 had reproduced the race on 9f6f7888 in 6 of 600 runs at a load of
50 to 80. No change to the code: main has the fix.


Gates
-----

On the branch `028-fx2` (no change to the code; main's harness):

- `java/before-commit.sh` at 851d2222: BEFORE COMMIT OK (78 s).
- The probe runs above under load: 0 findings in 45,000 runs.


Log
---

2026-11-20. Registered by coord-1120, from 030-30's report.

2026-11-20. Taken by fx2 of coord-1120, on the branch `028-fx2`.

2026-11-20. Done by fx2 of coord-1120: 028-29's second race, fixed in
main since 1c2ee58a; no fault of the database, no change.
