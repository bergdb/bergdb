028-29. Investigate: IndexJobsHarness counts a slow cleanup as stuck
====================================================================

Status: in progress. Kind: Investigate. Frans: none.
Created 2026-11-19 by Frans Lundberg.

What: `IndexJobsHarness` may count an index cleanup that is slow, on a loaded
machine, as stuck (a possible race between the harness's deadline and
the cleanup's steps). Separately, `testEveryPointAndFault` failed once
in the unit tests at a load near 80 on 2026-11-19 and passed on rerun
(028-24's gates; the log is kept outside the repository).

Why: A false failure of a harness costs a night's result and hides real ones;
the gates run on loaded machines.

Frans: none.

Done when: The cause of both is known; a harness counts a cleanup as stuck only
when it makes no progress, not by wall-clock alone; the flake reproduced
or explained; `java/before-commit.sh` BEFORE COMMIT OK; the index jobs
harness soak OK.

First step: Read how IndexJobsHarness decides "stuck" and what the failing run of
testEveryPointAndFault printed.


Findings
--------

**No fault of the database.** Both failures are races of the harness's own
checks with the index jobs that it runs; the database did what 020-10
says in each.

**testEveryPointAndFault, 2026-11-19.** The run that failed (the log of
028-24's gates) was "STOP at CLEANUP_STEP 2, 110 objects, seed 1", with
the finding "restart; after the start, memory has index "j" ...
generation 14, building ..., the stream index "j" ... generation 14,
active". The stop at the cleanup's second step came while build 2 still
ran, so the restart resumed it. `restart()` read memory's definition
(building), then the stream's: the resumed build activated the index
between the two reads. The same race of the check was seen once at
5dfee887 (023-05, p5-merge, section 3). `IndexManager.activate` holds its
lock from before the activation's commit to after memory's change, and
`definition()` takes the lock, so the two states are only a moment apart:
memory changes right after the commit, and the later check of the job
(`checkResumed`: the build ends ACTIVE, memory then active) passed in the
failing run, as it was the run's only finding.

Reproduced on 9f6f7888 at a load of 50 to 80: 1 run of 960 (STOP at
CLEANUP_STEP, BUILD_STEP, CLEANUP_END and ACTIVATE_BEFORE, 6 JVMs in
parallel), the same finding; made every time by
`testActivationBetweenRestartReads`, which waits between the two reads for
the resumed build to end.

**A second race, found here.** `testRetriedFaultThenDeletedDuringBuild`
failed once in 25 runs of the class at a load near 80: "call made its
change; creation 1 returned; memory has index "j" ... building ..., the
stream null". The deletion during build 1 (the harness's own helper
thread, at the build's third step call) committed between the creation
check's read of memory and its read of the stream. 028-23 had excused
the case where memory already had no definition, not this one.
Reproduced on 9f6f7888: 6 runs of 600 (INTERRUPT at BUILD_STEP 1, deleted
during the build). The deletion, like the activation, commits and changes
memory under IndexManager's lock.

**A third and a fourth race, found here.** `testEveryPointAndFault`
failed once in 20 runs of the class on the first fix: "stop; ERROR at
CLEANUP_END 1: the database stopped creation 2 with no stop". The Error
in the cleanup's thread fails the database (IndexManager.startCleanup),
and the harness's probe (`probe()`) made a get, then read the Db's state:
the get came before the failure, the state after it, and the probe took
the database for stopped. A get made again threw DbFailedException each
time (a probe with the details). Beside it, `alive()` read the field
`fired` twice: an Error that fired in the cleanup's thread between the
two reads skipped the wait for the failure and gave the finding "Error
fails the database ... the database goes on". Both reproduced on the
code before this fix: 14 runs of 1,800 (ERROR at CLEANUP_STEP and
CLEANUP_END), 12 of the first kind and 2 of the second; the database
failed with the Error injected each time.

**"Stuck" by the time alone.** `awaitCleanup()` counted a cleanup stuck
when its markers were left after CLEANUP_MS (30 s times harness.slow),
whatever the cleanup did; the restart's wait for the resumed cleanup was
the same, and a build's join had a bound of JOIN_MS (10 s times
harness.slow). After a RuntimeException at a cleanup's point, the harness
waited 50 ms and took the first marker as the one that stays. On a loaded
machine a cleanup that makes progress could pass these bounds (the
cleanup's thread runs at the lowest priority, with pauses between its
steps).

**The fix** (`IndexJobsHarness`, the harness only):

- `awaitMarkers()`: the live and the restart's waits for the cleanups
  count progress: the markers left and the number of entries of each
  marked generation, counted at most every 100 ms (less often on a large
  run, at most a tenth of the time). No one writes a deleted generation,
  so a change is a cleanup's progress. A cleanup is stuck only after
  CLEANUP_MS with no change; a slow cleanup that makes progress is waited
  for.
- The cleanup that the fault ended (a RuntimeException at CLEANUP_STEP or
  CLEANUP_END) is known at once from the thread that the fault fired in,
  "IndexCleanup-NAME-GEN": its thread returns and its marker stays for good
  (IndexManager.startCleanup). No wait decides it.
- `joinProgress()`: a build's join is taken again while the build's count
  grows; "hang" only when one join of JOIN_MS saw no committed step.
- `disagree()`: the restart accepts memory building and the stream the
  same definition activated only if memory read again after the stream
  has the activation (the lock above makes this exact).
- The creation's check accepts no definition in the stream only if the
  deletion during build 1 has begun and memory read again after the
  stream has none (the same lock).
- `probe()`: a get that returned while the Db is no longer active is made
  again, and its exception tells a failure from a stop. `alive()` reads
  `fired` once, before the probe, for the check of an active database
  after an Error; for a stop or a failure seen, after it.

**Tests.** `testSlowCleanupNotStuck` (each cleanup step sleeps 150 ms, 11
steps, a bound of 1 s without progress: no finding), `testNoProgressStuck`
(the second step waits 1.5 s, a bound of 300 ms: the finding "cleanup; no
progress for 300 ms"), `testActivationBetweenRestartReads` (fails with the
old comparison, with the 2026-11-19 finding, at the first run; passes
with the fix), `testDisagree`. About 5 s more in the unit tests.

After the fix, the same probes at a load of 35 to 50: 0 findings in 960
and in 600 runs; the class's 12 tests passed in repeated runs.


Log
---

2026-11-19. Registered by coord-1118 from a report of the day's work.

2026-11-20. Taken by hf of coord-1120, on the branch `028-29-28-harness`.
