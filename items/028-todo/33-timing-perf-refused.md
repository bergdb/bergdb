028-33. Fix: timing.sh's perf step is refused right after a build
=================================================================

Status: done. Kind: Fix. Frans: none.
Created 2026-11-20 by Frans Lundberg.

What: the first runs of `java/timing.sh` (2026-11-20, 02:54 to 04:17, on
f995e1a8, F53) measured CORE and the pause probe, but each perf step was
refused by `stress/performance.sh`'s own quiet check, `quiet_check`,
which dies under 90 % idle: at 18 % idle right after performance.sh
built the current tree, and at 74 % and 69 % idle right after
timing.sh's build of the candidate, although timing.sh itself had found
the machine 94 to 97 % idle at its start. timing.sh's WAIT and RUNWAIT
cover its own checks, not performance.sh's, which refuses at once.

Why: the perf step (performance.sh ab against the last release at 1M and
10M keys) is the release's timing figure and 028-19's; a timing run that
cannot reach it on a quiet machine fails its purpose. A macOS background
process (media analysis, about one core) was also busy at times that
night.

Frans: none.

Done when: performance.sh, called by timing.sh, waits for a quiet
machine for up to timing.sh's RUNWAIT (or its own wait setting) instead
of refusing at once, and its check runs after any build has ended; a run
of `java/timing.sh perf` on a quiet F53 reaches the scenarios; the
reports still say when a run was not quiet.

First step: java/timing.sh around its perf step (line ~277) and
java/stress/performance.sh's quiet_check (line ~221) and its callers;
the logs are java/build/timing/2026-11-20-0254/, -0353/ and -0414/ (not
kept in Git).


Result
------

- **performance.sh waits** (`quiet_check`): under MINIDLE % idle (a new
  setting, default 90 as before) it checks again every 30 s for up to
  QUIETWAIT minutes (new, default 0), printing each check, then runs, or
  stops with "the machine is not quiet (X% idle, under MINIDLE % for N
  minutes)". The line "CPU idle before the runs" says how long it waited.
  The check already came after the command's builds (the snapshot of
  "current", the harness's compilation); it stays there. caffeinate now
  starts before the check, so that a wait does not let the Mac sleep.
- **timing.sh passes** MINIDLE and QUIETWAIT=RUNWAIT (default 15) to
  `performance.sh ab`, the same wait as its own checks before each run of
  core and pauses. Its report has performance.sh's "CPU idle before the
  runs" line under "perf:".
- **A refusal is no longer an alert.** performance.sh exits 1 both for the
  comparison's alerts and for any `die`, its refusal included, and
  timing.sh took exit code 1 as alerts: the three runs of 2026-11-20 ended
  "TIMING ALERTS: perf" with an empty comparison line. timing.sh now reads
  the exit code only when the comparison ran ("Comparison exit code" in
  the log); otherwise a refusal is "stopped: the machine is not quiet
  (...)" and TIMING ALERTS: (busy, stopped: perf), as for core and pauses,
  and any other end is TIMING FAILED: perf with the log's last line.
- **By hand** performance.sh keeps refusing at once (QUIETWAIT=0): a person
  at the keyboard sees the refusal and the idle share at once, and the
  message names QUIETWAIT. A wait by default would leave a hand run
  silent for minutes on a machine that stays busy.
- **The cause** of the busy minute after a build, seen on F53 on
  2026-11-20 during the trials: Spotlight's mdworker processes indexing the
  new files (java/build/perf/builds/ is not in a `.noindex` directory, as
  timing.sh's reference clone is), and macOS's mediaanalysisd at about one
  core at times. Waiting covers both; the perf builds' place was not
  changed.

Trials (2026-11-20, F53, in a clone; the machine was 78 to 85 % idle
throughout, with desktop use and mediaanalysisd, so no trial met the
default MINIDLE of 90):

- performance.sh `reference` with SUITE=smoke, ONLY=w-hot-s: MINIDLE=99.9,
  QUIETWAIT=1: two checks, then refused after a minute, exit 1; MINIDLE=60,
  QUIETWAIT=3 with ten busy loops of 50 s: two checks at 0.0 % idle, then
  "CPU idle before the runs: 83.69% (after 70 s of waiting)" and the run,
  PERFORMANCE RUN DONE; MINIDLE=99.9 alone: refused at once, as before.
- `MINIDLE=78 WAIT=5 RUNWAIT=3 java/timing.sh perf`, FORCE unset, with
  performance.sh's snapshot of "current" removed so that it built it: 68 %
  idle right after the build, then 74 %, then "CPU idle before the runs:
  80.71% (after 70 s of waiting)" and the first scenario, read-100 [R];
  stopped there with a kill. The earlier code would have refused at the
  first check, as in the runs of 2026-11-20.
- `MINIDLE=70 RUNWAIT=1 java/timing.sh perf` with ten busy loops started
  after timing.sh's own check: performance.sh waited a minute and
  stopped; the report said "stopped: the machine is not quiet (0.0% idle,
  under 70 % for 1 minutes)" and TIMING ALERTS: (busy, stopped: perf), and
  the news entry "needs a look".

A run of `java/timing.sh perf` with the default MINIDLE of 90 on a quiet
F53 is left to the next timing run (013-02's plan): the machine was not
quiet during this work.


Log
---

2026-11-20. Registered by coord-1118 from the first timing runs.

2026-11-20. Done by an agent of the day's coordinator, on the branch
`028-33-timing-perf`: performance.sh's QUIETWAIT and MINIDLE, timing.sh
passes them and tells a refusal from alerts; the trials above.
BEFORE COMMIT OK.
