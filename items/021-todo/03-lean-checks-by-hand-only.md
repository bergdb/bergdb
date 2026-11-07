021-03. Fix: Lean's test programs run by hand only, and TakeCheck does not compile
==================================================================================

Status: in progress. Kind: Fix. Frans: none.
Created 2026-11-07 by Frans Lundberg.

What: checks of the Lean model that no script runs, so that nothing tells
when they break:

1. `lake exe sistest`, `lake exe phystest` and `lake exe reclaimtest`
   (`lean/lakefile.toml`; random runs of the model, the physical layer and
   reclaim) are run by hand only: `lean/README.md`, "Build and run", gives
   the commands (about 7, 7 and 1 minutes at its sizes), and neither
   `java/before-commit.sh`, `java/night.sh` nor the level scripts call
   them. The level scripts run `lake build` (its `#guard`s) and
   `tracecheck` only.
2. 007-08's `TakeCheck.java` (`items/007-bounds/08-step4-take-in-lean/`)
   calls `TransSeq.dither`, which 005-79 removed, so it no longer compiles
   against `main`. 015-19 kept it for the code of its time (the double
   take of 005-79's base); 015-03 (open, in 015) is to bring Lean's
   `javaTake` and TakeCheck to Java's integer take.

Why: from agent d30's read-through of the documentation for release
2026.3 (006-13's progress, 12:44; 8996de0), not fixed before the release:
006-13, section 5, "For Frans to decide (in the morning)", point 1.
Recommended there: after the release. A check that nobody runs breaks
without a sign, as TakeCheck did.

Frans, 2026-11-07, 08:00: "For a., do as recommended."

Frans: none. Nothing is decided here beyond what "done" means below.

Done when:

1. sistest, phystest and reclaimtest run unattended, with sizes that keep
   the step to a few minutes: as a step of `java/night.sh` (its report
   says OK or FAILED, and a failure fails the night), through a script of
   their own in `java/stress/` if that is simpler. Not in
   `java/before-commit.sh`: a new harness joins it only if it adds a few
   seconds (Frans, 2026-11-05), and these take minutes. The step fails
   when a program finds a failure (each program's exit code checked, or
   its output; shown once with a failure made by hand) and needs elan as
   the level scripts do. `lean/README.md`, "Build and run", and night.sh's
   header say so.
2. TakeCheck: if 015-03 is done, TakeCheck compiles against `main` and
   joins the same step if it takes a few minutes or less; if 015-03 is
   still open, this entry does not wait for it, and 015-03's log gets one
   line that TakeCheck joins 021-03's step when it compiles.
3. One `java/night.sh` run with the step: NIGHT OK. `BEFORE COMMIT OK`
   if anything under `java/` changed.

First step: run the three programs at their README sizes in a clone (the
time and the output of each, its exit code on a failure), then choose the
sizes for the step; check 015-03's status.


Log
---

2026-11-07. Registered by coord-1106 from 006-13's morning list, point 1,
at Frans's word (2026-11-07, 08:00).

2026-11-07. Taken by agent f13 of coord-1107 (006-14).

2026-11-07. By agent f13 of coord-1107. Times on F53, in a clone of `main`
at bfacd87 (`/Users/f/fl/bench/006-14/f13/`), the machine otherwise quiet
(no performance.sh, night.sh or level script): `sistest 5 40` 104 s,
`phystest 5 40` 95 s, `reclaimtest 20 30` 51 s; each scales with its seeds,
so the README's sizes, 20 40, take about 7 minutes each, as it says. Each
program counts its failures, prints "N failures" instead of "all checks
pass", and exits with status 1 (`return (if bad == 0 then 0 else 1)`).

1. New `java/stress/lean-tests.sh`: builds the three with `lake build
   sistest phystest reclaimtest` (elan needed, as the level scripts),
   runs `sistest 5 40`, `phystest 5 40` and `reclaimtest 20 30` (`full`:
   20 40, 20 40, 20 30), and fails a program whose exit code is not 0 or
   whose last line is not "all checks pass"; one line per program, then
   LEAN TESTS OK, or LEAN TESTS FAILED with the names and exit status 1;
   outputs in `java/build/lean-tests/`. In the clone: LEAN TESTS OK in
   249 s (103, 95, 51 s; lake build 3 s with the main tree's `.lake`).
   Shown once with a failure made by hand (`bad := bad + 1` before
   sistest's last line, in the clone only): "sistest 5 40 FAILED 100 s
   exit 1: 1 failures", LEAN TESTS FAILED: sistest, exit 1, the other two
   ok. `java/night.sh` runs it as a step after level4 (`step lean-tests`;
   its header lists it as step 4, the night now about 55 minutes); a
   failure fails the night, as every step's does. Not in
   `before-commit.sh`. `lean/README.md`, "Build and run", says so.
2. TakeCheck: 015-03 is still open, so this entry does not wait for it;
   015-03's log has the line that TakeCheck joins this step when it
   compiles.
3. Open: one `java/night.sh` run with the step, NIGHT OK. night.sh clones
   HEAD, so it needs this entry committed first; the coordinator runs it
   when planned and closes the entry after it. `BEFORE COMMIT OK (120 s)` (2026-11-07,
   08:57), on the tree with this entry's and 021-01's changes.

State: done but for the night run of point 3.
