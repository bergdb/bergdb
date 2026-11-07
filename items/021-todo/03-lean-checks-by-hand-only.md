021-03. Fix: Lean's test programs run by hand only, and TakeCheck does not compile
==================================================================================

Status: open. Kind: Fix. Frans: none.
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
