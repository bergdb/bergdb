028-33. Fix: timing.sh's perf step is refused right after a build
=================================================================

Status: open. Kind: Fix. Frans: none.
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


Log
---

2026-11-20. Registered by coord-1118 from the first timing runs.
