028-29. Investigate: IndexJobsHarness counts a slow cleanup as stuck
====================================================================

Status: open. Kind: Investigate. Frans: none.
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


Log
---

2026-11-19. Registered by coord-1118 from a report of the day's work.
