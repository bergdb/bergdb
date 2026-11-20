028-36. Investigate: IndexJobsHarness.testRetriedFaultThenDeletedDuringBuild under load
=======================================================================================

Status: open. Kind: Investigate. Frans: none.
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


Log
---

2026-11-20. Registered by coord-1120, from 030-30's report.
