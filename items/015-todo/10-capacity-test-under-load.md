015-10. Investigate: CapacityTester.testBudgetLoweredAndRaisedUnderReads fails under load on s1
===============================================================================================

Status: open. Kind: Investigate. Created 2026-11-03 by Frans Lundberg.

For release 2026.2: the test is in `bergdb.dev.Unit`, which W6 runs on
the release's jar on s1 (016-09, R5).

What: in two of three full runs of `bergdb.dev.Unit` on s1 (Linux, 2
cores) on the jar of `f2cb23b` with BuildInfo set to 2026.2, with JDK 27
and 17, on 2026-11-03 at 16:29 and 16:30, the test failed: "at most 924984
bytes, budget 231246 of 924984" (nothing was evicted after the budget was
lowered); then `NanotestForBergDB.databasesStopped` failed, as the failed
assert leaves its database running. A third run passed; the class alone
passed 3 of 3; on F53 it passes. s1 was not idle then: 016-08's runs were
on it. Between `323a54a`, whose jar passed on s1, and `f2cb23b` in `java/`:
`dde82e8` (005-79 A, the integer watermark), `b281d39` (005-69) and
`522b645` (005-80, Eviction's test hook).

Questions: does the test depend on timing (the eviction thread's wake on
a loaded machine), or did one of the three commits change it?

First step: the base's jar and main's, full Unit in turns on s1 under the
same load (`/opt/bergdb-bench/016/h4/cap-check.sh`, from 16:36).

Done when: the cause is known, and the test is fixed (Fix) or the change
is.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-03, 16:43. The first step: six full runs of `bergdb.dev.Unit` on
s1, the base's jar (`6f932f0`) and main's (`3e32f02`) in turns, the first
two rounds beside the night tests (load about 3): all SUCCESS, the test
passed each time. Unit took 29 to 90 s with the base's jar and 42 to 57 s
with main's, so the doubled time follows the load, not the commits. Not
reproduced; most likely the test waits too briefly for the eviction
thread on a loaded 2-core machine. Next: read the test's wait against
005-51's and 005-65's wake, and make the wait a bounded poll if it is a
fixed sleep.
