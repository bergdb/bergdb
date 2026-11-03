015-09. Fix: Reclaim.Tester.testCrashBeforeIterationEnd depends on timing under load
====================================================================================

Status: open. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

For release 2026.2: the test is in `java/before-commit.sh`, the only
commit gate (Frans, 2026-11-03, 15:40), so a test that fails under load
blocks or confuses the commits.

What: `bergdb.core.Reclaim.Tester.testCrashBeforeIterationEnd` failed once
in a `before-commit.sh` of 005-80's clone on F53, under the load of other
agents' gates: "truncate to 241352, before the length at the last cut,
246952". It passed 5 of 5 alone, and 005-80's change does not touch it.
The physical cut waits for durability (005-72), so under load it can land
after the record the test truncates to.

Why: a gate's test must not depend on timing.

Done when: the test waits for the cut it depends on, or truncates
relative to the cut's position, so that it does not depend on when the
cut lands; it passes under load (for example, 20 runs beside a stress
run); `BEFORE COMMIT OK`.

First step: read the test against 005-72's account of the physical cut.

Found 2026-11-03 by F1 in 005-80's gate (016-05).


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).
