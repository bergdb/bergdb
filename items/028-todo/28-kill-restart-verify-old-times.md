028-28. Investigate: the kill-and-restart harness's check at old times
======================================================================

Status: open. Kind: Investigate. Frans: none.
Created 2026-11-19 by Frans Lundberg.

What: `KillRestartHarness.verify()` reads the database at old times on the
real clock, with a retention of 20 seconds. A lookup whose time has
passed out of the retention is refused, and verify() does not tell such
a refusal from a lost or wrong value: a slow check on a loaded machine
could read too late and fail, or a check could be skipped. Noted while
sorting the test scripts by kind (028-23); not seen to fail.

Why: The harness must fail only for the database's faults (020-15), on loaded
machines too: night.sh and week.sh run under load.

Frans: none.

Done when: Either verify() reads only times inside the retention at the moment of
the read and says how it ensures it, or a refusal at a time that has
left the retention is counted as expected; a test that shows the case;
`java/before-commit.sh` BEFORE COMMIT OK; `kill-restart.sh 1000` KILL
RESTART OK.

First step: Read verify() (java/src/bergdb/pubimp/KillRestartHarness.java, around
line 942) and the lookups it makes; find whether a refusal can reach its
comparison.


Log
---

2026-11-19. Registered by coord-1118 from a report of the day's work.
