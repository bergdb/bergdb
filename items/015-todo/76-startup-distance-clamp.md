015-76. Fix: db.setStartupDistance clamps to 400,000 to 10^9 bytes without saying so: a call with a setting in force below 400,000 writes 200 kB and changes the setting
========================================================================================================================================================================

Status: open. Kind: Fix. Created 2026-11-04 by Frans Lundberg.

After release 2026.2 (a known issue of it); new in 2026.2 (its Javadoc's promise).

What: review R6's finding R6-F5 (items/016-release-2026-2/06-reviews/R6.md,
section R6-F5: where, intended, actual, effect, a proposed fix), shown by a
test or probe in 06-reviews/R6/. No second agent has checked it yet.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: verify it (016-06, section 2.6), then the probe made a test.


Log
---

2026-11-04. Registered by the coordinator of release 2026.2 (016-02).
