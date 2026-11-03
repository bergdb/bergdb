015-53. Fix: a transaction that runs when `stop()` comes is committed, but `execute()` throws `DbStoppingException` from reclaim's step
=======================================================================================================================================

Status: open. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: review R7's finding R7-F4 (items/016-release-2026-2/06-reviews/R7.md,
section R7-F4: where, intended, actual, effect, a proposed fix), shown by a
probe in 06-reviews/R7/. No second agent has checked it yet.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: verify it (016-06, section 2.6), then the probe made a test.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).
