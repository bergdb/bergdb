015-70. Fix: a budget decrease can settle above budget although the pins fit
============================================================================

Status: open. Kind: Fix. Created 2026-11-04 by Frans Lundberg.

After release 2026.2 (a known issue of it); new in 2026.2.

What: review R4's finding R4-F5 (items/016-release-2026-2/06-reviews/R4.md,
section R4-F5: where, intended, actual, effect, a proposed fix), shown by a
probe in 06-reviews/R4/. No second agent has checked it yet.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: verify it (016-06, section 2.6), then the probe made a test.


Log
---

2026-11-04. Registered by the coordinator of release 2026.2 (016-02).
