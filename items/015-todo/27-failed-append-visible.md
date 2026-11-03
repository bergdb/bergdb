015-27. Decide: a failed append's transaction was already visible to readers
============================================================================

Status: open. Kind: Decide. Created 2026-11-03 by Frans Lundberg.

For Frans: which side to change (recommendation in 016-02).

What: A get that runs while a put's append fails can see the put's values before the failure; `docs/levels.md`, section 3, says that a transaction is visible only after it is stored. One of the two is wrong: the code or the text.

Source: review R3, R3-F8 (016-06/R3, items/016-release-2026-2/07-concurrency/r3.md),
confirmed by verify-1 (items/016-release-2026-2/06-reviews/verify-1.md,
section R3-F8), with its probe and the reach.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`; or the entry is a known issue
in 2026.2's notes.

First step: the probe of R3-F8, made a test.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).
