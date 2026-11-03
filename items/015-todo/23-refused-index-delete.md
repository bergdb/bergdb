015-23. Fix: a refused index deletion stops maintaining an index that stays active
==================================================================================

Status: open. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

After the release unless it fits (rare trigger; in 2026.1 too).

What: When `deleteIndex`'s metadata transaction is refused (a user clock out of range), the index stays active but is no longer maintained: it leaves out later objects, also after a restart.

Source: review R3, R3-F9 (016-06/R3, items/016-release-2026-2/07-concurrency/r3.md),
confirmed by verify-1 (items/016-release-2026-2/06-reviews/verify-1.md,
section R3-F9), with its probe and the reach.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`; or the entry is a known issue
in 2026.2's notes.

First step: the probe of R3-F9, made a test.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).
