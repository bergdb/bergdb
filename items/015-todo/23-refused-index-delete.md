015-23. Fix: a refused index deletion stops maintaining an index that stays active
==================================================================================

Status: done 2026-11-09. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

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

2026-11-09. Done by release 2026.4's indexes (020-10), in night 006-15: a deletion is one transaction, refused or done, and the maps change only after its commit (020-10, 3.2 and 6.2); 4f8210f (020-10, I2 part 1), with harness H3 (9cbaa50). The test: IndexJobsHarness.testDeletionRefused (a refusal, an expiry and a RuntimeException at the deletion's transaction: nothing changed, in memory or in the stream; then the deletion works), in `before-commit.sh`, passing on `main` at `b768ef0` (020-11). Status: done.
