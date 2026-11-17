015-36. Fix: an interrupted deleteIndex leaves the index deleting with no job
=============================================================================

Status: done 2026-11-09. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: `deleteIndex` on an interrupted thread throws after it has set the index to deleting, and starts no job: the index is stuck deleting until a restart. Normal use; no data lost. (After 015-21, a retry starts the job.)

Source: review R3, R3-F11 (items/016-release-2026-2/07-concurrency/r3.md),
confirmed by verify-2 (items/016-release-2026-2/06-reviews/verify-2.md,
section R3-F11), with its probe, the reach and the effect.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: the probe of R3-F11, made a test.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-04. Review R8 found the same (R8-F1, items/016-release-2026-2/06-reviews/R8.md).

2026-11-09. Done by release 2026.4's indexes (020-10), in night 006-15: gone: a deletion is one transaction with no job and no state "deleting"; a cleanup in the background removes the old entries (020-10, 6.2); 4f8210f (020-10, I2 part 1). The test: PubTesterIndexJobs.testDeleteWithInterruptFlag (the deletion done, the flag kept, no job of the name), in `before-commit.sh`, passing on `main` at `b768ef0` (020-11). Status: done.
