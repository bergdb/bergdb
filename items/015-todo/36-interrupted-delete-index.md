015-36. Fix: an interrupted deleteIndex leaves the index deleting with no job
=============================================================================

Status: open. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

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
