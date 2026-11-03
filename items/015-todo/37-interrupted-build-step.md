015-37. Fix: an interrupted retry of a build step ends the build for this run
=============================================================================

Status: open. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: A build step that conflicts with an application's writes, with an interrupt pending on its thread, ends the build: the index stays creating, progress -1, no error shown, until a restart resumes it. Normal use; no data lost.

Source: review R3, R3-F5 (items/016-release-2026-2/07-concurrency/r3.md),
confirmed by verify-2 (items/016-release-2026-2/06-reviews/verify-2.md,
section R3-F5), with its probe, the reach and the effect.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: the probe of R3-F5, made a test.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).
