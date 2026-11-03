015-39. Fix: an index build's status object reads the worker's changing counter
===============================================================================

Status: open. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: A `Job.getStatus()` kept and read later changes its note, as it reads the worker's counter; the status is meant to be immutable. Wrong status text only.

Source: review R3, R3-F7 (items/016-release-2026-2/07-concurrency/r3.md),
confirmed by verify-2 (items/016-release-2026-2/06-reviews/verify-2.md,
section R3-F7), with its probe, the reach and the effect.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: the probe of R3-F7, made a test.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).
