015-24. Fix: a refused open through another class loader releases the active directory lock
===========================================================================================

Status: open. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

For 2026.2: new in this release.

What: Two class loaders that each load bergdb.jar (two webapps, a hot redeploy): the second `start()` on the same directory is refused, and its cleanup drops the first database's directory lock, so another process could then open the directory and write beside it. New in 2026.2 (005-63).

Source: review R2, R2-F1 (016-06/R2, items/016-release-2026-2/06-reviews/R2.md),
confirmed by verify-1 (items/016-release-2026-2/06-reviews/verify-1.md,
section R2-F1), with its probe and the reach.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`; or the entry is a known issue
in 2026.2's notes.

First step: the probe of R2-F1, made a test.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).
