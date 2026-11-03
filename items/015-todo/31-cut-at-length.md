015-31. Fix: a cut at the stream's length throws an internal Bug
================================================================

Status: open. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: `FileStream.pretruncate` at `pos == getLength()` throws `Bug` ("Unexpected newSize: 0"). Internal only: reclaim cuts behind its tail. No data lost on `main`; 2026.1 deleted the files before it threw.

Source: review R2, R2-F2 (items/016-release-2026-2/06-reviews/R2.md),
confirmed by verify-2 (items/016-release-2026-2/06-reviews/verify-2.md,
section R2-F2), with its probe, the reach and the effect.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: the probe of R2-F2, made a test.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).
