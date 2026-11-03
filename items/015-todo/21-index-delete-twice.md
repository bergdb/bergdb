015-21. Fix: a second delete job lets the first delete a replacement index
==========================================================================

Status: open. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

For 2026.2 if it fits; else a known issue (in 2026.1 too).

What: `deleteIndex` twice, then an index of the same name created while the first job still runs: the old job deletes the new index and its entries, also after a restart. A loss of derived data, through the Pub API.

Source: review R3, R3-F1 (016-06/R3, items/016-release-2026-2/07-concurrency/r3.md),
confirmed by verify-1 (items/016-release-2026-2/06-reviews/verify-1.md,
section R3-F1), with its probe and the reach.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`; or the entry is a known issue
in 2026.2's notes.

First step: the probe of R3-F1, made a test.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).
