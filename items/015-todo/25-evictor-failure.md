015-25. Fix: an exception in the evictor strands its requests on a dead worker
==============================================================================

Status: open. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

For 2026.2 if it fits (new in this release; internal trigger only).

What: An exception or Error in an eviction batch ends the evictor thread without failing the database; reads go on, nothing evicts any more (memory grows past the budget; `setCacheSizeInMb` has no effect), and loads park up to 2 ms each. New in 2026.2 (the evictor thread, 009).

Source: review R3, R3-F3 (016-06/R3, items/016-release-2026-2/07-concurrency/r3.md),
confirmed by verify-1 (items/016-release-2026-2/06-reviews/verify-1.md,
section R3-F3), with its probe and the reach.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`; or the entry is a known issue
in 2026.2's notes.

First step: the probe of R3-F3, made a test.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).
