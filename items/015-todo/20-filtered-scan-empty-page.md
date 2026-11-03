015-20. Fix: a filtered scan takes an empty page for the end of its range
=========================================================================

Status: open. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

For 2026.2: a wrong answer in normal use (016-06, section 6).

What: A typed primary scan (`usePrimary`) silently leaves out every later object when one page of about 100 entries holds no object (100 or more other entries in the directory). A wrong answer, through the Pub API in normal use.

Source: review R3, R3-F12 (016-06/R3, items/016-release-2026-2/07-concurrency/r3.md),
confirmed by verify-1 (items/016-release-2026-2/06-reviews/verify-1.md,
section R3-F12), with its probe and the reach.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`; or the entry is a known issue
in 2026.2's notes.

First step: the probe of R3-F12, made a test.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).
