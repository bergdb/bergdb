015-73. Fix: a corrupt startupPos in the last record is accepted, and the transactions before it are lost
=========================================================================================================

Status: open. Kind: Fix. Created 2026-11-04 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too. A fix needs a design choice (a header checksum, a format change, or structural checks as 005-75).

What: review R6's finding R6-F2 (items/016-release-2026-2/06-reviews/R6.md,
section R6-F2: where, intended, actual, effect, a proposed fix), shown by a
test or probe in 06-reviews/R6/. No second agent has checked it yet.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: verify it (016-06, section 2.6), then the probe made a test.


Log
---

2026-11-04. Registered by the coordinator of release 2026.2 (016-02).
