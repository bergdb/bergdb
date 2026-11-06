015-61. Fix: a deletion job that stop() or close() ends early reports "Done! Deleted"
=====================================================================================

Status: done. Kind: Fix. Created 2026-11-04 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: review R8's finding R8-F6 (items/016-release-2026-2/06-reviews/R8.md,
section R8-F6: where, intended, actual, effect, a proposed fix), shown by a
test or probe in 06-reviews/R8/. In 2026.1: yes (the same catch clauses and note; line 321 there).

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: verify it (016-06, section 2.6), then the probe made a test.


Log
---

2026-11-04. Registered by the coordinator of release 2026.2 (016-02).

2026-11-06. Done in 019-40 (its C5, review R6 of 006-13, the same fault
after a failure), by coord-1106's agent i40: a done flag after the
job's last sync; an ended job without it says "Stopped". Test
`PubTesterIndexJobs.testDeletionEndedByCloseIsStopped`, R8's probe,
fails before the fix.
