015-47. Fix: a byte[] value is shared with the caller: a change of the array changes the value in memory
========================================================================================================

Status: open. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: review S1's finding S1-F8 (items/016-release-2026-2/06-reviews/S1.md,
section S1-F8: where, intended, actual, effect, a proposed fix).

Evidence: its test in `PubTesterS1` (06-reviews/S1/S1-tests.diff) fails on
`e427a4c`; rerun by the coordinator, 21:26 (17 of 20 fail, as the report
says). The test's premise against the Javadoc is the review's; no second
agent has checked it.

Done when: the test passes on `main` after the fix and `before-commit.sh`.

First step: the test of S1-F8, in a tester of the area.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).
