015-46. Fix: a String or byte[] at an object key in an indexed directory breaks the index
=========================================================================================

Status: done 2026-11-09. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: review S1's finding S1-F7 (items/016-release-2026-2/06-reviews/S1.md,
section S1-F7: where, intended, actual, effect, a proposed fix).

Evidence: its test in `PubTesterS1` (06-reviews/S1/S1-tests.diff) fails on
`0b739f3`; rerun by the coordinator, 21:26 (17 of 20 fail, as the report
says). The test's premise against the Javadoc is the review's; no second
agent has checked it.

Done when: the test passes on `main` after the fix and `before-commit.sh`.

First step: the test of S1-F7, in a tester of the area.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-09. Done by release 2026.4's indexes (020-10), in night 006-15: every put and delete at an object key keeps the indexes, of any value: a String or a byte[] has no entry, so one put over an object deletes its entries (020-10, 3.3 and 5.1); 4a6deee (020-10, I1). The test: PubTesterIndexRaces.testStringOverObject (a String and a byte[] over an object, in w() and rw(), then a delete), in `before-commit.sh`, passing on `main` at `b768ef0` (020-11). Status: done.
