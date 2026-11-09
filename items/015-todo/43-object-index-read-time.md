015-43. Fix: index work reads the indexes before the read time: a new or deleted index is missed
================================================================================================

Status: done 2026-11-09. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: review S1's finding S1-F4 (items/016-release-2026-2/06-reviews/S1.md,
section S1-F4: where, intended, actual, effect, a proposed fix).

Evidence: its test in `PubTesterS1` (06-reviews/S1/S1-tests.diff) fails on
`e427a4c`; rerun by the coordinator, 21:26 (17 of 20 fail, as the report
says). The test's premise against the Javadoc is the review's; no second
agent has checked it.

Done when: the test passes on `main` after the fix and `before-commit.sh`.

First step: the test of S1-F4, in a tester of the area.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-09. Done by release 2026.4's indexes (020-10), in night 006-15: a write fixes its read time before it reads the index set, which it reads under the index manager's lock (020-10, 5.1 and 5.2); 249b684 (020-10, I1). The test: PubTesterIndexRaces.testRacesCreate, testRacesActivate and testRacesDelete (36 forced orders, each a write at a point of a definition's change), in `before-commit.sh`, passing on `main` at `fd6dd09` (020-11). Status: done.
