015-45. Fix: cryptoKey has equals() and no hashCode()
=====================================================

Status: done. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: review S1's finding S1-F6 (items/016-release-2026-2/06-reviews/S1.md,
section S1-F6: where, intended, actual, effect, a proposed fix).

Evidence: its test in `PubTesterS1` (06-reviews/S1/S1-tests.diff) fails on
`e427a4c`; rerun by the coordinator, 21:26 (17 of 20 fail, as the report
says). The test's premise against the Javadoc is the review's; no second
agent has checked it.

Done when: the test passes on `main` after the fix and `before-commit.sh`.

First step: the test of S1-F6, in a tester of the area.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).
2026-11-05. In progress: taken by session bergdb-e8 (its agent, in a clone).

2026-11-05. Done by session bergdb-e8's agent. Verified: `CryptoKey.equals` compares
`serialize()`, and `hashCode` was `Object`'s, by identity, against `Object.hashCode()`'s
contract.

* Test: `CryptoKey.testHashCode`: a key and one parsed from its `serialize()` are
  equal, have equal hash codes, and a `HashSet` finds one by the other; before the fix:
  "the hash codes of equal keys, expected 1734853116, got 703504298".
* Fix: `CryptoKey.hashCode()` returns `serialize().hashCode()`, consistent with
  `equals` (S1-F6's first fix), with Javadoc.
* 010-01: a method that `Object` has, overridden; no change of behaviour of the
  database (P1 to P12 not touched).
* Gate: `before-commit.sh`: `BEFORE COMMIT OK (104 s)`, unit 1154, f 81.
