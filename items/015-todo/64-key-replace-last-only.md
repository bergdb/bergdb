015-64. Fix: key replace replaces only the last "${transactionTime}" of a key
=============================================================================

Status: done. Kind: Fix. Created 2026-11-04 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: review R8's finding R8-F9 (items/016-release-2026-2/06-reviews/R8.md,
section R8-F9: where, intended, actual, effect, a proposed fix), shown by a
test or probe in 06-reviews/R8/. In 2026.1: yes (`RwEnvironmentImp.java` lines 481 and 482 there, the same `break`).

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: verify it (016-06, section 2.6), then the probe made a test.


Log
---

2026-11-04. Registered by the coordinator of release 2026.2 (016-02).
2026-11-05. In progress: taken by session bergdb-e8 (its agent, in a clone).

2026-11-05. Done by session bergdb-e8's agent. Verified: `replaceTransformation.transform`
in `RwEnvironmentImp` searched from the end of the key and stopped at the first match, so
only the last "${transactionTime}" was replaced, against
`Connection.setEnableKeyReplace()`'s Javadoc ("occurrences ... will be replaced"). The
code was changed, not the Javadoc: the Javadoc is the Pub API's promise, and a key with
the literal "${transactionTime}" left in it serves no use (every such put writes into
one directory).

* Test: `PubTester.testKeyReplaceEveryOccurrence`: a put at
  `/a/${transactionTime}/b/${transactionTime}${transactionTime}.txt` with key replace
  on; the value is at the key with all three replaced, and not at a key with only the
  last one or two replaced. Before the fix: "every occurrence replaced, expected 'v',
  got 'null'".
* Fix: the search goes on after a match, at the position one occurrence before it
  (occurrences cannot overlap, and the time's digits cannot form a new one).
* 010-01: no new setting or method. Which bytes a workload writes changes only for a
  key with two or more occurrences, which now gets the documented key; the format is
  unchanged, and StreamDigest's workloads use the Core API, so its digests are
  unchanged (P2; 018-01, section 2). A line in `releases/next.md`.
* Gate: `before-commit.sh`: `BEFORE COMMIT OK (104 s)`, unit 1154, f 81.
