015-42. Fix: an rw() on a connection changes its frozen lookup time
===================================================================

Status: done. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: review S1's finding S1-F3 (items/016-release-2026-2/06-reviews/S1.md,
section S1-F3: where, intended, actual, effect, a proposed fix).

Evidence: its test in `PubTesterS1` (06-reviews/S1/S1-tests.diff) fails on
`e427a4c`; rerun by the coordinator, 21:26 (17 of 20 fail, as the report
says). The test's premise against the Javadoc is the review's; no second
agent has checked it.

Done when: the test passes on `main` after the fix and `before-commit.sh`.

First step: the test of S1-F3, in a tester of the area.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-05. In progress: session bergdb-e8's agent verifies and fixes it, with
015-42, 48, 59 and 62 as one group.

2026-11-05. Done by session bergdb-e8's agent. Verified: an rw-transaction's
reads (`RwEnvironmentImp.get` and `getInternal`) went through
`ConnectionImp.getInternal` with the connection's `GetData`; after
`freezeLookupTime()` the first read, at `Long.MAX_VALUE`, set the frozen
time to the latest, and `transactionInfo()` then described the
transaction's last read. A put of an object in a directory with an index
did the same (`indexEntries`' read of the previous value).

* Tests (`PubTester`, unit): `testRwKeepsFrozenLookupTime`,
  `testObjectPutKeepsFrozenLookupTime` and `testRwKeepsTransactionInfo`,
  S1-F3's. Before the fix: "frozen after rw, expected '1', got '2'.",
  "frozen after an object put, expected '1', got '2'." and "after rw,
  expected 17938738170400001, got 17938738170400002.".
* Fix: an `RwEnvironmentImp` reads with a `GetData` of its own, made at its
  first read (`readData()`), through the new package-private
  `ConnectionImp.getInTransaction`, which touches no state of the
  connection; the transaction's read time is that `GetData`'s actual lookup
  time. Comments in both classes say why.
* Checked against 010-01's P1 to P12: no new work, wait, setting, public
  method or global state; the Core Layer and the stream are unchanged.
* A line in `releases/next.md` (Reliability).
* Gate, with 015-42, 48, 59 and 62: `before-commit.sh`: `BEFORE COMMIT OK
  (103 s)`, unit 1155, f 81.
