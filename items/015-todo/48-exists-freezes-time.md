015-48. Fix: freezeLookupTime(), then exists(): the frozen time is the read before, or -1
=========================================================================================

Status: done. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: review S1's finding S1-F9 (items/016-release-2026-2/06-reviews/S1.md,
section S1-F9: where, intended, actual, effect, a proposed fix).

Evidence: its test in `PubTesterS1` (06-reviews/S1/S1-tests.diff) fails on
`0b739f3`; rerun by the coordinator, 21:26 (17 of 20 fail, as the report
says). The test's premise against the Javadoc is the review's; no second
agent has checked it.

Done when: the test passes on `main` after the fix and `before-commit.sh`.

First step: the test of S1-F9, in a tester of the area.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-05. In progress: session bergdb-e8's agent verifies and fixes it, with
015-42, 48, 59 and 62 as one group.

2026-11-05. Done by session bergdb-e8's agent. Verified:
`ConnectionImp.getBytesAtLookupTime` (`exists()`; `IndexManager` and
`UseIndexBuilderImp` too) set the frozen time from the `GetData` before its
read, so from the read before, or -1 if there was none, where
`getInternal` sets it after its own read.

* Test (`PubTester`, unit): `testFreezeThenExists`, S1-F9's, and a second
  case with a read before the freeze (the frozen time must be the
  `exists()`'s, the latest, not the earlier read's). Before the fix:
  `LookupTimeNotAvailableException: Cannot lookup at time -1 ...` from the
  `get()` after the `exists()`.
* Fix: `getBytesAtLookupTime` sets the frozen time after its read, as
  `getInternal` does. No Javadoc changes: `freezeLookupTime()`'s already
  says it.
* Checked against 010-01's P1 to P12: no new work, wait, setting, public
  method or global state; the Core Layer and the stream are unchanged.
* A line in `releases/next.md` (Reliability).
* Gate, with 015-42, 48, 59 and 62: `before-commit.sh`: `BEFORE COMMIT OK
  (103 s)`, unit 1155, f 81.
