015-59. Fix: connection.getLookupTime() of a new connection throws IllegalArgumentException
===========================================================================================

Status: done. Kind: Fix. Created 2026-11-04 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: review R8's finding R8-F4 (items/016-release-2026-2/06-reviews/R8.md,
section R8-F4: where, intended, actual, effect, a proposed fix), shown by a
test or probe in 06-reviews/R8/. In 2026.1: yes (`ConnectionImp.java` lines 47 and 70 there).

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: verify it (016-06, section 2.6), then the probe made a test.


Log
---

2026-11-04. Registered by the coordinator of release 2026.2 (016-02).

2026-11-05. In progress: session bergdb-e8's agent verifies and fixes it, with
015-42, 48, 59 and 62 as one group.

2026-11-05. Done by session bergdb-e8's agent. Verified: `ConnectionImp`'s
constructor set `lookupTime = Long.MAX_VALUE`, above `Time`'s range, and
`getLookupTime()` threw `IllegalArgumentException` on a connection from
`newConnection()` (and the internal ones); `connection()`'s initializer
sets `Time.MAX`, which `Database.connection()`'s Javadoc called
"Long.MAX_VALUE".

* Test (`PubTester`, unit): `testNewConnectionLookupTime`: `Time.MAX` from
  `newConnection()` and `connection()`, and a read. Before the fix:
  "IllegalArgumentException: Time ouf of range, units:
  9223372036854775807."
* Fix: the constructor sets `Time.MAX.units()`. The reads are the same
  (`DbClock.lookupTime` takes the last transaction's time for both values).
  Javadoc: `Database.connection()` says that each call sets the lookup time
  to `Time.MAX`, and `newConnection()` that its connection has `Time.MAX`.
* Checked against 010-01's P1 to P12: no new work, wait, setting, public
  method or global state; the Core Layer and the stream are unchanged.
* A line in `releases/next.md` (Reliability).
* Gate, with 015-42, 48, 59 and 62: `before-commit.sh`: `BEFORE COMMIT OK
  (103 s)`, unit 1155, f 81.
