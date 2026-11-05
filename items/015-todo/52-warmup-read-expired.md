015-52. Fix: `execute()` can be refused with `LookupTimeNotAvailableException`, which neither its Javadoc nor docs/levels.md lists
==================================================================================================================================

Status: done 2026-11-05, night 006-12. Kind: Fix. Created 2026-11-03 by Frans Lundberg.

After release 2026.2 (a known issue of it); likely new in 2026.2 (2026.1 unknown).

What: review R7's finding R7-F3 (items/016-release-2026-2/06-reviews/R7.md,
section R7-F3: where, intended, actual, effect, a proposed fix), shown by a
probe in 06-reviews/R7/. No second agent has checked it yet.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: verify it (016-06, section 2.6), then the probe made a test.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-05. Done in the night 006-12 (W1, clone `g3a`), by R7's first proposal.
Verified with R7's probe as a test: `Db.warmup` reads the transaction's keys before
the write lock at the latest lookup time when it starts; a read held on the storage
while other writers commit and a cut overtakes that time threw
`LookupTimeNotAvailableException` out of `execute()`, and the transaction was not
run.

* Test: `ReclaimReaderTester.testWarmupReadOvertakenByCut` (f-test, 0.1 s), the probe
  with a stream (`HoldStream`) that makes the writer thread's first read wait: a
  database with `/old/x` behind its startup pos is restarted on it, the writer's
  warmup read of `/old/x` is held, other puts make a cut past the held position and
  the warmup's time, then the read goes on. Before the fix: "the transaction threw
  bergdb.pub.util.LookupTimeNotAvailableException: The lookup at time 160000001 ...
  expired while it ran"; after it, the transaction commits. Five runs in a row pass.
* Fix: `warmup` catches `LookupTimeNotAvailableException` and ends: the warmup only
  loads nodes, and the transaction reads again under the lock at the latest time.
  Other exceptions of the read (a storage failure, which fails the database) are
  thrown as before. `warmup`'s Javadoc says so. `execute()`'s Javadoc and
  docs/levels.md needed no change: the exception no longer comes out.
* The stream's bytes (P2): unchanged; the warmup writes nothing, and a single writer
  never meets the case. 010-01: no departure.
* A line in `releases/next.md` (Reliability).
