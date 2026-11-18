028-17. Fix: a crash after a new database's start left the primordial record alone
=================================================================================

Status: done. Kind: Fix. Frans: none.
Created 2026-11-18 by Frans Lundberg.

What: `java/night.sh` on `main` 1b1001ee (run 2026-11-18-1239), step 10,
`java/stress/kill-restart.sh 1000`, seed 20261118, failed in its 14th
database:

    KILL RESTART FAILED: FAIL java.lang.AssertionError: run 1, thread 0: its stamp at
    the start's time 17950111260150000 is null, but the journal has its transactions
    committed up to 7 by then (at 17950111259260001), the last committed one at
    17950111259260001, and none in flight: a committed transaction lost, or one there
    that was not committed by then; seed 20261118, database 14 (seed
    8330507075717304468; retain forever, startup distance default, cache default),
    run 2, kill in phase running + 608 ms

Why: a committed transaction lost would be a durability bug. The night
before (2026-11-16, seed 20261116) passed; 028-15 had landed in between.

Frans: none.

Done when: the cause is known; a fix in BergDB or in the harness, with a
test that fails before it; `java/before-commit.sh` BEFORE COMMIT OK,
`kill-restart.sh 1000` with seed 20261118 and two others KILL RESTART OK,
`level1.sh` and `level2.sh` full.

First step: replay the kept database and journal.


Findings
--------

**Not a lost durable transaction; a creation that was not durable.** No
transaction that a sync returned for was lost. The kept database
(`db14`) is 272 bytes: the first meta block and the primordial record,
`Db.CREATION_LENGTH`, and nothing else. Its journal: run 1 created the
database, committed 7 transactions in thread 0 within 250 ms, made no
sync, and was killed 608 ms into its schedule, before the write buffer's
first write; run 2 started on it and failed its check.

* **The harness's check.** T, the start's time, is
  `lookupTime(Long.MAX_VALUE)` in `DatabaseImp.testHookAfterStart`, the
  time of the stream's last record once the Core's start returned. Every
  transaction of the killed run with a time at or before T must be there,
  and those after T may be lost unless a sync covered them. The harness
  assumes that a start writes no record of its own into a database that
  holds data (it writes the creation only).
* **What 028-15 changed.** A start that finds the primordial record alone
  writes the creation's second record, an internal transaction that puts
  the startup distance at `/#i/-sd` (`Db.putStartupDistanceKv`), at its
  own time. The creating start made the primordial record durable before
  `created.txt` (015-01, `Db.syncCreation`) but not the second record,
  which waited in the write buffer like any commit. So a kill after the
  start returned and before the buffer's first write or a sync left the
  primordial record alone, beside `created.txt` (028-15 assumed that only
  "a crash between them", inside the creating start, leaves it). The next
  start, finding the primordial record alone, wrote the KV at its own
  time: T became the restart's time, later than the times of the
  transactions the crash lost, and the check failed. Before 028-15 the
  same stream gave T = the primordial record's time, and the lost
  transactions were after T, as unsynced ones may be.
* **The fault is BergDB's**, small: after 028-15 a new Pub database's
  creation was not durable when `start()` returned. Two effects: (1) a
  crash before the first write lost the creator's startup distance, and
  the next start put its own builder's (the test below: 2,000,000 instead
  of the creator's 5,000,000); (2) that start's record took a time after
  the lost transactions', so the database's history gained a record at
  the restart's time in a database that already held lost commits, and
  the start's time no longer separated the kept transactions from the
  lost ones. No committed data that was durable was lost: the 7
  transactions were never synced, and their loss is allowed (Database's
  Javadoc on sync()).
* **The harness was right** to fail: its rule, "a start writes nothing
  in a database that holds data", is what the creation's durability gave
  before 028-15, and what the fix gives back.

Reproduction:

* The kept database and journal (copied from the night run's tree), the
  journal without run 2's two lines, and the harness's child on it with
  database 14's seed, run 2, settings 0 0 0: the same failure on `main`
  (990212fc), every time.
* A probe, the harness's parent with every second kill aimed at
  "running" within 300 ms (`-Dkillrestart.phase=running
  -Dkillrestart.delay=300`), 200 kills, 2 per database, seed 20261118:
  on `main` it failed in database 56 (the same message, run 2 on a
  272-byte stream); on 31f8f08d, `1b1001ee^1`, the commit before
  028-15's merge, KILL RESTART OK (100 databases).

Bisection: 31f8f08d passes the probe and the new test, `main` fails
both. 028-15 is the cause.


What was done
-------------

* `Db.startInner`: when the start writes the creation's second record
  (the primordial record alone: a creation, or a crash inside the
  creating start), and the creation is synced (`created.txt`, the Pub
  API; `DbBuilder.createdTxt`), the start syncs it before it returns
  (`syncCreation(x.endOfLastTrans)`, rule D1, as the primordial record's
  sync). A Pub database's creation is then durable, both records, when
  `start()` returns, and only a crash inside the creating start leaves
  the primordial record alone; the next start then completes it, as
  028-15 said, with no user transaction before it. Without `created.txt`
  (the Core API alone) nothing changes: that creation was never synced.
  The cost: one more sync at a creation.
* `Db.syncCreation` takes the length to sync.
* 027-03, section 14.2 (step 8), and 027-11's start say so.
* The test: `DbTesterStream.testCreationDurableWhenStartReturns`, a
  unit test. It creates a database on files with `created.txt` and a
  startup distance of 5,000,000, commits a transaction without a sync,
  copies the files while the database runs (as a kill of the process
  leaves them), and starts the copy with a builder's startup distance of
  2,000,000: the copy must have the creator's 5,000,000, and if the
  transaction is not there, a start time before its time. Before the fix
  it fails ("the creator's startup distance, expected 5000000, got
  2000000"), every time; it passes on 31f8f08d and with the fix.

The harness is unchanged.


Gates
-----

At `9f91c5df` on the branch `028-17-kill-restart` (from `main` 990212fc,
which had not moved by the end), 2026-11-18, 15:40 to 16:08, with
night.sh running on `main` part of the time:

* `java/before-commit.sh`: BEFORE COMMIT OK (80 s).
* `java/stress/kill-restart.sh 1000 20261118` (the failing seed): KILL
  RESTART OK, 1000 kills and 54 exits in 1658 s.
* `kill-restart.sh 1000 20261117`: KILL RESTART OK, 1000 kills and 53
  exits in 1621 s.
* `kill-restart.sh 1000 20261119`: KILL RESTART OK, 1000 kills and 50
  exits in 1742 s.
* The probe above (200 kills aimed at "running", seed 20261118): KILL
  RESTART OK, 100 databases (it failed in database 56 on `main`).
* `java/stress/level1.sh` full: LEVEL 1 OK.
* `java/stress/level2.sh` full: LEVEL 2 OK.


State
-----

Done and gated on the branch `028-17-kill-restart`, not merged, not
pushed. For Frans: none needed; the fix gives back what 028-15 took (a
Pub database's creation durable when `start()` returns), at the cost
of one more sync at a creation.


Log
---

2026-11-18. Registered and taken by an agent of coord-1118 (in progress),
in a clone on the branch `028-17-kill-restart`.

2026-11-18. Done: the creating start syncs its record of the startup
distance when the creation is synced; a unit test; BEFORE COMMIT OK,
KILL RESTART OK with three seeds, LEVEL 1 and 2 OK; gated at 9f91c5df,
by an agent of coord-1118 (Claude, Opus 5.5).
