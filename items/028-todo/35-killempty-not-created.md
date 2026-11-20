028-35. Fix: the user app KillEmpty and a kill during a database's creation
===========================================================================

Status: done. Kind: Fix. Frans: none.
Created 2026-11-20 by Frans Lundberg.

What: in `week.sh short` on 2026-11-20 (030-30's gates), the user app
KillEmpty (`java/stress/apps/b5-kill/KillEmpty.java`) failed its final
check when a kill cut a database's creation: a start of such a directory
throws `DatabaseNotCreatedException`, which KillEmpty does not handle,
where Kill (`a4-kill/Kill.java`) and Buffers (`b3-buffers`) do. A fault
of the app, not of the database, as far as known.

Why: a false failure of week.sh's apps costs a week's result and hides
real ones.

Frans: none.

Done when: KillEmpty treats a database whose creation a kill cut as Kill
does (and checks that the refusal is the expected one); a run that hits
the case, or a test of it; `java/before-commit.sh` BEFORE COMMIT OK; the
apps' kill round OK.

First step: compare KillEmpty's start and final check with Kill.java, line
172.


Findings
--------

**A fault of the app, not of the database.** In 030-30's first `week.sh
short` (run 2026-11-20-1156, `apps-quick-cc`), KillEmpty's final check of
database 3 threw from `b.start()`: "The database was not completely created
... its stream, of length 272, holds the creation's first record and not
its second, the startup distance, and no data" (`Db.refuseIncompleteCreation`).
KillEmpty's child started its database with no handling of
`DatabaseNotCreatedException`; Kill (a4) removes the stream's files and
starts again.

**Two ways to the refused stream, both as the Core is made.** A kill
inside the creating start, and, since the Core API's creating start does
not sync (only a start with `created.txt`, the Pub API, syncs both records,
`Db.startInner`, 028-18), a kill after `start()` returned and before the
writer wrote the second record. The comment in `Db.startInner` says so: "a
crash before the record is durable, leaves the primordial record alone".
A probe that created a Core database on files and halted the JVM at once
after `start()` returned found no stream file at all; under load the
writer had written the first record alone. So a refusal is expected for
a database of which nothing durable was seen, and not after a sync or the
recovery of a transaction, which read both records from the files.

**Not changed here; for the coordinator.** The public Javadoc of
`Db.start()` (its `@throws DatabaseNotCreatedException`) and of
`DatabaseNotCreatedException` speak of a crash while the database was
created; that a Core API creation is durable only at the first sync, so
that a crash after `start()` returned can also give the exception, is said
only in the comment in `Db.startInner`. A candidate todo (Javadoc), not a
fault: the Pub API's start syncs the creation.

**The fix** (`KillEmpty.java`, the app only):

- The child takes the stream's files and their lengths before the start;
  on `DatabaseNotCreatedException` it checks that the refused start
  changed none of them ("the start writes nothing"), prints `NOTCREATED`,
  removes the files and starts again, which creates the database.
- The parent accepts `NOTCREATED`, from a killed child or from the final
  check, only while no child of the database reported a sync ("S i") or
  recovered a transaction ("R n", n >= 0); otherwise it fails ("a start
  refused it as not created after a sync ... or a recovery ..."). It
  counts the cases: "N creations cut and made again" in its OK line.
- A first version accepted the refusal only before any "R" line; two
  parents under load failed it (seeds 61 and 63: "R -1" from the creating
  child, then a refusal), which is the Core's second way above, not a
  fault. Hence the rule by sync and recovery.

**The case shown.**

- A Core database made by the child with no transaction, its stream cut
  to 272 bytes (the primordial record alone, the 030-30 state): the next
  child printed `NOTCREATED`, made the database again, recovered -1 and
  committed 40 transactions; the child after it recovered 39.
- Children at background QoS (`taskpolicy -b`, a slow creation) killed at
  0.4 to 3 s in steps of 0.1 s: 2 of 26 left the stream of 272 bytes; the
  next start printed `NOTCREATED` and recovered -1.
- Six parents (`KillEmpty parent 51..53, 61..63 DIR 120 1 500`, one kill a
  database) beside 12 JVMs of 028-36's probe, at a load of 11 to 38: all
  OK, with 4 creations cut and made again (seeds 51, 62 twice, 63).


Gates
-----

On the branch `028-fx2`, at a load of 5 to 30, with other sessions'
runs:

- `java/before-commit.sh` at 851d2222: BEFORE COMMIT OK (78 s).
- The apps' kill round, `java/stress/apps.sh kill 35` at 851d2222 (Kill
  300 kills, KillEmpty 250, Buffers kill 60, new seeds; 48 minutes): APPS
  OK; KillEmpty "0 creations cut and made again" in this round.


Log
---

2026-11-20. Registered by coord-1120, from 030-30's report.

2026-11-20. Taken by fx2 of coord-1120, on the branch `028-fx2`.

2026-11-20. Done by fx2 of coord-1120 on the branch `028-fx2` (851d2222): a
fault of the app; KillEmpty makes a database whose creation a kill cut
again, as Kill does, and accepts the refusal only while nothing durable of
the database was seen.
