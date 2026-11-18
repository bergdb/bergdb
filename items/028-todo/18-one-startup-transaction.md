028-18. Change: one startup transaction, the startup distance in the primordial record
=======================================================================================

Status: open. Kind: Change. Frans: decided (2026-11-18, 21:37).
Created 2026-11-18 by Frans Lundberg.

Frans, 2026-11-18, 21:30, on 028-15's creation in two records: ""a new
database is created with two records". Why not combine them into one
transaction. Seem better. Either we have a fully initialized database or
not." 21:37: "Document this work in a todo item. Start it now. One
startup transaction."

What: since 028-15 a new database's creation writes two records: the
primordial record (the empty tree), then the creating start's internal
transaction that puts the startup distance at `/#i/-sd` (028-15, decision
1). The reason was a test tool, not the database: the Lean trace checkers
require record 0 to be the model's empty initial tree. 028-17 then made
the creating start sync its second record, so that a Pub database's
creation is durable when `start()` returns; a crash inside the creating
start can still leave the primordial record alone, and the next start
then writes the startup distance with its own builder's value.

The change: one startup transaction. The primordial record holds the
startup distance's KV, so a creation is one record:

* a crash leaves either no database or a fully initialized one (a torn
  record is dropped whole);
* the path "primordial record alone: write the KV at the next start" goes,
  with its tests, and 028-17's second sync;
* a new database's first transaction is no longer one time unit later.

Done when:

* `java/`: the creation writes the KV in the primordial record; a start
  refuses a stream whose primordial record lacks it (a damaged stream),
  as 028-15 refuses a missing KV; 028-17's extra sync and the
  "primordial record alone" path removed; tests: a creation is one record
  holding the KV, a crash during creation leaves no database or a whole
  one, a change of the startup distance later, restarts.
* The trace export and the Lean checkers (`lean/`'s `tracecheck` and
  `treecheck`, `lean/contract/`'s `contractcheck` and `bridgecheck`)
  accept a record 0 that holds that KV, as a transaction from the empty
  tree. **If a pinned statement of `lean/contract/` must change** (such as
  the history's initial state), the agent stops before changing it and
  writes the proposed change here for Frans (statements change only on
  his word, 030's rules).
* 027-03 (sections 3, 6, 14.2, 15), 027-02 (record 0), 027-11, 028-15 and
  028-17 follow the code; `releases/next.md` if users see a change.
* Gates: `java/before-commit.sh`, `java/stress/core-build.sh unit f`,
  `java/stress/kill-restart.sh 1000` with seeds 20261118, 20261117 and
  20261119, `java/stress/level1.sh` to `level4.sh` full, and
  `lean/contract/gate.sh` (and `pin.sh` if pins move).

Sources: 028-15 (decision 1), 028-17, 027-03 (sections 6, 14.2, 15),
027-02.


Log
===

2026-11-18. Registered by coord-1118 at Frans's word (21:37); started the
same evening by an agent of coord-1118.
