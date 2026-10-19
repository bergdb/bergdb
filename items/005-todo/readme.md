005-todo
========

Created 2026-10-19 by Frans Lundberg. Status: open.

A list of things to do on BergDB: issues to fix, things to investigate,
decisions to make. Each entry is a subitem with its own ID and a short
definition: what, why, the questions, when it is done, the first step. An
entry that grows into real work gets an item of its own, linked from here.


The list
========

| ID | Kind | What | Status |
|---|---|---|---|
| [005-01](01-fix-m49-exception-safety.md) | Fix | M49: a transaction that throws inside `putKvs` is half committed (item 003) | open |
| [005-02](02-fix-m46-ordinal-bound.md) | Fix | M46: the top node ordinal bound, 2^30 − 1 over a database's life (item 002) | done |
| [005-03](03-sweep-cost.md) | Investigate | The sweep's cost under read churn (item 001, finding 10) | open |
| [005-04](04-a6-failures.md) | Decide | A6 fails in 5 Java transactions: is anything to be done? | open |
| [005-05](05-bergdb-future.md) | Decide | What to do with BergDB: publish it, when, money, paid work | open |
| [005-06](06-publication-literature.md) | Investigate | The literature and the options for a publication | open |
| [005-07](07-transaction-synchronization.md) | Investigate | Synchronization of transactions: how it is today, how it may need to change | open |
| [005-08](08-fix-node-table-tree-bins.md) | Fix | The node table's 256 maps make every bin a tree (`Cache3.mapIndex`): 61 bytes per KV, a slower `set` (006-02) | done |
| [005-09](09-fix-node-table-snapshot-race.md) | Fix | A race between a reader and a sweep lets the node table name a released object (INV-CAN); a unit test fails now and then (005-02) | open |
| [005-10](10-unused-code.md) | Investigate | Unused code in `java/` and `lean/`: find it and propose what to remove; nothing is removed without Frans's approval | open |

Status values: open, in progress, done, dropped, moved (to an item of its
own). Kinds: Fix (a known fault), Investigate (find out, then propose),
Decide (a question for Frans, prepared by an investigation).

Order, as proposed: 005-01 and 005-02 together (both change
`Db.executeInner`, and they are the only known faults); 005-04 is small and
can go any time; 005-03 after 005-01 and 005-02, since it changes the same
part of Java; 005-05 and 005-06 beside the rest, as they are mostly reading
and thinking, and 005-06 feeds 005-05. 005-07 is best before or with 005-01
(where a transaction's go point is) and before 005-03's fix. 005-08 is small
and can go any time, best before 005-03, whose sweeps walk the node table.
005-09 is small and can go any time; it can fail a gate until it is fixed.
005-10's proposal can go any time, as it changes nothing; a removal that
Frans approves is best made when no other change to `java/` is under way.


Files
=====

* [01-fix-m49-exception-safety.md](01-fix-m49-exception-safety.md). 005-01,
  fix M49.
* [02-fix-m46-ordinal-bound.md](02-fix-m46-ordinal-bound.md). 005-02, fix
  M46.
* [03-sweep-cost.md](03-sweep-cost.md). 005-03, investigate the sweep's
  cost.
* [04-a6-failures.md](04-a6-failures.md). 005-04, the A6 failures: decide
  whether anything is to be done.
* [05-bergdb-future.md](05-bergdb-future.md). 005-05, what to do with
  BergDB.
* [06-publication-literature.md](06-publication-literature.md). 005-06, the
  literature and the options for a publication.
* [07-transaction-synchronization.md](07-transaction-synchronization.md).
  005-07, synchronization of transactions: today's design, from the code and
  F1-007's notes, and what may need to change.
* [08-fix-node-table-tree-bins.md](08-fix-node-table-tree-bins.md). 005-08,
  fix the node table's tree bins, found and measured in 006-02; done, with
  its runs and tools in
  [08-fix-node-table-tree-bins/](08-fix-node-table-tree-bins/).
* [09-fix-node-table-snapshot-race.md](09-fix-node-table-snapshot-race.md).
  005-09, fix the race that lets the node table name a released object,
  found in 005-02.
* [10-unused-code.md](10-unused-code.md). 005-10, find unused code and
  propose what to remove, for Frans to approve.


Log
===

2026-10-19. Created the item, at Frans's request, with subitems 01 to 06.
Defined, not started.

2026-10-19. Added 005-07, synchronization of transactions, at Frans's
request, with the design notes found in F1-007.

2026-10-19. Added 005-08, the node table's tree bins, at Frans's request,
from 006-02's finding and its experimental patch.

2026-10-19. 005-02 done, at Frans's request ("Fix 005-02"), by Claude (Opus
5.5, Claude Code): the top node ordinal is a `long` below 2^48 without a
format change, and a user transaction is refused before it changes anything
near the end. M46 and item 002 closed. Its outcome is in the subitem.

2026-10-19. 005-08 done, at Frans's request ("Fix bergdb 005-08"), by
Claude (Opus 5.5, Claude Code): `Cache3.mapIndex` by Fibonacci hashing, and
a unit test that the node table's bins stay small; MEM 227 to 191 bytes per
KV, `set` 10 to 13 percent faster, the streams unchanged, the four gates and
the quick performance suite passed. The change in `java/` is left for Frans
to commit. Found on the way, for 005-03: a sweep breaks ties of age by the
node table's order, not by depth (005-08, "The table's order").

2026-10-19. Added 005-09, the race that lets the node table name a released
object, at Frans's request, from 005-02's finding (a unit test that fails now
and then).

2026-10-19. Added 005-10, unused code: find it and propose what to remove,
at Frans's request. For an AI to do; nothing is removed without Frans's
approval.
