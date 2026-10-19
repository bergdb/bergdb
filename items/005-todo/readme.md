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
| [005-02](02-fix-m46-ordinal-bound.md) | Fix | M46: the top node ordinal bound, 2^30 − 1 over a database's life (item 002) | open |
| [005-03](03-sweep-cost.md) | Investigate | The sweep's cost under read churn (item 001, finding 10) | open |
| [005-04](04-a6-failures.md) | Decide | A6 fails in 5 Java transactions: is anything to be done? | open |
| [005-05](05-bergdb-future.md) | Decide | What to do with BergDB: publish it, when, money, paid work | open |
| [005-06](06-publication-literature.md) | Investigate | The literature and the options for a publication | open |
| [005-07](07-transaction-synchronization.md) | Investigate | Synchronization of transactions: how it is today, how it may need to change | open |

Status values: open, in progress, done, dropped, moved (to an item of its
own). Kinds: Fix (a known fault), Investigate (find out, then propose),
Decide (a question for Frans, prepared by an investigation).

Order, as proposed: 005-01 and 005-02 together (both change
`Db.executeInner`, and they are the only known faults); 005-04 is small and
can go any time; 005-03 after 005-01 and 005-02, since it changes the same
part of Java; 005-05 and 005-06 beside the rest, as they are mostly reading
and thinking, and 005-06 feeds 005-05. 005-07 is best before or with 005-01
(where a transaction's go point is) and before 005-03's fix.


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


Log
===

2026-10-19. Created the item, at Frans's request, with subitems 01 to 06.
Defined, not started.

2026-10-19. Added 005-07, synchronization of transactions, at Frans's
request, with the design notes found in F1-007.
