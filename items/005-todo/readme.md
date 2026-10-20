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
| [005-04](04-a6-failures.md) | Decide | A6 fails in 5 Java transactions: is anything to be done? | done |
| [005-05](05-bergdb-future.md) | Decide | What to do with BergDB: publish it, when, money, paid work | open |
| [005-06](06-publication-literature.md) | Investigate | The literature and the options for a publication | open |
| [005-07](07-transaction-synchronization.md) | Investigate | Synchronization of transactions: how it is today, how it may need to change | open |
| [005-08](08-fix-node-table-tree-bins.md) | Fix | The node table's 256 maps make every bin a tree (`Cache3.mapIndex`): 61 bytes per KV, a slower `set` (006-02) | done |
| [005-09](09-fix-node-table-snapshot-race.md) | Fix | A race between a reader and a sweep lets the node table name a released object (INV-CAN); a unit test fails now and then (005-02) | open |
| [005-10](10-unused-code.md) | Investigate | Unused code in `java/` and `lean/`: find it and propose what to remove; nothing is removed without Frans's approval | in progress |
| [005-11](11-replication.md) | Decide | Replication: study the implementation and its tests; remove it, complete it, or change its design (005-10) | open |
| [005-12](12-transaction-outputs.md) | Investigate | Transaction outputs (`setOutput`, `getOutput`): study them, then test them or remove them (005-10) | open |

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
005-11 and 005-12 can go any time, best before 005-05's decision on
publishing, as both concern the Pub API.


Files
=====

* [01-fix-m49-exception-safety.md](01-fix-m49-exception-safety.md). 005-01,
  fix M49.
* [02-fix-m46-ordinal-bound.md](02-fix-m46-ordinal-bound.md). 005-02, fix
  M46.
* [03-sweep-cost.md](03-sweep-cost.md). 005-03, investigate the sweep's
  cost.
* [04-a6-failures.md](04-a6-failures.md). 005-04, the A6 failures: decide
  whether anything is to be done; done, with its tools and runs in
  [04-a6-failures/](04-a6-failures/).
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
  propose what to remove, for Frans to approve; the proposal, with its
  tables, plan, tools and runs, in [10-unused-code/](10-unused-code/), and
  the removal as Frans decided it in
  [10-unused-code/applied/](10-unused-code/applied/).
* [11-replication.md](11-replication.md). 005-11, replication: the
  decision material for Frans.
* [12-transaction-outputs.md](12-transaction-outputs.md). 005-12,
  transaction outputs: study, then test or remove.


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

2026-10-19. 005-04 done, at Frans's request ("Do as proposed"), by Claude
(Opus 5.5, Claude Code): A6 is not a target, the assumption stays A6'. Option
4's look found one kind of A6 failure only, the in-place split of a segment
root made by the same transaction, which keeps A6'; 61 Java-tier failures at
node sizes 8 to 62 are all that kind, and 21 new traces with it pass the
checker, with eviction too. No change to `java/` or `lean/`. Proposed, not
done: TREE, A6' and A-COPY as gate checks, and A6' as the checker's
diagnostic.

2026-10-19. 005-10 in progress, at Frans's request ("Do the 005-10 todo
item"), by Claude (Opus 5.5, Claude Code): the proposal is written, in
10-unused-code/proposal.md. About 11,700 lines can go in recommended groups
(A1 to F1); a patch with all of them passes the build, the unit and
f-tests, the four gates and `lake build` on a clone. Found on the way:
tests that never ran, as their classes are in no pack (one fails today),
and night tests that nothing runs (they pass). Nothing is removed; Frans
decides by ID.

2026-10-20. 005-10: Frans decided ("remove all recommended; C1 keep; C2
keep; C3 keep; D1 keep; D2 keep; D3 keep; E1 keep; G1 remove", and a
script for the night tests). Removed by Claude (Opus 5.5, Claude Code): A1
to A3, B1 to B3, F1 and part of G1, 3,071 lines in 103 files; added
`java/stress/night.sh`. The build, the unit and f-tests, the four gates,
`lake build` and `night.sh` pass on a clone; the change is in the main
tree, for Frans to commit. The rest of G1 waits: the proposal's G1 was
wrong for part of it (code behind those API methods is used), see the
subitem.

2026-10-20. 005-04's two proposals done, at Frans's request ("Yes"), by
Claude (Opus 5.5, Claude Code): TREE, A6' and A-COPY are gate checks, in
`A2A3Check2` (`level2.sh`, step 7) and in the checker's C-A, where A6'
replaces the diagnostic A6; the small and evict sets have a configuration
with A6's kind, whose traces must contain it. The four gates pass, also with
005-10's removal (`c6ca623`). See 005-04, "Follow-up".

2026-10-20. Added 005-11, replication, and 005-12, transaction outputs, at
Frans's request, from 005-10's G1 (the Pub API's methods that nothing in
the repository calls).
