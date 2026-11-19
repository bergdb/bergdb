028-25. Decide: one order of the marks for both ways of PE
=========================================================

Status: open. Kind: Decide. Frans: decision.
Created 2026-11-19 by Frans Lundberg.

What: the writer PE reports the key nodes of a transaction to Db, which
marks them in the order reported and makes them dirty in that order
(`Db.markAtEndOfOp`, `endOfOp`; 027-08, sections 1.9 and 1.10). The two
ways of `PeWriter` report in different orders:

* the plan's emit (`PeWriter.emit`) reports bottom-up: a node kept on the
  path (`keyNodeOnPath`) after the nodes below it, a node changed or made
  after its children;
* the short way of a transaction of at most 8 operations
  (`PeWriter.shortWay`) reports each segment leaf changed first, in the
  order of its first operation, and then, for each operation that wrote,
  the nodes of its path top-down.

So for a path with two or more inner nodes below the space root that are
not dirty yet, the transaction's got-dirty list has them in one order if
Java took the short way and in the other if it took the plan. The trees,
the ids and the set D are the same either way (the tree checker compares
both ways with the model on every traced transaction); the order is not
checked by anything: the tree checker's C-T9 compares gd as a set
(`lean/Check/Steps.lean`, `diffRecord`, `sameList`).

Why: the got-dirty list's order is in the stream: a record's got-dirty
pairs, and the order in which later takes write the nodes, so their
positions (027-03, section 8.4, whose rules are still to be written). Java
is deterministic, so the stream is too (P2), and a start rebuilds D from
the stored ids, not from the marks (027-11, 1.7), so nothing is wrong
today. But the record is not a function of PE's plan alone: 027-08 must
describe both orders, and a second implementation (the C clone, 012) that
wants Java's bytes must implement the short way's order as well as the
plan's, though the short way is only a speed-up. Found while writing
027-08 (its section 1.10).

Frans: decision, between:

* **A. Keep both orders.** 027-08 describes both (done, sections 1.9
  and 1.10). Nothing changes in the code or the stream. A second
  implementation copies the short way, or accepts other bytes.
* **B. One order: the short way reports as emit does.** In
  `PeWriter.shortWay`, report the leaves and the nodes on the paths in
  emit's order (post-order: for each segment tree, its nodes after the
  nodes below them, the trees after the first in key order before the
  space root's tree), so that the marks, and so the got-dirty list, are
  those of the plan whichever way Java takes. A small change of
  `shortWay`'s last loop (a walk of the paths' nodes deepest first), and
  of 027-08's 1.10. The stream's bytes of new databases change (the order
  of got-dirty pairs and of nodes taken), not the format's meaning: a
  start does not depend on the order, so no new record format is needed.
  A check could then compare Java's gd with the model's as a list (C-T9),
  if the model's marking order is made emit's too.

Recommendation: B, after 2026.6's release work allows (it is small, and
it makes PE's output a function of the plan, so that 027-08 and the
model can state one order); A costs nothing now.

Done when: A: Frans's choice in the log, and 027-08 unchanged. B: the
short way reports in emit's order, a DagTester test that compares the
marks of a transaction taken by the short way with those of the same
transaction forced through the plan (a test hook that turns the short
way off), 027-08 section 1.10 updated, `java/before-commit.sh` BEFORE
COMMIT OK and `level2.sh` LEVEL 2 OK.

First step: for B, a DagTester workload at node size 8 whose tree has
three inner levels in one segment tree, a transaction of one put with
both inner nodes below the space root clean, and the listener's reports
in each way.


Log
---

2026-11-19. Registered by an agent of coord-1118 while writing 027-08
(branch `027-08-writer`; the number given by coord-1118).
