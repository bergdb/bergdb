028-46. Change: DagTester's deletes at node size 62, joins by height
====================================================================

Status: open. Kind: Change. Frans: none.
Created 2026-11-24 by Frans Lundberg.

What: `DagTester.testDirtyNodeBoundOfPe`
(`java/src/bergdb/dag/DagTester.java`; 028-21), part (4), deletes most
keys under several inner nodes of trees thinned towards m, at node sizes
8, 14 and 30, and asserts at least ten joins (`Dag.statJoins`). Node size
62 is not among them (part (3), the random histories, runs at 62), and
the test counts the joins, not the heights at which they happen. The
change: part (4) at 62 too, the joins counted by height, and at each node
size an assertion of joins of inner nodes at height two or more: in
`PeWriter.joinAt`, a join whose children are at height `ht` of two or
more.

Why: the dirty-node bound is proved for joins of leaves and of the inner
nodes just above them (`Contract.PE.NoHigherJoins`); for transactions
that join inner nodes at height two or more it is tested, not proved, by
C-T8 and this unit test, and no check says that they reach such joins
(030-38, G10; 030-26, section 5, item 14). 030-39, finding F8; Frans
registered it on 2026-11-24 (006-33, point 3).

Frans: none.

Done when:

* PE counts its joins by the children's height, beside `Dag.statJoins`
  (a counter for tests and measurements, as the others: no change of
  what PE writes).
* Part (4) runs at node sizes 8, 14, 30 and 62; at each it asserts, as
  well as its ten joins, at least one join at height two or more. At 62
  (m = 16) a tree needs a root at height three or more for such a join.
* The new assertion run on part (4)'s cases as they were: the entry
  records at which node sizes they reached joins at height two or more,
  and the test fails at a size where they did not.
* `java/before-commit.sh` BEFORE COMMIT OK, within a few seconds of its
  time before; if the case at 62 needs more, the entry says how long and
  where it runs instead (a script in `java/stress/` and a step of
  `java/night.sh`).
* The texts: the test's Javadoc; 030-26, section 5, item 14 and 027-08,
  section 4.2 (the node sizes, and that the joins' heights are
  asserted). 030-38, the guarantees of release 2026.6, stays as it is.

First step: count the joins by `ht` in `PeWriter.joinAt` and run part
(4) as it is, at 8, 14 and 30, to see the heights of its joins; then
find the smallest tree at 62 that gives a join at height two or more.


Log
---

2026-11-24. Registered by an agent of lead-1124, from 030-39, F8
(Frans, 2026-11-24, 006-33, point 3).
