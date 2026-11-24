028-46. Change: DagTester's deletes at node size 62, joins by height
====================================================================

Status: done. Kind: Change. Frans: none.
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


Result
------

Done on 2026-11-24 by an agent of lead-1124, in test code and one
counter: PE's writes are unchanged.

* The counter: `Dag.statJoinsByHeight`, element i the joins of children
  at height i (0 for leaves), the last element for its height or more;
  `PeWriter.joinAt` counts each join there as well as in `statJoins`.
* Part (4)'s cases as they were, the checked transaction's joins at
  heights 0, 1 and 2 (none higher), for keep 2, 3 and B:
  * 8: 12/9/2, 11/10/2, 6/8/2: joins at height two in each case.
  * 14: 16/8/1, 24/10/2, 12/12/2: joins at height two in each case.
  * 30: 30/0/0, 40/3/0, 28/4/0: none at height two. The new assertion
    fails there: `b 30, keep 2: a join at height two or more, expected
    true, but was false`.
  * 62, the same cases (6 B^2 keys thinned to every third key), a trial:
    68/0/0, 92/3/0, 60/4/0: none. Their thinning joins too (257 joins at
    30), before the checked transaction.
* The cases now: at 8 and 14 as they were; at 30 and 62, cap^2 x 2 (m +
  2) keys (4,500 at 30, 34,596 at 62): their 2 (m + 2) nodes at height
  one, more than h, are cut into two nodes at height two of m + 2
  children each, under a root at height three. The thinning deletes
  every third key, so the leaves keep about B / 3 >= m keys and it joins
  nothing (0 joins at 30 and at 62). Joins at heights 0/1/2:
  * 30: 100/6/1, 120/8/1, 49/10/1.
  * 62: 378/12/1, 450/14/1, 185/18/1.
* Each case asserts at least ten joins and at least one join at height
  two or more. The cases depend on the tree's shape: at 30, 5,400 keys
  thinned the same way (nodes at height two of 12 children) gave a join
  at height two only at keep 30; at 62 trials of 6, 12 and 24 B^2 keys
  thinned to every third key gave none.
* Time: the test took 0.6 to 0.8 s before and 1.0 to 1.8 s after, on a
  loaded machine; within a second of before-commit.sh's
  time, so the case at 62 stays in the unit test.
* Texts: the test's Javadoc and part (4)'s comment; 030-26, section 5,
  item 14; 027-08, section 4.2. 030-38 unchanged.


Log
---

2026-11-24. Registered by an agent of lead-1124, from 030-39, F8
(Frans, 2026-11-24, 006-33, point 3).

2026-11-24. In progress: taken by an agent of lead-1124.

2026-11-24. Done (lead-1124): PE counts its joins by the children's
height (`Dag.statJoinsByHeight`); part (4) at 8, 14, 30 and 62 asserts a
join at height two or more in each case; the cases as they were reached
one at 8 and 14, not at 30, where the test failed; new cases at 30 and
62. Gate: BEFORE COMMIT OK.
