028-21. Investigate: does dirtyNodeBound bound the writer PE?
===========================================================

Status: open. Kind: Investigate. Frans: none.
Created 2026-11-19 by Frans Lundberg.

What: `Dag.dirtyNodeBound` (`java/src/bergdb/dag/Dag.java`, its
Javadoc), the bound on the index nodes that a transaction can make dirty
or create, which `Db.checkDirtyNodes` uses before the go point to refuse a
transaction whose record could pass the record limit (027-03, section
8.3). Its count was argued for the writer of record formats 6 and 7: the
splits' overflows (1 + (k - r - 1) / q a node), the upward unlink, root
collapse, and the merges at a delete, "a merge makes at most two new
nodes", four nodes a level of a delete's path and two levels more. Since
record format 8 the writer is PE (026-25; 027-08), and the Javadoc says:
"the bound is kept as it was, and checked for PE by the tree checker on
every traced transaction (its C-T8 ...) and by DagTester's tests of the
bound. An argument for PE's own counts is not written."

Why: the bound guards R1 (a refused call changes nothing): if it counts
fewer nodes than PE makes dirty, a transaction can pass the check and
make a record above the limit after the go point, which fails the
database. PE's mechanisms differ from those the argument names, and two
of them make more nodes than the old merge did:

* a join (`PeWriter.joinAt`) of a small child with a neighbour of up to
  B - 1 live entries is cut into parts of at most c (`nParts(c, n)`), so
  up to three new nodes at node size 30 (7 + 29 entries, c = 17), not
  two;
* the joined list of two inner children is rebalanced one level down
  before it is decided (`rebalance` called from `joinAt`), so one join
  can join grandchildren too, in any transaction whose changed child has
  fewer than m entries, not only at a delete.

C-T8 passes on every traced transaction of the level scripts (026-25,
section 6), and the bound is generous for a delete (about 30 nodes at node
size 30), so the bound may well hold; but no argument says so, and the
traces may not reach the worst shapes (many deletes that empty
neighbours on several levels in one transaction).

Frans: none.

Done when: either an argument for PE's counts written in the Javadoc of
`Dag.dirtyNodeBound` (each of PE's ways to make a node dirty or new:
appends, a replacement, a cut into parts, a join and its rebalance one
level down, a collapse, a new root, the nodes on the path that
`keyNodeOnPath` marks), with the bound changed if it does not cover them;
or a counterexample, a transaction whose marked key nodes pass the bound,
as a failing test in `DagTester`, and the bound fixed. Either way a test
of the worst shape found (`DagTester`, beside
`testDirtyNodeBoundOfDeletes`), `java/before-commit.sh` BEFORE COMMIT OK
and `level2.sh` (C-T8) LEVEL 2 OK.

First step: a DagTester workload that deletes, in one transaction, most
keys of neighbouring leaves under several inner nodes at node size 8 and
30, so that joins happen on several levels, and compare the key nodes
marked with `dirtyNodeBound` (as C-T8 does); then the argument.

Sources: 026-25 (sections 2 and 5), 027-08, 027-03 section 8.3, 024-11
(CB1, CB2, TU8), 023-07 section 5.4 (K4).


Log
---

2026-11-19. Registered by an agent of coord-1118 while bringing 027 up
to date with PE (branch `027-pe`).
