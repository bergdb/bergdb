028-21. Investigate: does dirtyNodeBound bound the writer PE?
===========================================================

Status: done. Kind: Investigate. Frans: none.
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


Finding
-------

The bound did not hold for PE. Two counterexamples, each a transaction of
puts only, whose key nodes made dirty passed `dirtyNodeBound` (each a
failing case of `DagTester.testDirtyNodeBoundOfPe` before the fix):

* **A new segment tree of h + 1 to B - 3 entries.** The count of a new
  tree (`freshTreeBound`) was the old writer's: one node until the
  node overflows, at B - 2 klongs. PE cuts every new list of more than h
  entries into parts of at most the cut size and puts a new root above
  them. At node size 30, 18 keys `/p00005/x00000` to `/x00017` under a
  segment leaf that has no `/p00005`: three key nodes made (two leaves of
  nine and a root), counted as one; the transaction marked 22 key nodes,
  bound 20. At node size 14 from 8 keys (12 marked, bound 10); at 62 a
  random transaction of 385 puts (418, bound 416).
* **A node cut into more parts than its overflows and one.** The count
  of a node that overflows was the old writer's splits, one more node
  each q klongs (10 at node size 30), so a node of 31 entries was counted
  as two new nodes and two klongs in its parent; PE cuts it into
  `cutParts(31)` = 3 parts of at most 15, three entries in the parent.
  The walked node's own count covers the third part, but the parent gets
  one klong a child more than counted: at node size 30, a root of 21
  klongs (18 live, one dead) whose three leaves of 21 klongs (19 live)
  each get 12 new keys has nine klongs for three counted as six, and is
  cut, while the count kept it: 12 key nodes marked, bound 10 (the case
  is built step by step in the test, and checks that PE cut the three
  leaves and the root).

Deletes were not short. PE's joins make more nodes than the old merges
(three at node size 30, 7 + 29 entries), and a join of two inner nodes
rebalances one level down, but a child is joined only if a delete below
it left it under m entries, and a delete's four nodes a level and two
levels more are generous: over about 1,500 transactions of deletes only
on thinned trees (single deletes, most keys of runs, every k-th key) the
bound was at least 5.9 times the nodes marked at node size 30 (6.3 at 62,
7.6 at 14, 9.8 at 8). A put's count is tight: a put's walked nodes are
all marked when PE appends to them, and margin 0 is common.

Why the traces did not show it: C-T8 checks the Lean copy of the same
count, which had the same gaps, and the level scripts' traces rarely put
more than h keys under one new segment in one transaction, or cut three
children of a node at the edge. In `Db` the walk runs only after the
cheap test (three nodes a level a put) fails, for transactions near the
record limit; there a transaction with many such shapes could pass the
check and make a record above the limit after the go point.


The fix
-------

`Dag.dirtyNodeBound` (and its copy in lean/SIS/Tree/Bound.lean, line for
line, which C-T8 uses), conservatively: the bound only grows.

* A node that overflows counts `max(overflows + 1, cutPartsBound(size +
  k))` new nodes, k the klongs counted for it, and its parent in its tree
  gets as many klongs (until now overflows + 1). `cutPartsBound(n)`: one
  if n is at most h, else max(2, ceil(n / (B / 2))), PeWriter.cutParts.
* A root of a tree (the space root, or a node below a segment leaf) that
  overflows counts the new roots above its parts, `rootsAbove(parts)`
  (PeWriter.settleRoot: a new root of the parts, cut again if it holds
  more than h), at least the overflows; the segment leaf above gets the
  overflows and one klongs as before.
* A new segment tree of n entries counts the most of the old count and
  PE's: `cutPartsBound(n)` and the roots above them, exact for PE.
* `Params.nodesALevel` (TP26, the user's limits bound the count), the
  count a level from q, raised for the new count: 8 + (3 q + 4) / (q - 1),
  one more at q = 2 (19 a level at node size 8, 13 at 14, 11 at 30 and
  62, was 14, 9, 8, 8); `ReleaseFits` still holds at every node size (the
  four theorems, by `decide`): at node size 8, 1,998,975,872 bytes of
  the limit's 2,013,265,912.


The argument for PE
-------------------

In `Dag.dirtyNodeBound`'s Javadoc and 027-03, section 8.3. In short: the
nodes PE makes dirty are the nodes of the paths it keeps with a node
written below, or appends to, all walked, and the nodes it makes:

* a node of the paths replaced or cut: every entry it gets is a klong
  counted for it, so the count's overflow test (size + k + 3 > B, or the
  dead klongs above theta) holds whenever PE's decide does not append
  (size, a time klong, the entries and a bitmap above B, or the dead
  klongs above theta); its list has at most size + k entries, so at most
  `cutPartsBound(size + k)` parts, at most two more than the overflows
  (q < B / 2);
* new roots above a cut root: `rootsAbove`;
* a new segment tree: PE's count, exactly;
* joins: every key node but a root holds m or more (V1, C-T6), the parts
  of a cut at least (h + 1) / 2 >= m, so a child is small only with a
  delete below it; a joined group is its small children and at most one
  other node, and as ceil((a + b) / c) <= ceil(a / c) + ceil(b / c) its
  parts are at most one a small child and two more, or the other node's
  own parts: three nodes a level a delete, and three entries and a bitmap
  in the parent, within a delete's four nodes a level and four klongs a
  node. A join one level down replaces a group counted there.
* root collapse and an emptied root make no node but the space root's
  empty leaf, which replaces the walked root.

It is an argument given V1, not a proof. `Db.checkDirtyNodes`'s cheap
test, three nodes a level a put and 20 a delete, is above PE's own count
(a put makes at most two nodes a level and a new root a segment tree), so
it was not changed.


Tests
-----

* `DagTester.testDirtyNodeBoundOfPe` (about 1 s): (1) new segment trees
  of 1 to 2 B + 2 keys at node sizes 8, 14, 30 and 62; (2) the parent
  case at 30; (3) random histories and transactions of runs of puts, new
  keys and deletes at the four sizes; (4) deletes of most keys under
  several inner nodes of trees thinned towards m, with joins (at least 10
  a case) on several levels. Before the fix (1) failed (node size 14,
  8 keys: 12 marked, bound 10) and so did (2) alone (12, bound 10).
* The exploration (a probe outside the repository, against the jar):
  new trees of up to 700 keys, about 3,000 random transactions of puts
  and deletes, 1,200 of deletes only, 600 of runs of new keys into
  appended leaves, at node sizes 6 to 62: no case above the bound after
  the fix; before it, the cases above.


Gates
-----

GATES


State
-----

Done on the branch `028-21-dirty-bound`; nothing left.


Log
---

2026-11-19. Registered by an agent of coord-1118 while bringing 027 up
to date with PE (branch `027-pe`).
