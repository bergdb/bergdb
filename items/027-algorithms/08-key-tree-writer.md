# 027-08. The key tree: the writer

Created 2026-11-13 by Frans Lundberg. Status: stub.

Part 4 of 027's outline (027-04, section 2.3; levels: 0). What a
transaction's operations do to the tree. Since record format 8 (026-25)
the writer is PE, "plan, then emit" (`Dag.putKvs`, `PeWriter`; the Lean
model's `Contract.PE.peTx`, proved in 030-21, and its copy for the tree
checker, lean/SIS/Tree/Pe.lean): from the transaction's whole batch, a
plan decides each touched node's final list (a leaf's operations applied,
empty children dropped, a changed child of fewer than m entries joined
with a neighbour by M1 within c, a root collapsed or raised) and what is
written for it, and emit writes each decided node once: nothing, klongs
appended (a time klong, a bitmap if a compare value left, a key klong for
each entry new or repointed) if they fit and leave at most theta dead
klongs, or new nodes, a list of more than h entries cut into parts of at
most B / 2; BU1 and the bound on key nodes by the live keys;
`dirtyNodeBound`. Until format 8 (release 2026.5's writer): a put and the
five splits, with h; a delete's upward unlink, the take-back, LE-b and
root collapse; the merges of underfull nodes (m and c); rule O at theta.

Not written yet: the outline's order of writing is 027-04, section 5.1.
Each part follows the template of 027-04, section 2.2.

**Until it is written, in brief** (from the code at `b03dcea7`;
`PeWriter`'s class comment and 026-25, sections 2 to 5, have the
details):

* **Who and when.** `Db.putKvs` gives the Dag a transaction's KVs, one a
  key, in strictly increasing key order, after every value
  transformation has run; a start's rerun gives it a record's KVs in
  stored order (027-11, section 1.7). One writer at a time, under the
  write lock; readers read at earlier times without locks.
* **Plan.** One walk from the space root, with a stack of frames, not a
  recursion (a key may have 8,193 segments): an inner node routes its
  operations to its children by their compare values; a segment leaf
  applies its operations by compare value (a put that ends there sets a
  new value node, a delete that finds the key removes the entry and
  makes a delete node for the record, a delete of a missing key is a
  noop), and a key that goes on plans the next segment's tree, whose new
  root, or none, becomes the leaf's entry. Each touched node gets a
  final list and a decision (`decide`): **same** if the list is its live
  list; **append** if the klongs that make it hold the list (a time
  klong, a bitmap if a compare value left, a key klong for each entry new
  or repointed) fit and leave at most theta dead klongs; else **new
  nodes**: one of its final list if only theta was passed and it fits,
  one if the list has at most h entries, else parts of at most B / 2
  (`cutParts`, sizes as even as possible).
* **Rebalance** (`rebalance`, `joinAt`): an empty child is dropped; while
  a changed child holds fewer than m entries and has a neighbour, it is
  joined with one: the left one if it is the last child, or if the two
  hold at most c (M1), else the right one; the joined list is one new
  node, or parts of at most c; two inner children's joined list is
  rebalanced one level down first. No joins below node size 8 (m = 1).
* **Settle a root** (`settleRoot`): an empty segment tree is dropped (the
  space root becomes an empty segment leaf); an inner root of one entry
  gives way to its child; a root cut into parts gets a new root above.
* **Emit**, bottom-up, each decided node once: kept nodes write nothing
  (one with a node written below it is reported on the path, so that Db
  makes it dirty as the model's marking does: D is the changed nodes and
  their current ancestors); appended nodes get their klongs; new nodes
  are filled, then reported made (their ids), then their pointers. Ids:
  a value or delete node when its operation is applied at its leaf, a
  segment tree's new key nodes when that tree is emitted, the space
  root's tree bottom-up and left to right, the top node last
  (`TopDs.newSuperRoot`, only if the space root is replaced). A node of the
  tree before that the transaction leaves unreachable is reported
  replaced.
* **The same decisions by counts.** For speed, Java decides some nodes
  without their lists where the counts give PE's decision: the short way
  of a transaction of at most 8 operations that only appends to its
  leaves and makes no segment tree (`shortWay`), leaves kept or appended
  to (`LeafFrame.leafNode`), inner nodes kept (sparse) or appended to
  (`appendedByCounts`), routing by one scan (`routeBySearch`).
* **How it is checked.** The tree checker compares Java with PE's copy
  (lean/SIS/Tree/Pe.lean) node for node, with the ids, on every traced
  transaction of the level scripts (027-02, section 4); `pecmp` showed
  that copy equal to the proved `Contract.PE.peTx` on the same traces
  (026-25, section 3); 030-21 proves that `peTx` meets the writer's
  contract. `dirtyNodeBound` is argued for PE since 028-21, which
  closed two gaps of the old count (027-03, section 8.3).
* **Removed with format 8** (026-25, section 5): the per-operation walk,
  the five splits (in place and not), rule O, the upward unlink, LE-b's
  relabel, root collapse by descent, the merges at the delete, the
  take-back and its books, the key access path (`KeyAccessPath`).


Log
===

2026-11-13. Created as a stub (Frans, 11:09, 027-04's Q3: "as
recommended").

2026-11-19. The description of the writer since record format 8, PE
(026-25).

2026-11-19. A summary of PE, until the part is written, from the code at
`b03dcea7` (`PeWriter`, `Dag.putKvs`) and 026-25. By an agent of
coord-1118, on the branch `027-pe`.

2026-11-19. 028-21: `dirtyNodeBound` argued for PE. By an agent of
coord-1118, on the branch `028-21-dirty-bound`.
