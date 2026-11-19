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


Log
===

2026-11-13. Created as a stub (Frans, 11:09, 027-04's Q3: "as
recommended").

2026-11-19. The description of the writer since record format 8, PE
(026-25).
