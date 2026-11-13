# 027-08. The key tree: the writer

Created 2026-11-13 by Frans Lundberg. Status: stub.

Part 4 of 027's outline (027-04, section 2.3; levels: 0). What a
transaction's operations do to the tree, in the order that record format 7
fixes: a put and the five splits, with h; a delete's upward unlink, the
take-back, LE-b and root collapse; the merges of underfull nodes (m and
c), with BU1 and the bound on key nodes by the live keys; at most theta
dead klongs a node (rule O); `dirtyNodeBound`.

Not written yet: the outline's order of writing is 027-04, section 5.1.
Each part follows the template of 027-04, section 2.2.


Log
===

2026-11-13. Created as a stub (Frans, 11:09, 027-04's Q3: "as
recommended").
