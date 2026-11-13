# 027-12. Memory: handles and eviction

Created 2026-11-13 by Frans Lundberg. Status: stub.

Part 8 of 027's outline (027-04, section 2.3; levels: 2, 4). What a
running database holds: one canonical object per index node; lazy reading
at a pointer's first touch, and lemma M; handles, the node table and the
record rule; the fast path without a lock and its memory-model edges, the
slow path, the maintenance follower.

Not written yet: the outline's order of writing is 027-04, section 5.1.
Each part follows the template of 027-04, section 2.2.


Log
===

2026-11-13. Created as a stub (Frans, 11:09, 027-04's Q3: "as
recommended").
