024-release-2026-5
==================

Created 2026-11-10 by Frans Lundberg. Status: open.

Release 2026.5 of BergDB, after 2026.4 (020): its plan, its decisions and
the work towards it. Frans, 2026-11-10, 17:52: "Time to create the
nnn-release-2026-5 item? We are already planning for it, so why not."
Its theme is not set yet.


Planned so far
==============

What Frans has put off to 2026.5 or to after 2026.4, with where it was
decided. Nothing else is decided.

From 023, the Core's cleanup (023-08, section 5, "Later, each on its
own", and section 7):

* **The builder's rule "the last operation wins"**, put or delete, for
  `Trans.Builder` as for the KVs that key transformations make one key,
  with BergDB's C clone (Frans, 17:41 to 17:48; 2026.4 keeps 015-40's
  rule: the last put, or a delete if there is no put).
* **P8, each reclaim step scans at its own time**, with fault 13's fix (a
  step counts only the KVs stored before pStart; 023-08,
  checks/p8-liveness.md) and the liveness tests: a shorter lag after a
  mass delete. No format cost.
* **Merges at the delete** (023-05 P5), switched on by the record's
  format, so that 2026.4's databases need no refusal.
* **Fix (a) of the dirty top-node window** (023-05 P7), if the ratchet
  test shows that the window grows (023-08, Q6).
* **`maintain()`**, the explicit call that drives cleanup (023-04, Y10).
* **The cache's tables** that keep their peak size after a mass delete
  (023-08, section 4).
* **The last touch of a reclaim iteration** over keys put beyond the
  scan's end, maybe by marking only the rewrite paths (023-08, section 4;
  review A, section 4.2).
* **Dead klongs in live nodes**: compaction, beyond 2026.4's named
  allowance (023-08, Q5).

Not to do (023-08, section 5): rule (b') of the window, and the replaced
queue on by default.


Files
=====

* 01-inventory.md. 024-01, the inventory of candidates for 2026.5, for
  Frans to choose a theme and a scope (Frans, 19:24 to 19:26). Being
  written.


Log
===

2026-11-10. Created the item (Frans, 17:52), with what 023-08 put off to
later.

2026-11-10. Frans (19:24): "About 2026.5. I would like to prepare for
this work. What can we do now?" 024-01, an inventory of the candidates,
started 19:26.
