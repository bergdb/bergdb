# 026-08. The node size fixed at 30 for users; other sizes for tests only

Created 2026-11-13 by Frans Lundberg. Status: open (registered, not
started).

For release 2026.6, with the stable stream format (027-03): one node
size, B = 30, for every database a user makes, by the Pub API and the
Core API; the sizes 8, 14 and 62 only for BergDB's own tests.


Decided
=======

Frans, 2026-11-13, 09:17, on 024-19's Q5 (a start reads B from the meta
block): "I was surprised with the node size parameter. Not sure we need
this at all. Fixed at 30 could be fine. We have, so far, found little
reason for other values. This is something that is easy to keep a
constant first, then allow variation in later versions if needed. The
other way around is hard. What do you think?" To the coordinator's
answer (below), 09:21: "Yes".

The coordinator's answer, as agreed:

* **For users and the stable format: 30, fixed.** Every size the stable
  format accepts is a promise each later release must keep. 024-19
  found no case for another: 30 within 10 % of the best in every
  measured workload; 62 cost 16 to 45 % more bytes a put at 10M to 100M
  keys; 8 and 14 serve the tests. The meta block keeps its node-size
  field (`u16` at byte 44, 027-03, section 6), written as 30, and a
  start refuses another value, as `Db.refuseOtherNodeSize` does now; the
  field is the hook for a later release that allows other sizes without
  a format change.
* **For the tests: 8, 14 (and 62) stay, test-only.** About 40 files use
  them (tests, harnesses, fuzzers, the conformance sets, `src-dev`): a
  small B gives deep trees with few keys, so splits, merges and
  collapses at many levels are tested in seconds. They are reached only
  from BergDB's own tests, not through public `DbBuilder` methods; a
  database made at a test size carries no promise that a later release
  reads it.
* **The Lean model: B stays a parameter.** A proof over every B costs no
  more than one at 30 and is more general.

What it revises: 024-19's Q2 (answered "yes, as recommended" at 08:54:
B a property of the database, 8, 14, 30, 62 by the Core API) becomes B =
30 for users, the other sizes internal; Q3's rule (v B / 30) stays, used
by the tests at 8, 14 and 62; Q5 (the start takes B from the meta block)
is dropped: with one size there is nothing to take.


The work
========

* `DbBuilder.maxNodeSize8()`, `maxNodeSize14()` and `maxNodeSize62()`
  leave the public Core API (package-private, or a test hook that the
  tests outside `bergdb.core` reach); `maxNodeSize30()` goes too or stays
  as a no-op, whichever keeps the Core API simplest.
* The Javadoc: `DbBuilder`, `Db` and the Pub API's package say the node
  size is 30.
* 027-03: the node size is 30 in the stable format; the field kept and
  checked; the test sizes named as outside the format's promise.
* releases/next.md: a Core API change (the setters gone).
* Gates: before-commit.sh, level1.sh, and the level scripts whose
  conformance sets run other sizes (they keep running them).


Log
===

2026-11-13. Registered by coord-1113 (Frans, 09:17 and 09:21).
