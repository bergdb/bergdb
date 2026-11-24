028-45. Change: a test of Db's dirty-node count with transformations
====================================================================

Status: open. Kind: Change. Frans: none.
Created 2026-11-24 by Frans Lundberg.

What: `Db.checkDirtyNodes` (`java/src/bergdb/core/Db.java`; 027-08,
section 4.2) refuses a user transaction, before its go point, whose index
nodes could take its record past the limit. Three of its ways of counting
are not tested on purpose:

* the cheap estimate: 3 nodes a level of a put's path, 20 of a delete's,
  of `height` levels a segment of the key, and 3 a key; where it fits,
  Db lets the transaction through without `Dag.dirtyNodeBound`;
* a key with a key transformation: counted by that estimate also when
  the rest is walked, with the segments of the key as given
  (`kv.getKey().length`), as the check runs before the transformation;
  a transformation may give a longer key (the Pub API's
  `${transactionTime}`);
* a key with a value transformation, which may give a put or a delete:
  walked by `Dag.dirtyNodeBound` as a put and as a delete (023-11,
  review B, B2).

The change: a unit test that compares, for transactions with such keys,
the count of each way with the key nodes the transaction marks.

Why: the theorems of the dirty-node bound count each key once, as the
put or the delete it is (`Contract.DNB.opsKd`); for these three ways the
link from Java's admission count to them is argued (028-21; 023-11,
review B, B2), not proved and not tested on purpose; C-T8 checks the walk
with a trace's effective operations only (030-38, G9 and section 4, item
6). A count below the nodes a transaction marks lets through a
transaction whose record could pass the limit after its go point, where a
failure fails the database. 030-39, finding F7, accepted for release
2026.6 with this entry proposed; Frans registered it on 2026-11-24
(006-33, points 2 and 3).

Frans: none.

Done when:

* A unit test of `bergdb.core`, run by `java/before-commit.sh`, makes
  transactions at node sizes 8 and 30 at least (`DbBuilder.maxNodeSize8()`
  for 8) with: value transformations that give a value, a delete of a
  present key (enough of them under a node to join nodes) and nothing on
  an absent key; key transformations, one of them to a key of more
  segments than the key as given; and plain puts and deletes. For each
  transaction it asserts that the key nodes it marks (as C-T8 counts
  them, `markedKeyNodes` in `lean/SIS/Tree/Bound.lean`: the nodes on the
  access path of its change, and those it makes) are at most the walked
  count and, where the estimate fits the limit (where Db takes it without
  the walk), at most the estimate; each count as Db computes it. It
  asserts too that its cases reach both ways of `checkDirtyNodes`: an
  estimate that fits the limit and one that does not (a test may lower
  `StoredTrans.recordLimit`, as DbTester's tests of the limit do).
* `checkDirtyNodes` gives the test its counts by a package-private method
  split from it; what it refuses is unchanged (`DbTesterLimits` and
  `LimitsTester` pass as before).
* `java/before-commit.sh` BEFORE COMMIT OK, within a few seconds of its
  time before.
* The texts that say these ways are not tested say what the test checks:
  030-26, 2.7 (and an item of its section 5), and 027-08, section 4.2.
  030-38, the guarantees of release 2026.6, stays as it is.
* A transaction that marks more key nodes than a count is a fault of the
  count: the test stays failing on the entry's branch, and the entry
  records the case, its seed and the fix proposed (with options for
  Frans, if the fix changes what Db refuses).

First step: read `Db.checkDirtyNodes` and 027-08, section 4.2; then
DagTester's `BoundCase`, which counts the key nodes a transaction makes
dirty through the Dag's listeners, as a model for counting them in a Db.


Log
---

2026-11-24. Registered by an agent of lead-1124, from 030-39, F7
(Frans, 2026-11-24, 006-33, point 3).
