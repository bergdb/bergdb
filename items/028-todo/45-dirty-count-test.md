028-45. Change: a test of Db's dirty-node count with transformations
====================================================================

Status: done. Kind: Change. Frans: decided (A, 2026-11-24, 12:26).
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

Frans: decision, since 2026-11-24: the fix of the fault the test found
(Result, "The fault"), options A to C there; recommended: A.

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


Result
------

Made on 2026-11-24 by an agent of lead-1124, on the branch `028-45`, in
test code and a split of `Db.checkDirtyNodes`; what Db refuses is
unchanged.

* The split: `Db.countDirtyNodes(Trans, boolean walk)` computes the
  counts, the cheap estimate and, if it does not fit or `walk` is true,
  the walked count (the estimate for the keys with a key transformation
  and `Dag.dirtyNodeBound` for the others), with the figures they are
  compared with (`Db.DirtyNodeCounts`: the limit, the bytes a node and of
  the top nodes, the most nodes a record takes). `checkDirtyNodes` calls
  it without the walk and throws as before, with the same message. The
  test calls `countDirtyNodes(Trans)`, which takes the write lock and
  walks.
* The test, `DbTesterDirtyCount.testCountsCoverMarkedKeyNodes` (unit, in
  `before-commit.sh`; about 0.3 s): at node sizes 8 and 30, the record
  limit lowered to 4 MB so that a transaction of a few deletes or a few
  tens of puts takes the walk. Each transaction: key transformations of
  keys of one segment to new keys of 15 or 16 at the start, where
  `height` is small; loads of plain puts; in two ranges, deletes by value
  transformations of two keys of three and then of two of three of those
  left, and of about half the rest one a transaction, joins asserted; 60 random
  transactions of 1 to 300 operations: plain puts and deletes, value
  transformations to a value and to null on present and absent keys, key
  transformations to keys of the database (puts, and with a
  transformation to null deletes) and to new keys of up to 16 segments
  from a key of one. The key nodes a transaction marks are counted from
  Db's own listeners on `x.putData`, wrapped, as `DagTester`'s
  `BoundCase` counts them: followed, made, appended to or on the path of
  the change, if the transaction changes anything, less those it
  replaced; that is at least C-T8's `markedKeyNodes`. For each: marks at
  most the walked count, and at most the estimate where the estimate
  fits; at each node size both ways reached and keys transformed to
  longer keys (node size 8: 85 transactions, 68 estimates that fit, 17
  walked; 30: 124, 85 and 30, and 9 refused by the walk, 005-31, as the
  test expects). All pass.
* The test fails when a count is made short on purpose (tried
  2026-11-24, not committed): the walked count a third and the estimate
  a quarter, or a value
  transformation walked as a put only, which a single delete by a value
  transformation that joins a node shows (6 marked, counted 5).
* `DbTesterLimits` and `LimitsTester` pass as before (in
  `before-commit.sh`).

### The fault

`testKnownFaultKeyTransformationDeeperThanCount` (unit, deterministic,
no seed; about 10 ms): at node size 8, keys of a prefix of 105 bytes cut
at each of its 15 segments, 40 keys at each, so that each of the 15
segment trees is three levels high; then one put of the key "g" (one
segment) with a key transformation to the prefix and "zzzzz" (16
segments). It marks 46 key nodes (three in each tree and a new one); the
estimate and the walked count are 39 (3 x 12 + 3, `height` 12 of a stream
of 64 kB), and the estimate fits. The test asserts the fault (marks above
both counts): it fails once the count covers the case, and is then to be
turned around. At node size 30 the same shape at 10 to 200 keys a level
gave segment trees of at most two levels, within the count (31 marked,
42 counted at 80 keys a level).

The cause: the estimate counts `height` levels for each segment of the
key as given, and a key transformation may give a key of more segments
(to 16 for a user's key, L2), each a segment tree on its path. At the
default record limit a record takes about 3.7M index nodes at node size
30 (10.5M at 8), and no transaction of the tests came near it; the
shortfall is of the count, seen with a lowered limit.

Options (each changes what Db refuses):

* **A. Count a key with a key transformation after the transformation**:
  a second check right after `Db.transformKeys`, which runs under the
  write lock before the go point and already refuses with every key given
  back (024-16), walking the keys as transformed with
  `Dag.dirtyNodeBound`. The count is then the same as for other keys; a
  transaction whose estimate did not fit only because of its key
  transformations is let through when its walk fits, and one whose
  transformed keys walk over the limit is refused there. Cost: a walk
  for those transactions, as for others. Recommended.
* **B. Count such a key by the most segments a key may have after it**:
  16 for a user's key (L2) instead of the given ones, in the estimate. No
  move of the check, but it refuses more: at `height` 33 (a stream of
  about 100 GB) 500 operations with key and value transformations count
  about 5.3M nodes, over the 3.7M a record takes at node size 30, where
  they count 330,000 now; the Pub API's key replace uses key
  transformations.
* **C. Keep the count**, documented as short for such keys, the known
  fault test kept, relying on the default limit's margin.


State
-----

2026-11-24 (lead-1124's agent): the test and the split are made and
pass, and the texts are updated (030-26, 2.7 and section 5, item 14;
027-08, section 4.2). The entry's last point is met as far as it can be
without a change of Db: the fault, its case and the options are above.
Its words "the test stays failing on the entry's branch" are not met:
as lead-1124's brief for this entry asked, the case is kept as a test
that asserts the fault, so that `before-commit.sh` passes. Open: Frans's
choice among A to C; the fix is a new step (or entry), and with it the
known-fault test turned around.


Log
---

2026-11-24. Registered by an agent of lead-1124, from 030-39, F7
(Frans, 2026-11-24, 006-33, point 3).

2026-11-24. In progress: taken by an agent of lead-1124.

2026-11-24. The test, the split and the texts made (lead-1124's agent);
the test found the estimate of a key transformed to a key of more
segments short (Result, "The fault"); Frans: decision. Gate: BEFORE
COMMIT OK.

2026-11-24. Registered as RB-005 (033), S4: within L1 to L5 the shortfall
cannot bring a transaction to the record limit (TP23, TP26, ReleaseFits;
TP26 stated, not proved; the least margin 0.7 % at node size 8); past it,
a transaction's nodes would never be taken and startup would grow, with no
failed database. The same count in 2026.5 and 2026.6.

2026-11-24. Frans chose option A (12:26); the fix is 028-50, with the
known-fault test turned around there.

2026-11-24. Done: the test landed (`ace0a1bb`); the fault it found
is RB-005 (033), fixed by 028-50 (`33193b20`) on `main` for 2026.7, with
the known-fault test turned around. Moved to Closed in 028's readme.
