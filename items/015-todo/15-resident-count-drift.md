015-15. Fix: a batch subtracts values never counted, and a count driven to 0 stays 0
====================================================================================

Status: done (2026-11-03). Kind: Fix. Created
2026-11-03 by Frans Lundberg.

For release 2026.2. Found by review R1 (016-06/R1 (items/016-release-2026-2/06-reviews/R1.md)), R1-F4, with a probe.

What: a value that the writer puts into a key node is not counted.
A capacity controller's batch (`Eviction.unswizzleValues`) takes every
written value of a pinned key node and `Residents.valueOut` subtracts
each, the uncounted ones too, down to 0; `grown` and `valueIn` skip a
count of 0 (the sign of "not counted"), so the node stays counted 0 while
it is resident. The resident bytes stay below the real ones, and the
database uses more memory than its budget: in the probe, `resident bytes
1033517, exact 1299038`; with a startup distance of 50 MB, 968 against
72,726 after 50 transactions. The object counter drifts too. New since
2026.1 (whose sweeps made the count exact by walks).

Done when: "counted" is kept apart from the size, so that an object whose
count reached 0 is counted again at its write and by `valueIn`; a value
the writer puts into a counted object is counted, or `valueOut` stops at
the holder's own size; the object counter does not drift; a unit test of
the probe's steps (the leaf's count equals `bytesOf` after its write, the
resident bytes equal an exact walk); `BEFORE COMMIT OK`. Whether D's dirty
nodes are counted between their writes stays as Residents' design says,
and docs/levels.md, section 7 says it, if "exact" is not kept.


State
-----

2026-11-03, 17:23: the fix, two unit tests, the mutations and the gate
done in the clone (rebased on `a46a597`); handed off for review
(`/Users/f/fl/bench/016/015-15/handoff/`). Open: the review.

The fix and why
---------------

Chosen by agent K, 2026-11-03, as the simplest correct way to meet "Done
when":

* **"Counted" apart from the size: -1 for "not counted"**, in
  `countedMemSize` (KeyNode, TopNode: the field's initializer), which
  `Residents` tests with `< 0` everywhere (`added`, `grown`, `released`,
  `valueIn`, `valueOut`; `released` sets -1). So a count of 0, should one
  ever come, is a count that `grown` and `valueIn` raise. Not a flag: no
  new field in every node object.
* **`valueOut` stops at the holder's own bytes** (`getMemSize()`): it takes
  v's bytes, but no more than the count holds above them. Not the other
  way of "Done when", counting the writer's values where it makes their
  pointers (`Cache3.pointerCreated`): the writer's values reach a node by
  several paths (a put's `addKlong`; a split's copies, reported again by
  `Dag.reportNewPointers`, also for a node registered after its fill, in
  `timeSplit`, and for a node's own pointers after `setContentFrom`; and
  `replaceKlong`), and leave it by others (`toPreviousState`, a replaced
  pointer), so that way would count some twice and need a `valueOut` on
  each path that drops one. The floor is a few lines in one method, costs
  the writer nothing, and keeps Residents' design for D, as "Done when"
  says: an object that the writer changed is counted with its size at the
  last count until its write.
* **The object counter** then does not drift: every counted object is
  counted once (`added` returns for a count of 0 or more) and `released`
  decrements for each.
* **What stays**: the resident bytes are below the bytes in memory by the
  growth and the writer's values of the objects changed since their last
  count, D's above all, until their write. docs/levels.md, section 7, now
  says so (it said "exactly"), as do Residents' class comment and
  `Eviction.sweep`'s Javadoc.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-03, 17:01 to 17:23, by agent K (016-05), in
`/Users/f/fl/bench/016/015-15/repo` from `main` at `d5fc369`:

* **The probe on the base** (R1/ValueOutProbe, compiled against the
  base's jar): `ValueOutProbe 100000 400` printed, after the batch, `[leaf
  15531 dirty: counted 0, bytes 800]`, at the end `resident bytes 1033517,
  exact 1299038` and `leaf 15531 counted 0 after the batch: now clean,
  written at 54392, in its handle true, counted 0, bytes 2916`;
  `ValueOutProbe 50000000 30`: both leaves counted 0 after the batch, and
  `resident bytes 968, exact 72726` after 50 transactions. As R1 saw it.
* **The fix**: section "The fix and why" above; `core/Residents.java`
  (`counted` -1 for not counted and package-private, for the test;
  `countedBytes` at least 0), `dag/KeyNode.java` and `dag/TopNode.java`
  (`countedMemSize = -1`), and comments: Residents' class comment,
  `valueOut`, `Cache3.pointerCreated` (it said "a value counts as resident
  from here"; and "or swizzled by a follow", which no follow calls),
  `Eviction.sweep`'s Javadoc ("exact"), docs/levels.md, section 7.
* **The tests**: `CapacityTester.testBatchOnPinnedLeaf` (unit), the probe's
  steps: a startup distance of 100 kB, 20 transactions of 1,000-byte
  values into one leaf, which stays dirty; batches with a budget of 1,000
  bytes until its values are taken (a batch ends after 2 ms: under load
  one may not reach the leaf's map; seen once); its count is then its
  bytes, its own; transactions until it is written: its count is its
  bytes; its eviction: the object counter one less. After each step
  `checkCounts`, over a walk of the resident objects: each index object
  counted (0 or more), at most with its bytes, with them if not dirty; the
  resident bytes the sum of the counts, the object counter their number.
  `Residents.testCountedApartFromSize` (unit): not counted is -1; a
  reader's value and a writer's value taken by a batch take the count to
  the own bytes, no further; a count of 0 is raised by `valueIn` and
  `grown`; a release once.
* **Mutations** (`/Users/f/fl/bench/016/015-15/mut/mutate.py`, with
  `unit.sh -c 'Residents|CapacityTester'`): M1, the floor removed: both
  fail (`its count after the batch, expected 800, got 0`; `Expected 224,
  got 0`). M2, the sentinel removed (0 as not counted, the floor kept):
  both fail at the -1 checks; with those left out, the Residents test
  fails at the count of 0 (`Expected 256, got 0`). M3, the base's
  accounting (`counted` made package-private to compile): the CapacityTester
  test fails (`its count after the batch, expected 800, got 0`). M3b, M3
  with the test's checks of the leaf's count and of each object's count
  left out: it fails at `one object less, expected 10, got 11`, the object
  counter's drift. With the fix the four tests pass (`testAccounting`
  unchanged).
* **The probe on the fix**: `ValueOutProbe 100000 400`: after the batch
  `resident bytes 1048, exact 1048; [leaf 15531 dirty: counted 800, bytes
  800]`; at the end `resident bytes 1036433, exact 1299038`, no leaf
  counted 0, every clean leaf counted with its bytes; the gap, 262,605, is
  the dirty leaves' (261,549, bytes less counts) and D's inner nodes'.
  `ValueOutProbe 50000000 30`: `resident bytes 1176, exact 1848` after the
  batch, `resident bytes 1896, exact 72726` after 50 transactions: D,
  counted at the last count, by design. In 3 of the first 8 runs, while
  another agent's gate ran, the batch stopped before one leaf's map or
  both (`exact 22998` or `37800` after it; a batch ends after 2 ms); then
  8 runs of 8 took both leaves' values, as 8 of 8 on the base.
* **The gate**: `java/before-commit.sh`, 17:15 to 17:16: `BEFORE COMMIT OK
  (107 s)`, 1,110 unit tests and 78 f-tests. Then the clone rebased on
  `main` at `a46a597` (015-12's and 005-79's changes) and gated again,
  17:19 to 17:22: `BEFORE COMMIT OK (175 s)`, 1,114 unit tests and 78
  f-tests, `doubles.py` clean.

2026-11-03, 17:28. Reviewed by the coordinator (016-05, H5): no faults. Open point,
for after the release: a batch's `freed` adds a taken value's full size even
when the count drops less (the floor), so a batch can end above its target;
the next trigger goes on from there. Combined gate on main: BEFORE COMMIT OK.
