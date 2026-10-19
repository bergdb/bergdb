005-09. Fix the race that lets the node table name a released object
====================================================================

Status: open. Kind: fix. Created 2026-10-19.


The issue
---------

`EvictionReaderTester.testReaderPausedInsideAFollow` fails now and then:
"INV-CAN: the node table names a snapshot of node N". Found in 005-02
([02-fix-m46-ordinal-bound.md](02-fix-m46-ordinal-bound.md), "Found on the
way"): the first `level3.sh` run there failed 1 of its 947 unit tests on
it, and passed when run again. So a gate can fail on it.

It is not 005-02's. Repeated under load (four JVMs per build beside four
busy loops, 150 runs each), the test failed once in 600 runs on the code
before 005-02 (`8c5a106`), with the same message, and in none of 600 with
005-02. The other three gates' unit runs passed it.

INV-CAN (the audit, `Audit.check`) says that the node table names canonical
objects only. The register row M31 and item 001's J1 and J3 rest on it
([level4-alignment.md](../../docs/level4-alignment.md)): a release clears
the canonical flag and takes the table's entry, and a later read loads the
version from the slot's position.


A likely cause
--------------

From reading the code at `8c5a106`, not tested:

* A reader's follow of a stream pointer
  (`NodeCollection.followStreamPointer`) takes the canonical object from the
  node table (step 3), then swizzles the slot (step 4):
  `if (result.isCanonical()) cache.pointerCreated(predecessor, pointerIndex, result)`.
* `Cache3.pointerCreated` checks `to.isCanonical()` outside the table's
  per-id lock, and then, under the lock, enters the object when the table has
  no entry for the node.
* A sweep releases an object that only the node table holds without the
  slot's pointer lock (`Eviction`, `release` and the loop over the table's
  objects): it clears the canonical flag, then `Cache3.released` removes the
  entry under the per-id lock.

If the release comes between the reader's check and its insertion, the
table gets back an object that is no longer canonical: a snapshot. The test
opens that window: it pauses a reader just before step 4 (the
`firstTouchListener`), starts a sweep of every evictable object, and lets
the reader go after 500 ms; when the sweep is slowed by load, it is still
running then.

Readers and sweeps overlap like this outside tests too (Q8: readers do not
take the write lock; a sweep runs under it). What a snapshot in the table
leads to is not known: a reader does not take it (step 3 wants a canonical
object), but the writer's `makeCanonical` and later releases meet it.


The task
--------

1. Reproduce: a probe that runs the test in a loop under load (as 005-02
   did: about 1 in 600), or better a deterministic test that makes the
   release come between the check and the insertion (a hook in
   `Cache3.pointerCreated`, as the test's hook in the follow).
2. Confirm the cause, or find the real one. Look also for the other
   check-then-act steps on the canonical flag and the table: `makeCanonical`,
   `isBetter`, the loader, and `released` itself.
3. Find out what a snapshot in the table can do: wrong records, two
   canonical objects, a lost entry, or nothing but the audit's failure.
4. Fix it, for example: check the flag again under the per-id lock in
   `pointerCreated` (and clear it under the same lock in the release), so
   that the check and the insertion are one step against a release.
5. Say in docs/level4-alignment.md (a register row, or M31's) and in
   docs/levels.md what it was.


Done when
---------

* A test that fails without the fix and passes with it; the flaky test
  passes many times under load (thousands of runs, not one in 600).
* No stream changes: StreamDigest the same as R8's; `EvictionInvariance` and
  the four gates print their OKs.
* The register and docs/levels.md say what was found and fixed.


First step
----------

Write the deterministic test of step 1, and see whether it gives the
audit's message.


Size and order
--------------

S, if the cause is the one above. Independent of the other entries; it
touches `Cache3`, which 005-08 changed (the maps, not `pointerCreated`).
005-07 (synchronization) should list it among the races found.
