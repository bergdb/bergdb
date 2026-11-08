019-46. Investigate: an INV-SLOT violation in EvictionAccountingTester under load
================================================================================

Status: done. Kind: Investigate. Frans: none.
Created 2026-11-08 by Frans Lundberg.

What: one run of `java/before-commit.sh` on the night of 2026-11-08 (in
the clone of 021-09, on `main` at 559b9ac plus 021-09's change to
`PubKeys`, no Core change of the night yet) failed in
`bergdb.core.EvictionAccountingTester.testAccounting`:

    seed 2: batch 12: the audit: [INV-SLOT: node 1599105, slot 4 for node
    1599101 names 1857728, its latest version is at 1859536 (stream)]

The test runs reader threads beside eviction. It passed three times
alone and in every later gate; the failing run was under load (a load
average of about 8, with the night's parallel gates). The log:
`/Users/f/fl/bench/006-15/night/evict-accounting-flake-unit.txt`. Found by
the agent of 021-09 (coord-1108's night).

Why: INV-SLOT is one of the Core's invariants (docs/levels.md): either a
pointer of a node can name an old version of another node (a real fault
of the bug-free Core of 2026.3, a stale pointer under eviction and
concurrent reads), or the audit reads a state that is not stable (a fault
of the test). Either way it must be known before 2026.4.

Done when: the cause is found and shown (a reproduction, by load or by a
forced schedule), and fixed in the Core or in the test, with a test that
fails before the fix; the level script of the mechanism run
(`java/stress/level*.sh`); `BEFORE COMMIT OK`; a line in
`releases/next.md` if the Core changed.


Cause: a real fault of the Core, not of the audit
-------------------------------------------------

A stale pointer made by a reader's `Cache3.dropIfEmpty` racing the
writer's load of the same node. It is in every release with handles (009,
step 3b, `4a1fc5e`; so 2026.2 and 2026.3).

The actors: the writer (one thread, Db's write lock held for its
transaction); readers (any threads, no write lock); eviction (the write
lock, between transactions); a lock per map of Cache3's handles (the
node table) and each handle's monitor.

1. A reader's follow whose read keeps nothing (a cache policy that keeps no
   index node: `Dag.CACHE_NOTHING`, which the Core API offers through
   `GetData.cachePolicy`, and which `EvictionAccountingTester` uses for a
   quarter of its reads) has made the node's live handle h
   (`liveOrNewHandle`), read the version without installing it, and calls
   `dropIfEmpty(h)` (`NodeCollection.followStreamPointer`). It runs without
   the write lock.
2. `dropIfEmpty` was, under h's map lock: test `h.obj == null`; then CAS
   LIVE to DEAD; then `kill(h, h.obj)`; then remove h from the map.
3. The writer, in a transaction, follows a pointer to the same node: step 3
   of the slow path takes the node's live handle from the map, h (before
   the reader's map lock); step 4, under h's monitor, LIVE to LOADING, the
   read, `install` (h.obj is the version, the latest before the
   transaction), LOADING to LIVE; step 5, the parent's pointer gets h;
   step 6, `makeCanonical`. Steps 4 to 6 take no map lock, so they can run
   whole between the reader's test and its CAS when the reader thread is
   descheduled there: a window of a few instructions, which load opens.
4. The CAS then succeeds on a LIVE handle that holds the writer's
   canonical object, and `kill`, written for an eviction under the write
   lock, evicts it: `h.writtenPos` is its position, the version before the
   transaction; its canonical flag is cleared; h.obj is null; h is DEAD
   and out of the table.
5. The writer goes on with the object it got: changes it, so that it is
   dirty in the record or in D, not canonical and in no handle (the
   audit's "pins: object of D ... is not the canonical, dirty object"),
   and writes it at a new position. The parent's pointer holds h, dead,
   whose serialized reference (the record rule, `Handle.serializedRef`)
   is h's written position: the parent's record names the version before
   the transaction, the stale pointer that the audit reports as INV-SLOT
   "(stream)", 019-46's failure; and readers that follow the parent read
   that version: old values, wrong answers. If the kill falls between
   steps 4 and 6, `makeCanonical` puts the object into the dead handle: a
   canonical object outside the table (INV-CAN).

In 2026.3 the Pub API reads with `CACHE_ALL_EXCEPT_LARGE_VALUE_NODES`,
which keeps every index node, so it does not reach `dropIfEmpty`; a user of
the Core API who reads with `CACHE_NOTHING` beside writes does.

Review R1 of release 2026.2 described this race, as its D2 (016-06, R1,
section 3: the kill before `makeCanonical`, which leaves a canonical
object in a dead handle), and left it unverified: no caller read with
`CACHE_NOTHING` then. `EvictionAccountingTester` (018-05) has since, for
015-71. R1's suggestion, `dropIfEmpty` taking h's monitor, would invert
the slow path's lock order (h's monitor, then the map's lock in
`liveOrNewHandle`, step 4) and could deadlock; the fix below decides after
the CAS instead.


Evidence
--------

* Load alone did not show it in about 20 minutes of runs on F53 at a
  load of 15 to 60 (the night's gates beside them): 900 seeds of the unit
  shape in 6 processes; runs of 300 batches with 6 readers in 6 processes
  for about 5 minutes (they found only the recount fault below); 130 runs
  of 150 batches with 6 readers and an audit after every transaction.
* A widened window does: a pause of 0.2 ms in `dropIfEmpty` between its
  test and its CAS (the test hook `Cache3.dropIfEmptyHook`, null in use).
  300 seeds of the unit shape (seeds 100 to 399), the test unchanged but
  for the hook: 31 failed (a few with two findings): 14 with "pins: object
  of D ... is not the canonical, dirty object", 11 with 019-46's INV-SLOT
  "(stream)", 3 with INV-SLOT "(memory, snapshot)" (2 of them with
  INV-CAN), and 5 with readers' wrong answers: old values, or null for a
  key that has a value. With the fix, the same 300 seeds: none failed.
* The forced schedule, deterministic: `NodeCollection
  .testDropIfEmptyKeepsTheWritersObject`. The hook runs the writer's
  follow of the node on the reader's thread (the map's lock is
  reentrant), as the writer's thread runs it in the window. Before the
  fix the writer's object came back not canonical, out of the table, its
  handle dead with a written position; with it, canonical, the table's,
  in a live handle.


The fix
-------

What: `Cache3.dropIfEmpty` decides that h is empty after h is DEAD, not
before: test (a fast exit); CAS LIVE to DEAD (if it fails, a loader holds
h, which is then not empty); then, if h.obj is not null, CAS back to LIVE
and keep h; else remove h from the map. No `kill`: an empty handle has
nothing to kill.

Why it is enough: once h is DEAD, h.obj cannot be set. `install` needs h
LOADING, which only a LIVE handle becomes (CAS LIVE to LOADING);
`register` holds the map's lock, which `dropIfEmpty` holds, and replaces a
dead handle by a new one; the writer's `makeCanonical` sets h.obj only to
replace the object that its own follow found in h or installed there, so
never fills an empty h, and nothing empties h in between (eviction needs
the write lock, which the writer holds; `dropIfEmpty` no longer kills a
filled handle). So an object seen after the CAS was put there before it,
and h lives on with it; an object not seen will not come, and removing h
is right. The DEAD between the two CAS is not seen by `liveOrNewHandle`
or by eviction and the audit (all under the map's lock); a loader that
sees it (the slow path's steps 3 and 4 test `isDead`) resolves the node
again with `liveOrNewHandle`, which waits for the map's lock and returns
h, LIVE again; `install`, `makeCanonical`, `Handle.usable` and the record
rule do not read the state. The revert's CAS cannot fail: nothing changes
a DEAD handle's state (an assert says so).

When and by whom: by a reader thread, at the end of a follow that kept
nothing; with or without a writer in a transaction. Eviction's own
`clockStep` and `evict` keep their test-then-kill: they run under the
write lock, when no writer follows and only readers' versions, never
canonical objects, can appear in a handle.

How it is checked: the forced-schedule test above (unit group); the night
test `EvictionAccountingTester.testAccountingWideDropWindow` (40 seeds of
the unit shape with the widened window, about 20 s; 2 of 40 failed before
the fix); the widened 300 seeds above; `java/stress/level4.sh` (eviction,
the audit, the readers, conformance with the Lean model); `BEFORE COMMIT
OK`.


Also found (not this entry's fault)
-----------------------------------

`EvictionAccountingTester`'s recount fails, deterministically, for some
seeds of a longer shape, with and without this fix: "pointer 4 of node 5237
holds a value of 1126456 bytes (over 1 MiB: not kept)", after a run of
restarts (015-68's class: a start keeps a large value of its rerun?). It
reproduces with a class in `bergdb.core` that calls
`EvictionAccountingTester.run(1075, new EvictionAccountingTester.Shape(300,
300, 4, 6, 0.002), System.out)`: batch 5; also seeds 1133, 1249, 1267 and
1276 of that shape. For a new entry.


Log
---

2026-11-08. Registered by the coordinator of the night (006-15) from the
gate failure in the clone of 021-09.

2026-11-08 to 09. Investigated, reproduced and fixed by the night's agent of
019-46, under Frans's delegation of 22:17: the cause above,
shown by a widened window and a forced schedule, after load alone had not
shown it; the fix in `Cache3.dropIfEmpty`, with the test hook
`Cache3.dropIfEmptyHook`; the tests
`NodeCollection.testDropIfEmptyKeepsTheWritersObject` (unit) and
`EvictionAccountingTester.testAccountingWideDropWindow` (night).
`java/stress/level4.sh` (full): LEVEL 4 OK (EvictionInvariance, restarts,
crashes and reclaim with the audit, 0 failed; ReclaimReaders, 0 failures;
conformance C-P and C-H, 0 of 10,353 transactions; LargerThanMemory).
`BEFORE COMMIT OK`. Status: done, 2026-11-09; the line in
`releases/next.md` is the coordinator's.
