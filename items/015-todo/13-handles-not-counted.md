015-13. Fix: the resident bytes count no handle, where 009-02, 4.7 counts them
=================================================================================

Status: done. Kind: Fix (decided). Created 2026-11-03 by Frans Lundberg.

For Frans; a known issue of 2026.2 until decided. Found by review R1
(016-06/R1 (items/016-release-2026-2/06-reviews/R1.md)), R1-F2, with a probe.

What: 009-02, 4.7 counts a live handle with its table entry (79 bytes)
and 32 bytes for each pointer that holds a handle. The code counts
neither (`Residents.bytesOf`, `added`; `Cache3`). In R1's probe that is
34 to 49 percent of the counted bytes, so a database uses that much more
memory than its budget, more with small nodes and small budgets. Not in
2026.1 (no handles).

Options: A, count them as 4.7 says (R1-F2's fix: `bytesOf` adds 32 per
handle pointer, `added` and `released` 79 per live handle); B, record in
009-02, section 9 and docs/levels.md, section 7 that the budget covers the
objects and their values only.

Recommendation: A after the release, with the eviction numbers measured
again (more eviction at a given budget); for 2026.2, the known issue in
the notes with the probe's figures.


State
-----

2026-11-03, 20:45: option A done as R1-F2 proposes, in
`/Users/f/fl/bench/016/015-13b/repo` (`main` at `04d257c` with agent K's
work-in-progress commit brought over and finished, rebased on `ca02b5e`,
015-14): the count, three
tests, the mutations, docs/levels.md, section 7, and `before-commit.sh`;
handed off for review in `/Users/f/fl/bench/016/015-13/handoff/`. Open:
the review (016-05, section 5). The eviction figures at a given budget
are not measured again (the Recommendation): at a given `cacheSizeInMb`
fewer objects stay resident than before, about a third fewer in R1's
probe (the same objects are now counted with 1.5 times the bytes); the
release notes should say so (016-03).


The fix
-------

What, when, by whom, how checked:

* **What is counted** (`Residents.bytesOf`): an index object's own bytes
  (`getMemSize`), 79 bytes for its live handle with the handle's entry in
  the node table (`ENTRY_BYTES`, 009-02, T1a), 32 bytes for each of its
  pointers that holds a handle, live or dead (`HANDLE_BYTES`), and its
  values; for key nodes and top nodes. As 4.7 says, an upper bound: a
  handle that several pointers hold, or a pointer and the table, is
  counted for each. Counted when the object enters its handle (`added`),
  recounted at its write (`grown`), taken away when it leaves (`released`),
  and checked against a walk by `resync` (the audit, the test schedules),
  all through `bytesOf`, as before.
* **When a pointer gets a handle after the count**: a loaded object's
  pointers hold nothing until they are followed, so a reader's follow
  that puts a handle into a pointer that held none adds 32 bytes to the
  holder's count (`Residents.handleIn`), in `NodeCollection
  .followStreamPointer`, step 5, under the holder's monitor, which the
  swizzle took already: the check of what the pointer held, the swizzle and
  the count are one step, as `valueIn` is for a value. A swizzle that
  replaces a handle by another (a dead handle resolved again) adds
  nothing. No other place puts a handle into a counted object's pointer
  that held none, but the writer's, on objects that its record's write
  recounts (`resolvePointers`, then `grown`), startup's before the count
  (`createMemoryPointers` before `registerSectionNodes`; the primordial
  super root), and `linkD` on D's objects, which are counted at their last
  count until their write, by 015-15's design. Eviction never takes a
  handle out of a pointer: a dead handle stays counted in its holders
  until they leave.
* **valueOut's floor** (015-15) is the holder's bytes without its values
  (`bytesWithoutValues`: its own, its entry and its handles), so that a
  batch that takes a pinned leaf's values does not take its handles' or its
  entry's bytes with them.
* **Not changed**: the stream, the Pub API, the capacity controller (it
  reads the counts; 015-10's stop rule counts maps, not bytes), the fast
  path of a follow (no count there: a pointer that holds a handle already
  is counted).
* **Checked by** `CapacityTester.testCountsWithHandles` (unit, about 0.05
  s), `Residents.testHandlesCounted` (unit), the two Residents tests and
  `testBatchOnPinnedLeaf` updated, the mutations in the Log, and R1's
  `HandleBytesProbe`.


Log
---

2026-11-03. Registered by the coordinator of release 2026.2 (016-02).

2026-11-03, 17:18. Frans: "This seems straigh-forward. If it really is
straight-forward and you have a proposal, fix it before the release." So
option A, R1-F2's proposal, before the release, by agent K after 015-15.

2026-11-03, about 17:00 to 17:26, by agent K (016-05), in
`/Users/f/fl/bench/016/015-13/repo` (`main` at `4948ec6` with 015-15's
commit cherry-picked, `813f1b6`): a work-in-progress commit, `959371d`,
not built or tested. Its State note, as K left it:

> 2026-11-03, 17:26, by agent K, stopped at the coordinator's request (usage),
> in `/Users/f/fl/bench/016/015-13/repo`: `main` at `4948ec6` with 015-15's
> commit cherry-picked (`813f1b6`), and a work-in-progress commit on top.
> Not built, not tested, not gated.
>
> * Done: `Residents.bytesOf` counts `ENTRY_BYTES` (79, the live handle with
>   its table entry) and `HANDLE_BYTES` (32) for each pointer that holds a
>   handle, for key and top nodes; `Residents.handleIn`; `valueOut`'s floor
>   is the own bytes plus the entry; Residents' class comment.
>   `NodeCollection.followStreamPointer`, step 5: the swizzle is under the
>   predecessor's monitor, and a pointer that held no handle calls
>   `handleIn`. Without that, a loaded object, whose pointers are null, stays
>   counted without the handles that readers swizzle in.
> * Checked as needed, not changed: startup sets its handle pointers before
>   `register` counts (`createMemoryPointers`, the primordial super root).
>   `linkD` sets D's pointers afterwards; D is counted at its last count, by
>   015-15's design. `resolvePointers` changes pointers just before the
>   record write, where `grown` recounts.
> * To do: the existing tests that expect `getMemSize()` sums
>   (`Residents.testAccounting`, `testCountedApartFromSize`, and
>   `CapacityTester.testBatchOnPinnedLeaf`'s "its values taken") now get +79
>   per object. Then:
>   * a test: a cold restart, all keys read, then over a walk `bytesOf`
>     equals the rule computed apart (`getMemSize + 79 + 32` per handle
>     pointer + values), and clean objects are exact;
>   * mutations: no `handleIn`; the base;
>   * HandleBytesProbe on the base gave `resident bytes 2312775`, 49 percent
>     not counted, as R1;
>   * docs/levels.md, section 7; the gate.
>   Eviction will run more often at a given budget, and is not measured
>   tonight (the entry's recommendation).
> * Base it again on `main` once 015-15 is committed there.

2026-11-03, 20:31 to 20:45, by agent F1-b (016-05), in
`/Users/f/fl/bench/016/015-13b/repo` (a clone of `main` at `04d257c`,
after 015-15 and 015-10; K's commit cherry-picked without conflicts):

* **K's change checked**: `bytesOf`, `handleIn`, the swizzle under the
  predecessor's monitor (`KeyNode.swizzle` and `setPointee` take that
  monitor themselves, so the lock order is as before, and the handle's
  monitor is no longer held at step 5). Every place that sets a pointer
  read (`setPointee`, `swizzle`, `setPointer` in `core/`): the section
  "The fix" above. Kept as K made it, but for valueOut's floor, now
  `bytesWithoutValues` (K's was the own bytes and the entry: a batch on a
  pinned node with handles and values the writer put in, not counted,
  could take its count below its handles' bytes).
* **Tests**: `Residents.testAccounting` and `testCountedApartFromSize`
  with the entry (+79 per object); `CapacityTester.testBatchOnPinnedLeaf`'s
  loop and "its values taken" by `bytesWithoutValues` (its loop would
  have run its 1,000 batches, as `bytesOf` never reaches `getMemSize`).
  New: `Residents.testHandlesCounted` (the rule on one node: entry, a
  handle swizzled in, a dead handle replaced, a value in and out) and
  `CapacityTester.testCountsWithHandles` (2,000 keys of 300 bytes, cold,
  every key read; everything that can go evicted with a budget of 1 byte;
  the budget raised, every key read; each clean resident object counted by
  4.7's rule computed in the test, with literal 79 and 32, and the resident
  bytes the sum of the counts; again after the budget lowered to a third,
  with dead handles in pointers, and after every key read again).
* **Met on the way** (not a fault of 015-13, for the coordinator): right
  after a cold start (startup distance 2,000 bytes), 4 of 77 clean
  canonical key nodes are counted 192 bytes below their bytes, on the code
  before 015-13 too (counted 224, `getMemSize` 416): most likely nodes of
  the startup section, counted at `registerSectionNodes`, whose arrays the
  rerun of the section's transactions grew, and that no write recounts.
  docs/levels.md, section 7's "exact but for the objects that the writer
  changed since their last count" covers them; they stay until their next
  write or their eviction. `testCountsWithHandles` evicts them first.
* **Mutations** (`/Users/f/fl/bench/016/015-13b/mut/mutate.py M1`, run
  in `java/`; then the unit tests of `Residents` and `CapacityTester`): M1, no `handleIn` call:
  `testCountsWithHandles` fails (`object 642997: counted 303, bytes 399`,
  checkCounts). M2, `ENTRY_BYTES` 0: it fails (`object 642997 by 4.7's
  rule, expected 399, got 320`). M3, `bytesOf` without the handles: it
  fails (`counted 399, bytes 303`), and so does
  `Residents.testHandlesCounted` (`Expected 303, got 335`). With the fix
  all pass.
* **R1's HandleBytesProbe** (`items/016-release-2026-2/06-reviews/R1/`):
  on the base (015-10b's jar, the code before 015-13) `resident bytes
  2312775` and 1,151,169 bytes by 4.7's rule not counted, as R1 found; on
  the fix `resident bytes 3463944`, the difference exactly 1,151,169; the
  key node with 30 handle pointers `bytesOf 1839` (800 + 79 + 30 x 32).
* **The gate**: `java/before-commit.sh`, 20:38:59 to 20:40:44: `BEFORE
  COMMIT OK (105 s)`, 1,134 unit tests, 79 f-tests. Then the unit tests of
  `Residents`, `Eviction`, `CapacityTester` and `EvictionReaderTester` 3
  times alone (35 tests, SUCCESS each) and the f-tests of the last three
  (17, SUCCESS). With 015-10's tests among them: unchanged, passing.
* **Rebased** on `main` at `ca02b5e` (015-14: the fast path's acquire
  reads; `NodeCollection`, `KeyNode`, `TopNode`), without conflicts: 015-14
  left step 5's swizzle as it was, and `getPointee`, which `bytesOf` reads
  under the object's monitor, is now an acquire read. `before-commit.sh`
  again, 20:42:29 to 20:44:15: `BEFORE COMMIT OK (106 s)`, 1,136 unit
  tests, 79 f-tests; M1 fails again as above; the four classes' unit tests
  twice, SUCCESS.

2026-11-03, 20:50, by the coordinator (016-05, H5): reviewed, no fault.
`bytesOf` follows 009-02, 4.7; a follow's swizzle into a pointer that held
no handle counts the handle under the holder's monitor, which the reader's
swizzle took already (the writer's now takes it too, uncontended); a dead
handle stays counted until the holder's write or release, so the count does
not drift. Two notes for 2026.2's notes: at a given cache size about a third
fewer objects stay in memory than in 2026.1 (R1's probe), as the handles are
counted now; and the constants (79, 32) are JDK 27's with compact headers
and compressed oops, an estimate on other JVMs. Committed after the
combined gate.
