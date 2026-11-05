015-67. Fix: a batch processes a whole map even past its handle limit
=====================================================================

Status: done 2026-11-05, night 006-12. Kind: Fix. Created 2026-11-04 by Frans Lundberg.

After release 2026.2 (a known issue of it); in 2026.1 too.

What: review R4's finding R4-F2 (items/016-release-2026-2/06-reviews/R4.md,
section R4-F2: where, intended, actual, effect, a proposed fix), shown by a
probe in 06-reviews/R4/. No second agent has checked it yet.

Done when: a test that fails on the code before the fix passes, and the
fix is in `main` after `before-commit.sh`.

First step: verify it (016-06, section 2.6), then the probe made a test.


Log
---

2026-11-04. Registered by the coordinator of release 2026.2 (016-02).

2026-11-05. Done in night 006-12 (W1). Verified: R4-F2 holds on the code
of the night's start. `Eviction.sweep` checked its handles, maps and time
before each CLOCK step, and a step (`Cache3.clockStep`) took a whole map
of the node table under its lock, whatever its size; a map has no maximum
size (about the resident index nodes / 4,096), so one batch's work grew
with the resident set.

* Fix: a map with more handles than the batch has left to examine is
  taken in parts. `clockStep(k, d, pinned, max)` takes map k whole, as
  before, if it has at most `max` handles, else returns null; the batch
  then copies the map's handles (`Cache3.mapHandles`, under its lock) and
  takes them from the copy in parts (`clockStep(k, part, from, to, ...)`),
  each handle under the map's lock as before, one that has left the map
  since the copy skipped; the copy and the next index (`Eviction.part`,
  `partNext`, under the write lock as the hand) stay for the next batch,
  which goes on where this one stopped. The hand moves on, and the map
  counts as taken (the round, the stop rule's maps), when its last part is
  done. A handle added to the map after the copy is met in the hand's next
  round, as a CLOCK step meets any handle once a round. The copy, a
  reference a handle, is the one work that grows with a map. A batch now
  examines at most its handles (4,096, or 65,536 under pressure); before,
  it could pass them by up to a map, as a step began whenever fewer had
  been examined. The pinned objects' values (`unswizzleValues`) are
  bounded with the handles: one node's pointers each.
* Javadoc of `BATCH`, `sweep`, the class and the `clockStep`s; docs/levels.md,
  section 7 (the capacity controller).
* Test: `Eviction.testBatchWithinItsHandlesInALargeMap` (unit group), R4's
  probe made a test: 5,000 detachable key nodes in map 0, budget 9/10 of
  the resident bytes (not under pressure), one batch from map 0. Before
  the fix it released 5,000 objects; after, at most `BATCH` (4,096), with
  map 0 unfinished, and the next batch (under pressure) takes the rest.
* P1 to P12 (010-01): P1 and P4 are what the fix restores (bounded
  eviction work); no new setting, thread, wait or API. Eviction does not
  change the stream's bytes (the twin tests compare streams with and
  without eviction). Gates: `before-commit.sh` and `level4.sh` (full).
