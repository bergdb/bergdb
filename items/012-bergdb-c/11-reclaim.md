012-11. Task: reclaim
=====================

Created 2026-10-27 by Claude (Opus 5.5, Claude Code), with 012-01, for
Frans Lundberg. **Status: draft, for Frans's approval with 012-01.**
Phase D (012-01, section 8). Effort: max. After: 012-10.


# 1. The goal

Level 3 in C: reclaim as `Reclaim` does it, so that the stream's front is
cut as in Java, the records reclaim writes are Java's bytes, and each
implementation opens the other's cut databases.

Done when:

1. **Iterations and steps** as `Reclaim`: an iteration starts when the
   stream has grown by twice the startup distance (the database's live
   one, 005-61) and a quarter of the retain duration has passed; each
   external transaction allows a step within `internalFraction` of the
   growth; a step rewrites the live values stored before the cut point
   and touches the key range (`Trans.touch`); the row of the iteration is
   stored with the step; the step reserve.
2. **The table** under `/#i/dreclaim/-table.txt` and the current row's
   key, as `StringMap` text, read and written as Java does; a database
   with a table written by Java continues in C, and the reverse.
3. **The cut**: safe positions, the wait for the startup position, the
   cut at `pCut` when `tEnd` is older than the retain duration, the first
   available lookup time and position, and the front files deleted, as
   `FileStream` deletes them (`CutStream` for the memory stream). With no
   thread, the cut is made in the calls, when the bytes it needs durable
   are durable (012-01, 4.3).
4. **Reads before the cut** are refused as Java refuses them: `getOne` and
   `getMany` with a lookup time before the first available one,
   `getTrans` of a removed position (NOT_AVAILABLE).
5. **Settings**: the retain duration (at least one second) and the
   internal fraction (0.001 to 0.90), and their getters; reclaim's status
   (`getReclaimIterationCount`, the first available time and position).
6. **The bytes**, from the decided cut (012-01, 3.2, point 8):
   `StreamDigest`'s Level 3 configurations in all three modes, `CoreSame`
   as it is (index writes, eviction, reclaim, restarts), random workloads
   with retain durations, setter calls, and runs in turns: C's files and
   bytes from the decided cut equal Java's, and so do the first available
   position and time.
7. **Each other's cut databases**: Java's open in C and C's in Java, with
   equal dumps.


# 2. Read first

* Java: `Reclaim` (714 code lines, and its class comment, the rules
  above), `CutStream` (68), `StringMap` (68), `FileStream`'s cut and
  deletes, `Db.getFirstAvailableLookupTime` and the reads' refusals,
  `Trans.touch`.
* `docs/levels.md`, Level 3; 001-07 (the alignment of Level 3), 011-07
  (its durability), 011-04's W1 and W2 (reads and the cut, the retain
  duration), 005-61 (the startup distance that spaces iterations), 005-53.
* `java/stress/ReclaimStress.java`, `ReclaimReaders.java`, and the
  testers `ReclaimRetentionTester`, `ReclaimReaderTester`.


# 3. The work

1. `StringMap` and the table, with unit tests on Java's texts.
2. Port `Reclaim`: the listener at each transaction's end, iterations,
   steps, the touch, the safe positions, the cut. Its floating point as
   012-04's rules say (012-01, 3.2, point 4).
3. The cut in the storage: the directory's front files, the memory
   stream's first position.
4. The comparisons, first without restarts, then with, then in turns.
5. The functional tests of the refusals and of the settings.


# 4. Tests

The comparisons of done items 6 and 7 on the quick and full sets; Java's
reclaim tests ported where they apply; a functional test that a long run
with a short retain duration keeps the directory's size bounded.


# 5. Notes

* Reclaim's records are ordinary transactions to the rest of the
  database, so the write path and startup of 012-09 and 012-10 carry over;
  most differences, if any, will be in the decisions of when to iterate,
  step and cut.
* With no thread, C's physical cut may come at another moment than
  Java's; only the decided cut is compared (012-01, 3.2, point 8).
* A step's size depends on the step reserve (`setStepReserve`, counted in
  index nodes followed, at `80 + 48 * maxNodeSize` bytes each) and on the
  approximate size of the KVs it scans (`key.length * 8 + value.length +
  100`): both are fixed formulas, so C gets the same steps by porting
  them, not by measuring its own memory.


# 6. Progress

Not started.
