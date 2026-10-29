012-11. Task: reclaim
=====================

Created 2026-10-27 by Claude (Opus 5.5, Claude Code), with 012-01, for
Frans Lundberg. **Status: done 2026-10-29 02:11** (part 1 done
2026-10-28 23:33, started 22:38; proper from 23:33, paused 23:55 to 01:12);
Q1 (6.4) decided by Frans on 2026-10-29 (option B), done in 6.9;
approved with 012-01 by Frans's go (012-01, 9.1).
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
  duration), 005-61 (the startup distance that spaces iterations), 005-53,
  005-62 (rule 4 by position after a cut, proved).
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
* A start after a cut: `NodeCollection.linkToCanonical` skips the stream
  pointers of D's nodes below the stream's first position
  (`pos < nodeStream.getFirstPos()`), which 005-62 proved right in Lean;
  C's startup (012-10) does the same, and the runs in turns with cuts
  check it.
* A step's size depends on the step reserve (`setStepReserve`, counted in
  index nodes followed, at `80 + 48 * maxNodeSize` bytes each) and on the
  approximate size of the KVs it scans (`key.length * 8 + value.length +
  100`): both are fixed formulas, so C gets the same steps by porting
  them, not by measuring its own memory.


# 6. Progress

## 6.1 The split

The conductor split 012-11 in two, so that reclaim runs beside 012-10
(startup, another agent, in `/Users/f/fl/bench/012/10-startup/`):

* **Part 1** (this agent, in `/Users/f/fl/bench/012/11-reclaim/`, a clone
  of `main` at `17c0ea3`): reclaim in a running C database, without
  restarts. Done items 1 (iterations and steps, the touch, the step
  reserve), 2 (the table and the current row's key, written as Java writes
  them; reading them back at a start is part 2), 3 (safe positions, the cut
  decision, the first available lookup time and position, the front files
  deleted in the calls when the bytes the cut needs are durable; 012-01,
  4.3), 4 (the reads' refusals before the cut), 5 (the settings and
  reclaim's status), and 6 for the workloads without restarts:
  `StreamDigest`'s Level 3 configurations in their plain and reads modes,
  random workloads with retain durations and setter calls; C's bytes from
  the decided cut, its first available position and time, equal to Java's.
  `cross.sh` compares the workloads with reclaim from the decided cut, not
  file by file (012-01, 3.2 point 8; 012-02, C2 and Q1; 005-72's
  recommended option), and keeps the file comparison for the others.
* **012-11 proper** (after 012-10): what needs a start: a table written by
  Java continued in C after a restart and the reverse (done item 2's
  second half), each other's cut databases opened (done item 7), the
  workloads with restarts (`StreamDigest`'s restarts mode, `CoreSame` as
  it is), and the runs in turns with cuts.

Part 1 changes `db.c` and `api.c` only for reclaim's hooks and settings,
in functions of their own where it can, and puts reclaim in a module of
its own, `reclaim`; 012-10 changes `db_open` and adds startup modules. The
conductor merges the two.

## 6.2 Part 1's progress

* 22:38: started; read 012-01 (1, 3, 4, 6), this plan, 012-02 (8.1, 8.13,
  9, 10.3, 15.2), 012-09 (6.5 to 6.9), 012-05 (6), `c/readme.md`, Java's
  `Reclaim`, `CutStream`, `FileStream.pretruncate`, `Db` (the marking,
  `putKvs`, `touchRange`, `executeInner`, the reads' refusals,
  `getTrans`), `Trans`, `NodeCollection.MaintenanceFollower`, `Gen`,
  `Export`; and 012-10's clone (read only): it has its own
  `init_from_db` in `db.c`, which refuses a database with the table.
* 22:47: the port (section 6.3's decisions): `src/reclaim.c` and `.h`
  (`Reclaim` line for line), the touch in `db.c`, `stream_pretruncate`
  (`FileStream`'s and `CutStream`'s cut), `plat_unlink`, the settings and
  status, `getTrans` of a removed record, `bergdb-run` without its exit 3
  for reclaim. **The first byte check**: five workloads
  (`sd-l3-node14-plain-n600`, `sd-l3-every1-plain`, three Gen seeds with
  retain 1 and 2 s, one with node size 8 and startup distance 100),
  Java's `Run` against `bergdb-run` of the test build: the same output and
  the same bytes from the decided cut at the first try (the files the same
  too). Commit `cf955fe`.
* 22:50: a batch by hand (scripts in the scratchpad): `StreamDigest`'s
  four Level 3 configurations in plain and reads (8, full size) and 123
  Gen seeds without restarts (1000 to 1060 with drawn retain durations,
  2000 to 2040 with 2 s, 3000 to 3020 with 1 s, node size 8 and startup
  distance 100): **131 of 131 the same** (outputs and bytes from the
  decided cut); 95 of them reclaim, 83 with a cut decided.
* 22:52: unit tests (`test/unit/t_reclaim.c`, 10 tests): the row's text
  against `StringMap`'s order (`sm_serialize`) and 012-02, 8.13's
  example; Java's `IterationInfo` tests (`testSerialize1`, `2`,
  `testDeserializeWithBadString`) and old rows' defaults; the table's text
  and parse; the settings; `Reclaim.Tester`'s tests without a restart,
  ported (`testIterationRewritesAllOldValues` with `testCutPointBeforeScan`:
  every live value at or after `pCut` when an iteration is done, `pCut` the
  pStart before, values spared; `testIterationsSpacedByRetention` with
  005-61's `setStartupDistance` check; `testLookupsFromFirstAvailableTime`
  without its restarts: after three cuts, getOne at every 25 ms from the
  first available time equals a model, getOne and getMany before it are
  refused, and the read of the first record below the cut is
  `ReadBelowFirstPosException`; `testStepReserveSplitsSteps` without
  eviction: four nodes split steps, the default none; the table read back
  by `rc_init_from_db` equals the table in memory); the allocation failures
  in turn over the run up to the first cut (315 runs: 171 refused with
  NOMEM and then executed, 144 failed databases; every close frees all).
  Functional test (`test/func/f_reclaim.c`, through `bergdb.h` only): a
  directory, 6,000 transactions with retain 1 s and a sync every 20: 33
  cuts, the directory at most 430 kB in the second half of a 6.8 MB stream;
  the stats, the refusals (getOne, getMany, getTrans of a removed record),
  the settings' checks, and forever: no cut after it.
* 22:55: `cross.sh` (section 6.3, decision 9): `cross.sh quick C=build/test`
  **OK, 20 workloads, side B's runs: C's of 12, 4 of them with reclaim**,
  0 differences (46 s).

* 23:00: **Java's bytes with split steps**: `Vectors.java` writes
  `reclaim.txt` (two runs of `Db` on a `MemoryStream`, node size 8,
  startup distance 2000, retain 1 s, 2,000 puts from a formula, with the
  default step reserve and with one of four nodes, which
  `testStepReserveSplitsSteps` uses: the length, the first available
  position and time, the iterations, the SHA-256 of the stream from the
  cut); `t_reclaim.c`'s `reclaim_java_vectors` runs the same in C: equal
  (the first try differed only in the meta blocks' database id: the test's
  open lacked `testSetup`'s `TEST_ID`; fixed in the test). The workloads of
  the cross sets do not split steps (the default reserve, 4 MiB), so this
  is the check of the split's bytes.
* 23:00: two hand-written workloads with a sync every 25 and 50
  transactions, so that the physical cut is made in C's runs too
  (`test/cross/workloads/reclaim-sync.wl`: 3,000 transactions, retain 1 s,
  node size 8, a `check 1` that is unavailable, `setretain` and
  `setfraction`; `workloads/full/reclaim-sync-large.wl`: 15,000
  transactions, values to 3 kB, startup distance 100,000, `setsd`,
  `setretain forever` and back): Java's and C's outputs and bytes from the
  decided cut the same, and both directories cut (files from 3,000,000 and
  37,000,000 on).
* 23:02: **mutations** of reclaim, each in a copy of `c/` against Java on
  9 to 12 workloads (5 of 22:47's, `gen-2003`, `gen-3004`,
  `sd-l3-node8-plain`, `sd-l3-node62-reads`, and for the later ones two Gen
  seeds with retain 20 and 10 s and `reclaim-sync`): `eod` set when the
  count stops at the last pair (012-02, 15.2 finding 12): 8 of 9 differ;
  the row's `rewritten` without `dirtiedBytes`: 9; the touch's marks not
  kept at `endOfTrans`: 8; `pCut` = `pStart`: 9; no touch: 9; values
  rewritten by `pStart`, not `pCut`: 9; the step's size without the key's
  `* 8`: 8; no iteration spacing: 1 of 12 (it binds only with a long
  retain duration; `reclaim_iterations_spaced` checks it too);
  `pSafe` set without the startup position: 4 of 12; the cut without the
  meta block's check: 9 of 12; the first available time `tStart`, not
  `tEnd`: 12 of 12. Unmutated: 0.

* 23:07: `cross.sh quick` Java against Java (without `C=`): **OK, 21
  workloads** (with `reclaim-sync.wl`), 0 differences (112 s): the
  comparison from the decided cut keeps Java's own runs equal.
* 23:15: beyond the sets, by hand (the scratchpad's scripts, `bergdb-run`
  of the release build against Java's `Run`): 200 Gen seeds without
  restarts, 5001 to 5100 with retain 3 s and 6001 to 6100 with retain 2 s,
  node size 8 and startup distance 100: **200 of 200 the same** (outputs
  and bytes from the decided cut), 175 of them with a cut decided (four
  runs were made again: a rebuild of the release build during the batch
  took their tool away, exit 127; again, the same).
* 23:03: `cross.sh full C=build/test` started in a run-only clone
  (`c/build/fullrun/`, a `git clone` of this clone at `615d7fc`, ignored by
  Git): 445 workloads.

* 23:33: **`cross.sh full C=build/test`** (the run clone at `615d7fc`):
  `CROSS full OK: 445 workloads, 1262 crash cuts, 498 corrupt variants, 6
  in turns, the planted difference at 1164 was found and explained; side
  B: .../build/fullrun/items/012-bergdb-c/c/build/test; 1828 s`; side B's
  runs: C's of 230, **102 of them with reclaim**, Java's of 215 (restarts);
  compared: 0 differences. The gate on the final part 1 code (`0f27af9`):
  `C BEFORE COMMIT OK (93 s)`, 315 unit tests, 5 functional tests, the
  quick set with 5 reclaim workloads run by C. **Part 1 done.**
* 23:33: the conductor: 012-10 is in `main` (`e1507b9`); pull it, keep
  both sides (012-10's for the start), gate, and **go on into 012-11
  proper** (the change of scope): the table restored at a start, cut
  databases opened by the other side, reclaim with restarts and in turns.
  A pause is expected about 23:55, for another session's timed run until
  01:50. Merged (`1e593f6`): 012-10's `init_from_db` (which refused the
  table) replaced by `rc_init_from_db` in `db_open`'s start; `run.c`
  without any exit 3; `cross.sh`'s `c_runs` "one segment or no reclaim"
  until reclaim with restarts is checked; the tables of unit and
  functional tests both sides'. Unit 340 tests, functional 8: OK.

## 6.3 Part 1's decisions

1. **The module** `reclaim` (`rc_`, `src/reclaim.c` and `.h`): `Reclaim`
   line for line, its state (the table, the settings, the first available
   time and position, the pending cut) in `struct reclaim`, a field of
   `struct db`. `db.c` keeps to the hooks: the touch (`touch_range`,
   `Trans.dirtiedBytes` in `make_dirty_if_needed`, the touch's marks kept
   at `end_of_trans`), the call of `rc_transaction_completed` at the end
   of `db_execute` (a failure there fails the database, as Java's
   `fail(t, e)`), the settings and the first available time and position
   delegated, `rc_init_from_db` at the open; `api.c`: the stats and
   `getTrans` of a removed record (`LookupTimeNotAvailableException`, as
   `Db.getTrans`). `trans.h`: `Trans.touch`, `touchFrom`, `touchTo`,
   `dirtiedNodes`, `dirtiedBytes`, and the builder's `put` and `keyRead`
   of segments.
2. **The row's text is written directly**, in the order of `StringMap`'s
   `HashMap` for its 11 names (012-02, 8.13), so that the step's value
   transformation, which cannot fail in C, needs no allocation; its buffer
   is allocated before the step's transaction. `t_reclaim.c` checks it
   against `sm_serialize`. Rows are read with `sm_parse`
   (`IterationInfo.deserialize`, its errors as `InternalDataException`).
3. **The maintenance follower** wraps the readers' follower and counts the
   index nodes it follows by id (an open-addressing set). Without restarts
   and eviction every node is in memory, so the readers' follower serves
   as Java's `memoryObject` path. Java's follower does not swizzle or
   install a version it reads from the stream: with 012-10's node table and
   stream pointers, 012-11 proper must keep that (no byte depends on it;
   memory does).
4. **The cut** (`stream_pretruncate`): for a directory, `FileStream`'s rule
   (the files that end before `pCut` taken off, the first position the
   next file's start), and the files deleted in the call, oldest first,
   the directory forced after each (005-46's thread's work; C has no
   thread). A memory stream cuts exactly, as `CutStream` (the tests'
   stream). A failed delete is the stream's failure, as Java's.
5. **When the cut is made**: as Java's `cutIfDurable`, at a user
   transaction when the durable length has reached the length at the
   decision. C's stream is durable after a sync and at the close (012-01,
   4.3), so C cuts at the first user transaction after a sync that covered
   the decision; without syncs the cut waits, and a cut pending at the
   close stays pending, as in Java, for the next start's `initFromDb`
   (part 2). C's files after a cut may so differ from Java's (C2); the
   bytes from the decided cut do not. **Changed on 2026-10-29** by Q1's
   option B (6.4, 6.9): C forces the stream itself for a pending cut.
6. **The step reserve** is `db_config.step_reserve`
   (`DbBuilder.reclaimStepReserve`, a test setting; 0: 4 MiB), not in
   `bergdb.h`, which leaves the builder's test settings out (012-03, 6.3).
7. **Statistics**: Java's `Stats` (off unless `enableStats()`) is left
   out, but for two counters for the tests, the steps and the split steps.
8. **`rc_init_from_db`** is written whole (the table, the current row, the
   cut row, a cut that the table marks and the stream does not show) and
   called at the open, where a new database has no table. 012-10's clone
   has its own `init_from_db` in `db.c`, which refuses a database with the
   table: at the merge it becomes a call of `rc_init_from_db`.
9. **`cross.sh`**: `c_runs` takes every workload of one segment (reclaim
   or not); for a workload that may reclaim (`retain_of`), `compare_db`
   compares the stream's bytes from the decided cut and the other files
   (`compare_stream`) instead of the files (`compare_dirs`), in the main
   comparison, after the dumps, in the turns and for the planted
   difference; the views of both sides start at the same position (the
   larger of the two sides' starts of the file that holds the cut) and are
   cut where side A's files begin (`split_view`), so the four scans and the
   corrupt variants work as before. The workloads without reclaim keep the
   file comparison. The dumps of databases with reclaim's table stay
   Java's (C's dumper replays, 012-08; 012-11 proper). New workloads: quick
   `sd:l3-node14:plain:n=600`, `sd:l3-every1:reads:n=400`,
   `gen:7:n=400,restarts=0,retain=1`,
   `gen:8:n=300,maxnode=8,sd=100,restarts=0,retain=1`; full: Gen 301 to
   340 `restarts=0` (drawn retain durations), 341 to 380
   `restarts=0,retain=2`, 381 to 400 `maxnode=8,sd=100,restarts=0,retain=1`.

## 6.4 A question for Frans: when C's cut frees the disk

**Decided by Frans on 2026-10-29: B, as recommended ("Do as
recommended"); done in 6.9.**

**Q1.** Java's buffer thread writes and forces the stream within 20 ms, so
a decided cut is made at one of the next transactions, and the directory
stays within about 1.25 times what the retention needs, whether the
application syncs or not. C has no thread (012-01, 4.2, 4.3): its stream
is durable after `bergdb_sync` and at the close, and part 1 makes the cut,
as Java's `cutIfDurable`, at the first transaction at which the durable
length has reached the length at the decision. An application that never
syncs never gets a cut while it runs; its directory grows until the next
start, which makes the pending cut (`initFromDb`). The bytes are the same
either way (C2).

* **A. As now**: the cut waits for the application's sync; `bergdb.h`
  says that reclaim frees the disk only after syncs (or a restart).
* **B. C syncs for the cut**: when a cut is pending and the stream is not
  durable up to the decision, `cutIfDurable` syncs the stream itself (one
  `F_FULLFSYNC` per cut, a few per retention period: an iteration starts
  at most every quarter of the retain duration) and cuts. Java's bound on
  the directory holds without the application's syncs; the cost is a
  force in the call that happens to make the cut.
* **C. A time rule**: 012-01, 4.3's possible improvement (write the buffer
  at the start of a call when the buffer time has passed), with a force:
  closest to Java's timing, but a force in many calls.

**Recommendation: B**, after 012-11 proper: one force per cut keeps
Level 3's bound on the directory, and the decision of when to cut stays
Java's. Part 1 does A, which is Java's rule read literally.

## 6.5 For the conductor: the merge with 012-10

**Done** in this clone at 23:33 (`1e593f6`, `main` at `e1507b9` pulled
on the conductor's word), as below; then 012-11 proper made `c_runs` take
every workload and `sdb` read the table (6.7). Kept for the record. 012-10's
clone (read at 23:05, `acfd03a`) and this one changed the same files in
places; what part 1 needed from the merge:

* **`db.c`, the start**: 012-10's `init_from_db` (it reads the table and
  refuses a database that has one) becomes a call of
  `rc_init_from_db(db, e)`, which reads the table and the current row and
  sets the first available position and time, and makes a cut that the
  table marks; 012-10's handling of `ERR_FAILED` there stays. `rc_init`
  right after the `memset` of `db_open`, before any return that calls
  `free_all` (which calls `rc_free`). Part 1's `db_open` sets
  `db->reclaim.retainDuration` and `stepReserve` from the config and drops
  the forever-only refusal.
* **`db.h`**: `struct db` loses `retain_duration` and `internal_fraction`
  (reclaim's own now) and gains `struct reclaim reclaim`; `struct
  db_config` gains `step_reserve`.
* **The followers**: part 1's maintenance follower wraps the readers'
  follower (`reclaim.c`, `maintenance_follow`); with 012-10's node table
  and stream pointers that follower loads, swizzles and installs, which
  Java's `MaintenanceFollower` does not (012-10's `ncoll.h` leaves it to
  012-11). No byte depends on it; 012-11 proper writes
  `nc_follow_maintenance` (by the version's position, a map of its own,
  no swizzle, no install, the ids counted) and uses it there.
* **`tools/run.c`**: 012-10 drops the exit 3 for restarts, part 1 the one
  for reclaim. **`cross.sh`**: 012-10's `c_runs` is "no reclaim", part 1's
  "one segment"; until 012-11 proper has checked reclaim with restarts,
  the merged `c_runs` should be "one segment or no reclaim" (and side B's
  turns of a workload that reclaims stay Java's, as 012-10 has them).
  Part 1's other `cross.sh` changes (`compare_stream`, `compare_db`,
  `split_view`, the views of workloads that reclaim, the new workloads)
  do not overlap 012-10's.
* **Not this task's files**: 05-cross-harness.md, 6.5 should say, as
  `cross.sh` is at 012-11's end: the comparison of a workload that
  reclaims is of the stream's bytes from the decided cut and the other
  files (`compare_stream`, `compare_db`: in the main comparison, after the
  dumps, after a crash copy's recovery and its run, in the turns and for
  the planted difference); its views start at a common position, cut at
  side A's file boundaries (`split_view`); every run and dump of side B is
  C's with `C=` (`c_runs` answers 1 and is kept as the place to send a
  kind of workload to Java); a workload that reclaims has crash variants
  only with `C=`, copies of side B's directory from the length at its last
  sync on (6.7, 01:20); and the new workloads (decision 9;
  `reclaim-sync.wl`, `reclaim-crash.wl`, `full/reclaim-sync-large.wl`;
  quick's turns with `sd-l3-node14-restarts-n600`). 03-c-api.md: the
  comment of `bergdb_set_retain_duration` in `bergdb.h` (forever, and when
  the front files are deleted, Q1).

## 6.6 What 012-11 proper had left

As of 23:45; all done by 01:41 (6.7) but item 7:

1. Done item 2's second half: done at 23:42 (runs in turns with reclaim).
2. Done item 6 with restarts: by hand at 23:40, in the full set at 01:41.
3. Done item 7: C dumps Java's cut databases (`sdb`'s `initFromDb`),
   Java dumps C's with its audit: quick at 23:38, full at 01:41.
4. Reads below the cut: Java's `expiredIfReadBelowCut` serves a read that
   a cut overtakes while it runs; C has one caller at a time and a
   callback may not call its database, so no cut comes during a read, and
   a read before the first available time is refused before it starts. No
   port needed; a note for 012-13's text.
5. The maintenance follower with stream pointers: done at 23:48.
6. Crash tests with reclaim: done at 01:20 (crash variants of C's
   directory from its last sync on; a cut pending at a start).
7. Frans's answer to Q1 (6.4): B, on 2026-10-29; done in 6.9.

## 6.7 012-11 proper's progress

* 23:36: the merged tree (`1e593f6`, 012-10's `main` and part 1):
  **C BEFORE COMMIT OK (101 s)**, 340 unit tests, 8 functional tests, the
  quick set with C's tools. A first probe of reclaim with restarts (the
  release build's `bergdb-run` against Java's `Run`):
  `sd-l3-node14-restarts-n600`, `coresame-n1500` (CoreSame as it is:
  index writes, reclaim, restarts), `gen-3-n300-retain2`, Gen 9 with 4
  restarts and retain 1 s, Gen 10 with 5 restarts, node size 8 and startup
  distance 100: **5 of 5 the same** (outputs and bytes from the decided
  cut): C's start restores the table and the current row
  (`rc_init_from_db`) as Java's does. Next: `c_runs` for every workload,
  side B's turns of reclaim workloads, and the dumps of cut databases by
  C (`sdb`'s `initFromDb`, which still refuses the table).
* 23:38: `c_runs` takes every workload, and side B's turns of reclaim
  workloads are C's; `sdb`'s `initFromDb` (the start that `bergdb-dump`
  uses) reads the table: the first available position and time from the
  row marked cut with the largest pStart (`rc_first_available_of_table`),
  and a cut that the table marks but the files do not show made, as
  Java's start. `cross.sh quick C=build/test`: **OK, side B's runs C's of
  21 (9 with reclaim), its dumps C's of 42**: C dumps Java's cut databases
  and its own, equal to Java's dumps, and Java's audit passes on C's.
* 23:40: by hand (release build against Java's `Run`): `StreamDigest`'s
  four Level 3 configurations in their restarts mode at full size,
  `CoreSame` as it is (6,000 transactions, index writes, reclaim,
  restarts), Gen 7001 to 7060 with retain 2 s and 8001 to 8020 with retain
  1 s, node size 8 and startup distance 100 (drawn restarts: 66 of the 85
  restart): **85 of 85 the same**, 76 with a cut decided.
* 23:42: quick's runs in turns get `sd-l3-node14-restarts-n600` (reclaim,
  segments alternately Java's and C's on one directory: Java's table
  continued by C and C's by Java): `cross.sh quick C=build/test` **OK, 2
  in turns**, 0 differences.
* 23:48: **the maintenance follower** (`ncoll.c`'s
  `nc_follow_maintenance`, `db_maintenance_follower`; Java's
  `MaintenanceFollower` and `followStreamPointer` with `maintenance`): an
  object in memory as the readers' (no touch); else the version read
  without raising the pointer's reference, making a handle, installing or
  swizzling, kept by nothing (freed at the next safe point); Java's map of
  the versions read by position, which saves reads only, left out.
  Reclaim's scan and reads use it, the ids counted as before. The 85
  workloads of 23:40 with the test build (AddressSanitizer): **85 of 85
  the same**; **C BEFORE COMMIT OK (103 s)**.
* 23:55: **paused** on the conductor's word (F53 to another session's
  timed run until 01:50); nothing of this task runs. State: everything
  committed (`750d38c`), the gate OK on it; the run-only clone
  (`c/build/fullrun/`) brought to `750d38c` and built. **Next, on
  resuming**: `cross.sh full C=build/test` in the run-only clone (about 30
  minutes; side B's runs and dumps now all C's, reclaim with restarts and
  in turns included), then this file's done items (section 1) as they
  hold, and 6.6's items 6 and 7.
* 01:12: resumed (F53 free earlier than planned; new hard stop 06:30).
  `cross.sh full C=build/test` started in the run-only clone at
  `750d38c`.
* 01:15: **crashes with reclaim**, by hand first (a script in the
  scratchpad): C runs `reclaim-sync.wl` with its syncs after the 2,900th
  transaction dropped, and copies of C's directory are cut at 32 positions
  from the length at its last sync to the end (valid crashes: C's stream
  is durable after a sync only, so every physical cut it made had its
  decision durable by then; a copy of Java's directory, whose cuts come at
  its own moments, might not be one); each copy dumped by Java and by C
  (each start recovers, reads the table and makes a cut that the table
  marks and the files do not show), then a restart and 20 transactions by
  both: **32 of 32 the same** (dumps, outputs, bytes from the decided
  cut); `reclaim-sync-large.wl` with its syncs after the 9,000th dropped,
  14 positions over 13 MB: **14 of 14**.
* 01:16: functional test `api_reclaim_pending_cut_at_open` (`f_reclaim.c`):
  3,000 transactions with retain 1 s and no sync: no file deleted while it
  runs nor at the close; the next open makes the cut (the first file's
  start after it, at most `pCut`), with the first available position and
  time as before, and reclaim goes on.
* 01:20: **crash variants of a workload that reclaims in `cross.sh`**:
  with `C=`, copies of side B's (C's) directory cut at the chosen and
  random positions from the stream's length at its last sync before the
  end (the rule above); the recovered directories and the runs after
  compared from the decided cut (`compare_db`); without `C=` none (a
  line in the report). New hand-written workload
  `test/cross/workloads/reclaim-crash.wl` (3,000 transactions, retain
  1 s, node size 8, startup distance 2000, a sync every 25 until the
  2,400th), in both sets' `CRASH`. `cross.sh quick C=build/test`: **OK, 22
  workloads, 93 crash cuts** (29 of `reclaim-crash`), 0 differences.
* 01:29: `cross.sh full C=build/test` (the run clone at `750d38c`), its
  comparison: **side B's runs C's of 445, 180 of them with reclaim, its
  dumps C's of 890**, Java's of none; compared in 940 s: **0
  differences**. The crash variants, corrupt variants and turns follow.

* 01:41: the full run's end: `CROSS full OK: 445 workloads, 1262 crash
  cuts, 498 corrupt variants, 6 in turns, the planted difference at 1164
  was found and explained; side B: .../build/fullrun/items/012-bergdb-c/c/build/test;
  1684 s` (C's runs of all 445, 180 with reclaim; C's dumps of all 890;
  crash, corrupt and turns: 0 differences). A last full run on the final
  commit (with `reclaim-crash`'s crash variants) follows.

* 02:11: **the last full run, on the final commit** (`157403e`; the code
  as at the gate's last run, `242918b`, C BEFORE COMMIT OK (130 s), 340
  unit tests, 9 functional tests): `CROSS full OK: 446 workloads, 1368
  crash cuts, 498 corrupt variants, 6 in turns, the planted difference at
  1164 was found and explained; side B: .../build/fullrun/items/012-bergdb-c/c/build/test;
  1751 s`: side B's runs C's of 446 (181 with reclaim), its dumps C's of
  892, 0 differences; the crash cuts with 106 of `reclaim-crash`.
  **012-11 done.**

## 6.8 Done when, as it holds

Section 1's items, with the evidence (6.2, 6.7):

1. **Iterations and steps** as `Reclaim` (`reclaim.c`): the start of an
   iteration (twice the live startup distance, a quarter of the retain
   duration), the step's allowance and size, the maintenance scan with the
   step reserve, the rewrites before `pCut`, the touch, the row stored by
   its value transformation, `eod` as `Dag.getMany` gives it. Checked by
   the bytes (below) and by mutations, each found (6.2, 23:02); the step
   reserve's split steps against Java's bytes (`reclaim.txt`).
2. **The table and the current row's key**, written as Java writes them
   (the row's text against `StringMap`'s order), read back at a start
   (`rc_init_from_db`; `sdb`'s for the dumper); a table written by Java
   continued by C and the reverse: the runs in turns with reclaim (quick:
   `sd-l3-node14-restarts-n600`; full: `sd-l3-node8-restarts`, `coresame`).
3. **The cut**: safe positions, the cut decided as Java decides it (the
   first available position and time equal Java's in every run's status
   lines), the front files deleted as `FileStream` deletes them
   (`stream_pretruncate`; `CutStream`'s exact cut for a memory stream),
   in the calls when the bytes the decision needs are durable (since
   2026-10-29 C forces them itself in the call that decides the cut: Q1's
   option B, 6.4, 6.9), and a cut that the table marks and the files do
   not show made at a start (`api_reclaim_pending_cut_at_open`, the crash
   checks). A long run with a short retain duration keeps the directory
   bounded (`api_reclaim_directory`: at most 430 kB of a 6.8 MB stream;
   with no sync, `api_reclaim_directory_no_sync`: at most 342 kB).
4. **Reads before the cut** refused as Java's: `getOne` and `getMany`
   before the first available time, `getTrans` of a removed record
   (`LookupTimeNotAvailableException`): unit and functional tests, and the
   workloads' `check` lines before the first available time ("check at=T
   unavailable", equal to Java's).
5. **Settings and status**: the retain duration (at least a second;
   forever stops new iterations and cuts, an iteration in progress ends),
   the internal fraction (0.001 to 0.90, NaN let through as Java's), the
   step reserve (a test setting, `db_config`), the iteration count and the
   first available time and position in the stats.
6. **The bytes from the decided cut**: `StreamDigest`'s Level 3
   configurations in all three modes, `CoreSame` as it is, Gen workloads
   with retain durations and setter calls, with and without restarts, the
   runs in turns, and crash copies: equal to Java's in the full set with
   C's tools (181 reclaim workloads, 02:11) and by hand beyond the sets
   (131 + 200 + 85 workloads, 6.2 and 6.7).
7. **Each other's cut databases**: C dumps Java's cut directories (and its
   own) with Java's text, Java dumps C's with its audit on: 892 dumps of
   side B by C in the full set, every one equal.

Q1 (6.4): decided by Frans on 2026-10-29 (B) and done (6.9); the rule of
when the disk is freed is in `bergdb.h` (`bergdb_set_retain_duration`) and
in `c/readme.md`, section 9, point 9.

## 6.9 Q1 decided: option B (2026-10-29)

Frans decided Q1 (6.4) on 2026-10-29 ("Do as recommended"): **option B**.
Done by a subagent of 012's conductor in `/Users/f/fl/bench/012/16f/` (a
clone of `main` at `57aaf9f`).

Progress:

* 07:36: started; read 6.4, `c/readme.md` 9, 012-14's 6.8, Java's
  `Reclaim.cutIfDurable`.
* 07:45: `cut_if_durable` (`reclaim.c`) forces the stream itself when a cut
  is pending and the stream is not durable up to the decision
  (`stream_sync`), then cuts; `bergdb.h`'s comments; `bergdb-run -mem`
  gives the durable length; `cross.sh`'s crash variants of a workload that
  reclaims start at C's durable length at the end; functional tests
  `api_reclaim_directory_no_sync` (new) and `api_reclaim_pending_cut_at_open`
  (reworked). The C gate next.

* 07:48: **C BEFORE COMMIT OK (167 s)**: 345 unit tests, 24 functional
  (`api_reclaim_directory_no_sync`: a 6.8 MB stream, no sync, 103 cuts
  decided, 103 forces, none else, files deleted in 33 of them, the
  directory at most 342 kB in the second half; with a sync every 20
  transactions, `api_reclaim_directory`, 410 kB), the quick set with 82
  crash cuts (93 before: `reclaim-crash`'s window, from C's durable length
  at the end, is now the last cut's decision to the end, 53 kB, where it
  was the last sync to the end, 665 kB). `cross.sh full C=build/test`
  started at 07:49. Docs: `c/readme.md` 9 (points 1, 2, 7, 9),
  `bergdb.h`'s comments, 03-c-api.md's change list.
* 08:29: `cross.sh full C=build/test` on `8e62a25` (the code as at the
  gate): `CROSS full OK: 446 workloads, 1357 crash cuts, 498 corrupt
  variants, 6 in turns, 1784 budget runs, the planted difference at 1164
  was found and explained; side B: .../16f/items/012-bergdb-c/c/build/test;
  2468 s` (0 differences in the comparison, the crash variants, the corrupt
  variants, the turns and the budget runs). The long run next.
* 09:45: **the long run** (`test/stress/long.sh 2 1000000 4000
  retain=1,restarts=50,sd=50000,huge=1,setters=10`, 012-14's million-transaction
  run, 6.8 there; output in `/Users/f/fl/bench/012/16f-out/long/`): the test
  build's and Java's runs exit 0 in 484 s, C's text is Java's, and the
  stream from the decided cut and the other files are Java's (both C
  builds); no sanitizer report. **The directory's peak (sampled every
  2 s): C's test build 25.2 MB, Java's 34.2 MB**; before this change, C's
  was 206 to 213 MB against Java's 36.5 MB (012-14, 6.8). The release build
  alone, sampled the same way (170 s): at most 25.2 MB, 7.2 MB at the end,
  its text Java's. The release run under `leaks --atExit` finished its
  text but `leaks` hung at its exit (the process stopped, state T, 0 % CPU
  for an hour; killed on the conductor's word), so `long.sh` printed LONG
  RUN FAILED for the leak check alone. Since about 08:30 `leaks --atExit`
  hangs on this machine for every program: a 20,000-transaction run in the
  foreground, and `build/release/unit` itself (both stopped at exit, killed
  after 2 to 3 minutes); at 07:48 the gate's leak steps passed. So no leak
  figure for this change beyond the gate's (its `unit-release` and
  `func-release` steps under `leaks`, 0 leaks, on the code as it is now:
  only these documents changed after `152d6e9`), and the gate cannot be
  run again until `leaks` works.
