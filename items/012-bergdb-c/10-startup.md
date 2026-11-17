012-10. Task: startup and recovery
==================================

Created 2026-10-27 by Claude (Opus 5.5, Claude Code), with 012-01, for
Frans Lundberg. **Status: done, 2026-10-28 23:23** (started 21:35 as part 1
of a split, 6.1; from 22:19 the whole task, 6.2), by a subagent of 012's
conductor in the clone `/Users/f/fl/bench/012/10-startup/`, for the
conductor to check and copy in; approved with 012-01 by Frans's go
(012-01, 9.1).
Phase C (012-01, section 8). Effort: max. After: 012-09.


# 1. The goal

C opens existing databases as Java does, with bounded startup (Level 2),
and recovers after a crash: it rebuilds exactly what Java has in memory
after its startup, so that the next records are the same bytes. With this
task, Levels 0 to 2 are done and milestone M3 is reached.

Done when:

1. **Recovery**, as `RecoverableStream`: the last valid meta block, the
   last whole record after it, the torn record's fill, an incomplete
   creation refused (`DatabaseNotCreatedException`, 005-33), and what a
   start writes and does not write.
2. **The start's checks**, as `Db.startInner`: the formats, the node size
   (005-50), the database id, the startup distance taken from the stream.
3. **The startup**, as `DbStarter` and `NodeCollection`: the startup
   section read from the last record's startup position, its nodes and
   positions (`posMap`, `newById`, `posToId`), the key nodes cut back to
   the startup time, Rule R, the memory pointers, the super root at the
   startup time from `topPos`, the section's transactions rerun so that D,
   the take's state (`TransSeq`: since `b8ac8a1` also each transaction's
   own bytes, the sums D and O and their checksum, and the span) and the
   startup position are as Java's, and rule 4 by position (005-57) in
   `linkToCanonical`.
4. **Loads**: a node not in memory is read from the stream when a read or
   a write follows a stream pointer, as `NodeCollection` does it, Rule R
   included.
5. **The bytes after restarts.** `StreamDigest`'s third mode (restarts)
   for its Level 2 configurations, and random workloads with restarts:
   C's files equal Java's.
6. **In turns.** The same workloads run with Java and C taking turns at
   every restart: the files equal those of Java alone and of C alone.
7. **Crashes.** 012-05's crash variants: C and Java recover each cut copy
   to the same bytes, give the same dumps, and write the same bytes after
   it.
8. **Java to C.** C opens every database of the sets without reclaim with
   its bounded startup, and its dump equals Java's; full replay (012-08)
   is no longer used to open a database.


# 2. Read first

* Java: `DbStarter` (501 code lines), `NodeCollection` (456),
  `RecoverableStream` (its recovery), `Db.start` and `startInner`,
  `StartupPos`, `StartInfo`.
* `docs/sis-model.md` (startup, Rule R, D, T1 and T2), 011-11 (the Level 2
  alignment, M18 on `topPos`), 005-57 (rule 4 by position) and 005-58
  (its proof), 005-32 (a start that throws), 005-33 (an incomplete
  creation), 005-40 (formats checked before anything is written), 007-01
  and 007-05 (what startup costs).
* `java/stress/RestartInvariance.java` and `CrashTest.java`.


# 3. The work

1. Recovery first, with the crash variants: C recovers each copy as Java
   does (bytes and dumps), before any startup logic (open, recover,
   close).
2. Port `DbStarter` and `NodeCollection`'s startup and loads, keeping
   Java's order of steps.
3. The restart comparisons: one restart, then a restart after every
   transaction (`StreamDigest`'s `l2-every1`), then the random sets.
4. The runs in turns: the strongest check of the rebuilt state, as a
   difference in D or the take shows in the next record.
5. Java's databases opened with bounded startup, and `bergdb-dump` on
   them.


# 4. Tests

The comparisons of done items 5 to 8 on the quick and full sets;
functional tests of a restart after every transaction, of a crash cut at
every position of a small stream (C alone, against C's own dumps), and of
the refusals (another format, another node size, an incomplete creation).


# 5. Notes

* The hardest task of 012 (012-01, section 10). A difference after a
  restart is a difference in the rebuilt state: compare C's D, the take's
  queue and the startup position with Java's at the same point. A small
  Java probe that prints them (in the harness, package `bergdb.core`, on
  the internals through `Db.internal()`) and a C counterpart help; they
  are tools of this task, not part of the API.
* What startup reads is bounded by the startup distance (Level 2). C must
  not read more than Java, as that would hide a difference in the section.


# 6. Progress

## 6.1 The split

012's conductor split this task in two on 2026-10-28, so that the parts
that do not need 012-09's write path start beside 012-09 proper (another
agent, in `/Users/f/fl/bench/012/09-proper/`):

* **Part 1** (a subagent, in the clone `/Users/f/fl/bench/012/10-startup/`,
  a clone of main at `8a7ceb9` with 012-08's final work merged, `3d1b4f5`;
  started 21:35):
  1. **Recovery** (done item 1), as `RecoverableStream`: the last valid
     meta block, the last whole record after it, the torn record's fill
     written as Java writes it (on 012-09 part 1's appends, `rstream`,
     `stream`), an incomplete creation refused
     (`DatabaseNotCreatedException`, 005-33), what a start writes and what
     it does not; checked with 012-05's crash variants: C's recovery of
     each cut copy gives Java's bytes.
  2. **The start's checks** (done item 2), as `Db.startInner`: formats,
     node size (005-50), the database id, the startup distance from the
     stream.
  3. **The startup's reading and rebuilding of the index** (done item 3
     but the rerun, and done item 4), as `DbStarter` and `NodeCollection`:
     the startup section from the last record's startup position, its
     nodes and positions (`posMap`, `newById`, `posToId`), the key nodes
     cut back to the startup time, Rule R, the memory pointers, the super
     root at the startup time from `topPos`, rule 4 by position (005-57)
     in `linkToCanonical`, and the loads of nodes not in memory when a read
     follows a stream pointer, Rule R included. Not part 1: the rerun of
     the section's transactions that rebuilds D and the take's state; this
     file says exactly what it must set, from Java, for 012-10 proper.
  4. **Java to C by bounded startup** (done item 8, for reads): C opens
     every database of 012-05's sets without reclaim with its bounded
     startup (reading only what Java reads), and its dump equals Java's;
     `bergdb-dump` opens by the bounded startup, the full replay kept as a
     test vehicle.
* **012-10 proper** (after 012-09): the rerun's D and take state as part
  of `Db`, the start inside `bergdb_open`, and done items 5 to 7 (the bytes
  after restarts, in turns, after crashes).

Part 1 writes its startup as modules of its own, with an entry point that
012-09's `db_open` can call; it does not edit `db.c` or `api.c`.

## 6.2 Part 1's progress

* 21:35: started; read 012-01 (sections 1, 3, 4, 6), this plan, 012-02
  (sections 4, 8.8 to 8.10, 8.14, 15), 012-07 (section 6), 012-08, 012-09
  (section 6), `c/readme.md`, `docs/sis-model.md` (6.2, 6.3), 011-11
  (sections 4, 8.3), 005-57, 005-58, Java's `DbStarter`, `NodeCollection`
  and `Db.start`/`startInner`, and 012-09 proper's `db.h` and `db.c` (read
  only, in its clone).
* 21:53: the modules (`84a2af8`): `lmap` (a long-to-long map), `ntable`
  (the node table, `Cache3`'s `register`, `install`, `makeCanonical`,
  `liveHandle`, `liveOrNewHandle`, `getNode`, `dropIfEmpty`), `ncoll`
  (`NodeCollection`: the readers' and the writer's followers with the loads,
  Rule R, the cut back during the reconstruction, `resolvePointers`,
  `linkToCanonical` with its check by node id), `recover`
  (`RecoverableStream.recover` with its fill, on 012-09 part 1's
  `rs_append`), `starter` (`Db.startInner`'s checks and recovery, then
  `handleStartParams`, `readTransactions` and `DbStarter` in Java's order,
  the rerun included: decision 1 below), `sdb` (a database opened by the
  bounded startup, for reads: getOne, getMany, getTrans);
  `bergdb-dump` opens by it (`-replay` keeps the full replay); `cross.sh`
  compares each crash copy as both sides' starts recovered it (their
  dumps), before the runs after; `t_sdb.c`: Java's stream of
  `records.txt` started at every cut (the fill as 012-06's plan says, the
  reads as the full replay's at every time, a second start writes
  nothing), Java's refusals, the allocation failures in turn.
* 21:54: `cross.sh quick C=build/tools-q`: **CROSS quick OK**, C's dumps
  by the bounded startup of 14 directories equal Java's, the 64 crash
  copies recovered by C's start equal Java's recovered copies, byte for
  byte (0 differences).
* 21:57: **C BEFORE COMMIT OK (59 s)**, 291 unit tests (`4156d1e`).
* 21:58: the probe (`50ba135`): Java's `StartProbe` (outside the
  repository, `scratchpad/10-startup/probe/`, package `bergdb.core`, the
  main stream wrapped to count its reads) and `bergdb-dump -probe` print
  what a start rebuilt and read: the startup position, D
  (`TransSeq.checksum`: each transaction's `lastPos`, `tt`, `tpos`,
  `startupPos`, own bytes, its got-dirty nodes' types and ids), the newest
  written top node and the super root (id and position), the node table
  (each live handle's id, its object's position, canonical and dirty, as a
  CRC32 of the sorted entries), the followers' loads, and the reads of the
  files (calls and bytes, below Java's `BufferedStream`). On the quick
  set's 14 directories without reclaim (both sides'): **all 14 lines
  equal**, also with Java's `-ea` against C's `-check` (`linkD`'s check by
  node id, which reads a header per pointer). So C rebuilds Java's D and
  node table and reads what Java reads, call for call and byte for byte.
* 22:03: Java's tests ported: `NodeCollection`'s (`t_ncoll.c`: 10 of its
  12, on a source of nodes as Java's `TestStream`; the writer's follower,
  the node table's rules and `lmap` against a model added) and
  `RecoverableStream`'s of `recover()` (`t_recover.c`: its 7 that C has,
  and the meta blocks a fill writes), `739ef88`.
* 22:04: `cross.sh full C=build/tools-full KEEP=1` started (a copy of the
  test build's tools at `739ef88`).
* 22:07: finding F1 (6.4) and its probe; C's `validateTransactions` does
  as Java's.
* 22:09: the probe scripts batched (`compare.sh`: one JVM per node size;
  `compare-crash.sh`: each crash cut of a kept set started by both, which
  recovers it, then the lines and the recovered directories compared). On
  the quick set's 64 crash cuts: **all lines equal and the 64 recovered
  directories equal**: after a crash too, C's start rebuilds Java's D and
  node table and reads what Java reads. (The reads are counted below
  Java's `BufferedStream`, whose thread may write recovery's fill to the
  file during a start, so that a later read of the fill would be counted
  in Java and not in C; it did not happen in these runs, and it would
  change a count, not a state.)
* 22:12: the probe also digests the canonical objects' contents
  (`40e87fe`): each key node's klongs, references and the references the
  record rule would write now (`getSerializedRef`), each top node's
  ordinal, root time and references: equal on the quick set's 14
  directories and 64 crash cuts. So the rerun rebuilds Java's nodes, not
  only their ids. And a creation cut short (`creation.sh`: the first file
  of a quick-set directory cut at 17 positions from 1 to 400): Java and C
  refuse the same 13 (1 to 263, `DatabaseNotCreatedException`, nothing
  written), start the other 4 alike (the primordial startup; at 265, 300
  and 400 the torn record's fill), and the 17 directories are equal after
  the starts.
* 22:13: the largest database of the full set, `sd-l2-default-100MB-plain`
  (77 MB, startup distance 100 MB): Java's and C's probes equal (a section
  of 6,966 records, 46 MB; D of 6,965 transactions; 3,160 canonical
  objects; 301 loads; 15,101 reads of 46,161,336 bytes, the same in both).
  C's start in the release build 0.26 to 0.47 s, 133 MB at most resident
  (it holds the section as Java does); Java's probe 0.71 s with its JVM's
  start (both while the full run's JVMs ran: indicative only).
* 22:15: the probe on the full set's directories (`compare.sh`, the
  directories of both sides of the 177 workloads without reclaim): **all
  354 lines equal**: the startup position, D's checksum, the newest
  written top node, the super root, the node table's entries and the
  canonical objects' contents, the loads, and the reads of the files: in
  all, 344,080 reads of 396,402,792 bytes and 21,344 loads, in Java and in
  C alike. Again with Java's `-ea` and C's `-check` (`linkD`'s check of
  rule 4 by position against rule 4 by node id, 005-57, which reads a
  header per stream pointer of D's nodes): all 354 equal, no check failed
  in either, 409,996 reads of 398,511,784 bytes.

* 22:19: **the change of scope** (the conductor, 22:17): 012-09 is done
  and in main (`1d1e2fb`); at a safe point, commit, merge main, gate, and
  go on past part 1 into 012-10 proper: the startup wired into `db_open`,
  the rerun that rebuilds D and the take's state (part 1 has it,
  decision 1), and done items 5 to 7 (the bytes after restarts, in turns,
  after crashes) with C running the workloads that have restarts. Hard stop
  01:50. Main merged (`ceb462b`: `main.c`'s tables both sides kept;
  `cross.sh` main's with part 1's two changes; `dump.c` part 1's, main's
  being part 1's base; `c/readme.md` main's): 329 unit tests and 4
  functional tests pass. The full run of part 1 (started 22:04, on the tools
  of `739ef88`) goes on meanwhile, on its own copies; the gate waits for it
  (the gate's quick set rebuilds the Java classes that the full run's JVMs
  load).

* 22:25: **the start wired into `Db`** (`ca1aa63`), as 6.5 said:
  `struct db` has the node table and the node collection; `db_open` runs
  `sr_check_and_recover` and `sr_start` after the creation (or on an
  existing stream), then sets the startup distance and position, the
  clock's last time, the newest written top node, `createPutAndGetData`,
  `ACTIVE`, and `initFromDb` (reclaim's table refused as unsupported); a
  start that fails finishes the stream first (the fill written, 005-32);
  `registerNewNode` registers in the node table; the followers are
  `ncoll`'s (their failures into `db->op_err`); `resolvePointers` is
  `nc_resolve_pointers`; close's roots and the recount take the table's
  handles (and, without room for the roots' list, every holder lets go and
  a safe point frees). 012-09's `startup_pos_from_last_transaction` and
  `primordial_startup` are gone (the starter does both, the creation's
  start included). `bergdb-run` starts existing databases (restarts,
  `-segments` from 1, a directory with a stream); `cross.sh`'s `c_runs` keeps
  only reclaim on Java, and side B's crash runs and turns are C's;
  `f_api.c` starts the database it made and writes after it. 329 unit
  tests, 4 functional tests. By hand, C's runs of `sd-l2-sd100-restarts`
  (19 restarts), `sd-l2-every1-restarts` (399: a restart after every
  transaction), `gen-1` and `gen-201`: **Java's files byte for byte and
  Run's text**.

* 22:28: part 1's `cross.sh full C=build/tools-full` (the tools of
  `739ef88`; since then the start differs only in 6.4's F1, the second top
  ordinal and the probe, none of which a stream of the sets reaches; the
  probes ran on the final start): **CROSS full OK: 279 workloads, 1262 crash
  cuts, 498 corrupt variants, 6 in turns, the planted difference at 1164 was
  found and explained (1,370 s)**. Side B's dumps: C's bounded startup on
  354 directories (Java's on the 204 that may reclaim), every one equal to
  Java's `Dump.java`; **the 1,262 crash copies recovered by C's start equal
  Java's recovered copies, byte for byte**, and C's dumps of them equal
  Java's. And C's runs of every workload of the full set that does not
  reclaim (`runall.sh`, beside the run: 177 workloads, 137 of them with
  restarts, `sd-l2-every1-restarts`' 399 included, each into a new
  directory): **all 177 give Java's files byte for byte and Run's text**.

* 22:38: the wiring's gate: **C BEFORE COMMIT OK (64 s)**, its quick set
  with C's runs of restarts, crash copies and turns (side B's runs: C's of
  12, Java's of 4, those that reclaim). `f_start.c` (`d4bc6fa`): a restart
  after every transaction (40) writes the bytes of the run without
  restarts; a crash cut at a sample of positions of a small stream, each
  copy started, read as the whole transactions, written after and started
  again; the refusals of a start, which write nothing. The final
  `cross.sh full C=build/tools-final KEEP=1` started 22:28 (the tools of
  `ca01ae4`, the library as at the end but for `29a9d9f`'s failure code of
  a start whose read of reclaim's table fails, which no stream of the sets
  reaches): 343 workloads, side B's runs C's of 241 (restarts included) and
  Java's of 102 (reclaim). At 22:39: "compared in 651 s: 0 differences"
  (the runs, the scans, C's dumps of 482 directories, the files after the
  dumps). The probe on its directories (both sides' of the 241 workloads
  without reclaim, side B's now C's): **all 482 lines equal** (441,126
  reads of 438,204,856 bytes and 30,828 loads in Java and in C alike).
  Its crash variants: **1,262 copies recovered by C's start equal Java's;
  1,262 cuts, 0 differences** (C's dumps of them, and C's runs after them,
  20 transactions and a restart, Java's bytes and text). The probe on the
  1,262 cuts (`compare-crash.sh`): **all lines equal, and the 1,262
  directories as Java's and C's starts recovered them equal**: after a
  crash, C's start rebuilds Java's state and reads what Java reads.
* 22:53: that full run ended **CROSS full FAILED: 29 differences**, all in
  the turns of the two workloads there that reclaim (`coresame`,
  `sd-l3-node8-restarts`): side B's segments went to C, which refuses a
  retain duration other than forever (exit 3, 012-11), so the turns'
  directories went their own way. The harness's slip, not C's: side B's
  turns of a workload that may reclaim stay Java's (`c_runs`, `4a0f1de`
  and on); the other four workloads in turns, C's segments on side B, had
  no difference. Everything before the turns passed (the runs, the dumps,
  the crash variants, the corrupt variants: 0 differences). The gate on
  the final code: **C BEFORE COMMIT OK (82 s)**. The full run again from
  22:55 on the final tools (those of `a5e45ee`, the test build).
* 23:22: **CROSS full OK: 343 workloads, 1262 crash cuts, 498 corrupt
  variants, 6 in turns, the planted difference at 1164 was found and
  explained (1,632 s)**. Side B's runs: C's of 241, restarts included, and
  Java's of 102 (reclaim, 012-11); side B's dumps: C's bounded startup on
  482 directories, Java's on 204; the 1,262 crash copies recovered by C's
  start equal Java's, and C's dumps of them and runs after them; the turns
  with C's segments on side B (four workloads; the two that reclaim with
  Java's), all equal. **012-10 done** (6.7).
* 22:38: a million keys, by hand (Export's `scale:1000000`: puts of 100
  keys a transaction, node size 30, startup distance 50 MB, a restart
  halfway, then a pass of puts and deletes): Java's `Run` and C's
  `bergdb-run` (release build) each in a directory of its own: **the same
  files (96 MB, the stream of 100,640,080 bytes) and the same text**. The
  restart's start read a section of 3,285 records from 15,554,600 to
  47,105,367. C 7.0 s in all, 367 MB at most resident; Java 4.4 s, 1.47 GB
  (while the full run's JVMs ran; C's time includes its forces at sync and
  close). And a start of that database, by the probe: Java's and C's lines
  equal (a section of 4,406 records from 55,208,904; D of 4,405
  transactions; 75,345 canonical objects, 48,454 of them dirty; 7,081
  loads; 30,333 reads of 47,451,504 bytes); C's start 1.6 s and 383 MB at
  most resident in the release build.

## 6.3 Decisions

1. **The rerun is in part 1.** The split left the rerun of the section's
   transactions to 012-10 proper, as needing 012-09's `execute`,
   `TransNodes` and got-dirty lists. It needs none of them: Java's
   `DbStarter.rerunTransaction` runs `Dag.putKv` with `Db.newPutData()`,
   whose marking does nothing while no transaction runs
   (`markAtEndOfOp` returns at once when `x.transInfo` is null) and whose
   pointer-created listener feeds the residents and eviction only (no
   byte); `TransNodes` is not touched; D is `TransSeq` (012-09 part 1's
   `transseq`). And part 1 needs the rerun: done item 8's dumps read the
   state after the startup time, which only the rerun's puts rebuild, and
   rule 4 (`linkD`, in part 1's scope) links the canonical objects of D's
   nodes, which only the rerun's D gives. So `starter.c` reruns as Java
   does, with a `PutData` of its own (the Dag's, the writer's follower, the
   rerun's node-change listener), and rebuilds D from the stored got-dirty
   ids, each list a counted holder of its nodes (012-09's rule,
   `add_got_dirty_node`). What 012-10 proper must check of it is the bytes
   after restarts (6.5).
2. **Modules.** `lmap` (`HashMap<Long, Long>` where its order does not
   matter), `ntable` (`Cache3` in part: the node table), `ncoll`
   (`NodeCollection`), `recover` (`RecoverableStream.recover` with its
   fill), `starter` (`Db.startInner`'s start and `DbStarter`), `sdb` (a
   database opened by the bounded startup, for reads: part 1's test vehicle
   and `bergdb-dump`'s way to open, until 012-09's `Db` calls `starter`).
   `db.c` and `api.c` are not touched.
3. **The entry points for 012-09's `Db`**: `sr_check_and_recover` (after
   `handleEmptyStream`) and `sr_start`, on a `struct sr_env` that names
   the database's parts (the stream with its in-memory meta block, the node
   table, the node collection, the Dag, D, the node size); `struct
   sr_result` gives back what `Db` sets: the startup position and distance,
   the clock's last time, the newest written top node (counted for the
   caller), `StartInfo`, and what was read. `sr_start` also does the
   primordial startup (`doPrimordialStartup`), with the node table.
4. **Java's `HashMap` iterations** (`posMap`, `cache.handles()`) handle
   each entry alone, so C's maps iterate in their own order (012-02, 10.2).
   `posMap` holds the objects of the newest versions not made in the rerun
   section only: Java makes an object of every node of the section and
   uses the others only for their ids and positions, which the parsed nodes
   (012-06's views) give; `changeKeyNodesToStateAtStartupTime` cuts back
   `posMap`'s key nodes, the only ones used after it.
5. **`idOf`'s cache** (Java: a `LinkedHashMap` of 100,000 by access order)
   is a map cleared at 100,000 entries. It decides how many headers are
   read again, never a byte; at startup only `linkToCanonical`'s top nodes
   and its check use it.
6. **`postStartupCheck`** checks the node table's key nodes
   (`KeyNode.check`) and their values' positions, where Java walks the
   memory nodes from the super root: the same objects but for versions
   loaded by readers, which are checked too.
7. **A start that fails** writes what Java's writes (005-32): the fill, if
   recovery got that far; `bergdb-dump` then finishes the stream (writes
   and forces), as Java's start closes its storage.
8. **`bergdb-dump`** opens by the bounded startup by default; `-replay`
   keeps 012-08's full replay (a test vehicle), `-check` turns on
   `linkToCanonical`'s check by node id (Java's `-ea`), `-probe` prints one
   line of what the start rebuilt and read (6.2, 21:58). A start writes:
   so `cross.sh` gives every dumper a copy, as it did.
9. **`DatabaseNotCreatedException`** is `ERR_FORMAT` here, as in 012-08's
   replay; 012-09 proper has `ERR_NOT_CREATED` for it (`db.c`), which the
   merge takes.
10. **The extensions of other modules**: `stream` (012-06's, 012-09's)
    counts the reads of a directory's files (`file_reads`,
    `file_read_bytes`), for the probe; nothing else of 06, 07 or 08 is
    changed. `ncoll` has a source of nodes for tests (`struct nc_source`,
    Java's `TestStream`).

## 6.4 Findings

* **F1. `DbStarter.validateTransactions` checks neither positions nor
  times.** Its locals `tpos` and `tt` start at −1 and are never updated
  in the loop (`DbStarter.java:621-646`), so "non-increasing tpos" and
  "non-increasing tt" compare each record with −1 only: a startup section
  whose times do not increase is not refused there, though 012-02, 2.6
  says the start checks it. Probe `TimesProbe` (outside the repository,
  `scratchpad/10-startup/probe/src/bergdb/core/TimesProbe.java`, on
  `build/java/classes` at `decc677`'s `java/`): three transactions at
  1000, 2000 and 3000 in a memory stream whose section holds them all, the
  last record's time set to 1500 in a copy of the bytes, and a start of the
  copy: without `-ea` it starts, and `getOne("/k2")` at the latest time
  gives null (the rerun put it at 1500, behind 2000); with `-ea` the rerun
  fails in `KeyNode` ("AssertionError: lastTimeIndex=3, lastTime: 2000,
  time=1500"). For the conductor to register in 005 (a slip of 005-75's
  kind; the positions increase anyway by the walk). C does as Java: the
  same two checks against −1 (`starter.c`), so C's start of such a stream
  stops at the Dag's assert, as Java's under `-ea` (012-14 may want the
  check made real, in both).
* Otherwise C does as Java at every step, and the probe (6.2, 21:58)
  finds Java's and C's starts equal in what they rebuild and read.
* Notes, not bugs (for the conductor, as 005-75's kind): in
  `DbStarter.rerunTransaction` the refusal's text reads a header ("; type
  at ...") only when the stored position is a valid position, but then
  `canonicalNode` has read the node and returned it, so that part of the
  message is never built; `DbStarter.PrevMap` is used by nothing but its
  own four tests (dead since `prevPos` chains went, 011-03, G3).

## 6.5 The rerun, and what is left

The rerun as Java does it, written down at the split for 012-10 proper and
then done by part 1 (decision 1) and wired into `Db` (22:25):

**What the rerun must set** (Java at `decc677`: `DbStarter.rerunTransactions`,
`rerunTransaction`, `canonicalNode`; ported in `starter.c`, and checked by
the probe: D's checksum and the node table equal Java's). For each record
R(j) of the section but its first, R(s), in order:

1. The ids: from `Spos.nextVpos(R(j).tpos)`, one per node the rerun
   creates, in the order the Dag reports them (`topNodeCreated`,
   `keyNodeCreated`, `valueNodeCreated`), each the next vpos (`nextVpos`).
2. A `PutData` for the record (Java: `Db.newPutData()`, the writer's
   follower), `tt` = R(j)'s time; each stored value or delete node of R(j)
   in the record's order: `Dag.putKv(key, value or null)`, then
   `clearFast`.
3. Each node created: its id; its position the id, or the position of the
   node of R(j) with that id if there is one, and then a value's
   `offsetFromTrans` that node's (005-34); an index node's position the
   newest version's in the section (`newById`) if it has one; an index node
   canonical and registered in the node table (`Cache3.register`).
4. D's `TransInfo` of R(j): for each stored got-dirty pair (id, position),
   in order, the node's canonical object (`canonicalNode`: the node table's;
   else its newest version in the section, else the version at the stored
   position, read, cut back to the startup time if a key node, canonical,
   registered; none: `StreamFormatException`, "startup error, node ... not
   found"), set dirty and appended to the got-dirty nodes; `tt`, `tpos`,
   `startupPos`, `lastPos` R(j)'s; own bytes `TransSeq.ownBytes` of the sum
   of `StoredValueNode.getByteSizeLong(value, key)` over R(j)'s value and
   delete nodes (48 more); then `TransSeq.add`. R(s) is not rerun and not
   in D.
5. Then rule 4 (`linkD`) on the canonical objects of D's nodes, the check,
   and the end of the reconstruction (no cut back from then on).

And around it, what `Db.startInner` sets (`sr_result` gives each): the
in-memory meta block, the last valid block with `lastTrans` the last
committed record (done by `sr_start` in `env->rs`); the startup distance
from it; `x.startupPos` the last record's `startupPos`; the clock's last
transaction time the last record's; `newestWrittenTop` the node `topPos`
names; then `createPutAndGetData`, the state `ACTIVE`, `reclaim.initFromDb()`
and `eviction.afterTransaction()`.

**Done since the change of scope** (6.2, 22:19 on): the start in `Db`
(`db_open` through `starter`, the node table and the node collection in
`struct db`, `registerNewNode`, the followers, `resolvePointers`, close's
roots), `bergdb-run` with restarts, `cross.sh` with C's runs of restarts,
crash copies and turns, `f_start.c`.

**Left after 012-10** (not 012-10's): eviction after the start's loads and
the memory budget (012-12), reclaim's table at a start and a cut stream
(012-11: `initFromDb` refuses the table as unsupported), and the question of
6.4's F1 (012-14 may make the check real, in both).

## 6.7 Done when, as it holds

Section 1's items, with the evidence (6.2):

1. **Recovery** (`recover`, `sr_check_and_recover`): Java's
   `RecoverableStream` tests of `recover()` (`t_recover.c`); `records.txt`'s
   stream cut at every position, the fill as 012-06's plan, a second start
   writing nothing (`t_sdb.c`); the full set's 1,262 crash copies and the
   quick set's 64 recovered by C's start equal Java's recovered copies, byte
   for byte; a creation cut at 17 positions: the same refusals
   (`DatabaseNotCreatedException`, nothing written) and starts as Java's.
2. **The start's checks**: Java's refusals with Java's exception names
   (`t_sdb.c`, `f_start.c`: another node size, an incomplete creation, bad
   magic bytes as `BadCryptoKey`, another version, no node size), nothing
   written; the database id and the startup distance from the stream (the
   in-memory block, a copy of the last valid one, writes the next blocks:
   equal bytes after restarts).
3. **The startup** (`starter`, `ncoll`, `ntable`): Java's and C's starts of
   every directory of the full set without reclaim (354) and of the quick
   set's crash cuts (64) equal in the startup position, D (its checksum),
   the newest written top node, the super root, the node table and the
   canonical objects' contents (the probe); the rerun's D and take's state
   also by the bytes of every run with restarts (item 5); rule 4 by
   position equal to rule 4 by node id at every start (the check).
4. **Loads**: Java's `NodeCollection` tests (`t_ncoll.c`); the loads and
   the reads of the files equal Java's at every start of the full set
   (344,080 reads, 396 MB, 21,344 loads); the dumps' reads (item 8).
5. **The bytes after restarts**: C's runs of the full set's 177 workloads
   without reclaim, 137 with restarts (`StreamDigest`'s Level 2
   configurations in the restarts mode, `l2-every1` with 399 restarts,
   Gen's seeds with restarts), Java's files byte for byte (`runall.sh`, and
   the final full run, below); `f_start.c`'s restart after every
   transaction against the run without restarts.
6. **In turns**: the full set's six workloads in turns, C's segments on
   side B (the final full run).
7. **Crashes**: C's start recovers each cut copy to Java's bytes and dumps
   it as Java does (item 1), and C's runs after the crash (20 transactions,
   a restart) write Java's bytes (the final full run); `f_start.c`'s cuts.

The task's instructions: **C BEFORE COMMIT OK** (82 s, at `a5e45ee`, the
final code; 329 unit tests, 7 functional tests, the quick set with C's
restarts); **`cross.sh full` with `C=` the final test build's tools: CROSS
full OK, 343 workloads, 1262 crash cuts, 498 corrupt variants, 6 in turns
(1,632 s)**. Milestone M3 (Levels 0 to 2) as far as 012-10 goes: C opens
and restarts databases with the bounded startup and writes Java's bytes
after it.
8. **Java to C**: `bergdb-dump` opens by the bounded startup, its dumps of
   354 directories equal Java's, and `bergdb-run` opens by `Db`'s start; the
   full replay is `bergdb-dump -replay`, a test vehicle.

## 6.6 For the conductor

The clone `/Users/f/fl/bench/012/10-startup/` has main merged at
`ceb462b` (012-09 done, `1d1e2fb`, and `27c947d`). The files of 012-10
(all under `items/012-bergdb-c/`): this file; new
`c/src/{lmap,ntable,ncoll,recover,starter,sdb}.{c,h}`,
`c/test/unit/{t_sdb,t_ncoll,t_recover}.c`, `c/test/func/f_start.c`;
changed `c/src/db.{c,h}` (the start wired in), `c/src/api.h` (its
comment), `c/src/stream.{c,h}` (the files' read counters), `c/tools/dump.c`
(the bounded startup, `-replay`, `-check`, `-probe`), `c/tools/run.c`
(restarts), `c/test/unit/main.c`, `c/test/func/f_api.c` (the start of the
database it made; `start_tests` in its table), `c/test/cross/cross.sh`
(the crash copies compared after both sides' recovery; `c_runs` reclaim
only; side B's crash runs C's, and its turns C's but for workloads that may
reclaim), `c/readme.md` (the module rows,
the tools), `c/tools/readme.md`. The Java probes (`StartProbe`,
`TimesProbe`) and the scripts `compare.sh`, `compare-crash.sh`,
`creation.sh`, `runall.sh` are outside the repository, in
`/private/tmp/claude-502/-Users-f-fl-repos-f1/84ff067e-dce6-4c28-a354-b5d6389d3c5b/scratchpad/10-startup/`
(`probe/` and the top); 012-10 may want `StartProbe` beside `Dump.java`
and `bergdb-dump -probe` in `cross.sh`, which would compare every start of
the sets that way. 012-05's text (05-cross-harness.md) does not yet say
that side B's runs with restarts, crash runs and turns are C's (only
reclaim stays Java's), nor the comparison after the recovery.
