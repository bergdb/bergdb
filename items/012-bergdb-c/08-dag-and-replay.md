012-08. Task: the Dag, reads, and Java's databases by full replay
=================================================================

Created 2026-10-27 by Claude (Opus 5.5, Claude Code), with 012-01, for
Frans Lundberg. **Status: done, 2026-10-28 21:15** (started 17:38; paused
18:11 to 20:53 for the usage window), in the clone
`/Users/f/fl/bench/012/08-dag/`, for the conductor to check and copy in;
approved with 012-01 by Frans's go (012-01, 9.1).
Phase B (012-01, section 8). Effort: max. After: 012-07.


# 1. The goal

The multiversion map in C (Level 0) and C's first reads of Java's
databases (Level 1, a replay of the whole stream): `Dag`'s puts, deletes
and reads at a time, `getMany`, and `getTrans`. Milestone M2: C reads
Java's databases.

Done when:

1. `Dag`: put and delete of a transaction's keys at its time, with the
   splits and new top nodes as Java makes them; `getOne` at a time,
   giving the value, its time and its transaction's position (as
   `GetData.kvTime` and `tpos`); `dirtyNodeBound` (005-31).
2. `getMany`: forward and backward, from a start key, inclusive or not,
   with the stop conditions of `GetMany` (none, end key, count, prefix, a
   callback), as `GetMany.Chain` walks.
3. `getTrans`: the record at a position, its time, positions and
   key-value pairs, with Java's refusals of positions (005-34, 005-43).
4. **Full replay**: a database is opened by reading every record from the
   start and applying its value nodes, puts and deletes, at the record's
   time. On databases without reclaim only: a cut stream cannot be
   replayed (Level 3 needs Level 2), and what reclaim rewrites is 012-11's
   to understand.
5. `tools/bergdb-dump` prints 012-05's dump format; for every database of
   the sets without reclaim, C's dump by full replay equals Java's
   `Dump.java`. `cross.sh` runs it with C as side B.
6. Java's tests ported where C has the behaviour: `DagTester`, the
   `@Nano` tests of `Dag` and `GetMany`; a random test of the Dag against
   a simple model map (key to its versions) with reads at random times.


# 2. Read first

* Java: `Dag` (802 code lines), `GetMany` (336), `KeyAccessPath`,
  `PutData`, `GetData`, `Kvt`, `DagTester`; `Db.getOne`, `getMany`,
  `getTrans` and `getOneInternal` for what the database adds around the
  Dag (the first available lookup time, the actual lookup time).
* `DbClock.lookupTime`: a read never sees a running or a future
  transaction.
* `docs/levels.md`, Levels 0 and 1; 011-04, "The level 1 bugs", for what
  went wrong in Java's Level 1 in 2026.


# 3. The work

1. Port `Dag`'s put path and read path, then `GetMany`.
2. An in-memory database (Level 0): a Dag fed by transactions in memory,
   for the unit tests and the model test.
3. Full replay over 012-06's trans iterator.
4. `getTrans` over 012-06's parser.
5. `bergdb-dump`, and its place in `cross.sh`.
6. The ported tests and the model test.


# 4. Tests

The ported tests; the model test under the sanitizers; the dump
comparison on the quick and full sets (databases without reclaim).


# 5. Notes

* A full replay gives the same key-value versions as Java's database, so
  the dumps compare, but not the same nodes in memory as Java's startup:
  that is 012-10. The replay is a step and a test vehicle, not the way C
  will open databases.
* The replay applies every record's value nodes, Java's internal ones too
  (the dummy of `setStartupDistance`), as Java's Level 1 replay did; the
  dump shows internal keys as Java's dump shows them.
* Memory (012-01, 4.5): the Dag's replacements and splits share values and
  handles between objects, and make temporaries (`first`, `last`), as in
  Java; the counts and the pending list take care of both, so the port
  keeps Java's order. `getMany`'s cursor counts the objects it holds, so
  that a long range frees what it has passed at safe points between
  leaves; a version read for one operation only is made without a holder
  and freed at the next safe point.


# 6. Decisions

Taken in this task, as the plan left them to it; 012-07's design (its
section 6.7) is followed as it is, and no 012-07 module was changed.

1. **Modules** (`c/readme.md`, section 2): `dag` (`Dag`'s put path,
   `getOne`, `dirtyNodeBound`, `findNode`, `createEmpty`; `PutData`,
   `GetData`, `KeyAccessPath`, `Dag.SplitListener`), `getmany`
   (`GetMany`, its `Chain`, the stop conditions `DontStop`, `Endpoint`,
   `GetN`, `Prefix`, `PrefixN` or a caller's, and `Dag.getMany`), `mdb`
   (a database of Level 0 in memory: Db's creation, a transaction's puts
   and deletes at its time, reads with `DbClock.lookupTime`'s clamp),
   `replay` (Level 1: `Db.start`'s checks and what it reports, the full
   replay into an `mdb`, `getTrans`), and `tools/dump.c` (`bergdb-dump`).
2. **Faithful line by line**: every method of `Dag`'s put and read paths
   in Java's order, the listeners called where Java calls them, Java's
   asserts as C's (`assertOk` is `kn_check_max(...) == NULL`). The splits,
   the new top nodes and the key node entries' times are Java's: Java's
   own `Dag` and C's give the same split counts, `dirtyNodeBound` and
   `getMany` state (with `Kvt.time`) on 960 transactions (`dag.txt`, a new
   generator in `Vectors.java`), and every dump compares.
3. **Failures**: a Dag function returns `false` where Java would throw: a
   failed allocation of the Dag's own (NOMEM), or a callback's failure
   (`opdata.h`); the counts stay right (012-07, 6.4.1). The caller knows
   which: `mdb`'s callbacks fail only on NOMEM, the replay's reads fail
   outside the Dag.
4. **Results as a sink** (`struct gm_sink`): Java's `GetMany.result` keeps
   `Kvt`s with a new key array and the value node's own bytes; C gives each
   pair to a function, valid during the call, which copies what it keeps
   (as the API copies into the read context's buffer, 012-03). A `Kvt`'s
   key is the chain's buffer, its value the value node (borrowed).
5. **Memory** (012-01, 4.5; 012-07, 6.4): the chain counts its links
   (`GetMany.Chain.linkNodes`, counted in 012-07, 6.4.2): `addLink`
   retains, `removeLink` and the chain's end release; so `getmany`'s
   `collect` can make a safe point between pairs (the `mdb` does).
   `KeyAccessPath`'s, `OpData`'s and `PutData`'s nodes are borrowed and
   cleared at the operation's end (`pd_clear`). `mdb` collects after
   each put, at each transaction's end and after its start; `mdb_free`
   frees all by close's walk. Every test ends with the allocator's count
   0; the recount runs after each transaction of the model test.
6. **The full replay** (`replay.c`): every committed record from the
   creation on, its value and delete nodes applied as `Db.putKvs` applies
   the transaction's pairs: in the record's order (the order in which the
   transaction made them, which is its pairs' order), each a `putKv` at
   the record's time, `clearFast` after each, `clear` at the end. A
   delete of a missing key made no node in Java and changed no index node,
   so nothing is lost. The Dag starts as Db's creation makes it (the root
   `KeyNode.nodeWithTime(tt)`, top node 0), not as `Dag.createEmpty` (an
   empty root, whose klongs and so splits differ). A restart changes no
   key node's klongs (P2, `RestartInvariance`), so the replay's Dag has
   Java's versions. The index nodes are the Dag's own, with no ids or
   positions (reads do not use them); each value node gets the parsed
   node's position, id and record, as Java's serializer gives them, so
   `Kvt.spos` and `GetData.tpos` are Java's.
7. **Recovery without writing**: the start takes 012-06's plan of Java's
   recovery (`rs_plan_recovery`): the stream's length after the fill
   (`status length=`), and the walks see the stream as Java's walks do
   after the fill, through a copy of the `struct stream` whose length is
   cut at the torn record (it only reads). `getTrans` at the torn record's
   position gives Java's answer there (not committed: `DbFailedException`);
   positions inside the fill would differ (C: past the end; Java: zeros),
   which no dump reaches. A cut stream (first position not 0), an empty
   one (Java creates it), and one with reclaim's table are refused as
   unsupported (`UnsupportedOperationException`; `bergdb-dump` exits 3):
   012-09 to 012-11.
8. **`cross.sh`**: with `C=`, side B's dumps of the workloads that may
   reclaim (`retain_of`) stay Java's (`build/cross/SET/java-only.txt`), and
   the report says how many dumps were C's. The crash variants never
   reclaim, so all their dumps are C's. Without `C=`, nothing changes.
9. **`DbClock.lookupTime`'s clamp** is one line in `mdb`
   (`mdb_lookup_time`), as the brief allows: the conductor merges it with
   012-09's `DbClock`.
10. **`dirtyNodeBound`'s collections**: `IdentityHashMap<KeyNode,
    Walked>` is an open-addressing table by address; the sort deepest
    first is a pass per depth (Java's stable sort; the order within a
    depth does not change the sum); `freshKeys` is a list per walked node,
    grouped by sorting; `freshTreeBound`'s recursion over the key's
    segments is a work list, since a long key has many segments (012-01,
    4.5, point 8). The result is Java's on the 960 vectors.


# 7. Progress

**Java's reference:** `main` at `c7ccde8`, `java/` as of `fd8f513`.
**Clone:** `/Users/f/fl/bench/012/08-dag/` (a clone of `bergdb` at
`c7ccde8`), committed locally; the conductor copies the files in.

* 2026-10-28 17:38: started. Read 012-01 (sections 1, 3, 4, 6), this
  plan, 012-07 (section 6), 012-06, 012-05 (section 6, `cross.sh`,
  `Dump.java`), 012-02 (sections 4 to 8), `c/readme.md`, and Java's `Dag`,
  `GetMany`, `KeyAccessPath`, `PutData`, `GetData`, `Kvt`, `DagTester`,
  `Db`'s reads and start, `DbClock`, `Reclaim.initFromDb`.
* 17:45: steps 1 to 5 (`8e8eb4c`): `dag`, `getmany`, `mdb`, `replay`,
  `tools/dump.c`, and `cross.sh`'s use of C's dump. `cross.sh quick
  C=build/test`: OK at the first run, C's dumps of 12 directories and of
  64 crash cuts equal Java's (32 s).
* 17:51: `cross.sh full C=build/tools-full` (a copy of the test build's
  tools, so that builds can go on) started in the background.
* 17:53 to 18:05: step 6, the tests (`93bb984`, `64216ce`, `4b3ccc6`,
  `e32edbd`): `t_dag.c` (`DagTester`, all 12 tests, with
  `java.util.Random`'s seeds, and 120 more seeds of its random
  transactions), `t_getmany.c` (`DbTesterGetMany`'s
  `testInclusiveStartKeyWithDeepTree` and `testStartKeyRandom`, the model
  test, the allocation failures in turn, `dirtyNodeBound`'s bound against
  Db's marking on 2,400 transactions), `t_replay.c` (Java's stream of
  `records.txt`: reads at every record's time against a map of its value
  nodes, `getTrans` against `StoredTrans.parse`'s fields and Java's
  refusals, the stream cut at every position, the start's refusals, the
  allocation failures), `t_dagvec.c` (Java's Dag against C's, `dag.txt`).
  `c/readme.md`: the module table, 012-07's nine modules and these four.
* 18:08: `t_dbgetmany.c` (`08796e1`): `DbTesterGetMany` on the Level 0
  database, 29 of its 33 `@Nano` tests (27 there, 2 in `t_getmany.c`) and
  its `testStopCondition1`; left out `test4` (a restart, 012-10) and the
  three with `KeyFactory.crazyKey`. `Dag` and `GetMany` have no `@Nano`
  tests of their own. 231 unit tests.
* 18:12: `-large` (scale's mode) against Java's `Dump -large` by hand, on
  an exported `sd:l2-sd1000-node8:plain:n=500`: the same 4,394 lines; on
  `gen:7` (it reclaims) C exits 3, as decided, where Java's start makes the
  cut that the table marks (it deletes the first file).
* 18:10: `bergdb-dump` skips an empty key in the scan's samples, as
  `Dump.Scan.keys` does (`30964af`; no workload has one).
* 18:11: **paused** at the conductor's request (the usage window, and F53
  for another session's timed runs until 20:50): `cross.sh full
  C=build/tools-full` (the test build's tools of `8e8eb4c`, whose dump
  path is today's but for the empty key above) stopped in its corrupt
  variants (scans only), after: **runs, scans and dumps compared, 0
  differences: C's dumps of 352 directories (176 workloads without
  reclaim, both sides' directories) equal Java's, Java's of 204
  (workloads that may reclaim); crash variants: 1,262 cuts, 0
  differences**, every crash cut dumped by C (1,004 s to there). The turns
  and the planted difference were not reached. Nothing of 012-08 runs.
  **Next, on resume:** the gate (`c/before-commit.sh`, C's dump in its
  quick set); then the second and last `cross.sh full`, with a copy of the
  final test build's tools (`build/tools-full2`), for its whole report;
  then the status line "done", the Done-when list's results, and the
  report to the conductor.
* 20:53: resumed (the conductor; new hard stop 01:50). **The gate: C
  BEFORE COMMIT OK (49 s)**: 230 unit tests, 8,607,616 checks, the release
  build under `leaks` with no leak, and the quick cross set with C's dump
  as side B (C's dumps of 12 directories and 64 crash cuts, Java's of 8;
  0 differences).
* 20:54 to 21:14: the second and last `cross.sh full`,
  `C=build/tools-full2` (the final test build's `bergdb-dump` and
  `bergdb-scan`, under the sanitizers): **CROSS full OK: 278 workloads,
  1262 crash cuts, 498 corrupt variants, 6 in turns, the planted
  difference at 1164 was found and explained (1,197 s)**. Side B's dumps:
  C's of 352 directories (the 176 workloads that do not reclaim, both
  sides' directories) and of all 1,262 crash cuts, every one equal to
  Java's `Dump.java`; Java's of 204 (the workloads that may reclaim).

**Findings in Java**: none. Two notes, not bugs: `DagTester`'s
`testVisit1` and `testPointerCreationListener` never clear the key access
path between puts (`Db.putKvs` calls `clearFast` after each `putKv`), so
its path grows across puts; no split of theirs reads a stale entry (C reads
every key back after the 10,000 puts: all there). And a torn record whose
size field has 1 to 3 bytes is completed to a size from those bytes
(`transHeaderFixBytes`, 012-02, 4.4), so recovery's fill can end before
the record's real end; `t_replay.c` checks C's length against that rule.

**For the conductor**: the files to copy in: this file;
`c/src/{dag,getmany,mdb,replay}.{c,h}`; `c/tools/dump.c`;
`c/test/unit/{t_dag,t_getmany,t_replay,t_dagvec,t_dbgetmany,main}.c`;
`c/test/unit/vectors/dag.txt`; `c/test/cross/cross.sh`;
`c/test/cross/java/Vectors.java`; `c/readme.md`. No 012-07 module
changed. `DbClock.lookupTime`'s clamp is one line in `mdb`
(`mdb_lookup_time`), to merge with 012-09's `DbClock`. `main.c` and
`cross.sh` may meet 012-09's changes (tables added; C's `bergdb-run`
as side B); `cross.sh`'s `java-only.txt` now names only dumps.

**Next:** 012-09, the write path: Db's listeners (`setIdOfNode`,
`registerNewNode`, `markAtEndOfOp`, `TransNodes`) plug into `putdata`'s;
`mdb` stays the Level 0 test vehicle and `replay` the reader of Java's
databases until 012-10's startup.

**Done when**, as it holds at the end (21:15); all six hold, with the
gate's `C BEFORE COMMIT OK (49 s)` and `CROSS full OK` above:

1. `Dag` (`dag.c`): `putKv` (puts and deletes of a transaction's keys at
   its time, with Java's splits, in place or not, and new top nodes),
   `getOne` (the value, `GetData.kvTime` and `tpos`), `dirtyNodeBound`
   (005-31), `findNode`, `createEmpty`. Java's Dag and C's agree on 960
   transactions (`t_dagvec.c`: the bound, the split counts, the state with
   `Kvt.time`); `DagTester` passes whole.
2. `getMany` (`getmany.c`): forward and backward, from a start key,
   inclusive or not, with `DontStop`, `Endpoint`, `GetN`, `Prefix`,
   `PrefixN` or a caller's stop condition; `DbTesterGetMany`'s tests and
   the model test pass, and every range of every dump equals Java's.
3. `getTrans` (`replay_get_trans`): the record at a position, parsed, with
   Java's refusals (005-34, 005-43) and failures (005-30).
4. The full replay (`replay.c`), on databases without reclaim; a cut
   stream, an empty one and one with reclaim's table are refused as
   unsupported.
5. `bergdb-dump` (`tools/dump.c`): Java's text, "bergdb-dump 1";
   `cross.sh` runs it as side B on every workload that does not reclaim:
   equal to Java's on all 352 directories and 1,262 crash cuts of the full
   set, and in the gate's quick set; `-large` by hand on one database.
6. The ported tests and the model test, under the sanitizers, with the
   recount and the allocator's count 0; the allocation failures in turn.

