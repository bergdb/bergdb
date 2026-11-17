# 022-07 Report: the C clone at release 2026.4 as released

Created 2026-11-11 by Frans Lundberg. Status: open (the port done, gated
and compared; two parts of the full set and 022's long runs not run: the
State section at the end).

The update of the C clone (`c/`) from the release candidate of 2026.4
(`main` at `d00096e`, record format 5; 022-04) to release 2026.4 as
released (the tag `release-2026.4`, `76f66f89`, 2026-11-10, record format
6): what changed in C, what shows that C matches the release's Java, the
faults found in C and in Java, C's departures, what is left. 024-01 calls
it CC1. It is 022-02's step T, the diff from the candidate to the tag,
which was to be a short confirming run and became a port of its own when
023 changed the delete path before the release (023-08, section 5). By
the agent `cc` of coord-1111, 2026-11-11, in a clone of its own, with
`JAVA_REF=2026.4`; the method and the form are 022-04's.


# 1. In short

* **C writes release 2026.4's bytes** in all that the port compared
  (section 3): the cross runs against the release's Java show 0
  differences, in the quick set and in a new set of 190 workloads for the
  delete path (`cross.sh deletes`); Java's vectors, written again from the
  release, are C's; the corrupt-stream set gives the same status, text and
  message in Java and C; and two streams of transactions with key
  transformations, which no cross workload has, are Java's byte for byte.
* **What changed** (section 2): record format 6; a delete that empties its
  leaf unlinks it upward (UP), with the take-back of a node that a split
  of the transaction made (TB) and its repoint (fault 12); the empty key
  first in every inner node (LE-b); root collapse (RC); the bound of a
  transaction's dirty nodes for deletes (K4); the sort of a transaction's
  keys after their transformations, one operation a key (SORT); a
  taken-back node out of the node table (DROP); a forward scan's end key
  in the Core (SE); the dead hand (DEAD); and 020-32's two refusals on
  damaged streams (CYC, PREV).
* **Java's new tests** are in C where C has what they test (section 3.5):
  22 of the Core's 28 new or changed test methods, 6 not for C.
* **Found**: no difference between C and Java once the port was made, and
  no fault of Java's product code; three notes on Java for the
  coordinator, one of them a test that does not test what it says
  (section 5). In C: one test whose bound was not an invariant (section
  4).
* **Departures** (section 6): three new ones, none in the bytes: the dead
  hand's round made whole in the call; a transaction executed again after
  two of its transformed puts became one key; the C API's ranges do not
  set the Core's end key.
* **Left** (section 9): Gen's 400 seeds of the full set and the 10M-key
  workload of puts, not run (the commands are in the State section);
  022's long runs; Frans's open points of 022's log.


# 2. What changed

## 2.1 In Java, between the candidate and the release

`git diff d00096e release-2026.4 --stat -- java/src`: 29 files, 3,013
lines added and 47 deleted, in 24 commits, every one read. In the Core's
product classes:

| ID     | Java's change                                     | Where in Java               |
|---|---|---|
| F6     | record format 6, the refusal names 2026.3         | `StoredTrans`               |
| UP     | a delete unlinks what it empties, upward          | `Dag.deleteUpward`          |
| TB     | the take-back of a split's node, with retarget    | `Dag.takeBack`, `PutData`   |
| F12    | fault 12: the segment leaf's klong repointed      | `Dag.spaceSplitInPlace`     |
| LE-b   | the empty key first in every inner node           | `KeyNode.firstAndSecond`    |
| RC     | root collapse after a climb                       | `Dag.collapseRoot`          |
| K4     | `dirtyNodeBound` counts a delete by path node     | `Dag`, `Db.checkDirtyNodes` |
| SORT   | key transformations first, sorted, one a key      | `Db.putKvs`, `sortByKey`    |
| DROP   | a taken-back node leaves the node table           | `Cache3.dropNode`, `Db`     |
| SE     | a forward scan's end key                          | `GetMany`, `Dag.getMany`    |
| DEAD   | the dead hand: the memory of ended versions       | `Eviction`, `Cache3`        |
| CYC    | 020-32: a descent or a scan that meets a cycle    | `OpData`, `GetMany`         |
| PREV   | 020-32: a damaged prevPos refused at the link     | `NodeCollection`            |

Reclaim's product code did not change (023-08, section 5, point 2: P8 is
out); `Reclaim.java`'s 85 new lines are two liveness tests. Nothing for C
in: `BuildInfo` (C has no counterpart), the Pub layer's four files, the
comments and test names of 023-11's B3 and B4, and the two test-only
commits of the release night (`85bed824`, `6e9671d4`: Java's storage
thread).


## 2.2 In C

Each is Java's code in Java's order, with Java's names in the comments
and Java's exception names and texts.

| ID     | In C                                                 | C's tests                    |
|---|---|---|
| F6     | `strans.h`'s `ST_RECORD_FORMAT` 6, `strans.c`        | `t_serial.c`, `t_records.c`  |
| UP, TB | `dag.c`'s `delete_upward`, `take_back`, `retarget`   | `t_delete.c`, `t_dbtester.c` |
| F12    | `dag.c`'s `space_split_in_place`                     | `t_delete.c`                 |
| LE-b   | `kn_first_and_second`, `dag.c`'s `empty_key_next`    | vectors, `t_delete.c`        |
| RC     | `dag.c`'s `collapse_root`, `take_back_root`          | `t_delete.c`, `t_dbtester.c` |
| K4     | `dag_dirty_node_bound`, `db.c`'s `check_dirty_nodes` | vectors, `t_delete.c`        |
| SORT   | `db.c`'s `put_kvs`, `sort_by_key`                    | `t_dbtester.c`, `sorted.txt` |
| DROP   | `ntable.c`'s `nt_drop_node`, `db.c`, `starter.c`     | `t_evict.c`, cross runs      |
| SE     | `getmany.c`'s `end_key`, `is_past_end`               | `t_dbgetmany.c`              |
| DEAD   | `evict.c`'s `ev_dead_hand`                           | `t_evict.c`                  |
| CYC    | `opdata.c`'s `op_descent_to`, `getmany.c`            | `t_delete.c`, corrupt set    |
| PREV   | `ncoll.c`'s `check_link_by_id`                       | `t_ncoll.c`, corrupt set     |

* **UP, TB, LE-b, RC, F12** are one block of `dag.c`, Java's
  `Dag.deleteUpward` and its eighteen helpers, with three new methods of
  `knode.c` (`kn_add_klong_copy_pointer`, `kn_copy_pointer`,
  `kn_repoint_klong`). Java's `Bug` exceptions are errors of the put (the
  database fails), not aborts. Java's static counters (`Dag.statUnlinked`
  and the others) are fields of the put data, as the library has no
  global state.
* **`PutData.replaced`**, Java's identity map from a node that a split of
  the transaction made to the node it replaces, is a table by address in
  the put data. Its nodes are borrowed, not counted (the close's walk
  frees by roots): a made node's entry leaves the table when the node is
  taken back, so no entry outlives its node (Java's entry stays and is
  never read again); an old node is held by its handle, which no eviction
  takes within a transaction (`dag.h`).
* **DROP**: `Db.takenBackInTrans` is a flag (`OBJ_TAKEN_BACK`) on the
  nodes of the replaced list, which holds them until the transaction's
  end; the startup's rerun drops such a node at once, as Java's
  `DbStarter`.
* **SORT**: every key transformation runs first; then, if one ran, a
  stable merge sort of a copy of the transaction's pairs (Java's
  `Arrays.sort` of objects is stable) and one pair a key by the builder's
  rule; value transformations in the put loop, for the pairs kept.
* **SE** is in the Core's `struct getmany` only; section 6, point 3.
* **DEAD**: section 6, point 1.
* **CYC**: `descentPower` is an `int` in Java and unsigned in C, as C's
  signed shift must not overflow; the same below 2^30 steps (section 5).
* **The harness**: `test/cross/java-build.sh` defaults to
  `JAVA_REF=2026.4`, the release's source zip checked against its
  `SHA256SUMS`; the harness's Java compiled against the release unchanged.
  New: `GenDel.java` and `cross.sh deletes` (section 3.2), `Batch.java`
  writes Java's delete counters beside each run, `CorruptSet.java` makes
  020-32's two copies, `Vectors.java` writes `sorted.txt`.


# 3. The evidence

## 3.1 The gate

`c/before-commit.sh` against release 2026.4 (`JAVA_REF`'s default), in a
detached worktree at the commit's tree, under the day's heavy-run lock:

| Commit     | What                               | Time  | Gate                         |
|---|---|---|---|
| `ed02ab6d` | the port, the tests, the documents | 08:33 | `C BEFORE COMMIT OK (297 s)` |
| `fb2a6d86` | the head: two commits of tests on  | 11:30 | `C BEFORE COMMIT OK (302 s)` |

The second gate covers `ad2a3023` (the scale workload of deletes; the
harness only) and `fb2a6d86` (the empty key's stream and its test): 550
unit tests, the other counts as the first's. The first gate's steps:
`build` 39 s; `rules` (45 modules, floating point only in the
11 allowed places); `unit` 549 tests, 11,203,001 checks; `unit-release`
548 tests and no leak; `func` and `func-release` 51 tests; `cross`:
`CROSS quick OK`, 27 workloads, 75 crash cuts, 85 corrupt variants, 2 in
turns, 54 budget runs, 83 s; `write`: `WRITECHECK OK`, 10,354 takes
replayed, 75,348 index nodes in order, 0 errors, 22 directories equal
after the re-append; `corruptset`: 65 copies, the same status and text in
each; `allocfail`: 634 runs (413 refused, 218 failed databases, 2
absorbed); `examples` OK. Against the candidate's gate (022-04, section
8.2): the unit tests went from 529 to 549, `cross quick` from 23
workloads to 27 (the four `del:` ones) and from 46 budget runs to 54, the
corrupt set's quick from 63 copies to 65, `allocfail` from 628 runs to
634 (the put data's table of the nodes that splits made is allocated).


## 3.2 The cross runs

Side A is the release's Java, side B is C's tools; each workload is run
by both, and the files, the runners' texts, the scans and the dumps of
each side's directory by both sides are compared (022-01; `cross.sh`'s
header).

**The quick set** (in the gate): 0 differences in 27 workloads, 75 crash
cuts, 85 corrupt variants, 2 runs in turns and 54 budget runs: 022's 23
workloads and four of the new `del:` ones.

**The delete path: `cross.sh deletes`**, new (`GenDel.java`). A workload
is rounds of a fill, a delete pattern, mixed transactions and a drive of
single puts, on keys of one of five shapes (one segment, so one tree at
the space root; two segments, trees of up to 100 keys; a few trees of
many keys; long keys of several segments; a scattered order). The nine
delete patterns: every key ascending, descending, shuffled; every k-th;
a range; all but the first and the last, then the first, then the last
(a chain of single children, which the delete of the first collapses
over several levels); from both ends inward; a random share; every key
but each k-th, then the rest. A third of the mixed transactions are
swaps: a range of the keys whose dead keys are put and whose live keys
are deleted, so that one transaction splits nodes and empties what it
split (the take-back). Between the phases: checks at the latest time and
at earlier times, gets, restarts with and without a sync. With a retain
duration the drive is 60 to 360 transactions, so that reclaim's
iterations and cuts pass over what the deletes left. About half of the
workloads end with every key deleted (the database empty), a restart and
puts again. The set: 80 workloads drawn from their seeds; 45 with each
pattern on each shape at node size 8 and startup distance 100, without
reclaim; the same 45 with a retain duration of 1 s; 20 with transactions
of up to 1,000 operations on 3,000 keys.

Its run, on the gate's build of `ed02ab6d` (08:33 to 08:43, 584 s):
`CROSS deletes OK`, **0 differences** in 190 workloads (265,289
transactions, 953,129 deletes, 463 restarts; 94 workloads with reclaim;
node size 8 in 123, 14 in 26, 30 in 27, 62 in 14), 116 crash cuts (each
recovered and dumped by both sides, then run on), 85 corrupt variants, 6
runs in turns (a workload's segments run by Java and C alternately on
one directory) and 760 budget runs (C under budgets of 1, 4,000, 64,000
and 1,000,000 bytes, where the dead hand runs too). What the 190
workloads made the writer do, by Java's own counters of side A's runs
(`Dag.statUnlinked` and the others; C's bytes are the same, so the
counts are C's too):

| What                                                | Count   | Workloads with it |
|---|---|---|
| nodes unlinked (UP)                                 | 811,345 | -   |
| climbs: deletes that emptied their leaf             | 574,107 | -   |
| the empty key's child emptied (LE-b)                | 108,874 | 187 |
| nodes taken back (TB)                               | 31,772  | 160 |
| root collapses (RC)                                 | 6,440   | 161 |
| roots taken back                                    | 2,204   | -   |
| an emptied space root kept, made by the transaction | 21      | -   |

**The delete path on a large database: `cross.sh scale SCALEDEL=1`**,
new: one workload of N keys `/k/000000000` and up, put 100 a transaction
(node size 30, startup distance 50 MB); a restart; a mass delete in key
order, 999 keys a transaction, of every key but one in a thousand; a
check and a restart, whose rerun has deletes; the kept keys deleted, so
that the database is empty and its root a segment leaf again; then every
hundredth key put again; a check and gets. The files, the texts, the
scans of the streams' last megabytes and the dumps are compared, C's
release build against Java. Neither run measured time.

| Keys       | Result           | Time  | Unlinked | Climbs  | Empty key | Taken back | Collapses |
|---|---|---|---|---|---|---|---|
| 1,000,000  | 0 differences    | 42 s  | 154,880  | 143,000 | 136,950   | 70         | 40        |
| 10,000,000 | 0 differences    | 241 s | 880,734  | 805,555 | 771,623   | 446        | 401       |

**022's full set, its first part** (`cross.sh random` on
`work/full/a.specs`, 11:30 to 11:48, 1,079 s, on the build of
`fb2a6d86`): StreamDigest's twelve configurations at full size in their
four modes and CoreSame's two workloads: `CROSS random OK`, **0
differences** in 50 workloads, 99 crash cuts and 100 budget runs (budgets
of 1 and 64,000 bytes). These workloads delete little: 14,003 climbs, no
take-back, no root collapse.

**Not run**: the full set's other workloads, Gen's seeds 1 to 400 with
their options (`work/full/b.specs` and `c.specs`, 200 workloads each),
and the 10M-key scale workload of puts; `cross.sh full`'s own crash cuts,
corrupt variants and runs in turns on those workloads. The coordinator
stopped the work here (08:50: the account's usage; the commands are in
the State section). A sample of twelve of them (Gen's seeds 1 to 8, 201
and 341 with the full set's options, and two more `del:` seeds) gave 0
differences (08:25, 88 s).


## 3.3 Corrupt streams

* **The corrupt-stream set** (`corruptset.sh`; C's dumper with `-check`),
  the whole set, seed 1, on the gate's build of `ed02ab6d`, under the
  lock (08:43 to 08:45, 122 s): `CORRUPTSET OK`, 6,217 damaged copies of
  the release's own streams, the same status, text and message in Java
  and C in each: 2,569 refused by both with the same exception and
  message, 3,560 started by both, 66 with a later read failing alike, and
  22 of 014-01's zero fill, the one class counted as known. (The
  candidate's set had 6,253 copies, 022-04, section 8.2: the streams of
  format 6 are other streams, so the tester's sample is another.) The
  gate's quick set has 65 copies.
* **020-32's two copies** are in both: `found-long-3971389/0`
  (`testFoundDescentCycle`: both starts take it, and a read of each
  dumper then fails on the cycle, with the same text, where each would
  have gone round without end) and `found-long-3971451/0`
  (`testFoundLinkByIdPrevPos`: both starts refuse it with the same
  `StreamFormatException` and message).
* **`corrupt.sh`** (damaged files and bit flips of C's and Java's
  directories, started by both dumpers; 08:45 to 08:46, 76 s): `CORRUPT
  OK`, 144 variants (83 refused by both, 43 started, 18 started with a
  read failing later), 101 messages compared, 0 differ.


## 3.4 Java's vectors

Written again from the release (`bergdb.core.Vectors`): of the thirteen
files, `dag.txt` (530 lines differ), `knode.txt` (68), `records.txt`
(62) and `reclaim.txt` (4) changed, with format 6, the empty key first
in a split's second half and the deletes' unlink; the other nine are
equal. C's unit tests give every line of the new files: the Dag's
transactions with `dirtyNodeBound` before each and the state after it
(`t_dagvec.c`), the key node's operations and stored bytes
(`t_knodevec.c`), the records (`t_records.c`) and the reclaim runs'
digests from the decided cut (`t_reclaim.c`). A fourteenth file is new,
`sorted.txt` (section 3.5).


## 3.5 Java's tests

Java's test methods that the release added or changed in the Core, by
022-05's classes (P: C had it; W: written now; N: not for C):

| Java's class                         | Test                                        | Class |
|---|---|---|
| `DagTester`                          | `testNoKlongNamesATakenBackNode`            | W |
| `DagTester`                          | `testDeleteEveryKeyAfterTheRootSplit`       | W |
| `DagTester`                          | `testDirtyNodeBoundOfDeletes`               | W |
| `DagTester`                          | `testDirtyNodeBoundSumsCollapsesOverTrees`  | W |
| `DbTesterDelete`                     | `testTransformedPutsAndDeletesWithRestarts` | W |
| `DbTesterDelete`                     | `testDeleteEveryKey`                        | W |
| `DbTesterDelete`                     | `testOneOperationAKeyAfterTransformations`  | W |
| `DbTesterDelete`                     | `testReusedTransKeepsItsKvs`                | W |
| `DbTester`                           | `testTransformedKeysSorted`                 | W |
| `DbTesterGetMany`                    | `testEndKeyAsEndpoint`                      | W |
| `DbTesterGetMany`                    | `testEndKeyPassesNoDeletedKeys`             | W |
| `DbTesterGetMany`                    | `testEndKeyPassesNoDeletedLongKeys`         | W |
| `DbTesterGetMany`                    | `testEndKeyChainEdges`                      | W |
| `Eviction`                           | `testDeadHand`, `testDeadHandF`             | W |
| `Eviction`                           | `testDeadHandBoundsItsWork`                 | N |
| `ReclaimReaderTester`                | `testHeldReadersAndTheDeadHand`             | N |
| `Reclaim.Tester`                     | `testQueueBeforeAKeyEnds`                   | W |
| `Reclaim.Tester`                     | `testRandomPutsAheadDoNotSlowTheScan`       | W |
| `CorruptStreamTester`                | `testFoundDescentCycle`                     | W |
| `CorruptStreamTester`                | `testFoundLinkByIdPrevPos`                  | W |
| `StoredTrans`                        | `testRefusesOldFormat`, `...NewerFormat`    | W |
| `NodeCollection`                     | `testLinkToCanonicalCheck`                  | W |
| `DbTesterFailure`                    | `testUncheckedCloseError...` (a wait)       | N |
| `FileStreamPowerLossTester`          | three tests: `close()`, not `stop()`        | N |
| `PubTesterIndex`, `PubTesterPrimary` | the Pub layer's                             | N |

* **Where they are in C**: `DagTester`'s in the new `t_delete.c`
  (`delete_...`, on `mdb`); `DbTesterDelete`'s and `DbTester`'s in
  `t_dbtester.c` (`dbt_transformed_puts_and_deletes_with_restarts`,
  `dbt_delete_every_key`, `dbt_one_operation_a_key_after_transformations`,
  `dbt_reused_trans_keeps_its_kvs`, `dbt_transformed_keys_sorted`);
  `DbTesterGetMany`'s in `t_dbgetmany.c` (`dbgm_end_key_...`);
  `Eviction`'s in `t_evict.c` (`evict_dead_hand`: one run, the databases
  in memory, so without Java's restarts); `Reclaim`'s in `t_reclaim.c`;
  `CorruptStreamTester`'s two as copies of the corrupt-stream set (section
  3.3) and `t_delete.c`'s `delete_cycle_in_the_dag`; `StoredTrans`'s in
  `t_serial.c`'s `serial_refuses_other_formats`; `NodeCollection`'s in
  `t_ncoll.c`'s `ncoll_link_to_canonical_check`.
* **Not for C** (N): a step's bound of the dead hand (C's round has no
  steps), readers in threads, Java's storage thread, `stop()`, the Pub
  layer.
* The Dag's tests run on `mdb` (a Dag without a database), as Java's on a
  Dag with a dummy follower; where Java draws with `java.util.Random`,
  C draws the same kind of input.
* **Reclaim's liveness tests** end their iteration in 15 and in 7
  transactions, the numbers that 023-08 and Java's comments give for the
  release's reclaim.
* **The two scans of SE's tests** follow 8 and 9 key nodes with the end
  key and 11 and 11 by the stop condition alone; Java's comments say 9
  for the long keys and 11 and 11.
* **`testReusedTransKeepsItsKvs`**: its case of two keys is Java's; its
  case of one shared key shows C's departure (section 6, point 2).
* **`testEndKeyChainEdges`**: C's chain is not driven from outside
  `getmany.c`; the test has the scan's result and its `eod`, and
  `Dag.getMany`'s two refusals.
* **Beyond Java's tests**: `sorted.txt`, a new vector: the streams of two
  databases that the release's Java wrote for
  `testTransformedKeysSorted`'s and
  `testOneOperationAKeyAfterTransformations`'s operations (`Vectors.java`,
  with Java's own classes). C runs the same operations through its API
  and writes the same bytes (`dbt_transformed_streams_are_javas`). The
  cross workloads have no transformations, so this is where SORT meets
  Java's bytes. A third stream of `sorted.txt`, `empty-key`: the key of
  no bytes, whose one segment has the compare value 0, as the empty key
  klong that every inner node begins with (LE-b), with deletes around it:
  put with `k00` to `k59`, the left half deleted, the empty key deleted,
  put again with the rest deleted, the database emptied, two keys put. C
  gives the values and the counts after each step and after a restart,
  and Java's bytes (`dbt_empty_key_stream_is_javas`); no ikey gives the
  empty key, so no cross workload has it. And
  `evict_taken_back_nodes_leave_the_table` (section 3.6), and
  `delete_descent_cycle_check`, Brent's detection on
  its own (a path of 100,000 distinct ids never fails; 36 paths into
  cycles are found within 4 (p + c) + 4 steps).


## 3.6 Negative controls

Each ported mechanism taken out of a copy of `c/src`, one at a time, the
unit tests built from the copy with the test build's flags, and the tests
of that mechanism run (`/Users/f/fl/bench/2026-11-11/cc/work/neg/`,
`run.sh` and `patch.py`): each fails, so each test sees what it tests.

| Taken out                                    | Tests that fail                                 |
|---|---|
| F12: the leaf's klong repointed in place     | `delete_no_klong_names_a_taken_back_node`       |
| TB: the retarget of every klong of tt        | `delete_no_klong_names_a_taken_back_node`       |
| LE-b: the empty key in a split's second half | 7: Java's vectors (`knodevec_java`), the Dag's  |
| RC: root collapse                            | `delete_every_key_after_the_root_split`, 2 more |
| K4: a delete counted as before 2026.4        | `delete_dirty_node_bound_sums_collapses_...`    |
| K4, B1: the most of one tree, not the sum    | `delete_dirty_node_bound_sums_collapses_...`    |
| SORT: no sort after the transformations      | 3: `dbt_transformed_streams_are_javas`, 2 more  |
| SE: the end key never ends a scan            | `dbgm_end_key_as_endpoint`, `..._chain_edges`   |
| DEAD: no dead hand                           | `evict_dead_hand`                               |
| DROP: at the transaction's end               | `evict_taken_back_nodes_leave_the_table`        |
| DROP: in the startup's rerun                 | `evict_taken_back_nodes_leave_the_table`        |
| CYC: the descent's check                     | `delete_descent_cycle_check` (180 checks)       |
| PREV: the refusal of a damaged prevPos       | `ncoll_link_to_canonical_check`                 |

* **DROP had no test at first**: with `nt_drop_node` doing nothing, the 117
  unit tests of the database, eviction, restarts and reclaim all passed (a
  taken-back node then stays in the node table, at a vpos, neither dirty
  nor ever written, until the close: memory, no byte). So
  `evict_taken_back_nodes_leave_the_table` was written for it: transactions
  that put 40 keys before the 40 live ones and delete those, 59 nodes
  taken back, a restart twice; after each transaction and each start no
  index object that was never written is in the node table unless it is
  dirty.
* **K4's first row**: `delete_dirty_node_bound_of_deletes`, Java's
  `testDirtyNodeBoundOfDeletes`, passes also with a delete counted as
  before 2026.4 (one klong in its leaf): the nodes that a delete unlinks
  leave the dirty set that the test counts, so its inequality has room.
  The sharp test of the count is B1's (section 5, note 3).
* Without CYC's check `delete_cycle_in_the_dag` and the corrupt set's copy
  do not fail: they do not end; the control runs the detection's own test.


# 4. Faults of C

No fault in C's bytes or answers was met after the port: every
comparison with the release's Java showed 0 differences (section 3).
Before the port C could not read the release's streams at all (format 6
refused), so there is no negative control of the whole as in 022-04,
section 3.6; the controls are those of the single tests (section 3.6).

* **A test's bound that was not an invariant** (`t_evict.c`'s
  `evict_twins`, C's own, of 022-06's U1-4): it held that the resident
  bytes less the pinned ones are at most the budget or the node table's
  bytes. While a floor raises the trigger, the pinned bytes can be less
  than the floor: `ev_run` takes the floor as old only when D has fewer
  nodes than at the floor's sweep, and a transaction with its take can
  leave D with as many nodes and fewer bytes. The trees that 2026.4's
  deletes make gave one such case (a budget of 2,000 bytes, node size 8,
  seed 12, transaction 226: D of 7 nodes before and after, 120 bytes
  fewer; the bound passed by 40 bytes). The test now adds that difference
  to its bound. The library is as it was; whether `ev_run` should also
  take the floor as old when D's bytes have shrunk is a question of C's
  own policy (section 9).


# 5. What the port found in Java

No fault of the product. Every difference between C and Java during the
port was C not yet ported. Three notes for the coordinator; none changes
a byte or an answer of a valid database:

1. **`OpData.descentPower` is an `int`** (020-32's cycle check; low,
   theoretical). Input, on the release's classes
   (`work/jk4/src/bergdb/dag/PowerProbe.java`): `descentFrom`, then
   1,073,741,830 calls of `descentTo` with distinct node ids (2^30 + 6),
   then the ids 4, 6, 8 again and again. Expected: the cycle's exception
   within about twice the steps of the path and the cycle, as Brent's
   detection moves its mark at every power of two. Got: no exception in
   3,000,000 steps of the cycle (after a path of 1,000 nodes: found after
   26). At step 2^30 `descentPower <<= 1` gives -2^31, and then 0;
   `++descentSteps == descentPower` is then never true and the mark stays.
   Only `Dag.dirtyNodeBound` descends that far in one check (one
   `descentFrom` a key, over all its segments: a key of gigabytes, on a
   damaged stream); a get and a put start the check again at each segment
   tree. C counts unsigned, which wraps to 0 and moves the mark again
   every 2^32 steps.
2. **`Dag.statUnlinked` and the six other counters are static**: two
   databases in one JVM count into the same numbers, so
   `DbTesterDelete.testDeleteEveryKey`'s and `DagTester`'s
   `statCollapses > collapses0` hold if any database of the JVM collapsed
   a root meanwhile. Tests and measurements only ("written by the writer
   only" is each database's writer). C's are fields of the put data.
3. **`DagTester.testDirtyNodeBoundOfDeletes` does not test K4's count.**
   Found by C's negative control (section 3.6), then reproduced in Java.
   Input: release 2026.4's `java/src` in a scratch copy
   (`/Users/f/fl/bench/2026-11-11/cc/work/jk4`), with
   `Dag.dirtyNodeBound`'s `if (deletes[k])` made `if (false &&
   deletes[k])`, so that a delete is counted as before 2026.4 (one klong
   in its leaf, nothing for its path, nothing for the collapses); the two
   tests called with `-ea`. Expected: `testDirtyNodeBoundOfDeletes` fails,
   as its Javadoc says that it tests K4's bound against the nodes that a
   transaction makes dirty. Got: it passes, in its random part, its chains
   (2) and (2b) and its transactions of 1,000 and 100,000 deletes; only
   `testDirtyNodeBoundSumsCollapsesOverTrees` fails ("klongs counted for
   the space root: 0"). The reason: the nodes that the deletes unlink and
   collapse leave the test's dirty set (`keyNodeReplaced` removes them),
   so the set stays below the walked nodes that the bound starts from.
   So K4's count of a delete has one test, B1's, which checks the space
   root's klongs in one shape. A test only; the product's count is as
   023-07, section 5.4 says.


# 6. Departures from Java

`c/readme.md`, section 11, has them, points 6 to 8 new. None is in the
stream's bytes.

1. **The dead hand's round is made whole** (DEAD). Java's hand takes a
   round over the node table in steps, one a transaction, of 4,096 units
   of work and 2 ms at most, as readers run meanwhile (023-07, section
   5.6; 023-11, F2). C makes the round whole in the call after the cut
   that moved the decided cut position, as C's sweeps are made (one
   caller; what it frees depends on the calls only, never on timing): the
   node table's slots and the pointers of the key nodes that stay, once
   for each cut that moves. With a budget only, as Java's: with
   `BERGDB_NO_EVICT` the memory of ended versions stays until the close.
2. **A transaction executed again after two of its transformed puts
   became one key has one of them** (SORT; Java's 023-11, F1). A C
   transaction is its builder; a put keeps its transformed key in place of
   the key given, and each execute builds the transaction again, one put a
   key (both as `bergdb.h` said before this port). So the second execute
   has the later put only, where Java's `Trans`, built once, keeps both
   KVs. Puts that got different keys keep their own state, as Java's.
3. **`bergdb_range.end_key` is the stop condition alone** (SE). Java sets
   `GetMany.endKey` in the Pub API's scans, which C does not have. A C
   range that set both would give the same pairs but another `eod` (the
   end key ends a scan as the end of the database does). Kept as it was;
   the Core has the mechanism and its tests.

The open departures of 022-04, section 6, stand (NOMEM a refusal, the
settings' refusal text, the unforced tail, a count of 0 is no count), and
022-05's (a close after a reported failure).


# 7. Size and time

**Size**: `git diff --numstat 1d5b18fa fb2a6d86 -- items/022-bergdb-c/c`:
43 files, 5,304 lines added and 466 deleted, comments and blank lines
included:

| Part                                      | Files | Added | Deleted |
|---|---|---|---|
| `src/`, the library                       | 18 | 1,509 | 38  |
| `include/bergdb.h`                        | 1  | 27    | 4   |
| `test/unit/`, unit tests                  | 10 | 2,535 | 14  |
| `test/unit/vectors/`, Java's vectors      | 5  | 336   | 331 |
| `test/cross/`, the harness and its Java   | 7  | 781   | 29  |
| `readme.md`, `before-commit.sh`           | 2  | 116   | 50  |

Of the library's lines, 907 are `dag.c`'s (the delete path and the
bound), 162 `db.c`'s, 82 `knode.c`'s, 70 `getmany.c`'s, 69 `evict.c`'s.
Java's own change was about 1,250 lines of product code (023-09, section
1). `GenDel.java` is 394 lines, the new `t_delete.c` 831.

**Time** (2026-11-11, from `date`):

| When           | What                                                          |
|---|---|
| 07:10          | the start: 022's documents, 023-07 to 023-09, Java's diff     |
| 07:20          | the first build with F6, LE-b, F12, UP, TB, RC, K4, SORT, DROP, CYC |
| 07:26          | the unit and functional tests pass, Java's new vectors among them |
| 07:30          | `cross.sh quick` against the release: 0 differences           |
| 07:41          | `GenDel.java`; a first run of 16 `deletes` workloads: 0 differences |
| 07:43 to 07:52 | Java's tests ported; SE, PREV; the corrupt set's two copies   |
| 07:53 to 08:06 | no builds (another agent's timing run): DEAD, `sorted.txt`, the documents |
| 08:08          | everything built: 548 unit tests pass                         |
| 08:13          | the negative controls; DROP's test written for the one that passed |
| 08:22          | the first commit, `ed02ab6d`                                  |
| 08:28 to 08:46 | the first hold of the lock: the gate, `deletes`, the corrupt sets |
| 08:39          | the empty key's stream and test, `fb2a6d86`                   |
| 08:47 to 11:25 | waiting: other agents' holds, then the integration's gates first |
| 11:25 to 11:52 | the gate on the head, the full set's first part, the scale deletes |

From the start to the gate's `C BEFORE COMMIT OK`: 1 hour 23 minutes, of
which about 30 minutes waited for the lock or for a timing run to end.


# 8. 022's night steps

Not run and not changed by this work. In `/Users/f/fl/bench/022/night/`
there are `runs-2026-4.sh` (022-02's step 4, the candidate's long runs)
and `step5.sh` (2026.3's, which Frans decided not to run, 022's log,
2026-11-10); there is no `step6-2026-4.sh`. After this update:

* **`runs-2026-4.sh`** pins `REV=8772b934`, C at the candidate with
  `JAVA_REF=git:d00096e` in `int.git`'s branch `2026.4`. Its runs would
  test the candidate, which is not the release: record format 5, and none
  of 023's delete path. It needs: this port's commits in `int.git` (the
  coordinator's landing; or `R` a clone of the repository that has them),
  `REV` set to the landed head, and no `JAVA_REF` (the default is the
  release). Its part `cross-full` now has 40 `del:` workloads more (its
  estimate of 45 minutes rises by a few), and a part for
  `cross.sh deletes` (the 190 workloads; section 3.2 has its time)
  belongs before `power-c`. Its smoke test must pass again before a
  `.READY` marker is written, as the tree is another.
* **`step5.sh`** is the 2026.3 port's and stays as it is, not to be run.


# 9. Left, and open points

1. The full set's Gen workloads and the 10M-key workload of puts (section
   3.2, "Not run"), and 022's long runs (section 8) on the landed tree:
   `cross.sh full`, `scale`, the corrupt set on seeds 2 and 3,
   `power.sh`, `random.sh`, `long.sh`.
2. Frans's open points of 022's log (2026-11-09, 19:30, point 4) stand as
   they were; this port touched none of them.
3. For Frans, from this port: the three departures of section 6, each kept
   at the choice that changes least (the API as it was); and whether C's
   eviction should take its floor as old when D's bytes have shrunk
   (section 4).
4. The builder's rule "the last operation wins" (023-08, section 7) is not
   in release 2026.4 and not in C: C follows a release.


# Log

2026-11-11. Created and written by the agent `cc` of coord-1111, from
07:10 to 11:55; the commits are on the clone's branch, for the
coordinator to land (Frans approved the landing when the gate reports;
the coordinator, 09:33).


# State

2026-11-11, 11:54, by `cc`. The work is stopped here, by the
coordinator's word of 08:50.

**Done, gated and committed** on the clone's branch, three commits on
`main`'s `1d5b18fa`, only `items/022-bergdb-c/c/` changed:

* `ed02ab6d`: the port (section 2: all thirteen IDs), Java's tests of the
  release in C (section 3.5), `cross.sh deletes`, `c/readme.md`,
  `bergdb.h`. Gate: `C BEFORE COMMIT OK (297 s)`, 08:33.
* `ad2a3023`: `cross.sh scale SCALEDEL=1` (the harness only).
* `fb2a6d86`, the head: the empty key's stream from Java and its C test.
  Gate on the head: `C BEFORE COMMIT OK (302 s)`, 11:30.

**Compared with release 2026.4's Java, 0 differences in each:** the quick
set (in both gates); the 190 `deletes` workloads with 116 crash cuts, 85
corrupt variants, 6 runs in turns and 760 budget runs; the scale workload
of deletes at 1M and at 10M keys; the full set's first part, 50
workloads; the whole corrupt-stream set, 6,217 copies, and `corrupt.sh`;
Java's vectors, fourteen files. The negative controls of the new tests,
all thirteen, fail as they must.

**Found:** no difference between C and Java, no fault of Java's product
code; three notes on Java (section 5), two reproduced in a scratch copy;
one C test's bound corrected (section 4); three departures, none in the
bytes (section 6).

**Not run, for a later quiet slot** (each one run in one slot, not
timing, in `/Users/f/fl/bench/2026-11-11/cc/gate/items/022-bergdb-c/c`,
the tree of `fb2a6d86`, whose `build/` is there from the gate of 11:30;
else `./build.sh` and `sh test/cross/java-build.sh` first; about 25
minutes each for b and c, about 6 for scale):

    W=/Users/f/fl/bench/2026-11-11/cc/work
    sh test/cross/cross.sh random SPECFILE=$W/full/b.specs C=build/test OUTDIR=$W/out/full-b
    sh test/cross/cross.sh random SPECFILE=$W/full/c.specs C=build/test OUTDIR=$W/out/full-c
    sh test/cross/cross.sh scale C=build/release OUTDIR=$W/out/scale-10m

`b.specs` is Gen's seeds 1 to 200, `c.specs` its seeds 201 to 400 with
the full set's options; `scale` is the 10M-key workload of puts. Each
must end with `CROSS ... OK`; a difference is a line `DIFFERENCE ...` in
`OUTDIR/report.txt`. And 022's long runs (section 8), which need the
landed tree.

**For the coordinator:**

* To land: the three commits of `022-07-c-2026-4` in the clone,
  `1d5b18fa..fb2a6d86`; 022's readme needs its line for 022-07, and
  022-04 and 022-02 can say that step T is this subitem.
* Java's three notes: section 5 (inputs, expected, got).
* A fault of mine: between 07:21 and 07:29 I ran C builds, C's unit tests
  (three runs of about a minute) and one `cross.sh quick` (112 s, two
  JVMs) while the lock's owner file said "touch timing: the last touch
  before the fix, 1M and 10M keys 07:21:11": I had checked the lock for
  heavy runs only, not the owner file's "timing" before light ones. That
  timing run may have been disturbed. From 07:29 every build and test of
  mine waited while an owner file said "timing". One more overlap of
  about 40 s: a unit test run of mine began at 07:53:04, 8 s before the
  second "touch timing" run took the lock (07:53:12).
* `/Users/f/fl/bench/2026-11-11/cc/work/out/` holds the runs' outputs
  (1.3 GB); it can be deleted once read.

**Where things are:** clone `/Users/f/fl/bench/2026-11-11/cc/clone`,
branch `022-07-c-2026-4`, head `fb2a6d86`; the gate's worktree
`/Users/f/fl/bench/2026-11-11/cc/gate` (detached at `fb2a6d86`, with its
`build/`); logs, the runs' scripts (`run1.sh`, `run2b.sh`, `run3.sh`),
the negative controls (`neg/`) and the scratch Java of section 5
(`jk4/`) in `/Users/f/fl/bench/2026-11-11/cc/work/`. No slot is held and
no command of mine is running.

**How to continue:** in the clone, `cd items/022-bergdb-c/c`,
`./build.sh`, `build/test/unit`, `build/test/func`; the gate is
`./before-commit.sh` (it must print `C BEFORE COMMIT OK`); the sets are
`sh test/cross/cross.sh quick|deletes|full C=build/test` and
`sh test/cross/cross.sh scale [SCALEDEL=1] [SCALE=N] C=build/release`.
