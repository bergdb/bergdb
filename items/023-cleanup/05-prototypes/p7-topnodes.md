# 023-05 P7. The dirty top nodes, written with the top node that names them

Created 2026-11-10 by Frans Lundberg. Status: open.

Prototype P7 of 023 (023-05) deals with the run of dirty top nodes that
stays in D after a mass delete (P6, section 5; P4's Q4; 023-06, section
11.3, point 4). Frans decided at 13:42 (023-06, Z13): "solve this now", in
2026.4. The code is on the branch `023-p7-topnodes` of the clone
`/Users/f/fl/bench/2026-11-10/p7/clone`, on P4's head `0e66d1c9`. The
review's design note is 023-06, section 18, and its correction is 18.7.

In short:

* **The cause, confirmed by a probe.** Rule A keeps a written top node
  dirty while a top node it names by a skip pointer is dirty. At T1's drive
  at N = 1M, each 1,000 drive transactions rewrote about 2,790 top nodes
  that stayed dirty. Each of them named a dirty skip target that its record
  did not hold, and 2,700 of them had a clean root.
* **Fix (a), built and gated.** The take also writes, in the same record,
  the dirty top nodes that the record's top nodes name by skip pointers.
  The chain is then written in one record: the still-dirty fixpoint cleans
  it, or, where a root below is dirty, files it whole in the newest list,
  so no inversion forms (6.5). A node written this way leaves its
  got-dirty list. A start drops a got-dirty id whose
  node has a version in a later record. The record syntax does not change.
* **T1 at N = 1M, drive 12,000** (twin / emptied database):
  * Before: max D 94 / 178; objects after the restart 83 / 184; dirty top
    nodes in the drive's second half, the most, 61 / 158.
  * With (a): max D 35 / 34; objects 25 / 33; dirty top nodes 12 / 5.
  * C6, C9 and a new check of the window pass. Before, all three failed.
* **Bytes.** The emptied database's drive writes 27 % fewer bytes (1,307
  against 1,800 a transaction) and the twin's 8 % fewer. Top node versions
  written per top node made: 7 against 40 (twin 11).
* **023-06's rule (b) is unsound.** Section 3 gives the counterexample, and
  `DbTesterRestart.testRuleBCounterexample` fails with (b) at its first
  seed: a historical read after a restart meets "Pointer to node 1931,
  which is not in the stream and not in memory". The review agrees (023-06,
  18.7).
* **(b'), the sound variant, built as an experiment.** It uses the time
  the child last went from clean to dirty, not the time of its list.
  * The time is stored in the got-dirty entry with the replacement time:
    (id, position, r, e), 32 bytes. The same stream with restarts.
  * On P5's branch, with (a), it lowers P5's left-out nodes right after
    the deletes from 248 to 150, and the deletes' bytes by 15 %. Kept in
    memory only, it gave 71 and 24 %; the stored form's longer entries move
    the take's phase (6.2).
* **P5's family over a long drive** (Frans's question for Z21). On P5's
  branch with (a) alone, T1 "inter" with 200,000 drive transactions:
  * The 259 left-out nodes leave D within 10,000 transactions.
  * After that, D holds 1 to 16 unreachable key nodes at each checkpoint,
    and none of them is still in D at the next checkpoint.
  * So the family does not stay; (b') makes it leave sooner (section 6.3).
* **Gates on (a):** level1 full, level2 full (70 conformance traces OK)
  and level3 full OK; level4 quick OK but for one conformance trace of 15,
  which fails C-S as expected (5.3). The unit steps leave out 3 tests
  whose expected values change (5.1). CrashTest, StreamDigest's four modes
  and RestartInvariance on runs that write ahead are OK.


## 1. The cause

### 1.1 The probe

CleanupRule (023-03's T1 and T4) got a probe of D's top nodes, after P6's.
Db counts the top nodes that the still-dirty test keeps dirty, and why
(commit `7eb0ba70`; the rest of the code is P4's).

* `tops`: the dirty top nodes.
* `inv`: the pairs of consecutive dirty top nodes, by ordinal, in which the
  newer one waits in an older got-dirty list than its predecessor.
* `rootDirty`: the dirty top nodes whose root is dirty.
* `still=a/b/c` (`Db.Internal.stillDirtyTops`), counted since the start:
  * a: the top nodes of the records that the still-dirty test kept dirty;
  * b: those of them with a dirty skip target that the record does not
    hold;
  * c: those of these with a clean root.
* `dprobe=1`: each dirty top node, with its list, its root and its dirty
  skip targets.

T1 at N = 1M, drive 12,000, P4's code (`runs/base-t1m-still.txt`). "still,
per 1,000" is the difference from the row before; the first row counts from
the start.

| At drive | Twin: tops | inv | Emptied: tops | inv | rootDirty | still, per 1,000       |
|---|---|---|---|---|---|---|
| 1,000    | 50         | 9   | 60            | 15  | 60        | 4,811 / 993 / 19       |
| 2,000    | 57         | 10  | 130           | 40  | 91        | 5,167 / 5,107 / 142    |
| 3,000    | 56         | 10  | 158           | 39  | 10        | 10,571 / 9,834 / 5,572 |
| 6,000    | 56         | 10  | 159           | 39  | 4         | 3,098 / 3,071 / 2,981  |
| 12,000   | 60         | 11  | 157           | 39  | 6         | 2,790 / 2,790 / 2,699  |

### 1.2 What it shows

* From drive 3,000 on, the 157 or so dirty top nodes have consecutive
  ordinals, and only 4 to 6 of them have a dirty root.
* Each 1,000 drive transactions rewrite about 2,790 top nodes that stay
  dirty. Each of them has a dirty skip target outside its record. So each
  is kept dirty by a neighbour that waits in a newer list, not by its root.
* The 39 inversions stay frozen from drive 3,000 to 12,000, as P6 found.
* P6's account holds (P6, 5.2):
  * the take writes lists oldest first;
  * Rule A puts a re-dirtied node into the newest list;
  * at an inversion, the newer node is written first, sees its predecessor
    dirty, and waits one more cycle, and so does every node above it.
* The twin has the same run, shorter: 50 to 61 dirty top nodes, 10 or 11
  inversions, about 770 such rewrites per 1,000 transactions.


## 2. Fix (a): the take writes the chain of dirty top nodes

### 2.1 What, when, by whom

* **What.** `TransSeq.take` first chooses whole transactions as before.
  Then `Db.writeAheadTops` adds to the record the dirty top nodes that the
  record's top nodes name by skip pointers (pointers 1 to h, which name
  older top nodes), and those that these name, transitively. Roots and key
  nodes are never added.
  * The order: the record's top nodes in their order, and each one's skip
    pointers by index. Each node added is examined in turn. This is a
    function of D and the record, so of the stream.
  * The limit: a node is added only while the record stays within the
    record limit, counted as `store()` counts it (the node's size and its
    got-dirty entry).
* **When and by whom.** The writer, in `Db.store`, under the write lock:
  after the take, before `resolvePointersOfTakenNodes`. So the added nodes'
  pointers are resolved by node id like the taken ones'. Then the record's
  nodes are cleaned, and the still-dirty fixpoint runs over all of them,
  unchanged (`handleStillDirtyNodes`, Rule A as today).
* **A node written ahead leaves its list.**
  * Each top node knows the got-dirty list it waits in (`TopNode.dirtyIn`).
    `TransInfo.addGotDirtyNode` sets it, and it is cleared when the list
    is taken or the node leaves the list.
  * `TransSeq.takeAhead` removes the node from that list and lowers D's
    count, which paces the take.
  * A node that the running transaction made dirty waits in no list of the
    sequence yet, and is not added.
* **A node that stays dirty** (its root is dirty, or a target did not fit
  the limit) joins the running transaction's list, as any node that Rule A
  keeps.
* **Switch.** `-Dbergdb.p7.ahead=false` turns it off (prototype only).

### 2.2 The start's rule

023-06, 18.7 states the rule for a start, and P7 built it as follows
(`DbStarter.rerunTransaction`):

* D is rebuilt from the got-dirty ids of the rerun records, as before. An
  id whose newest version in the section (Rule R's `newById`) lies after
  that record's last position is dropped.
* The node was pulled ahead of that list. If it is in D, it is there by
  the newer list of the record that wrote it, and stayed dirty.
* Without write-ahead no such id exists: a node of a rerun record's list
  stays dirty until that list is taken, and that comes after the end of
  the stream. So today's streams are unaffected, and the rule drops exactly
  what the running database took out.
* The lists, their counts, D's count, the own bytes and the span are then
  the running database's, so the take decides the same after a start.

### 2.3 How the other parts see it

* **The record.** It holds more top nodes, with no change of syntax. What
  a got-dirty id of record j means changes:
  * before: the node is dirty until j is taken;
  * now: the node is dirty until j is taken, or until a later record
    writes it.
* **The node-id check** (`canonicalNode`) is unchanged. A dropped id is
  never read. A node written ahead that stayed dirty is in the list of the
  record that wrote it, with that version's position, and is read and
  checked there.
* **Rule A and the still-dirty test** are unchanged (`javaTest`). They run
  over the larger record.
* **A node written before a node it names.**
  * In a record, every node's new position is set before any byte is
    serialized (`StoredTrans.prepareToSerialize`). So a top node and the
    targets written with it name each other's new positions, in any order.
  * A target not written (clean, or beyond the limit) is named by its last
    written position or its vpos, as today. Rule A keeps the naming node
    dirty while the target is dirty.
  * So no written node is left clean naming a position that is not
    written.
* **The Lean model** (not changed here):
  * Its step 5 takes the nodes of D with d(x) at most s(i). With (a) it
    must also take the closure over the skip pointers of the taken top
    nodes.
  * INV-1 becomes: D holds the nodes of gd(j), s(i) < j <= i, that have no
    version in a record after j. L-OUT's argument is unchanged (023-06,
    18.7).
  * T1 and T2 need checking with the new step. T3 needs nothing: the
    startup pos is chosen as before, and T3 holds for every pace.
* **The trace checker.** C-S runs the model's step from Java's state with
  Java's startup pos. At a record that writes ahead, Java's record has
  versions that the model's lacks, and Java's D differs. C-S fails there,
  as expected (5.3).

### 2.4 Tests added

* **`DbTesterRestart.testDirtyTopNodesWrittenAhead`** (unit, 0.4 s). It
  runs T1's twin: "/a.txt" overwritten 3,000 times with 1,000-byte values,
  reclaim with a retain duration of 100 transactions, and a startup
  distance of 100,000 bytes. It checks:
  * at most 30 dirty top nodes after each transaction from 1,000 on. With
    the write-ahead switched off it fails with 77; with it, 21 at most;
  * no top node kept dirty by a skip target outside its record, and nodes
    written ahead;
  * with a restart every 97 transactions: the same stream byte for byte,
    after each start the same got-dirty ids in the same lists, and starts
    that dropped written-ahead ids.
* **`CleanupRule hello check=1`** (023-03's T1). It exits with 1 unless:
  * C6 holds: max D in the window at most the twin's + a_n;
  * C9 holds: the objects after the restart and the probe at most the
    twin's + a_n;
  * the window check holds: the most dirty top nodes at a checkpoint of
    the drive's second half at most the twin's most + a_n. A run that
    ratchets up fails it.
  * Here a_n = 10 + h_fill, the bounded allowance with L = 1.
* **`RestartInvariance`** prints the top nodes written ahead and the ids
  its starts dropped (section 5.2).


## 3. Rule (b) of 023-06, 18.2, is unsound

### 3.1 The gap

023-06's 18.2 makes Rule A for a replaced node x compare d(y), the time of
the list its dirty child y is in, with r(x), x's replacement time. Its
argument says: "y dirty with d(y) >= r(x): y was clean just before d(y), so
lv(y) is good for every t < d(y) (INV-3)".

* sis-model.md's INV-3 holds only for a node whose latest version was
  written before d(y), so one that got into D by marking (step 3).
* A node that Rule A refiles at record j (step 7) has d(y) = j, and its
  latest version is written in j. That version names its dirty children's
  older versions, or their vpos.
* So it is good only for times before the oldest unwritten change below
  y, and that time can be before r(x).

### 3.2 The counterexample

x is current, with child y and grandchild z.

1. y has been dirty since t0, and so has x: marking marks the whole path.
   Both are in gd(t0).
2. z changes at k > t0 and goes into gd(k).
3. x is replaced at r(x), with k < r(x).
4. Record j1 >= r(x) takes gd(t0), but not gd(k). x and y are written.
   * y is refiled, since z is dirty: d(y) = j1 >= r(x).
   * By (b), x is clean. x@j1 names y@j1, which names z's version from
     before k.
5. Later z is written, and y is written clean. x never is again.
6. After a restart whose section begins later, a lookup at a time in
   [k, r(x)) reads x@j1, y@j1 and the old z. It misses z's change at k,
   or meets a vpos where z had no version.

With `javaTest`, x stays dirty until y is clean.

The window of dirty top nodes is this case: its nodes are refiled at every
write. So (b) would dissolve the window through the unsound step.

### 3.3 The test

`DbTesterRestart.testRuleBCounterexample` searches for the case at random.
It runs Level2Run's workload (node size 8, startup distance 2,000 bytes,
no reclaim, `/k/` and `/long/` keys, deletes), with one restart at the end,
and then reads every key at every time of its history and just before.
Mode `-Dbergdb.p7.ruleb=d` is (b) as 18.2 states it.

| Rule                                | Seeds | Result                                    |
|---|---|---|
| today's (`-Dbergdb.p7.ahead=false`) | 30    | passes                                    |
| (a), the default                    | 30    | passes                                    |
| (b) as written, with or without (a) | 1     | fails: the read of /k/19 at time 69 fails |
| (b'), with or without (a)           | 30    | passes                                    |

(b)'s failure: "Pointer to node 1931, which is not in the stream and not in
memory, index 4 of node 915". The database then refuses all work. The
review's author checked the counterexample and agrees (023-06, 18.7).


## 4. (b'): Rule A by the time the child last went from clean to dirty

### 4.1 The rule

* r(x): the time at which x stopped being current, set at the end of the
  transaction that replaced it (`Db.endOfTrans`: a split, the unlink, a
  merge's left-out node, root collapse, a new super root). It is set only
  for a node that stays in D.
* e(y): the time y last went from clean to dirty (`makeDirtyIfNeeded`).
  Rule A's refile does not change it. It is cleared when y ends clean.
* After a taken node x is written: x is dirty again iff it points to a
  dirty y, and either x has no r(x) or e(y) < r(x). For a current node this
  is `javaTest`.
* Why it is sound (023-06, 18.7): with e(y) >= r(x), y was clean at
  e(y) - 1. Its version then is good for every t < r(x), and lemma M
  carries that to the newer versions written while y stayed dirty.
* A node with no e known counts as dirty since before any replacement, and
  the test is then `javaTest`.

### 4.2 Stored with the got-dirty entry

With `-Dbergdb.p7.ruleb=true` (an experiment; commit `07b9e954`):

* each got-dirty entry is (id, position, r, e), 32 bytes instead of 16
  (`StoredTrans`'s serializer and parser, `store()`'s count,
  `TransSeq.recordBytes`, `checkDirtyNodes`, `writeAheadTops`);
* a start reads r and e with each entry it keeps (`DbStarter`), and the
  rerun sets r for a node of D that a rerun transaction replaces, as
  `endOfTrans` does;
* r and e are exact at a start. e is fixed while the node stays dirty and
  is stored where it is filed. r is stored if the node was replaced before
  that record; otherwise the replacement is in the section and is rerun.

The format byte stays 6. A database written with the switch cannot be read
without it.

### 4.3 Checks

* RestartInvariance with the switch on, on level2's three configurations
  and two with reclaim, one of them with a restart after every
  transaction: the stream is identical in all five. (b') let replaced nodes
  pass 40 to 643 dirty children, so the rule acted.
* `testDirtyTopNodesWrittenAhead` and the counterexample's 30 seeds pass.
* The unit tests with the switch on fail 4 tests, all expected values:
  * CorruptStreamTester's `testFound019_32`, `testFound021_11` and
    `testFound021_12`, which name byte offsets;
  * `TransSeq.testTakeWithBudget`, which counts 16-byte entries.
* `level2.sh quick` with the switch on (main clone, `07b9e954`; the unit
  step leaves out those 4 tests and Eviction's): steps 1 to 6 OK, the
  RestartInvariance configurations all identical. Step 7: A2A3Check2 OK;
  the trace checker fails C-S in 11 of 14 traces, 118 transactions, all
  "model only" in gd and D: the model's `javaTest` keeps dirty the replaced
  nodes that (b') cleans. C-L, C-R and C-V pass. This is the expected
  difference until the checker has the new test (023-06, 18.4).
* `DbTester.testRecordsWithinLimit` passes with 32-byte entries.


## 5. The gates

### 5.1 On (a)

| Gate                         | On         | Result                                               |
|---|---|---|
| `before-commit.sh`           | `7d59a04a` | 3 unit tests fail, all expected values (below)       |
| `level1.sh` full             | `ca949e5e` | LEVEL 1 OK; Props MEM 129 (at most 131), SS 1.51     |
| `level2.sh quick`            | `ca949e5e` | LEVEL 2 OK; conformance: 14 traces, TRACECHECK OK 14 |
| `level2.sh` full             | `ca949e5e` | LEVEL 2 OK; conformance: 70 traces, TRACECHECK OK 70 |
| `level3.sh` full             | `ca949e5e` | LEVEL 3 OK; 25 traces OK, C-CUT 0 of 305 CUT lines   |
| `level4.sh quick`            | `ca949e5e` | steps 1 to 4 OK; step 5, conformance evict: 14 of 15 |
| StreamDigest quick, 4 modes  | `e2f13dc9` | 11 configurations: the modes give the same stream    |
| CrashTest, 25 rounds         | `e2f13dc9` | 0 failures (also node size 8, sd 500)                |
| RestartInvariance, 5 configs | `e2f13dc9` | stream identical in all (5.2)                        |

* The level scripts ran in a separate clone at `ca949e5e`, where (b') is
  off. Their copies (`java/stress/p7-level*.sh`, not committed) leave out
  the 3 unit tests below.
* before-commit's f-tests (86) and demos passed. Its unit run took 1,625
  tests and failed 3, all of which change for a known reason:
  * `CorruptStreamTester.testFound021_11` and `testFound021_12` name byte
    offsets of the LONG workload's stream. The records now hold more top
    nodes, so the offsets move: new rows are needed (023-06, 11.3, point
    5; Z19).
  * `Eviction.testLoweredBudgetAfterPinsFell` builds a state in which the
    detachable objects lie between a budget, halfway between P1 and P0,
    and P0. With (a), P0, the pins of the hand's last round before the
    pins fall, is 3,622 bytes instead of 3,878, as D holds fewer top nodes.
    P1 (3,016) and the resident bytes before the test's eviction loop
    (6,624 in 16 objects) are the same. The loop evicts until the bytes are
    at most P0; its last object is larger than the gap, so it ends at
    3,016, below the budget of 3,319, and the test's precondition fails.
    The property it tests is untouched; the setup needs new numbers.
* `level2.sh` full, with the coordinator's approval, includes the default
  settings on disk past 50 MB and RestartInvariance at about 100 MB.
* Not run: `level4.sh` full.

### 5.2 RestartInvariance on runs that write ahead

The start's rule is exercised only when a restart's section holds a list
from which a node was written ahead. RestartInvariance now prints both
counts.

| Configuration                          | Written ahead | Ids dropped | Stream    |
|---|---|---|---|
| sd 100, 500 keys                       | 0             | 0           | identical |
| sd 1000, node size 8                   | 0             | 0           | identical |
| sd 10000, node size 14                 | 13            | 0           | identical |
| sd 2000, node 8, reclaim, every 1      | 3             | 9           | identical |
| sd 5000, node 8, reclaim, 50 keys      | 33            | 1           | identical |

The ids are dropped by B's starts, counted for the process. "every 1"
restarts after every one of 1,500 transactions; TRANSSEQ, the lookups and
the node identity agree at every checkpoint. `testDirtyTopNodesWrittenAhead`
restarts every 97 transactions and drops ids too (2.4).

### 5.3 The conformance difference

`level4.sh quick`, step 5, `conformance.sh evict`: trace `e-m-mixed-1`
fails C-S at one transaction of 501. Its check output:

* T(21) gd: Java only [1580]; versions only in Java: [1580];
* the references of node 5884 name 1580's version of T(21), not T(20);
* D: model only (1580, 20), Java only (1580, 21).

Top node 1580 was written ahead in record 21, stayed dirty (its root was
dirty), and moved from list 20 to list 21. This is the expected difference
of the model's step 5 from (a). All other checks of the 15 traces pass:
C-A, C-P (0 of 3,454 transactions), C-H (0 of 3,454), C-L and C-R. Most
pulls end that way (6.5).

The 70 traces of `level2.sh` full and the 25 of `level3.sh` (with reclaim)
all pass: their small trees make few top nodes, and none of their records
wrote ahead, so these runs do not test the model's side of (a). A trace
that writes ahead is needed for that (section 9).


## 6. The measurements

All counts are on F53, shared with other agents' runs. The streams are
deterministic, and each count is from one run. The builds:

* base: P4's code (`-Dbergdb.p7.ahead=false`);
* (a): the default;
* (a)+(b'): `-Dbergdb.p7.ruleb=true`, with r and e stored;
* (b') alone: both switches.

The runs are in `/Users/f/fl/bench/2026-11-10/p7/runs/m2/`.

### 6.1 T1, "after", on P4's branch

Twin / emptied database. "Tops" is the most dirty top nodes at a checkpoint
of the drive's second half. "B/tx" is the stream bytes a drive transaction,
from a third of the drive to its end. "W/made" is the top node versions
written per top node made over the same span.

| N, drive        | Build    | max D     | Objects   | Tops      | B/tx        | W/made       | Checks       |
|---|---|---|---|---|---|---|---|
| 1,000, 4,000    | base     | 79 / 90   | 85 / 102  | 57 / 60   | 1383 / 1396 | 11.0 / 12.0  | C9 fails     |
| 1,000, 4,000    | (a)      | 40 / 49   | 24 / 43   | 13 / 22   | 1294 / 1305 | 7.8 / 8.1    | C9 fails     |
| 1,000, 4,000    | (a)+(b') | 30 / 34   | 20 / 19   | 6 / 13    | 1249 / 1256 | 5.2 / 5.4    | OK           |
| 1,000, 4,000    | (b')     | 57 / 61   | 62 / 69   | 40 / 41   | 1295 / 1297 | 7.1 / 6.8    | OK           |
| 100,000, 4,000  | base     | 79 / 107  | 85 / 99   | 57 / 76   | 1383 / 1426 | 11.0 / 15.2  | C6, window   |
| 100,000, 4,000  | (a)      | 40 / 36   | 24 / 39   | 13 / 17   | 1294 / 1294 | 7.8 / 7.4    | OK           |
| 100,000, 4,000  | (a)+(b') | 30 / 28   | 20 / 31   | 6 / 14    | 1249 / 1264 | 5.2 / 5.7    | OK           |
| 100,000, 4,000  | (b')     | 57 / 71   | 62 / 79   | 40 / 59   | 1295 / 1342 | 7.1 / 11.2   | C9, window   |
| 1M, 12,000      | base     | 94 / 178  | 83 / 184  | 61 / 158  | 1421 / 1800 | 11.4 / 40.4  | all three    |
| 1M, 12,000      | (a)      | 35 / 34   | 25 / 33   | 12 / 5    | 1303 / 1307 | 7.3 / 7.2    | OK           |
| 1M, 12,000      | (a)+(b') | 31 / 29   | 17 / 35   | 6 / 16    | 1273 / 1289 | 5.8 / 6.2    | C9 by 1      |
| 1M, 12,000      | (b')     | 55 / 167  | 63 / 176  | 41 / 151  | 1305 / 1814 | 7.0 / 39.5   | all three    |

* (a) closes the window at every N. (b') alone does not: the window's
  nodes have been dirty since their creation, before their successors'
  replacement, as section 3 predicts.
* (a)+(b') lowers D and the top node writes further, in the twin as well.
  C9 at 1M fails by one object (35 against 17 + 17), because the twin's
  count falls more.
* At N = 1,000, (a) fails C9: 43 against 24 + 14. The emptied database
  keeps 14 unreachable key nodes in D at the end against the twin's 9.
  With (a)+(b') it passes (19 against 20 + 14).
* With (a), no top node is ever kept dirty by a skip target outside its
  record (`still` b = 0 in every run).

### 6.2 T1 "inter", N = 100,000, drive 4,000

"Dold" is D's key nodes that a scan at the latest time does not reach
(left out or replaced), right after the deletes. "Del" is the bytes the
deletes append, user records and reclaim's steps.

| Branch | Build            | D after | Dold | Del, MB | max D (twin / B) | Objects (twin / B) |
|---|---|---|---|---|---|---|
| P4     | base             | 60      | 45   |         | 79 / 23          | 85 / 29            |
| P4     | (a)              | 67      | 53   |         | 40 / 22          | 24 / 25            |
| P4     | (a)+(b')         | 67      | 53   |         | 30 / 23          | 20 / 33            |
| P4     | (b')             | 61      | 47   |         | 57 / 23          | 62 / 25            |
| P5     | base             | 262     | 248  | 11.47   | 79 / 80          | 85 / 83            |
| P5     | (a)              | 273     | 259  | 11.22   | 40 / 34          | 24 / 41            |
| P5     | (a)+(b')         | 163     | 150  | 9.77    | 30 / 28          | 20 / 31            |
| P5     | (b')             | 305     | 291  | 10.58   | 57 / 66          | 62 / 64            |
| P5     | (a)+(b'), memory | 83      | 71   | 8.69    | 32 / 36          | 27 / 31            |
| P5     | (b'), memory     | 141     | 127  | 9.94    | 70 / 58          | 88 / 62            |

The P5 rows are on P5's head `71e386de` with P7's commits cherry-picked
(branch `023-p7-on-p5` in `/Users/f/fl/bench/2026-11-10/p7/p5clone`):
`runs/m2/p5-inter100k-*.txt`, and for the rows marked "memory", with r and
e kept in memory only (16-byte entries), `runs/p5/inter100k-*.txt`.

* **D right after the deletes is one moment of a moving take.** The stored
  form's 32-byte entries change the stream's length, so the take's share
  and dither, and so which lists are taken when. The same rule then leaves
  150 left-out nodes or 71. (b') alone even leaves 291 in the stored form.
* **The bytes are the steadier measure.** The deletes write 15 % fewer
  bytes with (a)+(b') stored (9.77 MB against 11.47), 24 % with r and e in
  memory, where the entries are 16 bytes shorter. The user's delete
  records with r and e in memory: 7.67 MB against 9.47. That is a part of
  P5's 11.3 point 1 ("inter" writes 2.1 times P4's bytes; P4 wrote 5.5 MB
  there), not all of it.
* With (a) alone, P5 fails C9 (41 against 24 + 15): dirty replaced roots
  remain. (b') clears them.
* On P4's branch "inter" has no window and few left-out nodes. (b')
  changes little there.

### 6.3 The long drive on P5's branch (Frans's question for Z21)

T1 "inter", N = 100,000, with 200,000 drive transactions and reclaim
running, on P5's branch (`runs/p5/long-inter-*.txt`). "Stayed" is the
nodes of Dold that were also in Dold at the last checkpoint, 10,000
transactions before.

| At drive      | (a): D | Dold | stayed | rootDirty | (a)+(b'): D | Dold | stayed | rootDirty |
|---|---|---|---|---|---|---|---|---|
| after deletes | 273    | 259  | -      | 10        | 83          | 71   | -      | 8         |
| 10,000        | 20     | 5    | 0      | 6         | 29          | 12   | 0      | 13        |
| 50,000        | 21     | 7    | 0      | 8         | 21          | 7    | 0      | 8         |
| 100,000       | 25     | 8    | 0      | 9         | 29          | 12   | 0      | 13        |
| 130,000       | 36     | 16   | 0      | 17        | 4           | 1    | 0      | 2         |
| 200,000       | 16     | 6    | 0      | 7         | 28          | 12   | 0      | 13        |

* **With (a) alone, the left-out nodes leave D.** All 259 are gone within
  10,000 transactions, and from then on no unreachable key node of D is
  still there at the next checkpoint. D holds 1 to 16 such nodes at each
  of the 20 checkpoints, about the dirty replaced roots of the newest top
  nodes (`rootDirty` one more).
* **(b') makes them leave sooner**, at the deletes (71 against 259, with r
  and e in memory, as this run had them), but not fewer in the steady
  state (1 to 13 against 1 to 16).
* The twin: D 21 to 23 with (a), 16 with (a)+(b'), at every checkpoint.

T4's queue on P5's branch, 200,000 transactions (`runs/p5/long-queue-*`):

| Build    | D, at the 10 checkpoints | Dold     | stayed, the most | Bytes, MB |
|---|---|---|---|---|
| (a)      | 64 to 186                | 34 to 74 | 4 (at 200,000)   | 123.07    |
| (a)+(b') | 75 to 135                | 35 to 66 | 0                | 116.78    |

In the queue, the merges and unlinks at the head leave out 35 to 75 nodes
at any time, and they turn over. (b') writes 5 % fewer bytes.

### 6.4 T4's ordered queue, 100,000 transactions, on P4's branch

| Build    | Stream at 100,000, MB | D at 100,000 | W/made  |
|---|---|---|---|
| base     | 58.56                 | 116          | 116     |
| (a)      | 58.35                 | 144          | 109     |
| (a)+(b') | 57.35                 | 96           | 65      |
| (b')     | 56.96                 | 64           | 56      |

The queue makes few top nodes (32 in 100,000 transactions) but writes each
one about 110 times: they stay dirty through their roots. (b') halves that.
D's count varies a lot between checkpoints; one checkpoint says little.

### 6.5 What the pulls do

A probe (`cd81d789`) counts the top nodes written ahead that stayed dirty.
T1 at N = 1M, drive 12,000, at the end of the drive, counted from the
start:

| Database | Build    | Written ahead | Stayed dirty | Top versions written | Top nodes made |
|---|---|---|---|---|---|
| twin     | (a)      | 5,450         | 4,773        | 6,310                | 857            |
| emptied  | (a)      | 11,992        | 11,435       | 20,667               | 859            |
| twin     | (a)+(b') | 3,956         | 3,367        | 4,813                | 857            |
| emptied  | (a)+(b') | 10,643        | 10,179       | 19,094               | 859            |

* **Most pulled nodes stay dirty**: 88 % in the twin and 95 % in the
  emptied database. A node of the chain below them has a dirty root, a
  replaced root that names the hot segment root of reclaim's internal
  keys (P6, 5.1).
* **Such a pull still dissolves the window.** It does not clean the node,
  but files it in the newest list together with the node that named it.
  The chain then moves as one, and no inversion forms. So the pull is
  worth its write: about one top node version, about 100 bytes, a drive
  transaction, against 2.8 rewrites a transaction before.
* **A cheaper form**, for production: move such a node to the newest list
  without writing it. A start must then also drop an entry of an older
  list whose node is in a later list, which changes INV-1 once more. Not
  built.


## 7. Requirements and tests met

023-02 and 023-03, as P4 gives them, with these changes:

* **023-03's C6 and C9** pass with (a) at N = 100,000 and 1M, against a
  twin whose own D and objects (a) has lowered. At N = 1,000, C9 still
  fails, as on P4 (43 against 38). With (a)+(b') it passes at 1,000 and
  100,000, and fails at 1M by one object.
* **The window does not ratchet**: in the long drives it stays at 2 to 17
  dirty top nodes over 200,000 transactions (6.3), and the unit test bounds
  it at every transaction.
* **R26 (performance)**: fewer bytes in every T1 row; the queue about the
  same (0.4 % fewer). The largest record of the drive's window grows by up
  to 1.9 kB (twin 5,344 bytes against 3,480). Times not measured.
* **R24 (Lean alignment)**: (a) changes the model's step 5 and INV-1 at a
  start; (b') changes its step 7 and the physical theorems' closure
  (023-06, 18.4). Neither is in the model yet.


## 8. Faults and limits found

* **(b) as 023-06's 18.2 stated it is unsound** (section 3), found before
  any code was built on it, and confirmed by a test.
* **No fault found in (a)** by the gates run.
* **Most pulls do not clean.** 88 to 95 % of the pulled top nodes stay
  dirty, because a root below them is dirty (6.5). They still keep the
  chain in one list. The write costs about 100 bytes a drive transaction.
* **(b') in 6.3 and in 6.2's "memory" rows is in memory only.** It
  applies the same rule as the stored form, but its records are 16 bytes
  shorter for each got-dirty entry, so the take's phase differs (6.2).
  The stored form was checked with RestartInvariance and measured in 6.1,
  6.2 and 6.4.
* **Format.** (b') stored makes every got-dirty entry 32 bytes, behind a
  switch; a database written with it cannot be read without it.
* **Test expected values**: 3 unit tests with (a), 4 with (b') stored
  (5.1, 4.3).


## 9. What is left for a production version

* (a): decide how to treat a pull that will stay dirty (6.5): write it as
  now, or move it to the newest list without writing it; remove the
  switch and the probes' counters; new rows for CorruptStreamTester and
  new numbers for the Eviction test (Z19).
* The Lean model: step 5 with the closure, INV-1 with "no version in a
  later record", the trace checker's step; then conformance with the
  write-ahead (`e-m-mixed-1` passes), and a trace set whose records write
  ahead often, such as T1's twin with node size 8.
* (b'): the format without a switch: the 32-byte entry in format 6, or r
  and e only for the entries that have them; the model's step 7 and the
  physical theorems' weaker closure (023-06, 18.4 and 18.7; Z21); the
  level scripts and conformance with it on.
* `level4.sh` full on (a); the level scripts with (b') once the checker
  has its test.
* Docs: levels.md on the take (the write-ahead) and on Rule A for replaced
  nodes; sis-model.md, INV-1 and step 7.


## 10. Questions for Frans

* **Q1. (a) in 2026.4?** It closes the window at every N measured, changes
  no record syntax, and keeps `javaTest`. It needs the model's step 5 and
  INV-1 changed (R24). Recommended: yes.
* **Q2. (b') in 2026.4, with (a)?** It is sound by 023-06, 18.7. With
  P5's merges it lowers the left-out nodes at the deletes (248 to 150, or
  71 in another phase of the take) and cuts the delete bytes by 15 %
  (6.2). Without it, the family still leaves D within 10,000 transactions
  (6.3). It needs 16 more bytes for each got-dirty entry, and
  the physical theorems re-proved (Z21). Recommended: with P5's merges,
  yes; without merges, it can wait for a release that changes the format.
* **Q3. The three tests' expected values** (5.1): approve the new values
  in the format entry (Z19)?


## 11. State

2026-11-10, 14:45. Branch `023-p7-topnodes` in the clone
`/Users/f/fl/bench/2026-11-10/p7/clone`, head `cd81d789`. Its commits on
P4's `0e66d1c9`:

| Commit     | What                                                                      |
|---|---|
| `7eb0ba70` | the probe: CleanupRule's tops, inversions, dprobe and checks; Db's counts |
| `7fd16455` | fix (a): `writeAheadTops`, `TransSeq.takeAhead`, the start's rule         |
| `7d59a04a` | CleanupRule prints the nodes written ahead                                |
| `f7d521e3` | `testDirtyTopNodesWrittenAhead`; the switch `bergdb.p7.ahead`              |
| `ca949e5e` | (b') in memory, `bergdb.p7.ruleb=true`; CleanupRule's Dold                 |
| `92cda0be` | `testRuleBCounterexample`; (b) as written, `bergdb.p7.ruleb=d`             |
| `f787fa3b` | CleanupRule's "stayed"                                                    |
| `e2f13dc9` | RestartInvariance prints the write-ahead counts                           |
| `07b9e954` | (b') stored: r and e in the got-dirty entry; top versions written         |
| `cd81d789` | a probe: the pulled top nodes that stayed dirty                           |

* Branch `023-p7-fix-a` is (a) alone, at `f7d521e3`.
* The P5 clone: `/Users/f/fl/bench/2026-11-10/p7/p5clone`, branch
  `023-p7-on-p5`: P5's `71e386de` with P7's commits up to `07b9e954`.
* The gate clone: `/Users/f/fl/bench/2026-11-10/p7/gate`, at `ca949e5e`,
  with the level scripts' copies `java/stress/p7-level*.sh`.
* Runs: `/Users/f/fl/bench/2026-11-10/p7/runs/` (the matrix in `m2/`, P5's
  runs in `p5/`, the gates in `gate-*.txt`); scripts:
  `/Users/f/fl/bench/2026-11-10/p7/tools/`.
