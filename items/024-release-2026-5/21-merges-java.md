# 024-21. Merges at the delete, in Java

Created 2026-11-11 by Frans Lundberg. Status: done (2026-11-11): on
`main` since `d502af3d`, with 024-22. QJ1 accepted by the coordinator
under Frans's delegation (024-28, section 8); QJ2 not answered; QJ3
decided by rule.

The one algorithm that release 2026.5 ("solid algorithms", 024-04)
still has to put in place: merges of underfull key nodes at the delete
(024-11's MG), in Java, on a branch from `main`, with record format 7.
What to build is 024-11, sections 1, 5 and 7; the source is the
prototype P5 (023-05) with fault 12's fix (023-08), as 024-14's
measuring build has it. Frans approved (2026-11-11) merges alone, BU1 as
the bound, one rerun path and a new record format, and that 2026.5 may
refuse 2026.4's databases; at 11:44 he asked for reasonable assumptions
"for now" on the node size, the thresholds and the dead klongs, to get
the merges done today, one change at a time (section 2). The agent
"mgl" writes the same merge into the Lean tree model (024-22) at the
same time; section 6 is for it.

Names are 024-11's: B the node size, m, h, c the thresholds, V1 to V9,
F1 to F4, M1 to M5, BU1, BU2, CB1 to CB4, TU1 to TU10. Findings here are
MJ1, MJ2, ...; questions QJ1, QJ2, ...


## 1. In short

Written 16:03, final; section 10 is the exact state.

* **Built**, branch `024-21-merges`, head **`54f0a6f5`**, in
  `/Users/f/fl/bench/2026-11-11/mgj/clone` (nothing landed; the
  coordinator lands it with 024-22 from int's combined head
  `024-13-int-m`, after its gates): P5's merge ported to `main` (`Dag`, +660 lines with BU1's
  check); **record format 7**, and a start refuses format 6 with a
  message that names release 2026.4 (tested, and by hand both ways with
  the 2026.4 jar); the thresholds as named constants in one place,
  **8/17/17 at node size 30** (Frans, 14:34; 024-14, QT1; P5's 7/15/15
  before); `dirtyNodeBound` with the merges (024-11's CB2); BU1's checker
  `Dag.checkFill`, called after every transaction by UnlinkFuzz,
  `MergeTester` (new) and `DbTesterMerge` (new: restarts, crash cuts,
  readers with eviction); "no merge" a `Bug` (024-22's J1); the TREE
  line with m, c and h (J2, J9); `main` merged in at `23c6ac5e`; the
  review's fixes R1 to R6 (7.1); the documents.
* **Gates**: all six of the brief (before-commit, unlinkfuzz, level1 to
  level4 full, with conformance small, drain, reclaim and evict) passed
  twice: on `30c393df` with P5's thresholds and on `ed9d8163` with
  8/17/17 (LEVEL 4 OK at 15:38). On the head `54f0a6f5` (`main` merged,
  the review's fixes): BEFORE COMMIT OK at 15:40; level2 to level4 there
  are int's, on the combined head with 024-22. The Lean checker's checks
  pass with merges; 024-22 found the branch equal to its model on 239
  traces (P5's set); traces with 8/17/17 in `mgj/traces-m8/`.
* **Review** (rev21, `21-merges-java/review.md`): land with fixes, no
  defect found in the merge code; R1 to R6 done (7.1).
* **Numbers, with P5's thresholds** (section 8; 100,000, 1M, 10M keys):
  BU1 holds in every run; key nodes 1.29 to 1.90 times the twin's
  (`main`: 2.0 to 21.5; at 10M 024-03's sparse shape 1.43 against
  2026.4's 15.7); a delete's bytes 0.91 to 1.05 times `main`'s; a
  database without deletes wrote `main`'s bytes. With 8/17/17 the put
  path changes at node sizes 30 and 62 (8.2).
* **Fuzz**: 5,186 rounds (3,750 with P5's set, 1,436 with 8/17/17), 0
  failures, 431,278 merges.
* **Changed expected values** (each its own commit, for approval; 5.4):
  DagTester's chains of single children at node size 6 (`8582dbe6`);
  Reclaim's record limit 100 kB to 200 kB (`b0cb3db2`); Eviction's dead
  hand's restarts later (`6c334f4e`); CorruptStreamTester's pinned
  copies (`4ef56d44`, and `5fa27223` for 8/17/17: two of them in
  another seed); DagTester's BoundCase in key order (`54f0a6f5`, R6).
* **Findings**: MJ1, thrash at node size 8 (0.75 new nodes an operation
  against 2026.4's 0.375); MJ2, a delete with a key transformation was
  counted as a put in `checkDirtyNodes` (fixed). Questions: section 9.


## 2. The assumptions "for now"

Each is one named constant, in one place: the section "Format 7's fill
rule" of `Dag` (`java/src/bergdb/dag/Dag.java`), read only through
`Dag.splitAbove`, `Dag.minFill` and `Dag.mergeCap`, so that a later
decision is a change of a few lines and a re-gate.

**The thresholds, decided at 14:34** (Frans; 024-14, QT1): 024-14's set
m8, 8/17/17 at node size 30, in `55add999`; until then, as the brief
said "for now", P5's 7/15/15 (m = B / 4, h = c = B / 2). Other node
sizes as 024-14's build scaled them (QT2 open): 2/4/4 at 8, 3/7/7 at 14
(P5's values), 16/35/35 at 62; `MergeTester.testThresholds` checks V1's
conditions for every node size from 8 to 64. h = 17 changes the put
path at node sizes 30 and 62 (024-14, section 4.3: about 1 % more bytes
a put in a random fill at 10M, 6 to 13 % fewer key nodes);
`dirtyNodeBound`'s room after a replacement is q = max(2, min(B / 2, B
- h, B - c) - 3), 10 at 30 (024-14's count).

| What             | For now                                    | In the code              |
|---|---|---|
| B, the node size | as today: 30 by default, from the meta block | `maxNodeSize`          |
| h, a split's half | 17 at B = 30 (2026.4: 15)                | `SPLIT_ABOVE_30`         |
| m, the least fill | 8 at B = 30                               | `MIN_FILL_30`            |
| c, a merge's cap | 17 at B = 30                               | `MERGE_CAP_30`           |
| other node sizes | v B / 30, m at least 2 (024-14's scaling)  | `THRESHOLDS_NODE_SIZE`   |
| no merges below  | B = 8 (m = 1 there)                        | `MERGE_MIN_NODE_SIZE` 8  |
| Dead klongs      | nothing beyond the merge (024-11, QU3)     | -                        |
| Merged nodes     | P5's way: new nodes, the take-back         | `Dag.merge`              |

* **B below 8** (only `Dag`'s own tests and fuzzers; a database has 8,
  14, 30 or 62): m = 1, so no node is merged and the delete is
  2026.4's. Reason: a space split's halves hold at least h / 2 live
  klongs, fewer than 2 at B = 6 or 7, so V1 with m = 2 cannot hold
  there (024-11, 5.4: "for every B from 8"; 024-22, 2.1, the same).
  `unlinkfuzz.sh`'s configuration at node size 6 so still runs 2026.4's
  delete.
* **Merged nodes, P5's way, with fault 12's fix**: `main` has the fix
  since 2026.4 (`Dag.spaceSplitInPlace` points the segment leaf's klong
  of tt in place); QU6's other way (a node of tt as N1, net entries) is
  for later.
* **Dead klongs**: a merged node holds only live klongs, so a merge
  drops the dead ones of L and R; nothing else removes them (024-18
  studies the options).


## 3. Design note

Written 11:58 to 12:30, before and while the code was ported; it states
what was built.

### 3.1 What is taken from P5 as it is

* The merge: `Dag.merge` (M1 to M5), `mergeParent` (M4), `link`,
  `sibling`, `liveCount`, `klongsOf`; its call after each change a
  delete makes (`mergeAfterDelete`, the fix loop); the walk of the path
  again after a rule O (`descendToDepth`, with `PutData`'s counts
  `fullNodes` and `newRootsMade`); `KeyNode.addSortedKlong`; and the
  sibling rule M1 (the left sibling if both fit in c, else the right
  one, else the left one).
* Root collapse (F1) after the merges, as P5 calls it: 2026.4's
  `collapseRoot`, unchanged.

### 3.2 What the port to `main` changes

* **No switch, no debug print**: merges are the rule of format 7,
  always on for B >= 8. A database is written and rerun by one rule.
* **The thresholds** from section 2's constants, not from P5's private
  formulas; `handleFullNode`'s `maxNodeSize / 2` became `splitAbove`:
  with P5's set the same value, and the put path `main`'s to the byte
  (8.2); with 8/17/17 h is 17 at node size 30, 35 at 62, so the put
  path changes there (8.2).
* **What `main` has that P5 did not**: fault 12's fix, `retarget` in
  `takeBack`, `keyNodeTakenBack` and `Cache3.dropNode` (P4, in 2026.4),
  the X5 (c) `Bug`, K4's count of collapses in `dirtyNodeBound`,
  024-07's `touchPaths`, 024-10's last operation wins. The merge stands
  beside them; none of them changed. The merge calls are in
  `deleteUpward`'s three places that change a node (024-22, MD1, the
  same).
* **`dirtyNodeBound`**: CB2's simple count, not P5's sharper one (3.5).
* **Statistics**: P5's counters stay as counters for the tests and the
  fuzz (`Dag.statMerges` and the rest, one more: `statMergeDescents`),
  written by the writer only.

### 3.3 The record format: 7

* **Format 7 has format 6's layout**; a delete's rule includes the
  merge, so a record of deletes means another tree than in format 6.
  `StoredTrans.RECORD_FORMAT` is 7.
* **A start refuses format 6**, as 2026.4 refuses 5: the parse of the
  record that the last valid meta block names throws a
  `VersioningStreamException`: "Cannot parse stored transaction of
  format version 6; this version of BergDB reads format 7 only. A
  smaller number is a database written by an older version of BergDB,
  which this version cannot open: format 6 was written by release
  2026.4, which opens it (its deletes have no merges; bergdb 024-21),
  format 5 by release 2026.3 and earlier ...". Tested by
  `StoredTrans.testRefusesFormat6`; one rerun path, no rule chosen by a
  record's format.

### 3.4 What a start reruns

The start reruns each record's operations through `Dag.putKv`, in the
stored order, as today (`DbStarter.rerunTransaction`). A delete runs
`deleteUpward` with the merges: the same nodes are underfull, the same
siblings are chosen, the same new nodes are made in the same order, so
they get the same ids (vpos in the order made; a node taken back uses
its id too, as P4's do). A sibling is read through the follower, from
the stream if it is not resident, as the writer read it, and is not
marked. A merge is a function of the delete and the state (V9; the
model's A1). Tested node for node (ids, klongs, pointers) by
`DbTesterMerge.testRestartsRerunTheMerges` (restarts every third
transaction, startup distances 10 B and 10 MB) and
`testCrashCutsRerunTheMerges` (a stream cut at every second record's
end and inside it).

### 3.5 dirtyNodeBound with merges (CB2)

`Dag.dirtyNodeBound` is 2026.4's count with, for each delete:

* **four klongs in every node of its path** (2026.4: two): a merge of a
  child gives a node at most three (a bitmap, the left child's klong,
  a second new node's klong), and a rule O of that child before its
  merge one (a time split's klong, which the merge then points in
  place; 024-22's MF1 is this case), and one for the extra overflow
  below;
* **four nodes for each level of its path and two levels more**: at most
  one merge a level (CB1: the loop climbs only after a merge into one
  node), two new nodes a merge, and two for one extra overflow of a
  merged node (a half and a new root): a merged node holds the klongs of
  two positions of the walk, and floor((a + b) / q) <= floor(a / q) +
  floor(b / q) + 1; the two levels are for new roots that the
  transaction's splits can make above the path;
* **the room of a node on a delete's path at most q**, the room of a
  merged node, which starts with up to c + 1 klongs: q = max(2, min(B /
  2, B - h, B - c) - 3), 10 at node size 30 with 8/17/17 (12 with P5's
  set, 2026.4's B / 2 - 3), also for 2026.4's later overflows, as a time
  split now keeps up to h klongs;
* no sibling that a merge leaves out is made dirty (it gets no entry).

It is an argument checked by tests, not a proof: `DagTester`'s
`testDirtyNodeBoundOfDeletes` (TU8: random histories, transactions of
1,000 deletes at node sizes 8, 14, 30, one of 100,000 at 30) and
`testDirtyNodeBoundSumsCollapsesOverTrees` compare it with the key
nodes the writer makes dirty; both pass. **The cap it gives**: at node
size 30 a path of 5 nodes counts about 30 nodes a delete, so a record's
limit (15/16 of 2^31 - 9 bytes, 544 bytes a node) takes about 120,000
deletes in one transaction; a larger one is refused before it changes
anything by `Db.checkDirtyNodes`, with its message "The transaction is
too large: the index nodes it can make dirty or create, up to N, could
take ... bytes in a record, more than ... (bergdb 005-31). A larger
update must be split into transactions." Frans intends fixed limits far
below it (024-17: 1,000 operations). `Db.checkDirtyNodes`'s cheap test,
which accepts a transaction without the walk, counts 20 nodes a level
for a delete (2026.4: 7; P5: 11), above the walk's count of one delete
with its path's overflows at node size 8.
* **MJ2, a delete with a key transformation counted as a put.** In
  `Db.checkDirtyNodes` a key with a key transformation is counted
  without the walk, by the cheap test's rule; but that line tested only
  for a value transformation, so a plain delete through a key
  transformation counted 3 nodes a level, a put's, in 2026.4 too. Now it
  counts as a delete (`ea721a68`).

### 3.6 Readers and handles

* **A reader on an older version** looks up at a time before tt, so it
  stops at every node's time klong of tt. A merge changes only: P, by
  entries of tt (a bitmap and K klongs after P's time klong of tt), or
  by pointing a K klong of tt in place (behind that time klong); L and
  R, by dropping their entries of tt (`toPreviousState(tt - 1)`, which
  no reader before tt sees); and new nodes, reachable only through
  klongs of tt. So every node and klong that a reader before tt can
  reach is as it was; it reads L and R through P's old klongs. Readers
  take no lock and wait for nothing, as with a split.
* **Handles**: N1's and N2's pointers are copies of L's and R's
  (`addToEnd` with `getPointee`): the same handle objects, as a time
  split's last version shares them, so a child evicted through its
  handle is evicted for both. L and R stay in the node table while a
  reader or a handle names them (unlinked as a split's replaced node;
  CLOCK or the dead hand takes them); a node that the transaction made
  and took back leaves the table at the end of the transaction
  (`Cache3.dropNode`).
* **The test**: `DbTesterMerge.testReadersAcrossMerges`: two reader
  threads scan and get at random earlier times while the writer deletes
  all but every third of 1,500 keys at node size 8, with eviction after
  every transaction (`Schedule.EVERY`); every answer is the model's.
  Level 4's conformance (C-P, C-H, eviction with handles) is in the
  gates.

### 3.7 What reclaim and the cut see

* Reclaim's steps put and never delete, so they merge nothing; its
  touch (024-07) dirties the paths of a step's own puts, which go
  through merged nodes as through any node.
* A node left out by a merge is to the cut what a split's replaced
  node is: reachable only at times before tt, so stored at or after
  the cut iteration's pStart, or dirty (023-06, section 6).
* T-COVER's premise, every index node has a data node below it (the
  checker's CUT-live): with V1 every key node that is not a root holds
  at least m >= 2 live klongs, so it holds at least as well as in
  2026.4; the checker's run is in the gates (level 3, conformance
  reclaim).


## 4. As built

Commits on `024-21-merges`, from `main`'s `2105baa7`:

| Commit     | What                                                          |
|---|---|
| `be6d7f5a` | the merges, format 7, the constants, CB2, `checkFill`, tests  |
| `8582dbe6` | changed test: DagTester's chains at node size 6 (5.4)         |
| `b0cb3db2` | changed test: Reclaim's record limit 200 kB (5.4)             |
| `6c334f4e` | changed test: Eviction's dead hand, restarts later (5.4)      |
| `4ef56d44` | changed test: CorruptStreamTester's moved row (5.4)           |
| `4fc47e1d` | documents: `docs/levels.md`, `docs/sis-model.md`, `next.md`   |
| `ea721a68` | the cheap test's 20 nodes a level; MJ2                        |
| `30c393df` | a merge's impossible states a `Bug` (024-22, J1; QJ3)         |
| `55add999` | the thresholds 8/17/17 (024-14, QT1; section 2)               |
| `5fa27223` | changed tests: CorruptStreamTester's rows for 8/17/17 (5.4)   |
| `d6442486` | documents: the thresholds 8/17/17                             |
| `ed9d8163` | MergeTester.testRuleOBeforeAMerge (024-22, J4, MF1)           |
| `4c8656d5` | merge of `main` (`23c6ac5e`: 024-12's tree model, 024-16)     |
| `9cb8fcd6` | the review's R1 (J2, J9: TREE line m, c, h), R2 to R5         |
| `54f0a6f5` | changed test: DagTester's BoundCase in key order (R6; 5.4)    |

Files (lines added and removed, `git diff --stat 2105baa7`): `Dag.java`
+640 (the constants 50, the merge 330, BU1's check 110, CB2 30, the
calls 10), `MergeTester.java` 364 (new), `DbTesterMerge.java` 296
(new), `StoredTrans.java` +31 (format 7, the message, its test),
`UnlinkFuzz.java` +21 (BU1 after every transaction, the merge counts),
`Db.java` +6 (the cheap test), `PutData.java` +5, `KeyNode.java` +9,
the two `Pack` files, and the four tests of 5.4.

* **`Dag.checkFill(time, gd)`**, BU1's checker: walks every key node
  reachable at the time through the latest live klong of each compare
  value, and checks V1 (every node that is not a root of a segment tree
  holds at least m live klongs), V2 (an inner root at least 2, a leaf
  root at least 1 but the space root), V4 (a segment tree's leaves at
  one depth) and TU2 (key nodes at most S + (n + S - 1) / (m - 1));
  returns the counts and the first violation. Loads nodes through the
  follower, as a reader; an explicit stack (long keys).
* **Called after every transaction** by UnlinkFuzz (every mode and
  `unlinkfuzz.sh`'s configurations), `MergeTester` and `DbTesterMerge`.


## 5. Tests

### 5.1 024-11's TU1 to TU10

| TU   | Where, on the branch                                           | Result |
|---|---|---|
| TU1  | UnlinkFuzz (BU1 after every transaction); MergeTester's TU1 test | pass |
| TU2  | `checkFill`'s count, in every call above                       | pass   |
| TU3  | MergeTester.testSparseAgainstTwin (3,000 keys); 8.1 at 100,000, 1M | pass   |
| TU4  | the same, right after the deletes with no reclaim (R forever)  | pass   |
| TU5  | MergeTester.testThrashAtABoundary (10,000 operations)          | pass, MJ1 |
| TU6  | 8.1: a delete's bytes 0.91 to 1.05 times `main`'s (BU4: 1.2)  | pass   |
| TU7  | UnlinkFuzz's `checkTakenBack` and MergeTester's V8 walk (in memory) | pass |
| TU8  | DagTester.testDirtyNodeBoundOfDeletes (1,000 deletes; 100,000) | pass   |
| TU9  | a cold start at 50 MB after deletes (PF1)                      | not run |
| TU10 | U1 at 10M (8.3): 1.43 times the twin; bytes and scans not run  | part   |

* **MergeTester** (`bergdb.dag`, 6 tests, 3 s): TU1, TU2, TU3, TU4, TU5,
  `testNoChainOfSingleChildren` (a delete of all keys but two of a tree
  of several levels leaves at most 3 key nodes; the next delete
  collapses at most one level), `testThresholds` (P5's set at every
  database node size, and V1's conditions on it). TU1's run reaches
  every case of P5's section 2.4 (merges into one node and into two, of
  leaves and of inner nodes, a left and a right node made by the
  transaction, two klongs of a compare value in the parent, nodes taken
  back, root collapse after a merge) and asserts each.
* **DbTesterMerge** (`bergdb.core`, 3 tests, 0.8 s): restarts and crash
  cuts (3.4), readers with eviction (3.6); BU1 after every transaction.
* **UnlinkFuzz with many seeds** (`mgj/fuzzlong.sh`, one core, pausing
  while a timing run holds the machine; frozen build `b1`): block 1,
  seeds from 1000, 12:52 to 13:30: 1,250 rounds in nine configurations,
  0 failures, 106,593 merges: node sizes 8, 14 and 30; random keys with
  60 to 70 % deletes, 30 to 80 operations a transaction; UnlinkFuzz's
  long keys (1 to 3 segments) shuffled with a second operation on 10 %
  of the keys (key transformations, fault 12's modes); fifo windows;
  random keys shuffled with 20 % twice. BU1, V8, gets and scans at every
  time checked after every transaction. Block 2, seeds from 5000, 13:30
  to 14:07: the same, 1,250 rounds, 0 failures, 106,083 merges. Block 3,
  seeds from 9000, to 14:44: 1,250 rounds, 0 failures, 107,075 merges.
  Blocks 1 to 3 ran P5's thresholds (`b1`); block 4, seeds from 13000,
  runs the head with 8/17/17 (frozen build `b2` of `ed9d8163`), seeds
  from 13000, to 15:22: 1,250 rounds, 0 failures, 106,646 merges. Block
  5, node sizes 30 and 62 only (where 8/17/17 differs from P5's set),
  seeds from 17000, 15:22 to 16:02, stopped at the coordinator's word
  after three of its seven configurations: 186 rounds (100 at 30 with
  70 % deletes, 36 at 62, 50 at 30 with 80 operations a transaction), 0
  failures, 4,881 merges. Beside them `unlinkfuzz.sh` in the gates
  (7).
* **MergeTester.testRuleOBeforeAMerge** (024-22's MF1, its J4): at node
  size 8, twelve keys of the model's case, a delete whose rule O comes
  before a merge in one operation; BU1, gets at every time, V8 and
  `dirtyNodeBound` at least the nodes made dirty after it.
* **StoredTrans.testRefusesFormat6**: 3.3.
* **T11 by hand** (`21-merges-java/T11.java`, Pub API, 300 keys, two
  thirds deleted): a database written by release 2026.4's jar
  (`releases/2026.4/bergdb-2026.4.jar`) is refused by the branch at the
  start with the message of 3.3; one written by the branch is refused by
  2026.4 ("format version 7; this version of BergDB reads format 6 only.
  A larger number is a database written by a newer version of BergDB.");
  each opens its own.
* **A planted fault** (TU7's kind, fault 12's: the merge takes back a
  node of tt without pointing its parent's klongs of tt to N1; worktree
  `mgj/plant`, never on the branch) is caught by every net: UnlinkFuzz
  in all six configurations tried within the first two seeds (B = 8, 14,
  30; random, long keys shuffled with dup, sorted, fifo: "klong N points
  to taken-back node"), MergeTester's V8 walk, DagTester's
  `testNoKlongNamesATakenBackNode`, and all three DbTesterMerge tests
  (the writer's assertion "spos of index node pointer is vpos", as fault
  12 gave).
* **MJ1, thrash at node size 8.** TU5's workload (2,000 keys in key
  order, one key deleted and put in turns, 10,000 one-key
  transactions), new key nodes an operation, the branch against
  `main`'s build of 2026.4's delete: 0.093 against 0.093 at B = 30,
  0.300 against 0.207 at 14, **0.750 against 0.375 at 8**. At 8 a merged
  node of c + 1 = 5 klongs is full after two transactions, and a space
  split's halves hold m = 2, so a split and a merge follow each other
  every few operations: CB4's separation is one key at B = 8. The test
  asserts at most 0.5 at 14 and 30, at most 1.0 at 8. Bytes, not
  correctness; B = 8 is a test size (the Pub API has 30). With 8/17/17
  (`b2`): 0.110 at 30 (2026.4: 0.093), 8 and 14 unchanged.

### 5.2 023-03's tests

023-03's T1 to T4 live in the prototype `CleanupRule` (023-03's
directory and P5's branch), not on `main`: section 8 runs its shapes
with 024-14's probe `THR` on this branch. What the merges change, test
by test:

* **T1, T2** ("sparse", every 30th key kept; the twin's shape): failed
  on `main` (023-03, 8.5: `main` 15.3 times the twin's key nodes here,
  8.1); with merges 1.45 to 1.58 times the twin at 1M, within BU2's 2,
  in every delete order (8.1). T1's strict allowance (the twin's nodes
  plus 10) is not met, as 024-11 expected; the drive was not run.
* **T3** (single scans right after the deletes, R forever): failed on
  `main` (full scans, the head). The shape a scan follows right after
  the deletes, with no reclaim, is 8.1's count (1.29 to 1.90 times the
  twin) and MergeTester.testSparseAgainstTwin's (BU2 asserted); T3's own
  sum of the key nodes each scan follows was not run.
* **T4** (a queue): unchanged by merges in kind (P5: 117 nodes as P4).
* **T6** (lookups against a model): in every test above.
* **T7** (restarts, crashes, readers): DbTesterMerge, level 2 to 4.
* **T11** (format 6 refused, naming 2026.4): 3.3.

### 5.3 P5's own tests, ported

* **UnlinkFuzz `strict=1`** (P5: every node but a root at least B / 4):
  now always on, as BU1's `checkFill` after every transaction, with V2,
  V4 and TU2 too; P5's fuzz matrix (sizes 8 and 14, random, fifo and
  long keys, 40 to 70 % deletes) is in `fuzzlong.sh`'s nine
  configurations, with 30 and with fault 12's modes added.
* **A2A3Check2's batch deletes** (P5's four configurations): `level2.sh`
  has seven draining configurations since 024-09; all pass (7).
* **CleanupRule's shapes** (023-03's prototype): 024-14's `THR` probe
  with BU1's check (8).
* **BoundProbe** (P5's `dirtyNodeBound` against the nodes made dirty):
  DagTester's bound tests (TU8). **LimitProbe** (records under a lowered
  record limit, restarts with the same checksum): not ported; the
  record limit is tested by Reclaim.Tester (5.4) and the restarts by
  DbTesterMerge.

### 5.4 Changed expected values of existing tests

Each its own commit, for Frans's approval:

* **`8582dbe6`, DagTester**: `testDirtyNodeBoundOfDeletes`'s cases (2)
  and (2b) build a chain of single children that root collapse takes
  in one delete, several levels; with merges no such chain forms at
  node sizes 8 and more (V1), so they run at node size 6, which has no
  merges, and (1) and (3) run at 6 too, beside 8, 14 and 30.
  `testDirtyNodeBoundSumsCollapsesOverTrees` at node size 6 with two
  trees, 16 collapses (was three trees at node size 8, 15): three trees
  split a space root of node size 6.
* **`b0cb3db2`, Reclaim.Tester.testLastStepWithinRecordLimit**: the
  record limit 200 kB (was 100 kB): the count of 3.5 gives up to 922
  nodes, 179 kB, for its user transactions of 8 puts and 8 deletes at
  node size 8, which 100 kB refused. The index of 6,000 keys at node
  size 8 is over 1,000 nodes, at 192 bytes each over 200 kB, so the
  test still has the last step that did not fit before 024-07.
* **`6c334f4e`, Eviction.testDeadHand**: the restarts at overwrite 190,
  390, ... (were 120, 270, ...): with merges the first cut came after
  the first restart, which loads only the startup section, so no object
  stored before the cut was resident when the hand ran, and it took
  none (counted: table objects stored before the cut 0 at every
  checkpoint). The test's claims are unchanged.
* **`4ef56d44`, CorruptStreamTester.testFound019_32**: its second row
  (workload take, seed 3552484, a value node's key) found again in the
  stream of format 7: the workload's last record's last value node, at
  27808, offset 596 (was 31880, offset 156; the record is shorter).
* **`54f0a6f5`, DagTester's BoundCase** (the review's R6): a
  transaction's keys in key order, puts and deletes mixed, as Db applies
  them (until then the puts first), so that the tests of
  `dirtyNodeBound` reach a put after a merge into the node that took its
  range; they pass.
* **`5fa27223`, CorruptStreamTester, for 8/17/17** (h = 17 at the
  default node size changes every workload's stream): testFound019_32's
  second row again (27640, offset 708); testFound021_11's three rows in
  LONG's seed 1 (the key node id 4129 in the record at 28856, offset
  1112, its pointer 1 at byte 120, set to the newest top node 30504 and
  to an older one 26224; the top node of the record at 30472, its skip
  pointer 0 set to the key node at 7080); testFound021_12 in seed 20767
  instead of 20766 (the node at offset 72 of the record at 21592, flips
  21698 and 21842; its three refusal texts: "Time not increasing, 430,
  16712100, index=16", key node 16971 at 21664, startup time 480):
  seed 20766's stream has no node before the startup section that the
  start reads; testFoundDescentCycle in seed 20777 instead of 20767,
  the first node of the record at 25584 with its prevPos set to 21344,
  the version of its child before the section, which the xor of 0x80
  did by chance in the old stream (no xor of 0x80 at byte 8 gives the
  cycle in seeds 20767 to 20830). Found by a search probe that first
  found the old rows in the old stream (`21-merges-java/CstFind.java`,
  `NodeMap.java`, `NodePtrs.java`).


## 6. For the model (024-22)

The rule as built, in order, at `30c393df` (the code: `Dag.java`, the
sections "The upward unlink at a delete", "Format 7's fill rule" and
"Merges at the delete"). It is 024-22's section 2.4 step for step;
where they differ, it says so.

**Constants** (`55add999`; 024-14's m8). At node size 30: h = 17 (rule
O: a last version of more klongs, counting its time klong, is space
split), m = 8, c = 17. Another node size B: h = 17 B / 30, m = max(2, 8 B
/ 30) for B >= 8, else 1 (no merges), c = 17 B / 30, by integer
division (8: 4, 2, 4; 14: 7, 3, 7; 62: 35, 16, 35; below 8 h = B / 2).
Until `55add999`: P5's B / 2, max(2, B / 4), B / 2. Java does not carry m and c in a trace:
a writer of format 7 always uses these (024-22, 2.5, proposes `TREE m g
h k mb mm`: my trace branch writes them, section 10).

**A delete of key k at tt** (`Dag.deleteUpward`, leaf Xd at depth d of
the key access path, compare value cv):

1. cv not live in Xd: a noop. Note `fullNodes` and `newRootsMade`.
2. Xd keeps a live klong: `appendDeleteKlong(Xd)` (the bitmap of tt: the
   transaction's own last bitmap in place, else a new D klong with a
   time klong if needed, else rule O on Xd's last version with the
   bitmap). Then **fix** at depth d; if it merged, **RC** on the tree of
   k's last segment.
3. Xd is emptied: 2026.4's climb decides the stop node s first (the
   first node above that keeps a live klong; the X5 (c) `Bug` and the
   inner space root `Bug` as before), then takes back (made by tt) or
   unlinks each node below s. With merges only roots are emptied, so
   the nodes below s are root leaves and s is a segment leaf, or the
   space root (argued; 024-22's runs: `up.climb` only from a segment
   root).
   * s a segment leaf: `appendDeleteKlong(s)` of the emptied root's
     compare value; **fix** at s's depth; if it merged, **RC** on s's
     tree.
   * s inner (not reached with merges, kept as 2026.4's): the bitmap or
     LE-b's `emptyKeyNext`; **fix** at s's depth; **RC** on s's tree.
   * s the space root as the leaf itself: the bitmap, nothing more.

**fix at depth d** (`mergeAfterDelete`): nothing if m < 2. The path is
fresh if no rule O ran since step 1 (`fullNodes` unchanged); d moves
down one for each new root made since step 1. While d > 0: x is the
path's node at d (or, if the path is stale, the node at d of a new
descent at tt along k, `descendToDepth`, marked as any descent); p the
node at d - 1. Stop if p is a segment leaf (x a segment root), or x has
at least m live compare values. Else **merge x**: two new nodes: stop;
one new node: the path is stale, d = d - 1 plus the new roots that the
merge's rule O made, and go on.

**merge x at d** (`merge`), p its parent:

* **M1.** Over p's K klongs not deleted by p's last bitmap: ix, the
  latest of x's compare value cx; ia, the latest of the smallest
  compare value above cx; ib, the latest of the largest below. Neither
  ia nor ib: a `Bug` (a state V1 and V2 exclude; 024-22, MD2 and J1;
  P5 skipped the merge; `30c393df`). Left = child of ib, read quietly
  (`followQuietly`, from the stream if needed, not marked). If ib
  exists and (no ia, or cnt(left) + cnt(x) <= c, each counted up to c +
  1): L = left, R = x. Else L = x, R = the child of ia, read quietly.
  So when ib exists but the two do not fit, the left one was read too.
* **M2.** lvL, lvR: L's and R's last versions at tt (`lastVersion`:
  T(tt), then the live klongs in compare order). n = nL + nR. Either
  empty, or an inner one not starting with the empty key: a `Bug`, as
  above (V1, V3).
* **M3.** two = n > c; k = two ? ceil(n / 2) : n. N1 = T(tt) and the
  first k klongs; N2 = T(tt) and the rest. In an inner pair, R's first
  klong (the empty key) is replaced by R's klong in p (klongR, as it is
  in p). If two, secondKlong = the klong at position k (after that
  replacement), and an inner N2's first klong is the empty key. Every
  klong keeps its pointer and position (the same pointee). Made in the
  order N1, N2 (ids), each reported made and changed; `madeFor(N1, L or
  what L replaced if tt made L)`, `madeFor(N2, R or what R replaced)`.
* **M4** (`mergeParent`). deleteR = no N2, or cv(secondKlong) != cR.
  union = p's last bitmap, with every K klong of cR if deleteR. lInPlace
  = p's last time klong is tt and ib's (L's) klong is after it; rInPlace
  = !deleteR and the same for R's klong. need = (deleteR and p's last
  klong is not a bitmap of tt ? 1 : 0) + (lInPlace ? 0 : 1) + (N2 and
  not rInPlace ? 1 : 0) + (p's last time klong is not tt ? 1 : 0). If
  size + need <= B: the bitmap first (in place if it is the
  transaction's last klong, else `addDeleteKlong`, which adds T(tt) if
  needed), then L's klong to N1 (repointed in place, or a new K klong
  klongL), then if N2: (deleteR ? secondKlong : klongR) to N2 (in place
  if rInPlace, else new). Else rule O: last = p's last version with
  union; in it klongL points to N1; if N2: klongR points to N2 (not
  deleteR) or secondKlong is inserted in order; then `handleFullNode(p,
  last)` with nothing to insert (a time or space split, in place if tt
  made p).
* **M5.** For o in L, R: made by tt: every K klong of tt in p after p's
  last time klong that names o is pointed to N1 (`retarget`; does
  nothing if p was replaced by rule O, whose last version has no klong
  naming o), and o is taken back (`keyNodeTakenBack`: out of D, never
  written, leaves the node table). Else unlinked: its entries of tt
  dropped (`toPreviousState(tt - 1)`), reported replaced.
* Returns 2 if two, else 1.

**RC** (`collapseRoot`, 2026.4's, unchanged): while the segment tree's
root (re-descended, followed quietly) is inner, has one live klong (the
empty key), and is not a fresh node of tt (`made && replacedBy == null`
ends it): a root made by a split of tt is taken back in place
(`takeBackRoot`), else replaced by its child through a new top node or a
klong in the segment leaf above (`replaceRoot`).

**Departures from 024-11, section 5**, all as 024-22's 2.4 and MD1
describe: P5's order (fix after the bitmap at each of
`deleteUpward`'s change points, RC after the loop, F2 as 2026.4's
climb); m = 1 below B = 8. 024-22's J2 (the TREE line with m and c) is
in its own combination of the branches (024-22, J6) and in mine (section
10); J4's unit test of MF1's shape is not written (5.1's TU1 run and the
fuzz reach rule O before a merge).

**Built jar and traces for the model**: the frozen build of
`4ef56d44` is `/Users/f/fl/bench/2026-11-11/mgj/b1/` (`bergdb.jar`,
`stress/`, `HEAD.txt`); traces with the tree exporter: section 10.


## 7. Gates

Each in a slot (`mgj/gate.sh`, one run a hold; logs in
`/Users/f/fl/bench/2026-11-11/mgj/runs/gate-*.txt`). The rows above
"With 8/17/17" ran P5's thresholds (`30c393df` and before). conformance.sh's
drain set runs inside `level2.sh` (10 seeds), reclaim inside `level3.sh`,
evict inside `level4.sh`.

| Gate                  | Commit     | Result                                             |
|---|---|---|
| `before-commit.sh`    | `ea721a68` | BEFORE COMMIT OK (86 s): unit 1,660, F 89, demos 14 |
| `before-commit.sh`    | `30c393df` | BEFORE COMMIT OK (84 s), the head                  |
| `unlinkfuzz.sh`       | `30c393df` | UNLINKFUZZ OK, 3,226 rounds, 338 s                 |
| `level1.sh` full      | `30c393df` | LEVEL 1 OK; MEM 130 (at most 131), SS 1.51         |
| `level2.sh` full      | `30c393df` | LEVEL 2 OK, 13 min (below)                         |
| `level3.sh` full      | `30c393df` | LEVEL 3 OK, 9 min (below)                          |
| `level4.sh` full      | `30c393df` | LEVEL 4 OK, 14 min (below); a first run stopped 13:35 |
| With 8/17/17:         |            |                                                    |
| `before-commit.sh`    | `ed9d8163` | BEFORE COMMIT OK (92 s): unit 1,661, F 89, demos 14 |
| `unlinkfuzz.sh`       | `ed9d8163` | UNLINKFUZZ OK, 3,226 rounds, 299 s                 |
| `level1.sh` full      | `ed9d8163` | LEVEL 1 OK; MEM 130, SS 1.51                       |
| `level2.sh` full      | `ed9d8163` | LEVEL 2 OK: conformance small 70, drain 50 traces  |
| `level3.sh` full      | `ed9d8163` | LEVEL 3 OK: conformance reclaim 30, C-CUT 0 of 318 |
| `level4.sh` full      | `ed9d8163` | LEVEL 4 OK: conformance evict 51, C-P and C-H 0    |
| After the review:     |            |                                                    |
| `before-commit.sh`    | `54f0a6f5` | BEFORE COMMIT OK (89 s): unit 1,664, F 89, demos 14 |

* **level2.sh**: conformance small, 70 traces, TRACECHECK OK 70;
  conformance drain, 50 traces, TRACECHECK OK 50 (the Dag's counters
  over them: 93,340 nodes unlinked, merges' left-out nodes among them;
  2,515 taken back by the climb and root collapse, 2,468 of them roots;
  7,834 collapses; LE-b's relabel 0); A2A3Check2 on the seven draining
  configurations, 33,000 transactions: A2, A3, A5, marking, TREE, A6'
  and A-COPY OK; TakeCheck OK (300 cases). So the trace checker's
  checks (C-A, C-S, the model's step on every transaction, every
  restart invisible) pass with merges; no check failed, so no case of
  the model's rule being narrower than the merge to report.
* **level3.sh**: ReclaimStress 4 x 50 rounds with a cut, 0 failures;
  RestartInvariance with reclaim, four configurations: stream identical,
  same cut; CrashTest, ReclaimReaders (gets and scans at old times
  while reclaim cuts, 0 failures), LoadTest, PowerLoss OK; conformance
  reclaim, 30 traces, TRACECHECK OK 30: C-A, C-S, C-V (live), C-R
  (probes), C-L (411,511 first touches) and C-CUT (318 cuts) 0 failures.
* **level4.sh**: EvictionInvariance, nine configurations, every
  schedule, the audit on: EVICTION INVARIANCE OK; conformance evict, 51
  traces, TRACECHECK OK 51: C-P (550,045 pointers checked) and C-H
  (536,166 handles, 398,685 object histories) 0 of 11,946 transactions
  fail, C-L, C-R, C-V 0; LargerThanMemory on disk OK. So handles and
  eviction across merges agree with the model's invariants.
* **unlinkfuzz.sh**: every configuration ran with BU1 checked after
  every transaction (B >= 8: m = 2, 3, 7; drain-b6 at node size 6 has
  no merges and runs 2026.4's delete).


### 7.1 The review (rev21)

`21-merges-java/review.md`, 14:57 to 15:27: land with fixes, no defect
found in the merge code; restarts (3,004 restarts, node for node), the
bound (about 128,000 transactions in key order), BU1 and the format's
refusal probed clean. Done on `024-21-next`, then `024-21-merges`:

* **R1** (blocks): `main` merged (`4c8656d5`, `main` at `23c6ac5e`, no
  conflict); the TREE line gives m, c and h, `TREE M G H k
  minFill(M) mergeCap(M) splitAbove(M)`, the 8-token form that 024-22's
  checker reads since its `d150bcf6` (J2 and J9); `docs/trace-format.md`
  says so (`9cb8fcd6`). The rest of R1 is the landing's: 024-22 with
  it, and the combined head gated by int (level2's `treeconf` at
  8/17/17).
* **R2**: `docs/levels.md`: a cold start also reads the siblings that the
  rerun's merges read (TU9 not measured), and a sibling is not marked.
* **R3**: the sibling rule's third case (the left one when there is no
  right one) and R's klong pointed to N2 when N2 starts at its compare
  value, in `docs/levels.md`.
* **R4**: UnlinkFuzz's header gives m = 8 at node size 30.
* **R5**: Reclaim.Tester's comment cites the review's probe of the old
  touch (it fails at 200 kB), not the wrong arithmetic.
* **R6**: done (`54f0a6f5`, 5.4). **R7** (the dead hand's restarts after
  the first cut), **R8**, **R9**: notes, not changed.


## 8. Numbers

**All numbers here are with P5's thresholds, 7/15/15** (the branch's
build `b1` of `4ef56d44`, before Frans's decision of 14:34 for 8/17/17);
024-14 has the m8 set's ratios (its section 4.2: worst 1.49, k = 2 1.07).
Counts, no timing. Run 12:58 to 13:02 in one slot (two JVMs, two cores
each): 024-14's probe `THR` with a line of BU1's check (`Dag.checkFill`
by reflection), on `b1` and on `main`'s `2105baa7` (worktree
`mgj/mainwt`); scripts and outputs in `21-merges-java/` (`numbers.sh`,
`summ.py`, `numbers-1m.txt`).

### 8.1 024-11's shapes at 100,000 and 1M keys

Keys `/k/%010d` put in key order, 100 a transaction; then every key but
each k-th deleted, 100 a transaction, ascending, descending or in a
fixed random order (hashed); counted right after the deletes, no drive.
The twin: the kept keys put fresh in key order, 100 a transaction (its
put path is `main`'s). "x" is key nodes over the twin's; `main`'s row
uses the same twin.

| 1M keys     | Key nodes | Twin   | x    | main   | x     | Merges a delete | Rec a delete |
|---|---|---|---|---|---|---|---|
| k2-asc      | 75,000    | 39,498 | 1.90 | 78,997 | 2.00  | 0.012 | 1.00 |
| k2-desc     | 75,000    | 39,498 | 1.90 | 78,997 | 2.00  | 0.012 | 1.00 |
| k2-hashed   | 75,000    | 39,498 | 1.90 | 78,997 | 2.00  | 0.009 | 1.05 |
| k10-asc     | 11,134    | 7,899  | 1.41 | 78,997 | 10.00 | 0.172 | 0.91 |
| k10-desc    | 10,219    | 7,899  | 1.29 | 78,997 | 10.00 | 0.176 | 0.93 |
| k10-hashed  | 11,573    | 7,899  | 1.47 | 78,998 | 10.00 | 0.098 | 1.03 |
| k30-asc     | 3,825     | 2,634  | 1.45 | 40,332 | 15.31 | 0.185 | 0.97 |
| k30-desc    | 4,158     | 2,634  | 1.58 | 40,332 | 15.31 | 0.181 | 1.00 |
| k30-hashed  | 3,859     | 2,634  | 1.47 | 40,332 | 15.31 | 0.102 | 1.03 |
| k100-asc    | 1,202     | 790    | 1.52 | 16,997 | 21.52 | 0.187 | 1.03 |
| k100-desc   | 1,332     | 790    | 1.69 | 16,998 | 21.52 | 0.178 | 1.04 |
| k100-hashed | 1,139     | 790    | 1.44 | 16,998 | 21.52 | 0.103 | 1.04 |

* **BU1 holds in every run** (24 runs and their twins, and after every
  fill): `checkFill` found no key node but a root under m = 7 and no
  violation of V2, V4 or TU2's count (the 1M rows: at most 75,000 key
  nodes against TU2's 83,341 for k = 2). 024-14's probe column `under7 =
  1` is the probe's approximation, not a node under m.
* **BU2 holds in every shape**: at most 1.90 times the twin (k = 2, all
  orders), else 1.29 to 1.69; at 100,000 keys the same within 0.05 (1.42
  to 1.74, k = 2 1.90). `main`: 2.00 to 21.52. These are 024-14's P5
  ratios (its section 4.2) to the row: the port behaves as P5.
* **A delete's bytes** ("Rec a delete": the user's record bytes a delete
  over `main`'s): 0.91 to 1.05 at 1M, 1.00 to 1.04 at 100,000; the
  stream's bytes 0.92 to 1.05. BU4 (at most 1.2) holds. Merges a delete:
  0.009 to 0.187 (CB3's amortized bound has room).
* **A put's bytes are `main`'s**: a random fill of 1M, 231.7 record
  bytes a put on both, 88,990 key nodes on both; 200,000 overwrites
  after it, 317.0 bytes an overwrite on both; at 100,000 the same.

### 8.2 The put path writes `main`'s bytes (StreamDigest)

The branch with its record format set back to 6 (worktree `mgj/f6wt`,
one line, only for this) against `main`'s build:

* **PutDigest** (`21-merges-java/PutDigest.java`, puts and overwrites
  only: node sizes 8, 14, 30, 62; keys in order, at random, overwrites;
  reclaim on and off): **24 of 24 streams identical**, byte for byte.
* **StreamDigest quick** (RestartInvariance's workloads, which delete):
  40 of 44 digests differ, all four modes of l2-every1, l2-idle-2,
  l2-sd100, l2-sd1000-node8, l2-sd10000-node14, l2-sd100000-node62,
  l3-every1, l3-node8, l3-node14 and l3-node62; **l2-idle-1 is
  identical** (`21-merges-java/streamdigest-compare.txt`). In each build
  the four modes (plain, reads, restarts, restarts-once) give the same
  stream for every configuration: the restarts' reruns with merges make
  what the run without restarts made (T8).
* So with format 7 every digest differs from 2026.4's in the format
  byte; with that byte aside, with P5's set, only workloads that delete
  change.
* **With 8/17/17** (`ed9d8163`, format byte set back to 6, 14:45):
  PutDigest 15 of 24 identical: node sizes 8 and 14 (their thresholds
  are P5's) and keys put in key order at 30 (and at 62 without
  reclaim); 9 differ, the random fills and overwrites at 30 and 62, as
  h = 17 (35 at 62) keeps fuller last versions: at 30 the stream 0.9 %
  longer after a random fill without reclaim, 1.5 to 2.5 % shorter with
  reclaim or overwrites. StreamDigest not rerun with 8/17/17.

### 8.3 10M keys

With P5's thresholds (`b1`). Run 14:25 to 14:33 in one slot, two JVMs
(`21-merges-java/numbers10m.sh`), the branch only; `main`'s figures are
024-03's (section 5) and 024-14's.

| 10M keys                           | k2-asc            | k30-rand          |
|---|---|---|
| fill                               | key order         | random            |
| key nodes after the deletes        | 749,946           | 38,522            |
| the twin's                         | 394,949           | 26,874            |
| times the twin (BU2)               | 1.90              | 1.43              |
| `main`, times the twin             | 2.00 (024-14)     | 15.7 (024-03)     |
| BU1 (`checkFill`)                  | holds, 0 underfull | holds, 0 underfull |
| merges a delete                    | 0.012             | 0.166             |
| record bytes a delete              | 83.5              | 66.8              |
| siblings read from the stream      | 0                 | 52,346            |

* **TU10's U1 at 10M**: 024-03's sparse database (a random fill of 10M,
  every 30th key kept) has 38,522 key nodes, 1.43 times its twin, where
  2026.4 had 419,680, 15.7 times (024-03, section 5); BU1 holds; the
  deletes ran with eviction on (the builder's defaults: 52,346 sibling
  reads from the stream, about 3 % of the 1.6M merges' siblings). Bytes
  a transaction afterwards and scans (TU10's other two measures) were
  not run (no drive).
* **k = 2 at 10M** is 024-11's worst shape for m = B / 4: 1.90, as at
  1M (024-14's P5 at 10M: 1.90).


## 9. Questions for Frans

* **QJ1. The changed tests** (5.4): approve the new values? Two of
  CorruptStreamTester's pinned copies moved to other seeds with
  8/17/17 (021-12's from seed 20766 to 20767; the descent cycle from
  20767 to 20777, its xor replaced by the prevPos it gave by chance),
  as their situations no longer arise in the old seeds' streams.
* **QJ2. Thrash at node size 8** (MJ1): 0.75 new nodes an operation
  against 2026.4's 0.375 at a boundary. Accept for a test size, or give
  B = 8 its own thresholds later (one constant)?
* **QJ3. "No merge" is a `Bug` now** (`30c393df`; 024-22, MD2 and J1),
  decided by rule (the model and the code the same): P5 skipped the
  merge in states that V1 to V3 exclude and left the node under m; no
  test or fuzz run reached one. Overturn: three lines back to the skip.
  024-11 5.6's climb inside a tree stays as 2026.4's (024-22, MD3).


## 10. State

2026-11-11, 16:03, by the agent "mgj" of coord-1111. Stopped: the work
of this item is done; the branch is in int's combined landing head
(`024-13-int-m`), which int gates and the coordinator lands.

* **Clone** `/Users/f/fl/bench/2026-11-11/mgj/clone`, branch
  `024-21-merges`, head **`54f0a6f5`** (section 4: 14 commits and a
  merge of `main` at `23c6ac5e`; six commits change tests, 5.4). The
  working tree is clean. BEFORE COMMIT OK on it at 15:40 (reported to
  the coordinator). Its `lean/.lake` is a copy from before the merge of
  `main` (024-12 changed `lean/`): run `lake build` before a level
  script in this clone.
* **Gates**: all six of the brief passed on `30c393df` (P5's set) and on
  `ed9d8163` (8/17/17); on `54f0a6f5` before-commit. The landing's gates
  run on the combined head (`main`, 024-21, 024-22) by int (the
  coordinator, 15:27): before-commit, level1, level2 full with
  `treeconf` at 8/17/17, level3, level4, unlinkfuzz, conformance.
* **No slot held**, no take waiting, nothing running (fuzz block 5
  stopped at 16:02, its 186 rounds clean, 5.1).
* **Frozen builds**: `mgj/b1/` (`4ef56d44`, P5's thresholds), `mgj/b2/`
  (`ed9d8163`, 8/17/17).
* **Other worktrees** of the clone (not for landing): `mgj/next` (branch
  `024-21-next`, the same commit as the head), `mgj/mainwt` (`main` at
  `2105baa7`), `mgj/f6wt` (branch `024-21-f6probe`: `ed9d8163` with the
  format byte set back to 6, for the digests), `mgj/plant` (the planted
  fault), `mgj/trace` (branch `024-21-merges-trace`: `ed9d8163` with
  024-12's `46478dd5`, for the traces in `mgj/traces-m8/`).
* **Not done**: the numbers with 8/17/17 (024-14 has that set's ratios;
  the PutDigest rerun is in 8.2); TU9 (a cold start after deletes) and
  TU10's bytes and scans at 10M; the review's R7 (the dead hand's
  restarts placed after the first cut).
* **Dead klongs** (Frans, 14:27: 024-18's QD1, option 2 with theta 7)
  went to the agent "o2" as item 024-23, from the combined head.

2026-11-13. Status set after the release (coord-1113).
