# 023-05 P5. Merges of underfull nodes at the delete

Created 2026-11-10 by Frans Lundberg. Status: open.

Prototype P5 of 023 (023-05): merges of underfull nodes at the delete
(023-04, 2.4, MG; 023-06, 3.3 and 5.2), towards the strict allowance, on
top of prototype P4 (the upward unlink with LE-b, the empty key first, root
collapse and X5 (a)). Frans's plan of 2012: "Merges are made when the
current version of a node shrinks because of a delete"; the multiversion
B-tree's weak version condition. The code is on the branch `023-p5-merge`
of the clone `/Users/f/fl/bench/2026-11-10/p5/clone`, on P4's head
`5466e153` and P4's `0e66d1c9` (section 9 has the head).

In short:

* It works. With merges, no node but a root holds fewer than B / 4 live
  klongs after any transaction: UnlinkFuzz's new strict check passes at
  node sizes 8 and 14, under heavy deletes, with scans and gets at every
  time against a model.
* T2's "sparse" (every 30th key kept) is where MG is needed: at N =
  100,000, 390 key nodes reachable against the twin's 270, P4's 4,036 and
  `main`'s 7,902; the kept stream 9.0 MB against the twin's 8.3, P4's 27.7
  and `main`'s 35.0. At N = 1,000, 10 nodes, the twin's. Every other T1 row
  ends at the twin's 6 nodes, "inter" too (P4: 14).
* The deletes write about what P4's write: 0.94 to 1.07 times in most
  rows, 0.86 in "sparse", but 2.1 in T1's "inter", where the deletes meet
  reclaim's internal keys in the space root's tree: left-out versions of
  the leaf at the front of the deletes name a node that reclaim makes dirty
  in most transactions, so Rule A keeps them dirty and they are written
  again and again (section 6; with R forever 1.03). One sibling is read per
  merge, about one merge per 5 deletes in key order; under eviction 2 % of
  them from the stream.
* With `noEvict()`, up to 32 % more objects stay resident after the
  deletes than with P4: the nodes left out by merges, until eviction.
* Gates (section 3): `before-commit.sh` and the four level scripts in
  full pass (the trace checker on 70 traces, 25 with reclaim, 45 with
  eviction); A2A3Check2 on 7 configurations. `IndexJobsHarness` flaked
  twice under load (races of its checks, not P5's).
* 023-06's second pass set three conditions, all met: the level scripts in
  full (levels 1 to 3 at `789b1654`, level1 and level4 at the bound's
  commits, `before-commit.sh` at the head), the "inter" bytes (explained
  above), and `dirtyNodeBound` by the transaction, which P1's count made
  refuse more than about 150,000 deletes at node size 30 (now about 2
  million; an argument and a probe, not a proof; section 6).


## 1. Design note

023-06, section 5 asks for it before the code. B is the node size
(`maxNodeSize`, klongs); "live" counts a node's live compare values at the
transaction time tt (the latest klong of each, not deleted).

### 1.1 The rule

* **When.** In the deleting transaction, for each delete, by the writer,
  after the delete has changed its node: the leaf, or with the upward
  unlink (UP) the first node above that keeps a live klong (`stop`).
* **What.** That node X, if it is not the root of its segment tree and
  holds fewer than m = B / 4 live klongs (at least 2), is merged with a
  sibling S under the same parent P: the child of the previous live klong
  of P if the two fit in one node (B / 2), else the next one's, else the
  previous one's. (The note first said the next one, then the previous;
  the left one first fills the nodes that a run of deletes in key order
  leaves behind, section 4.1.) L and R are the left and right
  of the two, cL and cR their compare values in P.
* **The new nodes.** The live klongs of L's and R's last versions at tt,
  in order (all of L's are below cR, all of R's at or above it), make one
  new node if they are at most B / 2, else two new nodes of half each (a
  redistribution). Each starts with a time klong of tt, as a time split's
  last version does. Inner nodes: R's empty key becomes cR's klong in the
  merged node (its bound in P), and a second new node starts with the
  empty key, as a space split's second half does (LE-b: the empty key stays
  the first klong of every inner node). Leaves need no relabel.
* **The parent.** P's klong of L points to the first new node (a new klong
  of cL at tt that shadows the old one, or the same klong changed in place
  if it is of tt, behind P's time klong of tt); R's compare value is
  deleted by a bitmap of tt that sets the bits of every klong of cR,
  before any new klong; a second new node gets a klong of its first
  compare value (or R's klong, pointed to it, if that is cR). A full P is
  replaced by its last version with these pointers set, through
  `handleFullNode` with no klong to insert, so that a space split puts each
  klong in its own half.
* **The old nodes.** L and R get no entry of tt: one that existed before
  is unlinked (`toPreviousState(tt - 1)`, reported replaced, as a split's
  node), so it is written still if it was dirty from an earlier
  transaction: lookups before tt read it through P's old klongs. One that
  the transaction made is taken back: every klong of tt in P that names
  it (the live one, and deleted ones) is pointed to the new node first,
  and it leaves D, the record and the node table (P4's `keyNodeTakenBack`).
* **The climb.** A merge into one node takes a live klong from P; P is
  then checked in the same way, and so on up to the segment root. Then
  root collapse (RC) as in P4: a root left with one live child gives way
  to it. A redistribution leaves P's count as it was and ends the climb.
* **Separated thresholds.** A merged node holds at most B / 2, so it takes
  about B / 2 more klongs (B / 4 single-key transactions) before it is full
  and split again, and a split's halves hold at least B / 4 = m (a space
  split comes when the last version holds more than B / 2), so no split
  makes a node that a merge takes at once. A redistribution's halves hold
  more than B / 4. So alternating puts and deletes at a boundary copy the
  same pair at most once per about B / 4 operations.

### 1.2 The cases 023-06 lists

* **A sibling made by this transaction** (a split's half, a merge's node):
  taken back as above; its klong of tt in P is changed in place. The new
  nodes are recorded (`PutData.madeFor`) as replacing the old left and
  right node (for a node of the transaction: the node it replaced), so
  that a merged node emptied later in the same transaction is taken back
  by P4's `takeBack` like a split's node.
* **A sibling that is dirty but not yet written**: unlinked like any old
  node; it stays in D and is written once, with its state before tt, as a
  node a split replaces.
* **A sibling not in memory**: read by the writer through its follower,
  as a put reads its path (from the stream, under eviction too), but not
  marked (`followQuietly`): the model marks only nodes with a change below
  them (P1's fault 2), and a left-out sibling ends with no entry of tt.
* **The leftmost child with LE-b**: X under the empty key merges with its
  right sibling; the merged node takes the empty key's place in P. X the
  last child merges with its left sibling. The empty key is never deleted
  in P: only R's compare value is, and R is never the leftmost.
* **Inner nodes and segment leaves**: the same rule; the second segment
  leaf of a merge may hold klongs to segment roots, which are copied like
  value pointers.
* **The climb and roots**: a segment root is never merged (no sibling in
  its tree); RC collapses a root with one child after the merges.
* **The Lean assumptions.** A2: every change is an entry of tt, in place
  only behind tt's time klong. A3: no node that the transaction made is
  left unreachable; taken-back nodes are named by no klong, deleted or not,
  and are not in the record. TREE: the new nodes have one current parent,
  P, by one live klong each. A6': a deleted klong of tt that names a new
  node lies in P, from which the node is reachable by a live klong. A-COPY:
  the new nodes' pointers are copied from L and R while both are current,
  before they are left out.
* **`Dag.dirtyNodeBound`**: a merge makes up to two new nodes and adds
  three klongs to the parent; the siblings it leaves out are not made
  dirty. As built: counted for the transaction, not for each delete (2.3,
  section 6).
* **The startup rerun**: a merge is a function of the delete and the state
  at tt - 1 and earlier deletes of tt (A1), with new node ids in creation
  order, so the rerun of the record makes the same merges and the same
  nodes; it reads the sibling as the writer did.


## 2. The mechanism as built

Code places are on the branch's head (section 9), in `java/src/bergdb/`.

### 2.1 Where it runs

* `Dag.deleteUpward` (dag/Dag.java:1083) calls `Dag.mergeAfterDelete`
  (1625) after each change a delete makes: the leaf's bitmap (1095), the
  bitmap of a leaf the climb keeps for A3 (1143), the segment klong deleted
  in a segment leaf above (1181), and the change at an inner `stop` (1197,
  before root collapse). Root collapse (`collapseRoot`) follows a merge in
  the first three cases too, as it did in the fourth.
* `mergeAfterDelete` takes the node at the depth that took the change. The
  key access path is used as it is if no full node was handled since the
  change began; else the path is walked again from the space root along
  the key (`descendToDepth`, 1659, marking as any descent does: every node
  on it is an ancestor of the change). Each new root that a space split
  made since then moves the depth one down (`PutData.newRootsMade`; splits
  go up the key's path only). It stops at a segment root, at a node with
  at least m live klongs, at a node without a sibling, or after a
  redistribution; after a merge into one node it goes on with the parent.
* `PutData.fullNodes` and `newRootsMade` (dag/PutData.java:33): Dag's own
  counts, set in `handleFullNode` and at the new roots of the space splits;
  the split listener's counts are not set in every PutData.

### 2.2 The merge

* `Dag.merge` (1693): the parent's live klongs next below and above the
  node's; the sibling by `Dag.sibling` (1842), which follows the pointer
  through the writer's follower with `followQuietly` (no mark, not on the
  path) and counts the reads, and those from the stream; L and R; their
  last versions (`KeyNode.lastVersion(tt)`); the new nodes built with
  `KeyNode.addToEnd`, R's empty key replaced by its klong in P for inner
  nodes, the second node's first klong by the empty key; `keyNodeCreated`,
  `PutData.madeFor` (the new node replaces the left node's old node, or
  what a node of the transaction replaced), `reportNewPointers`.
* `Dag.mergeParent` (1863): the parent's change as in 1.1, the bitmap
  first, a klong of tt in place (`link`, 1929); a full parent through
  `lastVersionGivenDel`, `replaceKlong` and `KeyNode.addSortedKlong`
  (dag/KeyNode.java:963), then `handleFullNode` with no klong to insert.
* L and R: `unlink` if they existed before tt; else `retarget` (1945), every
  klong of tt in P that names the node pointed to the first new node, and
  `keyNodeTakenBack` (P4's, from P2: out of D, the record and the node
  table).
* `Dag.takeBack` (1446, P4's) now retargets too: it pointed only the live
  klong of tt to the node it replaced; a deleted klong of tt can name the
  taken-back node as well (a merge's right node, or, already in P4, the
  next child's own klong after `emptyKeyNext` pointed the empty key to it),
  and a written node would then name a node that is never written.
  UnlinkFuzz checks this now (2.4); no run of P4's had reached it.
* `liveCount` (1977): distinct live compare values, counted up to a limit.
* `MERGES` (1596): `-Dbergdb.p5.merge=false` turns merges off, for the
  measurements against P4 (section 4).

### 2.3 Other changes

* `Dag.dirtyNodeBound` (477) and `Dag.mergeBound` (578): a delete adds 2 klongs
  to every node of its path, as P4; P1's off-path count for each delete
  (4 nodes a level and 2) is gone; the merges are counted for the
  transaction (section 6). `Db.checkDirtyNodes`'s cheap test: 11 nodes a
  level a segment for a delete (core/Db.java:2725; P4: 7), which only
  decides whether the walk runs.
* `CorruptStreamTester.testFound019_32` names records and node offsets of
  streams of format 5; merges change those workloads' streams, so a row
  whose node is not there is skipped and printed (section 6).
* `stress/UnlinkFuzz.java`: `strict=1` fails when a reachable node but a
  root holds fewer than B / 4 live klongs; every run checks that no
  pointer of a node reachable at any time, deleted and shadowed klongs too,
  names a node taken back; counts of the cases (2.4).
* `stress/CleanupRule.java`: `keep=K` (023-03's "sparse"; its twin holds
  the kept keys, put fresh in the same order and transaction sizes), the
  bytes appended in the fill, the deletes and the drive, and the Dag's
  counts a phase (read by reflection, so the same file builds on `main`).
* Static counters in `Dag` (`statMerges` and others), and a debug print
  (`-Dbergdb.p5.debug=true`); not for production.

### 2.4 The cases 023-06 names, as tested

UnlinkFuzz at node sizes 8 and 14, strict, five configurations each
(random keys with 40, 50 and 70 % deletes and 6 or 30 operations a
transaction, a FIFO, keys of 1 to 3 segments), 8 to 30 seeds each, gets and
scans at every time after every transaction; no failure, and no reachable
node but a root below B / 4 (`runs/fuzz-head3.txt`). In each configuration:

* a node made by the transaction merged, as the left node: 52 to 571
  times at size 8, 10 to 291 at 14; as the right one: 51 to 324, 8 to 280;
* two klongs of one compare value in the parent of a merge: 168 to 790,
  56 to 361;
* a root made by a split of the transaction and collapsed in it (P4's
  take-back of a root): 5 to 86, 1 to 80;
* a split's half emptied in the same transaction: with merges a node is
  merged before it empties, so the climb took back only roots but once
  (keys of 1 to 3 segments, size 8); such a half is merged as a node made
  by the transaction instead (the first case);
* merges into one node and redistributions, of leaves and inner nodes.


## 3. The gates

| Gate, commit                           | Result                                               |
|---|---|
| UnlinkFuzz strict, `5dfee887`          | 0 failures, 0 underfull nodes: sizes 8, 14, 5 configs |
| A2A3Check2, 7 configs, `789b1654`      | A2, A3, A5, marking, TREE, A6', A-COPY: 0 failures   |
| `before-commit.sh`, `4c6bea65`         | FAILED: `testFound019_32`, a row's node moved (6)    |
| `before-commit.sh`, `5dfee887`         | FAILED: `IndexJobsHarness`, a race of its check      |
| `before-commit.sh`, `789b1654`         | FAILED: `IndexJobsHarness`, another race (below)     |
| `before-commit.sh`, `789b1654`, again  | BEFORE COMMIT OK (312 s), a clean worktree           |
| `level1.sh`, full, `789b1654`          | LEVEL 1 OK; MEM 129 (at most 131), SS 1.51           |
| `level2.sh`, full, `789b1654`          | LEVEL 2 OK, 12 min; conformance 70 traces TRACECHECK OK |
| `level3.sh`, full, `789b1654`          | LEVEL 3 OK; conformance with reclaim 25 traces OK    |
| `before-commit.sh`, `429b56d3`         | BEFORE COMMIT OK (264 s)                             |
| `level1.sh`, full, `429b56d3`          | LEVEL 1 OK; MEM 130 (at most 131), SS 1.51           |
| `level4.sh`, full, `71e386de`          | LEVEL 4 OK, 15 min; conformance with eviction 45 OK  |
| `before-commit.sh`, `71e386de`         | BEFORE COMMIT OK (307 s), a clean worktree           |

`429b56d3` and `71e386de` change only `Dag.dirtyNodeBound`, which decides
whether a transaction is refused before it changes anything, and lower it
for deletes; levels 2 and 3 were not run again on them, `before-commit.sh`,
level1 and level4 were.

level2's conformance step: every one of the 70 traces of conformance.sh's
small set, 10 seeds, is a step of the model that meets its assumptions,
and every restart is invisible; level3's: 25 traces with reclaim, 303 cuts,
`CutOK` for every one; level4's: 45 traces with eviction, C-P and C-H in
none of 10,356 transactions (the taken-back nodes leave the node table),
and LargerThanMemory with 2,000,000 keys.

A2A3Check2's configurations: level2's three, and four of batch deletes
(40 and 60 operations a transaction with 50 to 70 % deletes, node sizes 8
and 14; 10 operations with 70 % deletes and keys of two segments), 2,000 to
3,000 transactions each (`runs/a2a3-head4.txt`).

`IndexJobsHarness.testEveryPointAndFault` failed once in `before-commit.sh`
at `5dfee887` on a loaded machine: after a restart, the index manager's
definition in memory was "building" and a read of the stream right after
it "active". The check reads memory first and the stream second while the
resumed build runs; a build that activates the index between the two reads
gives this finding, so it is a race of the check, not a wrong lookup (the
later read has the newer state). At `789b1654` another test of the same
harness failed once, `testRetriedFaultThenDeletedDuringBuild`: "creation 1
returned, and memory has no definition", where the harness's own thread
deletes the index at build step 3 in the background, and the check reads
the definition after the creation returns, so a deletion that comes first
gives the finding. Both ran in `before-commit.sh` beside the f-tests and
the demos, with my measurements and other agents' runs on F53. The same
code passed the first test 35 times in a row alone (33 with merges, 2
without; `runs/ijh-*`), the whole harness 20 times with merges and 20
without, and the whole unit suite once (`wt-build`).


## 4. Measurements

All counts, from CleanupRule (023-03's prototype with the changes of 2.3)
on frozen builds: `main` (`1901394c` and 023-03's tests), "P4" (this
branch with `-Dbergdb.p5.merge=false`: P4's code with the retarget, which
changes no count here), and P5. Runs and output:
`/Users/f/fl/bench/2026-11-10/p5/runs/` (`main-*`, `off-*`, and `h2-*` and
`h4-*` for P5, the head's merge rule; the scripts in `../scripts/`). M4 is
"reach", the key nodes reachable at the latest time; M1 the most kept in
the window; M11 the objects after a start and a probe. The fill writes the
same bytes in all three.

### 4.1 T1, "sparse" (every 30th key kept)

| Measure, N = 100,000    | Twin  | Main    | P4     | P5    |
|---|---|---|---|---|
| M4, reachable           | 270   | 7,902   | 4,036  | 390   |
| M5, dead klongs         | 558   | 101,046 | 49,617 | 3,193 |
| M1, MB, most in window  | 8.31  | 34.97   | 27.74  | 9.01  |
| M8, D, most in window   | 217   | 145     | 232    | 258   |
| M11, after the probe    | 391   | 7,945   | 4,127  | 516   |
| Deletes, MB             | -     | 10.16   | 8.28   | 7.15  |
| Drive, MB               | 14.11 | 6.63    | 9.28   | 13.27 |

At N = 1,000: M4 10 (twin 10, `main` 85, P4 47), M11 92 (twin 103). At
N = 1,000,000, with a drive of 12,000 (P1's, 3.1): M4 3,824 against the
twin's 2,639 (1.45 times), kept at the end 35.6 MB against 30.6, the
deletes 81 MB (P5 only). The drive writes the twin's bytes: reclaim's
iterations rewrite the kept keys' values, as the twin's do; P4's and
`main`'s iterations are still held by the deleted keys (023-06, section
2), so they write less.

With the right sibling first (the design note's first rule, `4c6bea65`),
"sparse" at 100,000 reached 531 nodes: a run of deletes in key order left
nodes of about m live klongs behind it. The left sibling first, when the
two fit in one node, fills them to about B / 2: 390, 1.44 times the twin's,
whose leaves hold about B / 2 too. The strict allowance (a_n = 10) holds
at 1,000, not at 100,000 (section 6).

### 4.2 T1, the other rows, N = 100,000

| Row (long: 10,000)  | M4 P4 | M4 P5 | Deletes, MB: main | P4     | P5     |
|---|---|---|---|---|---|
| after, ascending    | 6     | 6     | 10.94             | 6.16   | 6.37   |
| after, descending   | 6     | 6     | 11.04             | 6.70   | 7.17   |
| after, random       | 6     | 6     | 94.68             | 91.37  | 86.45  |
| inter               | 14    | 6     | 9.35              | 5.49   | 11.47  |
| hashed, random      | 6     | 6     | 132.85            | 109.88 | 104.84 |
| long                | 6     | 6     | 6.39              | 1.00   | 1.03   |

Twin and P5 in every row: M4 6, a get of 1 node, a head of 6; P5's M1
2.11 to 2.20 MB (twin 2.13), M11 83 to 121 (twin 85). `main`'s M4 is 7,901
to 112,765. At N = 1,000,000 ("after", a drive of 12,000): M4 6, kept at
the end 2.89 MB against the twin's 1.88, M8 186 against 94 and M11 177
against 83 (P1's C6 and C9 at 1M, its 5); the deletes 70 MB.

### 4.3 T3, R forever, right after the deletes

| Shape, N = 100,000 | M4 main | P4    | P5  | Deletes, MB: main | P4    | P5    |
|---|---|---|---|---|---|---|
| after              | 7,897   | 1     | 1   | 6.78              | 4.82  | 5.11  |
| sparse             | 7,897   | 4,031 | 385 | 6.65              | 5.64  | 5.23  |
| inter              | -       | 1     | 1   | -                 | 4.11  | 4.25  |
| hashed, random     | 112,759 | 1     | 1   | 108.96            | 96.57 | 93.33 |

"Sparse"'s twin: 263 nodes. The single scan of the first user key follows
1 node in every row, as the twin's.

### 4.4 T4, the queue

| Keys, transactions | M4 main | P4    | P5    | Head P4, P5 | Kept, MB: P4 | P5   |
|---|---|---|---|---|---|---|
| ordered, 100,000   | 11,147  | 117   | 117   | 4, 4        | 1.48         | 1.39 |
| ordered, 1,000,000 | 111,434 | 117   | 117   | 4, 4        | 1.49         | 1.73 |
| hashed, 100,000    | 112,782 | 2,134 | 2,128 | 5, 5        | 3.54         | 3.33 |

`main`'s at 1M from P1's report (3.4); "kept" at the last checkpoint
(`main` 53.2 MB at 100,000). The stream appended: ordered 1M, P5 625 MB
against P4's 596 (1.05 times); ordered 100,000, 60.7 against 58.6;
hashed, 163.4 against 162.9. The largest record at 1M: 29.7 kB (P4
32.4). P5 merges 19,980 times in 1M ordered transactions (one in 50, half
of them redistributions), and reads as many siblings.

### 4.5 Cache and sibling reads

* Resident objects right after the deletes, `noEvict()`: P5 against P4,
  1.27 ("after"), 1.30 ("sparse"), 1.32 ("after", random), 1.03
  ("hashed"), 1.005 ("long"). The nodes that merges leave out stay in the
  cache until eviction takes them, as a split's replaced nodes do; the
  taken-back ones leave the node table at once.
* With eviction (`evict=3000000`, "sparse", 100,000): 586 of 28,642
  sibling reads came from the stream (2 %); 1,126 objects resident after
  the deletes (P4 1,295).
* Siblings read: one a merge into the right sibling, up to two when the
  left one is read and does not fit (28,642 reads for 17,941 merges in
  "sparse"; 22,088 for 22,088 in "after", where the left is never read:
  the run of deletes leaves no left sibling under the parent).


## 5. Requirements and tests met

023-02:

* R1, R16 (lookups, readers): by design (entries of tt only, in place only
  behind tt's time klong) and by every check run: UnlinkFuzz (gets and
  scans both ways at every time), CleanupRule's checks at the latest time
  and within R, and the gates (section 3).
* R3, R5 (the reachable index): as P4, and in sparse ranges too: every
  reachable node but a root holds at least B / 4 live klongs after every
  transaction (the fuzz's strict check).
* R9 (scans): single scans follow the twin's nodes (T3, T4's head).
* R11 (puts and deletes): a merge makes at most two new nodes and reads
  one or two siblings a level; about one merge in 5 deletes in key order.
* R12 (b), underfill: yes, strict, by m = B / 4.
* R14 (memory): the start's objects near the twin's (4.1, 4.2); right
  after the deletes, up to 32 % more resident objects than P4 (4.5).
* R17, R18 (determinism, restarts): the merges are a function of the
  delete and the state at tt (A1); section 3's restart tests.
* R22, R23: format 6, as P4.
* R24 (Lean): no change of the model (023-06, section 6); the trace
  checker in section 3.

023-03: T1 at the twin's shape in every row at 1,000 and 100,000 but
"sparse" at 100,000 (1.44 times the twin's nodes; strict misses there,
the bounded allowance too: a_n of 10 + 4 h_fill = 34 nodes); T3's single
scans pass; T4 steady to 1M. T5 to T12 not run beyond the gates.


## 6. Faults and limits found

* **A fault of the take-back, P4's, found by thinking it through and now
  checked by UnlinkFuzz**: `takeBack` pointed only the live klong to the
  node it replaced. A deleted klong of tt that names a taken-back node (in
  P4, the next child's own klong after `emptyKeyNext` pointed the empty key
  to a child made by the transaction, if that child then empties in the
  same transaction) would keep a pointer to a node never written. Fixed for
  P5 (2.2); P4 should take the same change.
* **A first-version fault, found by the strict fuzz**: the climb gave up
  when a space split happened during the delete, and an underfull node made
  by a time split stayed. Now the depth follows the new roots (2.1).
* **"Sparse" at 100,000: 390 nodes against the twin's 270.** Nodes hold m
  to B / 2 live klongs; a twin put in key order holds about B / 2. Strict
  (a_n = 10) needs a denser rule (023-06, 5.3: the honest target is a
  constant factor). An experiment, not committed (`runs/exp-cap.diff`): a
  merged node of up to 3 B / 4 live klongs instead of B / 2 gives 324 nodes
  (1.20 times the twin's) with 7,834 merges instead of 17,941 and the same
  bytes in the deletes (7.42 MB against 7.15); "after" too, with 7,894
  merges instead of 22,088 and 6.33 MB against 6.37. Up to 2 B / 3 gives
  416, worse than B / 2's 390: the shape depends on the run of deletes. The
  price is the smaller gap before the next split, B / 4 klongs instead of
  B / 2, so more thrash at a boundary; not measured.
* **T1's "inter" writes 2.1 times P4's bytes in its deletes** (11.5 MB
  against 5.5): the user's delete records 9.5 MB against 4.8, reclaim's
  steps 2.0 against 0.7. With R forever (T3) 1.03 times; "after", whose
  keys have a segment tree of their own, 1.03 times. **Explained** (probes
  on copies of the head, `runs/exp-*.diff`): D right after the deletes
  holds 248 left-out key nodes (111 leaves, 137 inner; P4 45, "after" 56).
  106 pointers of the left-out leaves name one reachable dirty node, a
  segment root, which in this run can only be the root of the segment tree
  of reclaim's internal keys ("/#i/...": the user's keys and "/a.txt" have
  one segment); the left-out inner nodes name the left-out leaves (326
  pointers) and each other (146). In "inter" the deleted keys start right
  after "/#i/" in the space root's tree, so the leaf at the front of the
  deletes holds the klong of that segment tree, which reclaim's steps make
  dirty in most transactions. Each merge of that leaf leaves out a version
  of it that is dirty (reclaim's step marked it) and names that segment
  root;
  Rule A (a written node stays dirty while a pointer of it names a dirty
  object) then keeps it, and the left-out inner nodes above it, dirty, and
  they are written again and again. Not more nodes left out than in
  "after" (3,250 dirty left-out nodes in both), but these stay. The same
  family as P1's old root leaves and the top nodes in D (P1, 5; P4, 5;
  023-06, 2), here made often by merges at the hot leaf. A left-out node
  that was dirty before the transaction cannot leave D at once: lookups
  between its last change and tt need its state, which is not written yet;
  one that got dirty in the transaction only already leaves D (unlink,
  `keyNodeReplaced`, as P1 to P4). Remedies, for phase 2 with Rule A's
  question (P6): a left-out node's stream version needs no live pointer to
  the hot node's newest version, or merges avoid a node that names a
  segment root dirtied by reclaim.
* **Memory**: up to 32 % more objects resident right after the deletes
  with `noEvict()` (4.5).
* **`CorruptStreamTester.testFound019_32`**: its rows name byte positions of
  format 5's streams; merges change the workloads' streams. One row of ten
  (workload "take", seed 3552484, the record at 31880, a value node's key)
  has no node there now and is skipped; the other nine pass. It needs to
  be found again in the new stream (as StreamDigest's digests need new
  values; F10).
* **`dirtyNodeBound` was far above `main`'s for deletes; now counted by the
  transaction** (023-06's condition). A probe (`scripts/BoundProbe.java`,
  20,000 keys, transactions of 1,000 deletes) found at node size 30 a bound
  of 25,000 to 29,000 nodes against `main`'s 158 to 854: P1's count of 4
  nodes a level and 2 more for each delete, which P4 kept, and P5's merges
  on top. A transaction of more than about 150,000 deletes was refused,
  which `main` takes. Now (2.3, `Dag.mergeBound`): the path's 2 klongs a
  delete as P4, no off-path nodes for the unlink, LE-b and root collapse
  (they change none), and the merges counted for the transaction: at most
  one merge a level for each delete, and with m >= 3 at most (3 W m + 2 d)
  / (m - 2) merges for W nodes of the paths and d deletes (a node of the
  paths merges at most twice before its merged node holds 2m - 1, then
  once for at most every m / 2 deletes in it; a merge into one node is a
  delete in the parent), two new nodes each, and the parents' splits from
  their klongs. At size 30 the probe's bounds are now 3,200 to 13,500
  (about 11.5 nodes a node of the paths and 1 a delete), so a transaction
  is refused only above about 2 million deletes; at size 8 (m = 2, one
  merge a level a delete) above about 130,000. `LimitProbe` (a record limit
  of 300 kB, 300 random transactions of up to 600 deletes, sizes 8, 14 and
  30, 3 seeds each): no record over the limit, restarts give the same
  checksum; at size 30 it accepts 138 to 150 transactions of 300, the
  largest with 164 deletes (before: 57 to 78, 25), records at most 43 kB.
  The count is an argument and a probe, not a proof: an undercount would
  let a transaction's dirty nodes outgrow a record (005-31). The probe's
  own count of the nodes a transaction makes dirty was not reliable
  (TransSeq takes them), so the bound is not checked against counted nodes.
* **`IndexJobsHarness` flakes under load, not a P5 fault** (3): two of
  its checks race with the harness's own background index jobs; 0 of 40
  reruns of the harness fail, with or without merges.
* **Not done**: merges of segment roots (none have siblings), and DC (dead
  klongs in live nodes, 023-06, 5.3): M5 is 3,193 against the twin's 558 in
  "sparse", the bitmaps of the deletes after a merge.


## 7. What is left for a production version

* The denser rule for "sparse", if strict at large N is wanted, and its
  thrash test (alternating puts and deletes at a boundary).
* T1 "inter"'s rewrites of left-out nodes by Rule A (6), with P6's
  question of Rule A.
* Keep the path through a merge instead of walking it again; drop the
  counters, the debug print and the `MERGES` switch.
* `dirtyNodeBound`: a proof of the merge count, or a count by node only,
  and a check against counted nodes for transactions of 1,000 deletes at
  node sizes 8, 14 and 30 (023-06, 6).
* Unit tests in DagTester for the cases of 2.4 with fixed transactions;
  UnlinkFuzz strict as a step of `level1.sh`.
* `testFound019_32`'s rows found again in the new streams; new digests.
* The C port: about 300 lines more than P4's (`merge`, `mergeParent`, the
  retarget, the descent).
* Performance runs (T10) and a startup measure at 50 MB: the rerun now
  reads siblings too.


## 8. Questions for Frans

* **Q1. The sibling rule.** The left sibling first when both fit in B / 2,
  else the right one (2.2). Good, or the multiversion B-tree's plain rule?
* **Q2. Strict for "sparse".** 1.44 times the twin's nodes at 100,000 with
  m = B / 4 and merged nodes of at most B / 2; 1.20 with merged nodes of up
  to 3 B / 4 (an experiment, 6). Accept a constant factor (023-06, 5.3), or
  take the larger merged node and test its thrash?
* **Q3. P4's take-back** (6): take the retarget into P4's branch?
* **Q4. `testFound019_32`**: skip the moved row for the prototypes, or
  find it again in the new stream now?
* **Q5. "inter"'s rewrites** (6): left-out versions of the leaf that names
  reclaim's internal keys stay dirty by Rule A. Treat it with Rule A's
  question (P6, the top nodes in D), or avoid it in the merge rule now (for
  example by not leaving out a node that names a segment root dirtied in
  the transaction before)? Recommended: with Rule A; the cost is bytes,
  not correctness.
* **Q6. `dirtyNodeBound`'s merge count** (6): an argument and a probe, not
  a proof. Accept for 2026.4, or ask for a proof or a count by node only?


## 9. State

2026-11-10, 14:08. Clone `/Users/f/fl/bench/2026-11-10/p5/clone`, branch
`023-p5-merge`, head `71e386de`: on P4's `5466e153` (fetched 12:32), P4's
`0e66d1c9` cherry-picked as `a614d508`, then `163fed3f` the merges,
`4c6bea65` keyNodeTakenBack, the take-back's retarget and CleanupRule's
measures, `5dfee887` the left sibling first and `testFound019_32`'s skip,
`789b1654` CleanupRule's user bytes, `429b56d3` dirtyNodeBound by the
transaction, `71e386de` its margin for new roots. Levels 1 to 3 passed at
`789b1654`. `before-commit.sh` and level1 passed at `429b56d3`,
`level4.sh` full (`runs/level4.sh-b.log`) and `before-commit.sh` (in
`p5/wt-build`, `runs/bc-6-wt.txt`) at `71e386de`; paths under
`/Users/f/fl/bench/2026-11-10/p5/`. Frozen builds:
`runs/b-head4` (`789b1654`), `runs/b-bound` (the bound), `runs/b-main`,
`runs/b-exp*` (experiments; their diffs `runs/exp-*.diff`, not committed).
Worktrees: `p5/wt-main` (`main` with the new CleanupRule), `p5/wt-build`
(clean, `71e386de`). Probes: `scripts/BoundProbe.java`,
`scripts/LimitProbe.java`. All gates done; nothing running.
