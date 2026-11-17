# 023-05 P1. The upward unlink, the leftmost child relabelled

Created 2026-11-10 by Frans Lundberg. Status: open.

Prototype P1 of 023 (023-05): a delete that empties a key node unlinks it
from its parent in the deleting transaction, and so on upward (023-04,
2.1, UP); an inner node's smallest live klong is relabelled down the next
child's left edge (023-04, 2.2, LE-a); a node that a transaction made and
emptied is taken back (023-04, X5 (a)); and a root with one live child
collapses (023-04, 2.3, RC). Reclaim is not changed. The code is on the
branch `023-p1-relabel` of the clone `/Users/f/fl/bench/2026-11-10/p1/clone`:
six commits on `main` (`1901394c`) and 023-03's test prototype, head
`13b3692f`.

In short:

* It works for every shape tried. T1 ends at the twin's shape at N =
  1,000 and 100,000: 6 key nodes reachable, as the twin, against 7,902 on
  `main` (but "inter", 14); the kept stream 2.20 MB against the twin's 2.13
  and `main`'s 40.4. T4's queue is steady to 1M transactions: 117 nodes
  reachable, a head scan of 4 nodes, 1.5 MB kept and a cut every 0.6 s,
  against `main`'s 111,434 nodes, 111,320 and 557 MB.
* With R forever (T3), right after the deletes, 1 node is reachable in
  every shape, as the twin, against 7,897 to 112,759 on `main`.
* The deletes write fewer bytes than on `main` (0.16 to 0.89 times), and
  hold up to 8 % more objects in memory with `noEvict()`.
* Gates at the head: `before-commit.sh` and `level1.sh` to `level4.sh`, full,
  all OK (section 2). The trace checker found three faults that the other
  tests had not, two in `level2.sh` and one with eviction (the last found
  first by prototypes P2 and P4); all fixed (section 5).
* Bounded allowance: 16 of T1's 18 rows pass; the two misses are D and the
  start's objects (C6, C9), which move with the phase of the drive. At 1M,
  T1 needs a drive of about 4,300 instead of 4,000 (reclaim's iteration
  that spans the deletes scans the keys live at its start), and then D
  and the start's objects stay above the twin's (section 5).


## 1. The mechanism as built

Code places are on the branch's head, `13b3692f`, in `java/src/bergdb/`.

### 1.1 The climb (UP)

* **When and by whom.** In the deleting transaction, for each delete, by
  the writer under the write lock: `Dag.setValue` calls `Dag.deleteUpward`
  (Dag.java:808, 1039) instead of `appendDeleteKlong`. The startup's rerun
  runs the same code.
* **The test.** The segment leaf is empty after the delete if every KEY
  klong's bit is in the union of its last bitmap and the bits of the
  key's compare value. A delete sets the bits of every klong of its
  compare value, so a KEY klong outside the union is a live key. Not
  empty: `appendDeleteKlong` as today.
* **The plan.** Empty: before anything changes, the climb goes up the key
  access path, as the splits find the parent, while the parent would be
  left with no live klong, and stops at the first node that keeps one,
  `stop`. Then every node below `stop` is unlinked, deepest first, and
  `stop` gets the change. A climb that cannot go on (1.3) changes nothing
  above its leaf.
* **Unlink** (`Dag.unlink`, Dag.java:1325). The node loses its klongs of
  tt, if it has any (`toPreviousState(tt - 1)`, as a node replaced by a
  split), and is reported as replaced (`keyNodeReplaced`), so `Db.endOfTrans`
  takes it out of D if it got dirty in this transaction only. If it got
  dirty in an earlier transaction it stays in D and is written: lookups
  before tt need that state.
* **The change at `stop`.** A segment leaf: the segment's klong (a longer
  key's next segment tree) is deleted by `appendDeleteKlong`; `setNode`
  treats a deleted segment as absent. An inner node, the klong not its
  smallest live one: it is deleted, and the range joins the left
  sibling's. The smallest live one: the relabel (1.2).
* **A segment root** left with no live klong is unlinked like any node:
  the segment's klong in the segment leaf above is deleted, and a later
  put of a key with that segment makes a new segment tree (`setNode`).
  Neither replaced nor left: nothing then routes to it.
* **The space root** left with no live klong: a segment leaf stays, empty,
  which is a valid root. An inner one is replaced by an empty segment
  leaf (`KeyNode.nodeWithTime(tt)`) through a new super root
  (`TopDs.newSuperRoot`, as time-split-2): an inner node with no live klong
  would fail the next put (`checkFound`). With RC this is rare: no test
  reached it (the counter stayed 0), so the code is not exercised.

### 1.2 The leftmost child (LE-a)

* `Dag.relabelSmallest` (Dag.java:1390). The inner node gets a KEY klong
  with the emptied child's compare value c, its old smallest, whose
  pointer is a copy of the next child's pointer
  (`KeyNode.addKlongCopyPointer`, KeyNode.java:895: the same pointee and
  reference, read under the node's monitor as `lastVersionGivenDel` copies
  pointers), and a bitmap that deletes the next child's compare value. The
  new klong shadows the old c, as a time split's klong does. A full node
  is replaced by its last version with the smallest klong set to c (the
  order stays sorted), through `handleFullNode` with no klong to insert.
* Down the next child's left edge, one node a level, to the level above
  the leaves: `Dag.descendToRelabel` (Dag.java:1471) goes down again from
  the space root at tt, by the key's segments and then by c, to the first
  inner node with no live klong at or below c, which gets the same
  relabel. Going down again after each change keeps the key access path
  right for the splits a change can cause. Leaves are searched by
  equality and are not changed; the next child is not followed but its
  pointer copied, so it is not marked: the model marks it only if
  something below it changed.
* The invariant kept: an inner node's smallest live klong is its klong in
  its parent, and a root's is the empty key. UnlinkFuzz checks it after
  every transaction (1.5).
* Cost: one node a level off the path, once per emptied leftmost child;
  each descent follows the path again, so O(H²) follows a relabel. A
  production version keeps the path instead.

### 1.3 A node made and emptied by one transaction (X5 (a))

* **The rule.** The splits record each node they make with the node it
  replaces (`PutData.madeFor`, PutData.java:106; at Dag.java:1654, the time
  split, 1819 to 1856, the space split, 1702 and 1714, the splits in
  place). A node made by the transaction (its first klong of tt) that the
  climb would unlink, and that is recorded, is taken back
  (`Dag.takeBack`, Dag.java:1368): its parent's klong of tt to it is
  pointed to the node it replaced (`KeyNode.repointKlong`, KeyNode.java:933;
  a klong of tt behind the time klong of tt, where every reader stops, as
  `replaceKlong` changes such klongs), and the climb then deletes or
  relabels that klong as for any emptied child. The node is reported as
  taken back (`keyNodeTakenBack`, which calls `keyNodeReplaced` by default),
  so it leaves D and is never written, and nothing points to it: for the
  stream and the model it was never made, and A3 holds. Db then drops it
  from the node table at the transaction's end, after D (`Cache3.dropNode`,
  Cache3.java:371; Db.java:1534), and the startup's rerun at once
  (DbStarter.java:405), as
  prototype P2 found it must (its commit `a0af194d`; `13b3692f` here). An
  inner space root made by the transaction gives way to the new empty
  root in the top node of tt. No klong is shifted and no bit remapped.
* Any other node made by the transaction is not unlinked: the first
  segment leaf at or below it keeps the delete, linked and empty, as on
  `main` (X5 (c)). A segment leaf made by a put holds the put's key and
  cannot empty in its transaction; no run reached this case.
* **Why it matters.** Without it, batch deletes in key order left 400 such
  nodes at N = 100,000 (a relabel time-splits a full inner node, and the
  same batch empties the new node), each with a chain of single
  children: 830 nodes reachable against the twin's 6. With it: 0 and 6.

### 1.4 Root collapse (RC)

* `Dag.collapseRoot` (Dag.java:1175), after a climb that ends in an inner
  node: while the root of that segment tree is an inner node with one live
  klong, its only child takes its place: the space root through a new
  super root, a segment root through a klong of the same compare value in
  the segment leaf above, which shadows the old one, as time-split-1 does.
  The old root is unlinked; a root that the transaction made (a split's
  last version or new root) is taken back as in 1.3 (`c00449e9`): the space
  root's top node of tt changes in place, and a segment root's klong of tt
  is first pointed to the node that root replaced. The one live klong of a
  root is the empty key, and the relabel keeps the empty key down the left
  edge, so the child is a valid root.
* The child does not change, so it is followed without being marked
  (`Dag.followQuietly`, Dag.java:1287, and `descendToRootQuietly`, 1232,
  when the loop goes down again; section 5).
* Only roots collapse: an inner node below the root with one live child
  stays. So two live keys whose paths part high in a tree keep a chain of
  single children each (T2's row "inter", section 3).
* Without the take-back of a root made by the transaction, deleting every
  key of a tree in one transaction left a chain of 3 to 8 single children
  above the one live key (a probe, one-segment keys, 1,000 to 20,000 keys);
  with it, 1 node, as the twin.

### 1.5 Other changes

* `Dag.dirtyNodeBound` (Dag.java:477, 511): a delete counts 2 klongs in
  every node of its path, not 1 in its leaf, and 4 nodes a level plus 2
  (the relabel off the path and its splits, a new root and top node).
  `Db.checkDirtyNodes`'s cheap test counts 7 nodes a level a segment for a
  delete instead of 3 (Db.java:2709). Conservative; not checked against
  counted nodes.
* `StoredTrans.RECORD_FORMAT` 6 (StoredTrans.java:56), so that a start
  refuses earlier databases (023-02, F9 (a), F10); its unit test now names
  the format after the current one as the newer one.
* `stress/A2A3Check2.java`: a node reported as made and as replaced in one
  transaction counts as taken back, not as made, and is printed. A change
  of a checker of the model's rules: for Frans to approve (section 7).
* `stress/UnlinkFuzz.java` (new): random transactions of puts and deletes
  on the Dag alone; after each, gets of every key at every time, scans
  forward and backward from random start keys, inclusive or not, with
  limits, at every time, against a model; and the tree at the latest
  time: no reachable node without a live klong, the relabel's invariant,
  and the live keys. Shapes: random, a FIFO, long keys of 1 to 3
  segments.
* `Cache3.dropNode`, `Db.endOfTrans` and the rerun's listener in
  `DbStarter`: a node taken back leaves the node table (1.3).
* Static counters in `Dag` (`statUnlinked` and others) for the
  measurements; not for production.

### 1.6 Readers, lookups, the rerun and reclaim

* Entries only at tt, in nodes reachable at tt; an unlinked node loses its
  entries of tt; klongs of tt change in place only behind the time klong
  of tt (the re-pointing, the transaction's own bitmap). Readers before tt
  see the tree as it was, so lookups at every available time are as
  before (023-02, R1, R16). UnlinkFuzz, DagFuzz and CleanupRule's checks
  (023-03, T6) found no wrong lookup.
* The rerun: the climb is a function of the delete and the state at
  tt - 1 (the model's A1), so a start redoes it with the same ids;
  RestartStress and RestartInvariance pass (section 2).
* Reclaim: its touch follows live klongs only, so it no longer reaches an
  unlinked node: in T1 it visits 7 nodes, as the twin's, against 7,320 on
  `main` at N = 100,000. The unlinked nodes' versions go with the cuts:
  T1's kept stream is the twin's (section 3).
* A workload of puts only gives the same counts as `main`: the twin with
  20,000 more overwrites gives the same RESULT line on both.


## 2. The gates

| Gate, commit                         | Result                                                 |
|---|---|
| `before-commit.sh`, `13b3692f`       | BEFORE COMMIT OK, 326 s                                |
| `level1.sh`, full, `13b3692f`        | LEVEL 1 OK; MEM 129 (at most 131), SS 1.51 (worktree)  |
| `level2.sh`, full, `13b3692f`        | LEVEL 2 OK; conformance: 70 traces, all TRACECHECK OK  |
| `level3.sh`, full, `13b3692f`        | LEVEL 3 OK; conformance reclaim: 25 traces, 305 cuts   |
| `level4.sh`, full, `13b3692f`        | LEVEL 4 OK; conformance evict: 45 traces, C-H 0 fail   |
| conformance.sh evict, `13b3692f`     | CONFORMANCE OK, 45 traces (`c00449e9` fails C-H)       |
| `before-commit.sh`, `c00449e9`       | BEFORE COMMIT OK, 307 s (also `a0af531b`, `0f16daae`)  |
| `level1.sh`, full, `c00449e9`        | LEVEL 1 OK; MEM 129 (at most 131), SS 1.51             |
| `level2.sh`, full, `e60f6c82`        | FAILED at its last step, conformance small (section 5) |
| `level2.sh`, full, `c00449e9`        | LEVEL 2 OK; conformance: 70 traces, all TRACECHECK OK  |
| `level3.sh`, full, `c00449e9`        | LEVEL 3 OK; conformance reclaim: 25 traces, 305 cuts   |
| `level4.sh`, full, `c00449e9`        | stopped in step 3, for `13b3692f` (section 5)          |
| A2A3Check2, 5 configs, `c00449e9`    | all rules hold, nodes taken back counted               |
| UnlinkFuzz, `13b3692f`               | 0 failures: 3 shapes, sizes 8 to 30 (and batches of 60) |
| DagFuzz as level1, 4,500 rounds      | 0 failures                                             |
| StreamDigest quick, `13b3692f`       | the four modes agree; every digest differs from `main` |

`level1.sh` passed at `e60f6c82` too. A2A3Check2's five configurations are
level2's three and two of batch deletes (40 and 60 KVs a transaction, 50
and 60 % deletes).

StreamDigest's digests differ in all 11 configurations, as expected: the
format byte is in every record. 7 keep their length; 4 with deletes are
shorter (l2-idle-1 by 48 bytes, l2-sd1000-node8 by 8,336, l2-sd10000-node14
by 78,912, l3-node8 by 20,600), and in l3-node14 and l3-node8 the cut comes
earlier (first available time 18.2 s and 6.2 s of test time earlier). New
digests need Frans's approval with the format (023-03, 6.2).


## 3. Measurements against `main`

All counts, from 023-03's prototype (`CleanupRule`) on frozen copies of the
head's build and of `main`'s, run the same way; `main`'s equal 023-03's
(section 8). Runs and output: `/Users/f/fl/bench/2026-11-10/p1/runs/`
(`*-final.txt` for the head, `13b3692f`; its counts equal `c00449e9`'s but
the resident objects).

### 3.1 T1, "after", against the twin

| Measure                 | Twin  | Main 1,000 | P1 1,000 | Main 100,000 | P1 100,000 |
|---|---|---|---|---|---|
| M1, MB, most in window  | 2.13  | 2.26       | 2.15     | 40.42        | 2.20       |
| M3, ms                  | 1,039 | 1,221      | 1,222    | 5,951        | 1,142      |
| M4, reachable           | 6     | 84         | 6        | 7,902        | 6          |
| M5, dead klongs         | 35    | 1,047      | 31       | 102,918      | 61         |
| M6, get                 | 1     | 1          | 1        | 1            | 1          |
| M8, D, most in window   | 79    | 166        | 89       | 26           | 107        |
| M9, bytes, in window    | 2,840 | 25,968     | 2,840    | 1,729,720    | 2,872      |
| M10, touch visited      | 7     | 85         | 7        | 7,320        | 7          |
| M11, after the probe    | 85    | 156        | 97       | 7,927        | 106        |
| Loads after the probe   | 2     | 163        | 5        | 15,800       | 5          |
| Cuts in the drive       | 11    | 11         | 11       | 0            | 15         |

M10 is the last iteration done (on `main` at 100,000 the one in progress
never ends). At N = 1M, `main` (drive 4,000): M1 319.0 MB, M3 12,956 ms, M4
78,999, M8 31, M11 79,033. P1:

| Drive                        | M1, MB | M3, ms | M4 | M8  | M9, bytes | M11 |
|---|---|---|---|---|---|---|
| 4,000, P1                    | 286.5  | 1,003  | 6  | 161 | 5,256     | 126 |
| 12,000, P1                   | 2.52   | 1,225  | 6  | 134 | 3,624     | 144 |
| 12,000, its twin             | 2.19   | 1,039  | 6  | 94  | 3,480     | 83  |

The reclaim iteration that runs during the deletes started before them, so
its scan at its tStart passes the 1M keys live then, about 16 kB of KVs a
step; it ends near drive transaction 3,300, the cuts resume, and from 4,300
on M1 is the twin's (2.29 MB at 5,000). `main`'s never ends in the drive:
its largest record there is 12 MB, P1's 2.4 MB.

### 3.2 T2, the matrix, by 023-03's criteria

C1 to C3 and C5 to C10 with the bounded allowance (a_n = 10 + 4 h_fill),
and with the strict one (a_n = 10, C4 too). C11 needs H2, not in the
prototype. `main` fails every row in both (023-03, 8.2; the same runs).

| Row, N = 1,000      | M4 | M5  | M8  | M11 | Bounded | Strict    |
|---|---|---|---|---|---|---|
| after, ascending    | 6  | 31  | 89  | 97  | pass    | C9        |
| before              | 6  | 31  | 89  | 97  | pass    | C9        |
| around              | 6  | 39  | 89  | 103 | pass    | C9        |
| inter               | 10 | 57  | 21  | 23  | pass    | pass      |
| hashed, random      | 6  | 41  | 81  | 92  | pass    | pass      |
| after, descending   | 6  | 28  | 104 | 118 | C9      | C6 C9     |
| after, random       | 6  | 32  | 88  | 99  | pass    | C9        |
| after, 3 versions   | 6  | 45  | 89  | 97  | pass    | C9        |
| long                | 6  | 39  | 107 | 106 | pass    | C6 C9     |

| Row, N = 100,000     | M4 | M5  | M8  | M11 | Bounded | Strict    |
|---|---|---|---|---|---|---|
| after, ascending     | 6  | 61  | 107 | 106 | pass    | C6 C9     |
| before               | 6  | 59  | 82  | 79  | pass    | pass      |
| around               | 6  | 42  | 116 | 96  | C6      | C6 C9     |
| inter                | 14 | 146 | 24  | 25  | pass    | C4        |
| hashed, random       | 6  | 58  | 102 | 97  | pass    | C6 C9     |
| after, descending    | 6  | 42  | 83  | 87  | pass    | pass      |
| after, random        | 6  | 68  | 94  | 86  | pass    | C4 C6     |
| after, 3 versions    | 6  | 48  | 103 | 106 | pass    | C6 C9     |
| long, N = 10,000     | 6  | 37  | 88  | 97  | pass    | C9        |

The twin: M4 6, M5 35, M8 79, M11 85. In every row C1, C2, C3, C5, C7, C8
and C10 pass with both allowances; M3 is 1,013 to 1,247 ms (twin 1,039),
M9 at most 4,048 bytes (twin 2,840), and the touch visits 7 to 15 nodes.
C6 and C9 are the noisy ones: the twin's own M8 is 79 at a drive of 4,000
and 94 to 105 at 12,000, and M11 is in proportion (5).

### 3.3 T3, single scans right after the deletes, R forever

| Shape            | Main, M4 | P1, M4 | Main, the first user key | P1  |
|---|---|---|---|---|
| after            | 7,897    | 1      | 1                        | 1   |
| before           | 7,897    | 1      | 7,897                    | 1   |
| around           | 8,039    | 1      | 4,020                    | 1   |
| inter            | 7,896    | 1      | 1,182                    | 1   |
| long, N = 10,000 | 60,787   | 1      | 60,787                   | 1   |
| hashed, random   | 112,759  | 1      | 4                        | 1   |

N = 100,000 (long: 10,000). The twin with R forever: 1 and 1. A scan of n
KVs at the latest time follows the nodes of the live keys only; at an
earlier time t, those live at t, as the unlink is at each delete's own
time (023-02, F3). T3's 1,000 rounds were not run.

### 3.4 T4, the queue

| Keys, transactions       | M4      | Head    | M3, s | M1, MB | Cuts  | M9, kB |
|---|---|---|---|---|---|---|
| ordered, 100,000, main   | 11,147  | 11,033  | 78.2  | 53.2   | 9     | 1,860  |
| ordered, 100,000, P1     | 117     | 4       | 1.26  | 1.48   | 165   | 32     |
| ordered, 1,000,000, main | 111,434 | 111,320 | 893.1 | 557.1  | 10    | 20,643 |
| ordered, 1,000,000, P1   | 117     | 4       | 1.38  | 1.49   | 1,695 | 32     |
| hashed, 100,000, main    | 112,782 | 130     | 9.9   | 112.5  | 20    | 391    |
| hashed, 100,000, P1      | 2,134   | 5       | 1.23  | 3.54   | 211   | 25     |

M9: the largest record of the run. In P1 every checkpoint from 10,000 on
has the same M4 (117 ordered, 2,134 hashed, the 1,000 live keys' own
trees), a head of 4 or 5 nodes, M1 1.30 to 1.71 MB ordered and 3.17 to
3.83 MB hashed, and M3 1.03 to 1.70 s, R plus the cut's phase. Against
T4's allowances of the first checkpoint after the warm-up, all pass but
C2 (M3 within R / 4): it misses at some checkpoints, by up to 0.4 s (1,698
ms at 20,000 against 1,052 + 250), and at 1M once, 1,535 ms at 500,000
against 1,256 + 250.

### 3.5 What the deletes write and hold

The delete phase of T3 (R forever, no reclaim): the stream it adds, the
dirty nodes left after it, and the objects resident with `noEvict()`.

| Shape, N         | Main, bytes | P1, bytes  | Ratio | D, main | P1 | Objects, main | P1      |
|---|---|---|---|---|---|---|---|
| after, 100,000   | 6,778,848   | 5,036,136  | 0.74  | 132     | 53 | 9,592         | 10,094  |
| around, 100,000  | 6,886,568   | 5,792,288  | 0.84  | 108     | 72 | 10,800        | 11,576  |
| inter, 100,000   | 5,963,400   | 4,322,152  | 0.72  | 130     | 70 | 9,597         | 10,105  |
| long, 10,000     | 6,367,392   | 1,018,816  | 0.16  | 612     | 24 | 60,952        | 61,006  |
| hashed, 100,000  | 108,958,784 | 96,573,416 | 0.89  | 429     | 56 | 117,507       | 126,514 |
| after, 1,000,000 | 68,203,168  | 50,754,448 | 0.74  | 114     | 55 | 95,987        | 100,993 |

Fewer bytes: an emptied node is not written again, and the bitmap of a
climb lands in a node of the path that is written anyway. More objects
(up to 8 %): the relabel's splits of inner nodes make more node versions,
which stay in memory with `noEvict()` (the nodes taken back leave it since
`13b3692f`); after a restart and a probe, P1 holds
97 to 144 objects where `main` holds 156 to 79,033 (M11).


## 4. Requirements and tests met

023-02:

* R1, R16 (lookups, readers): yes, by design (1.6) and by every check run.
* R3, R5 (the reachable index, work): yes for nodes with nothing live
  below, at every time from the delete on; not for dead klongs in nodes
  that keep live keys (M5; F1), which go only at the node's time split.
* R6 (reclaim keeps up): yes in T4 and T1 to 100,000; at 1M the iteration
  running at the deletes takes about 3,300 transactions to end (3.1).
* R9 (scans): yes at every time, from the delete on (3.3, T4's head).
* R10 (gets): the height shrinks only at the roots (RC): a get of
  "/a.txt" follows 1 node, as the twin's, but in "inter" 5 (3.2).
* R11 (puts and deletes): O(H) nodes, off the path one a level for a
  relabel; records of at most 32 kB in T4 against 20 MB on `main`.
* R12 (a): yes. R12 (b), underfill: no (no merge; F5).
* R13 (stream): yes to 100,000; at 1M after a longer drive.
* R14 (memory): D and the start's objects within the bounded allowance to
  100,000 but in two rows; at 1M not (5).
* R17, R18 (determinism, restarts, crashes): RestartStress,
  RestartInvariance and CrashTest in level1 and level2 (section 2);
  StreamDigest's four modes agree.
* R22, R23: format 6, earlier databases refused at the start.
* R24 (Lean): A2A3Check2 with the taken-back change, and the trace
  checker (level2 to level4, section 2); the model is not changed.

023-03: T1 bounded at N = 1,000 and 100,000 in 16 of 18 rows (one misses
C9 by 7 objects, one C6 by 3 dirty nodes); at 1M it fails C1 with the
fixed drive of 4,000, and C6 and C9 after convergence. T2 as in 3.2. T3's
single scans pass. T4 passes but for C2, M3 by up to 0.4 s at some
checkpoints. T6 found nothing. T7 and T8 through the level scripts and
StreamDigest. T9: section 2. T10 and T11 not run.


## 5. Faults and limits found

Two faults were found by `level2.sh`'s trace checker (conformance.sh small,
the a6 traces: two-segment keys, 40 KVs a transaction) after
`before-commit.sh`, `level1.sh`, A2A3Check2 and the fuzzers had passed;
both fixed in `0f16daae`:

* **The relabel's klong before its bitmap.** In the trace format a bitmap
  deletes the klongs before it that have the compare values of its new
  bits (docs/trace-format.md, "D"); Java's bitmap deletes by index. The
  relabel appended its klong c and then a bitmap with the bits of c's
  older klongs, so the model deleted the new klong too: the relabelled
  child was unreachable in the model at tt (C-A: A2, A3, A5, A-COPY), not
  in Java. Now the bitmap comes first, as when the transaction's own
  bitmap is changed in place.
* **Root collapse marked an unchanged node.** After a collapse the loop
  went down again to look at the new root, and that follow marked it
  dirty, though nothing below it changed; the still-dirty test then kept
  its parents dirty too (C-S: gd and D, Java only). Now the segment root
  is followed without marking (`Dag.descendToRootQuietly`).

A third, with eviction, fixed in `13b3692f`:

* **A node taken back stayed in the node table.** Its canonical object,
  never written and named by no node, stayed in the table, and the trace
  checker's C-H (handles) failed with eviction: conformance.sh evict,
  e-mixed seed 3, fails at `c00449e9` and passes at `13b3692f`; so do 8
  draining traces with 65 % deletes and random eviction, and the whole
  evict set (45 traces). Prototype P2 found it in its own take-back and
  fixed it with `Cache3.dropNode`; P4 saw it on P1's `0f16daae`; the
  coordinator relayed it, and P1 took P2's fix.

The first was a disagreement between Java's index-based bitmap and the
model's compare values, which only the trace checker compares; the second
a marking that A2A3Check2's configurations did not reach; the third a
state of the node table that only the checker with handles sees. All show
why the level scripts' conformance steps must gate this change.

Limits:

* **D and the start's objects** (C6, C9). After convergence at 1M, D in
  the window is 134 against the twin's 94, and the start's objects 144
  against 83 (bounded allowance 38). D there is the newest top nodes (128
  of 155 in a probe, a run of consecutive ids) and old root leaves: the
  same make-up as the twin's D (55 top nodes and 24 leaves at 100,000),
  and no node of the deleted keys (3 of D's nodes are reachable key
  nodes, as the twin's 3 to 5). The still-dirty test (Rule A) keeps a
  written node dirty while any pointer of it, live or dead, names a dirty
  object; old root leaves name the current segment root of reclaim's
  internal keys, dirty in most transactions, and the top nodes name the
  leaves and each other, so the run's length follows phase and history.
  New super roots come at the twin's rate. The twin's own D moves with
  them: 79 at a drive of 4,000, 94 to 105 at 12,000, 96 and 87 with
  20,000 and 60,000 more overwrites before the drive (the same on `main`).
  At 100,000 P1's D is 82 to 116 by row. My reading, not proven: the gap
  is phase, not a rest of the deletes; at 1M not explained.
* **T1 at 1M needs a longer drive.** Reclaim's iteration that spans the
  deletes scans at its tStart, where the keys are live (3.1). Not P1's
  code; it costs about one step a transaction for 1/16 of the live data
  at tStart, so the drive T1 needs grows with N (023-03, Q1).
* **Single-child chains.** Below the node where two live paths part, each
  keeps its chain of single children (row "inter", 10 at 1,000 and 14 at
  100,000, against 6): RC takes roots only. Strict needs a merge (MG) or the
  rebuild by reclaim (RB) (023-04, X3).
* **Dead klongs in live nodes** (M5, C4 strict): the relabel and the
  climb's bitmaps add klongs to nodes that keep live keys; they go at the
  node's next time split (F1; 023-04, X4).
* **Not exercised.** The replacement of an inner space root by an empty
  leaf, and the fallback for a node made otherwise than by a split
  (X5 (c)): no run reached either (their counters stayed 0, also in a
  probe that deletes every key in one transaction).
* **Cost.** A relabel goes down from the root again for each level,
  O(H²) follows; not measured in time.


## 6. What is left for a production version

* Keep the key access path through the relabel instead of going down
  again; a follower call that does not mark, instead of swapping pd's
  listener (`followQuietly`); remove the static counters.
* `dirtyNodeBound`: a test of the bound against counted nodes for
  transactions of many deletes, and a tighter count.
* A test for the space root replaced by an empty leaf, and for the
  fallback of X5 (c), or a proof that it cannot happen.
* The cause of the larger D and start at 1M (5).
* Unit tests: the relabel, the take-back and RC in DagTester; UnlinkFuzz
  and a probe of one transaction that deletes every key in `level1.sh`;
  023-03's tests as code (`CleanupTester`, `cleanup.sh`). An A2A3Check2
  configuration that reaches root collapse after a collapse: its three
  configurations did not, and the trace checker found that fault (5).
* Java's bitmap deletes by index, the model's by compare value (5): an
  assert that every bitmap's new bits cover every earlier klong of their
  compare values would catch a disagreement where it is made.
* The C port: about 400 lines of C (`deleteUpward` and its helpers, the
  record of replaced nodes, the pointer copy and re-pointing).
* Dead klongs in live nodes and underfill, for strict: reclaim's rebuild
  (P3's direction) or merges.
* Performance runs (T10) and Props, with Frans's tolerance (023-02, F12).


## 7. Questions for Frans

* **Q1. A2A3Check2.** A node made and taken back in one transaction counts
  as not made (1.5). Approve this change of the checker?
* **Q2. The take-back.** The parent's klong of tt is pointed to the node the
  taken-back node replaced (1.3), instead of being removed with its bits
  remapped (023-04, X5 (a)). Approve this form?
* **Q3. T1 at large N.** Accept a drive that grows with the live data at
  the start of the iteration that spans the deletes, or must reclaim's
  scan skip what was deleted since its tStart (P3's area)?
* **Q4. D after the deletes** (5). D and the start's objects stay above
  the twin's at 1M, made of top nodes and root leaves as the twin's are.
  Must P1 explain it before a comparison of the prototypes, or later?


## 8. State

2026-11-10, 13:25. Done for this phase. Clone
`/Users/f/fl/bench/2026-11-10/p1/clone`, branch `023-p1-relabel`, head
`13b3692f`: `a0af531b` the unlink and the relabel, `b3dde5ab` the
take-back, `e60f6c82` root collapse, `0f16daae` the two faults the trace
checker found, `c00449e9` root collapse takes back a root made by the
transaction, `13b3692f` a node taken back leaves the node table; on
`f08b3a88` (023-03's tests) and `main`'s `1901394c`. The head passes
`before-commit.sh` and `level1.sh` to `level4.sh`, full (section 2). A
worktree of branch `023-p1-rc-made` (the same commits) at
`/Users/f/fl/bench/2026-11-10/p1/wt-rc`. A baseline of `main` with the
same tests: `/Users/f/fl/bench/2026-11-10/p1/main-clone`. Runs, scripts and
frozen builds: `/Users/f/fl/bench/2026-11-10/p1/runs/` (`t1.sh`, `t1b.sh`,
`t4.sh`, `fuzz.sh`, `a2a3.sh`, `judge.py`, `all-final.sh`; `b-final/` the
head's build, `b-main/`). Probes: `/Users/f/fl/bench/2026-11-10/p1/probe/`.
Nothing running. Next, for Frans and the coordinator: section 7, and the
comparison with P2 and P3.
