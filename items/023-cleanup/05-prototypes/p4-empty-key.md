# 023-05 P4. The upward unlink, the empty key first

Created 2026-11-10 by Frans Lundberg. Status: open.

Prototype P4 of 023 (023-05): P1's upward unlink at the delete (023-04,
2.1, UP), with the leftmost child handled by "LE-b, the empty key first"
(023-04, 2.2 and X1) instead of P1's relabelling down the left edge (LE-a).
X5 (a), root collapse (RC) and format 6 are P1's, with two changes found
here: a root that a split of the transaction made also collapses, and a
node taken back leaves the node table (P2's fix). The code is on the branch
`023-p4-empty-key` of the clone `/Users/f/fl/bench/2026-11-10/p4/clone`, on
P1's head `0f16daae` (fetched at 11:55).

In short:

* Every inner node has the empty key as its smallest live klong. One rule
  of the space split changes; an emptied leftmost child costs one klong in
  its parent, which is on the delete's path. No node off the path changes:
  P1 changed 704 nodes off the path in T3's "after" at N = 100,000, P4 none.
* The deletes write 2 to 6 % fewer bytes than P1's (none fewer in
  "hashed") and 0.16 to 0.89 of `main`'s, and leave as many objects in
  memory as `main` (+0.1 %; "hashed" +8 %), where P1 leaves 7 to 8 % more.
* T1 ends at the twin's shape (6 nodes reachable) in every row at N =
  1,000 and 100,000 but "inter" (10 and 14, as P1); "hashed" too (P1 9),
  as a root made by a split of the transaction now collapses. 17 of T1's
  18 rows pass the bounded allowance (P1 at `0f16daae` 16). T4's queue is
  the same as P1's, byte for byte.
* Gates: `before-commit.sh` and `level1.sh` OK; UnlinkFuzz with a stronger
  check, A2A3Check2, and the trace checker on 21 draining traces made for
  P4 and on conformance's `e-mixed` pass; `level2.sh` full: LEVEL 2 OK,
  with its 70 traces; `level3.sh` and `level4.sh` quick OK; conformance's
  evict and reclaim sets OK; `level1.sh` OK at the head too. Not run:
  StreamDigest (its digests change), the full level3 and level4.
* Every reader takes the empty key as a lower bound, as it takes the roots'
  empty key today; 021-28's end key loses no pruning (section 1.5).
* At N = 1M, after convergence, D and the start's objects hold a run of
  dirty top nodes whose length depends on the history, not on LE-b: P4 178,
  P1 91 with batches of 100 keys; P4 179, P1 236 with batches of 99 (3.6,
  Q4).


## 1. The mechanism as built

Code places are on the branch's head, in `java/src/bergdb/`.

### 1.1 The rule: the empty key first

* **What.** Every inner node (a key node that is not a segment leaf) has
  `Klong.EMPTY_KEY`, the compare value 0, as its smallest live klong, at
  every time it exists. Its parent's klong to it, the compare value of the
  first key routed to it, stays a lower bound of every key below it, as
  before; the empty key is a weaker lower bound inside the node.
* **The one rule that changes.** A space split of an inner node gives its
  second half the empty key as its first klong, while the parent gets the
  second half's first compare value for it, as before
  (`KeyNode.firstAndSecond`, KeyNode.java:1387 to 1407). A klong being
  inserted by the split (a split of the child it names) that has that
  compare value goes to the second half as the empty key too, so that it
  shadows the copied one: without that, the second half would have the old
  child under the empty key and its replacement under the compare value,
  and a scan would visit both (a mutation test, section 2, found this).
* **By whom and when.** The writer, in every space split of an inner node:
  space-split-1, -2 and -3 and the split in place of a node made by the
  transaction (`Dag.spaceSplit`, `Dag.spaceSplitInPlace`, which both call
  `firstAndSecond`). The roots that space splits make had the empty key
  first already (Dag.java:1854, 1880 and in place 1734).

### 1.2 The leftmost child at a delete (LE-b)

* **When.** In the deleting transaction, when the upward unlink's climb
  stops at an inner node `s` whose klong to the emptied child is the empty
  key (`Dag.deleteUpward`, Dag.java:1135 to 1145). A klong that is not the
  empty key is deleted with a bitmap, as P1 does for any klong but the
  smallest. `s`'s smallest live klong must be the empty key; if not, the
  writer throws `Bug` (the database fails rather than misroutes).
* **What** (`Dag.emptyKeyNext`, Dag.java:1422). The next live child is the
  one with the smallest live compare value but 0, at index j with compare
  value c_j. `s` gets a bitmap of tt that deletes c_j (or the transaction's
  own bitmap is changed in place), and a new klong of the empty key whose
  pointer is a copy of pointer j (`KeyNode.addKlongCopyPointer`, P1's): the
  same pointee and reference, read under the node's monitor. The new klong
  shadows the old empty key, as a time split's klong shadows the old one;
  the old klongs of 0 get no delete bit.
* **In place.** If the latest klong of the empty key is of tt (a split of
  the transaction made it, a take-back pointed it to the old node, or an
  earlier delete of the same transaction gave it), its pointer is set to a
  copy of pointer j instead (`KeyNode.copyPointer`, KeyNode.java:933): it
  is behind the time klong of tt, where every reader stops, as
  `replaceKlong` changes such klongs. So a node gets at most one klong of
  the empty key a transaction.
* **A full node** is replaced by its last version without the old empty
  key's klongs, whose first klong (that of c_j) becomes the empty key; the
  order stays sorted. Through `handleFullNode` with nothing to insert, as
  P1's relabel did: a time split or a space split, and the splits above.
* **Nothing below changes.** The next child's own first klong is the empty
  key already, or it is a segment leaf. P1's `relabelSmallest` and its
  descent down the left edge (`descendToRelabel`) are gone.
* **If no other child is live**, `s` is empty too and the climb goes on
  upward: the climb's test treats every klong of 0 as deleted
  (`allKeysIn` with `bitsOf(s, 0)`), shadowed ones included.

### 1.3 What is kept from P1, and two changes to it

* **Kept**: the climb and `unlink` (UP), the take-back of a node made and
  emptied by one transaction (X5 (a), P1's form: the parent's klong of tt
  pointed to the node it replaced), `StoredTrans.RECORD_FORMAT` 6, P1's
  `dirtyNodeBound` and `Db.checkDirtyNodes` counts (now a margin: LE-b
  changes no node off the path), the counters in `Dag`.
* **RC also takes a root made by the transaction** (`Dag.collapseRoot`,
  `Dag.takeBackRoot`, Dag.java:1170 to 1250). P1's collapse stopped at a
  root whose first klong is of tt. In T3's "hashed" the last batch of
  deletes replaced the full space root by its last version (a time split
  for a bitmap), and later deletes of the batch left it one child: four
  levels of single children stayed (get 4 against the twin's 1). Now such
  a root, if a split of the transaction made it (`PutData.replacedBy`), is
  taken back: the klong of tt that links it, in the top node of tt
  (`TopDs.newSuperRoot` updates it in place) or in the segment leaf above
  (`KeyNode.repointKlong`, P1's), is pointed to its one child, and the root
  is never written. T1's "hashed" at N = 100,000 goes from 9 reachable
  nodes to 6, the twin's.
* **A node taken back leaves the node table** (`Cache3.dropNode`,
  `Dag.NodeChangeListener.keyNodeTakenBack`, `Db.endOfTrans`, and at once
  in the startup rerun, `DbStarter`), as P2 does for its dropped nodes (P2,
  section 6, finding 4). Without it the trace checker's C-H fails with
  eviction: the canonical object of a node never written stayed in the
  table. P1 at `0f16daae` fails so in conformance's own `e-mixed` seed 3
  (37 of 61 transactions) and in draining configurations (section 2).

### 1.4 Every place that makes an inner node or changes its first klong

| Place                                        | The empty key first, because              |
|---|---|
| space-split-3, -2: the new root              | `EMPTY_KEY` added first, as before        |
| any space split: the first half              | the old node's first klong, by induction  |
| any space split: the second half             | 1.1, the new rule                         |
| `spaceSplitInPlace`, also its new root       | the same `firstAndSecond`; root as before |
| time splits, `lastVersion`                   | the live klongs, sorted: 0 is first       |
| `lastVersionGivenDel` in `appendDeleteKlong` | never deletes 0 in an inner node (1.2)    |
| `timeSplit`'s `replaceKlong` of the child    | the path's klong, 0 for the first child   |
| `emptyKeyNext`, full node                    | sets the last version's first klong to 0  |
| RC, `replaceRoot`, `takeBackRoot`            | the child is inner with 0 first, or leaf  |
| `TopDs.newSuperRoot`, the empty space root   | a segment leaf (`KeyNode.nodeWithTime`)   |
| a new segment tree                           | starts as a segment leaf, as before       |
| reclaim, eviction, the startup               | make no key node; the rerun is the Dag's  |

The empty key stays live in an inner node from its first klong to its
last: only `emptyKeyNext` replaces it, with another klong of 0; a delete
bitmap never sets its bits (the climb unlinks a node that loses its last
live klong instead). UnlinkFuzz checks the rule after every transaction.

### 1.5 Every reader: the empty key is a lower bound of every key

A klong's compare value above the leaf is read as a lower bound of every
key below it. The empty key's 0 is a lower bound of every key, so every
reader that reads the roots' empty key today reads the new nodes right.
Each place, as the code reads:

| Reader                                       | With the empty key first                  |
|---|---|
| gets, `getEqNodeInSegment` (Dag.java:432)    | `searchLte` finds 0 or a closer klong     |
| puts, deletes, `setValue`, `setNode`         | the same; `checkFound` cannot fire        |
| `dirtyNodeBound`'s walk (Dag.java:493)       | the same; its walk never stops early      |
| P1's descents, `descendToRootQuietly`        | the same, with `checkFound`               |
| `Chain.setup` forward (GetMany.java:246)     | `searchLte`; no start key: -1, then 0     |
| `Chain.setup` backward (GetMany.java:257)    | `searchLte`, as for any start key         |
| `Chain.setup`, hasDiff (240, 242)            | the first klong (0) or the last           |
| `Chain.next`, both ways (345 to 353)         | sibling order; 0 sorts first              |
| 021-28's `isPastEnd` (branch only)           | right; no pruning lost, see below         |
| reclaim's scan and touch                     | `GetMany`, as above                       |
| the startup rerun (`DbStarter`)              | reruns the Dag's rules, the split's too   |
| the trace checker, the Lean model            | no routing by key: K entries, D by value  |
| A2A3Check2, TraceExport's LIVE lines         | no routing by key                         |
| `KeyNode.searchFirst`                        | would take a shadowed 0; not used (P2)    |

* **Scans.** Forward from no start key, `searchLte(-1)` finds nothing and
  the cursor -1 then finds 0 with `searchGt`, as in a root today. A
  backward scan's setup above the leaf finds 0 or a closer klong for every
  start key, so its "before the first" case occurs only in a segment leaf.
  `Chain.next` only steps between siblings; the shadowed klongs of 0 are
  hidden as any shadowed klong is.
* **021-28's end key** (`isPastEnd`, branch `scan-deleted-keys`) is checked
  on each klong `Chain.next` finds before its pointer is followed. It sees a
  klong of 0 only as the first klong of a child it has just entered; that
  child's bound is its klong in the parent, which `isPastEnd` checked one
  level up (or the child is a root, which had 0 first already). The bound
  0 is weaker, never wrong, and adds no follow: no pruning is lost. With
  LE-c (P2) the same check needs an exception (P2, section 2).
* **Lookups at earlier times.** Every change is a klong of tt or a change in
  place behind the time klong of tt. A reader at time t before tt sees
  the old klong of 0 to the old child; the next child, reached by the
  empty key from tt on, gets keys below its old klong only at later times.

### 1.6 Tests changed

* `stress/UnlinkFuzz.java` (P1's): the relabel's invariant is replaced by
  LE-b's (every inner node's smallest live klong is 0), and a stronger
  one: every live key of a segment leaf is in the range its parents'
  klongs give it, at or after the klong that leads to it and before the
  next one. Two mutations of `firstAndSecond` are found by it: without the
  rule (the invariant, at once) and without the inserted klong's mapping
  (a scan with a key twice, random shape).


## 2. The gates

| Gate                                    | Result                                        |
|---|---|
| `before-commit.sh`, `aeb364ce`          | BEFORE COMMIT OK (350 s)                      |
| `level1.sh`, full, `aeb364ce`           | LEVEL 1 OK; MEM 129 (at most 131), SS 1.51    |
| `before-commit.sh`, `5466e153`          | BEFORE COMMIT OK (361 s)                      |
| `before-commit.sh`, `0e66d1c9`          | BEFORE COMMIT OK (352 s)                      |
| `level1.sh`, full, `0e66d1c9`           | LEVEL 1 OK; MEM 130 (at most 131), SS 1.51    |
| `level2.sh`, full, `0e66d1c9`           | LEVEL 2 OK (17 min); conformance 70 of 70     |
| `level4.sh quick`, `0e66d1c9`           | LEVEL 4 OK; conformance 15 of 15 (C-H, C-P)   |
| `level3.sh quick`, `0e66d1c9`           | LEVEL 3 OK; conformance 10 of 10, 122 cuts    |
| `conformance.sh evict 2`, `0e66d1c9`    | CONFORMANCE OK, 30 of 30 (C-H, C-P 0 fail)    |
| `conformance.sh reclaim 2`, `0e66d1c9`  | CONFORMANCE OK, 10 of 10, 122 cuts            |
| UnlinkFuzz, P1's 11 configurations      | 0 failures                                    |
| UnlinkFuzz, 6 draining configurations   | 0 failures, 20 rounds each                    |
| A2A3Check2, P1's 5 configurations       | all rules hold                                |
| A2A3Check2, 4 draining configurations   | all rules hold; roots taken back 2 to 69      |
| trace checker, 21 draining traces       | 21 TRACECHECK OK at `0e66d1c9`                |
| the same, at `5466e153`                 | 4 fail C-H (eviction): fault 3 of section 5   |
| trace checker, e-mixed, P1's `0f16daae` | C-H fails in seed 3 (37 of 61): P1's fault    |

Draining configurations: 25 to 200 keys, 60 to 70 % deletes, node sizes 8
and 14, long keys, transactions of up to 60 keys (in the two with long keys,
2 and 4 of the roots taken back are segment roots); for the traces also
reclaim (retain 1), eviction (rune=random) with reads and restarts. Scripts
in `/Users/f/fl/bench/2026-11-10/p4/runs/` (`fuzz.sh`, `fuzz2.sh`,
`a2a3.sh`, `traces.sh`, `traces-e2.sh`).


## 3. Measurements

All counts from 023-03's `CleanupRule`, on frozen builds of P4 and of P1's
`0f16daae`, run the same day; `main`'s from 023-03, section 8 (as P1's
report gives them); P2's from its report (P2, section 4). Runs:
`/Users/f/fl/bench/2026-11-10/p4/runs/` (`t1b-*.txt`, `t3s-*.txt`,
`t4-*.txt`, `t1m-*.txt`; the builds `b-v4`, the head, and `b-p1`).

### 3.1 T1, "after", against the twin

| Measure                | Twin  | Main 1k | P1 1k | P4 1k | Main 100k | P1 100k | P4 100k |
|---|---|---|---|---|---|---|---|
| M1, MB, most in window | 2.13  | 2.26    | 2.15  | 2.14  | 40.42     | 2.25    | 2.19    |
| M3, ms                 | 1,039 | 1,221   | 1,219 | 1,221 | 5,951     | 1,141   | 1,144   |
| M4, reachable          | 6     | 84      | 6     | 6     | 7,902     | 6       | 6       |
| M5, dead klongs        | 35    | 1,047   | 29    | 32    | 102,918   | 60      | 56      |
| M6, get                | 1     | 1       | 1     | 1     | 1         | 1       | 1       |
| M8, D, most in window  | 79    | 166     | 88    | 90    | 26        | 106     | 107     |
| M9, bytes              | 2,840 | 25,968  | 3,120 | 2,856 | 1,729,720 | 2,872   | 3,488   |
| M10, touch visited     | 7     | 85      | 7     | 7     | 7,320     | 7       | 7       |
| M11, after the probe   | 85    | 156     | 101   | 102   | 7,927     | 106     | 99      |

P1's columns are from runs of `0f16daae` the same day, a little apart from
P1's report (`e60f6c82`). P2 at 100,000: M1 2.12, M4 6, M5 59, M8 95, M11
101. N = 1,000,000 is in 3.6.

### 3.2 T2, the matrix, by 023-03's criteria

`judge.py` (P1's) on the 18 rows of T1: C1 to C3 and C5 to C10 with the
bounded allowance (a_n = 10 + 4 h_fill), and with the strict one (a_n =
10, and C4). `main` fails every row (023-03, 8.2).

| Row                 | M4, P1 | M4, P4 | Bounded, P1 | Bounded, P4 | Strict, P4 |
|---|---|---|---|---|---|
| 1k after, asc       | 6      | 6      | pass        | pass        | C6 C9      |
| 1k before           | 6      | 6      | pass        | pass        | pass       |
| 1k around           | 6      | 6      | pass        | pass        | C9         |
| 1k inter            | 10     | 10     | pass        | pass        | C4         |
| 1k hashed, random   | 8      | 6      | pass        | pass        | pass       |
| 1k after, desc      | 6      | 6      | C9          | C9          | C6 C9      |
| 1k after, random    | 6      | 6      | pass        | pass        | pass       |
| 1k after, 3 vers.   | 6      | 6      | pass        | pass        | C6 C9      |
| 100k after, asc     | 6      | 6      | pass        | pass        | C6 C9      |
| 100k before         | 6      | 6      | pass        | pass        | C6 C9      |
| 100k around         | 6      | 6      | pass        | pass        | C6 C9      |
| 100k inter          | 14     | 14     | pass        | pass        | C4         |
| 100k hashed, random | 9      | 6      | pass        | pass        | C9         |
| 100k after, desc    | 6      | 6      | pass        | pass        | C6 C9      |
| 100k after, random  | 6      | 6      | C6          | pass        | C4 C6 C9   |
| 100k after, 3 vers. | 6      | 6      | pass        | pass        | C6 C9      |
| long 1k             | 6      | 6      | pass        | pass        | pass       |
| long 10k            | 6      | 6      | pass        | pass        | C9         |

P4 passes 17 of 18 rows bounded (P1 16); the one miss, 1,000 descending,
is P1's too: 118 objects after the probe against 85 + 26. Strict fails
mostly on D and the start's objects (C6, C9), by 3 to 33, as P1 and P2;
"inter" keeps the live key's chain of single children below the root (M4
10 and 14; the twin 6), as RC takes roots only.

### 3.3 T3, single scans right after the deletes, R forever

| Shape            | Main, M4 | P1, M4 | P4, M4 | P4, get |
|---|---|---|---|---|
| after            | 7,897    | 1      | 1      | 1       |
| before           | 7,897    | 1      | 1      | 1       |
| around           | 8,039    | 1      | 1      | 1       |
| inter            | 7,896    | 1      | 1      | 1       |
| long, N = 10,000 | 60,787   | 1      | 1      | 1       |
| hashed, random   | 112,759  | 1      | 1      | 1       |

N = 100,000 (long: 10,000). The twin: 1. P4's first build, without RC's
take-back, left "hashed" at 4 (3 levels of single children above the
leaf, 1.3). P2: "inter" 5, "hashed" 4 (no RC).

### 3.4 T4, the queue

| Keys, transactions  | M4, main | M4, P4 | Head | M3, s | M1, MB | Cuts  | M9, kB |
|---|---|---|---|---|---|---|---|
| ordered, 100,000    | 11,147   | 117    | 4    | 1.26  | 1.48   | 165   | 22.7   |
| ordered, 1,000,000  | 111,434  | 117    | 4    | 1.38  | 1.49   | 1,695 | 22.2   |
| hashed, 100,000     | 112,782  | 2,134  | 5    | 1.23  | 3.54   | 211   | 19.0   |

At the last checkpoint. P1's runs of `0f16daae` give the same stream,
byte for byte (595,703,808 bytes at 1M, 162,915,712 hashed), and the same
counts: in a queue of 1,000 live keys the tree has two inner levels, so an
emptied leftmost child's parent is always above leaves, and P1's relabel
changes no node off the path either (P1's counter: 0). The relabel's klong
c and LE-b's klong 0 have the same size. `main`'s from P1's report: 78.2 s
and 53.2 MB at 100,000; 893.1 s and 557.1 MB at 1M. P2 (its 4.4): M4 117,
head 4, 1.22 s and 1.34 MB at 100,000, 1.04 s and 1.29 MB at 1M; hashed
2,134, 5, 1.23 s and 3.54 MB, as P4.

### 3.5 What the deletes write and hold, and the cost of the leftmost child

The delete phase of T3 (R forever, no reclaim, no drive): the stream it
adds, and the objects resident after it (`noEvict()`, the test setup).

| Shape, N         | Main, bytes | P1, bytes  | P4, bytes  | P4/main | P4/P1 |
|---|---|---|---|---|---|
| after, 100,000   | 6,778,848   | 5,036,136  | 4,819,920  | 0.71    | 0.957 |
| around, 100,000  | 6,886,568   | 5,792,288  | 5,457,496  | 0.79    | 0.942 |
| inter, 100,000   | 5,963,400   | 4,322,152  | 4,110,216  | 0.69    | 0.951 |
| long, 10,000     | 6,367,392   | 1,018,784  | 1,000,832  | 0.16    | 0.982 |
| hashed, 100,000  | 108,958,784 | 96,573,416 | 96,573,208 | 0.89    | 1.000 |
| after, 1,000,000 | 68,203,168  | 50,742,416 | 48,496,008 | 0.71    | 0.956 |

| Shape, N         | Objects, main | P1      | P4      | P4/main |
|---|---|---|---|---|
| after, 100,000   | 9,592         | 10,297  | 9,600   | 1.001   |
| around, 100,000  | 10,800        | 11,578  | 10,814  | 1.001   |
| inter, 100,000   | 9,597         | 10,305  | 9,607   | 1.001   |
| long, 10,000     | 60,952        | 61,027  | 60,960  | 1.000   |
| hashed, 100,000  | 117,507       | 126,524 | 126,515 | 1.077   |
| after, 1,000,000 | 95,987        | 102,998 | 96,000  | 1.000   |

P2's bytes (its report, 4.3): after 4.74 MB, around 5.30, inter 4.03,
hashed 97.97, long 0.99: about 2 % below P4's in "after", as LE-c writes no
klong for the leftmost child. The independent prototype of 023-04 (path
copying, Codex's study, 10.2) wrote 1.8 to 2.0 times `main`'s bytes and
held 2.8 to 2.9 times its cache objects at 1M; P4 writes 0.71 and holds
1.00.

With eviction at a budget of 1 MB (T1, "after", N = 100,000, R = 1 s),
both write the same stream as without it; after the deletes P4 holds 377
objects (P1 524) and has loaded 547,213 versions (P1 555,215).

The leftmost child, counted by the Dag's counters (`statRelabels`,
`statRelabelNodes`, `statTakenBack`) in the same runs:

| Shape, N         | Leftmost, P1 | Leftmost, P4 | P1, off path | P1, taken back | P4, taken back |
|---|---|---|---|---|---|
| after, 100,000   | 7,321        | 7,335        | 704          | 209            | 6              |
| around, 100,000  | 7,362        | 7,406        | 768          | 4              | 0              |
| inter, 100,000   | 7,324        | 7,346        | 669          | 204            | 0              |
| long, 10,000     | 776          | 769          | 70           | 27             | 6              |
| hashed, 100,000  | 2,374        | 2,374        | 58           | 20             | 10             |
| after, 1,000,000 | 72,106       | 72,128       | 6,999        | 2,009          | 6              |

"Leftmost": emptied leftmost children; P4 changes no node off the path.
The counters run over the fill too, where nothing is unlinked. So P1's relabel changes about one node off the path
for ten emptied leftmost children, and its time splits of full inner
nodes make about three nodes that the same batch empties and takes back.
Against P1, P4 saves about 30 bytes of the stream per emptied leftmost
child (216 kB for 7,321 at 100,000; 2.25 MB for 72,106 at 1M), about 310
bytes per node P1 changes off the path, and the 7 % of objects P1 holds
more than `main` (the relabel's split nodes, kept with `noEvict()`).
LE-b's own cost per emptied leftmost child: one klong (16 bytes in the
stored node) in a node that the delete writes anyway, or none when the
klong of 0 is of the transaction already.

### 3.6 T1 at N = 1,000,000

A drive of 12,000 (the fixed 4,000 is too short for every prototype, as
reclaim's iteration over the deletes scans the 1M keys live at its start;
P1, section 5). Same-day runs of the same command on both builds:

| Measure, after the drive | Twin  | P1, `0f16daae` | P4    |
|---|---|---|---|
| M1, MB, most in window   | 2.19  | 2.21           | 2.81  |
| M3, ms                   | 1,039 | 1,224          | 1,232 |
| M4, reachable            | 6     | 6              | 6     |
| M5, dead klongs          | 23    | 40             | 48    |
| M8, D, most in window    | 94    | 91             | 178   |
| M9, bytes                | 3,480 | 3,184          | 3,752 |
| M11, after the probe     | 83    | 100            | 184   |

The tree is the twin's in both. P4's D is 160 to 178 from drive 3,000 on,
and stays so to drive 30,000 (155 to 167); P1's falls from about 250
(drive 2,500, both) to 58 to 81. With other histories it is the other way
round: with batches of 99 keys instead of 100, P1's D is 213 to 236 (237
objects after the start) and P4's 165 to 179 (183); with values of 101
bytes, P4's is 153 to 164 (160). Section 5, limit 1, has what D holds.


## 4. Requirements and tests met

023-02, as P1's report gives them (P1, section 4), with these changes:

* R1, R16 (lookups at every available time, readers): by design (1.5) and
  by every check run; LE-b changes no reader.
* R3, R5: as P1 for nodes; "hashed" now at the twin's (3.2, 3.3).
* R10 (gets): T1's "after" and "hashed" 1 node as the twin; "inter" 3 at
  1,000 and 5 at 100,000, as P1.
* R11 (puts and deletes): O(H) nodes on the path; no node off it; records
  of at most 23 kB in T4 (`main` 20 MB).
* R14 (memory): the objects after the deletes as `main`'s (3.5); D and the
  start's objects within the bounded allowance at 1,000 and 100,000 but
  one row; at 1M not, with the run of dirty top nodes (section 5).
* R17, R18: `level1.sh` (RestartStress, RestartInvariance); `level2.sh` in
  section 2.
* R22, R23: format 6, as P1.
* R24 (Lean): A2A3Check2 with P1's taken-back change and the trace checker
  accept LE-b and the root take-back with the model unchanged; the C port
  (R25) does not follow.
* R27: StreamDigest's digests change (format 6, and other bytes): not run.

023-03: T1 bounded in 17 of 18 rows at 1,000 and 100,000, and at 1M not
(C6, C9: D 178 and 184 objects against 94 + 38 and 83 + 38); T3's single scans at the twin's in
every shape; T4 ordered and hashed at P1's; T6 found nothing (every
CleanupRule run checks lookups at the latest time and within R). T7, T8
through the level scripts; T10 and T11 not run.


## 5. Faults and limits found

Found and fixed here:

1. **The split's inserted klong** (1.1). A space split of an inner node
   that inserts a klong for the child of the second half's first klong
   must give it the empty key too. Found by a mutation of the rule with
   UnlinkFuzz's random shape before any run of the real code.
2. **RC stopped at a root made by the transaction** (1.3): "hashed" kept
   three levels of single children. P1's limit; P4 takes such a root back.
3. **A taken-back node stayed in the node table** (1.3): the trace
   checker's C-H failed with eviction. P1's fault (it fails conformance's
   own `e-mixed` seed 3); P2 found and fixed the same.

Limits:

* **D and the start's objects at 1M** (3.6): 166 to 178 against the twin's
  94 and P1's 91, so the restart loads 184 objects against 83. D is the
  newest top nodes, 158 to 165 of them with consecutive ids, and 13 to 18
  old leaves; no reachable key node but the twin's. A probe that follows
  the dirty pointers from the oldest dirty top node finds none dirty below
  it: it was written while its predecessor was dirty and stays dirty by
  Rule A through its skip pointer, and each newer one through its
  predecessor. The run forms while reclaim catches up after the deletes
  (D about 250 at drive 2,500 in P1 and P4), and then keeps its length in
  P4 and shrinks in P1. P1's own `e60f6c82` had such a run too (D 148,
  P1's Q4, cause not found), its `0f16daae` not, but with batches of 99
  keys (D 236, 3.6): the length depends on the history, not on LE-b or the
  tree, whose shape is the twin's in all of them. Not explained here; a
  question of the still-dirty test on top nodes, for phase 2 (Q4).
* **Single children below the root** ("inter": 14 reachable at 100,000,
  the twin 6): RC takes roots only, as in P1 and P2. Strict needs a merge
  or reclaim's rebuild (023-04, X3).
* **Dead klongs in live nodes** (M5): the shadowed klongs of 0 are dead
  klongs of their node until its next time split, as a time split's
  shadowed klong is.
* **The empty key in a node is not tight.** A get or put that a node's
  empty key routes follows the child as before; no reader uses the first
  klong of a node as its own bound (1.5). A future reader that wants a
  node's lower bound from its own klongs, not its parent's, would get 0.
* **`dirtyNodeBound`** keeps P1's count for a delete, with the off-path
  node it no longer needs; not checked against counted nodes.
* **T1 at 1M** needs a longer drive, as for P1 and P2 (reclaim's iteration
  that spans the deletes); see 3.6.
* **The C port** does not follow: about P1's 400 lines less the relabel,
  plus the split rule (a few lines in `firstAndSecond`).


## 6. What is left for a production version

* The split rule in the Lean model's words, if the model ever gets keys;
  today it has none (1.5).
* A unit test in KeyNodeTester for `firstAndSecond` of an inner node (the
  empty key, and the inserted klong of the same compare value), and
  DagTester cases for LE-b in place, LE-b of a full node, and RC's take-back
  of a space root and of a segment root.
* UnlinkFuzz and the draining A2A3Check2 and trace configurations in the
  level scripts.
* P1's list (P1, section 6) but the relabel's items: the follow without
  marking, `dirtyNodeBound` against counted nodes, the static counters.
* The digests of StreamDigest, with format 6, for Frans's approval.


## 7. Questions for Frans

* **Q1. LE-b or LE-a.** Both change no reader. LE-b changes one rule of
  the space split (second halves of inner nodes start with the empty key)
  and writes 2 to 6 % fewer bytes in the deletes, no node off the path, and
  holds `main`'s objects; LE-a keeps the split as it is. Take LE-b?
* **Q2. RC's take-back** of a root made by a split of the transaction
  (1.3): keep it, as it closes "hashed" to the twin's shape?
* **Q3.** P1's questions Q1 (A2A3Check2 counts a taken-back node as not
  made) and Q2 (the take-back's form) apply to P4 as well.
* **Q4. The run of dirty top nodes** (section 5): at 1M, P4 keeps about 160
  dirty top nodes after convergence, P1's `0f16daae` about 70, P1's
  `e60f6c82` about 150, with the same tree. Investigate the still-dirty
  test on top nodes (Rule A through skip pointers) before comparing the
  prototypes on M8 and M11 at 1M?


## 8. State

2026-11-10, 13:06. Done for this session. Clone
`/Users/f/fl/bench/2026-11-10/p4/clone`, branch `023-p4-empty-key`, head
`0e66d1c9`: `aeb364ce` LE-b, `5466e153` RC's take-back of a root made by
the transaction, `0e66d1c9` the node-table drop of taken-back nodes; on
P1's `0f16daae` (fetched 11:55; P1's branch may have moved since). A
worktree of `0f16daae` for reference builds: `/Users/f/fl/bench/2026-11-10/p4/p1ref`.
Frozen builds in `/Users/f/fl/bench/2026-11-10/p4/runs/`: `b-v4` (the head),
`b-v3` (`5466e153`), `b-v1` (`aeb364ce`), `b-p1` (P1's `0f16daae`); the
runs' outputs and scripts there (`t1b.sh`, `t3s.sh`, `t4s.sh`, `t1m.sh`,
`t1m-var.sh`, `fuzz.sh`, `fuzz2.sh`, `a2a3.sh`, `a2a3d.sh`, `traces.sh`,
`traces-e2.sh`, P1's `judge.py`). Probes (`P4Stats`, `P4Tree`, `P4Wrap`,
the dirty-chain dump, a copy of P1's D dump) in
`/Users/f/fl/bench/2026-11-10/p4/probe/`. Open: Q4, the run of dirty top
nodes at 1M; the unit tests of section 6.
