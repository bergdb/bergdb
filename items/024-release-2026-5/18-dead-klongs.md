# 024-18. Dead klongs in live nodes: their cost and three options, measured

Created 2026-11-11 by Frans Lundberg. Status: done (2026-11-11): QD1
decided, option 2 with theta 7 (Frans, 14:27), made in 024-23; QD2 to
QD5 not answered (024-28, section 8).

A study for Frans's decision on dead klongs in live key nodes (024-05,
ST4; 024-11, U5 and QU3): what a dead klong is and costs, from the code;
how many there are, counted on `main` and on 024-14's measuring build
with merges, under five workloads; and the three options, each with its
price in numbers. Probes and a measuring prototype on a branch that is
not landed; no product code.

Frans, 2026-11-11, 11:24, when asked to accept 024-11's allowance: "This
is important. I need to understand this better. We need to. Perhaps with
measurements. Let's call the options 1, 2, and 3. I like the idea of 3,
that reclaim will rewrite nodes so the cost goes to zero eventually. I
don't understand the cost of this option fully. Option 2 is also
interesting as a trade-off. With 2, I suppose the reclaim would
automatically reduce this cost to some extent. By the way, the node size
of 30 is open for discussion. And should it even be a fixed constant? And
should an index node be stored more compact in the stream? Big
questions. But these are important now when we want to settle the
algos. Solid algorithms are the aim."

The options, by his numbers:

1. **The allowance**: nothing beyond merges (024-11, MG); the bound
   named: at most B dead klongs a node, on nodes in proportion to the
   live keys (024-11, BU1 and BU3).
2. **Compaction at the write** (024-11's CW, 023-04's DC): a node with
   theta or more dead klongs counts as full and is replaced by its last
   version at the next write to it.
3. **Compaction by reclaim** (024-11's CT): reclaim rewrites the nodes
   that hold dead klongs, so that the cost goes to zero within an
   iteration, cold nodes too.

Names: B the node size (30), live and dead as in 024-11, section 2.1;
"the history" of a node is all its klongs but its live KEY klongs and
one time klong: its dead KEY klongs, its other time klongs and its delete
bitmaps. Cite as "024-18, section 3" and the questions as "024-18, QD1".


## 1. Summary

Kept current; written 13:13. Frans decided at 11:55 (through the
coordinator) to build merges on `main` now with option 1 "for now"
(024-21, agent "mgj"); this study then decides between 1, 2 and 3.
Measured at 100,000 and 1M keys on `main`, on 024-14's merges build,
and (from 12:53) on 024-21's merges on `main` (section 6.2); not at 10M
(no slot).

* **A dead klong costs 16 bytes each time its node is written**, 24
  bytes of heap while the node is resident, and one more klong for every
  lookup that passes the node. It goes only when its node is replaced:
  rule O (the node full), a merge, an unlink (section 2). **Time klongs
  cost as much**: under random overwrites a leaf holds 10.0 live, 4.7
  dead and 5.4 time klongs, 354 bytes a write against 208 for its last
  version.
* **Counted at 1M keys** (section 3): every shape that writes holds 0.4
  to 0.5 dead klongs a live one, on `main` and with merges, with R
  finite or forever (and for B = 14, 30 and 62 in "over"); a queue
  none. **The worst is a cold database with R finite**: 0.83 on `main`
  and on 024-21, 0.69 on 024-14's m8 (h = 17), all
  of them reclaim's own rewrites, which visit each cold leaf every second
  iteration. With merges a deleted key's klong goes within about two
  such visits; with R forever a cold node keeps what it has.
* **Frans's supposition about option 2 holds, down to theta**: reclaim's
  rewrites are writes, so with option 2 each cold leaf is compacted at
  reclaim's next visit and keeps fewer than theta dead klongs (inner
  nodes likewise, through their children's compactions); nothing
  without a retain duration. Its price comes from replacing nodes that
  are dirty (hot leaves, and inner nodes that a step just changed): theta 7
  0.30 to 0.35 dead a live klong for -3 % to +6 % stream bytes; theta 3
  0.11 to 0.13 for +28 % to +46 %; theta 1 two to three times (4.2, 6.1).
* **Option 3 as stated (3a)** replaces 90 to 95 % of all nodes every
  iteration: 3 to 8 % of an iteration's bytes as last versions, plus a
  walk, a range in the step's record and the touch as a writer. **Its
  variant 3b**, reclaim's own writes leave their nodes as last versions,
  reaches zero but costs +51 % to +134 % bytes, because it replaces nodes
  that are dirty and Rule A writes their left-out versions again.
  **Variant 3c**, the same for nodes not changed since the iteration
  began, costs +0 to +3 %, and takes "cold" from 0.83 to 0.14 (leaves
  0.09; inner nodes keep up to B) (section 5).
* **On 024-21's build** (merges on `main`) the same holds: in
  "sparsecold" 0.85 dead klongs a live one with merges alone, 0.16 with
  3c for +0.3 % bytes, 0.36 with theta 7 for +7 % (6.2).
* **Recommended: 3c with merges, option 1 for the rest; option 2 not
  now** (6.4). Both are written as patches on `main` for 024-21's branch
  (`024-18-option2-main`, `024-18-3c-main`). Questions QD1 to QD5.


## 2. A dead klong, from the code

`main` at `558cdfe3`: `Dag`, `KeyNode`, `Klong`, `StoredKeyNode`,
`Reclaim`, `Eviction`. 024-14's build with merges (`Dag.merge` on
`024-14-thresholds`) for the events of a merge.

### 2.1 The node

A key node is three arrays of up to B entries in time order (`KeyNode`:
`klongs`, `pointers`, `pos`). A klong is a time klong T(t), a KEY klong
K(e, p) with up to 7 key bytes e and a pointer p (a value or a child),
or a delete bitmap D(bits) of the klongs it deletes (`Klong`). A writer
only appends: a put adds K, preceded by T(tt) if the node has no klong of
tt yet; a delete sets bits in the transaction's D (one a node a
transaction, changed in place), again after T(tt). A K klong is
**shadowed** when a later K of the same compare value follows it, and
**deleted** when the last D has its bit: either way it is **dead**,
invisible at every time from the later klong on, and kept for lookups at
earlier times.

### 2.2 What makes one

| ID | Event                                   | In                 | Dead klongs made           |
|---|---|---|---|
| E1 | a put of a live key (an overwrite)      | its segment leaf   | 1 (shadowed), and T(tt)    |
| E2 | a delete of a live key                  | its segment leaf   | 1 (deleted), D and T(tt)   |
| E3 | reclaim's rewrite of a value            | its segment leaf   | 1 (shadowed), as E1        |
| E4 | a child replaced by a time split        | the parent         | 1 (the old klong shadowed) |
| E5 | a child space split                     | the parent         | 1, and a new K klong       |
| E6 | a later key of tt in a node made in tt  | that node          | 1 a key (see below)        |
| E7 | an unlink, a climb, a relabel (format 6) | the parent        | 1 or 2                     |
| E8 | a merge (MG; 024-14's build)            | the parent         | 1 or 2                     |
| E9 | a root collapse                         | the segment leaf   | 1 (shadowed)               |

* **E1 and E3 are the same code**: a step's rewrite is a put of the same
  key and value in an internal transaction (`Reclaim.step`). So every
  value reclaim rewrites leaves one dead klong in its leaf, until the
  leaf is next replaced.
* **E4 and E5** put dead klongs in inner nodes, and in segment leaves
  that hold segment roots, at every replacement of a child: so a hot
  path's inner nodes collect them as fast as its leaves.
* **E6, a split inside a transaction.** A node made by tt (a last version
  or a half) holds every live klong as a klong of tt, after T(tt). A
  later put of tt to another key of the node appends a K klong that
  shadows the copied one: a dead klong in a node that is not yet
  written. `KeyNode.replaceKlong` replaces such a klong in place, but
  only the klong being inserted at the split (`Dag.timeSplit`), not the
  later ones. A user's transaction of 100 random keys rarely puts two
  keys of one leaf; a reclaim step rewrites about 130 neighbouring keys,
  so about 11 to 13 a leaf.
* **E7 and E8.** A delete that empties a node deletes the parent's klong
  (`deleteUpward`, `emptyKeyNext`); a merge points eL to the new node
  (a shadow) and removes or renames eR (024-11, section 5.3, M4).
* **A split of the node itself makes none**: rule O replaces the node by
  its last version, T(tt) and the live klongs, or by two halves of them.

### 2.3 When one goes today

Only when its node is replaced, and the replacement is reachable at tt:

* **Rule O** (`Dag.handleFullNode`): when a write needs more room than
  the node has. The room counts every klong, live, dead, T and D
  (`node.size + 1 < maxNodeSize`): so the history fills a node and makes
  its own end, and a node with many live klongs fills sooner.
* **A merge** (024-11, MG): the node merged is replaced by one with live
  klongs only. **An unlink**: the node is left out whole.
* Nothing else. Reclaim's touch makes dirty, it does not compact (024-07:
  since today only the paths of the step's own puts). Eviction unloads a
  node as it is. A start rebuilds nothing.

So a node that gets no write keeps its dead klongs for good: with R
forever, a cold node keeps them as long as the database lives (a delete
entry after 700 cuts; 023-08, section 3). With R finite a cold leaf is
written by reclaim (E3) every second iteration (section 3.3), so its
deleted keys' klongs go at its next split, a bounded number of
iterations later, and reclaim's own shadows take their place.

### 2.4 What one costs

* **Stream: 16 bytes each time its node is written** (`StoredKeyNode`:
  32 bytes a node and 8 a klong and 8 its reference; a T or D klong costs
  16 too, its reference unused). A node is written whole whenever it is
  dirty at a take: its own writes, its children's (Rule A), reclaim's
  rewrites below it. The stream kept, with R finite, holds R's records
  and one or two iteration spans of such writes.
* **Heap: 24 bytes a klong of the arrays' capacity** while the node is
  resident (`KeyNode.getMemSize`: 80 + 24 a slot; capacities 2, 6, 14,
  30, 62). A leaf of 10 live keys in its last version has 14 slots, 416
  bytes; the same leaf with its history passes 14 klongs and gets 30
  slots, 800 bytes. And a dead klong's pointer may still hold what it
  named: the old value, or the old child's handle. With an eviction
  budget the old value goes when a sweep or the dead hand unswizzles it
  (`Eviction.deadStep`, after a cut); with `noEvict()` when the node is
  replaced.
* **Reads: one more klong to examine**, at every node a lookup passes:
  `searchEq` and `searchLte` read every klong up to the lookup time, live
  or not, and a get at the latest time reads the whole node. A scan's
  cost per node follows the node's size in the same way.
* **A later put** writes the node again with its history: a leaf of
  20.1 klongs is 354 bytes, its last version 208 (section 3.2).

The klongs that are not live are not only the dead KEY klongs. In the
measurements a node holds about as many time klongs as dead ones (one a
transaction that wrote it); the last version keeps one. Options 2 and 3
remove both together.


## 3. Today's state, measured

### 3.1 Method

The probe `DK` (`18-dead-klongs/DK.java`), a variant of 024-14's `THR`:
the same setup (024-03's PF1: a `FileStream` with the builder's defaults,
startup distance 50 MB, a test clock of 1 ms a transaction, keys
`/k/%010d`, values of 100 bytes, 100 distinct keys a transaction), and a
**census**: every key node that a scan of `/k/` reaches at the latest
time, read with the maintenance follower, counted for leaves (segment
leaves) and inner nodes apart: klongs of each kind, live and dead
(deleted or shadowed), the bytes a write of the node stores, the heap of
its arrays, a histogram of dead klongs a node, and option 3's set
(section 5). A census after the fill, every 5,000 or 20,000
transactions, and at the end of each reclaim iteration.

The workloads, 1M keys:

* **over**: a random fill, then transactions of 100 overwrites of random
  keys (the steady state; 024-03's drive).
* **sparse**: a fill in key order, every key but each 10th deleted in a
  fixed random order (024-14's k10-hashed), then overwrites of random
  live keys.
* **sparsecold**: sparse's fill and deletes, then overwrites of the live
  keys of the first 1 % of the key space only: Frans's cold nodes after
  deletes.
* **cold**: a random fill, then overwrites of the first 1 % of the keys
  only: the rest is never written again.
* **fifo**: a queue: a fill in key order, then transactions of 50
  deletes of the oldest keys and 50 puts of new keys at the end.

Each with R = 1 s (1,000 transactions; "r1") and with R forever ("r0":
reclaim off). Builds: `main` (`558cdfe3`, built as it is); 024-14's
frozen build `b1` with merges (P5's merge with fault 12's fix,
`024-14-thresholds` at `bff5e810`) with its recommended set m8, 8/17/17;
and the prototypes of sections 4 and 5, on `main` and on `b1` (State
lists the branches). Section 3 runs 20,000 transactions after the shape,
sections 4 to 6 60,000 (4 to 18 iterations). Counts only, one JVM a
run, no slot; exact and repeatable. The probe's last version ends a run
with a check of every live key's value by a scan (runs in `out/verify`:
`main`, 3c, theta 1 and 3, every shape, all pass). Outputs in
`/Users/f/fl/bench/2026-11-11/dead/out/`, summarized by
`tools/summ.py`.

### 3.2 `main` at 1M keys

At the end of 20,000 transactions after the shape (a census at
transaction 20,000; leaves, then inner nodes). "d/l" is dead klongs a
live klong; "stored" the bytes of one write of every node, against the
same nodes as their last versions; heap the arrays, against the last
versions'.

| Shape, R | Nodes   | Live klongs | Dead    | d/l  | T       | Stored MB   | Heap MB     |
|---|---|---|---|---|---|---|---|
| over r1  | 100,170 | 1,000,007   | 471,451 | 0.47 | 542,977 | 35.4 / 20.8 | 71.9 / 44.5 |
| inner    | 11,241  | 111,406     | 53,149  | 0.48 | 62,093  | 4.0 / 2.3   | 8.0 / 5.0   |
| over r0  | 99,967  | 1,000,001   | 458,015 | 0.46 | 553,926 | 35.4 / 20.8 | 71.7 / 44.4 |
| inner    | 11,193  | 111,158     | 53,399  | 0.48 | 63,445  | 4.0 / 2.3   | 8.1 / 5.0   |
| sparse r1 | 72,004 | 100,007     | 499,338 | 4.99 | 571,194 | 21.0 / 5.1  | 42.5 / 11.9 |
| inner    | 6,994   | 78,993      | 27,983  | 0.35 | 34,958  | 2.5 / 1.6   | 5.1 / 2.9   |
| sparse r0 | 72,001 | 100,001     | 515,703 | 5.16 | 587,585 | 21.6 / 5.1  | 43.5 / 11.9 |
| inner    | 6,994   | 78,993      | 33,544  | 0.42 | 40,512  | 2.7 / 1.6   | 5.0 / 2.9   |
| cold r0  | 73,772  | 1,000,001   | 4,752   | 0.00 | 328,893 | 23.7 / 19.5 | 49.2 / 43.5 |
| inner    | 7,071   | 80,841      | 20,764  | 0.26 | 24,721  | 2.2 / 1.6   | 4.7 / 3.6   |
| fifo r1  | 72,731  | 1,000,007   | 33      | 0.00 | 72,762  | 19.5 / 19.5 | 51.2 / 51.2 |
| inner    | 7,709   | 80,435      | 17      | 0.00 | 7,721   | 1.7 / 1.7   | 3.2 / 3.2   |

* **Random overwrites: half a dead klong a live one**, in leaves and
  inner nodes alike, with R finite or forever: the steady state of rule
  O. A leaf fills to 30 klongs and is replaced by its last version of
  about 11; on average it holds 4.7 dead and 5.4 time klongs. The
  histogram is wide: 10 % of leaves with none, 13 % with 9 to 16.
* **A queue makes none**: the deletes empty whole leaves at the head,
  which are unlinked; the puts fill new leaves at the tail.
* **A cold database after a random fill** has dead klongs in its inner
  nodes only (E4, E5 of the fill: 0.26 a live klong), and with R forever
  6,123 of the 6,215 inner nodes that hold one were not written in the
  last 5,000 transactions: they keep them for good. Its leaves have
  none (a random fill only inserts) but 4.4 time klongs each.
* **Scattered deletes without merges**: 5 dead klongs a live key in the
  leaves, which hold 1.4 live keys each (72,004 leaves for 100,007 keys;
  024-14's twin has about 8,000): 75 % of the leaves' stored bytes are
  history. This is underfill and dead klongs together; with merges
  (section 3.4) the leaves are few, and their dead klongs are bounded by
  B a node on them.

### 3.3 Reclaim's visits of cold leaves

With R finite, reclaim rewrites each live value stored before pCut, the
pStart of the iteration before (`Reclaim`, class comment). A value it
rewrote in iteration i is stored after pStart(i), so iteration i + 1 does
not rewrite it and iteration i + 2 does: **a cold leaf gets reclaim's
writes every second iteration**, all its live values at once. Seen in
"cold r1" on `main`: the leaves' dead klongs stay at 320,000 from the end
of iteration 1 to the end of iteration 2 (a census every 5,000
transactions), and rise to 431,000 while iteration 3 rewrites the fill's
values. At the end of iteration 2, 60,544 of the 61,479 leaves with a
dead klong and 7,140 of 7,242 such inner nodes had not been written in
the 5,000 transactions before.

### 3.4 With merges (024-14's m8)

The same table on 024-14's build with m8 (8/17/17), at transaction
20,000 of the phase. Its put path keeps fuller nodes (h = 17), so the
nodes are fewer than `main`'s in every shape.

| Shape, R  | Nodes  | Live klongs | Dead    | d/l  | T       | Stored MB   | Heap MB     |
|---|---|---|---|---|---|---|---|
| over r1   | 88,185 | 1,000,007   | 391,961 | 0.39 | 454,076 | 32.4 / 20.2 | 65.3 / 44.0 |
| inner     | 8,553  | 96,733      | 37,704  | 0.39 | 44,906  | 3.1 / 2.0   | 6.3 / 4.3   |
| over r0   | 88,164 | 1,000,001   | 377,703 | 0.38 | 465,004 | 32.3 / 20.2 | 65.2 / 44.0 |
| sparse r1 | 9,178  | 100,007     | 40,715  | 0.41 | 49,690  | 3.3 / 2.0   | 6.8 / 4.5   |
| inner     | 925    | 10,098      | 4,152   | 0.41 | 5,049   | 0.3 / 0.2   | 0.7 / 0.4   |
| cold r0   | 73,645 | 1,000,001   | 3,816   | 0.00 | 327,857 | 23.7 / 19.5 | 49.1 / 43.5 |
| inner     | 5,822  | 79,465      | 15,826  | 0.20 | 19,465  | 2.0 / 1.6   | 4.1 / 3.5   |
| cold r1   | 82,110 | 1,000,007   | 413,714 | 0.41 | 231,081 | 28.9 / 19.9 | 60.9 / 43.8 |
| inner     | 6,932  | 89,037      | 26,231  | 0.29 | 21,453  | 2.4 / 1.8   | 5.0 / 3.9   |
| fifo r1   | 72,731 | 1,000,007   | 29      | 0.00 | 72,759  | 19.5 / 19.5 | 51.2 / 51.2 |

* **Merges change the count, not the rate.** After the scattered
  deletes 9,178 leaves for 100,007 keys (`main`: 72,004), and 0.41 dead
  klongs a live one, as under plain overwrites: the dead klongs are now
  in proportion to the live keys (024-11, BU3), at about 0.4 a live
  klong in the steady state of every shape that writes.
* **The deleted keys' klongs go** where the drive writes: 23,823 right
  after the deletes, 188 one iteration later, none after two. What stays
  is the overwrites' shadows, at the steady state's rate.
* **A cold database with R finite** (cold r1) holds as many dead klongs
  as a hot one: reclaim's rewrites (E3) shadow a klong for each value of
  each cold leaf every second iteration (section 3.3), and they are what
  the 413,714 are. With R forever (cold r0) the leaves keep none and the
  inner nodes keep the fill's 0.20 a live klong, for good.

### 3.5 Frans's cold node: deleted, then never written

"sparsecold" on `main`, R = 1 s, 60,000 transactions after the deletes,
12 iterations: the leaves' klongs deleted by the user's deletes (the
"deleted" part of the dead), at the end of each iteration that rewrote
the cold values:

| Iteration end                 | 2       | 3       | 5       | 7       | 9       | 11      |
|---|---|---|---|---|---|---|
| deleted klongs in leaves      | 383,665 | 336,244 | 317,034 | 275,088 | 224,804 | 141,557 |
| all dead klongs in leaves     | 419,543 | 461,662 | 531,918 | 558,945 | 561,475 | 416,036 |

* **With R finite they do go, slowly.** A cold leaf gets reclaim's
  rewrites every second iteration (odd iterations here take about
  10,000 transactions, even ones 1,336); each visit adds a time klong
  and a shadow for each live key (1.4 a leaf here), and the leaf's next
  rule O drops the deleted klongs. After 11 iterations 37 % of them are
  still there; all of them go only when every such leaf has filled once.
* **Meanwhile the dead klongs grow**: reclaim's shadows replace the
  deleted klongs and outnumber them (4 to 5.6 dead klongs a live key).
* **With merges they go in two visits.** The same run on m8: 23,823
  deleted klongs after the deletes, 2,875 after iteration 3, 4 after
  iteration 5, none after 7. A merged leaf holds 8 to 17 live keys, so
  one visit of reclaim adds as many klongs and the leaf is full by the
  second. The dead klongs stay at 0.5 to 0.8 a live one: reclaim's own.
* **With R forever** nothing writes these leaves: what the deletes left
  stays (sparse r0 before its drive: 315,638 deleted klongs). Then the
  database keeps every version by its own setting, and a dead klong is
  part of that retained history; it costs because it sits in a node that
  is still read and, if written, written whole.


## 4. Option 2: compaction at the write

### 4.1 The mechanism, as prototyped

* **What.** Before each write to a key node (a put's K klong, a delete's
  bitmap, a child's klong in its parent), the writer counts the node's
  dead KEY klongs. With theta or more, the node counts as full: rule O
  replaces it by its last version with the write applied (a time split;
  a node that tt made is compacted in place, as today). A space split
  only if the last version and the write do not fit in B; today's rule
  would space split every last version of more than h klongs, which
  splits full nodes that only needed compacting (4.2, "Merges and the
  fill").
* **When, by whom:** in the writing transaction, by the writer's thread,
  in `Dag`'s write paths where rule O is decided today (`setValue`,
  `setNode`, `appendDeleteKlong`, `appendKlongs`, `handleFullNode`).
* **The bound:** after every write a node holds at most theta dead
  klongs (fewer than theta before it, at most one more by it). Never
  zero: a node that is not written again holds up to theta for good.
* **Checked how:** a census as section 3's (`DK`) counts it; to land, the
  walk of UnlinkFuzz strict would check "at most theta" after every
  transaction, as it checks merges' m.
* **The stream and a start:** no field. The rule is a function of the
  node, so a record of the new format means it and the rerun makes the
  same nodes: one more rule of format 7, as merges are.
* **The prototype**: `-Dbergdb.theta=T`, with a counter of compactions,
  on 024-14's build (branch `024-18-option2`, `tools/patch-o2.py`) and on
  `main` (branch `024-18-option2-main`, `5e0ab160`, 60 lines of `Dag`,
  `tools/patch-o2clean.py`). Not for landing: not gated, no restarts.

### 4.2 Its price, measured

"sparsecold" at 1M, R = 1 s, on 024-14's build (m8)
with and without the prototype; at the end of 60,000 transactions after
the deletes (18 iterations). "Stored" is the stored bytes of every node
over their last versions'; "B/op" the stream's growth over the 60,000
transactions an operation (the user's records and reclaim's).

| Set        | Nodes  | Dead   | d/l  | T a node | Stored | B/op  | Compactions/op |
|---|---|---|---|---|---|---|---|
| m8         | 10,103 | 76,875 | 0.70 | 1.66     | 1.60   | 236.8 | -              |
| theta 7    | 9,892  | 33,682 | 0.31 | 1.15     | 1.25   | 248.6 | 0.156          |
| theta 3    | 9,890  | 14,401 | 0.13 | 1.06     | 1.11   | 302.4 | 0.373          |
| 3b (r3)    | 9,910  | 532    | 0.00 | 1.04     | 1.01   | 269.2 | 0.065          |

* **Frans's supposition holds, to theta.** With option 2 reclaim's
  rewrites are writes, so every cold leaf is compacted at reclaim's next
  visit if it holds theta or more dead klongs, which a cold leaf does
  after the visit's first rewrites: the deleted klongs are gone after the
  first visit (0 from
  iteration 3 on, as with 3b), and a leaf then holds fewer than theta
  dead klongs (the histogram ends at 3 for theta 3). Not zero: the
  visit's own rewrites leave up to theta - 1 behind. Precisely:
  * reclaim rewrites only the live values stored before pCut, so it
    writes every leaf that holds one: every cold leaf, every second
    iteration (section 3.3), and no leaf whose values are all newer
    (those are written by users, and option 2 applies to those writes);
  * inner nodes are compacted the same way, by the klongs that their
    children's compactions add (a shadow each): in "cold" on `main`'s
    base, theta 3 leaves 0.11 dead klongs a live one in all nodes;
  * without a retain duration reclaim does not run: a cold node keeps
    what it had at its last write, fewer than theta.
* **The price is in replacing nodes that are dirty**, as for option 3
  (5.3): hot leaves under the users' writes ("over"), and in a cold
  database the inner nodes that the step before changed, which each
  step's compactions of leaves fill with shadows. theta 3 replaces a node
  every few writes (0.37 to 0.48 replacements an operation) and costs
  28 % to 46 % more stream bytes at 1M; theta 7 -3 % to +6 % (6.1);
  theta 1 two to three times (100,000 keys).
* **Merges and the fill.** A compaction is a time split: it keeps every
  live klong, so it lowers no count and BU1 (at least m live klongs a
  node) is untouched; it makes no node a merge would not. It keeps a
  last version of more than h live klongs in one node where rule O would
  space split it, so nodes are fuller: under overwrites on `main`'s base
  91,254 key nodes with theta 3 against 111,412 (-18 %), 111,389 with
  theta 7. On m8 (h = 17) the counts hardly change. The thresholds of
  024-14 need no change for theta 7.

**Written as a patch** (coordinator, 11:55): option 2 alone, 60 lines of
`Dag` with `-Dbergdb.theta`, branch `024-18-option2-main` on `main`
(`tools/patch-o2clean.py`, which applies to `main` and to a merges
branch, `handleFullNode` by either anchor). UnlinkFuzz (lookups and
scans at every time against a model, 024-14's matrix, node sizes 8, 14
and 30) with theta 1 on `main`: 36 runs, 0 failures; on 024-21's
build, strict (BU1 after every transaction as well), theta 3: 36 runs, 0
failures; theta 7: 36 runs, 0 failures. The
probe's own check (every live key's value at the latest time, by a
scan) passes with theta 1 and 3 and with 3c, in every shape.


## 5. Option 3: compaction by reclaim

### 5.1 As stated (3a): reclaim finds and rewrites every such node

* **What.** In each iteration, reclaim replaces every node reachable at
  the step's time that holds a dead klong (and with it its extra time
  klongs and bitmaps) by its last version, bottom-up, so that every node
  not written since holds none at the iteration's end. 024-11's CT.
* **Found how.** Not by the step's puts: a cold inner node above leaves
  that reclaim rewrites is on their paths, but a node with a dead klong
  whose values are all newer than pCut is on no step's path. So a walk:
  the touch of before 024-07, now as a writer, over the current tree.
  It cannot be the step's key range at the current time, which was
  024-07's fault (the last step walked every node put after the scan's
  last key: 772,454 nodes at 10M keys in time order); it needs its own
  cursor, a bounded number of nodes a step, resumed from a key stored in
  the iteration's row.
* **In which transaction:** the step's internal one; a replaced node's
  parent gets a klong of tt, and is replaced in turn (it now holds a
  dead klong), up to the root: so 3a replaces the closure of the nodes
  with dead klongs under their ancestors (section 5.3 counts it).
* **A restart** reruns it: the walk is not a function of the record's
  puts, so the step's record gets a flag and the walk's range (two
  keys), and a start walks the same range at the record's time before
  the record's puts, making the same nodes with the same ids (024-11,
  3.5 and 3.6: RB's and CT's field).
* **The touch, T-COVER and the cut.** The walk is a second touch, a
  writer: 024-07's bounds B1 to B4 get the walk's bound; T-COVER's
  premises hold (a replacement is a new node, dirty, with a live key
  below). A node replaced while dirty must still be written, and Rule A
  keeps a node dirty while a child is: RB's decisive cost (023-05 P3,
  5.3: 105,083 of 113,976 rebuilt nodes at 1M replaced a node in D).
* **Lean:** the model's touch step, `touchOf`, `T13_markTouch` and
  T-SCHEME's argument made again; the bound "within an iteration" needs
  reclaim's scheme in Lean (024-06, D1). As 024-11's RB, less the merges.

### 5.2 The variant 3b: reclaim's own writes leave clean nodes

The variant that does not rewrite every node every iteration, and needs
no walk (prototyped: `-Dbergdb.rtheta=1 -Dbergdb.inplace=1`, set "r3"):

* **What.** A put of a reclaim step to a node that the step's
  transaction did not make replaces the node by its last version with
  the put applied (rule O's time split; its parent, now holding a dead
  klong, likewise, once per step); a put to a node that the transaction
  made changes that node's klong of the key in place (it is of tt,
  behind T(tt), where every reader stops). So every node a step writes
  is its last version when the step ends: no dead klong, one time klong.
* **Which nodes:** the leaves of the values the step rewrites and their
  paths, which the step's scan reaches today: every leaf with a live
  value stored before pCut, so every cold leaf every second iteration
  (section 3.3), and every inner node above one.
* **A restart:** the step's record is rerun as its puts; the rule needs
  to know that a record is a step's: a flag in the record (format 7), or
  the step's row KV, which every step's record holds. No range, no walk.
* **The touch, T-COVER, the cut:** unchanged; the touch stays the paths
  of the step's own puts. A replaced node is to the cut a split's
  replaced node. A node that the step replaces while it is dirty (a user
  wrote it since its last take) is written once more, as at a split.
* **Lean:** the model's put gets the step's flag: a step's put is
  "replace by the last version, then put", one definition; A2 and A3 as
  for a split.
* **What it does not reach:** a node written by a user after reclaim's
  last visit (it holds that write's dead klongs, at most B), a leaf whose
  every value is newer than pCut (hot), and nothing at all with R
  forever.

**3c, 3b for cold nodes only** (prototyped as C3, `-Dbergdb.rcold=1`;
as a clean patch on `main`, `-Dbergdb.reclaimCompact=1`, branch
`024-18-3c-main`):
as 3b, but a step's write replaces a node only if the node's last klong
is older than the iteration's tStart; a node changed since (by a user or
by an earlier step) gets the write as today. The rule is a function of
the node and of tStart, which the iteration's row in reclaim's table
holds, so a start's rerun applies it the same way: a step's record
needs its flag (or its row KV), nothing more. It never replaces a node
that the iteration has made dirty, which is what 3b pays for (5.3).

### 5.3 Its price, measured

**3a by counting** (no prototype): at each iteration's end, the nodes
that hold a dead klong, the closure with their ancestors (what 3a
replaces, since each replacement puts a dead klong in the parent), its
size as last versions, against the bytes the iteration wrote (1M keys,
R = 1 s; `tools/iter3.py`):

| Shape, build   | Nodes   | With a dead klong | Closure | As last versions | Iteration  | Share     |
|---|---|---|---|---|---|---|
| over, `main`   | 111,412 | 100,392           | 101,505 | 21.0 MB          | 626 MB     | 3.4 %     |
| cold, `main`   | 110,198 | 102,398           | 103,569 | 21.7 MB          | 693 / 282 MB | 3.1 / 7.7 % |
| cold, m8       | 96,260  | 88,574            | 89,710  | 20.7 MB          | 688 / 325 MB | 3.0 / 6.4 % |
| sparsecold, m8 | 10,103  | 9,273 to 9,498    | 9,560   | 2.1 MB           | 142 / 57 MB | 1.5 / 3.7 % |

(Two figures: an iteration that rewrites the cold values, and the one
after it, which rewrites none.)

* **024-11's statement is verified**: at an iteration's end 90 to 95 %
  of all nodes hold a dead klong in every shape that writes, so 3a
  replaces nearly every node every iteration. Written as last versions
  that is the index's size, 3 to 8 % of what an iteration writes today.
* **That is not its price.** The prototypes below show that the bytes
  of a compaction are small, and the price is in replacing a node that
  is dirty: the version left out is written again, and Rule A keeps a
  left-out inner node dirty while one of its children is (023-05 P3,
  5.3; 024-11, 3.1, "inter").

**3b and two restrictions, prototyped** on `main` (branch
`024-18-option3-main`; sets M3, C3, D3 in `tools/job5.sh`): M3 is 3b as
in 5.2; C3 compacts only a node whose last klong is older than the
iteration's tStart (not changed in this iteration: neither by a user
nor by an earlier step); D3 also a node last changed by an earlier step
of the same iteration. 1M keys, R = 1 s, 60,000 transactions (4 to 5
iterations); "d/l" at the end, "B/op" over the 60,000:

| Variant          | cold: d/l | cold: B/op    | over: d/l | over: B/op     | sparsecold: d/l | B/op  |
|---|---|---|---|---|---|---|
| `main`           | 0.83      | 264.9         | 0.48      | 459.3          | 2.52            | 231.7 |
| M3 (3b)          | 0.01      | 400.3 (+51 %) | 0.39      | 1077.0 (2.3 x) | 0.03            | 286.7 |
| D3 (C3 + steps') | 0.02      | 406.3 (+53 %) | -         | -              | 0.35            | 292.1 |
| C3 (cold only)   | 0.14      | 266.5 (+1 %)  | 0.46      | 460.7 (+0 %)   | 0.43            | 235.9 |

(`main` has no merges: in "sparsecold" its leaves hold 1.3 live keys,
so even C3's clean leaves leave 0.43 there; on 024-14's build with
merges, 3b's r3 left 0.00 in "sparsecold" at 14 % more bytes, table of
section 4.2.)

* **Zero has a price only where reclaim replaces nodes that it made
  itself in the same iteration.** D3 differs from C3 by exactly that,
  and costs as much as M3: each step replaces its path's inner nodes,
  which the step before made and which are still dirty, so their
  left-out versions are written as well, and Rule A keeps a left-out
  inner node dirty while one of its children is (023-05 P3, 5.3, found
  the same for RB). Its rewrite iterations then finish in 13,860
  transactions instead of 22,993, as reclaim's allowance follows the
  stream's growth, and the database runs more of them.
* **C3 costs nothing measurable** (+1 % in "cold", +0 % in "over", +2 %
  in "sparsecold") and leaves every leaf that reclaim visits clean (in
  "cold" 0.09 dead klongs a live one in leaves, at the steps' boundaries
  and in the hot range), but inner nodes keep 0.69: each is compacted by
  the first step that reaches it, and the later steps of the iteration
  add a shadow for each child they replace. Stored, every node over its
  last version: 1.14 (`main` 1.71, m8 1.59).
* **In a hot database nothing changes** (0.46 to 0.48 in "over"): users
  write every node, rule O keeps its steady state, C3 leaves such nodes
  alone, and M3, which does not, pays 2.3 times the bytes.
* **A rule by count** (rewrite only nodes with k or more dead klongs) was
  not measured with C3: C3's cost is already within the noise, and a
  count would only leave more behind. What decides the price is which
  nodes are replaced (dirty or not), not how many dead klongs they hold.


## 6. Comparison and recommendation

Written 12:18.

### 6.1 Measured, 1M keys, R = 1 s

"d/l": dead klongs a live klong at the end of 60,000 transactions after
the shape; "B/op": the stream's growth an operation over them, against
the same build without the option. All on `main`'s base (prototype
branch `024-18-option3-main`), but "sparsecold" for option 2, which is
on 024-14's m8 against m8 (marked m8): without merges "sparsecold" has
1.3 live keys a leaf and says little of options 2 and 3.

| Option              | cold: d/l | cold: B/op | over: d/l | over: B/op | sparsecold: d/l | B/op     |
|---|---|---|---|---|---|---|
| 1 (`main`)          | 0.83      | 264.9      | 0.48      | 459.3      | 2.52            | 231.7    |
| 1 (m8, merges)      | 0.69      | 286.3      | 0.39      | 456.6      | 0.70            | 236.8    |
| 2, theta 7          | 0.30      | +6 %       | 0.35      | -3 %       | 0.31 (m8)       | +5 % (m8) |
| 2, theta 3          | 0.11      | +46 %      | 0.13      | +28 %      | 0.13 (m8)       | +28 % (m8) |
| 3b (M3)             | 0.01      | +51 %      | 0.39      | +134 %     | 0.03            | +24 %    |
| 3c (C3)             | 0.14      | +1 %       | 0.46      | +0 %       | 0.43            | +2 %     |
| 2 (theta 7) with 3c | 0.14      | +5 %       | 0.35      | -2 %       | 0.42            | +7 %     |

On m8, "over": theta 7 -2 % (0.31), theta 3 +29 % (0.12), theta 15
nothing.

* **The stream kept** hardly moves with any option (within 3 %: "cold"
  983 MB on `main`, 982 with 3c, 1,007 with theta 7, averaged over the
  censuses): it is the retention window's records and values, and the
  index nodes are a small part of it.
* **The heap of the index's arrays** (KeyNode.getMemSize over every
  node, as if all were resident) follows the dead and time klongs:
  "cold" 81.4 MB on `main`, 55.4 with 3c, 65.9 with theta 7, 49.4 as
  last versions; "over" 80.3, 80.0 and 76.9.
* **Reads** were not timed (no timing hold); a lookup examines every
  klong of each node it passes, so their cost per node follows "stored"
  in the tables above (1.7 times the last version on `main` in every
  writing shape, 1.14 with 3c in "cold").

At 100,000 keys, option 2 on `main`'s base, "over" and "cold": theta 1
+194 % and +57 % (0.04 dead klongs a live one), theta 3 +44 % and +33 %,
theta 7 +4 % and +6 %, theta 15 nothing: a node with 15 dead klongs is
full with their time klongs before theta is reached. A queue ("fifo")
has no dead klongs with any option (theta 3: +5 % bytes for nothing; 3c
+2 %). In "sparse" (`main`, every node hot) 3c changes nothing (2.87
dead klongs a live one, against 2.89) for +3 % bytes.

### 6.2 On 024-21's build (merges on `main`), 1M keys

Both patches applied as they are to 024-21's `024-21-merges` at
`4ef56d44` (P5's thresholds, format 7), branch `024-18-on-024-21`; run
12:53 to 13:12. "cold" and "over" have no deletes and match `main` to the node;
"sparsecold" is now the case with merges. Every run ends with its value
check passed.

| Option     | cold: d/l | cold: B/op | over: d/l | over: B/op | sparsecold: d/l | B/op          |
|---|---|---|---|---|---|---|
| 1 (merges) | 0.83      | 264.9      | 0.48      | 459.3      | 0.85            | 224.5         |
| 2, theta 7 | 0.30      | 279.8 (+6 %) | 0.35    | 446.8 (-3 %) | 0.36          | 241.2 (+7 %)  |
| 3c         | 0.15      | 266.7 (+1 %) | 0.46    | 461.2 (+0 %) | 0.16          | 225.1 (+0 %)  |

Also: "over" with theta 3 0.13 dead klongs a live one for +28 % (589.8);
"fifo" no dead klongs with or without 3c (148.1 and 150.7 B/op).

* **3c with merges reaches what it did on 024-14's build**: in
  "sparsecold" 0.16 dead klongs a live one against 0.85, stored nodes
  1.15 times their last versions against 1.72, for 0.3 % more bytes.
* **Option 2 with theta 7 halves the dead klongs** in "sparsecold" for
  7 % more bytes, and lowers "over" to 0.35 for 3 % fewer.

### 6.3 What each one is

| Option   | Dead klongs left                           | Zero, cold nodes, R finite      |
|---|---|---|
| 1        | at most B a node; 0.4 to 0.8 a live klong  | no; deleted keys' go by rule O   |
| 2        | at most theta a node, after every write    | no; under theta at each visit    |
| 3a       | none at an iteration's end, but new writes | yes, every iteration             |
| 3b       | none in what reclaim writes                | yes, at the next visit           |
| 3c       | none in leaves reclaim visits; inner keep  | leaves yes; inner nodes at most B |

| Option | Format and rerun                       | Lean (024-12)                    | Size               |
|---|---|---|---|
| 1      | nothing beyond merges                  | nothing                          | 0                  |
| 2      | a rule of format 7 (theta from B)      | the put's and delete's full test | 60 lines of `Dag`  |
| 3a     | a step's flag and walk range; a cursor | the touch as a writer; T-SCHEME  | RB's, ~300 (guess) |
| 3b     | a step's flag (or its row KV)          | a step's put: replace, then put  | ~40 lines          |
| 3c     | a step's flag; tStart from the table   | as 3b, with tStart in the trace  | ~45 lines          |

None of them keeps "what is deleted costs nothing, eventually" to the
letter with R forever: then nothing writes a cold node, and option 2's
theta is the least that stays. With R finite, option 1 with merges
already removes each deleted key's klong within about two visits of
reclaim (section 3.5); options 2 and 3 do it at the first visit, and
3b and 3c also remove reclaim's own shadows, so that a cold node's cost
goes to its last version.

### 6.4 Recommendation

**Option 3 as 3c: reclaim's own writes leave the cold nodes they write
as last versions. Option 1 for everything else; option 2 not now.**

* **3c gives Frans's wish where it matters.** The cold database with R
  finite is the worst case today (0.83 dead klongs a live one on
  `main`, 0.69 with merges), and all of them are reclaim's own shadows.
  3c takes it to 0.14 (0.09 in leaves; the rest in inner nodes, at most
  B each), at +1 % stream bytes, because it never replaces a node that
  the iteration has changed, which is what made 3b cost +51 % to
  +134 %. A deleted key's klong goes at reclaim's next visit of its
  leaf, within two iterations.
* **It is small and deterministic**: no walk, no range, no touch as a
  writer; a flag on a step's record, and a rule of the node and the
  iteration's tStart, which reclaim's table holds, so a start reruns it.
  The Lean model's put gets the step's flag and tStart.
* **Hot nodes need nothing more.** Their dead klongs are rule O's steady
  state, about 0.4 a live klong and at most B a node, written by their
  users anyway. Option 2 with theta 7 lowers that to 0.35 for -3 % to
  +6 % bytes; with theta 3 to 0.12 for +28 % to +46 %. Not worth a rule
  of the format now; kept as a patch (`024-18-option2-main`) if Frans
  wants a bound that holds with R forever, the only case no reclaim
  option reaches.
* **3a and 3b reach zero but replace dirty nodes**, which Rule A makes
  expensive. Not recommended.
* **Before it is decided** (QD3): 3c with restarts (the prototype's
  flag is not rerun), at 10M, and reads timed. At 1M on 024-21's build
  it is measured (6.2). Written
  as a patch for that: branch `024-18-3c-main` (`74a0ba1a`, on option
  2's `5e0ab160`), `-Dbergdb.reclaimCompact=1`, 45 lines of `Dag` and 5
  of `Reclaim` (`tools/patch-3cclean.py`); it gives C3's counts.


## 7. Frans's further questions

Short, as asked (coordinator, 11:55): the node size (024-19) and the
stored form (024-20) are studies of their own, postponed. What these
counts say:

* **Dead klongs a live klong do not depend on B.** "over", R forever,
  `main`, 1M keys, after 20,000 transactions, with the builder's sizes
  (`DK B=`): 0.46, 0.46 and 0.45 dead klongs a live one for B = 14, 30
  and 62 (in leaves and inner nodes alike); a leaf holds 2.0, 4.6 and
  9.5; one write of every leaf stores 1.53, 1.70 and 1.79 times its last
  version; the bytes a put are 476, 426 and 421. Rule O sets the rate (a
  leaf starts at its last version and is replaced at B), so the options
  scale with B as their parameters do: option 1's bound is B a node,
  option 2's theta should be a fraction of B, option 3's cost an
  iteration is the index's size as last versions.
* **B is a property of the database already**: 8, 14, 30 or 62 by the
  builder, kept in the meta block, another size refused at a start
  (005-50); 62 is the format's limit (a delete bitmap has 62 bits). The
  rules that depend on B (merges' m, h, c; option 2's theta) must be
  functions of B in the format (024-14, QT2).
* **The stored form.** Of a stored leaf under random overwrites (B = 30)
  45 % is live klongs, 25 % time klongs, 21 % dead klongs, 9 % headers;
  a time klong carries an unused 8-byte reference (12 % of the bytes). A
  form that stores only the klongs added since the node's previous
  stored version (named by prevPos, which every stored key node has)
  would remove most of the stream cost of dead klongs without any
  compaction, at the price of reads through a chain of versions. 024-20
  should measure the bytes a write and a put in each form, the reads and
  loads through a chain, and how each form changes options 2 and 3.


## 8. Questions for Frans

Cite as "024-18, QD1".

**Decided, QD1: option 2 with theta 7** (Frans, 2026-11-11). Asked by
the coordinator for the cons of 3c (its restart's rerun not tested; it
leaves the provable bound at B a node; inner and hot nodes unchanged;
one run each at 1M only; 024-20 may change the picture), 14:21: "I am
leaning towards 2 with threshold 7. It seems simpler. And I think we
need to accept that we need to take this step by step. We cannot change
everything at once. As you said, compactation of stored nodes can change
things. And this is not thouroughly measured." To the proposed order
(the merges first, then option 2 as a change of its own, model first;
3c shelved), 14:27: "Yes." And to measuring at 10M with MEM and reads
timed before it lands: "No. Let's get this in now. We will measure
carefully and study alternatives later." So option 2 (section 4) is
built after the merges (024-21, 024-22), through the model, with theta
7 for B = 30 as a named constant, and lands on its gates; the careful
measurements (10M, MEM, reads) and the alternatives (3c, 024-20's
stored form) come later. QD3 to QD5 lapse with 3c; QD2 stands as
recommended (option 2 gives the bound with R forever).

* **QD1. Which option?** Recommended: **3c** (reclaim's writes compact
  the cold nodes they reach) with merges, option 1 for the rest (6.4).
* **QD2. A bound with R forever?** With R forever nothing writes a cold
  node, so only option 2 bounds its dead klongs below B; the database
  then keeps every version by its own setting. Recommended: **accept**
  option 1's bound there (at most B a node, nodes in proportion to the
  live keys), and keep option 2's patch for later.
* **QD3. The next measurement**: 3c on 024-21's branch with restarts
  that rerun the steps' flag (a record field), at 10M, and gets and
  scans in a timing hold (1M is done, 6.2).
  Recommended: **yes, before 3c becomes a rule of format 7.**
* **QD4. The step's flag in format 7**: an explicit field of a step's
  record, or the presence of reclaim's row KV in it? Recommended: **an
  explicit field**: the rule should not depend on an internal key's
  name.
* **QD5. 3c's inner nodes** keep up to B dead klongs (0.69 a live klong
  in inner nodes, a tenth of the nodes): accept, or look for a rule that
  also cleans them without replacing dirty nodes? Recommended:
  **accept** for 2026.5.


## 9. State

2026-11-11, from 11:26, by the agent "dead" of coord-1111. Last update
13:49.

* **Clone** `/Users/f/fl/bench/2026-11-11/dead/clone` from `main` at
  `558cdfe3`; measuring branches, none for landing as they are
  (worktrees beside the clone):
  * `024-18-on-024-21` (`g-wt`, committed `d64aab58`): both patches on
    024-21's `024-21-merges` at `4ef56d44` (merges, format 7, P5's
    thresholds), applied by the two scripts as they are (build `dead/bg`;
    sets g0, g7, g3, g3c in `tools/job8.sh`).
  * `024-18-option2-main` (`o2m-wt`, committed `5e0ab160`): option 2
    alone on `main`, `-Dbergdb.theta=T` (`tools/patch-o2clean.py`;
    build `dead/bo2m`).
  * `024-18-3c-main` (`c3m-wt`, committed `74a0ba1a`, on `5e0ab160`):
    3c, `-Dbergdb.reclaimCompact=1` (`tools/patch-3cclean.py`; build
    `dead/bc3m`; sets c3c, c3c0 in `tools/job7.sh`).
  * `024-18-option3-main` (`m3-wt`, uncommitted): the variants M2, M3,
    C3, D3, T7C3 (`tools/patch-main.py` and two edits; builds `bm3`,
    `bm3c`, `bm3d`; `tools/job5.sh`, `job6.sh`).
  * `024-18-option2` (`o2-wt`, uncommitted), on 024-14's
    `024-14-thresholds`: option 2 and r3 on m8 (`tools/patch-o2.py`,
    build `b2`, `tools/job2.sh`).
  * `024-18-dead`: `main` (build `bmain`).
* **Here** (`18-dead-klongs/`): the probe `DK.java`, the two patch
  scripts and the three summarizers; the rest in
  `/Users/f/fl/bench/2026-11-11/dead/tools/`.
* **Probe** `DK.java` here and in `dead/probe/` (compiled against each
  build in `dead/probe/c-*`); it ends with a check of every live key's
  value. `tools/summ.py`, `cmp.py`, `iter3.py` summarize; outputs in
  `dead/out/` (`1m`, `1m-long`, `g1m`, `probe100k`, `B`, `verify`).
* **Done**: sections 1 to 8 on the 100,000 and 1M runs; UnlinkFuzz of
  option 2 with theta 1 (36 runs, 0 failures).
* **Stopped, 12:26**: runs on 024-21's build and the fuzz were started
  at 12:25 inside thr's timing hold (my error: the owner files were not
  read before the start); the coordinator killed three JVMs, I stopped
  the rest and discarded their outputs. Every run script in `tools/` now
  refuses to start while an owner line has "timing:", and
  `tools/guard.sh` stops my lane the moment one appears. UnlinkFuzz with
  theta 3 on `main` stopped at size 14 with 0 failures
  (`out/fuzz-theta3-partial.txt`).
* **Done, 12:53 to 13:07**: the 1M runs on 024-21's build, one JVM, no
  slot (`tools/jobs-g-one.txt`, `out/g1m/`; section 6.2). Running at
  13:08: the last of them ("fifo" and theta 3 "over").
* **Done, 13:13 to 13:31**: UnlinkFuzz strict on 024-21's build with
  theta 3, 36 runs, 0 failures (`out/fuzz-g-theta3.txt`); 13:31 to
  13:48 the same with theta 7, 36 runs, 0 failures. Nothing of mine
  runs now; no slot is held.
* **Not done**: 10M (no slot; `tools/hold10m.sh` dropped); 3c with
  restarts; timing of reads.
* **To continue**: QD1 to QD5 with Frans. For 3c as a rule: a field in a
  step's record (QD4), its rerun at a start, a test with restarts, then
  10M on 024-21's branch with `tools/job8.sh` sets g0 and g3c.

2026-11-13. Status set after the release (coord-1113).
