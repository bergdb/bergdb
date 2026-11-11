# 024-22. Merges at the delete in the Lean tree model

Created 2026-11-11 by Frans Lundberg. Status: open.

The model's half of the one algorithm that release 2026.5 ("solid
algorithms", 024-04) still has to put in place: merges at the delete
(024-11, MG), written into 024-12's Lean model of the key tree and run
before and beside the Java code (024-21, the agent "mgj"). Frans's order
(024-04, section 6): a design note, a Lean definition that runs with its
invariants and cost bounds stated as properties, runs on small exhaustive
cases and the fuzz, then Java checked against the model; the proofs when
the change has settled. Frans, 2026-11-11, 11:44: "Could we instead make
reasonable assumptions on 1, 2, 3. Go with this "for now". To get the
merges at the delete done today. [...] To be able to change one thing at
a time." So today: the definition, its stated properties and its runs;
the large proofs are not today's work.

Cite the decisions as "024-22, MD1", the stated properties by their TP
numbers (024-12's series, continued), the findings as "024-22, MF1".


## 1. In short

Kept current; section 11 has the exact state; section 9 the questions. Written 14:10.

* **What the model defines.** The merge at the delete in 024-12's Lean
  tree (branch `024-22-merges-lean`, head `8e78cf65`, on 024-12's gated
  head `d90586d0`): 024-11's algorithm as P5 placed it in release
  2026.4's `deleteUpward` and as mgj ports it to Java (024-21): after a
  delete changes a node, a node that is not a segment root and holds
  fewer than m live klongs is merged with a sibling (one new node, or
  two when they hold more than c), the parent is checked in turn, then
  root collapse; merged nodes are new nodes, a node of the transaction
  is taken back with its klongs repointed (024-11's QU6, P5's way; 2.9
  says what the model shows about the other way). The thresholds are
  parameters, not literals (`Params.mergeBelow` m, `mergeMax` c;
  `withMerges`: m = max(2, B / 4), c = B / 2 from node size 8, no merge
  below, as Java). About 300 lines in `Exec.lean`; no rule of 2026.4
  changed, and with m below 2 the model is 2026.4's tree, run for run.
* **What the runs covered before Java** (section 3; `treetest`, one
  core): exhaustive sequences at node sizes 8, 10 and 12 after four
  kinds of prefix, every subset of a transaction's deletes (or puts and
  deletes), pairs, random runs, the whole model (records, D, startup):
  about 253,000 states with merges, and 024-12's 340,000 without. After
  every transaction: V1 and the other invariants, the map (gets at
  every time, scans), BU1's count, CB1, CB3, A6, `dirtyNodeBound` of
  record format 7 and TP26. **0 failures of the algorithm.**
* **What they found** (3.2): no fault of the merge. MF1, a cost: a
  delete in a full leaf can split up to a new root and merge back down
  in one operation (6 nodes made, 4 taken back); correct; an option for
  later. MF2, the parameters: outside TP28 (024-11's formulas at node
  size 6) V1 fails at once and P5's "no merge" skip becomes reachable,
  which is why the model makes the skip an error and Java should (J1).
  J5: the retarget of a merge's take-back matters in exactly one case,
  which single deletes reach only in nodes full of dead klongs. MF3,
  found by Java's traces, not by the model's runs: the model refused a
  root above the trace's level bounds that a delete makes and takes
  back in one operation (the model's fault, fixed; 5.1).
* **Fault 12, planted** (section 4). Its kind in the merge (a take-back
  without the retarget): caught by the random runs at once, and by the
  exhaustive runs once a prefix of overwrites was added (the runs
  without it missed it). Fault 12 itself: caught by no check that
  `treetest` had; with one operation a key it can no longer dangle, it
  breaks only A6; A6 is now checked on every state, and catches it in
  the first transaction that reaches the rule.
* **Against Java** (section 5): Java with merges (024-21's `f507148d`
  with 024-12's exporter, in a scratch combination) on `treeconf.sh`
  drain, small and reclaim, 10 seeds: 230 traces, 50,308 transactions,
  30,636 merges (1,875 into two nodes, 9,597 of inner nodes): **the
  model gives Java's change, klongs and records exactly** (C-T1 to
  C-T9), V1 holds on Java's tree after every transaction, and
  `tracecheck` on reclaim traces is OK (A6; every cut, I2 included).
  One trace failed first, by MF3, the model's; after the fix all pass.
  **No difference of Java's**, so no reading of 024-11 had to be
  chosen. The medium set (node sizes 8 to 62, 4,569 transactions,
  7,101 merges): all 9 traces OK.
* **Properties** (2.7, 6): stated TP28 to TP37 (the thresholds'
  conditions, V1, TH2, TH3 as BU1's count, CB1, CB3, the merge's sizes,
  klongs and fill, the split's fill); V2 to V9, TH1 and I2 are 024-12's
  statements, which with merges speak of the merged tree;
  `dirtyNodeBound` of format 7 restated from Java and TP26 with merges.
  **Proved:** TP28 from node size 8 (and its failure at 4 and 6), TP34
  to TP37: every node a merge or a space split makes holds m or more.
  Left: TP30 (V1 kept, the B-tree proof) and TP31 to TP33.
* **Gated** (section 8): `lake build` (all targets; no sorry or axiom),
  the whole `treetest` default set (31 min, 0 failures), `treeconf.sh
  all 5` on the branch's own Java (115 traces OK), on the commit before
  MF3's fix. **Not yet gated:** `level2.sh` on the head `8e78cf65`
  (running since 13:59, about 18 minutes); on the head so far `lake
  build` (180 jobs), two `treetest` runs and the 110 drain traces of
  Java with merges.
* **For Java (mgj):** section 7, J1 to J8.

## 2. The design note

### 2.1 The assumptions "for now", as parameters

Frans's three questions of 11:44 (024-14's), answered "for now" by
024-11's values, each a parameter of the definitions, not a literal:

| What                    | Value now                 | In the model                   |
|---|---|---|
| node size B             | 30 (8 to 62 in tests)     | `Params.M`, as before          |
| m, the least fill       | max(2, B / 4): 7 at 30    | `Params.mergeBelow`            |
| c, the merge's cap      | B / 2: 15 at 30           | `Params.mergeMax`              |
| h, a time split's most  | B / 2, today's rule O     | `handleFullWith`'s `M / 2`     |
| dead klongs             | nothing beyond the merge  | no change                      |
| how merged nodes made   | P5's: new nodes, take-back | `merge`, `mergeParent`        |

* `Params.withMerges` sets m and c from M by 024-11's formulas; the
  default `mergeBelow = 0` is release 2026.4 (no merge), so every run of
  024-12 is unchanged. Merges are on when m is 2 or more.
* h stays the literal `M / 2` of rule O, as in 2026.4: 024-14's other
  sets (m8, m9, dense) change h too; then h becomes a parameter, one
  line in `handleFullWith` (not done, not asked today).
* **The thresholds must meet `MergeParamsOK`** (TP28, section 2.7): 2 <=
  m; a merge into two nodes gives each at least m, m <= (c + 1) / 2; a
  space split's smaller half has at least m, m <= (M / 2) / 2; the nodes
  made fit, c + 1 <= M. **024-11's values meet it from M = 8 on, and not
  at M = 4 or 6**: at 6, m = max(2, 1) = 2, and a space split of a last
  version of 3 live klongs makes a half of 1. So the runs with merges are
  at node sizes 8, 10 and 12 (and 14, 30 in Java's traces); 4 and 6 run
  2026.4's tree only. Proved for every M >= 8 (section 6).

### 2.2 Where the merge enters the model

All in `lean/SIS/Tree/` (024-12, 2.8 said where):

* **`Node.lean`**: `Params` gets `mergeBelow` and `mergeMax` (default
  0), `Params.merges`, `Params.withMerges`; `KNode.live` and `KNode.cnt`
  (024-11's cnt: the live compare values at the latest time; Java's
  `liveCount` without its limit).
* **`Exec.lean`**, a new section "Merges at the delete" between
  `collapseRoot` and `climb`: `descendToHeight` (P5's `descendToDepth`),
  `mergeIdx`, `mergeKlongs` (M2, M3, a pure function), `newKlongs`,
  `insertSorted` (`addSortedKlong`), `mergeParent` (M4), `sibling`
  (M1's read), `merge` (M1 to M5), `mergeUp` (P5's `mergeAfterDelete`,
  024-11's F3 and F4), `afterDelete` (the merges, then RC, F1).
* **`newKey` and `runOpsFrom`** (MF3, 5.1): a key node made outside the
  level bounds is an error at the transaction's end, unless taken back
  (024-12, 4.2, had it an error at once).
* **`deleteUpward`**: three calls, where P5 has them: after the bitmap
  in a leaf that keeps a live key; after the bitmap in the segment leaf
  where the upward unlink stops; after the bitmap or LE-b in an inner
  stop node (then RC as before). Nothing else of the delete changes.
* **`Inv.lean`**: `walk` checks V1, `FillOK`, beside `RootsOK`.
* **`Bound.lean`**: `dirtyNodeBound` of record format 7, restated from
  mgj's Java (3.4), when `Params.format7` (m is set); `overflows` with
  `merged`; `Limits.dirtyNodes` (TP26) with merges.
* **`MergeProps.lean`** (new): TP28 to TP37 (section 2.7).
* **`TreeTest.lean`**: the runs with merges (section 3).

### 2.3 What the state needs

Nothing new in P, in `W` or in a record. The merge's nodes are new key
nodes of the transaction, as a split's (`newKey`, ids in Java's order:
m1, m2, then the parent's split); the nodes left out are unlinked or
taken back with the functions that the upward unlink uses (`unlink`,
`takenBack`, `retarget`); `madeFor` gets m1 and m2, as for a split's
halves. **One difference from Java:** P5 finds the node to check after a
change by its depth, kept right by counting the full nodes and the new
roots since (`PutData.fullNodes`, `newRootsMade`). The model finds it by
its segment and height (`descendToHeight`), which a split keeps and a
new root is above; it re-descends every time, where P5 reuses the path
when no node was full. The same node either way, as every split and new
root of a delete is on its key's path; no counter in `W`.

### 2.4 The steps, in order

A delete of key k at tt (`putKv`, `setValue`, `deleteUpward`):

1. **Descend** to the segment leaf of k's last segment cv, as today. No
   live klong of cv: a noop.
2. **The leaf keeps a live klong**: the bitmap in the leaf
   (`appendDeleteKlong`: in place, new, or rule O on a full leaf); then
   `afterDelete` at the leaf's segment g and height 0.
3. **The leaf is emptied: UP, as 2026.4** (`climb`, take-back or unlink
   of each node below the stop node). The stop node is a segment leaf:
   its bitmap, then `afterDelete` at its segment and height. An inner
   stop node (LE-b or a bitmap): then `mergeUp` at it, then RC as before.
   The space root kept empty: nothing more.
4. **`afterDelete g h`**: if merges are on, `mergeUp` from (g, h); if it
   merged, RC on segment g's tree (`collapseRoot`, unchanged).
5. **`mergeUp`, the fix loop** at (g, h): re-descend to the node x of
   segment g at height h on k's path, at depth d. Stop if x is the space
   root (d = 0), a segment root (its parent is a segment leaf), or holds
   m or more live klongs. Else `merge x d`: two nodes made, stop; one
   node made, go on at (g, h + 1) (the parent lost a live klong).
6. **`merge x d`** under its parent p (M1 to M5):
   * M1, the sibling: in p, over the klongs that p's last bitmap does
     not delete, x's own klong (the last of x's compare value), the
     smallest compare value above it (the right sibling) and the largest
     below (the left one). Left if it exists and either no right one
     exists or cnt(left) + cnt(x) <= c; else the right one. A sibling is
     read as any node, not marked; it must be of x's kind.
   * M2, M3, `mergeKlongs`: L's live klongs, then R's, in compare order;
     an inner R's first klong (the empty key) gets cR, R's compare value
     in p. At most c of them: one node m1. Else m1 gets the first
     ceil(n / 2) and m2 the rest, whose first compare value g p gets; an
     inner m2 starts with the empty key. Each new node is a time klong of
     tt and the key klongs, in segment g at x's height.
   * `madeFor`: m1 replaces L (or what L replaced, if tt made L), m2 R.
   * M4, `mergeParent`: R's compare value is deleted (a bitmap of tt, the
     transaction's own last bitmap in place) unless m2 starts at cR, when
     R's klong names m2; L's klong names m1, in place if it is of tt,
     else by a new klong; m2's new klong of g if R's was deleted. Room is
     counted as P5 does; without it rule O replaces p by its last version
     with the bitmap's union, L's klong pointed to m1 (`replaceKlong`)
     and m2's klong pointed or inserted (`insertSorted`).
   * M5: L and R are left out. One that existed loses its klongs of tt
     (`unlink`); one that tt made is taken back, after every klong of tt
     in p that names it names m1 (`retarget`, V8).
7. **RC** (`collapseRoot`): while the segment tree's root is an inner
   node with one live klong, its child takes its place (2026.4's rule).

**What 024-11, section 5, says and the model does:** the same algorithm
in another order. 024-11's F2 (a root leaf emptied: remove its klong in
the leaf above, fix that leaf) is 2026.4's climb, which decides the stop
node first and changes nothing below it, as Java does; its F1 (RC)
inside the loop is RC after the loop, as nothing but the merges below
the root can leave the root one klong. **2026.4's climb inside a tree,
LE-b and the take-back of an emptied half** stay in the model as they
are; with V1 they should be reached for roots only (024-11, 5.6, said
"the model omits them"; MD3 below). The runs count each rule (`trail`).

### 2.5 The trace: does format 3 suffice

**Yes, with the two thresholds on the TREE line.** C-T1 compares the
change (NEW and ADD lines: m1, m2 and the nodes of a parent's split,
with ids, levels and entries; the parent's bitmap and klongs of tt); C-T2
compares the klongs of every key node that T(i) made or gave an entry
(KN lines: m1, m2, the parent, the leaf); a node left out that existed
gets no entry of tt and no KN line, and the model's change has none for
it either; a node taken back is in neither. C-T9 compares every record
and D. What the checker cannot know from a format 3 trace is whether
the writer merged and with which m and c.

* **Proposed: `TREE m g h k mb mm`**, two more numbers, the writer's
  `mergeBelow` and `mergeMax`; a TREE line of 5 tokens is a trace of
  2026.4's writer (both 0). `treecheck` reads either. The exporter
  writes Java's values, so a change of Java's constants needs no change
  of the checker.
* **Not needed:** the siblings read (the model reads them from P), the
  nodes taken back (the model knows them), counts of merges (the
  `trail` gives the model's; C-T1 compares the result).
* **A risk for C-T9, not for C-T1:** D after a merge. Java reports a
  node left out as replaced, so that it leaves D if it got dirty in this
  transaction only (as an unlinked node); the model's still-dirty test
  (`javaTest`) decides it from reachability. They agree for 2026.4's
  unlink; whether for merges is the first thing C-T9 will tell.
  (Result: they agree; C-T9 passes on every trace, 5.1.)
* **What the TREE line's G and H do not cover:** a node that a
  transaction makes and takes back (MF3, 5.1); the model checks the
  bounds on the change, not on every node made.

### 2.6 The cost bounds

* **CB1, one delete:** at most one merge for each level of the segment
  tree it is in, below its root (the loop moves up one height a merge
  and stops at the root). A merge reads at most two siblings (the left
  one, and the right one if the left one does not fit), makes at most
  two nodes, and gives p at most four klongs (a time klong, a bitmap,
  two key klongs).
* **CB2, `dirtyNodeBound`:** Java's count before the go point must
  count the merges; 2026.4's does not. The model restates Java's count
  (`Bound.lean`), so the model's runs check TP23 (the nodes marked are
  at most the count) against 2026.4's count, and report every
  transaction that exceeds it (section 3). Java's new count (024-11's
  QU7: the simple one) is mgj's; the model restates it when it exists.
* **CB3, amortized:** over a run from R(0), merges <= deletes + 2 x
  space splits.
* **CB4, thrash:** a merged node holds at most c + 1 klongs (TP34), so
  B - c - 1 more fit before rule O; the rate is a measurement (024-14,
  section 6), not a statement here.

### 2.7 The properties

New statements, `lean/SIS/Tree/MergeProps.lean`, each a `def ... : Prop`
(no `sorry`, no axiom in what is built), numbered after 024-12's TP27:

| TP | Name                  | What it says (024-11's name)               | Run  |
|---|---|---|---|
| 28 | `MergeParamsOK`       | the thresholds' conditions (2.1)           | PROVED |
| 29 | `FillOK`              | V1: a key node that is not a segment       | S    |
|    |                       | root has at least m live klongs (BU1 (a))  |      |
| 30 | `MergeInvPreserved`   | TH2: with merges on, TP7 (the invariants,  | S    |
|    |                       | V1 among them) after every run             |      |
| 31 | `NodeCountBound`      | TH3, BU1's count: key nodes <= S + (n +    | S    |
|    |                       | S - 1) / (m - 1) at every time             |      |
| 32 | `MergeOpBound`        | CB1: a transaction's merges <= its         | S    |
|    |                       | deletes x (H + 1)                          |      |
| 33 | `MergeAmortized`      | CB3: merges <= deletes + 2 x space splits  | S    |
|    |                       | over every run from R(0)                   |      |
| 34 | `MergeSizeOK`         | V5 of the merge: m1 at most c klongs, or   | PROVED |
|    |                       | each node at most ceil(n / 2)              |      |
| 35 | `MergeKeepsKlongs`    | the merge keeps the pointers, in order;    | PROVED |
|    |                       | the compare values but the empty keys'     |      |
| 36 | `MergeFillOK`         | V1 and V5 at a merge: with TP28, its nodes | PROVED |
|    |                       | hold m or more and fit in a node           |      |
| 37 | `SplitFillOK`         | V1 at a space split: with TP28, each half  | PROVED |
|    |                       | of rule O holds m or more key klongs       |      |
| 23 | `DirtyBoundOK`        | 024-12's, now with format 7's count (3.4)  | S    |
| 26 | `DirtyBoundFromLimits` | 024-12's, its limit restated with merges  | S    |

Where 024-11's other names are in the model already, with merges on (the
statements take p, so they speak of the merged tree as they stand):

| 024-11           | In the model                                      |
|---|---|
| V2, roots        | `RootsOK` and `NonEmptyOK` in `walk` (TP3, TP6)   |
| V3, order        | `RangeOK`, `LeftmostOK` (TP2, TP6)                |
| V4, balance      | `KindsOK`: an inner node's children one height    |
|                  | below it; leaves are height 0 (D5), so every leaf |
|                  | of a segment tree is at its root's height         |
| V5, size         | `SizeOK` (TP5); the merge's part TP34             |
| V6, history      | A2 (TP14, `StepOK.current`)                       |
| V7, new nodes    | A3, TREE, A6', A-COPY (TP14, TP16)                |
| V8, closed       | `PointersOK` (TP4): a klong, live or dead, names  |
|                  | a node of P, never one taken back                 |
| V9, function     | A1 (TP19), ids (`StepOK.fresh`, `distinct`)       |
| TH1, the map     | `GetOK`, `ScanOK` (TP10, TP11)                    |
| TH4, the costs   | TP32, TP33, and TP23 with Java's new count        |
| I2 of 024-07     | TP27 `DataBelowOK`, unchanged: it follows from    |
|                  | `NonEmptyOK` and `KindsOK`, which V1 strengthens  |

How hard each proof looks: section 6.

### 2.8 Decisions taken here

* **MD1. P5's structure, not 024-11's loop as written.** The calls of
  `mergeAfterDelete` in 2026.4's `deleteUpward`, as P5 placed them, and
  RC after the loop: this is what Java builds (mgj ports P5), and 2.4
  shows it is 024-11's algorithm in another order.
* **MD2. What P5 skips is an error.** P5's `merge` returns "no merge"
  for a node without a sibling, an empty node, or an inner node whose
  first live klong is not the empty key, and the loop stops. Each is a
  state that V1 to V3 exclude; in the model each is a `Bug:` error, so a
  run that reaches one fails (TP8, `NoBug`). For Java: the same (7).
* **MD3. 2026.4's climb, LE-b and the take-back of an emptied half
  stay.** 024-11 (5.6) proposed to omit them; changing one thing at a
  time (Frans, 11:44), the model keeps them and counts them. If the runs
  never reach the climb inside a tree or LE-b with merges on, that is
  the evidence for making them a `Bug` later.
* **MD4. The node after a change is found by segment and height**
  (2.3), not by P5's counted depth: the same node, no counters.
* **MD5. The thresholds on the TREE line** (2.5).
* **MD6. `withMerges` gives m = 1 below node size 8**, as Java's
  `Dag.minFill` (024-21): 024-11's m = max(2, B / 4) fails TP28 there.
* **MD7. With merges the model's runs require A6, not only A6'**
  (`treetest model`): 024-12 (6.2) says the gates will; the merge's
  retarget and in-place pointers are what keep it.

### 2.9 P5's way and the other way (024-11, QU6)

P5's way, modelled here: a merge always makes new nodes; a node of tt
that it leaves out is taken back, and every klong of tt in the parent
that names it is pointed to m1 (`retarget`); the parent's entries of tt
are added (a bitmap bit, a new klong), never removed. The other way: a
node of tt is changed in place (as a split's `spaceSplitInPlace`), and
the parent's entries of tt are the net change (a klong of tt that tt
deletes is removed, not marked). What the model shows (numbers in 3.3):

* **The take-back is common.** Nodes of tt taken back by merges, per
  merge (`merge.takeback` against `merge.one` + `merge.two`, 3.1 and
  3.3): 0.10 with transactions of one or two operations after fresh
  puts, 0.39 in both random runs, 0.46 after the overwrites of prefix
  4, 0.53 and 1.26 for transactions of many deletes (fresh, and in
  nodes full of dead klongs: there a merge often leaves out two nodes
  of tt). Every merge after a delete's rule O takes back the time
  split's node.
* **The retarget matters in one case only** (section 4, A): the right
  node R made by tt and its klong of tt deleted by the merge's bitmap.
  Everywhere else the merge points L's klong of tt in place and nothing
  names the node taken back. The other way removes that case by form
  (no dead klong of tt), which is 024-11's "V8 by form".
* **MF1 is P5's way at its most costly**: a time split of tt merged and
  taken back in the same operation. In place, the merge would take the
  time split's node as its N1; net, the parent would not keep its klong.
* **What it would change:** ids (fewer nodes made, so the ids of a
  transaction's later nodes), the parent's klongs (fewer bitmaps and
  shadowed klongs of tt), so the bytes of a record's nodes and what a
  start reruns: a change of format 7's meaning. The model has every piece
  (`spaceSplitInPlace`'s pattern; `retarget`); the change is perhaps 60
  lines of `merge` and `mergeParent`. Not done: one thing at a time.


## 3. The runs before Java

`lake exe treetest` with `merge` (`Params.withMerges`; G = 1, H = 8), one
configuration a process, one core, on the branch's working tree.
Logs in `/Users/f/fl/bench/2026-11-11/mgl/runs/`. After every
transaction each run checks: the invariants' walk with V1 (`faultsAt`:
`FillOK`, `RootsOK`, `NonEmptyOK`, `LeftmostOK`, `RangeOK`, `KindsOK`,
`SizeOK`, well-formed klongs, history and klongs one to one), pointers
of every entry to nodes of P (TP4, V8), every key's get at every time
against the reference map (TP10, TH1), the scans (TP11), a noop delete
(TP12), the skip search (TP24), TP21 and TP22, and with merges BU1's
count (TP31), CB1 (TP32: merges of one operation at most the tree's
height and one) and CB3 (TP33, from R(0)); an error of the writer
other than the level bounds is a failure (TP8, so P5's skips of MD2
too). TP23 against 2026.4's `dirtyNodeBound` is counted, not failed.

### 3.1 Exhaustive

Every sequence of `depth` transactions of one operation (a put or a
delete of one key) after a prefix (2: every key put in its own
transaction; 3: then all again in one; 1: all in one; 4: as 2 twice, so
that nodes are full of dead klongs and a delete's rule O comes before a
merge). The first five rows ran with 2026.4's `dirtyNodeBound`, the
rest with format 7's (3.4).

| M  | Depth | Keys | Prefix | States | Merges | Two | Inner | Taken back | Failures |
|---|---|---|---|---|---|---|---|---|---|
| 8  | 3     | 12   | 2      | 14,424 | 2,429  | 10  | 0     | 11         | 0        |
| 8  | 3     | 12   | 3      | 14,424 | 5,965  | 18  | 1,910 | 846        | 20 (CB1) |
| 8  | 3     | 12   | 1      | 14,424 | 1,332  | 0   | 0     | 11         | 0        |
| 10 | 3     | 14   | 2      | 22,764 | 224    | 0   | 0     | 0          | 0        |
| 12 | 3     | 16   | 2      | 33,824 | 786    | 0   | 0     | 0          | 0        |
| 8  | 3     | 12   | 4      | 14,424 | 5,886  | 12  | 1,841 | 2,692      | 0        |

* TP23 (2026.4's `dirtyNodeBound`, restated in `Bound.lean`) was not
  exceeded in any of these transactions: one operation a transaction
  is far inside 2026.4's count. The transactions of many deletes are
  in 3.3.
* `up.climb` is reached only from a segment root that the delete
  empties (`up.stop-at-segment-leaf` equals it in every run): no climb
  through an inner node, and LE-b (`leb.*`) is never reached with
  merges on (MD3).

* **The 20 failures of prefix 3 are my check's, not the algorithm's**
  (MF1 below): CB1's computed form first allowed a delete as many merges
  as the tree's height before or after the transaction; a delete raised
  its tree by one level and lowered it again within the operation.
  Corrected to the height and one; TP32's statement (deletes x (H + 1))
  was never wrong.

### 3.3 Transactions of many operations, random runs, the whole model

With `treetest-3` (format 7's `dirtyNodeBound`: TP23 and TP26 are
failures), in one slot, 12:51 to 13:04. "Subsets": every transaction
that deletes (and with puts: or puts) any set of the keys, from the
prefix, then `depth` single operations. Taken back: by merges, of
which the left node or the right one was made by tt.

| Form         | M | Keys | Prefix | States | Merges | Two   | Inner | Taken back (L, R)        |
|---|---|---|---|---|---|---|---|---|
| subsets, del | 8 | 12   | 2      | 4,095  | 8,534  | 428   | 0     | 4,500 (4,285, 215)       |
| subsets, del | 8 | 12   | 4      | 4,095  | 17,077 | 700   | 4,026 | 21,593 (14,020, 7,573)   |
| subsets, all | 8 | 9    | 3      | 19,682 | 38,674 | 2,080 | 1,385 | 27,995 (20,758, 7,237)   |
| subsets, put | 8 | 10 a | 0, +1  | 21,483 | 0      | 0     | 0     | 0                        |
| pairs, depth 2 | 8 | 12 | 2      | 83,232 | 26,786 | 90    | 180   | 2,805 (1,719, 1,086)     |
| random       | 8 | 40   | 20 x 200, <= 12 ops | 4,000 | 1,134 | 100 | 252 | 443 (238, 205) |
| random       | 8 | 25 b | 10 x 200, <= 20 ops | 2,000 | 440   | 25  | 0   | 172 (103, 69)  |

a: the empty key and nine keys under one 7-byte prefix: a transaction
of their puts makes a segment root and splits it (fault 12's rule,
`split.space2.inplace`, 92 times). b: the empty key and 24 keys under
three 7-byte prefixes, half the operations deletes (`split.space2.inplace`
2, RC of segment roots 323).

* **Failures: 0 in every run**: V1, the map, BU1's count, CB1, CB3,
  TP23 with format 7's count, TP26 with merges, A6 (from `treetest-4`
  on, section 4).
* The most merges: 3 in one operation (random, M = 8), 6 in one
  transaction (deletes of 12 keys).
* `treetest model 8 6 60 30 merge`: the whole model on the merged tree
  (records, D, startup), 360 transactions: A2 to A5, TREE, A6', A6,
  A-COPY on every one, T1 and T2: 0 failures.
* The climb's take-back (`up.takeback`) is reached with merges on
  (2,187 times, subsets with puts): a root leaf that a split of tt made
  and the same transaction empties; still a root, as MD3 expects.

### 3.2 Findings

* **MF1. A delete in a full leaf can split its way up and merge back
  down in one operation** (not a fault; a cost). Smallest case: M = 8,
  12 keys, prefix 3, then `put [0]`, then `del [0]`. The leaf of [0]
  and [72] is full of dead klongs (8 klongs, 2 live): the delete's rule
  O makes a time split (a new leaf of 1 live klong, m - 1), whose klong
  overflows the full root: a space split of the root and a new root
  above (height 2); then the merges: the new leaf with its right
  sibling, the first half of the root with the second (both of tt,
  taken back), and RC takes back the new root (`rc.takeback.space`).
  One delete: 6 key nodes made, 4 taken back, 2 merges, 7 rules. The
  model, 024-11 (5.2, step 2: rule O first, then fix) and P5 all do it
  this way. **An option, not taken:** when a full node's last version
  after the delete has m - 1 live klongs, merge that last version with
  the sibling at once (no time split, so no klong of it in the parent).
  It changes what a record means, so it is the model's and Java's
  together, later (one thing at a time). For Java: `dirtyNodeBound`
  must count rule O before a merge, as mgj's count does ("a rule O of
  the child before its merge").

### 3.4 `dirtyNodeBound` of format 7, restated (CB2, TP23, TP26)

mgj's count (024-21, commit `3cd9b4c6`: four klongs in every node of a
delete's path, not two; a node on a delete's path has at most q = max(2,
M / 2 - 3) of room, `overflows`' `merged`; and 4 x (depth + 3) nodes for
each delete) is restated in `Bound.lean`, term by term, when
`Params.format7` (m is set: 1 below node size 8, where Java counts the
merges as a margin and nothing merges; 2 or more from 8). With it TP23
(the key nodes marked are at most the count) is a failure of a run, no
longer a note. **TP26 restated with merges** (the coordinator, 12:28):
`Limits.dirtyNodes` for format 7 is operations x (20 x segments x (H +
2) + 14), for 2026.4's 8 x ... + 2: the delete's klongs doubled, room q
on its path, and the merges' 4 x (segments x (H + 2) + 3). `treetest`
checks both on every transaction (the transaction's own operations and
longest key as its limits), `treecheck` on Java's (C-T8).
`Params.withMerges` gives m = 1 below node size 8, as Java's
`Dag.minFill`.

* **MF2. Outside TP28 the merges fail at once, two ways** (a finding
  about the parameters, not the algorithm). `exhaustive 6 2 9 2 merge`,
  024-11's formulas forced at node size 6 (m = 2, c = 3): 324 states,
  20 failures. (a) FillOK: a space split of a last version of 3 live
  klongs makes a half of 1 (`[put [0]]` twice after the prefix). (b)
  `Bug: merge ... has no sibling`: prefix, `put [0]`, `del [0]`: the
  leaf is full, its rule O's klong fills the full root, whose space
  split makes an inner half with one live klong (the time split's
  node), so the merge below it has no sibling. This is the state P5
  and 024-21 count as "no merge" and skip; it is reachable exactly when
  TP28 fails, which Java excludes by m = 1 below node size 8 (MD6), and
  then a skip would leave V1 broken silently: J1's reason.

## 4. Fault 12, planted

023's fault 12 (023-08, section 4) was a take-back that left a klong of
tt naming a node that is never written. Planted twice, in a copy of the
branch's Lean files (`/Users/f/fl/bench/2026-11-11/mgl/plant/`), never
in the branch:

* **A, fault 12's kind in the merge:** `merge` takes back a node of tt
  without `retarget` (P4's mistake: "the take-back left a deleted klong
  naming a node never written", 024-11, 3.1).
  * The exhaustive runs of 3.1 (single operations) and the delete
    subsets at M = 8, 12 keys (4,095 transactions, 4,500 take-backs by
    merges) **do not catch it**: in all of them the node taken back is
    the left one, whose klong of tt the merge points in place to m1, so
    no klong of tt names it after; the retarget does nothing there.
  * **The random runs catch it** (M = 8, 40 keys, 20 seeds of 200
    transactions): at T(109) of the first seed, a single delete of
    [1224]: TP4, "key node 109004 names 109002, no node of P". The
    case, from the writer's trail: the leaf's merge (one node) takes a
    klong from its parent, which is full: rule O makes a time split of
    it (109002, made by tt, m - 1 live klongs), whose klong fills the
    root: a time split of the root too (109004, a new root, and a new
    top node). Then 109002 is merged with its left sibling, which fits:
    it is the right node R, made by tt; the merge's bitmap in 109004
    deletes R's klong of tt, which still names R when R is taken back.
  * **The exhaustive run with prefix 4 catches it** (nodes full of dead
    klongs, added for this): M = 8, 12 keys, depth 3, 20 failures, the
    smallest at depth 3: the prefix, then `put [0]`, `put [0]`, `del
    [392]`: TP4, "key node 25006 names 27000, no node of P". The same
    run without the plant: 0 failures (3.1).
  * So: the single-operation exhaustive runs reach the merge's
    take-back only in the form that needs no retarget, unless nodes are
    full of dead klongs. The subsets of deletes in one transaction
    (deletes in key order) take back a right node of tt 215 times
    (`merge.made.right`), but never leave a klong of tt in the parent
    that names it: the parent there is the full space root, which rule
    O replaces by its last version (`merge.parent.full`, 3,247 times).
    Prefix 4 and the random runs are in the default set now.
* **B, fault 12 itself:** `split.space2.inplace` (a segment root made
  and split in one transaction) adds a second klong of tt in the
  segment leaf instead of pointing the first in place.
  * **No check of `treetest` as it was catches it**, though the runs
    reach the rule (92 times in the subsets of puts under one 7-byte
    prefix at M = 8; 2 in the random runs with three prefixes; once at
    M = 4 with pairs): the walk, the pointers, the gets and scans all
    pass. The dead klong of tt names the first half, which is a node of
    P and reachable through the new root: nothing dangles. **With one
    operation a key it cannot dangle**: the first half is a node that
    the transaction made fresh, and a delete in the same transaction of
    a key under a segment that did not exist before is a noop, so
    nothing takes the half back; fault 12 needed two operations on one
    key (023-08, section 3).
  * **What it breaks is A6** (024-12, 6.2: no pointer of a reachable
    node to a reachable node that is not its live child), which
    `treetest` checked only in `model` runs (A6', and A6 with merges
    since this item). **A6 is now in every state's checks** (`checkSt`,
    with 024-12's `adoptFailures`). With it the fault is caught at once:
    at M = 8, the first transaction of seven puts under a new prefix
    (A6: the space root's dead klong of tt names the first half); at M
    = 4 (merges off), the prefix of 6 keys and then `[del [120,8], put
    [120,72]]`, `[put [120,8], put [120,72]]`. Without the plant A6
    holds in every run of section 3 (merges on and off).



## 5. Against Java

**How:** mgj's branch has no tree exporter (it is on 024-12's branch
only). A scratch combination,
`/Users/f/fl/bench/2026-11-11/mgl/comb/clone`: this branch's base
`d90586d0` with mgj's `024-21-merges` merged (`f507148d`, no conflict),
and one line in `TraceExport` (the TREE line's thresholds, 2.5); Java
built there, `treeconf.sh` run there with this branch's `treecheck`
(`TREECHECK=`): the draining configurations (UnlinkFuzz's workloads
among them), the small set and reclaim's set, at node sizes 8, 14 and
30; then the medium set (to 62). Scripts `runs/set4.sh`, `hold1.sh`.

### 5.1 Results

* **First trace, 13:07** (one core, no slot; Java built in the
  combination): `d-batch`, seed 1 (node size 8, 200 keys, 60
  transactions of 40 operations, 60 % deletes): TREE line `TREE 8 0 4 1
  2 4`; 2,171 operations, 172 merges (30 into two nodes, 40 of inner
  nodes), 91 nodes taken back by merges; **C-T1 to C-T9: 0 failures**,
  so the model's merge makes Java's nodes, ids, klongs and entries,
  and the model's own run from R(0) writes Java's 61 records and D.
  The risk named in 2.5 (D after a merge) did not show.
* **The three sets, 3 seeds** (13:06 to 13:07, one slot, PAR = 2;
  `runs/comb3-*.log`): every trace TREE OK, every check 0 failures.

| Set     | Traces | Transactions | Operations | Merges | Two | Inner | Taken back |
|---|---|---|---|---|---|---|---|
| drain   | 33     | 4,170        | 76,153     | 8,216  | 456 | 2,681 | 5,341      |
| small   | 21     | 2,130        | 12,020     | 332    | 26  | 64    | 147        |
| reclaim | 15     | 8,784        | 27,369     | 695    | 54  | 119   | 157        |

* So on 15,084 transactions of Java with merges (node sizes 8, 14 and
  30, keys of up to 5 segments, transactions of up to 80 operations,
  reclaim's steps with their touches and cuts), the model's merge makes
  Java's nodes with their ids, levels and klongs, its parent's bitmaps
  and in-place pointers, its take-backs (C-T1, C-T2), and the model
  alone writes Java's records and D (C-T9). **No difference of Java's
  and none of the model's; 024-11's text needed no reading chosen**:
  where it is open (the order of F1 and F2, the node after a change),
  both follow P5.
* **10 seeds** (`hold1.sh`, 13:41 to 13:44, `runs/comb10-*.log`):

| Set     | Traces | Transactions | Operations | Merges | Two   | Inner | Taken back |
|---|---|---|---|---|---|---|---|
| drain   | 110    | 13,900       | 251,395    | 27,167 | 1,605 | 8,946 | 17,732     |
| small   | 70     | 7,100        | 40,260     | 1,050  | 93    | 202   | 440        |
| reclaim | 50     | 29,308       | 91,281     | 2,419  | 177   | 449   | 559        |

  small and reclaim all OK; drain 109 of 110 OK, **one failure, the
  model's (MF3)**: `d-a6-4` (node size 8, long keys, 60 transactions of
  40 operations, 60 % deletes), T(38): the model stopped with `bounds:
  the tree leaves the level bounds: segment 0, height 4; G = 2, H = 3`,
  and C-T9 differed from R(38) on (44 failures, all after it). C-T1 to
  C-T8 passed on every transaction Java's structure gave.
* **MF3. The model refused a transient root above the trace's level
  bounds** (the model's fault, fixed). A trace's G and H are the
  largest of the nodes Java wrote (`TraceExport.levels`). In MF1's
  pattern a delete's rule O splits up to a new root one above them,
  and the merges and root collapse take it back in the same operation,
  so Java never writes it; the model's `newKey` raised `bounds:` as the
  node was made. Fixed in `Exec.lean`: a key node made outside G and H
  is noted (`W.outside`) and is an error only if the transaction does
  not take it back (`boundsOK`, at the end of `runOpsFrom`); the writer
  never reads a new node's level, only its segment and height (`gh`).
  The statements need no change: the change of a transaction holds no
  node outside the bounds, as before. With the fix (commit `8e78cf65`):
  `d-a6-4` TREE OK, C-T1 to C-T9, and all 110 drain traces again OK. Found by Java's traces, not by `treetest`, whose runs
  have H = 8 and never reach it: a reason for "Java checked against
  the model" beside the model's own runs.
* **The medium set**, 1 seed (13:44 to 13:59, `runs/comb1-medium.log`,
  the checker before MF3's fix): 9 traces OK, node sizes 8 (3), 14,
  30 (4) and 62; 4,569 transactions, 246,174 operations, transactions
  of up to 200 operations; 7,101 merges (2,301 into two nodes, 1,134 of
  inner nodes), 4,162 nodes taken back by merges; C-T1 to C-T9 all 0.
* V1 (`FillOK`) holds on Java's tree after every transaction (C-T6);
  LE-b is never reached; the climb only from emptied segment roots.
* **`tracecheck` on the 15 reclaim traces of Java with merges**
  (`runs/reclaim3/`, one core): TRACECHECK OK on all, 8,799
  transactions: C-A (A2 to A5, TREE, A-COPY) and A6 (no adoption below
  the old parent) on every one, C-S, and **every one of the 180 cuts**
  (C-CUT with CUT-live, I2 of 024-07: every index node reachable at the
  iteration's end has a value below it, TP27): merges keep it.
* C-T8: format 7's `dirtyNodeBound` holds on every transaction, with
  room: drain 70,078 key nodes marked against 1,703,233 counted (24
  times; 2026.4's count had 4.5 times on its drain set, 024-12, 5.2).
  A record limit is reached by the count first: a cost of CB2's simple
  count (QU7), mgj's to weigh (J7).


## 6. Proofs

Proved (`lean/SIS/Tree/MergeProps.lean`; `#print axioms`: propext,
Quot.sound and, for the first, Classical.choice, Lean's own):

* `mergeParamsOK_withMerges`: TP28 for 024-11's thresholds at every
  node size from 8 (omega on m = max(2, M / 4), c = M / 2).
* `not_mergeParamsOK_six`, `_four`: 024-11's formulas fail TP28 at 6
  and 4 (by `simp`).
* `mergeSizeOK`: TP34, the sizes of the merge's nodes.
* `mergeKeepsKlongs`: TP35, the merge keeps the pointers in order, and
  in a segment leaf the klongs themselves (with `mergeList_length`,
  `mergeList_ptrs`, `renameHead_*`).
* `mergeFillOK`: TP36, the local part of 024-11's "why V1 holds": with
  TP28, a merge of n live klongs, m <= n <= m - 1 + M - 1, makes nodes
  of at least m live klongs that fit in a node (from TP34, by omega).
* `splitFillOK`: TP37, the other local part: with TP28, each half of a
  space split (`halves`, 024-12's, of a last version of more than M / 2
  klongs) holds at least m key klongs (by the lengths of `take` and
  `drop`, the inner half's renamed first klong, omega). With TP36 and a
  time split keeping its count, every node that a transaction makes
  holds m or more: what remains of V1's proof is that a delete lowers a
  count by one and the loop then merges (TP30, the large part).

What remains, with sizes (a guess, as 024-12's section 6):

* **Small:** that `mergeKlongs`' nodes are sorted and the parent's new
  compare value g lies between them (from TP35 and the order of the
  live klongs).
* **Medium:** TP32 (CB1), by the loop's shape: `mergeUp` makes one merge
  a height and stops at a root; with the fuel, an induction. TP31 from
  V1, V2, V4 on layer A (a counting lemma on trees).
* **Large, the B-tree proof** (024-12's TP7) with V1 in it: TP30. Each
  rule of 3.1's reach list, the merge's four parent cases and the
  take-back, keeps the walk's invariants; one to two weeks, as 024-12
  says, plus the merge's cases (perhaps a third more).
* **Large, on top:** TP33 (CB3), the potential argument of 024-11 (5.5)
  over a run; TP23 with format 7's count (Java's argument, "not a
  proof", 024-21).


## 7. For Java

For mgj (024-21), kept current; newest last.

* **J1 (12:30). P5's three skips should be a `Bug`** (MD2): `merge`'s
  `return 0` for no sibling, for an empty L or R, and for an inner L or
  R whose first live klong is not the empty key (`statMergeSkipped`).
  The model makes each an error and no run reaches one; with V1 to V3
  none can happen, and a skipped merge would leave a node under m.
* **J2 (12:30). The TREE line** of `TraceExport` (tree=1, on 024-12's
  branch): `TREE M G H k minFill(M) mergeCap(M)`; `treecheck` reads 5
  or 7 tokens. One line; in my scratch combination (section 5).
* **J3 (12:30). The model agrees with your structure**: P5's three
  calls of `mergeAfterDelete` in `deleteUpward`, `collapseRoot` after a
  merge, `minFill` 1 below node size 8 (`withMerges` now the same). It
  finds the node after a change by segment and height, not by depth and
  the counts `fullNodes`, `newRootsMade` (MD4): the same node; nothing
  asked.
* **J4 (12:30). MF1**: a delete in a full leaf can make a time split, a
  root split and a new root, then merge twice and collapse the root, in
  one operation (3.2). Correct; your `dirtyNodeBound` counts the rule O
  before a merge. A unit test of it, in key order: the empty key, eight
  keys of one segment and four of two segments (three under one 7-byte
  prefix, one under another), as `treetest`'s `testKeys 12` (compare
  values `[0]`, `[72]`, `[120,8]`, `[120,72]`, `[120,144]`, `[136]`,
  `[184,136]`, `[200]`, `[264]`, `[328]`, `[392]`, `[456]`, ordered as
  numbers, segment by segment); at node size 8 each put in its own
  transaction, all again in one, then a put of the empty key, then its
  delete.
* **J5 (12:30). The retarget of a merge's take-back** is needed when
  the right node R was made by the transaction and the merge deletes
  R's klong (section 4, A); single deletes reach it only in nodes full
  of dead klongs (overwrites), a fuzz with repeated keys does.
* **J6 (12:36). The trace combination exists**: 
  `/Users/f/fl/bench/2026-11-11/mgl/comb/clone`, branch `comb`: 024-12's
  `d90586d0` with your `f507148d` merged (no conflict) and J2's TREE
  line (uncommitted there, one line of `TraceExport`). I run
  `treeconf.sh` there (section 5); your planned trace branch is not
  needed for the comparison. When 024-12 is on `main`, J2's line goes
  with your branch.
* **J8 (14:05). 10 seeds and the medium set agree too** (5.1): 239
  traces, 54,877 transactions, 37,737 merges. The one failure was the
  model's (MF3: a transient root above the trace's level bounds);
  nothing for Java.
* **J7 (13:10). Your `f507148d` agrees with the model** on every trace
  of `treeconf.sh` drain, small and reclaim (3 seeds; section 5.1):
  15,084 transactions, 9,243 merges, C-T1 to C-T9 all 0. Format 7's
  `dirtyNodeBound` is 24 times the nodes marked on the drain set (2026.4's
  count was 4.5 times): no fault, but it brings the record limit's
  refusal near (your "about 120,000 deletes" at node size 30).

## 8. Gates

| Gate                                   | Result                                 | On         |
|---|---|---|
| `lake build` (all targets)             | OK, 180 jobs                           | `ad3707eb` |
| grep in the tree's Lean files          | no sorry, axiom, admit, native_decide  | `ad3707eb` |
| `#print axioms` of the 7 theorems      | propext, Quot.sound, Classical.choice  | `ad3707eb` |
| `treetest` (whole default set)         | TREETEST OK, 31 min, one core          | `63e39de6` |
| `treeconf.sh all 5`, own Java          | TREECONF OK, 115 traces                | `ad3707eb` |
| Java with merges, 10 seeds (5.1)       | 230 traces OK (after MF3's fix)        | `8e78cf65` |
| Java with merges, medium set           | 9 traces OK                            | `ad3707eb` |
| `level2.sh`                            | not run yet                            |            |

* `treetest`'s default set: 024-12's runs (merges off, node sizes 4 to
  8; 340,000 states; random; `model`), now with A6 checked on every
  state: 0 failures, so 2026.4's tree keeps A6 in all of them; then the
  merge set (`runMergeSet`, 10 runs, 164,000 states, `model` with
  merges): 0 failures.
* On `8e78cf65` (MF3's fix: the bounds check at the transaction's end)
  so far: `lake build treetest treecheck`, `treetest exhaustive 8 3 12
  4 merge` and `exhaustive 4 3 5 2 pairs` (0 failures), the 110 drain
  traces of Java with merges (all OK). To run on it: `level2.sh`, and
  `treeconf.sh all 5` again.
* The branch changes no Java, so `before-commit.sh` is not a gate of
  it; `treeconf.sh` and `level2.sh` check the changed checker against
  2026.4's Java (merges off), where nothing should move.


## 9. Questions for Frans

Each with a default that the work follows until he says otherwise.

* **QM1. P5's way for 2026.5** (024-11's QU6): new nodes and the
  take-back, as now in the model and in Java, which agree on every
  trace. The other way (in place and net) removes the one case that
  needs the retarget and MF1's waste, at the price of a change to what
  a record means (2.9). **Default: P5's way in 2026.5;** the other way
  is a candidate for when the format is made stable (2026.6).
* **QM2. MF1's option**: a delete that leaves a full node's last version
  at m - 1 merges it at once, with no time split first. **Default: not
  now;** first count how often it happens at 1M to 10M keys (024-21's
  numbers can say).
* **QM3. "No merge" as a `Bug`** (J1; 024-21's QJ3). **Default: yes**,
  as 024-21 recommends, after its fuzz night: MF2 shows that the state
  is reachable exactly when the thresholds break TP28.
* **QM4. A6 required** (024-12, 6.2, planned it): `treetest` checks it
  on every state since this item, and no run of 2026.4's tree or of the
  merged one breaks it; fault 12 itself is caught only by it. **Default:
  keep it in `treetest`**; `tracecheck` and the gates follow 024-12's
  plan.
* **QM5. Format 7's `dirtyNodeBound`** counts 24 times the nodes marked
  on the drain set (2026.4's: 4.5): a transaction of deletes is refused
  at about 120,000 at node size 30 (024-21). **Default: CB2's simple
  count (024-11's QU7) for now;** a sharper count is a later change of
  Java and of `Bound.lean` together.


## 10. Log

2026-11-11, 11:50. Started (agent "mgl" of coord-1111). Read the common
brief, 024-04, 024-11, 024-12, the tree model's Lean files, P5's merge
(`023-p5-merge`, `71e386de`) and `main`'s `deleteUpward`.

11:55 to 12:08. The clone (from 024-12's `5b6843cf`), the merge in
`Exec.lean`, V1 in `walk`, `treetest` with merges; first compiles on one
core (no slot: no timing run then).

12:05 to 12:16. The design note (section 2); `MergeProps.lean` and its
proofs; the first exhaustive runs (3.1), one core.

12:16 to 12:25. MF1 found and the CB1 check corrected; fault A planted
and run (section 4). **A mistake:** thr's timing hold began at 12:23:18
and two of my single-core runs went on until 12:25:37, as I had not
read the owner files before starting the second; stopped, told the
coordinator twice (the second time for the run my process listing had
missed). Since then every run of mine goes through `slot.sh take`.

12:26 to 12:30. Rebased onto 024-12's gated head `d90586d0` (no
conflict); format 7's `dirtyNodeBound` restated from mgj's commit, TP26
restated with merges, `withMerges` as `Dag.minFill`; the scratch
combination with mgj's branch (section 5).

12:30 to 12:51, nothing run (thr's timing hold): TP36 written, A6 in
`model` runs with merges, the run scripts, J1 to J6.

12:51 to 13:04, one slot (set3): the build, 3.3's runs, fault B (not
caught), then A6 in every state's checks and fault B caught; MF2.
13:00, commit `63e39de6` after `lake build` (180 jobs).

13:06 to 13:15. Java with merges against the model (set4, one slot):
every trace of drain, small and reclaim OK (5.1); `tracecheck` on the
reclaim traces OK, every cut with I2. TP37 proved in the plant copy
(to commit after the gates).

13:08 to 13:40. Waited for a slot (asked the coordinator at 13:34);
`treetest`'s default set on `63e39de6` on one core meanwhile (OK, A6
on 2026.4's runs too). 13:38, TP37 committed (`ad3707eb`).

13:40 to 13:59, one slot (`hold1.sh`): `lake build`, `treeconf.sh all
5` (OK), Java with merges with 10 seeds: one drain trace failed, MF3,
the model's; fixed and committed (`8e78cf65`) at 13:50, all 110 drain
traces rechecked OK; the medium set OK.


## 11. State

Written 2026-11-11, 14:05 (agent "mgl" of coord-1111).

* **Branch** `024-22-merges-lean` in
  `/Users/f/fl/bench/2026-11-11/mgl/clone`, three commits on 024-12's
  gated head `d90586d0` (not on `main`; it needs 024-12 to land first):
  `63e39de6` (the merge, V1, TP28 to TP36, format 7's count, TP26,
  `treetest` with merges and A6, `treecheck`'s TREE line), `ad3707eb`
  (TP37 and its proof), `8e78cf65` (MF3's fix). Lean only; no Java.
* **Done:** sections 2 to 7; the runs of section 3; faults A and B
  (section 4); Java with merges, 10 seeds of three sets, `tracecheck`
  on reclaim traces (5.1); the gates of section 8's table.
* **Running:** `runs/hold2.sh`, `level2.sh` on the head `8e78cf65`,
  in a slot since 13:59 (log `runs/hold2.log`, `runs/level2-g.log`).
* **Not done:** `level2.sh` on the head (running); `runs/set5.sh` (deeper runs: node sizes 14 and 30, 1,000
  transactions); the proofs of TP30 to TP33.
* **Copies:** `mgl/plant/lean` (planted faults; clean, with a `debug6`
  mode in `TreeTest.lean`), `mgl/comb/clone` (branch `comb`:
  `d90586d0` + mgj's `f507148d` + J2's TREE line, uncommitted; Java
  built there).
* **To continue:** read `runs/hold2.log`; then `set5.sh`. Every script in
  `runs/` takes its own slot with `slot.sh`.
