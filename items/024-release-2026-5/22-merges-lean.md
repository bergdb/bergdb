# 024-22. Merges at the delete in the Lean tree model

Created 2026-11-11 by Frans Lundberg. Status: open: on `main` since
`67925924`, the first proofs since `2a7bdc52`; TP30 to TP33 not proved
(024-28, section 6), the second prover's runs go on.

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

Final for today; section 11 has the exact state; section 9 the questions
(Frans took the defaults at 14:34). Written 16:05.

* **What the model defines.** The merge at the delete in 024-12's Lean
  tree (branch `024-22-merges-lean`, head `90eb124a`, with `main` since
  024-12 landed there): 024-11's algorithm as P5 placed it in release
  2026.4's `deleteUpward` and as mgj ports it to Java (024-21): after a
  delete changes a node, a node that is not a segment root and holds
  fewer than m live klongs is merged with a sibling (one new node, or
  two when they hold more than c), the parent is checked in turn, then
  root collapse; merged nodes are new nodes, a node of the transaction
  is taken back with its klongs repointed (024-11's QU6, P5's way; 2.9
  says what the model shows about the other way). The thresholds are
  parameters, not literals (`Params.mergeBelow` m, `mergeMax` c, and
  since 14:40 rule O's `splitAbove` h); `withMerges` gives Frans's
  8/17/17 of 14:34 for node size 30 (024-14's m8), scaled as v B / 30
  for other sizes, no merge below 8, the same as 024-21's Java (2.1a).
  The runs and the comparison below used 024-11's m = max(2, B / 4), h =
  c = B / 2, which are the same at the test sizes 8 to 14 and differ at
  30 and 62. About 300 lines in `Exec.lean`; no rule of 2026.4
  changed, and with m below 2 the model is 2026.4's tree, run for run.
* **What the runs covered before Java** (section 3; `treetest`, one
  core): exhaustive sequences at node sizes 8, 10 and 12 after four
  kinds of prefix, every subset of a transaction's deletes (or puts and
  deletes), pairs, random runs, the whole model (records, D, startup):
  about 315,000 states with merges (node sizes 8 to 14; at 8/17/17 also
  30 and 62), and 024-12's 340,000 without. After every transaction: V1 and the other invariants, the map (gets at
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
* **Properties** (2.7, 6): stated TP28 to TP38 (the thresholds'
  conditions, V1, TH2, TH3 as BU1's count, CB1, CB3, the merge's sizes,
  klongs and fill, the split's fill); V2 to V9, TH1 and I2 are 024-12's
  statements, which with merges speak of the merged tree;
  `dirtyNodeBound` of format 7 restated from Java and TP26 with merges.
  **Proved:** TP28 from node size 8 (and its failure at 4 and 6), TP34
  to TP38: every node a merge or a space split makes holds m or more,
  and a merge's nodes are in order.
  Left: TP30 (V1 kept, the B-tree proof) and TP31 to TP33.
* **8/17/17** (2.1a, 5.2; 14:35 to 15:02): the model and the count
  follow 024-21's move term by term; TP28 proved for the new formulas;
  short runs at node sizes 8, 14 and 30 pass; **mgj's 21 traces at
  8/17/17 equal the model** (4,080 transactions, 5,655 merges; C-T1 to
  C-T9, and `tracecheck` with A6), and with h = 15 they would not (the
  control); in my combination with 10 seeds and the medium set, 239
  traces, 54,877 transactions, 36,923 merges: all equal; BU1's count
  holds on Java's tree after every transaction of all 260 traces.
* **Gated** (section 8): on `e32eb6d9` (8/17/17, `main` merged in),
  `lake build` (no sorry or axiom), `level2.sh` full (LEVEL 2 OK, its
  step 8 the tree model against `main`'s Java) and the whole `treetest`
  set (TREETEST OK, 30 min); on the head for landing, `90eb124a` (BU1's
  count in `treecheck`, active only with merges), `lake build`. Java
  with merges is not a gate here (024-21's branch, compared in a
  combination and by mgj's traces); int gates the combined head.
* **Landing:** this branch's head `90eb124a` is in int's combined
  landing head (`024-13-int-m`) with 024-21; the coordinator lands
  them together.
* **For Java (mgj):** section 7, J1 to J9.

## 2. The design note

### 2.1 The assumptions "for now", as parameters

Frans's three questions of 11:44 (024-14's), answered "for now" by
024-11's values, each a parameter of the definitions, not a literal (as
first written; the thresholds since 14:34 in 2.1a):

| What                    | Value until 14:34         | In the model                   |
|---|---|---|
| node size B             | 30 (8 to 62 in tests)     | `Params.M`, as before          |
| m, the least fill       | max(2, B / 4): 7 at 30    | `Params.mergeBelow`            |
| c, the merge's cap      | B / 2: 15 at 30           | `Params.mergeMax`              |
| h, a time split's most  | B / 2, today's rule O     | `Params.splitAbove` (14:40)    |
| dead klongs             | nothing beyond the merge  | no change                      |
| how merged nodes made   | P5's: new nodes, take-back | `merge`, `mergeParent`        |

* `Params.withMerges` sets m and c from M by 024-11's formulas; the
  default `mergeBelow = 0` is release 2026.4 (no merge), so every run of
  024-12 is unchanged. Merges are on when m is 2 or more.
* h stayed the literal `M / 2` of rule O, as in 2026.4, until 8/17/17
  made it a parameter (2.1a).
* **The thresholds must meet `MergeParamsOK`** (TP28, section 2.7): 2 <=
  m; a merge into two nodes gives each at least m, m <= (c + 1) / 2; a
  space split's smaller half has at least m, m <= h / 2; the nodes
  made fit, c and h at most M - 2. **024-11's values meet it from M = 8 on, and not
  at M = 4 or 6**: at 6, m = max(2, 1) = 2, and a space split of a last
  version of 3 live klongs makes a half of 1. So the runs with merges are
  at node sizes 8, 10 and 12 (and 14, 30 in Java's traces); 4 and 6 run
  2026.4's tree only. Proved for every M >= 8 (section 6).

### 2.1a The thresholds decided: 8/17/17 (Frans, 14:34)

Frans decided at 14:34 024-14's m8 for B = 30 (QT1): m = 8, h = 17,
c = 17; QT2 (other node sizes) open, the test sizes scaled as 024-14's
build scales them, v B / 30 with m at least 2. In the model since
14:40 (section 10's log):

* **h is a parameter now**, `Params.splitAbove` (default M / 2, 2026.4's
  rule O), read by `handleFullWith` (`Dag.splitAbove`).
* **`withMerges`**: m = max(2, 8 M / 30), h = c = 17 M / 30 from node
  size 8; m = 1 below (no merge, as Java). So 2/4/4 at 8, 2/5/5 at 10,
  3/6/6 at 12, 3/7/7 at 14 (024-11's values there too: every run of
  section 3 at these sizes stands), 8/17/17 at 30, 16/35/35 at 62.
* **TP28** reads h: m <= h / 2 (a space split's halves), and c and h at
  most M - 2 (Java's check in 024-14's build). Proved for the new
  formulas from node size 8 (`mergeParamsOK_withMerges`), and for the
  old ones too (`mergeParamsOK_p5`). TP37 reads h.
* **The TREE line** gets h too: `TREE M G H k m c h` (J9); 5 or 7
  tokens still read, with h = M / 2.
* **`dirtyNodeBound`** restated from mgj's head `0281018e` (024-21's
  move to 8/17/17, commit `7fccc2d7`): the room after a replacement is
  q = max(2, min(M / 2, M - h, M - c) - 3) (`roomAfterReplacement`, 10
  at node size 30; 2026.4's max(2, M / 2 - 3) without merges), in every
  overflow count, the fresh trees' too. Nothing else of the count
  changed there.
* **Runs at 8/17/17** (`runs/short-817.log`, `m30.log`; one core):
  exhaustive 8 3 12 4 (14,424 states), random at node size 14 (5 x 200
  transactions), at 30 (10 x 300 transactions of up to 30 operations
  on 100 keys, half deletes: 3,000 states, 87 merges) and at 62 (3 x
  300, 900 states), `model` at 30 (4 x 150 transactions; T1, T2, A6):
  0 failures.
* **Java and the model agree on the formulas**: `Dag.minFill`,
  `splitAbove`, `mergeCap` at `0281018e` are `withMerges`' three, term
  by term (m = 1 below 8; h = 17 B / 30 at every size).

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
| 31 | `NodeCountBound`      | TH3, BU1's count: key nodes <= S + (n +    | S, T |
|    |                       | S - 1) / (m - 1) at every time             |      |
| 32 | `MergeOpBound`        | CB1: a transaction's merges <= its         | S    |
|    |                       | deletes x (H + 1); since 2026-11-12 for a  |      |
|    |                       | transaction as Java gives it (024-16):     |      |
|    |                       | sorted, keys well formed, a fresh base.    |      |
|    |                       | Without them false (`MergeOpBoundAny`)     |      |
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
| 38 | `MergeOrderOK`        | V3 at a merge: its nodes in compare order, | PROVED |
|    |                       | the first below the second's bound g       |      |
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
* **Later, `set5.sh`** (14:14 to 14:31, one slot, `treetest-head` of
  `8e78cf65`; stopped at 14:31 for int's re-gate of 024-12, as the
  coordinator asked): every transaction of puts and deletes on 10 keys
  after prefix 4 at M = 8, 59,048 states, 123,936 merges, 133,426
  nodes taken back, 0 failures; random at M = 14, 10 seeds of 300
  transactions of up to 16 operations on 80 keys, 3,000 states, 285
  merges (29 into two nodes, 20 inner), 0 failures. Not finished:
  random at M = 30, 1,000 transactions at M = 8, `model` at M = 14,
  the exhaustive depth 4.
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


### 5.2 At 8/17/17

* **mgj's traces** (`/Users/f/fl/bench/2026-11-11/mgj/traces-m8/`,
  branch `024-21-merges-trace` at `4dbd7582` = 024-21's `0281018e` +
  `d90586d0` + the TREE line `TREE 30 0 2 1 8 17`; 7 configurations x
  3 seeds), checked at 15:00 in one slot (`runs/hold4.sh`, outputs in
  `runs/m8/`): 21 traces, node sizes 8 (12), 14 (6) and 30 (3); 4,080
  transactions, 107,965 operations, 5,655 merges (1,332 into two
  nodes, 639 of inner nodes), 4,110 nodes taken back by merges.
  **`treecheck`: TREE OK on all 21, C-T1 to C-T9 0 failures;
  `tracecheck`: TRACECHECK OK on all 21** (C-A with A6, C-S; no
  reclaim, so no cut).
* **BU1's count on Java's tree** (`treecheck`'s C-T6 since `90eb124a`:
  after every transaction, the key nodes reachable at most S + (n + S -
  1) / (m - 1), n and S from the tree's own scan): mgj's 21 traces pass
  it, and so do the combination's 239 traces (`runs/bu1-comb.log`,
  16:01).
* **Their TREE line has no h**: a line of 7 tokens now gives h = c
  (commit `e7b66354`), as h = c in every set a writer of format 7 has
  had (P5's B / 2, m8's 17 B / 30). **Control:** the same trace with h
  = M / 2 = 15 (the checker before) fails C-T1 in 176 of 200
  transactions: the comparison sees h.
* **My combination at 8/17/17** (`mgl/comb/clone`: `d90586d0` +
  024-21's `0281018e` + the TREE line with m, c and h; `runs/hold3.sh`,
  15:02 to 15:19, one slot; `runs/comb817-*.log`): `treeconf.sh` drain,
  small and reclaim with 10 seeds, medium with 1: **239 traces, all TREE
  OK**, 54,877 transactions, 629,146 operations, 36,923 merges (3,516
  into two nodes, 10,721 of inner nodes), 21,816 nodes taken back by
  merges; node sizes 8, 14, 30 (8/17/17) and 62 (16/35/35); C-T1 to
  C-T9 0 failures, reclaim's steps and cuts included.

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

* **Done since:** `mergeOrderOK`, TP38 (15:10): with the two nodes'
  live klongs in compare order and bounded by R's compare value in the
  parent, the merge's nodes are in compare order and the first's below
  g (lists: `Pairwise`, `take` and `drop` of a sorted list, the inner
  renames; first try).
* **Tried at 15:25 to 15:35, put off: TP32 by frame lemmas** (each
  action of the writer keeps the merge count, `merge` adds one; in
  `mgl/plant/lean/SIS/Tree/MergeFrame.lean`, not on the branch). The
  monad's own lemmas went fast (pure, throw, bind, read, get, modify,
  `note`, `fresh`); the writer's functions with matches applied to the
  reader and the state (`getNode` and every function above it) need a
  case split each by hand, about 35 of them: a day, or a `do`-aware
  simp set first. A form with the loop's fuel, merges <= deletes x
  ((G + 1)(H + 2) + 2), is no easier: the frame is the work.
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
* **J7 (13:10). Your `f507148d` agrees with the model** on every trace
  of `treeconf.sh` drain, small and reclaim (3 seeds; section 5.1):
  15,084 transactions, 9,243 merges, C-T1 to C-T9 all 0. Format 7's
  `dirtyNodeBound` is 24 times the nodes marked on the drain set (2026.4's
  count was 4.5 times): no fault, but it brings the record limit's
  refusal near (your "about 120,000 deletes" at node size 30).
* **J8 (14:05). 10 seeds and the medium set agree too** (5.1): 239
  traces, 54,877 transactions, 37,737 merges. The one failure was the
  model's (MF3: a transient root above the trace's level bounds);
  nothing for Java.
* **J9 (14:40). 8/17/17**: the model has h as a parameter and record
  format 7's thresholds as 024-14's build scales them (2.1a). For the
  comparison the TREE line needs h too: `TREE M G H k minFill(M)
  mergeCap(M) splitAbove(M)` (my combination writes it). Tell me (your
  item's "For the model") when your head has 8/17/17 and its
  `dirtyNodeBound` for it; I restate the count and run `treeconf.sh`
  against it.


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
| `lake build` (all targets)             | OK, 180 jobs                           | `8e78cf65` |
| `level2.sh` full (its step 8: treeconf) | LEVEL 2 OK, 15 min                    | `8e78cf65` |
| `lake build`; `level2.sh` full          | 180 jobs; LEVEL 2 OK, 15 min          | `e32eb6d9` |
| `treetest` (whole default set, A6)      | TREETEST OK, 30 min, one core         | `e32eb6d9` |
| `lake build`                            | 181 jobs                              | `90eb124a` |

* `treetest`'s default set: 024-12's runs (merges off, node sizes 4 to
  8; 340,000 states; random; `model`), now with A6 checked on every
  state: 0 failures, so 2026.4's tree keeps A6 in all of them; then the
  merge set (`runMergeSet`, 10 runs, 164,000 states, `model` with
  merges): 0 failures.
* On `8e78cf65` (MF3's fix: the bounds check at the transaction's end):
  `lake build`, `treetest exhaustive 8 3 12 4 merge` and `exhaustive 4
  3 5 2 pairs` (0 failures), the 110 drain traces of Java with merges
  (all OK), and `level2.sh` full (13:59 to 14:14, LEVEL 2 OK): its step
  8 ran `treeconf.sh` at full size on the branch's own Java (small 70
  traces, drain 110, reclaim 15: 29,794 transactions), its step 7
  `conformance.sh` (70 traces, and drain 50, TRACECHECK OK), and the
  take's check.
* The branch changes no Java, so `before-commit.sh` is not a gate of
  it; `treeconf.sh` and `level2.sh` check the changed checker against
  2026.4's Java (merges off), where nothing should move.


## 9. Questions for Frans

Each with a default that the work follows until he says otherwise.
**Decided (Frans, 2026-11-11, 14:34): QM1 to QM5 as the defaults**
(the coordinator's message).

**Decided: QM1 to QM5 as their defaults** (Frans, 2026-11-11, 14:34,
asked whether the five defaults are all right: "2, yes.").

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


14:31. `set5.sh` stopped and its slot released for int's re-gate of
024-12 (the coordinator). 14:34, Frans: 8/17/17 (024-14, QT1), QM1 to
QM5 as the defaults.

14:35 to 14:50, no slot, one core: h as a parameter, `withMerges` as
format 7's 8/17/17 scaling, TP28 and TP37 with h (proved), the count's
room as mgj's `roomAfterReplacement` (from 024-21's `0281018e`), h on
the TREE line; `lake build` (180 jobs); short `treetest` runs (2.1a);
commit `37e8fbb0`. The combination re-merged with 024-21's
`0281018e`. `hold3.sh` (Java at 8/17/17 against the model) waits for
15:30.

14:56 to 15:02. 024-12 on `main` (`b84cf761`); `main` (`944e6944`)
merged into the branch (`447d3f0e`, no conflict, no Lean file changed
by it; `lake build` OK). mgj's traces at 8/17/17 checked (5.2): all
OK, after the TREE line of 7 tokens gives h = c (`e7b66354`); reported
to the coordinator.

15:20 to 15:45. `level2.sh` on `e32eb6d9` (LEVEL 2 OK). TP38 proved.
TP32 by frame lemmas tried and put off (section 6). BU1's count in
`treecheck` (`90eb124a`), mgj's 21 traces pass it. mgj's TREE line of 8
tokens (m, c, h) checked: read as such. Head for landing given to the
coordinator: `90eb124a` (the int agent lands 024-21 and 024-22 together
on a combined, gated head).

15:45 to 16:05. `treetest`'s whole default set on `e32eb6d9` OK; BU1's
count on the combination's 239 traces OK. The branch is in int's
combined landing head (`024-13-int-m`). Wrapped up at the coordinator's
word: `set6.sh` skipped for today, the proofs left for a later agent
(section 11), dead klongs to "o2" (024-23).

2026-11-12: TP32 restated with the premises Java meets (Frans, 07:26);
the unconditional form is false (two counterexamples, `08559fff`).
`MergeOpBound` now takes, of the final transaction, `NoBug`'s premises,
which `Within` puts on every earlier one: sorted (one operation a key,
in key order, since 024-16, S3), keys well formed, a fresh base. The
old form is `MergeOpBoundAny`, which the two counterexamples refute
(neither transaction is sorted). TP32 follows from the old form, or
from a premise on the heights the writer reaches
(`mergeOpBound_of_transientHeight`, `mergeOpBound_of_outsideHeight`).
Not proved. `treetest` checks CB1 per operation, on sorted transactions
only; `treecheck` does not check it. Branch `024-22-tp32-restate`, head
`cb57e5c8` (agent "tp32s"), `lake build` OK (215 jobs).

2026-11-13, agent "cost" (coord-1113): TP32 and TP33, not proved.
Branch `024-22-cost`. Proved, with no premise: a transaction's merges
into two nodes are at most its deletes that deleted
(`execW_twoMerges_le_deletes`: `mergeUp` returns after one, and a delete
runs it at most once; the frame lemmas for the note "merge.two" are in
`MergeTwoFrame.lean`, about 260 s to build). TP33 reduced
(`MergeNodeCount.lean`): from the step of any potential that is zero on
R(0) (`mergeAmortized_of_potentialStep`); with the count of the reachable
key nodes that are not the root of their segment tree (`nonRootCount`, no
fill needed) to `NodeCountStep`; and with the bound above to
`OneMergeStep`: that count at P@i and the merges into one node at most
that count at P@(i - 1) and twice the space splits
(`mergeAmortized_of_oneMergeStep`). A merge into one node removes one
such node, a space split adds at most two, nothing else adds one. The
step held on every transaction of random runs (scratch, not kept: M = 8,
H = 2, G = 0 and 1, theta on and off, about 1,200 transactions). It held
for each operation too, with the count taken on the writer's own tree
(its nodes over P@(i - 1), from its super root, at time i: 13,000
operations at M = 8 and 10), and that count equals the count of P@(i - 1)
before the first operation and of P@i after the last. So a proof goes by
operation, as TP10's get in `GetWriter.lean` (`MergeNodeCountOps.lean`):
the count on the writer's first state is P@(i - 1)'s (`initCountOK`,
proved); on its last state it is P@i's, from the lift of the writer's key
nodes (`commitCountOK_of_lift`; `CommitLiftOK` is TP10's premise too);
and each operation keeps the step (`OpCountOK`, open). So TP33 follows
from `OpCountOK` and `CommitLiftOK` (`mergeAmortized_of_opCount_lift`).
`OpCountOK` needs the writer's tree to be a tree between operations: TP7's
B-tree proof carried through a transaction.

TP32: open; the gap is still a premise on the heights the writer reaches
(`mergeOpBound_of_transientHeight`). TP7 does not give it: TP7 speaks of
the trees between transactions, and a prefix of the transaction that
ends above H fails `boundsOK`, so it is no run within reach. Searches
(scratch, M = 8): no sorted counterexample. At H = 0, every sorted
transaction over 14 to 16 key positions from 7 initial trees, cut where
its deletes passed its merges by more than 1 to 3; at H = 0 and 1,
random ones, 20,000 to 50,000 a tree, theta on and off, and at H = 0 six
sets of thresholds outside TP28. In the random ones no successful
transaction reached height H + 2. A route, not formalized: in a sorted
transaction no later operation reaches a key below the current one. A
node whose keys are all below it holds m or more live klongs (V1), so it
is never the merged node, only a sibling that the merged node joins;
and a split keeps the smallest m or more in its first half. So the nodes
of a height with m or more such children never become fewer. One at
height H + 1, or two at H in one segment tree, keep that tree above H to
the end, and `boundsOK` fails. A root at H + 2 needs one at H + 1 with h
or more children, made by splits at H whose left halves become such
nodes as the operations pass them; what is left to show is that too few
of them can stay ahead of the operations. It needs V1 and the key ranges
of the writer's tree between operations, that is TP7 within a
transaction. At M = 8 by hand they are too few; at larger M and H it is
not clear (dense trees give more), and if a successful sorted transaction
can reach H + 2 there, TP32 may still hold, by the deletes that merge
less, but then it needs a potential, not a bound on the heights.

TP32's heights, the night of 2026-11-13 to 14 (cost; 024-12's (4) entry,
step 4 (A) to (C)): the writer's heights are now a proved walk, which TP32's
open premise (`mergeOpBound_of_transientHeight`, a bound on the heights the
writer reaches) can use.
- Every key node's height is exact in the writer's overlay at every state
  of a transaction (`HtInv`), and so after every run (`HeightAllOK`), given
  `OpDelChkOK` (`treeRun_heightLiveOK_chk`).
- A split's cascade, a delete's bitmap and a merge each add at most one to
  the largest cached height (`seenHeight_appendDeleteKlong`,
  `seenHeight_appendKlongs`, `seenHeight_merge`; `HeightsFuel.lean`,
  `HeightsFuelMerge.lean`). The bound for a whole operation is not proved.
- Runs (`12-tree-model/heights-op-check.lean.txt`): in 18201
  operations of 316 runs within reach, the nodes an operation made were at
  most one above the nodes it found, in every segment.

The writer's tree (asked by the coordinator at 12:55, ahead of TP32):
`WriterTreeOK` (`WriterTree.lean`), the writer's nodes over P@(i - 1), read
at time i from its super root, are a tree: every live klong is a link (in
a leaf too, so a value or the next segment's root), no reached node names
the root, and each node is named by one reached node under one compare
value. `TLink` was widened to every live klong so that `TreeOK` is TP10's
TREE premise (`htree_of_treeOK`); it gives the uniqueness of the key's
search (`visits_unique_of_tree`, `visits_unique_seg_of_tree`). The
first state has it from P@(i - 1)'s tree, and every later one if each
operation keeps it (`OpTreeOK`, open; `writerTreeOK_between` with
`CommitLiftOK`). Proved to keep it, as whole operations on prover
latest's cases of `OpGetOK`: a put into a leaf with room, a delete with
no effect, a delete's bitmap with the merges off, the time and space
splits below a parent with room, both splits in place, and the space
root's space, time and in-place splits (`WriterTreePut.lean`,
`WriterTreePut2.lean`, `WriterTreeRoot.lean`); as state lemmas, given the
writer's state after it: a merge into one node and into two, LE-b's
relink, root collapse of the space root and of a segment root, the upward
unlink (`WriterTreeMerge.lean`, `WriterTreeMergeTwo.lean`). The writer's
code of the merge keeps it too (`writerWP_merge_tree`, `WriterTreeMergeOp.lean`):
into one node or two, with the parent on the path reached, room in it for
four klongs and no compaction, and the two nodes not made by the
transaction; on the way, `mergeIdx` chooses the last live klong of each
compare value (`mergeIdx_last`), and the parent's live klongs after are
known (`mpNode_live_lookup`). Under prover latest's writer invariant
`PutInv`, every put at leaf level without an inner split keeps the tree, as
latest's `OpGetOK` cases: `writerWP_put_leafRoot_tree`,
`writerWP_put_leafBelow_tree` (`WriterTreePutInv.lean`),
`writerWP_put_segLeaf_tree` (a segment root that is a leaf: its time split,
space split and space split in place under a new segment root,
`WriterTreeSegRoot.lean`, `WriterTreeSegSplit.lean`, `WriterTreeSegInPlace.lean`)
and `writerWP_put_newSeg_inv_tree` (`WriterTreeNewSeg.lean`). The merge
keeps it also for nodes the transaction made (`writerWP_merge_made_tree`,
`WriterTreeMergeMade.lean`: the parent's klongs retargeted, the nodes taken
back); root collapse at the space root, the whole loop
(`writerWP_collapseRoot_space`, `WriterTreeCollapse.lean`); LE-b with room
(`writerWP_emptyKeyNext_tree`, `WriterTreeLeb.lean`); root collapse at a
segment root, one step (`WriterTreeCollapseSeg.lean`); the four cascades of
prover latest, a leaf split under a full parent split under a grandparent
with room (`TimeSplit2After`, `SpaceSplitTimeAfter`, `TimeSpaceAfter`,
`SpaceSpaceAfter`), as state lemmas and as whole puts
(`WriterTreeCascade.lean`, `WriterTreeCascadePut.lean`,
`WriterTreeInnerHalves.lean`, `WriterTreeSpaceSpace.lean`; the live klongs of
an inner node's halves with klongs put, `halves_inner_cons_live`). The deletes
into a segment leaf below an inner parent with room, the merges off, as prover
putinv's: the bitmap, the full leaf's time split or space split, in place or
not (`writerWP_del_leafBelow_tree`, `writerWP_del_leafBelow2_tree`;
`WriterTreeDelFull.lean`, `WriterTreeDelSpace.lean`). With `PutInv` (024-12):
`OpTreeInvOK`, each operation from a state that meets `PutInv` keeps the tree,
which with putinv's `OpPutInvOK` gives `PutInv` at every reached state
(`putInv_reached_inv`); and each of putinv's rules, the four cascades too,
keeps `PutInv` with no premise on the tree after (`putInv_*_full`;
`WriterTreeInv.lean`, `WriterTreeCascadeInv.lean`). Depth in a tree: every
path to a node has one length (`PathLen.depth_unique`), so a change of a node's
child does not change what reaches the node (`tReach_updN_parent`;
`WriterTreeDepth.lean`). Cascades of any depth (`WriterTreeCascadeGen.lean`,
`WriterTreeCascadeGen2.lean`): `appendKlongs j (X j) ins` along the access
path's nodes X s .. X D, X s with room for two klongs, the others existed
before the transaction, each node's compare values in the range of its
parent's klongs (prover latest's form, which putinv's `RangeOrder` gives),
keeps the writer's tree (`writerWP_appendKlongs_chain`; time splits only,
`writerWP_appendKlongs_timeChain`). The proof is by induction up the path: the
tree with the klongs put in X j (a tree that is not the writer's state) is a
tree, and each split moves that tree one level up (`treeOK_timeSplit_gen`,
`treeOK_spaceSplit_gen`); the writer's split leaves the parent's step open
(`writerWP_handleFullWith_time_up`, `_space_up`), for prover latest's get side.
The cascade of any kind (`writerWP_appendKlongs_chainG`, `WriterTreeChainG.lean`;
the writer's steps in `WriterTreeChainSteps.lean`, the tree's in
`WriterTreeChainTree.lean`): also a split below a segment leaf (a new inner
node above the halves, `treeOK_segSpaceStep`), splits in place of nodes the
transaction made at any level (below a leaf, the leaf repointed:
`treeOK_segSpaceInPlaceStep`), and a top at the space root that splits, in
time or space, in place or not, with a new root (`treeOK_rootTimeStep`,
`treeOK_rootSpaceStep`, `treeOK_rootSpaceInPlaceStep`). Its premises: the
cascade stops at a node with room or at the space root, a full node below an
inner parent has its compare values in that parent's link's range, and a node
that space splits has two live klongs. A delete's leaf split below the cascade
(`WriterTreeDelChain.lean`): a last version given, whose live klongs are among
the leaf's, split in time or space, in place or not, below an inner node or a
segment leaf, then the cascade (`writerWP_delSplit_chainG`); for the delete's
last version `lastVersionGivenDel`, h at least 2 (`writerWP_delLeaf_chainG`,
its halves by `delLast_halves`); and a delete's leaf that is the space root
(`writerWP_delRootSplit_tree`).
The reading (TP10's `OpGetOK`) after the writer's merge of two nodes the
transaction did not make, into one node or two, the parent reached, inner, with
room: every key reads as before (`writerWP_merge_get`, `WriterGetMergeTail.lean`;
its tail `writerWP_mergeTail_get`), the siblings' compare values from putinv's
`RangeOrder` (`mrg_child_range`) and `mergeIdx`'s choice (the siblings adjacent
in the parent); by the tree lemmas `getFromR_mergeOne` and `getFromR_mergeTwo`
(`WriterGetMerge.lean`, a merge into two read as a merge into one at an unused
id, then a split). The same for nodes the transaction made
(`writerWP_merge_made_get`, `WriterGetMergeMade.lean`: `retarget` keeps the
parent's live klongs, as none of them names a merged node after `mergeParent`;
the merged nodes, taken back, had no value). Root collapse at the space root,
the writer's loop, keeps the reading (`writerWP_collapseRoot_space_get`,
`WriterGetCollapse.lean`): an inner root whose only live klong is the empty
key's reads every key as its child (`getFromR_collapse`), given a premise on
the fuel: every path from the root is shorter than `fuel`, which the heights
bound (`PathsFit`, `FuelPaths.lean`, one Prop agreed with prover latest). The
segment-root collapse steps keep the reading (`writerWP_takeBackRoot_seg_get`,
`writerWP_replaceRoot_seg_get`, `WriterGetCollapseSeg.lean`: the leaf's klong to
the root names its child, which reads every rest of a key as the root,
`getFromR_subst`). The upward delete at tree level (`WriterGetUp.lean`): with
the key's leaf emptied (latest's `getFromR_leaf_change_seg`), the chain below the
stop node reads nothing (`chain_deadBelow`), so deleting the stop node's klong to
it, at an inner node, by LE-b or at a segment leaf, keeps every reading
(`getFromR_up_inner`, `getFromR_up_leb`, `getFromR_up_leaf`; a search outside a
node's range finds nothing, `getEqR_none_above`, `getEqR_none_below`). At the
writer's level, `writerWP_deleteUpward_inner` (`WriterGetUpW.lean`,
`WriterGetUpT.lean`): the climb (`writerWP_climb`), the chain unlinked, the stop
node's bitmap with room, root collapse at the space root; the writer's tree
after is a tree (`treeOK_up_inner`) and the key reads nothing, every other key
as before. `writerWP_deleteUpward_up` (`WriterGetUpAll.lean`) takes every stop:
a segment leaf, an inner node by a bitmap, or by LE-b when its klong to the
chain is the empty key's (`writerWP_emptyKeyNext_room_frame`,
`lebNode_live_lookup`; the tree relinked, `treeOK_dropSubtree_tr`), each with
room. `writerWP_deleteUpward_upT` (`WriterGetUpTake.lean`) adds the take-back:
a node of the chain that the transaction made is taken back and its parent
retargeted, so the stop node may be retargeted too; a retargeted node has the
same klongs but for pointers (`KNode.shapeOf`: size, bitmap, bits, dead count
and LE-b's node alike, so the room premises carry over), and its live klongs
but the chain's are the node's (`KNode.retarget_liveAt_ne`, from `oneLink`).
Its limits: the merges off, root collapse at another segment a premise
(`hcollSeg`). Root collapse at any segment (`WriterGetCollapseLoop.lean`): the
loop keeps any invariant that its descent, its node read and its two steps keep
(`writerWP_collapseRoot_inv`); the descent rebuilds the path as steps linked from
the space root (`writerWP_descendToSegmentRoot_linked`, `SegDesc`); a step at a
segment root keeps `CollGetInv` (`collGetInv_segStep`: every path after is one
before, no shorter, `segCollapse_pathLen`), the take-back and, with room in the
segment leaf, the replacement (`writerWP_takeBackRoot_seg_coll`,
`writerWP_replaceRoot_seg_coll`); so `writerWP_collapseRoot_coll` with a caller's
invariant J and room in the leaf (`hroom`). A full leaf (the cascade, which
latest's `writerWP_appendKlongs_chainGR` reads) is not taken: `CollGetInv` needs
the paths within the fuel after it, which no cascade lemma states yet.
The fuel premise is per segment since 2026-11-13, 19:20 (the coordinator's
decision on cost's finding, written in 024-12): `CollGetInv` and the collapse
and upward-delete lemmas take latest's `SegFits N t (p.fuel - 1) r` in place of
`PathsFit`, which no transaction keeps when a segment tree grows above H inside
it (`segFits_transfer`, `SegDepthLe.of_inner`, `FuelPaths.lean`); prover putinv's
`RangeUpAll`, `RangeUpTake` and `RangeCollapseSeg` take it too. The merges'
loop for any invariant its steps keep (`writerWP_mergeUp_inv`,
`writerWP_afterDelete_inv`, `WriterMergeUpLoop.lean`). The merge with a full
parent at tree level (`WriterTreeMergeFull.lean`): `mergeParent` goes one of two
ways (`writerWP_mergeParent_cases`); the full way hands `handleFull` the
parent's last version with the new pointers (`mergeFullLast`), whose live klongs
are `mergeParentNode`'s (`mergeFullLast_lookup`); the delete's split with its
cascade, generalized to any last version whose tree is a tree
(`writerWP_fullSplit_chainG`, `WriterTreeFullSplit.lean`), splits it; the merged
siblings are then not reached (`mergeV_reach`) and the last loop keeps the tree
(`writerWP_mergeCleanup_wNode`, `treeOK_after_cleanup`). So
`writerWP_merge_any_tree` and `writerWP_mergeTail_any_tree`: the writer's merge
keeps the tree with the parent full or with room, given the cascade's premises
for the path above the parent (as for the delete) and the halves of its last
version (`hhalves`). Not taken: the parent the space root (d = 1), whose split
makes a new root. The reading (`GetMergeFull.lean`): a time split of a node with
any last version below an inner parent, with its cascade, reads as the tree with
the node's content replaced by that version (`writerWP_handleFull_timeV`, from
latest's `getFromR_timeLevel` and `writerWP_appendKlongs_chainGRQ`, as in
`writerWP_del_accessPathR`); that tree reads as before the merge
(`getFromR_mergeOne`, `getFromR_mergeTwo`, with the full last version's live
klongs, `mergeFullLast_iff`). So `writerWP_merge_full_get` and
`writerWP_mergeTail_full_get`: the writer's merge keeps the reading, the parent
with room or full, when the state after fits the fuel or no new root is made
(`ChainNoNewRoot`). Its limits: a full parent that existed before the
transaction, below an inner node, its last version not space split
(`hnospace`); open: the space split of the full parent, in place or not, and the
parent a segment root (below a segment leaf). The merges' loop at tree level
(`writerWP_mergeUp_tree`): it keeps the tree and a caller's invariant when each
merge does; its descents read as before (`writerWP_descendToHeight_readsU`). `InnerChildrenExist` (`ChildrenExist.lean`) is the Prop agreed
with prover putinv, who proves it for the writer's states.
Not yet: the whole put and delete around the cascade; a merge whose parent is
full or compacted;
the mergeUp loop and the delete as a whole.
Their premises beyond TREE: the ids from w's next one on in neither the
base nor a live klong (`hbaseF`, `hfreshT`).

The merge with a full parent of every kind (cost, 2026-11-13, evening). A full
parent at depth D + 1 reads as its last version in every kind of split
(`writerWP_handleFull_lastV`, `GetMergeLevel.lean`). That covers a time split
or a space split, in place for a parent that the transaction made or not, below
an inner node or a segment leaf, each with its cascade. The proof is
`writerWP_appendKlongs_chainGRV`'s step at its top level, for a last version
with nothing put. The halves of such a version search as it does
(`halves_read_nil`, `halves_cover_nil`, `HalvesNil.lean`), and a node of a time
klong and sorted key klongs is its own last version
(`KNode.lastVersion_newKlongs_sorted`). A parent split in place stays reached.
The merge's last loop leaves it as it is, since its key klongs are its last
version's, and those name neither merged node (`writerWP_mergeCleanup_pSame`,
`key_mem_newKlongs_liveAt`). So the reading is kept for any parent at depth
D + 1 (`writerWP_merge_any_get`, `writerWP_mergeTail_any_get`, `GetMergeAny.lean`),
and for the parent at the space root (d = 1) on the get side and the tree side
(`writerWP_handleFull_rootV`, `writerWP_merge_root_get`,
`writerWP_merge_root_tree`, `GetMergeRoot.lean`). Their premises:
* the parent's last version is a time klong and sorted key klongs (`hsorted`;
  true of `mergeFullLast` when the second new node's first compare value is
  not one of the parent's other live ones; not yet proved);
* splitAbove is at least 2 (`hsa2`);
* for a space split below an inner node, the last version's live compare values
  are in the range of the parent's link (`hrangeL`; `RangeOrder` gives this);
* a space split in place below a segment leaf is left out (`hspaceL`, as
  `writerWP_appendKlongs_chainGRV` leaves it out).

The reading holds when the state after fits the fuel. Without that, it holds
when no split makes a new root: the space root does not space split, and the
parent's parent is inner (for d = 1, the root does not space split).

The last version's sortedness is proved (`mergeFullLast_sorted`,
`MergeFullSorted.lean`). The second new node's first compare value lies between
the left child's and the parent's next one, and differs from the right child's
unless it replaces it. So the get-side theorems no longer take `hsorted`; the
root tree side still does. Case 4 of 024-12's assembly is reduced to named step
obligations (`opGetCaseOK_delMerge`, `DelMergeCase.lean`; the list is in
024-12). The merge from the state's invariants is `writerWP_merge_get_inv`
(`GetMergeInv.lean`): its premises come from PutInv, PutInvG, RangeOrder and the
path facts (`PathOK`). The merges' loop and the collapse keep the delete's inner
invariant `DelInv`.

## 11. State

Final for today: 2026-11-11, 16:05 (agent "mgl" of coord-1111). Nothing
of mine runs or holds a slot.

* **Branch** `024-22-merges-lean` in
  `/Users/f/fl/bench/2026-11-11/mgl/clone`, **head `90eb124a`**, in
  int's combined landing head `024-13-int-m` with 024-21 (`4105fc1a`).
  `main` (`944e6944`, with 024-12) is merged in at `447d3f0e`. This
  item's commits: `63e39de6` (the merge, V1, TP28 to TP36, format 7's
  count, TP26, `treetest` with merges and A6, the TREE line),
  `ad3707eb` (TP37), `8e78cf65` (MF3), `37e8fbb0` (8/17/17, h a
  parameter), `e7b66354` (a 7-token TREE line: h = c), `e32eb6d9`
  (TP38), `90eb124a` (BU1's count in `treecheck`). Lean only.
* **Gated** (section 8): `lake build` on `90eb124a`; `level2.sh` full
  and `treetest`'s whole default set on `e32eb6d9` (`90eb124a` changes
  only `treecheck`'s checks with merges).
* **Against Java:** before 8/17/17, 239 traces of the combination with
  f507148d (5.1); at 8/17/17, mgj's 21 traces and the combination's
  239 (5.2), all equal, BU1's count included.
* **Next, not done:**
  1. `runs/set6.sh` at 8/17/17, one slot (skipped today by the
     coordinator): exhaustive 10 3 14 4 and 8 4 10 4, `model` at 14,
     random on segment keys; the random M = 30 runs had only 87 merges
     (3.3, 2.1a): a run with more keys at 30 is worth more.
  2. `treeconf.sh large` against Java with merges (up to 5,000
     transactions; may need a hold of its own, or `--norun`).
  3. **The proofs, for a later agent** (section 6 has the sizes):
     * TP30 (V1 kept, `MergeInvPreserved`): the B-tree proof of 024-12's
       TP7 with V1 added. Its local parts are proved: TP36 (a merge's
       nodes hold m or more and fit), TP37 (a space split's halves
       hold m or more), TP38 (a merge's nodes in order). Left: that a
       delete lowers a count by one, and that the loop (`mergeUp`)
       then merges every node below m, up to a root; and every other
       rule keeps V1 (a time split keeps the count). Statement in
       `SIS/Tree/MergeProps.lean`; the run evidence is section 3.
     * TP32 (CB1, `MergeOpBound`): needs frame lemmas, that every action
       of the writer but `merge` keeps `W.merges`. Begun in
       `mgl/plant/lean/SIS/Tree/MergeFrame.lean` (not on the branch):
       `MergesLe`, its lemmas for pure, throw, bind, read, get, modify,
       `note`, `fresh`, and a step tactic `mstep`. The blocker is
       `getNode` and every function above it: matches applied to the
       reader and the state, which `split at h` does not open; each
       needs `cases` on the scrutinee by hand, about 35 functions. A
       `do`-aware simp set (or a Hoare-style `WP` for `M`) first.
     * TP31 (BU1's count): a counting lemma on trees from V1, V2, V4;
       then the walk to that tree. Checked on runs and on Java's trees.
     * TP33 (CB3): the potential argument of 024-11, 5.5, over a run.
  4. Dead klongs (024-18, option 2): to the agent "o2" (024-23), on
     top of this branch's model.
* **Copies:** `mgl/plant/lean` (planted faults, clean; `MergeFrame.lean`;
  a `debug6` mode), `mgl/comb/clone` (branch `comb`: `d90586d0` +
  024-21's `0281018e` + the TREE line with m, c and h, uncommitted;
  Java built there).
* **Logs:** `/Users/f/fl/bench/2026-11-11/mgl/runs/` (each script there
  takes its own slot with `slot.sh`).

2026-11-13. Status set after the release (coord-1113).

### 11.1 State, the night of 2026-11-13 to 14 (agent "cost")

Names since 025-02 (2026-11-14): 025-02's name map.

Branch `024-22-cost` in `/Users/f/fl/bench/2026-11-13/cost/clone`, main
merged at every checkpoint; the full build passes and every theorem of the
night uses only propext, Classical.choice and Quot.sound. The details are
in 024-12's (4) entry (step 4) and section 1's list.

* **Proved:**
  - TP7's (b), the live heights after every run, from one named premise:
    `treeRun_heightLiveOK_chk`, `invPreserved_of_open_chk`
    (`HeightsChkRun.lean`). The heights' walk: every key node's height
    exact in the writer's overlay at every state of a transaction
    (`HtInv`, `WriterHeights*.lean`, `HeightsRun.lean`).
  - TP10's fuel premise between operations (`TxSegFitsOK`, latest's
    `hfit`) from the heights: `txSegFitsOK_of_takeBelowDelR`
    (`HeightsFit.lean`), by the doomed transaction.
  - Step 4 (B): a split's cascade, a delete's bitmap and a merge each add
    at most one to the cached heights; a whole put too
    (`HeightsFuel.lean`, `HeightsFuelMerge.lean`, `HeightsFuelPut.lean`);
    every operation, given the delete's (`opHtStep_of`,
    `HeightsOpStep.lean`).
  - Step 4 (C), part 1: a descent that succeeds from a node of height h
    had fuel above h (`ht_descendLte_height`, `HeightsFuelDescent.lean`).
  - One of `OpDelChkOK`'s checks, `checkPathFree`: the path's nodes are
    pairwise distinct (`ht_path_ne`, `HeightsPathNodup.lean`), so the
    upward delete's loop takes back no node at the stop node or above
    (`ht_deleteUpwardChk2`, `HeightsPathFree.lean`). The premise without
    it, `OpDelChk2OK`, gives TP7's (b) and TP10's fuel premise:
    `treeRun_heightLiveOK_chk2`, `invPreserved_of_open_chk2`,
    `txSegFitsOK_of_takeBelowDelR2`; at the runs a predicate R holds of,
    for latest's run induction, `opHtDelOKUnder_of_chk2`,
    `execW_htCacheU`, `txSegFitsOK_of_takeBelowDelR2U`
    (`HeightsUnder.lean`).
  - putinv's `DelFullFitsOK` in its reached form, `DelFullFitsOKR`
    (`delFullFitsOKR_of`, `HeightsFitsR.lean`): given the heights' state
    `HtJ` at the descent's end, which putinv's descent walk carries with
    `htJ_descendLte`, `htJ_pathAdd`, `htJ_start` (`kdhtJ_*` with the
    kinds), from `htStart_reachedU` at the operation's start. The
    cascade's lemmas are generalized in place to a set of ids (`SBInvS`,
    `sbS_*`; `SBInv` the case of every id).
  - The upward delete's stop node is a segment leaf with the merges on
    (`StopLeafLive.lean`): with the fill at the delete's start (latest's
    `LiveCounts`) a node one delete empties has one live klong, so it is
    no node an inner node names (`mergeBelow` ≥ 2) and no inner segment
    root (two live klongs): `stopLeaf_of_liveCounts` (the path's flags
    `fReach_path`; an emptied node has at most one live klong). So
    putinv's `UpLebFitsOK` with the fill, `UpLebFitsOKL`, holds
    vacuously (`upLebFitsOKL_of`): hFitL goes from the flat list where
    `LiveCounts` is at hand (latest's `live_reached`). Probe:
    `12-tree-model/leb-probe.lean.txt`, with the merges on 3382 deletes
    (45 climbing), no stop node off a segment leaf and no LE-b; with the
    merges off 792 deletes, 61 inner stop nodes, 34 LE-b.
  - putinv's `UpCascFitsOK` in its reached form, `UpCascFitsOKR`, from
    `UpHolderOK` (`upCascFitsOKR_of`, `HeightsUpCascR.lean`): the heights'
    walk at the loop's end from the descent's end (the stop node and the
    chain's nodes are leaves of height 0 by the fill; the other nodes
    unchanged; the path's nodes distinct), then the cascade as for
    `DelFullFitsOKR`.
* **Open, as exact statements** (named premises; each with its test):
  - `OpDelChkOK p` (`HeightsChkRun.lean`): a delete, from a state that
    the transaction's earlier operations reach, runs as its copy with a
    check at every take-back (`putKvDelChk`, `DelChk.lean`).
    `12-tree-model/delchk-check.lean.txt`: 7987 deletes, 0 failures
    (7137 of fixed and random runs; 850 of random runs whose keys make
    one-key segments, so that 77 deletes climb).
    Its weaker form `OpDelChk2OK p` (`HeightsPathFree.lean`) asks the
    same of the copy without `checkPathFree` (`putKvDelChk2`); the first
    implies it (`opDelChk2OK_of_chk`). The same script, the same 7987
    deletes, 0 failures.
  - `UpHolderOK` (`HeightsUpCascR.lean`), in place of putinv's
    `UpCascFitsOK`: at the upward loop's end every node not taken back
    holds, by a live klong now or before the transaction, only nodes not
    taken back, has its times at most the transaction's, and the chain's
    nodes taken back are the transaction's. Checked on runs by putinv
    (its UpChk2.lean): 2529 loop ends, 0 failures (1385 with chain nodes
    taken back, 954 unlinked, 173 cascades), the loop keeping `gh` too (a
    hypothesis of `UpCascFitsOKR`; putinv can prove it with a loop walk
    that knows the parent cached).
  - `TakeBelowFuelDelOK p` (`HeightsFit.lean`): a delete takes back no
    node of height fuel or more that it found at its start.
    `12-tree-model/heights-op-check.lean.txt`: 3224 operations that took
    nodes back, 0 failures.
  - `OpDelHtStepOK p` (`HeightsOpStep.lean`): a delete adds at most one
    to every cached height. `heights-op-check.lean.txt`: 8416 deletes, 0
    failures.
  - The holder family `HtDelFamily` (`WriterHeightsDelete.lean`) is a
    second route to TP7's (b), superseded by `OpDelChkOK`.
  - TP32 and TP33 as before (section 11; TP32's heights paragraph above).
* **Next:**
  1. The checks left in `OpDelChk2OK` (`checkPathFree` is proved,
     `HeightsPathNodup.lean`, `HeightsPathFree.lean`):
     - The holders (`checkFree`, `checkRoot`): from putinv's TP4 walk
       (`TakeJ2` with `TreeOK`, through `liveHolder_unique`).
     - `checkOld`'s segment leaf and the stop node a segment leaf: from
       the fill at the delete's start (latest's `LiveCounts`,
       `live_reached`), by `stopLeaf_of_liveCounts` (proved,
       `StopLeafLive.lean`). What is left: the lemma asks the key access
       path linked by live klongs in the operation's starting tree
       (`(K i, X i) ∈ (Nn (i - 1)).liveAt c.i`, `wNode` of the start at
       each `X i`), which the heights' walk (`HtInv`) does not carry;
       putinv's descent walk (`writerWP_del_toLeafMK`) carries it, but for
       the writer's `putKv`, not the checked copy. So: either that link
       invariant through the walk of `putKvDelChk2`'s descent, or a
       `Refines` argument that the checked copy's prefix reaches the
       writer's state; then a copy without the two checks and its
       refinement. About 2.5 to 3 hours. It ties the heights' run
       induction to TP7's (the fill), as latest's run induction does.
     - `checkOld`'s node of the view: a walk of `madeFor` over every
       operation (`setMadeFor` passes `replacedBy x`, or an x the
       transaction did not make).
     - Or the stop node's check goes if the copy keeps the writer's branch
       for an inner stop node (LE-b, `emptyKeyNext`, then the merges and
       root collapse): it needs a heights' lemma for `emptyKeyNext`, whose
       next child the fold picks among all of the node's klongs.

     Each proved check gives a weaker premise through `Refines`
     (`DelChkRefines.lean`), as `opDelChk2OK_of_chk` does.
  2. `TakeBelowFuelDelOK`: a node a delete found and takes back is
     reachable at its start from a segment root it descended, so below
     the fuel by (C)'s part 1. What it needs, a reach frame through the
     delete's writes: a node found at the operation's start and reachable
     (by live klongs, within its segment tree) at a later state of the
     operation was reachable at its start from that segment's root, or is
     below a node so reachable. The writes that add a reach are the new
     nodes' klongs (merges, splits: they name found nodes that the node
     they replace named), the retargets (to `madeFor`, nodes of the view)
     and root collapse (the child of the root). Then: the delete's first
     descent passes every segment root on its key's path below the fuel
     (`ht_descendLte_height`), and a node reachable from a root of height
     R has height at most R (the heights' walk). A walk of the delete with
     a reach invariant over `wNode`, in the style of putinv's
     `TtReachedN` walk; about 1500 to 2500 lines, a night of its own.
  3. `OpDelHtStepOK`: one root split per segment and delete, as the new
     root keeps room in the same operation (the merges' fill). Nothing
     uses it yet.
* **Test scripts** (`12-tree-model/`, the run command in each header):
  `delchk-check.lean.txt`, `heights-op-check.lean.txt`,
  `merge-hold-check.lean.txt`, `segfit-check.lean.txt`,
  `leb-probe.lean.txt`.

**2026-11-15, prover "putinv2": three premises are false as stated.** `hCoU`
(`CollapseUnlinkAllOK`), `hU` (`UpUnlinkTreeOK`) and `hHL`
(`UpHolderLiveRunOK`) are false for every parameter set, at the first run
(`collapseUnlinkAllOK_false`, `upUnlinkTreeOK_false`,
`upHolderLiveRunOK_false`; `PremisesFalse.lean`). So the top theorems
`invGetScanOK_merges` and `invGetScanOK_merges_noOutside` hold vacuously as
they stand: no parameter set meets all their premises.

* **Why.** Each premise speaks of every writer state that meets a local
  invariant, not of the states that runs reach: `hCoU` of every state with
  `CollGetInvF` and `SegDesc`, `hU` and `hHL` of every state with `PutInv`
  and `UpLoopEnd`. Those invariants say nothing of the writer's books: of a
  cached node's version before the transaction, of the next id, of the nodes
  taken back. The tests ran the premises at the states that runs reach, so
  they could not see this.
* **The counterexamples.** Small states at time 1, over the first run's P:
  - `hCoU`: the next id 0, and a cached space root whose version before the
    transaction names its leaf 11. Every hypothesis holds; 11 is not below
    the next id.
  - `hU`: a space root over a leaf whose klong of the transaction deletes its
    klong of before, which names the space root. At the loop's end the leaf
    is unlinked back to that version, so the tree has a cycle.
  - `hHL`: a cached node that nothing reaches names a node taken back.
