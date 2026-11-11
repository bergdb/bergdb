# 024-23. Dead klongs: option 2, theta 7

Created 2026-11-11 by Frans Lundberg. Status: open.

Option 2 of 024-18 (compaction at the write) built as a change of its
own, after the merges (024-21, 024-22), model first (024-04, section 6):
a design note, the rule in the Lean tree model with its bound stated,
the model's runs, then Java checked against the model, then the gates.

Frans's decision (024-18, section 8, "Decided, QD1"), 2026-11-11, 14:21:
"I am leaning towards 2 with threshold 7. It seems simpler. And I think
we need to accept that we need to take this step by step. We cannot
change everything at once. As you said, compactation of stored nodes can
change things. And this is not thouroughly measured." To the order (the
merges first, then option 2 as a change of its own, model first; 3c
shelved), 14:27: "Yes." To measuring at 10M with MEM and reads timed
before it lands: "No. Let's get this in now. We will measure carefully
and study alternatives later."

Names as in 024-18 and 024-11: B the node size, m, h, c the thresholds
of format 7, theta option 2's threshold, BU1, V1. A write is any change
of an existing key node's klongs by the writer. Cite the decisions taken
here as "024-23, OD1", the questions as "024-23, QO1".


## 1. In short

Kept current; section 10 has the exact state. Written 16:12.

* **Design note written** (section 2). The rule is 024-18's option 2
  made exact: a node holds at most theta dead KEY klongs; a write that
  would leave more finds the node full, and rule O replaces it by its
  last version with the write applied, always one node (a time split).
  theta = 7 at B = 30, 7 B / 30 at the other sizes (1, 3, 14 at 8, 14,
  62), none below 8. No record field; one more rule of format 7.
* Lean, Java, the comparison and the gates: not yet.


## 2. Design note

Written 16:01 to 16:12, from 024-18 (sections 2, 4 and 6), the merges'
code on `024-13-int-m` (`a78aa498`: `Dag`, `KeyNode`; `Exec.lean`,
`Node.lean`, `Bound.lean`) and 024-17, section 5.2.

### 2.1 Dead klongs, counted

* **dead(X)**: the KEY klongs of key node X that are dead at the latest
  time: deleted by X's last bitmap, or followed by a later KEY klong of
  the same compare value (shadowed). Each klong counts once, deleted and
  shadowed alike. Over all of X's klongs, those of the running
  transaction included. Time klongs and bitmaps are not counted (a
  compaction removes them with the dead klongs; 024-18, 2.4).
* **Who counts, when**: the writer, in the writing transaction, at each
  write, from the node as it is (`Dag.deadCount`, Lean's
  `KNode.deadCount`): one pass over at most B klongs with a scan of the
  later ones, at most B^2 / 2 comparisons. No field in the node, the
  stream or the record: so a node read from the stream, a node reloaded
  after eviction and a node of a start's rerun give the same count.

### 2.2 The rule (OD1)

* **What.** Before the writer applies a write to key node X, it takes w,
  the dead klongs the write adds. If dead(X) + w > theta, X is **full**:
  rule O (`handleFullNode`) replaces X by its last version with the
  write applied. Otherwise the write is applied to X as today. So after
  every write X holds at most theta dead klongs.
* **w, write by write** (Java's paths; the Lean model has the same):

  | Write                                       | Where (Dag)          | w                     |
  |---|---|---|
  | a put's KEY klong                           | setValue             | 1 if its key is live  |
  | a new segment's klong                       | setNode              | 0                     |
  | a delete's bitmap, new or the tt's in place | appendDeleteKlong    | 1                     |
  | a split's klongs in the parent, RC's klong  | appendKlongs         | 1 a live compare value |
  | LE-b: a bitmap and the empty key            | emptyKeyNext         | 2, or 1 in place      |
  | a merge's parent                            | mergeParent          | 1 or 2                |
  | a klong of tt pointed in place              | retarget, link, ...  | 0                     |

  "Live" is the compare value's latest KEY klong in X, not deleted by
  X's last bitmap. A klong pointed in place (behind X's time klong of
  tt) adds no klong and no dead klong, so it never compacts.
* **Size first.** The room test of today (`node.size + 1 < B` and its
  forms) is made first; a node that fails it is replaced by rule O as
  today, with h deciding between a time split and a space split.
  Compaction is the case of a node that has room and would hold more than
  theta dead klongs.
* **A compaction is always a time split.** The node passed the room
  test, so it holds the write; its last version with the write applied
  has no more klongs than the node with the write (it drops every dead
  klong, every time klong but one and every bitmap), so it fits in B
  (at most B - 1 klongs). 024-18's "a space split only if the last
  version and the write do not fit in B" is so never reached, and rule
  O's h does not apply to a compaction: the last version may hold more
  than h klongs, as 024-18 measured ("nodes are fuller"). A node that
  the transaction made is compacted in place (`timeSplitInPlace`), as
  today; any other is replaced by a new node and loses its klongs of tt
  (`toPreviousState`), as at a time split today.
* **Why "dead(X) + w > theta" and not "dead(X) >= theta at any write"**
  (024-18's wording, the prototype's code). The two are the same for
  every write that adds one dead klong: an overwrite, a delete,
  reclaim's rewrite, a split's or RC's klong in the parent; those are
  nearly all. They differ in two cases. A write that adds none (a new
  key, a new segment, a space split's second klong) does not compact a
  node that holds theta: it has no need to. A write that adds two (LE-b,
  a merge's parent) compacts at theta - 1: otherwise it would leave
  theta + 1. And the transaction's own bitmap, changed in place, is a
  write too (the prototype skipped it: a second delete in one node of
  one transaction left theta + 1). So the bound is exact, and the rule
  reads as the room test does: a write that would not fit finds the node
  full. QO1 asks Frans.
* **No record field, no flag.** The rule is a function of the node and
  the write, so a start's rerun of a record makes the same nodes with
  the same ids: one more rule of record format 7, as the merges are. The
  format number stays 7 (format 7 is not released; 2026.5 refuses
  2026.4's databases). A database made by the code between the merges'
  landing and this one is not reopened safely by this code (its rerun
  would compact where its writer did not): internal builds of one day.

### 2.3 theta (OD2)

* **theta = 7 at B = 30** (Frans's QD1), `Dag.THETA_30`, the Lean
  model's `Params.theta`.
* **Other node sizes, scaled as the thresholds are**: theta(B) = 7 B /
  30 by integer division, at least 1: **1 at 8, 3 at 14, 14 at 62**.
  Below 8 (Dag's own tests; no database has such a size): **off**, 0, as
  the merges are off there (`Dag.MERGE_MIN_NODE_SIZE`): the rules of
  format 7 apply from node size 8. Open with 024-14's QT2 (other node
  sizes): 1 at B = 8 compacts at every second dead klong, which costs at
  B = 30 two to three times the bytes (024-18, 6.1, theta 1); B = 8 is
  no size for a large database. QO2.
* **Off**: theta 0 is today's behaviour, write by write (the Lean model's
  default, the treecheck of an older trace).

### 2.4 With rule O's h, the merges' m and c, and BU1

* **h = 17**: unchanged for a full node by size. A compaction is not
  rule O's choice (2.2): one node, of up to B - 1 klongs.
* **m = 8 and BU1**: a compaction keeps every live klong, so no node's
  live count changes: V1 (every node but a root holds m or more), BU1's
  count (024-11, TH3), the merges' triggers are as without option 2. It
  makes no node a merge would not, and takes none away.
* **c = 17**: a merge's new nodes hold no dead klong. A merge's parent
  change adds one or two (024-18, E8) and may compact the parent: the
  merges' loop already walks its path again after any rule O
  (`pd.fullNodes`; the Lean model's `descendToHeight`).
* **The upward unlink, LE-b, RC, the take-backs**: unchanged, but that
  their writes count (2.2). A compaction of a node that the transaction
  made keeps its id (in place), so the take-back's `madeFor` stays.
* **Dead klongs a node**: at most theta after every write, where the
  merges alone leave B (024-11, BU1's allowance; 024-18, 6.3).

### 2.5 The bound, stated

* **TP39 (DeadBoundOK)**: after every transaction, every key node
  reachable at its time holds at most theta dead klongs; with theta 0,
  nothing. Checked: by the walk of the invariants (Lean's `walk`, so
  treetest after every transaction and treecheck's C-T6 on Java's
  structure), by UnlinkFuzz's strict walk after every transaction (Java,
  `Dag.checkFill`'s count), by DagTester's tests of the rule.
* **After every write** holds too, node by node, by the rule's form;
  stated as TP39's per-write form (`writeDeadOK`) if cheap, else in
  words.
* **Not zero**: a node that is not written keeps up to theta for good
  (with R forever, a cold node; 024-18, QD2).

### 2.6 dirtyNodeBound

`Dag.dirtyNodeBound` (and its restatement, Lean's `dirtyNodeBound`,
TP23) counts for each node walked its overflows: 1 + (k + 1 - room - 1)
/ q for k klongs and its room, q = 10 at B = 30. What option 2 adds:

* **A node with room can be replaced.** A node that holds d dead klongs
  and gets k klongs can be compacted if d + k > theta (each klong the
  count gives a node adds at most one dead klong, but LE-b's and a
  merge's two, for which the count gives four klongs a delete).
* **Only once, and not more than by size after.** The compaction is one
  new node (a time split) and one klong in the parent. Its replacement
  holds no more klongs than the node would at every later point, so it
  overflows by size no more often than the node would have; and every
  later compaction in the transaction is of a node that the transaction
  made, in place: no node, no klong in the parent.
* **So**: overflows(k, size, d) = max(today's count, 1 if theta > 0 and
  d + k > theta). A node that overflows by size already counts its
  replacement; one that does not gets one overflow (2 nodes in the
  count, one more than the compaction makes). d is the node's
  dead count as walked (the writer's node). Java and Lean change the
  same way; TP23 is checked by treetest after every transaction and by
  treecheck's C-T8 on Java's traces, and DagTester's bound tests.
* **024-17's bounds do not change**: its count of format 7 takes each
  node's overflows and one as at most 2 + k / q (024-17, 5.2); the new
  term is at most 1, so the sum, TP26's form 20 x s_i x (H + 2) + 14, the
  limits (452 operations at 112 bytes) and q stand. The worst case of a
  walked node was already a node without room.
* **024-16** (one operation a key): unchanged. Its E6 case (a later put
  of tt in a node that tt made shadows a klong of tt) counts as dead
  klongs and compacts that node in place, with no node made.

### 2.7 Where it lands

* **Java**: `Dag`: `THETA_30`, `theta(b)`, `deadCount`, the w of each
  write path, `handleFullNode`'s compaction (a time split), the count in
  `overflows`; `TraceExport`'s TREE line with theta as its 9th token
  (docs/trace-format.md); UnlinkFuzz's strict walk checks at most theta
  dead klongs a node after every transaction; DagTester's tests of the
  rule (a node reaching theta is compacted; a restart reruns the same
  nodes); docs/levels.md, docs/sis-model.md, releases/next.md.
* **Lean**: `Params.theta` (0 off), `Params.withTheta`;
  `KNode.deadCount`; in `Exec.lean` the w of each write and
  `handleFullWith`'s compaction; `Bound.lean`'s `overflows`; `Inv.lean`'s
  walk with DeadOK; `Props.lean` TP39; treecheck reads a TREE line of 9
  tokens (the older forms still read, theta 0); treetest's `theta` word
  and runs at 8, 10 and 12 (theta 1, 2, 2).


## 3. Lean

Commit `aabafc04` on `024-23-option2` (on `024-13-int-m`'s `2679622e`),
Lean only, before any Java (024-04, section 6).

* **The parameter.** `Params.theta` (0, off, the default: 2026.4's and
  the merges' tree, write for write), `Params.thetaFor` (7 M / 30, at
  least 1, 0 below 8) and `Params.withTheta`. `withMerges` is unchanged,
  so 024-22's runs are as they were; Java's format 7 is
  `withMerges.withTheta`.
* **The count.** `KNode.deadCount` (Node.lean): Java's loop, a key klong
  deleted by the last bitmap or followed by a key klong of its compare
  value.
* **The rule** (Exec.lean). `deadOver p n'`: the node with the write
  applied would hold more than theta. Every write of the writer builds
  that node already before it stores it (`putNode`), so the test is on
  it: `setValue`'s put, `appendKlongs` (a split's or RC's klongs in the
  parent; also `setNode`'s full path), `appendDeleteKlong` (new bitmap,
  and the transaction's own in place), `emptyKeyNext`, `mergeParent`.
  `setNode`'s klong of a new segment adds no dead klong and is not
  tested, as in Java. A compaction is `handleFullWith ... (compact :=
  true)`: rule O's time split (in place for a node of the transaction)
  whatever h says, with the trail's note `dead.compact` (and
  `bitmap.dead`, `bitmap.inplace.dead`, `leb.dead`, `merge.parent.dead`).
  Java's form, the dead klongs a write adds (2.2's table), is the same
  number: deadCount(n') - deadCount(n).
* **The bound in `dirtyNodeBound`** (Bound.lean): `Walked.dead`, and
  `overflows` gives at least 1 to a node with dead + klongs > theta
  (2.6). `freshTreeBound` is unchanged (new nodes).
* **The invariant.** The walk (Inv.lean) reports `DeadOK` for a node of
  more than theta dead klongs, so `faultsAt`, treetest's checks of every
  state and treecheck's C-T6 on Java's structure check TP39.
* **Stated** (SIS/Tree/DeadProps.lean): TP39 `DeadBoundOK` (every key
  node reachable after every transaction of a run within reach holds at
  most theta dead klongs) and TP40 `DeadWriteOK` (write by write: from a
  P where every key node holds at most theta, every node the writer
  holds at the transaction's end does). **Proved**: `thetaFor_values`
  (1, 3, 7, 14 at 8, 14, 30, 62; 0 at 6), `thetaFor_pos`, and the
  rule's local form `deadOver_false`. TP39 and TP40 are not proved: they
  need the whole writer (as TP30 does); the runs check them.
* **treecheck** reads `TREE M G H k m c h theta` (9 tokens); 5, 7 and 8
  tokens still read, with theta 0. Its summary line prints theta.
* **treetest**: the word `theta` (with `Params.withTheta`; below node size
  8 forced to theta 1, as `merge` forces m below 8) on `exhaustive`,
  `subsets`, `random` and `model`; the set `thetas` (`runThetaSet`), part
  of the default run: exhaustive with merges at 8 (theta 1, prefixes 2
  and 4, pairs), 10 and 12 (theta 2), subsets at 8, random at 8 and 14
  (theta 3), the whole model at 8, and option 2 alone at 4 (forced) and 8.


## 4. Java

Commit `1838b687`, after the model (section 3); 024-18's prototype
(`5e0ab160`, `d64aab58`) ported by hand, not by its patch script, to the
rule of 2.2.

* **`Dag`**: `THETA_30 = 7` and `theta(b)` beside the thresholds (one
  method, as `minFill`, `mergeCap`, `splitAbove`); `deadCount(node)`
  (public, for the checks), `isLive(node, cv)`, `deadFull(node, dead)`
  (theta 0: never; a node of n klongs with n - 1 + dead <= theta: not
  counted; else the count, stopped at the limit). The write paths, each
  with the dead klongs of 2.2's table: `setValue` (1 if the key is live),
  `appendKlongs` (1 for each klong of a live compare value; so
  `setNode`'s full path, the splits' parents and `replaceRoot`),
  `appendDeleteKlong` (1; the transaction's own bitmap in place first),
  `emptyKeyNext` (2, 1 in place), `mergeParent` (1 or 2). Each that
  finds the node dead-full calls `handleFullNode(..., compaction = true,
  ...)`, which counts `statCompactions`, refuses (a `Bug`) a last
  version that would not fit, and takes the time split whatever h says.
  About 120 lines with the comments; the prototype's
  `-Dbergdb.theta` is gone, theta is a rule of the format.
* **`dirtyNodeBound`**: `Walked.dead` (the node's count as walked) and
  `overflows(klongs, size, merged, dead)` at least 1 when dead + klongs >
  theta; `freshTreeBound` keeps the old form. The Javadoc's list has the
  case.
* **`checkFill`** (BU1's walk) checks TP39 too: every reachable key
  node at most theta dead klongs (`Fill.deadKlongs`, `deadMax`). So
  UnlinkFuzz's strict walk after every transaction, MergeTester's runs
  and DbTesterMerge's Db-level runs (with restarts and crash cuts) check
  it. UnlinkFuzz prints the compactions and the most dead klongs of a
  node after a transaction.
* **TraceExport**: the TREE line's 9th token, `Dag.theta(maxNode)`.
* **Tests**: `bergdb.dag.DeadKlongTester` (new): theta's values; a leaf
  of 10 keys and 7 overwrites holds theta, the 8th overwrite replaces it
  by its last version of 11 klongs and none dead, the old one keeps its
  history, and `dirtyNodeBound` counts the replacement; a compaction of
  a leaf of 18 keys (19 klongs, above h = 17) is one leaf; the
  transaction's own bitmap in place compacts; random transactions at
  node sizes 8, 14 and 30 keep at most theta and reach it exactly.
  `DbTesterMerge.testRestartsRerunTheCompactions` (new): overwrites at
  node sizes 14 and 30, a restart every third transaction at startup
  distances of 10 bytes and 10 MB: the tree after each start the same,
  node for node, and the reruns compact (10 MB). The existing restart and
  crash-cut tests of the merges (node size 8, theta 1) now rerun
  compactions too, and pass unchanged. **No existing test's expected
  value changed.**
* **Docs**: docs/levels.md (the rule, after the merges' paragraph),
  docs/sis-model.md (3.4 and the format's paragraph), docs/trace-format.md
  (the TREE line's th), releases/next.md (the format 7 entry: one more
  rule; its figures are 024-18's, to be replaced by section 7's).


## 5. The model's runs, and Java against the model

### 5.1 treetest (the model alone)

`treetest thetas` (section 3) on `aabafc04`, one core, 16:01 to 16:48
(29 minutes of CPU): after every transaction the invariants' walk with
DeadOK (TP39), V1, BU1's count, CB1, CB3, A6, TP23 with the count of 2.6
and TP26; gets at every time and scans; TP19 up to depth 4; the model
run with C-A, T1 and T2. `o2/runs/thetas1.txt`: **TREETEST OK**.

| Run                                              | States | Failures |
|---|---|---|
| exhaustive 8, depth 3, 12 keys, prefix 2, merges | 14,424 | 0        |
| exhaustive 8, depth 3, 12 keys, prefix 4, merges | 14,424 | 0        |
| exhaustive 10, depth 2, 14 keys, prefix 4, merges | 812   | 0        |
| exhaustive 12, depth 2, 14 keys, prefix 4, merges | 812   | 0        |
| exhaustive 8, depth 2, 12 keys, prefix 2, pairs, merges | 83,232 | 0 |
| subsets 8, 12 keys, prefix 2, merges             | 4,095  | 0        |
| subsets 8, 9 keys, prefix 3, puts, merges        | 19,682 | 0        |
| subsets 8, 210 keys, depth 1, puts, merges       | 21,483 | 0        |
| random 8, 20 seeds, 200 steps, 40 keys, merges   | 4,000  | 0        |
| random 8, 10 seeds, 124 keys, 50 % deletes, merges | 2,000 | 0       |
| random 14 (theta 3), 10 seeds, 300 steps, merges | 3,000  | 0        |
| model 8, 6 seeds, 60 steps, merges (C-A, T1, T2) | -      | 0        |
| exhaustive 4 (theta 1 forced), no merges         | 22,620 | 0        |
| exhaustive 8, depth 3, prefix 4, no merges       | 14,424 | 0        |

theta is 1 at node size 8, 2 at 10 and 12, 3 at 14. 205,008 states;
TP23 never exceeded. The rules reached: 146,760 compactions, of them by
a new bitmap 25,569, by the transaction's own bitmap in place 7,882, by
a merge's parent 54,097, by LE-b 106 (the rest by puts and the splits'
klongs in parents).

### 5.2 treeconf: Java with option 2 against the model

`java/stress/treeconf.sh` on `1838b687`'s build (the TREE line with
theta, so treecheck runs the model with Java's theta): the model gives
Java's change, klongs and records exactly (C-T1 to C-T9), its invariants
hold on Java's tree after every transaction (TP39 among them), C-T8's
bound holds.

| Set     | Seeds | Traces | Transactions | Compactions | Merges | Result       |
|---|---|---|---|---|---|---|
| small   | 10    | 70     | 7,100        | 21,860      | 1,144  | TREECONF OK  |
| drain   | 10    | 110    | 13,900       | 50,800      | 27,627 | TREECONF OK  |
| reclaim | 3     | 15     | 8,777        | 8,560       | 715    | TREECONF OK  |

Compactions are the model's `dead.compact` (of them by a delete's
bitmap in place: 33, 11,606 and 10). No trace reached LE-b (`leb.*`): with
the merges a delete empties only a root. Earlier, 16:20, 4 seeds of
small and drain: OK as well.


### 5.3 Controls: the checks bite

In a copy of the model (`o2/plant/lean`), each fault alone, treetest:

* **A, `dirtyNodeBound` without option 2's term** (2.6): random runs at
  node size 8 with merges and theta 1 (10 seeds, 200 transactions, 40
  keys): TP23 fails in 4 transactions (7 key nodes marked, the count 6;
  a put of two keys whose leaves hold theta dead klongs). So the term is
  needed, and TP23's check reaches the case.
* **B, the transaction's own bitmap changed in place without the test**
  (as the prototype had it): the same random runs: DeadOK (TP39) fails
  in 20 transactions of 2,000 (a node with 2 dead klongs, theta 1), from
  transaction 31 on, three deletes in one leaf. So the walk's TP39 check
  catches a write that the rule misses.


## 8. Questions for Frans

Cite as "024-23, QO1". Each was decided by rule here so that the work
could go on; each is a default that Frans may overturn.

* **QO1. The rule's form.** Built: a write is applied only if the node
  then holds at most theta dead klongs (dead + added > theta: full).
  024-18's words and prototype: "theta or more before a write". The same
  for every write that adds one dead klong (overwrites, deletes,
  reclaim's rewrites, a split's or RC's klong in the parent); built so
  that the bound is exact (at most theta after every write, TP39): a
  write adding none does not compact, LE-b and a merge's parent (two)
  compact at theta - 1, and the transaction's own bitmap changed in
  place counts (the prototype could leave theta + 1). Recommended:
  **keep it**.
* **QO2. theta at other node sizes.** Built: 7 B / 30, at least 1, so 1
  at 8, 3 at 14, 14 at 62; off below 8 (no database has such a size). At
  B = 8 theta 1 compacts often (theta 1 cost two to three times the
  bytes at B = 30; 024-18, 6.1). Recommended: **keep it for 2026.5**, and
  decide B = 8's theta with 024-14's QT2 and the node-size study
  (024-19).
* **QO3. Databases made between the two landings.** The rule is part of
  format 7 without a new format number: a database written by the
  merges' code without this rule reruns differently with it. Only
  internal builds of one day can hold one. Recommended: **land both on
  `main` before anyone keeps a database**, and keep format 7.


## 10. State

2026-11-11, 16:34, by the agent "o2" of coord-1111.

* **Clone** `/Users/f/fl/bench/2026-11-11/o2/clone`, branch
  `024-23-option2`, on `024-13-int-m`'s `2679622e` (the merges, 024-21
  and 024-22, with `main` of 16:0x; `main`'s later commits are items
  only). Commits: `aabafc04` (Lean), `1838b687` (Java, tests, docs),
  `6a24e0f0` (lean/README.md). Head **`6a24e0f0`**.
* **Done**: the design note (2), Lean (3), Java (4). treeconf small (10
  seeds, 70 traces), drain (10, 110), reclaim (3, 15): TREECONF OK with
  option 2 on. treetest `thetas`: running (one core,
  `o2/runs/thetas1.txt`), the first four runs 0 failures.
* **Running**: treeconf medium (3 seeds) in slot heavy2 (from 16:26);
  a control in `o2/plant/lean` (dirtyNodeBound without option 2's term).
* **Next**: the gates (section 6) by `o2/gate.sh` and `o2/gate-lean.sh`,
  one slot at a time; the 1M count by `o2/count1m.sh cold over
  sparsecold` (DK compiled in `o2/probe/c`, the build frozen in
  `o2/b1`), section 7.
