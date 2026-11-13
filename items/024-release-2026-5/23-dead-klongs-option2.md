# 024-23. Dead klongs: option 2, theta 7

Created 2026-11-11 by Frans Lundberg. Status: done (2026-11-11): on
`main` since `08659847`. QO2 decided (024-19, Q4); QO1 and QO3 as built,
not marked answered.

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

Kept current; section 9 has the exact state. Written 18:16.

* **The rule** (section 2): 024-18's option 2 made exact. A key node
  holds at most theta dead KEY klongs: a write that would leave more
  finds the node full, and rule O replaces it by its last version with
  the write applied, always one node (a time split). The same as
  024-18's "theta or more before a write" for every write that adds one
  dead klong; exact where a write adds none or two, and the
  transaction's own bitmap counts (QO1). theta = 7 at B = 30, 7 B / 30
  at the other sizes (1, 3, 14 at 8, 14, 62), none below 8 (QO2). No
  record field: one more rule of format 7. `dirtyNodeBound` counts one
  overflow for a node its klongs can take above theta; 024-16's and
  024-17's bounds do not change.
* **Model first**: Lean (`aabafc04`): `Params.theta`, `deadOver` in every
  write, TP39 and TP40 stated (the local form and theta's values
  proved), treecheck reads theta from a 9-token TREE line, treetest's
  `thetas` set: 205,008 states, 0 failures (5.1). Then Java
  (`1838b687`): `Dag.theta`, `deadCount`, `deadFull` in every write path,
  the count in `dirtyNodeBound`, TP39 in `checkFill` (so UnlinkFuzz's
  strict walk), the TREE line, new tests, docs.
* **Java equals the model** (5.2): treeconf small, drain, reclaim and
  medium, 222 traces, 43,513 transactions, 137,285 compactions: all TREE
  OK (C-T1 to C-T9, TP39 on Java's tree). Two planted faults are caught
  (5.3): `dirtyNodeBound` without the new term fails TP23; the
  prototype's unchecked own bitmap fails TP39.
* **Five existing tests changed** (4.1), each its own commit, for Frans:
  pinned stream positions and two fragile states moved; one test misused
  PutData.
* **Reviewed** (rev23, 4.2): land with fixes; R1 (a test of mine made
  vacuous) fixed, R3 and R4 done, R2 for the landing message, R5 to R7
  notes.
* **Gated** (6), head **`e0fb9d77`**: lake build, no sorry or axiom,
  test-traces, before-commit, level1 to level4 full, unlinkfuzz,
  conformance small, medium, reclaim, evict and drain: all OK.
* **At 1M keys** (7): 0.29 to 0.31 dead klongs a live one (the merges
  alone 0.48 to 0.85), -3 % to +8.5 % stream bytes, 13 to 16 % fewer key
  nodes; every value checked.


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
  compactions too, and pass unchanged. Four existing tests needed a
  changed value (4.1).
* **Docs**: docs/levels.md (the rule, after the merges' paragraph),
  docs/sis-model.md (3.4 and the format's paragraph), docs/trace-format.md
  (the TREE line's th), releases/next.md (the format 7 entry: one more
  rule; its figures are 024-18's, to be replaced by section 7's).


### 4.1 Changed expected values of existing tests

Each its own commit, for Frans's approval. Option 2 changes the stream
of every workload that overwrites (at node size 30 from the 8th dead
klong of a node, at 8 from the 2nd), so tests that pin bytes or shapes
of a stream moved, as with the merges (024-21, 5.4). Found by
`before-commit.sh` on `e633004f` (8 failures, 17:04); each change
checked by a probe in `o2/probe2/src` against the new build and 024-21's
frozen merges build (`mgj/b2`), so that the same case is pinned again:

* **`1d38e6f4`, CorruptStreamTester** (four tests; the probes CstRows,
  CstOne, CstLeaf, CstFlip, CstPtr, Cst11 and 024-21's CstFind, NodeMap,
  NodePtrs): testFound019_32's rows 1, 2 and 8 at their records' new
  places, each with the same refusal (`Bad klong type, 2`, `Bad key of
  value node`, a read that fails); row 6 ("a leaf's flag") in ALL's seed
  729025, refused as before ("Pointer 23 of node 0 names a node of type
  30"): seed 729011's stream writes no key node after its first record
  any more, its primordial node being compacted rather than filled; the
  last row's odd value pointer at the stream's byte 7200 (a read fails,
  as before; 3336 is now in a node the start reads, refused by its
  checksum). testFound021_11 in the record at 22712 (key node 6217's
  pointer 1, to the newest top node 22904 and the older 18008; the top
  node's skip pointer 0 to the key node at 18848), all refused as
  before. testFound021_12 in the same seed 20767, its node at offset
  208 of the record at 26632, and its three refusal texts.
  testFoundDescentCycle in seed 20828, the record at 39248, prevPos
  15800 (CstFind's search, seeds 20767 to 20830).
* **`c8a59666`, DbTester.testDecreaseOfStartupDistance** (replaces
  `c6655215`, after the review's R1): the decrease to 450 kB (was 500
  kB), "no jump" counted from the stream's end before the call, as
  before. Probed: at 500 kB the paced take of the call moved the startup
  pos to 3,517,520, past the one transaction that was 1,281 bytes inside
  the point (3,511,608 < 3,512,889); with the merges alone it stopped 4.3
  kB before its transaction. `c6655215` counted from the end after the
  call instead, which the review (rev23, R1) showed holds with a planted
  jump too, as the call's own record is about 250 kB: wrong of mine. At
  450 kB the test passes, a planted jump fails it, and the span shrinks
  for 7 commits (rev23's check).
* **`214d4635`, Eviction.testLoweredBudgetAfterPinsFell**: 520
  transactions (was 500). After 500 the test's own evictions down to P0
  left nothing detachable above the pins (P1 3,183 = resident 3,183, P0
  3,442), so the state it tests (resident between the budget and P0) was
  not reached; probed at 400 to 600, 520 reaches it (P1 3,151, resident
  3,981, P0 4,013). Fragile before too (it depends on where the hand's
  evictions stop).
* **`7103d741`, EvictionReaderTester.testEvictionKeepsTheRecords**: 40
  keys (was 30). The space root at node size 8 is compacted to 2 live
  klongs, so the walk of the top node's and the root's pointers found 1
  clean index node, not the 3 it asks; with 40 keys 6.
* **`1f9fdb64`, DagTester.testPointerCreationListener** (an f-test,
  found by the second run of `before-commit.sh`, 17:14): the key access
  path is cleared after each put, as Db does. The test never cleared it,
  so it grew over its 10,000 puts; its space root, a segment leaf with
  one long segment, never split before; with option 2 the segment root's
  splits give it a shadowed klong each, it is compacted, and its time
  split took the path's node before it for its parent ("time-split-1,
  missing klong in keyAccessPath, 10186"). A test's misuse of PutData,
  not a fault of the rule: Db and the model clear the path at each put.


### 4.2 The review (rev23)

The review in this item's directory, `review.md` (rev23, 17:18 to 17:45, on
`1f9fdb64`): **land with fixes**; no defect in the rule; planted faults
in three of the four counting paths, the restart's determinism and
`dirtyNodeBound`'s term are caught by Java's own tests. Done on top
(no history rewritten, the gates running):

* **R1** (should fix): `c8a59666` (4.1).
* **R3**: `e3732d24`, a comment at `emptyKeyNext`'s test: not reached at
  format 7 from node size 8; the model runs it (treetest, theta forced
  below 8).
* **R4**: `e3732d24`: docs/levels.md and Dag's comment say that
  reclaim's rewrites compact the cold leaves that they take above theta
  (not every leaf they reach); releases/next.md says its figures are
  024-18's prototype's until section 7's.
* **R2** (format 7's meaning changes without a format bump): for the
  landing message (QO3).
* **R5, the count's cost on every put**: `setValue` takes `isLive` (a scan
  and `lastBitmap`) before `deadFull`'s cheap size test, and `deadCount`
  is up to B^2 / 2 comparisons on a node above theta (about 450 at 30,
  1,900 at 62). Left for the measurement Frans put later (QD1); if it
  shows, test the size first or count in one pass per compare value.
* **R6, TP40's premise** (every key node of P) is wider than TP39's
  conclusion (the nodes reachable): true (a replaced or unlinked node goes
  back to its state before the transaction), to be stated or narrowed
  when the two are proved.
* **R7, treecheck takes theta from the TREE line** without comparing it
  with `Params.thetaFor M` (nor m, c, h with theirs): Java's and Lean's
  values agree (`DeadKlongTester.testTheta`, `thetaFor_values`); a
  one-line check is optional, not made.


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
| medium  | 3     | 27     | 13,736       | 56,065      | 19,870 | TREECONF OK  |

Compactions are the model's `dead.compact` (of them by a delete's
bitmap in place: 33, 11,606, 10 and 6,643). The medium set has node
sizes 8 to 62 (theta 1 to 14) and up to 8,000 keys; its traces at node
size 62 take the checker 14 minutes each (16:26 to 17:02 in all). No trace reached LE-b (`leb.*`): with
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


## 6. Gates

On `1f9fdb64` (`e633004f` with section 4.1's five test commits), each
in a slot of its own (`o2/gate.sh`, logs in `o2/logs/`):

| Gate                                      | When           | Result                          |
|---|---|---|
| `lake build`, no sorry or axiom, axioms   | 17:15          | OK, 183 jobs; 0 sorry, 0 axiom  |
| `lean/test-traces/run.sh`                 | 17:15          | TRACE TESTS OK                  |
| `java/before-commit.sh`                   | 17:15 to 17:17 | BEFORE COMMIT OK (101 s)        |
| `java/stress/level1.sh`, full             | 17:18 to 17:21 | LEVEL 1 OK, MEM 129 (172 s)     |
| `java/stress/unlinkfuzz.sh`               | 17:21 to 17:26 | UNLINKFUZZ OK, 3,226 rounds     |
| `java/stress/level2.sh`, full             | 17:26 to 17:39 | LEVEL 2 OK (771 s)              |
| `java/stress/level3.sh`, full             | 17:39 to 17:47 | LEVEL 3 OK, C-CUT 0 of 314      |
| `conformance.sh medium`                   | 17:47 to 17:49 | OK, 9 traces TRACECHECK OK      |
| `conformance.sh reclaim`                  | 17:49 to 17:52 | OK, 30 traces TRACECHECK OK     |
| `conformance.sh evict`                    | 17:52 to 17:53 | OK, 51 traces TRACECHECK OK     |
| `java/stress/level4.sh`, full             | 17:53 to 18:07 | LEVEL 4 OK                      |
| the 1M count (section 7)                  | 18:07 to 18:11 | values checked OK, three shapes |
| `conformance.sh small`                    | 18:11          | OK, 70 traces TRACECHECK OK     |
| `conformance.sh drain`                    | 18:12          | OK, 15 traces TRACECHECK OK     |
| on `e0fb9d77`: lake build, axioms, traces | 18:12          | OK, as above                    |
| on `e0fb9d77`: `java/before-commit.sh`    | 18:12 to 18:14 | BEFORE COMMIT OK (103 s)        |

* The axioms (`#print axioms` of the README's list and of 024-22's and
  024-23's theorems): Lean's standard ones; `thetaFor_values` none,
  `thetaFor_pos` and `deadOver_false` propext and Quot.sound.
* before-commit: unit 1,670 tests, f 89, DEMOS OK (14 runs). Its first
  two runs, on `e633004f` (17:04) and with the four tests of 4.1 changed
  (17:14), failed: 8 unit tests, then 1 f-test (section 4.1).
* level2 (on `1f9fdb64`'s build): conformance small 70 traces and drain
  50, TRACECHECK OK (A6 required); A2A3Check2's ten configurations OK
  with A6; treeconf small, drain and reclaim as section 5.2's; take
  TAKECHECK OK; every stress step 0 failures.
* The gates from level3 on build the head `e3732d24` (the review's fixes,
  4.2: a test, comments and docs only after `1f9fdb64`).
* unlinkfuzz: 32 configurations, 697,388 compactions; the most dead
  klongs of a node after a transaction (its strict walk, TP39) is theta
  exactly in every configuration with theta on (1 at node size 8, 3 at
  14, 7 at 30); node size 6 has none (theta off), at most 2.
* level3: conformance with reclaim 30 traces, C-CUT 0 of 314; level4:
  conformance with eviction 51 traces (C-P 0 of 11,943 transactions,
  C-H 0), EvictionInvariance, LargerThanMemory; every step 0 failures.
* The final head `e0fb9d77` adds to `e3732d24` only releases/next.md's
  figures (section 7); lake build, the axioms, test-traces and
  before-commit ran on it last (unit 1,670 tests, f 89, demos).
* By `o2/gates-all.sh`, 17:18 to 18:12, each gate in its own slot, one
  slot at a time; no failure, so no rerun.


## 7. The count at 1M keys

A sanity check that dead klongs a live klong drop as 024-18 measured, no
timing: 024-18's probe DK (compiled in `o2/probe/c` against the build of
`1f9fdb64`, frozen in `o2/b1`), its setup unchanged (1M keys, R = 1 s,
60,000 transactions after the shape, a census every 20,000 and at each
iteration's end), one JVM at a time in one slot, 18:06 to 18:11
(`o2/count1m.sh`; outputs `o2/out1m/`, summed by `o2/dl.py` as 024-18,
6.2 takes them: d/l over leaves and inner nodes at transaction 60,000,
B/op the stream's growth over the 60,000 an operation). Against 024-18's
runs on 024-21's build (6.2): the merges alone (g0) and its prototype of
option 2 at theta 7 (g7):

| Shape      | Merges: d/l | B/op  | Prototype: d/l | B/op  | 024-23: d/l | B/op           |
|---|---|---|---|---|---|---|
| cold       | 0.83        | 264.9 | 0.30           | 279.8 | 0.29        | 284.7 (+7.5 %) |
| over       | 0.48        | 459.3 | 0.35           | 446.8 | 0.31        | 445.0 (-3.1 %) |
| sparsecold | 0.85        | 224.5 | 0.36           | 241.2 | 0.31        | 243.5 (+8.5 %) |

* **Dead klongs drop as measured**, a little further than the prototype's
  (0.29 to 0.31 a live klong, against 0.30 to 0.36), for about the same
  bytes (the percentages against the merges alone). The census's
  histogram has no node above 8 dead klongs at any census of the three
  runs (with the merges alone, "cold" had 51,278 leaves above 8 at
  transaction 60,000). Each run ends with DK's check of every live key's
  value by a scan: OK (1,000,000, 1,000,000 and 100,000 keys).
* **Fewer key nodes** (13 to 16 %): 94,299 in "cold" and 96,737 in "over" (merges
  alone 110,671 and 111,412; prototype 105,627 and 111,389): a
  compaction keeps one node of up to B - 1 klongs where rule O would
  split a last version above h.
* Not measured, as Frans decided (QD1): 10M keys, MEM, reads and their
  time, the cost of the count on each put (4.2, R5).


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
  **Decided** by 024-19, Q4 (Frans, 2026-11-12, 07:36): theta at least
  2, so 2 at 8; made in 024-27 (on main since a7dfb6f7). The text above
  describes theta as first built.
* **QO3. Databases made between the two landings.** The rule is part of
  format 7 without a new format number: a database written by the
  merges' code without this rule reruns differently with it. Only
  internal builds of one day can hold one. Recommended: **land both on
  `main` before anyone keeps a database**, and keep format 7.


## 9. State

2026-11-11, 18:15, by the agent "o2" of coord-1111. Done; reported to
the coordinator, who lands it.

* **Clone** `/Users/f/fl/bench/2026-11-11/o2/clone`, branch
  `024-23-option2`, head **`e0fb9d77`**, working tree clean. On `main`'s
  `4c75ebf1` (merged at `e633004f`). Commits after the merge base
  `2679622e`: `aabafc04` (Lean), `1838b687` (Java, tests, docs),
  `6a24e0f0` (lean/README.md), `e633004f` (merge of `main`), the test
  commits `1d38e6f4`, `c6655215` (replaced by `c8a59666`), `214d4635`,
  `7103d741`, `1f9fdb64` (4.1), the review's fixes `c8a59666` and
  `e3732d24` (4.2), and `bf48bb24`, `e0fb9d77` (releases/next.md's
  figures).
* **Gated** (section 6): all of the brief's gates, OK; before-commit and
  the Lean checks again on `e0fb9d77`.
* **For Frans**: the six test commits of 4.1 (with `c8a59666`) need his
  approval; QO1 to QO3 (section 8); the landing message says that format
  7's meaning changes without a format number (R2, QO3).
* **Not done, by Frans's decision** (QD1): 10M keys, MEM, reads timed,
  the cost of the count on every put (R5). Not proved: TP39, TP40 (R6).
* **Nothing runs; no slot is held.** Scratch: `o2/plant/lean` (the
  controls of 5.3), `o2/probe2` (the probes of 4.1), `o2/probe3`,
  `o2/out1m`, `o2/runs`, `o2/logs`.

2026-11-13. Status set after the release (coord-1113).
