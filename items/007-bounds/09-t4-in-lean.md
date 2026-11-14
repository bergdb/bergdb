# 007-09. T4 and a cold start's reads in Lean

Created 2026-11-13 by Frans Lundberg. Status: for Frans's review; brought
up to date on 2026-11-14 with the Lean on `main` at `5f413438`.

What was proved on 2026-11-13: T4, the bound on the records at the ends of
the startup section and on the debt D (007-01, sections 5.1 and 6; 007-03,
"After the plan"), a bound on a cold start's reads (007-03, step 6), and
one theorem that joins them with T3, `bounded_startup`. This subitem was
first written at 12:43 from the Lean at `8af385a0` (provers "t4" and
"t42"). This version adds the rest of the day: the provers "t43" (12:27 to
13:02), "t44" (13:12 to 14:01) and "t45" (14:01 to 14:13), and the second
review of the definitions by Codex at 13:12 (`09-t4-in-lean/second-review.md`).
The Lean of 007 is unchanged on `main` since `b41fad85` (2026-11-13,
14:16) but for a comment. The layout follows 007-08.


## 1. The answer

**In plain words, for BergDB.** Bounded startup, as 007-01 argues it, is
now one theorem, `bounded_startup`: after any run of the model that meets
its premises, a cold start reads at most a number F of node versions and
headers. F depends on the largest startup distance M, the least cost m of
a record, the height H of the tree, the size of a transaction and a few
constants of the tree. It has no term for the number of keys or the age
of the database, beyond the height of the tree. It joins three parts, each
proved in the model:

* T3, the section: the take, with Java's byte limit, keeps the startup
  section below N = 2M/m + 2 transactions.
* T4, the records and the debt: each record of the section holds its
  transaction plus at most |D| versions; with BergDB's own still-dirty test
  and its virtual root, every node of D reaches, through pointers live or
  dead, a change of the last Hp + 1 sections, so |D| is bounded by those
  sections' changes if no node has more than Q pointer parents.
* The reads: a start parses every version of the section, reads a header
  for each pointer of a top node of D (rule 4), and the rerun reads a
  header and a version for at most H + 1 nodes per node, entry, touch and
  lost pointer of each transaction's change, plus the merges' sibling
  reads.

**For BergDB itself it is reduced to premises, not proved.** For 024-12's
model of BergDB's tree (`treeSpec`), `LiveAppend`, T3's count and Java's
removals (`DropRunOKJ`, but for its count K) are proved. Open are the
model's assumptions on each transaction (`RunOK`), TREE, the fit of each
transaction's nodes in a record (005-31), the heights H and Hp, the
pointer parents Q, the size of a change A, the nodes a transaction makes
unreachable K, the merges' sibling reads B and the top node's pointers Pt
(section 5). Frans deferred them on 2026-11-13, 16:14
(006-24, section 4). Two of them, Q and Hp, count pointers that are no
longer live, and no bound independent of the database's age is known for
either (section 5; question Q4). Until they are bounded, "a cold start's
reads do not grow with age" holds for the model given its premises, not
for BergDB.

What changed since the first version:

* T4's debt is proved for BergDB's still-dirty test and its virtual root
  (`T4_debt_java`), and counted by the tree's height, not the model's
  level numbers.
* 007-01's "about the last two sections" stays false (section 4, point 2).
* The second review found four definitions short of Java (section 5).
  Three are fixed by new definitions: Java's removals (`DropStepJ`), reads
  counted as reads, not as objects (`lazyReads`), and a record's gd counted
  whole (`RecordGdBound`). The fourth, the take's byte limit, is modelled
  (`takePolicyB`); T3 holds with it where each transaction's nodes fit,
  and Java's runs never reached a stop (028-12).
* A first guess for the count k of `DropStepJ`, (H + 1) per operation, is
  refuted: a merge cascade loses two pointers a height
  (`BoundColdCascadeExample`). About 2 (H + 1) is the conjecture.

All bounds count versions, ids and reads, not bytes.


## 2. The trusted definitions

These, with the statements of section 3, are what Frans must check
against the prose. They rest on trusted definitions from before, which did
not change: the step, `marked`, `RunOK`, `pathOf`, `lazyStartup`, TREE
(`treeAt`, `TreeRunOK`), `LiveAppend`, the take (`takePolicy`, 007-08)
and 024-12's `treeSpec`.

### 2.1 From the first version (12:43)

Eight in `lean/SIS/BoundT4.lean` and two in `lean/SIS/BoundCold.lean`.

* `spAt S j`: s(j), the startup pos of R(j); 0 past the end of S.
* `spIter S n j`: s applied n times to j. After R(k) the startup section is
  R(s(k)), ..., R(k), and a start reruns T(s(k)+1), ..., T(k). "The last n
  sections" are the transactions after `spIter S n k`. So the last two
  sections are T(s(s(k))+1), ..., T(k). This makes 007-01's "the last two
  sections" (section 6) precise.
* `levelOf P x`: the level of x in P, 0 if x is not in P. It is the
  model's level number. In a tree with the data nodes on level 0 and the
  root on level h, it is the height of x. In 024-12's model of BergDB's
  own tree it is a code, not a height; the definitions of 2.2 count
  heights instead.
* `onAccessPath ts τ x`: x is on the access path of the change of T(τ) in
  the run ts. Either x is reachable at τ, after the change, with a node
  below it (x included) that T(τ) creates or gives an entry (`marked`);
  or T(τ)'s touch marks x (reclaim's touch, item 001). From 007-01,
  section 6: "on the access path of T(j)'s change (the changed nodes and
  their ancestors)". The touch is not in the prose, but step 3 marks
  touched nodes too, so it belongs.
* `changeAt ts τ`: the change of T(τ) in the run, made on P after
  T(τ-1). The counts use it.
* `RecordBound db tr R`: R is the record that tr appends to db. With i the
  stream's length, D the debt before T(i) and c the change of T(i):
  1. R holds T(i);
  2. every version in R is of a data node that T(i) creates, or of a node
     of D;
  3. R has at most (the data nodes T(i) creates) + |D| versions;
  4. at most |D| entries of R's gd are nodes of D.

  From 007-01, 5.1: "A record holds T(i), its value nodes, gd(i) and the
  versions of the nodes taken, which come from D. So R(s) and R(k) cost at
  most a transaction plus the debt." It counts versions and ids, not
  bytes. Point 4 leaves the rest of gd(i) unbounded; the review found that
  gap, and `RecordGdBound` (2.2) closes it.
* `RecordByDebt db tr`: the step appends one record, and it meets
  `RecordBound`.
* `DebtByChanges ts`: after the run ts, with k = |ts|, every node x of D
  is on the access path of a T(τ) with `spIter S (lev(x) + 1) k` < τ ≤
  k: one of the last lev(x) + 1 sections. From 007-01, section 6: "So D
  holds the nodes changed in about the last two sections and their
  ancestors at those times", with lev(x) + 1 in place of "about two".
* `rerunReach sp S`: for any stream S, summed over T(s+1), ..., T(k): the
  nodes on the writer's paths for T(j)'s change (`pathOf`), the nodes
  T(j) creates, and the nodes of gd(j). From 007-03, step 6: "a cold
  startup reads at random only what the rerun touches".
* `removedAt sp P c j`: the nodes reachable at j-1 that are not reachable
  at j after the change c. In BergDB, a node that a split replaces, a merge
  or an upward unlink leaves out, a replaced root, the old top node.

The first cold-start theorems (`coldReads_*`) count the objects that the
lazy startup makes (`Mem.next`), not reads. The review showed that this
undercounts: Java parses every version of the section, repeats included,
and reads headers that make no object. After `runJ 8`
(`BoundColdReadsExample`) the start makes 13 objects but reads 24 times.
`lazyReads` (2.2) counts reads.

### 2.2 Added after 12:43

T4 with BergDB's still-dirty test, `lean/SIS/BoundT4Java.lean`:

* `PtrBelow P x z`: z is x, or below x through pointers live or dead (a
  node no longer reachable keeps its entries, so its pointers).
* `DebtByChains ts`: every node x of D reaches through `PtrBelow` a node
  on the access path of a change of the last lev(x) + 1 sections. With the
  exact test z is x itself (`DebtByChanges`). From 007-01, section 6,
  second point.
* `ptrParents P z`: the nodes of P with an entry that points to z, live or
  dead. 007-01, section 6: "how many such nodes point to a node of D".
* `geomSum Q h`: 1 + Q + ... + Q^h.
* `PtrHeightLe P h x`: every chain of pointers, live or dead, down from x
  has at most h steps. For a top node this includes its dead skip pointers
  to older top nodes.
* `DebtByChainsH ts`: `DebtByChains` with the height h of x along all
  pointers in place of lev(x).

Heights, `lean/SIS/BoundHeight.lean`:

* `LiveHeightLe P t h x`: every chain of live pointers at t down from x
  has at most h steps. For BergDB's virtual root: the tree's height at t
  plus one.

A record's gd whole, `lean/SIS/BoundT4Gd.lean`:

* `RecordGdBound ts j R`: for the record of T(j + 1), with D the debt
  before it: the ids of R's gd not in D are distinct; every id of gd is in
  D or on the access path of T(j + 1)'s change; |gd| ≤ (ids not in D) +
  |D|.

Removals, `lean/SIS/BoundColdDrop.lean` and `BoundColdDropJ.lean`:

* `DropStep` (first, 12:51): a node that stays reachable loses at most one
  live child per entry, and a removed node's children stay reachable. The
  review showed it false for Java: one delete bitmap kills several
  children (`Dag.appendDeleteKlong`), and `Dag.deleteUpward` unlinks a
  parent with its children. `BoundColdDropJExample` checks both failures
  on runs of `treeSpec`.
* `DropStepJ w P j c k`, `DropRunOKJ`, `lostTo`, `addsWeight`: Java's
  removals. A node that stays reachable loses at most the weight w of the
  entries it gets; the nodes the change makes unreachable lose at most k
  pointers to each other.
* `bvalW`: the weight of a BergDB entry: a key klong 1, a delete bitmap
  the number of its compare values, a top node's root pointer and the
  root's entry for a new top node 1, a skip pointer and data 0.

Reads, `lean/SIS/BoundColdReads.lean`:

* `lazyReads sp sib S`: what a cold start from S reads, after
  `DbStarter.doOrdinaryStartup`: every version of R(s), ..., R(k) with
  repeats (`sectionVersions`, as `StoredTrans.Parser.parse`), 2 for the
  top node of the last transaction, a header read for each pointer of a
  top node of D (`topHeaderReads`, rule 4's top-node fallback in
  `NodeCollection.linkToCanonical`), and the rerun's reads: a header and a
  version for each stream pointer the writer follows
  (`followStreamPointer`), a version for each node of gd(j) without an
  object (`canonicalNode`), and `sib tr` follows outside the writer's
  paths for each transaction tr (`Dag.merge`'s siblings). The assertion
  reads of `checkLinkById` are not counted: production runs without
  assertions.

T3 with the byte limit, `lean/SIS/BoundTakeBytes.lean`:

* `takeLoopB`, `takePolicyB`: Java's `TransSeq.take` with `maxBytes`: a
  transaction that the deadline or the pace takes is taken only if its
  got-dirty nodes, `nodeB` bytes each, fit in what is left of `maxB`;
  else the take ends there (a stop, not a skip).

`bounded_startup` adds no definition.


## 3. The theorems

In the 13 files `lean/SIS/Bound*Theorems.lean` besides
`BoundTheorems.lean` (T3, 007-08); the proofs are in
`lean/SIS/Proof/Bound*.lean` (5,933 lines besides T3's of 007-08, 2,205
of them in the first version). The 17 main ones, checked here, use
Lean's standard axioms only, and every push of 13 November passed the
coordinator's axiom audit (006-24, section 5). No file of
`lean/SIS/Bound*.lean` or `lean/SIS/Proof/Bound*.lean` holds `sorry`,
`admit`, `native_decide` or `axiom` (section 7).

**Bounded startup** (`BoundStartupTheorems.lean`,
`BoundColdDropCountTheorems.lean`):

* `bounded_startup`: after a run with the premises listed in section 5, a
  cold start reads (`lazyReads`) at most

      (N + 1)(V0 + A + Dm) + 2 + N((H + 1)A + Dm)Pt
        + 2N(H + 1)(A + K) + 2NB

  times, with N = 2M/m + 2 (the most transactions of a section, by
  `T3_takeB_count`) and Dm = (1 + Q + ... + Q^Hp)(Hp + 1)N(H + 1)A (the
  most nodes of D, by `T4_debt_java_tree_height`). The first term is the
  section's versions (T4's records), the second the top node, the third
  rule 4's header reads, the fourth the rerun's paths, the last the
  merges' siblings.
* `bounded_startup_tree`: the same for `treeSpec` with BergDB's weights,
  with `DropRunOKJ` and k replaced by K, a bound on the nodes each
  transaction makes unreachable (`removedAt`).

**T4, the records**:

* `T4_record`, `T4_records`, `T4_ends`: every record meets `RecordBound`
  against the debt before its transaction. No assumption.
* `T4_record_gd`: with `RunOK` and BergDB's test (or the exact test with a
  written root), every record meets `RecordGdBound` too.
* `T4_record_gd_height`: with TREE after T(i + 1) and the root's live
  height at most H, |gd| ≤ (H + 1)(new nodes + entries) + touched nodes +
  |D|.

**T4, the debt**, exact test (no virtual root):

* `T4_debt`, `T4_debt_restarts`: `DebtByChanges` after a run with
  `RunOK`, without and with restarts. Any policy.
* `T4_debt_count`, `T4_debt_tree`: |D| at most the access paths of the
  last H + 1 sections; with TREE, (H + 1)(new nodes + entries) + touched
  nodes summed over them, H the root's level.

**T4, the debt**, BergDB's test, with or without a virtual root:

* `T4_debt_java`, `T4_debt_java_restarts`: `DebtByChains` after a run
  with `RunOK`.
* `T4_debt_java_height`: the same by height along all pointers
  (`DebtByChainsH`).
* `T4_debt_java_count`, `T4_debt_java_height_count`: |D| at most the nodes
  that reach the access paths of the last H + 1 sections.
* `T4_debt_java_tree`: with TREE and at most Q pointer parents per node,
  |D| ≤ geomSum Q H × `T4_debt_tree`'s bound, H the root's level.
* `T4_debt_java_tree_height`: the same with the nodes of D of height at
  most Hp along all pointers and the root's live height at most Hl after
  every transaction: |D| ≤ geomSum Q Hp × ((Hl + 1)(new nodes + entries)
  + touched nodes) summed over the last Hp + 1 sections.

**A cold start's reads**, counted as reads (`BoundColdReadsTheorems.lean`):

* `lazyReads_same_start`: the counted rerun's memory is `lazyStartup`'s,
  so `lazyReads` counts the reads of the same start.
* `coldReadsJ_lazy`: for any stream, at most the section's versions + 2 +
  the top-node header reads + 2 `rerunReach` + 2 × the sibling follows.
* `coldReadsJ_run`: after a run with `RunOK` and BergDB's test (or the
  exact one with a written root): the writer's paths and new nodes of the
  section's transactions in the run, and 2|D|, in place of `rerunReach`.
* `coldReadsJ_height`: with TREE, `DropRunOKJ` and the root's live height
  at most H: (H + 1)(new nodes + entries + touched nodes + entry weights +
  k) per transaction in place of its paths.
* `coldReadsJ_run_noD`, `coldReadsJ_height_noD`: the same with BergDB's
  test and `LiveAppend`, without the 2|D| term: every node of gd(j) has
  an object when the rerun comes to it.

**Removals** (`BoundColdDropJTheorems.lean`,
`BoundColdDropJTreeTheorems.lean`, `BoundColdDropCountTheorems.lean`):

* `removedAt_bound_J`: with `DropStepJ`, a change makes at most (entry
  weights + k) nodes unreachable; `coldReads_height_dropJ` uses it.
* `blive_lost_le`, `DropStepJ_kept_tree`, `DropRunOKJ_tree`: for
  `treeSpec`, `DropStepJ`'s first point holds with `bvalW` after any run
  with `RunOK` and TREE; only k is left.
* `DropStepJ_dropped_removed`, `DropRunOKJ_tree_removed`: with TREE, k is
  at most the number of nodes the change makes unreachable, so for
  `treeSpec` `DropRunOKJ` holds with that count, given `RunOK`, BergDB's
  test and TREE, and nothing else.

**T3 with Java's byte limit** (`BoundTakeBytesTheorems.lean`,
`BoundTakeBytesCountTheorems.lean`):

* `takeB_progress`: while the span is at least 2 sd, the take takes the
  oldest transaction if its nodes fit.
* `T3_takeB`: the section without its last record costs less than 2M, as
  `T3_take`, if the whole debt fits in the limit before every transaction.
* `T3_takeB_count`: if each transaction's own nodes fit (005-31), the
  section holds at most one transaction, or n with (n - 2)m < 2M.

**Still on `main`, superseded**: `coldReads_lazy`, `coldReads_handles`,
`coldReads_run`, `coldReads_tree`, `coldReads_run_noD`,
`coldReads_tree_noD` count objects, not reads; `removedAt_bound`,
`coldReads_tree_drop` and `coldReads_height` rest on `DropStep`, false for
Java. They are true of the model and used by nothing above.

**Examples** (checked by running with `#guard`, not proofs):
`BoundT4Example` (two sections fail), `BoundT4JavaExample` (with BergDB's
test D grows with the run's past replacements), `BoundHeightExample` (the
examples meet `DropStep` with heights at most 2), `BoundColdDropJExample`
(`DropStep` fails and `DropStepJ` holds on `treeSpec`),
`BoundColdReadsExample` (24 reads for 13 objects), `BoundTakeBytesExample`
(the byte limit stops the take; a span of 103 against 2M = 6),
`BoundColdCascadeExample` (k = 10 for one delete at H = 7).


## 4. What is true and what is not of the prose

1. **007-01, 5.1, the records at the ends: true** (`T4_ends`), counted in
   versions and ids, and with gd counted whole: at most (H + 1)(new nodes
   + entries) + touched nodes + |D| ids (`T4_record_gd_height`). A bound
   in bytes needs a bound on a version's bytes. BergDB has one (a node
   holds a fixed number of klongs); the model does not (007-01, 5.1).
2. **007-01, 6, "about the last two sections": false in general.** What
   holds is lev(x) + 1 sections (`T4_debt`), by height h + 1 for BergDB's
   test (`T4_debt_java_height`). The counterexample is
   `lean/SIS/BoundT4Example.lean`. The root is on level 4 with two
   children on level 3, x and w. Under x is y1 (level 2), with two leaves
   y2 and y2' (level 1). Under w is w1 (level 2) with the leaf w2. Data
   nodes are on level 0. The policy asks for s(1), ..., s(8) = 0, 0, 0,
   1, 2, 3, 4, 6. Record by record (printed from the model):
   1. T(1) gives x a new child z1. x, z1 and the root get dirty, d = 1.
   2. T(2) adds a data node under y2'. y2' and y1 get dirty, d = 2.
   3. T(3) adds a data node under y2. y2 gets dirty, d = 3. This is the
      last change below x.
   4. T(4) to T(8) add data nodes under w2, outside x's subtree.
   5. T(4), s = 1, takes x, z1 and the root. x's new version names y1's
      version of R(0), which is stale. So x stays dirty, d(x) = 4.
   6. T(5), s = 2, takes y1 and y2'. y1's new version names y2's version
      of R(0), stale since T(3). So y1 stays dirty, d(y1) = 5.
   7. T(6), s = 3, takes y2, which is clean after it.
   8. T(7), s = 4, takes x again. x's new version names y1's version of
      R(5), which names y2's stale version. So x stays dirty, d(x) = 7.
   9. T(8), s = 6, takes y1, whose new version names y2's of R(6). y1 is
      clean.

   After T(8), D holds x and the root (d = 7) and w's path (d = 8). The
   last two sections are T(4) to T(8), after s(s(8)) = s(6) = 3. None of
   them changes anything below x. The last three sections, after
   s(s(s(8))) = 0, hold T(3). Each level of put-backs (x through y1, y1
   through y2) moves the change one section further back. After T(8) no
   child of x is dirty. What keeps x in D is the stale version of y1 that
   x's version names. The run meets `RunOK`. All of this is checked by
   `#guard`s, which `lake build` runs; it is not a proof checked by the
   kernel. The startup positions reduce by `decide +kernel`, but D does
   not: the step sorts with `List.mergeSort`, which the kernel cannot
   reduce (tried on a list of three numbers too). Decided (Q1): a dated
   note in 007-01, section 6.
3. **The bound may be one section loose.** x is on level 3: the theorem
   allows four sections, the example needs three. The proof allows index
   nodes on level 0, the data nodes' level. If only data nodes are there,
   its argument seems to give lev(x) sections. A reading, not proved.
4. **007-01, 6, "at most h times those changes": true in form, over more
   sections and, with BergDB's test, times geomSum Q Hp.** With the exact
   test and TREE: (H + 1)(new nodes + entries) + touched nodes, summed
   over H + 1 sections (`T4_debt_tree`). With BergDB's test: that times
   1 + Q + ... + Q^Hp, over Hp + 1 sections
   (`T4_debt_java_tree_height`). If the sections are alike, with C new
   nodes and entries each, the exact test gives about (H + 1)² × C
   (arithmetic, not a theorem).
5. **007-01, 6, BergDB's test: true in chain form, counted only with an
   assumption, as the prose says.** Every node of D reaches, through
   pointers live or dead, a change of the last lev(x) + 1 sections, also
   with BergDB's virtual root (`T4_debt_java`). The prose: "A bound needs
   an assumption on how many such nodes point to a node of D". That is Q
   (`ptrParents`), and `BoundT4JavaExample` shows that without it no
   bound in the last sections' changes holds: a node that a split
   replaced keeps its pointers and stays in D, and D grows with the
   number of replacements in the run's past. The premise as stated counts
   every pointer parent, live or dead, of every node; the prose asks only
   for those that point to a node of D (section 5).
6. **007-03, step 6: "a cold startup reads at random only what the rerun
   touches, at most a node per level of the tree for each key rerun, and
   the section bounds that ... without T4": true for the rerun, in
   reads.** The rerun reads at most a header and a version for H + 1
   nodes per node, entry, entry weight, touch and lost pointer of each
   transaction of the section (`coldReadsJ_height_noD`), with BergDB's
   test and no |D| term. A start reads more than the rerun: every version
   of the section, which holds the debt (T4's records), a header for each
   pointer of a top node of D, and the merges' siblings. So T4 is needed
   for the whole start, through the section's size, not for the rerun.
7. **007-01, 7, T3 and T4 together: proved in the model, in reads, from
   premises** (`bounded_startup`). It uses T3 counted in transactions
   (N = 2M/m + 2), not in cost: the cost form (`T3_takeB`) needs the whole
   debt to fit in a record's room. In bytes it would need a largest
   version, as `T3_bounded` assumes a largest record.
8. **007-08, T3 for BergDB's take: true with the byte limit where the
   nodes fit, false in general in the model.** The take's byte limit
   (`TransSeq.take`'s `maxBytes`) stops the take, also after the
   deadline. If each transaction's nodes fit (005-31) the section stays
   below 2M/m + 2 transactions (`T3_takeB_count`); if the whole debt fits,
   below 2M in cost (`T3_takeB`). Without that, `BoundTakeBytesExample`
   has a take stopped for ever and a span of 103 against 2M = 6. In
   Java's runs the limit never stopped a take (028-12: 18 runs, the whole
   debt at most about half the room at the real record limit), and since
   2026-11-14 `DbBuilder` refuses a startup distance above 10^9 (028-12,
   option A, `773c53e7`).


## 5. What is not covered

**The open premises of `bounded_startup`**, in plain words, and their
state for 024-12's tree model (`treeSpec`). Frans deferred the open ones
on 2026-11-13, 16:14 (006-24, section 4).

* `RunOK`: the model's assumptions on the structure and each transaction
  (A2 to A5, the rules for data nodes and the touch). Open for `treeSpec`
  (024-12, TP14); held on the tree model's own runs (024-12, section 4).
* `LiveAppend`: an appended entry keeps the live pointers that it does not
  replace. Proved for `treeSpec` (TP15, `liveAppendTree`).
* BergDB's still-dirty test (`javaTest`): the algorithm's choice, BergDB's
  own. The review found it matches `Db.handleStillDirtyNodes`.
* TREE in R(0) and after every transaction: every reachable node, the
  root aside, is the live child of exactly one reachable node. Open for
  `treeSpec` (TP16, with TP7). The key tree's top theorem
  (`invGetScanOK_merges_flat`, 024-12, section 1) proves the tree's own
  invariant (`Tree.TreeAt`) from 10 named premises; it is not stated as
  SIS's TREE, and no theorem connects the two.
* The take is Java's, with its byte limit (`takePolicyB`); settings at
  most M; every record costing at least m > 0. Facts of the model and the
  configuration.
* `hfit`: each transaction's got-dirty nodes fit in the record's room
  (005-31). Not proved for Java; 028-12 measured a margin of 220.
* H, the root's live height after every transaction: the tree's height
  plus one. Open for `treeSpec`: the writer keeps key trees within G and
  H, but no theorem gives `LiveHeightLe`. It grows with the log of the
  number of keys, as 007-01 allows.
* Hp, the height of every node of D along all pointers, live or dead.
  Open. For a top node it follows dead skip pointers to older top nodes,
  so it may grow with the database's age if a top node can be in D; the
  review: "includes dead top-node chains; establish a useful height
  bound". Not checked on Java's runs.
* Q, the pointer parents of every node, live or dead, over the whole run.
  Open. The review: "A per-run Q exists, but no useful uniform Java Q is
  established." In BergDB a node that a split replaces keeps its pointers
  to its old children, so a long-lived node may gather old parents with
  age; `BoundT4JavaExample` has such a run in the model. Not checked on
  Java's runs.
* `DropRunOKJ` with weights w and counts k: proved for `treeSpec` with
  BergDB's weights and k the nodes each transaction makes unreachable,
  given `RunOK`, BergDB's test and TREE (`DropRunOKJ_tree_removed`). So
  `bounded_startup_tree` needs K instead.
* A: per transaction, its new nodes, entries, touched nodes and entry
  weights. A premise on the workload; for `treeSpec` the like statement
  in operations is TP20's `MadeBound`, open.
* K: the nodes each transaction makes unreachable. Open. Not (H + 1) per
  operation: `BoundColdCascadeExample` has one delete with merges at four
  heights that makes 11 nodes unreachable at H = 7 (k = 10). Over that
  run, 8 of the 23 transactions with two merges or more exceed H + 1 per
  operation, none 2 (H + 1). About 2 (H + 1) per operation is the
  conjecture.
* B: the merges' sibling follows per transaction. Each merge follows at
  most two siblings (`Dag.merge`), so B is twice the merges; the merges of
  one operation at most the tree's height and one is TP32, open, and the
  amortized count TP33, open.
* Pt: the pointers of a version of a top node. About 49 in Java (a root
  pointer and a skip pointer for each set bit of an ordinal below 2^48);
  not proved in the model.
* V0: the versions of R(0). A constant of the initial database.

**The second review** (`09-t4-in-lean/second-review.md`), finding by
finding:

* `DropStep` false for Java (delete bitmaps; `Dag.deleteUpward` unlinks
  parent and children): fixed by `DropStepJ`, proved for `treeSpec` but
  for its count K (above). The old `DropStep` and its theorems are still
  on `main` (section 3).
* `RecordBound` leaves the gd outside D unbounded: fixed
  (`RecordGdBound`, `T4_record_gd`, `T4_record_gd_height`).
* The cold bounds count objects, not reads (every version parsed; header
  reads; the merges' sibling reads): fixed (`lazyReads`, the
  `coldReadsJ_*` theorems). The siblings are a premise, B.
* `hQ` counts all past parents, stronger than the prose: open (Q above).
* The level number is not Java's tree height: fixed by `LiveHeightLe`
  and `PtrHeightLe`; but `PtrHeightLe` includes dead top-node chains:
  open (Hp above).
* The take's byte limit after the deadline: modelled and proved where the
  nodes fit, refuted without (section 4, point 8); not reached in Java's
  runs (028-12); closed.
* 007-09, section 5 stale: fixed by this version.

**Not covered besides:**

* Bytes. All bounds count versions, ids and reads. A bound in bytes needs
  a largest version.
* T3 in cost inside `bounded_startup`: it uses the count, so N grows as
  the least record cost m falls; with small records N is large.
* Java against the model: checked on Java's traces (024-12, C-T1 to
  C-T9), not proved; Q, Hp, K and B are not among the checks.


## 6. Questions for Frans

**Q1. 007-01's "about the last two sections".** Options:

* A. A dated note in 007-01, section 6, as the note of 2026-10-26 in
  5.3. Proposed text: "Note, 2026-11-13: proved for the exact test, a
  node x of D is on the access path of a change of the last lev(x) + 1
  sections, so h + 1 for a tree of height h; two do not suffice
  (007-09, section 4)."
* B. Edit the sentence itself.
* C. Leave 007-01 as it is; 007-09 is the correction.

Recommended: A. 007-01 stays a record of what was thought, and a reader
of section 6 sees the correction.

Decided: A (Frans, 2026-11-13, 12:49: "As recommended."); the note is
in 007-01, section 6.

**Q2. The trusted definitions as they are (section 2).** Options:

* A. Accept them as they are.
* B. Accept them, with fixes to comments, no definition changed:
  `BoundCold.lean`'s header says that rule 4 reads nothing and that every
  object is a version it reads; `BoundColdDrop.lean` presents `DropStep`
  as BergDB's, which the review showed false; `lean/README.md`'s
  paragraph on the bounds ends with `coldReads_height` and does not name
  `DropStepJ`, `lazyReads`, `RecordGdBound`, `T3_takeB` or
  `bounded_startup`, and its "Not done" still calls `DropStep` "not
  checked on Java's runs" and T3 "proved without its record limit".
* C. B, and remove the superseded definitions and theorems (`DropStep`
  and the theorems on it, the object counts of `coldReads_*`).

Recommended: B. The old theorems are true of the model and cost nothing
to keep; the comments mislead a reader. Open since 2026-11-13; the
definitions of 2.2 are added to what is asked.

**Q3. The scope of the work in progress.** Options:

* A. Add BergDB's virtual root and counts by the height to the brief of
  "t43" (section 5 of the first version), so that T4 holds for BergDB's
  own shape.
* B. Keep the brief: BergDB's test without a virtual root first; the
  rest later.
* C. Stop at the exact test.

Recommended: A, with B as a checkpoint on the way.

Done: A, on the coordinator's call (coord-1113, 2026-11-13, 12:43,
"Frans may overturn"), not overturned; `T4_debt_java` holds with a
virtual root, and the counts are by height (section 3).

**Q4. Q and Hp, the premises that may grow with age.** When the deferred
work on bounded startup's premises resumes (Frans, 2026-11-13, 16:14),
what comes first for these two? Options:

* A. Measure them: Q and Hp on Java's traces, as the checker does for
  TREE (024-12, C-T1 to C-T9), at growing ages of one database. Then it is
  known whether they stay bounded in practice.
* B. Restate T4's debt for BergDB with a weaker premise: Q only over the
  pointer parents that point to a node of D (007-01, section 6's words),
  Hp only over live pointers and a top node's pointer to the root, and
  prove the count again.
* C. Leave both as premises; state bounded startup for BergDB as
  conditional on them.

Recommended: A, then B if the measurement shows growth. A is cheap and
says whether B is needed; C leaves "does not grow with age" unshown for
BergDB. Default if Frans says nothing: A first when the deferred work
resumes.


## 7. Log

2026-11-13. Written for Frans's review, from the Lean on `main` at
`8af385a0`, 007-01, 007-03 and 007-08. Checked here: `#print axioms` of
the eleven theorems (`propext`, `Classical.choice`, `Quot.sound`; the
first two cold-start ones without `Classical.choice`); no `sorry`,
`admit`, `native_decide` or `axiom` in the new files; the example's run,
printed record by record; `decide +kernel` (section 4, point 2). Not
rebuilt: 024-12's board reports 327 jobs for `8af385a0`.

2026-11-13. Q1 decided: A (Frans, 12:49); the note added to 007-01,
section 6.

2026-11-14. Brought up to date with the Lean on `main` at `5f413438`
(Frans, 11:58: "Do as recommended"): the provers t43, t44 and t45, the
second review, `bounded_startup`, 028-12. Sections 1 to 6 rewritten; Q3
marked done; Q4 added. Checked here: each theorem of section 3 exists on
`main` with that name; no `sorry`, `admit`, `native_decide` or `axiom` in
`lean/SIS/Bound*.lean` and `lean/SIS/Proof/Bound*.lean`; `#print axioms`
of 17 theorems (`bounded_startup`, `bounded_startup_tree`,
`DropRunOKJ_tree_removed`, `DropStepJ_dropped_removed`, `DropRunOKJ_tree`,
`removedAt_bound_J`, `T4_debt`, `T4_debt_java`,
`T4_debt_java_tree_height`, `T4_record_gd`, `T4_record_gd_height`,
`coldReads_tree`, `coldReadsJ_lazy`, `coldReadsJ_run_noD`,
`coldReadsJ_height_noD`, `T3_takeB`, `T3_takeB_count`): `propext`,
`Classical.choice`, `Quot.sound`. Run with the build of t45's clone at
`47fbadc0`, whose Bound files equal `main`'s but for a comment in
`BoundColdDropJ.lean`; the main tree's build has no `.olean` for
`BoundStartupTheorems` (stale), and was not rebuilt.
