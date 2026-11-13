# 007-09. T4 and a cold start's reads in Lean

Created 2026-11-13 by Frans Lundberg. Status: for Frans's review.

What was proved on 2026-11-13: T4, the bound on the records at the ends of
the startup section and on the debt D (007-01, sections 5.1 and 6; 007-03,
"After the plan"), and a bound on a cold start's reads (007-03, step 6).
The Lean is on `main` since `8af385a0`, the merge of branch `007-t4` at
`48bfe93f`. The layout follows 007-08.


## 1. The answer

A record holds its transaction, and versions only of the data nodes that
the transaction creates and of nodes that were in D before it. So R(s)
and R(k), the records at the ends of the startup section, are bounded by
their transaction plus the debt, as 007-01 says. This is proved with no
assumption at all.

The debt is proved with the exact still-dirty test and a root that is
written like any node. Every node x of D is on the access path of a change
in the last lev(x) + 1 startup sections, where lev(x) is the level of x.
So with TREE, |D| is at most (H + 1) times the changes of the last H + 1
sections, plus their touched nodes, where H is the root's level.

007-01's "about the last two sections" is false in general. A run of 8
transactions has a node of D whose last change below it is three sections
back (section 4).

A cold start makes at most one object for each of these: the section's
index nodes (read in order), the nodes on the writer's paths of the
section's transactions, the nodes they create (not read), the nodes of D,
and 2 more. So, but for one case (section 2), it reads at most that many
versions. This holds for BergDB's still-dirty test too.

Not yet for BergDB itself: the debt with BergDB's still-dirty test and its
virtual root, a cold start's reads without |D|, and a bound on the nodes
that a transaction makes unreachable. All bounds count nodes, not bytes.


## 2. The trusted definitions

These, with the statements of section 3, are what Frans must check
against the prose. Eight are new in `lean/SIS/BoundT4.lean` and two in
`lean/SIS/BoundCold.lean`. They rest on trusted definitions from before,
which did not change: the step, `marked`, `RunOK`, `pathOf`,
`lazyStartup` and TREE (`treeAt`).

* `spAt S j`: s(j), the startup pos of R(j); 0 past the end of S.
* `spIter S n j`: s applied n times to j. After R(k) the startup section is
  R(s(k)), ..., R(k), and a start reruns T(s(k)+1), ..., T(k). "The last n
  sections" are the transactions after `spIter S n k`. So the last two
  sections are T(s(s(k))+1), ..., T(k). This makes 007-01's "the last two
  sections" (section 6) precise.
* `levelOf P x`: the level of x in P, 0 if x is not in P. It is the
  model's level number. In a tree with the data nodes on level 0 and the
  root on level h, it is the height of x. In 024-12's model of BergDB's
  own tree it is a code, not a height (section 5).
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
  bytes. It does not count the rest of gd(i), the nodes that got dirty in
  T(i) itself: they are T(i)'s own.
* `RecordByDebt db tr`: the step appends one record, and it meets
  `RecordBound`.
* `DebtByChanges ts`: after the run ts, with k = |ts|, every node x of D
  is on the access path of a T(τ) with `spIter S (lev(x) + 1) k` < τ ≤
  k: one of the last lev(x) + 1 sections. From 007-01, section 6: "So D
  holds the nodes changed in about the last two sections and their
  ancestors at those times", with lev(x) + 1 in place of "about two".
* `rerunReach sp S`: for any stream S, summed over T(s+1), ..., T(k): the
  nodes on the writer's paths for T(j)'s change (`pathOf`), the nodes
  T(j) creates, and the nodes of gd(j). P is the logical startup's
  (`baseStruct` and the rerun). From 007-03, step 6: "a cold startup reads
  at random only what the rerun touches".
* `removedAt sp P c j`: the nodes reachable at j-1 that are not reachable
  at j after the change c. In BergDB, a node that a split replaces. The
  prose does not name it. The writer's path includes the nodes above such
  a node, so the count needs it.

The cold-start theorems count the handles that the lazy startup gives
out (`Mem.next`), one per object. Each object is made from a version it
reads, or for a node that the rerun creates. So the count bounds the
versions read, but for one case: with a virtual root, the model makes the
root's object from every top node it reaches by skip pointers
(`topsRead`). Java reads only the newest top node at a start
(`DbStarter.topNodeOfLastTransaction`), so for Java the count holds.


## 3. The theorems

In `lean/SIS/BoundT4Theorems.lean` and `lean/SIS/BoundColdTheorems.lean`;
the proofs are in `lean/SIS/Proof/BoundT4.lean`, `BoundT4Debt.lean`,
`BoundT4Tree.lean` and `BoundCold.lean` (2,205 lines). All eleven use
Lean's standard axioms only (`#print axioms`), and none uses `sorry`.

The records:

* `T4_record`: on any database with a stream, the record that a
  transaction appends meets `RecordBound`. No assumption: not A1 to A5,
  not the policy, not the still-dirty test.
* `T4_records`: in a run, every record R(i+1) meets `RecordBound` against
  the debt before T(i+1). No assumption.
* `T4_ends`: the same for R(s) and R(k), R(0) aside. It is `T4_records`
  for those two records; its condition is not used.

The debt:

* `T4_debt`: `DebtByChanges` holds after a run, given three things.
  `RunOK`: the model's assumptions on the structure and on each
  transaction (A2 to A5, the rules for data nodes and the touch). The
  exact still-dirty test. And `sp.virt = false`: a root written like any
  node, not BergDB's virtual root. Any policy, so BergDB's take too.
* `T4_debt_restarts`: the same with restarts after any transactions.
* `T4_debt_count`: with `T4_debt`'s assumptions, and every node of D on a
  level up to H: |D| ≤ N(a+1) + ... + N(k), with a = `spIter S (H + 1) k`,
  for any N such that N(τ) bounds the distinct nodes on T(τ)'s access
  path.
* `T4_debt_tree`: with TREE after every transaction too, and H the root's
  level after the run: |D| is at most the sum, over T(τ) of the last H + 1
  sections, of (H + 1) × (new nodes + entries of T(τ)) + (touched nodes of
  T(τ)). A touch is closed upwards (`StepOK.touchUp`), so touched nodes
  count once.

A cold start's reads:

* `coldReads_lazy`: for any stream S, the lazy startup gives out at most
  |section's index nodes| + `rerunReach` + 2 handles.
* `coldReads_handles`: the same for the startup with handles, with rule 4
  by node id (`handleStartup`) and by position, Java's since 005-57
  (`handleStartupPos`).
* `coldReads_run`: after a run with `RunOK` and BergDB's still-dirty test
  (or the exact one with a written root), at most the section's index
  nodes, plus, for each T(j) of the section, its writer's path in the
  run's P before T(j) and the nodes it creates, plus |D| + 2. The gd(j) of
  the section add up to D (INV-1).
* `coldReads_tree`: with TREE in the initial structure and after every
  transaction, and H the root's level: the same, with each writer's path
  replaced by (H + 1) × (new nodes + entries + touched nodes +
  `removedAt`) of T(j).


## 4. What is true and what is not of the prose

1. **007-01, 5.1, the records at the ends: true** (`T4_ends`), counted in
   versions and ids. "A transaction" is T(i) with its data nodes and its
   own got-dirty ids; "the debt" is D before T(i). A bound in bytes needs
   a bound on a version's bytes. BergDB has one (a node holds a fixed
   number of klongs); the model does not (007-01, 5.1).
2. **007-01, 6, "about the last two sections": false in general.** What
   holds is lev(x) + 1 sections (`T4_debt`). The counterexample is
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
   reduce (tried on a list of three numbers too).
3. **The bound may be one section loose.** x is on level 3: the theorem
   allows four sections, the example needs three. The proof allows index
   nodes on level 0, the data nodes' level. If only data nodes are there,
   its argument seems to give lev(x) sections. A reading, not proved.
4. **007-01, 6, "at most h times those changes": true in form, over more
   sections.** With TREE it is (H + 1) times the new nodes and entries,
   plus the touched nodes, summed over H + 1 sections, not two. If the
   sections are alike, with C new nodes and entries each, that is about
   (H + 1)² × C (arithmetic on `T4_debt_tree`, not a theorem).
5. **007-01, 6, BergDB's test: not proved**, as the prose expected. The
   induction (`debt_main`) does not use the still-dirty test. It needs
   `RunOK`, the invariants of a correct start (which BergDB's test also
   gives) and no virtual root. Only its first step uses the exact test: a
   node that step 7 puts back is dirty. With BergDB's test a node can be
   put back while clean, through a dead pointer to a node of D.
6. **007-03, step 6: "a cold startup reads at random only what the rerun
   touches, at most a node per level of the tree for each key rerun, and
   the section bounds that ... without T4": partly true.** Proved, for
   BergDB's test too: the section's nodes in order, the writer's paths,
   and the nodes of D (`coldReads_run`). "Without T4" is not shown, since
   |D| is a term: at a start each node of a gd(j) gets an object, read
   from its latest version. "A node per level": with TREE, H + 1 per node
   created, given an entry, touched or made unreachable, and nothing
   bounds `removedAt` yet.
7. **007-01, 7, T3 and T4 together: the parts are proved, not the
   whole.** T3 is in cost, T4 in versions and ids. No theorem joins them
   into one bound on what a start reads and reruns.


## 5. What is not covered

* T4's debt with BergDB's still-dirty test (point 5).
* BergDB's virtual root. `T4_debt` needs `sp.virt = false`, and so does
  `debt_main`. In the model the exact test with a virtual root breaks T1,
  a correct start (`exactWitness3` in `lean/SIS/Example.lean`).
  So BergDB's shape is its own test with the virtual root, and no T4
  statement covers that yet.
* Levels in BergDB's tree. The counts use the root's level number as H.
  In 024-12's `treeSpec` (`lean/SIS/Tree/Spec.lean`) a level is a code of
  segment and height, the top nodes have levels of their own, and the
  virtual root is on level keyMax + 2 + 2^48 - 1. So (H + 1) and lev(x) +
  1 say nothing useful there. A bound for BergDB would count the nodes on
  a path, the height, not the level number.
* A cold start's reads without the |D| term, and a bound on `removedAt`.
* Bytes, and one theorem that joins T3, T4 and the cold reads (point
  7): 007-03's promise. It would need a largest cost of a version, as
  `T3_bounded` assumes a largest record. Best after T4 holds for BergDB.
* Work on the first and fourth points has started (prover "t43", 024-12's
  board, from 12:27). The second and third are not in its brief.


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

**Q2. The trusted definitions as they are (section 2).** Options:

* A. Accept them as they are.
* B. Accept them, with three fixes to comments, no definition changed:
  `BoundCold.lean`'s header says that every object the startup makes is a
  version it reads, which needs "but a virtual root"; `lean/README.md`'s
  list of theorems lacks `coldReads_tree`; and its "Not done" should name
  the virtual root and the |D| term of the cold reads.
* C. Change a definition. To weigh: `onAccessPath` has the touch;
  `levelOf` is a level number; `RecordBound` counts versions, not bytes,
  and leaves out T(i)'s own got-dirty nodes; `T4_ends` adds nothing.

Recommended: B.

**Q3. The scope of the work in progress.** Options:

* A. Add BergDB's virtual root and counts by the height to the brief of
  "t43" (section 5), so that T4 holds for BergDB's own shape.
* B. Keep the brief: BergDB's test without a virtual root first; the
  rest later.
* C. Stop at the exact test.

Recommended: A, with B as a checkpoint on the way. Without them T4 says
nothing yet about BergDB's own tree.


## 7. Log

2026-11-13. Written for Frans's review, from the Lean on `main` at
`8af385a0`, 007-01, 007-03 and 007-08. Checked here: `#print axioms` of
the eleven theorems (`propext`, `Classical.choice`, `Quot.sound`; the
first two cold-start ones without `Classical.choice`); no `sorry`,
`admit`, `native_decide` or `axiom` in the new files; the example's run,
printed record by record; `decide +kernel` (section 4, point 2). Not
rebuilt: 024-12's board reports 327 jobs for `8af385a0`.
