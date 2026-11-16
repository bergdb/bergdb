# 030-02. The plan for the bridges (TP14, TP16, TP19)

Created 2026-11-16 by Frans Lundberg. Status: open (the plan; no proof started).

The plan for 030's direction D3: prove for BergDB's key tree the abstract
model's assumptions TP14 (`RunOK`), TP16 (TREE, A6', A-COPY) and TP19 (the
writer reads only nodes reachable before the transaction), so that recovery,
restarts, lazy reading and eviction with handles (006-26, sections 3.1 to 3.3)
hold for BergDB's tree, and not only for any structure that meets the
assumptions. Written on the night of 16 to 17 November by an agent of
coord-1116 ("I" below), by reading: no build, no run, one scratch check that
the statements below elaborate.


# 1. In short

- **All three rest on `l4` and `htbL`, and on nothing else of D1.** Each
  bridge needs the tree's invariants after every run (TP4, P's tree, the
  kinds, the heights) and the writer's facts at a transaction's end. Only the
  joint induction inside the top theorem `invGetScanOK_merges_tbL` gives them,
  and it takes `l4` and `htbL`. So the bridges will be reduced to the top
  theorem's two open premises, and proved the day D1 proves them, by one
  line of assembly.
- **A finding: TP14 and TP19 are false as stated**, at a run that makes its
  top node of ordinal 2^48. The model puts the root on the level of a top
  node of ordinal 2^48, and its writer has no guard; Java refuses a
  transaction 1,024 below that bound since 005-02. TP16 holds there.
  Section 3. Not proved in Lean (the run is about M · 2^48 transactions
  long); the default is to prove the bridges for runs below the bound.
- **The statements to prove**, from one bundle of D1's facts,
  `TreeRunFacts p` (step 1):
  - TP14: `RunOKTreeB p`, TP14 for runs of fewer than 2^48 transactions;
  - TP16: `EvictRunOKTree p`, as stated;
  - TP19: `ExecReadsReachableOk p` for the transactions the model runs,
    then `ExecReadsReachableB p`, as stated below 2^48 transactions.
- **Size**: about 9,000 to 22,000 lines; 30 to 70 prover-hours at the
  plan's figures, two to four nights of three provers. On 15 November
  planned routes ran 2 to 10 times faster than their plans; the parts with
  no route yet (A6, A-COPY) should be counted at the plan's figures.
- **The order**: tests on runs first (step 0); a shared base (D1's facts
  exported, the two forms of the tree, TREE; steps 1 to 3); then TP14, which
  gives recovery, restarts and T13 for the tree, and with TREE lazy reading
  (steps 4 and 5); then A6 and A-COPY, which give eviction with handles
  (steps 6 and 7); TP19 beside them (step 8).
- **Under MT** the base carries over; the five new facts about the writer
  inside a transaction (W1 to W5) would be redone for MT's writer, and are
  smaller there (section 11).
- **Questions for Frans**: five, each with a default (section 12). The
  first: a guard at ordinal 2^48 in the model's writer, or the bridges with
  a bound (default: the bound; no trusted file changes).


# 2. What the bridges are, and what they give

## 2.1 The three statements as they stand

All in `lean/SIS/Tree/Props.lean` (trusted).

- **TP14**, `RunOKTree p`: `∀ al ts, Within p ts → SIS.RunOK (treeSpec p)
  al ts`. `SIS.RunOK` (`SIS/Assumptions.lean`) is `SpecOK` (TP13, proved:
  `specOKTree`) and, for each transaction j, `StepOK sp P (j + 1) c`: P is
  the model's P after j transactions, which is `treeRun p (ts.take j)`
  (`runPSame`, proved), and c the tree's `exec` on P@(j). `StepOK`'s fields:
  `fresh`, `distinct`, `current` (A2), `dataFixed`, `dataNoPtrs`, `levels`
  (A4), `newReachable` (A3), `noRes` (A5), `virt` (`VirtStep`: `newTop`,
  `topFixed` (R3), `rootAdds` (R2), `closure` (R4), `dead`), and the touch's
  `touchIndex`, `touchReach`, `touchUp`.
- **TP16**, `EvictRunOKTree p`: `∀ al ts, Within p ts → EvictRunOK (treeSpec
  p) al ts`. `EvictRunOK` (`SIS/Phys.lean`): `EvictStep` (`treeAt`, TREE;
  `adoptAt`, A6') at every j up to the run's length, R(0) included, and
  `CopyStep` (A-COPY) for every transaction.
- **TP19**, `ExecReadsReachable p`: `∀ ts, Within p ts → ∀ tx, exec p tx
  (ts.length + 1) (view (treeSpec p) (treeRun p ts) ts.length) = exec p tx
  (ts.length + 1) (viewOf (treeRun p ts))`.
- **A trap in the names.** `SIS.Tree.RunOK p P t` (`GetAssembly.lean`:
  `RunLinksOK`, `TreeAt`, `InvOK`; the run premise in `l4`'s type) is not
  `SIS.RunOK sp al ts`. Inside `namespace SIS.Tree`, write `SIS.RunOK` for
  the abstract one.

## 2.2 What each gives

- `SIS.RunOK` with Java's still-dirty test: `T1_recovery`, `T1_nodes`,
  `T1_crash`, `T2_restart`, `T13_markExact` (`SIS/Theorems.lean`); with
  `CutOK`, `T8_recoverCut` and `T12_restartCut`; and `T4_debt_java`.
- With `LiveAppend` (TP15, proved: `liveAppendTree`) and `TreeRunOK` (TREE
  after every transaction, the first part of TP16): `T1_lazy`, `T2_lazy`,
  `CC_canonical` (`SIS/PhysTheorems.lean`).
- With `LiveAppend` and all of `EvictRunOK`: `TC_handles`, `TR_handles`,
  `TR_handles_restarts`, `TP_handles`, `Rule4Pos_handles`
  (`SIS/HandleTheorems.lean`).
- `bounded_startup` takes `RunOK` and TREE among its premises (D4).
- TP19: no theorem takes it. It ties the tree checker: `Check/TreeRun.lean`
  computes the change from P where the model has P@(i - 1). With TP19 what
  the checker computes is the model's change.

So the milestones, each for BergDB's tree from `l4` and `htbL`:

- M1, TP14: recovery after a crash, restarts, marking (T1, T2, T13).
- M2, TP14 and TREE: lazy reading (T1_lazy, T2_lazy).
- M3, all of TP16: eviction with handles.
- M4, TP19: the tree checker computes the model's change.


# 3. TP14 and TP19 are false as stated after 2^48 top nodes

What I read:

- `Params.topLevel o = keyMax + 1 + o` and `Params.rootLevel = keyMax + 2 +
  (2^48 - 1)` (`SIS/Tree/Node.lean`, which says "ordinals are below 2^48").
  So a top node of ordinal 2^48 is on the root's level. Checked in Lean:
  `p.topLevel (2 ^ 48) = p.rootLevel` by `omega`
  (/Users/f/fl/bench/2026-11-16/night/d3/Forms.lean).
- `newSuperRoot` (`Exec.lean`) makes a top node with the next ordinal
  whenever the space root changes: its split, its time split, root
  collapse. One a transaction at most (later calls change it in place).
  Nothing bounds the ordinal; `boundsOK` checks only key nodes (G and H).
- A run of puts of one key fills the space root, a leaf, with klongs of that
  key, and time-splits it about every M transactions, each time with a new
  top node. Every transaction is sorted, its key well formed, its base
  fresh, and it ends in no error: the run is within reach. After about M ·
  2^48 transactions it makes the top node of ordinal 2^48.
- That transaction's change gives the root the entry `.top z`, with z on the
  root's level. `StepOK.levels` (A4) fails. `reachFrom` follows a pointer
  only to a lower level, so z is not reachable at i: `newReachable` (A3) and
  `current` (A2, for z's own entries) fail too. **TP14 is false** for that
  run.
- After it only the root is reachable. On P@(i) the next transaction's
  writer does not find its top node (`topOf`: "corrupt: top node z is not
  in P@(i-1)") and `exec` gives the empty change; on P itself a put gives a
  change. **TP19 is false** for that run.
- **TP16 holds** there. Only the root is reachable, so TREE and A6' hold
  trivially, and A-COPY does not look at the root's level. No later
  transaction is within reach (each fails at `topOf`).
- Java refuses a user transaction 1,024 below 2^48 since 005-02 (item 002).
  The model's writer lacks that refusal.

Not in Lean: the run itself. A counterexample in Lean needs the writer
evaluated on a symbolic run of M · 2^48 transactions (a shape invariant of
the space root, and every rule of a put and a time split on it): perhaps
1,000 lines, and uncertain. A conditional lemma is cheap: a change that
gives the root a top node of ordinal 2^48 fails `StepOK.levels`.

The options (030's rule: statements change only on Frans's word):

- **(a)** The model's writer refuses as Java does: a `bounds:` error in
  `newSuperRoot` before the ordinal reaches the bound. A change of a trusted
  definition (`Exec.lean`): the gate's base is made again; the lemmas about
  `newSuperRoot` get a throw branch, which `WriterWP` takes for free. TP14
  and TP19 can then be proved as stated.
- **(b)** No change: prove the bridges for runs of fewer than 2^48
  transactions, as new statements beside TP14 and TP19, which stay as they
  are, marked false in 024-12's list of properties with this section as the
  reason. Inside, the proofs use "every top node of P has an ordinal below
  2^48" (`TopsBelow`); fewer than 2^48 transactions give it, since each makes
  at most one top node. With (a) later, `Within` gives `TopsBelow` too.
- **(c)** Restate TP14 and TP19 with the bound.

Default: (b). Recommended for later: (a), so that the model refuses what
Java refuses. Question 1.


# 4. What the tree model gives, and what is missing

## 4.1 From D1, at every run within reach

- Inside the proof of `invGetScanOK_merges_tbL` (`SIS/Tree/DeadTop.lean`),
  as `have`s, not theorems:
  - `hJ`: `RunTreeQ p (LatestQD p)` at every run within reach. That is
    `RunLinksOK` (`PointersOK`, TP4; `KeyHistOK`; `KeyNonempty`), `TreeAt`
    (P's key nodes a tree from the space root, at the run's last time) and
    `LatestQD` (`InvOK`, `PointersOK`, `KindsAllOK`, `HeightAllOK`,
    `SizeOK`, `LeftAllOK`, `DeadAllOK`).
  - `joint` (`jointHtJ_reached1`), at every state between operations:
    `PutInv`, `RangeOrder`, the live counts, `HtInv`, `WriterTreeOK` and
    `J2At`, the take-back's (B) and (C) with their node facts (`J2N`:
    `TtReachedN`, `DeadLiveN`, `OldBelowN`, `OldStartN`, `MadeStartN`,
    `ValsNoNodeN`).
  - Both need `l4` (the live counts) and `htbL` (the fuel). Step 1 exports
    them as one theorem.
- Proved with no premise: `CommitLiftAt` (P after a transaction reads as the
  writer's last state, from `RunLinksOK` before it; `TakeBackRun.lean`);
  `PtrsOK` through the writer for every transaction (`WriterPtrs*.lean`);
  TP13, TP15, TP17, TP18 and `runPSame`; `TakenNotValOK`.

## 4.2 Near the bridges already

- **TREE**: `TreeAt` is the tree's own statement of a tree (006-26, 5.3):
  `TReach` and `TLink` through `knodeOf`'s `liveAt`; `oneLink`, a node is
  named by one live klong of one reached node; `rootFree`, nothing names the
  space root.
- **A2 and A3 for key nodes**: `TtReachedN`, a node with a klong of the
  transaction's time is reached from the space root, and `MadeStartN`,
  every made node starts at the transaction's time; both at the end.
- **(C)**, `DeadLiveN`: a klong to a node the transaction made comes with a
  live klong of the same node to it.
- **The kinds and the heights**: `KindsAllOK` (every klong, live or dead,
  names a node of the right segment, or a value), `HeightAllOK` (live
  children one height below).
- **A template**: `PtrsOK` with `KeepsPtrs` and its tactics (`wpSimplify`,
  `ptCore`, `ptUse`), 1,609 lines with its run (`WriterPtrs*.lean`): an
  invariant carried through every rule of the writer, for every
  transaction.

## 4.3 Missing: the two forms of the tree

- **LiveCorr.** The abstract model's live children of a key node, `blive
  (h.upTo t)` (`Val.lean`: a fold of `setAssoc` over the entries), against
  the tree's `(klongsOf h).liveAt t` (`Inv.lean`: `lastVersionGivenDel` over
  `prefixAt`, with the bitmap at t). No lemma relates them: `blive` appears
  in no proof under `SIS/Tree`. Building blocks: `KlongRoundTrip.lean`
  (`parseKlongEntry`), `SearchFold.lean` (`lookup_setCv`),
  `KlongBitmap.lean`, `Check/Live.lean` (`bstep`, `Has`).
- **ReachCorr.** `reachable (treeSpec p) P t y` (from the root, along live
  pointers to lower levels only) against: y is the root, or the root's live
  top node, or `TReach (knodeOf p (viewOf P)) t r y` from the space root r.
  It needs the levels to fall along every live pointer: for key nodes from
  `KindsAllOK`, `HeightAllOK` and `keyLevel`'s arithmetic (a segment leaf's
  child is in the next segment, at most H high); for the top node, the
  bound of section 3.
- **The top chain.** Every top node of P is reached from the newest one
  through skip pointers (R4), and no older top node is reachable (`dead`).


# 5. TP14

## 5.1 The statement

```lean
/-- TP14 for runs of fewer than 2^48 transactions (bergdb 030-02, section 3). -/
def RunOKTreeB (p : Params) : Prop :=
  ∀ (al : Algo BVal Tx) ts, Within p ts → ts.length < 2 ^ 48 →
    SIS.RunOK (treeSpec p) al ts

theorem runOKTreeB_of_facts (p : Params) (hp : MergeParamsOK p)
    (hF : TreeRunFacts p) : RunOKTreeB p

theorem runOKTreeB_tbL (p : Params) (hp : MergeParamsOK p)
    (hth : 2 ≤ p.theta ∨ p.theta = 0) (htbL : TakeBelowFuelDelSL p)
    (l4 : OpCaseOK p (RunOK p) (QLive p) DelMergeOpenCase) : RunOKTreeB p
```

With question 1's (a): `runOKTree_tbL ... : RunOKTree p`, TP14 as stated.

## 5.2 Field by field, and what each rests on

For transaction j of a run within reach: P is `treeRun p (ts.take j)`, i is
j + 1, c is `changesOf i w` with the touch, w the writer's last state, and
P' is `P.apply i c`, whose key nodes read as w's (`CommitLiftAt`). Every
field uses ReachCorr at P' or at P (both reached states).

- `fresh`, `distinct`: made ids are at or above the base (`fresh` adds 2),
  the base is above P's ids (`Within`), made ids differ. Small.
- `dataFixed`, `dataNoPtrs`: entries go to key nodes of the overlay, to
  values made (`.data`, no pointer), to the root and to the new top node; a
  value is no overlay node (`ValsNoNodeN`). Small.
- `current` (A2) and `newReachable` (A3):
  - key nodes: `TtReachedN` and `MadeStartN` at the end, through
    `CommitLiftAt`, then ReachCorr. Existing facts.
  - values made: W1 (new, section 5.3).
  - the root: always reachable. The new top node: named by the root's last
    entry, below the root's level by the bound.
- `levels` (A4): every pointer of an entry of time i goes to a lower level.
  Time-i klongs, live or dead: W3 (new). The new top node's root pointer (a
  key node) and skips (older top nodes). The root's entry: the bound.
- `noRes` (A5): an old node reachable at i was reachable at i - 1. W2 (new)
  at the end, then an induction along the `TReach` path from the space
  root: a node not in the overlay keeps its live klongs of i - 1.
- `virt`:
  - `newTop`: one top node made, then changed in place; it gets entries.
  - `topFixed`: entries go to key nodes (below `topLevel 0`) and to the new
    top node.
  - `rootAdds`: `changesOf` gives the root its entry exactly when it makes a
    top node; the adds are sorted by node id, the root's first.
  - `closure` (R4): the new top node's skip at its ordinal's lowest set bit
    names the old top node (the old one has no skip at that bit), which
    reaches every older one: a run invariant, `TopChain`.
  - `dead`: a top node's skips name older top nodes, none of them
    reachable.
- `touchIndex`, `touchReach`, `touchUp`: the touch (`touchFrom`) is the top
  node, the space root and the key nodes of `pathFrom` at i - 1, each a live
  child of the one before, so reachable (ReachCorr). With TREE at i - 1
  (step 3), the nodes above a touched node are those before it on its path,
  all touched; the root is the allowed exception.

## 5.3 Three new facts about the writer

Each is stated at the states the writer reaches from a reached P (the
`StateOK` form), or carried for every transaction as `PtrsOK` is; never as
a premise about any state that meets a local invariant (030's rule: on 15
November three premises were false as stated for that reason).

- **W1, `ValsNamed`**: every value the transaction made is named by a live
  klong of an overlay node that has a klong of time i. A put makes it so;
  merges and splits copy live klongs; with one operation a key, no later
  operation deletes it, and a node that holds it is never emptied, so never
  taken back.
- **W2, `LivePtrsKnown`**: every live klong at i of an overlay node, and
  every live klong of its version before the transaction (`toPrev`), names a
  node the transaction made or a node of the view (reachable at i - 1); so
  do the overlay's ids, the space root and the made-for ids. A sketch:

```lean
structure LivePtrsOK (Known : NodeId → Prop) (c : Ctx) (w : W) : Prop where
  live : ∀ q ∈ w.nodes, ∀ cv y, (cv, y) ∈ q.2.liveAt c.i →
    Known y ∨ y ∈ w.made.map (·.id)
  prev : ∀ q ∈ w.nodes, ∀ cv y, (cv, y) ∈ (q.2.toPrev (c.i - 1)).liveAt (c.i - 1) →
    Known y ∨ y ∈ w.made.map (·.id)
  ids : ∀ q ∈ w.nodes, Known q.1 ∨ q.1 ∈ w.made.map (·.id)
  rootKey : Known w.top.rootKey ∨ w.top.rootKey ∈ w.made.map (·.id)
  madeFor : ∀ q ∈ w.madeFor, Known q.2 ∨ q.2 ∈ w.made.map (·.id)
```

  With `Known y := (c.view y).isSome` and a view whose live klongs name
  nodes of the view (ReachCorr gives that for P@(i - 1)), it holds for every
  transaction, sorted or not, like `PtrsOK`. TP19 uses it too.
- **W3, `KlongLevels`**: every key klong of time i of a kept overlay node
  names a node of a lower level: in an inner node, a node of its segment
  one height below; in a segment leaf, a node of the next segment or a
  value.

## 5.4 Size and risks

- Size, the shared base aside: 2,500 to 6,500 lines; 7 to 20 prover-hours
  at the plan's figures.
- False as stated: section 3; handled by the bound.
- W3 for a dead klong of time i. The writer's books keep heights for live
  klongs (`NodeHt`), not for dead ones; `OverlayKinds.lean` says "a dead
  klong can name a node of another height" (a retarget at the parent of a
  root that a split made: a segment leaf or the top node, where the level
  falls anyway). Test W3 before proving it.
- A5 through a take-back that retargets a klong to the node a split
  replaced: that node was read, so it was reachable at i - 1. W2 covers it
  if the made-for ids are known, as `PtrsOK.madeFor` has them.
- `touchUp` needs TREE at i - 1, so TP14 waits for step 3.


# 6. TP16

## 6.1 The statement

TP16 as stated:

```lean
theorem evictRunOKTree_of_facts (p : Params) (hp : MergeParamsOK p)
    (hF : TreeRunFacts p) : EvictRunOKTree p

theorem evictRunOKTree_tbL (p : Params) (hp : MergeParamsOK p)
    (hth : 2 ≤ p.theta ∨ p.theta = 0) (htbL : TakeBelowFuelDelSL p)
    (l4 : OpCaseOK p (RunOK p) (QLive p) DelMergeOpenCase) : EvictRunOKTree p
```

The run that reaches ordinal 2^48 needs a short case of its own: only the
root is reachable there.

## 6.2 TREE at every j

From `TreeAt` (`oneLink`, `rootFree`) with LiveCorr and ReachCorr. A
reachable node but the root has one reachable parent: the root for the
newest top node; that top node for the space root (nothing else names it:
`rootFree`, and a top node's only live child is its root pointer); one key
node for every other node, values included (`oneLink`). No key node names a
top node (`KindsAllOK`). R(0) by a direct proof. Rests on `TreeAt`,
`KindsAllOK`, `HeightAllOK` and `PointersOK` at every run (D1). 300 to 800
lines; 1 to 3 hours.

## 6.3 A6' at every j, through A6

Prove the stronger A6 for the tree, and derive A6'. A6: every pointer of a
reachable node that is not its live child names a value or a node that is
not reachable. Frans's decision of 2026-11-11 (024-12, section 6.2): "The
gates will require A6, not A6'"; TP16's statement stays.

- A run invariant, `DeadUnreach P t`, by induction over the run.
- A pointer dead before T(i): its target was a value or not reachable at
  i - 1, and by A5 (TP14) is not reachable at i.
- A pointer that T(i) kills, or a klong of time i that is dead at i: its
  target is a value; or a node the transaction made, and then (C) gives a
  live klong of the same node to it, so it is no case; or an old node that
  T(i) unlinked from that node. **W4** (new): at the end, an old node
  unlinked from a kept node is not reached from the space root. The cases:
  a merge (both merged nodes left out), a split and a time split (the node
  replaced), root collapse (the old root), the upward delete (the emptied
  chain), LE-b (the child stays, under the empty key), a retarget (the old
  node is a live child of the same parent again).
- Size: 1,500 to 4,000 lines; 4 to 12 prover-hours. The riskiest part: no
  route exists, and W4 goes through the delete with the merges, as (B) and
  (C) did (`TakeDead*.lean`).

## 6.4 A-COPY for every transaction

- **W5, `CopySrc`** (new): every key klong of time i of an overlay node,
  every made-for id, the top node's root pointer and its skips name a node
  the transaction made, or a node z that the writer read from P@(i - 1), or a
  live child of such a z before the transaction, where z is changed,
  replaced or unlinked by the transaction's end. Such a z is in `pathOf`: it
  was reachable at i - 1, and it is changed or not reachable at i.
- A risk to test first: a node that the writer read and copied from, and
  that is live again at the end with no change. The case I see: a split's
  node when one half is taken back and its parent's klong retargeted to the
  old node. Then `pathOf` may not hold the old node, and its parent's
  pointees hold the old node but not its children. 024-12's take-back runs
  (`TakeBackRunExample.lean`) have such transactions.
- Size: 1,000 to 3,000 lines; 3 to 8 prover-hours.


# 7. TP19

## 7.1 The statements

```lean
/-- TP19 for the transactions the model runs (bergdb 030-02, section 7). -/
def ExecReadsReachableOk (p : Params) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) →
    exec p tx (ts.length + 1) (view (treeSpec p) (treeRun p ts) ts.length) =
      exec p tx (ts.length + 1) (viewOf (treeRun p ts))

/-- TP19 below 2^48 transactions (bergdb 030-02, section 3). -/
def ExecReadsReachableB (p : Params) : Prop :=
  ∀ ts, Within p ts → ts.length < 2 ^ 48 → ∀ tx : Tx,
    exec p tx (ts.length + 1) (view (treeSpec p) (treeRun p ts) ts.length) =
      exec p tx (ts.length + 1) (viewOf (treeRun p ts))
```

Each with `_of_facts` and `_tbL` theorems as in 5.1. With question 1's (a):
`ExecReadsReachable p` as stated.

## 7.2 How

- The writer reads P in three places only: `getNode` (`c.view x`, the one
  read inside the monad), `topOf` and `lastTop` (outside it). A grep of
  `Exec.lean` finds no other.
- **19a**, the transactions the model runs: a frame lemma for every
  function of the writer. Two contexts that differ only in the view, the
  first's a part of the second's: a run that ends well on the first ends the
  same on the second. Generic, with no invariant: `getNode` finds the node
  in both, or throws on the first. A sketch:

```lean
def ViewSub (c c' : Ctx) : Prop :=
  c'.p = c.p ∧ c'.i = c.i ∧ ∀ x nd, c.view x = some nd → c'.view x = some nd

def MonoV {α : Type} (f : M α) : Prop :=
  ∀ c c' w r, ViewSub c c' → f c w = .ok r → f c' w = .ok r
```

  Then `Within p (ts ++ [tx])` says the run on P@(i - 1) ends well, so the
  run on P gives the same change. The touch: `pathFrom` goes from the space
  root along live klongs at i - 1, so it reads only reachable nodes
  (ReachCorr), where the two views agree (P's entries are all of time i - 1
  or before).
- **19b**, every transaction below the bound: a simulation. Under W2 the
  writer's next read is of a node of the overlay or of P@(i - 1), so both
  runs go step by step alike, errors included. W2 holds for every
  transaction, so 19b covers transactions out of order, with a key twice, or
  with a base below P's ids (the ids made then collide with P's; `getNode`
  looks in the overlay first, so P is not read for them).
- What the checker needs: 19a ties it when the model's run ends well; only
  19b says that the checker's change is the model's for every transaction.

## 7.3 Rests on, size, risks

- Rests on ReachCorr and the levels at P, so on D1's run facts (`l4`,
  `htbL`); 19a on no fact of the writer; 19b on W2.
- Size: 19a 1,000 to 2,000 lines (about 60 functions of the writer, each a
  frame lemma in `PtrsOK`'s style), 2 to 5 hours; 19b 1,500 to 3,000 lines
  more, 4 to 8 hours.
- False as stated: section 3.
- Every read along a live klong: `mergeIdx` and `emptyKeyNext` pick, among
  the klongs the last bitmap does not delete, the last of a compare value,
  so live ones. I read those two and `sibling`, not every call site of
  `getNode` (37 lines of `Exec.lean` name it, the view or `knodeOf`).


# 8. The steps

Each step by an Opus 5.5 prover at xhigh effort, in its own clone, under
the night's rules (/Users/f/fl/bench/2026-11-16/night/common.md, or the
day's). New files go in `lean/SIS/Tree/`, named `Bridge*.lean`, imported
from `SIS.lean`. The gate's trusted closure counts every constant of a module
outside `SIS/Tree`, so a file in `SIS/Proof` or `Check` would fail it.
Commits start "030-02: ". The State section below is the provers' note.

- **Step 0. Tests on runs** (one agent, 2 to 4 hours, no proof). Scratch
  files in the agent's directory, as the fit/ scripts
  (/Users/f/fl/bench/2026-11-13/cost/fit/), with the checker's functions
  (`Check/Steps.lean`: `stepFailures`, `treeFailures`, `adoptFailures`,
  `copyFailures`); runs under a heavy slot (`slot.sh`).
  - The bridges on the model's runs with the merges and Java's theta, at
    node sizes 8, 14 and 30: `lake exe treetest model M seeds steps keys
    merge theta` (`modelRun` checks `StepOK`, TREE, A6', A6 and A-COPY) and
    `lake exe treetest merges`; with the counts of merges, take-backs and
    root collapses that the runs reached.
  - TP19 on random runs at every transaction, with transactions out of
    order, with a key twice and with stale bases besides sorted ones
    (`treetest` checks it only in the exhaustive runs, to depth 4).
  - LiveCorr on every key node at every time of those runs.
  - W1 to W5 at every state between operations, as
    `TakeBackRunExample.lean` computes (A) and (B); the take-back's cases
    counted, and the A-COPY case of 6.4 sought out.
  - Done when: a report with the counts and every failure. A failure stops
    the proof of its item (section 10).
- **Step 1. `TreeRunFacts`** (0.5 to 1 hour; 100 to 250 lines). Can start
  at once.

```lean
/-- What the bridges take from D1 (bergdb 030-02, step 1). -/
def TreeRunFacts (p : Params) : Prop :=
  (∀ ts, Within p ts → RunTreeQ p (LatestQD p) (treeRun p ts) ts.length) ∧
  StateOK p (RunTreeQ p (LatestQD p)) (fun ts tx w =>
    WriterTreeOK p (treeRun p ts) (ts.length + 1) w ∧
    TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w)

theorem treeRunFacts_tbL (p : Params) (hp : MergeParamsOK p)
    (hth : 2 ≤ p.theta ∨ p.theta = 0) (htbL : TakeBelowFuelDelSL p)
    (l4 : OpCaseOK p (RunOK p) (QLive p) DelMergeOpenCase) : TreeRunFacts p
```

  The proof is the top theorem's own up to its `hJ` and `joint`, copied;
  the top theorem stays as it is. A later step may add a field (`PutInv`,
  `HtInv`). If D1 changes `l4`'s form (030-01), only this theorem changes.
- **Step 2. The two forms** (3 to 8 hours; 800 to 2,000 lines; two agents):
  - 2a, LiveCorr, with no run facts: `y ∈ blive (h.upTo t) ↔ ∃ c, (c, y) ∈
    (⟨b, klongsOf h⟩ : KNode).liveAt t`, for a history of key and delete
    entries with its times in order (what `KeyHistOK` gives).
  - 2b, ReachCorr, the levels along live pointers and the top facts (one
    root pointer a top node; ordinals at most the transactions; `TopChain`;
    `TopsBelow` from the bound), from 2a's statement as a hypothesis until
    2a lands.
- **Step 3. TREE at every j** (1 to 3 hours; 300 to 800 lines): `treeAt`
  from `TreeAt`; R(0); the case at the bound. After step 2.
- **Step 4. TP14's fields but A2 to A5** (3 to 8 hours; 1,000 to 2,500
  lines): `fresh`, `distinct`, the data rules, `VirtStep`, the touch. After
  steps 2 and 3.
- **Step 5. TP14's A2, A3, A4, A5** with W1, W2 and W3; then
  `runOKTreeB_tbL` and milestones M1 and M2: T1, T1_crash, T2, T13,
  T1_lazy and T2_lazy for BergDB's tree, each from `hp`, `hth`, `htbL`,
  `l4` and the bound (4 to 12 hours; 1,500 to 4,000 lines). W2 can start
  after step 2a, with `PtrsOK` as its template; W1 and W3 after step 1.
- **Step 6. A6 and A6'** with W4 (4 to 12 hours; 1,500 to 4,000 lines).
  After step 5's A5.
- **Step 7. A-COPY** with W5; then `evictRunOKTree_tbL` and milestone M3,
  the handle theorems for the tree (3 to 8 hours; 1,000 to 3,000 lines).
  After step 3.
- **Step 8. TP19**: 8a (19a, `MonoV`) after step 2; 8b (19b) after W2 (6 to
  13 hours; 2,500 to 5,000 lines).
- **Step 9. The rest of the assembly** and the list of corollaries, if
  steps 5 and 7 left any (1 to 2 hours; 200 to 500 lines).

What runs in parallel:

- First, step 0 beside steps 1 and 2a, which do not depend on the tests
  (step 1 is a copy; 2a is about two folds).
- Then three provers on different files: A takes 2b, 3, 4, then 6; B takes
  W2, 8a, then 8b; C takes W1 and W3, step 5's assembly, then 7.
- In all: about 9,000 to 22,000 lines; 30 to 70 prover-hours at the plan's
  figures.


# 9. Tests and the gate

- Every new statement is checked on runs first, in step 0 or in its step's
  own scratch run, before its proof.
- The gate: `sh /Users/f/fl/bench/2026-11-16/night/gate-1116.sh <clone>
  <outdir>` tonight; later the day's gate, which the coordinator re-bases on
  `main`. It passes only with:
  - no forbidden word in `lean/` (its grep finds "sorry" and "admit" in
    comments too: do not write them);
  - the trusted closure unchanged: no constant outside `SIS/Tree`, no
    change to `Props.lean`, `Read.lean`, `Exec.lean`, `Spec.lean`,
    `Node.lean` or `Check/` (question 1's (a) would need a new base);
  - the top theorems' statements unchanged;
  - every module of `SIS/Tree` imported.
- On GATE PASS: "GATED NAME <commit> gate-N: <theorem> with premises
  <list>" to main; the coordinator lands it.
- The new top theorems (`runOKTreeB_tbL`, `evictRunOKTree_tbL`,
  `execReadsReachableOk_tbL`, `execReadsReachableB_tbL`, the milestones'
  corollaries) join the gate's audit list when they land (the coordinator
  changes the gate); until then each prover reports `#print axioms` for
  them.
- Java stays tied by the trace checker (level 2 to 4, night.sh); the
  bridges change nothing there.


# 10. Stop rules

- The STOP file of the night (/Users/f/fl/bench/2026-11-16/night/STOP, or
  that day's), checked before each build and every 20 minutes; the night's
  clock (no new step after 04:30; stop at 05:30).
- A test fails: no proof of that item. Report the run. For a stated
  property: the counterexample in Lean and the strongest true form as a new
  statement; TP14, TP16 and TP19 are never changed (Frans decides).
- A step passes three times its planned lines or hours with nothing gated:
  stop it, write the State note, report.
- A step needs a change of a trusted definition or of an existing
  statement: stop, report (question 1 is one).
- Frans decides MT: stop the parts inside a transaction (W1 to W5, step 8b),
  keep what is gated, plan them again for MT's writer.
- D1 restates `l4` (030-01): only step 1 changes.


# 11. Under MT and subtransactions (026-18), briefly

- The abstract model does not change. Each subtransaction is a model
  transaction with its own time and record (026-18, section 3), so the
  bridges are stated per subtransaction, as now; the readers' visible times
  are outside them.
- Carries over: steps 1 to 4, and 8a's frame lemma, done again mechanically
  for the writer's changed functions. They speak of P between transactions
  and of the abstract model.
- Gets smaller: W1 to W5. No node is made and left out (006-28, 7.5: "A2
  and A3 (TP14) have no take-back to argue about"). A user subtransaction
  makes no merge, no upward delete and no root collapse; a fix step merges,
  unlinks or collapses nodes from before it, which then are not reachable
  (A6), and copies only from them (A-COPY). Not sized; my guess is half of
  steps 5 to 7 or less.
- Unchanged: the 2^48 bound, reached sooner (a fix step that changes the
  space root makes a top node).
- So the base is worth doing before Frans's decision; the writer-level
  parts are not.


# 12. Questions for Frans

1. **The ordinal bound** (section 3): (a) the model's writer refuses as Java
   does, a trusted change with a new gate base; (b) the bridges with the
   bound as new statements, TP14 and TP19 kept and marked false; or (c)
   TP14 and TP19 restated with the bound. Default: (b) now; (a) when the
   trusted files next change.
2. **The counterexample in Lean** for section 3: the whole run is a
   symbolic run of M · 2^48 transactions, perhaps 1,000 lines, uncertain.
   Default: the conditional lemma (a change that gives the root a top node
   of ordinal 2^48 fails `StepOK.levels`; tens of lines) and the argument in
   prose in 024-12's list of properties; the whole run only on your word.
3. **TP19's scope**: 19a (the transactions the model runs) is cheap; 19b
   (every transaction, as stated) needs W2. Default: both, 19a first, 19b
   after TP14.
4. **A6 for A6'**: prove A6, as your decision of 2026-11-11 asks of the
   gates, and derive TP16's A6'; TP16's statement stays. Default: yes.
5. **When**: 030's map puts D3 after D1's top theorem, or after D2's
   decision if MT is taken. Default: steps 0 to 3 whenever a prover is free
   (they hold under both outcomes and do not wait for `l4` or `htbL`); steps
   4 to 8 after your MT decision.


# 13. What I could not check

- No run: W1 to W5 and A6 are untested; TP19 is tested only in the
  exhaustive runs to depth 4.
- LiveCorr's corners: a delete of a compare value with no klong; the
  bitmap's bits by index against `setAssoc` by compare value.
- That the run to ordinal 2^48 exists: by my reading of `newSuperRoot` and
  the time split, not built.
- Whether W3 holds for every dead klong of time i.
- A-COPY through the take-back's corners (6.4).
- That no proof uses TP19: none found by grep; `TreeTest.lean` and
  `Check/TreeRun.lean` name it in comments.
- The sizes: by analogy with the take-back's (B) and (C) through every rule
  (`TakeInv*.lean`, `TakeDead*.lean`, `TakeBackRunJ*.lean`: 38 commits from
  19:21 to 22:32 on 13 November) and with `PtrsOK` (1,609 lines). The
  bridges are statements of a new kind, so 15 November's speed may not
  hold for them.
- The cost of `treetest model` at node size 30.
- My one check in Lean: the statements of sections 5, 7 and 8 and a
  corollary for T1 elaborate against `main`'s `lean/` (in htbl's clone,
  /Users/f/fl/bench/2026-11-16/night/d3/Forms.lean, with placeholder
  proofs), and `p.topLevel (2 ^ 48) = p.rootLevel`.


# State

2026-11-16, 22:31: the plan is written; no step has started.


# Log

2026-11-16, 22:04 to 22:31. Written by an agent of coord-1116 for D3. Read
006-26 (sections 1 to 5, 8), 006-28 (sections 4 and 7.5), 026-18, 024-12
(sections 4.3 and 6), `Props.lean`, `Assumptions.lean`, `Phys.lean`, the
abstract theorems' statements, `DeadTop.lean`, `Exec.lean`'s writer and the
tree's run facts. One scratch check in Lean (section 13).
