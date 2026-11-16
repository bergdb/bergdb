# 026-19. The proof trial of 026-18: subtransactions in Lean

Created 2026-11-16 by Frans Lundberg. Status: open (the plan written; the
trial not started).

A short proof trial of 026-18's idea, on MT's rules as 026-17 tried them
(`Mt.lean` on the branch `026-17-mt-trial`): prove that one fix step
keeps the invariant that holds between subtransactions, and that gets and
scans are right at the times that end a main transaction. It turns the
proofs' gain, an estimate in 006-28 and 026-17, into evidence before
Frans decides MT, NW or neither.

Frans, 2026-11-16, 13:11, on 026-18: "A "short proof trial" does seem
reasonable. Perhaps starting tonight after 22.00, we will see. Depends on
other work." 13:48: "Plane the short proof trial (3). Use a Fable High
agent."

The proposal it starts from (026-18, section 5): one or two
prover-days; (1) a step lemma: one fix step (a merge) keeps the
in-between invariant, the full invariant with holes on the paths of the
keys still being fixed; (2) gets and scans right at visible times from
the full invariant, reusing today's proofs; (3) if time allows, the holes
close when the driver ends, for one key.

The plan follows.


# 1. The plan in short

Written 2026-11-16 by an agent of coord-1116 (Fable, high). "I" below is
that agent. Nothing is proved here, and no proof is started. The
statements of section 3 are Lean text in
[19-proof-trial/](19-proof-trial/): the runs' definitions are
type-checked as they are; the invariants and the targets are type-checked
against stand-ins only (section 11).

**What the trial is to prove.** One statement at the top, `VisibleOK`:
at every visible time of an MT run in the model, the tree has today's
invariant, and every get and every scan returns what the reference map
gives. For the database: after each main transaction (a user transaction
and its fix steps), readers see a tree as sound as today's and the right
data, though the tree was under the fill or had empty leaves in between.
The trial proves the fix step that is a merge, and the readers; the other
kinds of subtransaction stay named premises. So the top statement will
be **reduced**, not proved (006-26's senses), and the plan says to what.

**Three findings in the code shape the plan** (section 2):

1. Today's invariant has a name and a form that takes holes well. The
   run induction carries `RunTreeQ p (LatestQD p)`. Its three fill
   checks (K5's `NonEmptyOK`, `RootsOK`, `FillOK`) are one predicate,
   `LiveCounts`. The in-between invariant is the same list of parts with
   `LiveCounts` asked only outside the paths of the pending keys.
2. Gets do not follow from the invariant. Today each step of the writer
   proves that it changes the reading of its own key only. Scans do
   follow, from the invariant and the gets, by one lemma that speaks of
   any structure (`scan_eq_contents`): it reuses unchanged. So "gets
   right at visible times" needs the gets carried through every
   subtransaction; the trial does it for the merge.
3. Today's proofs have two layers. The lower one speaks of any state of
   the writer (`WriterWP (merge x d) c w ...`) and can be reused: by
   reading, `Mt.merge` is today's `merge` on nodes from before the
   transaction, but the books. The upper one, the run induction, is
   stated for `treeRun` and `Within`, today's transactions; it must be
   restated for MT's two kinds. Its size is what 006-28 could not
   estimate.

**The steps** (section 6): a setup; then two provers side by side, one
on the fix step at the writer's state (the bridge to today's `merge`,
the path, the fill with holes), one on the run (the lift to the
structure, the readers, the induction); then the frame, the driver's end
for a key, and if time allows unlink, collapse and the user's delete.
4,200 to 11,000 lines, about 14 prover-hours for the first two tiers.

**Evidence** (section 4): seven measures, read in a few lines. First
among them: the lines and hours of "a merge keeps the fill" under MT,
against today's open premise `l4` (not proved, 3,000 lines or more by
006-27's estimate), and whether a premise of `l4`'s or `htbL`'s kind is
left.

**The cost** (section 8): one night, 22:05 to 06:00, two provers at
most, Opus 5.5 at xhigh; about 10 % of the new week.

**A limit, said first.** With the bridge, MT's proof of the merge stands
on today's lemmas, the take-back's branches included. The trial measures
what MT adds and which premises go. What MT frees stays 026-17's count
(C4: 8.4 % of the tree by name, 19.9 % by text), unless measure E6 can
be taken.


# 2. What the code has today

Read on main at 60623acb; `lean/` there is the same bytes as at the
branch point of `026-17-mt-trial` (`git diff d8da4a35 main -- lean` is
empty). `lean/SIS/Tree` has 474 files, 167,243 lines.

## 2.1 The invariant: its name and its parts

- **TP6, `InvOK p P t`** (Props.lean): `faultsAt p (viewOf P) t = []`,
  the walk of Inv.lean that the tree checker runs. K4 and K5 of MT's
  trial use this walk.
- **What the run induction carries**, the full invariant, I:
  `RunTreeQ p (LatestQD p) P t` (TakeBackRun.lean, DeadRun.lean,
  LatestJoint.lean). Its parts:
  - `RunLinksOK p P t`: `PointersOK`, `KeyHistOK`, `KeyNonempty`;
  - `TreeAt p P t`: the key nodes reached at t are a tree;
  - `InvOK p P t`;
  - `PointersOK P`, `KindsAllOK p P`, `HeightAllOK p P t`, `SizeOK p P`,
    `LeftAllOK p P`;
  - `DeadAllOK p P`.
- **`InvOK` from parts.** `invOK_of_parts` (InvAssembly.lean) builds it
  from `RootKeyOK`, `KeyNodesOK`, `KindsAllOK`, `HeightLiveOK`,
  `NonEmptyOK`, `LeftmostOK`, `RootsOK`, `FillOK` and `RangeAtOK`. The
  last lines of `invOK_snocR` (LatestJoint.lean) get each of them from
  the parts above, from `RangeAtOK`, and from the three fill checks.
- **The three fill checks are one predicate.** `LiveCounts p N t r`
  (LiveCounts.lean), over any reader of nodes N: a node reached with the
  walk's flags has a live klong unless it is the space root as a leaf;
  an inner segment root has two; with the merges on, a node that is not
  a root has m. `liveCounts_parts` gives `NonEmptyOK`, `RootsOK` and
  `FillOK` from it. These are exactly the faults that K5 allows on a
  pending key's path.
- **At the writer's state** the induction along a transaction carries
  `PutInv c base w`, `RangeOrder`, `LiveCounts`, `HtInv`, `WriterTreeOK`
  and the take-back's `J2At` (`jointHtJ_reached1`, StratumChk.lean).
- **The top theorem** `invGetScanOK_merges_tbL` (DeadTop.lean) gives
  `InvPreserved`, `GetOK`, `ScanOK`, `LatestGetOK` and `LatestScanOK`
  from `hp`, `hth`, `l4` and `htbL`. `l4` is "a delete with the merges
  keeps `LiveCounts`" (`OpCaseOK p (RunOK p) (QLive p)
  DelMergeOpenCase`); `htbL` is the fuel of a node that a delete takes
  back.

## 2.2 How gets and scans follow today

- **Scans, from the invariant and the gets.** `scan_eq_contents`
  (ScanLatest.lean): for any P with `HighKindsOK`, `DataEntriesOK`,
  `ViewEncoded` and `InvOK p P t`, a scan gives the tree's contents in
  its range and order. It names no run. `rootContents_eq_refKvs` then
  makes the contents the reference's, from the gets
  (`latestScanOK_of_latestGet`).
- **Gets, from the writer, step by step.** `LatestGetOK` comes from
  `TxGetOK` (GetLatest.lean): after a transaction a get gives the
  operation's value for its key, and what it gave before for every other
  key. That comes from each operation's case at the writer's state
  (`OpGetOK`, GetWriter.lean) and the lift to the structure. A get is
  not a function of `InvOK` alone.
- **Earlier times**, from append-only histories: `getOK_of_latest`
  (HistoricalGet.lean), `scanOK_of_latest` (HistoricalScan.lean,
  `scan_of_readExtension`).

So 026-18's "the readers' theorems are stated only where the full
invariant holds, so today's proofs of gets and scans carry over" is
right for scans and for the reader's side of gets. The writer's side of
gets is per step, and MT's steps are new. The gets are right at every
boundary of MT's runs, the untidy ones too (026-17, K1), so the trial
carries them at every state, not only at visible times.

## 2.3 The merge's proofs: two layers

- **The writer's layer, for any state.** For `merge x d` from a state
  with `PutInv`, `PutInvG`, `RangeOrder` and the path down to x
  (`PathOK`), the parent inner:
  - the tree: `writerWP_merge_tree_inv2` (MergeTreeInv.lean);
  - the ranges: `writerWP_merge_range_inv` (RangeMergeRoot.lean);
  - the reading: `writerWP_merge_get_inv` (GetMergeInv.lean), when the
    state after fits the fuel;
  - the kinds, the heights, the dead klongs, the leftmost klong, the
    books: `kd_merge` (WriterKindsMerge.lean), `ht_merge`
    (WriterHeightsMerge.lean), `dw_merge` (DeadMergeStep.lean),
    `left_merge` (WriterLeftMerge.lean), `putBook_merge`
    (DelMergeBook.lean);
  - the take-back's facts: `writerWP_merge_any_j2` (TakeMergeAny.lean)
    and the loop's `writerWP_mergeUp_delJ` (TakeDelMergeKd.lean).
- **The fill has no such lemma for a whole merge**: that is `l4`, open.
  Its pieces exist: `mergeKlongs_live_fill` (MergeLiveFill.lean: the
  merged nodes hold m live klongs each when the two together hold m),
  `halves_live_fill` (SplitLiveFill.lean), LiveChain.lean's counts, and
  the cascade's steps with exceptions, `LiveEdgesX` (LiveStepsX.lean,
  846 lines; `writerWP_appendKlongs_chainGLX`, WriterTreeChainG.lean).
  `LiveEdgesX` asks that an excepted node is named by segment leaves
  only (a new segment's empty leaf), so it does not fit a hole below an
  inner node as it is.
- **The run's layer, for today's runs only.** The lift of a writer's
  last state to the structure and the step of the invariant are stated
  for `treeRun p ts` and `Within p (ts ++ [tx])`: `commitLiftAt_of_links`
  (TakeBackRun.lean), `liveCounts_commit`, `rangeAtOK_commit`
  (LiveCounts.lean), `invOK_snocR` (LatestJoint.lean), `latestQD_snocR`
  (LatestTop.lean), `OpCaseOK` (GetOpAssembly.lean). A run of MT is no
  `treeRun`: its transactions are `Mt.runUser` and `Mt.runFix`, not
  `exec`.
- **Sizes of today's proofs of the same case**, for section 4:
  - files of `lean/SIS/Tree` with `Merge` in the name: 87 files, 37,571
    lines (the largest: MergeTreeInv 2,301, GetMergeLevel 2,101,
    TakeMergeRoot 1,991, GetMergeRoot 1,781, TakeMergeTail 1,761,
    GetMergeAny 1,669);
  - of them the merge's take-back (`^Take.*Merge|Merge.*Made|Retarget`):
    14 files, 10,215 lines;
  - every take-back file (`^Take|MadeFor|DelHole|Retarget`): 52 files,
    22,826 lines;
  - the fill (`^Live|LiveFill|LiveKeys|LiveOrder`): 21 files, 5,515
    lines;
  - the fuel and the heights (`^Heights|^Ht|Fuel|Stratum`): 29 files,
    11,357 lines.

## 2.4 MT's definitions against today's

By reading `Mt.lean` (branch `026-17-mt-trial`, cbe51516) beside
Exec.lean; not checked in Lean.

- **`Mt.merge` is `merge` without the books.** The two texts differ in:
  the check of an empty node (MT: only for inner nodes, R3); the made
  nodes (MT: an error; today: retarget and take back); `setMadeFor`
  (MT: none); `unlink` of the two merged nodes (MT: none; today it
  changes nothing when the node has no klong of the transaction's
  time); the notes. So from a state where neither node is of the step's
  time and neither is empty, a run of `Mt.merge` is a run of `merge`
  that ends in the same state but `madeFor` and `trail`. The empty leaf
  (R3) has no counterpart: today's `merge` ends in a `Bug:` there.
- **A put is today's put.** `Mt.putKv (.put key h)` and
  `putKv (.put key h)` differ only in the unused parameter `key`.
- **R1's delete** is `deleteUpward`'s first lines: `appendDeleteKlong`,
  unchanged.
- **The path.** `Mt.path` is a new loop (`pathGo`); it visits the nodes
  that a reading of the key visits, which today's proofs have as a pure
  function, `fromVisits N t fuel key r` (GetFrame.lean), with frame
  lemmas (`getEqR_frame`, `getFromR_frame`).
- **`unlinkTree` and `collapse`** call `appendDeleteKlong` and
  `replaceRoot`, unchanged; today's lemmas for them
  (`writerWP_appendDeleteKlong_*`, `writerWP_replaceRoot_*`) are the
  candidates.


# 3. The statements

The Lean text is in `19-proof-trial/MtRun.lean.txt` and
`19-proof-trial/MtSub.lean.txt`; step P0b makes them
`lean/SIS/Tree/MtRun.lean` and `MtSub.lean`. Each target is a
proposition `T_...`; a proved target is a theorem `t_... : T_... p`. All
is in the namespace `SIS.Tree.Mt`.

**Two rules for every statement here.**

- **The fixed statements** are those of MtRun.lean (the runs, `ReadsOK`,
  `ScansOK`), `Full`, `LiveCountsH`, `Hole` and `VisibleOK`. They say
  what the result means. A prover does not change them; if one is wrong
  he stops that step and writes why (section 6.3).
- **The working statements** are `Sub`, `StInv`, `FixW`, `FrameW`,
  `DelW` and the obligations built on them. A prover may add a part to
  `Sub` or `StInv`, or a hypothesis to `FixW`, `FrameW` or `DelW`, when
  a proof needs a book that holds at the reached states. Each such
  change is one line in his GATED message and in this entry's log, and
  (a2) and the induction must still hold with it.

## 3.1 The runs

Type-checked. A state, a step, the reached states, the reference:

```lean
structure St where
  P : Struct BVal
  t : Time
  pend : List Key
  ops : List Op

def St.init (p : Params) : St := ⟨initStruct p, 0, [], []⟩

def commit (P : Struct BVal) (i : Time) (w : W) : Struct BVal := P.apply i (changesOf i w)

def fixOf (p : Params) (base : NodeId) (key : Key) (i : Time) (view : View BVal) :
    Except String (Fix × W) :=
  runWith p base i view (do path key; target)

inductive SubStep (p : Params) : St → St → Prop
  | user (s : St) (tx : Tx) (noops : List Bool) (w : W) :
      s.pend = [] → tx.sorted = true → tx.wf = true → (∀ q ∈ s.P, q.1 < tx.base) →
      runUser p tx.base tx.ops (s.t + 1) (view (treeSpec p) s.P s.t) = .ok (noops, w) →
      SubStep p s ⟨commit s.P (s.t + 1) w, s.t + 1, deletedKeys tx.ops noops, s.ops ++ tx.ops⟩
  | fix (s : St) (k : Key) (rest : List Key) (base : NodeId) (w : W) :
      s.pend = k :: rest → (∀ q ∈ s.P, q.1 < base) →
      runFix p base k (s.t + 1) (view (treeSpec p) s.P s.t) = .ok (true, w) →
      SubStep p s ⟨commit s.P (s.t + 1) w, s.t + 1, k :: rest, s.ops⟩
  | done (s : St) (k : Key) (rest : List Key) (base : NodeId) (w : W) :
      s.pend = k :: rest → (∀ q ∈ s.P, q.1 < base) →
      runFix p base k (s.t + 1) (view (treeSpec p) s.P s.t) = .ok (false, w) →
      SubStep p s ⟨s.P, s.t, rest, s.ops⟩

inductive Reached (p : Params) : St → Prop
  | init : Reached p (St.init p)
  | step (s s' : St) : Reached p s → SubStep p s s' → Reached p s'

def St.ref (s : St) : List Tx := [{ base := 0, ops := s.ops }]

def ReadsOK (p : Params) (s : St) : Prop :=
  ∀ key, keyWf key = true → get p (viewOf s.P) s.t key = refGet s.ref 1 key

def ScansOK (p : Params) (s : St) : Prop :=
  ∀ (req : ScanReq) (limit : Nat), req.wf = true →
    (scan p (viewOf s.P) s.t req limit).map (fun kv => (kv.key, kv.h)) = refScan s.ref 1 req limit
```

- **What it says.** `pend` is the driver's list (R5): the user
  subtransaction's deleted keys, in key order; a fix step is for the
  first of them; a key leaves when `runFix` returns false. A state with
  `pend = []` is at a visible time. This is `Mt.fixAll`'s order, as a
  relation; the trial does not prove that `fixAll` follows it.
- **Each subtransaction has a time of its own**, as in MT's trial and as
  026-18, section 3, proposes. A `done` uses no time.
- **As `Within`:** a step has no error, the user's keys are sorted and
  well formed, and each first id is above every id of P.
- **The reference** is today's `refGet` and `refScan` on one transaction
  that holds every user operation so far. No new reference is defined.

## 3.2 (a) The full invariant and the in-between invariant

```lean
def LiveCountsH (p : Params) (N : NodeId → Option KNode) (t : Time) (r : NodeId)
    (H : NodeId → Prop) : Prop :=
  ∀ x b s n, FReach N t r x b s → N x = some n → ¬ H x →
    (n.liveAt t = [] → b = true ∧ s = true ∧ n.leaf = true) ∧
    (n.leaf = false → b = true → 2 ≤ (n.liveAt t).length) ∧
    (p.merges = true → b = false → p.mergeBelow ≤ (n.liveAt t).length)

def Hole (p : Params) (P : Struct BVal) (t : Time) (D : List Key) (x : NodeId) : Prop :=
  ∃ k ∈ D, ∃ r cv, rootAt (viewOf P) t = some r ∧
    (x, cv) ∈ fromVisits (knodeOf p (viewOf P)) t p.fuel k r

def HoleW (c : Ctx) (base : View BVal) (w : W) (key : Key) (x : NodeId) : Prop :=
  ∃ cv, (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key w.top.rootKey

abbrev Full (p : Params) (P : Struct BVal) (t : Time) : Prop := RunTreeQ p (LatestQD p) P t

structure Sub (p : Params) (P : Struct BVal) (t : Time) (D : List Key) : Prop where
  links : RunLinksOK p P t
  tree : TreeAt p P t
  kinds : KindsAllOK p P
  heights : HeightAllOK p P t
  size : SizeOK p P
  left : LeftAllOK p P
  dead : DeadAllOK p P
  range : RangeAtOK p P t
  live : ∀ r, rootAt (viewOf P) t = some r →
    LiveCountsH p (knodeOf p (viewOf P)) t r (Hole p P t D)

def StInv (p : Params) (s : St) : Prop :=
  Sub p s.P s.t s.pend ∧ StructTimesLE s.P s.t ∧ HighKindsOK p s.P ∧ DataEntriesOK s.P ∧
    ViewEncoded (viewOf s.P) ∧ ReadsOK p s
```

- **I** is `Full`: today's run invariant, unchanged.
- **I_sub** is `Sub p P t D`, D the pending keys: every part of I but
  `InvOK`, which is replaced by the parts it is built from, with the
  fill (`LiveCounts`) asked only outside the holes. A hole is a node on
  the path of a pending key. An inner node still has the empty key's
  klong (`LeftAllOK`), so no inner node is empty: 026-17's Q6.
- **Against K5.** K5 filters the walk's fault texts by name and node;
  `Sub` states the same with the parts. That the two agree is by
  reading, not proved (section 9).
- **The path** is `fromVisits`, the reader's, not `Mt.pathAt`: the frame
  lemmas speak of it. That `Mt.path` visits the same nodes is part of
  steps A2 and E (question 4).

The targets:

```lean
def T_liveCountsH_none : Prop :=
  ∀ p N t r, LiveCountsH p N t r (fun _ => False) ↔ LiveCounts p N t r

def T_full_of_sub (p : Params) : Prop :=
  ∀ P t, StructTimesLE P t → Sub p P t [] → Full p P t

def T_sub_of_full (p : Params) : Prop :=
  ∀ P t, StructTimesLE P t → Full p P t → Sub p P t []
```

- **(a1)** A few lines, as `liveEdgesX_false_iff` (LiveStepsX.lean).
- **(a2)** With no pending key, I_sub is I: the last lines of
  `invOK_snocR`, with `invOK_of_parts`, `rootKeyOK_of_treeAt`,
  `keyNodesOK_of_parts`, `heightLiveOK_of_all`, `leftmostOK_of_leftAll`
  and `liveCounts_parts`, each unchanged. This is the lemma that makes
  the result mean something: at a tidy boundary the tree is today's.
- **(a3)** I gives I_sub: `LiveCounts` and the ranges from `InvOK`, as
  a transaction's first state gets them today: `walk_of_fReach` and
  `liveCounts_init` (LiveCounts.lean), `rangeOrder_init`
  (PutInvRange.lean). Those are stated for `treeRun` and the writer's
  time; restated for any P at the structure's time.

## 3.3 (b) The step lemma

At a reached state, the fixed form:

```lean
def FixStepOK (p : Params) (C : Fix → Prop) : Prop :=
  ∀ (s : St) (k : Key) (rest : List Key) (base : NodeId) (w : W) (f : Fix) (w1 : W),
    Reached p s → StInv p s → s.pend = k :: rest →
    (∀ q ∈ s.P, q.1 < base) →
    runFix p base k (s.t + 1) (view (treeSpec p) s.P s.t) = .ok (true, w) →
    fixOf p base k (s.t + 1) (view (treeSpec p) s.P s.t) = .ok (f, w1) → C f →
    StInv p ⟨commit s.P (s.t + 1) w, s.t + 1, k :: rest, s.ops⟩

def T_fixStep_merge (p : Params) : Prop :=
  MergeParamsOK p → (2 ≤ p.theta ∨ p.theta = 0) → FixStepOK p IsMerge
```

`IsMerge f` is `∃ x d, f = .merge x d`; `IsUnlink` and `IsCollapse`
alike. In words: one fix step of kind C for the first pending key takes
I_sub to I_sub with the same pending keys, and every get stays right.
The pending set does not grow; it shrinks only by (e). A measure that
falls with each fix step, the fixing's bound, is out of scope (section
7).

At the writer's state, the two working forms that the provers share:

```lean
def FixStart (c : Ctx) (base : View BVal) (w : W) : Prop :=
  w.made = [] ∧ w.taken = [] ∧
    ∀ y yn, wNode c.p base w y = some yn → ∀ s, Klong.time s ∈ yn.ks → s < c.i

def FixW (p : Params) (C : Fix → Prop) : Prop :=
  ∀ (key : Key) (c : Ctx) (base : View BVal) (w : W) (H : NodeId → Prop), c.p = p →
    ViewCoherent c base → FixStart c base w → PutInv c base w → PutInvG c base w →
    RangeOrder (wNode p base w) c.i w.top.rootKey →
    LiveCountsH p (wNode p base w) c.i w.top.rootKey H →
    (∀ f w1, (do path key; target : M Fix) c w = .ok (f, w1) → C f) →
    WriterWP (fixStep key) c w (fun r w' => r = true →
      PutInv c base w' ∧ PutInvG c base w' ∧
      RangeOrder (wNode p base w') c.i w'.top.rootKey ∧
      LiveCountsH p (wNode p base w') c.i w'.top.rootKey
        (fun y => H y ∨ HoleW c base w' key y) ∧
      ∀ k, wGet p c.i base w' k = wGet p c.i base w k)

def FrameW (p : Params) : Prop :=
  ∀ (key k' : Key) (c : Ctx) (base : View BVal) (w : W), c.p = p →
    ViewCoherent c base → FixStart c base w → PutInv c base w → PutInvG c base w →
    RangeOrder (wNode p base w) c.i w.top.rootKey →
    WriterWP (fixStep key) c w (fun _ w' => ∀ y, HoleW c base w k' y →
      TReach (wNode p base w') c.i w'.top.rootKey y → HoleW c base w' k' y)

def T_fixW_merge (p : Params) : Prop :=
  MergeParamsOK p → (2 ≤ p.theta ∨ p.theta = 0) → FixW p IsMerge
```

- **`FixW`**: from any set of holes H, a fix step leaves the fill
  broken only in H or on its own key's path in the new tree; it keeps
  `PutInv`, the ranges and every reading. H is a set of nodes here, so
  this form needs nothing about the other pending keys. This is MT's
  `l4`: the fill is kept but on one path, a local fact.
- **`FrameW`**: a node that stays in the tree stays on the path of every
  key that had it on its path. With it the holes of the other pending
  keys are still on their paths after the step, which K5's form needs.
- **`FixStepOK` from the two** and the lift (step B3):
  `FixW p C → FrameW p → FixStepOK p C`, for the kinds and heights and
  the other parts of `Sub` with their own lemmas of 2.3.

Why the merge's fill holds, in words, for the prover (my reasoning, not
checked in Lean):

- A merged node of one holds the live klongs of both. If the sibling is
  no hole it has m, so the node has m. If both were holes the node may
  be under m; it is on the key's new path.
- A merge into two happens above c live klongs, and c is at least
  2m - 1 (`MergeParamsOK`): each has m (`mergeKlongs_live_fill`).
- The parent loses a klong and may go under the fill or to one klong: it
  is on the key's path. If it is full it splits: a time split's node has
  the same live klongs and is on the path; a space split's halves have m
  each (`halves_live_fill`); a new root has two.
- No other node changes, and no flag of the walk changes.

## 3.4 (c) The user subtransaction

```lean
def UserStepOK (p : Params) : Prop :=
  ∀ (s : St) (tx : Tx) (noops : List Bool) (w : W), Reached p s → StInv p s → s.pend = [] →
    tx.sorted = true → tx.wf = true → (∀ q ∈ s.P, q.1 < tx.base) →
    runUser p tx.base tx.ops (s.t + 1) (view (treeSpec p) s.P s.t) = .ok (noops, w) →
    StInv p ⟨commit s.P (s.t + 1) w, s.t + 1, deletedKeys tx.ops noops, s.ops ++ tx.ops⟩

def DelW (p : Params) : Prop :=
  ∀ (key : Key) (c : Ctx) (base : View BVal) (w : W) (H : NodeId → Prop), c.p = p →
    keyWf key = true → ViewCoherent c base → PutInv c base w → PutInvG c base w →
    RangeOrder (wNode p base w) c.i w.top.rootKey →
    LiveCountsH p (wNode p base w) c.i w.top.rootKey H →
    WriterWP (putKv (.del key)) c w (fun _ w' =>
      PutInv c base w' ∧ PutInvG c base w' ∧
      RangeOrder (wNode p base w') c.i w'.top.rootKey ∧
      LiveCountsH p (wNode p base w') c.i w'.top.rootKey
        (fun y => H y ∨ HoleW c base w' key y) ∧
      ∀ k, keyWf k = true →
        wGet p c.i base w' k = if k == key then none else wGet p c.i base w k)
```

- **`UserStepOK`** is (c): from I at a visible time (`StInv` with no
  pending key, which is I by (a2)) the user subtransaction gives I_sub
  with its deleted keys pending, and the reference with its operations.
  In the trial it is a **named premise** of the top statement.
- **`DelW`**, R1's delete at the writer's state (`putKv` here is
  `Mt.putKv`), is its new part and is in tier 3. It reuses the bitmap's
  lemmas: `writerWP_appendDeleteKlong_room_exact` (TakeDeadDelete.lean),
  `writerWP_appendDeleteKlong_full_inv_any` (DelStepsFullGet.lean) and
  the noop's `writerWP_del_noop_seg` (GetFrame.lean).
- **The puts** are today's by the equation of 2.4, so the put's lemmas
  at the writer's state apply. But a put after a delete of the same
  subtransaction starts from a state with holes, and today's fill cases
  for puts (`liveCase_putLeafRoom`, `liveCase_putLeafFull`,
  `liveCase_putNewSegFull`, ...) assume `LiveCounts` without holes and
  are stated for `treeRun`. Restating them with holes is not in the
  trial.

## 3.5 (d) Gets and scans at visible times

```lean
def T_scans_of_full (p : Params) : Prop :=
  ∀ s, Reached p s → StInv p s → s.pend = [] → ScansOK p s
```

- **Scans**: from `StInv` at a visible time. (a2) gives `InvOK`;
  `scan_eq_contents` and `rootContents_sorted` (ScanLatest.lean) apply
  **unchanged**; the contents are the reference's from `ReadsOK`, by
  `rootContents_eq_refKvs` and `refKvs_keyWf` (ScanLatest.lean) and
  `treeRun_treeContents_keyWf` (RunEncoding.lean), **restated** for
  `Reached`.
- **Gets**: `ReadsOK` is a part of `StInv`, at every reached state. At
  `St.init` it is `get_init` (InvInit.lean). Each kind of step keeps
  it: the merge by `FixW`'s last line (`writerWP_merge_get_inv` through
  the bridge) and the lift of a get through `commit` (today's
  GetCommit.lean, 879 lines, stated for `treeRun`: restated).
- **The run's facts** that `scan_eq_contents` asks: `treeRun_highKindsOK`
  (NodeKinds.lean), `treeRun_dataEntriesOK` (DataEntries.lean),
  `treeRun_encoded_of_within` (RunEncoding.lean) and `treeRun_timesLE`
  (RunPrefix.lean), **restated** as parts of `StInv` kept by `commit`.
- **Earlier visible times** (a read at an old visible time on a later
  structure) follow as today from `scan_of_readExtension`
  (HistoricalScan.lean) and `readExtension_apply_past`
  (ReadExtension.lean). Not a target; a prover adds it only if it is a
  few lines.

## 3.6 (e) The driver's end for a key

```lean
def DoneOK (p : Params) : Prop :=
  ∀ (s : St) (k : Key) (rest : List Key) (base : NodeId) (w : W),
    Reached p s → StInv p s → s.pend = k :: rest →
    (∀ q ∈ s.P, q.1 < base) →
    runFix p base k (s.t + 1) (view (treeSpec p) s.P s.t) = .ok (false, w) →
    StInv p ⟨s.P, s.t, rest, s.ops⟩
```

In words: when the first pending key's path needs no fix, the key
leaves, and I_sub holds without it: its holes are closed. With (a2), I
holds when the last key leaves. The core is a fact about `Mt.targetGo`
alone: if it returns `Fix.none`, every node of the path meets the three
counts. My reasoning, not checked in Lean: a node under the fill is
merged or passed over as an only child; then the node above has one live
klong and is itself under the fill (m is 2 or more) or a root that
collapses; so the walk never ends in `none` after it met a fault. New
work; it needs that `Mt.path`'s nodes are `fromVisits`'s, that the
walk's root test is the flag b of `FReach` (by the kinds), and that
`KNode.cnt` is the number of klongs live at the step's time (as
`newKlongs_cnt_of_sorted`, MergeLiveFill.lean, has it for new nodes).

## 3.7 The trial's top statement

```lean
def T_reached_inv (p : Params) : Prop :=
  MergeParamsOK p → (2 ≤ p.theta ∨ p.theta = 0) →
  UserStepOK p → FixStepOK p IsMerge → FixStepOK p IsUnlink → FixStepOK p IsCollapse →
  DoneOK p → ∀ s, Reached p s → StInv p s

def VisibleOK (p : Params) : Prop :=
  ∀ s, Reached p s → s.pend = [] → Full p s.P s.t ∧ ReadsOK p s ∧ ScansOK p s

def T_visible (p : Params) : Prop :=
  MergeParamsOK p → (2 ≤ p.theta ∨ p.theta = 0) →
  UserStepOK p → FixStepOK p IsMerge → FixStepOK p IsUnlink → FixStepOK p IsCollapse →
  DoneOK p → VisibleOK p
```

- **`T_reached_inv`** is the induction over `Reached`: a few lines from
  the obligations, plus that a `runFix` that returned true has a
  `fixOf` of one of the three kinds.
- **`T_visible`** is the result to report. As each obligation is proved
  its premise leaves the corollary, as on 15 November. The planned end
  of the first two tiers: `VisibleOK p` from `hp`, `hth`, `UserStepOK`,
  `FixStepOK p IsUnlink` and `FixStepOK p IsCollapse`; that is
  **reduced** to the user subtransaction and the two other fixes. Each
  premise speaks of reached states with the invariant, and each is
  tested (section 9).

## 3.8 What each statement reuses, and what is restated

- **Unchanged, by name:** `scan_eq_contents`, `rootContents_sorted`;
  `invOK_of_parts`, `liveCounts_parts` and the other lemmas of (a2);
  the whole-merge lemmas of 2.3 through the bridge; the pieces of the
  fill; `fromVisits` and its frames; `refGet`, `refScan`; `PathOK` and
  `writerWP_descendLte_reads` (GetFrame.lean) for the path.
- **Restated for Mt's definitions:**
  - the bridge itself (A1): `Mt.merge` runs as `merge`; `Mt.putKv` of a
    put is `putKv`;
  - the path (A2): `Mt.path` gives `PathOK` and `fromVisits`; today's
    lemmas are about `descendToSegmentRoot` (for example
    `checkRoot_ok_of_segDesc`) and do not apply to `pathGo`;
  - the fill with holes (A3): `LiveEdgesX`'s steps for holes below
    inner nodes;
  - the run's layer (B1, B3): the lift and the step of each part of the
    invariant, for `commit` in place of `treeRun`;
  - the run's facts and the contents (B2).
- **New:** the empty leaf's merge (R3), `FrameW`, `DoneOK`, the
  induction.


# 4. What "evidence" means

Seven measures. The trial's report gives each in a line or two; the
numbers come from `wc -l`, `grep` and the log's times, by a script
`counts.sh` kept in the evidence directory.

- **E1, what MT adds.** Lines and prover-hours of each step of section
  6, from the files' sizes and the times of the GATED messages. Beside
  it 006-28's guess for "Left" (section 7.5: "I cannot size it without a
  try").
- **E2, the fill.** Lines and hours of `T_fixW_merge`'s part about
  `LiveCountsH` (step A3), and whether it is proved. Against it: `l4`,
  today's same fact inside one delete, not proved, 3,000 lines or more
  (006-27, section 8); and the fill's proved files today, 21 files,
  5,515 lines. This is the number that turns 006-28's "well under the
  3,000 lines" into a measure.
- **E3, the reuse.** For each family of 2.3 (tree, ranges, reading,
  `PutInv`, kinds, heights, dead klongs, leftmost, books): did today's
  lemma apply to `Mt.merge` through the bridge with no change (yes, no,
  not tried), and the bridge's lines. A prover marks a declaration that
  copies one of main's with changes by the comment `-- restated from
  NAME`; E3 counts them and their lines.
- **E4, the readers.** For each lemma of 3.5: used unchanged, or
  restated (lines).
- **E5, the premises.** The premises of the best gated `t_visible`, by
  name; for each, how it is tested. And: is any of them of `l4`'s or
  `htbL`'s kind, a fact that is not local to one step? The answer is
  yes or no with the name.
- **E6, the take-back.** The trial's declarations whose statement names
  a book of the take-back (`taken`, `madeFor`, `TakeJ2`, `J2At`,
  `retarget`, `toPrev`): a count by grep, with the names. If 025-02's
  `Reach.lean` (/Users/f/fl/bench/2026-11-14/cleanup/tools/) runs with
  the trial's theorems as roots: the lines of main's take-back files
  (2.3's second and third counts) that `t_fixW_merge`'s proof reaches.
  If it does not run as it is, the report says so and gives the grep
  only.
- **E7, what went wrong.** Statements found false, with the
  counterexample; steps stopped by size; working statements changed.

**How to read them** (my rule, question 6):

- **The gain is supported** if `T_fixW_merge` is proved with no premise
  of `l4`'s or `htbL`'s kind, its fill part in under 3,000 lines, and
  `scan_eq_contents` applied unchanged.
- **Not supported** if step A3 stops by size, or by a false statement
  with no local repair.
- **Open** otherwise; the report says what is missing.

**What the measures cannot say:** how many of today's lines MT lets go
(026-17's C4 stays the estimate, E6 its only check); the user
subtransaction's cost; anything of Java.


# 5. Where the work happens

- **Nothing reaches main** but this entry's text and the evidence
  directory `items/026-release-2026-6/19-proof-trial/`. No file of
  main's `lean/` or `java/` changes.
- **The directory:** /Users/f/fl/bench/2026-11-16/pt/, with `a/clone`
  and `b/clone` for the two provers, the gate, the STOP file and the
  gates' logs.
- **The clones** (step P0a, the coordinator, shell only): each a clone
  of /Users/f/fl/repos/bergdb at main, with a new branch
  (`026-19-proof-trial-a`, `-b`) and the four files of the trial's
  branch taken as they are:
  `git checkout 026-17-mt-trial -- lean/SIS/Tree/Mt.lean lean/MtTest.lean
  lean/MtDeps.lean lean/lakefile.toml`, committed. Check:
  `git diff 026-17-mt-trial -- lean` is empty. (A merge of the branch
  gives the same `lean/`; it may conflict in `items/`.)
- **The build:** `.lake` copied from a tree whose `lean/` is main's and
  that is built in full, for example
  /Users/f/fl/bench/2026-11-15/day/htb/clone (474 modules of
  `SIS/Tree` built; `git diff 1de529c4 main -- lean` is empty), then
  `lake build` and `lake build SIS.Tree.Mt` under one heavy slot
  (`slot.sh`). The clone of 026-17 has only 258 of the 474 modules
  built and main's own tree 127: neither will do.
- **The files the trial adds**, all in `lean/SIS/Tree/`: MtRun.lean,
  MtSub.lean (P0b); MtBridge.lean, MtPath.lean, MtMergeLive.lean,
  MtMergeEmpty.lean, MtMerge.lean (prover A); MtLift.lean,
  MtReaders.lean, MtStep.lean, MtTop.lean (prover B); MtFrame.lean,
  MtDone.lean; in tier 3 MtUnlink.lean, MtCollapse.lean, MtUserDel.lean.
  MtTop.lean imports them all. `SIS.lean` is not changed, so main's
  default targets build as on main.
- **The result branch** `026-19-proof-trial`: the coordinator merges the
  two provers' branches at the end, runs the gate on the merge, and
  fetches the branch into the main repo. It is kept, not merged, as
  `026-17-mt-trial` is.
- **The gate**, `gate-1116.sh` (P0b writes it from
  /Users/f/fl/bench/2026-11-15/day/gate-1115.sh and tests it on a file
  with a `sorry`, which must fail). Run by a prover after each step's
  commit; it ends in `GATE PASS` or `GATE FAIL: why`. It checks:
  - `lake build` (main's default targets) and `lake build
    SIS.Tree.MtTop`, each exit 0, under one heavy slot;
  - no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`,
    `implemented_by`, `extern` in `lean/`;
  - main's `lean/` and Mt.lean unchanged:
    `git diff --name-status main -- lean` lists only added files
    (`A`) named `lean/SIS/Tree/Mt*.lean`, `lean/MtTest.lean`,
    `lean/MtDeps.lean`, and `M lean/lakefile.toml`; and
    `git diff 026-17-mt-trial -- lean/SIS/Tree/Mt.lean lean/MtTest.lean
    lean/MtDeps.lean lean/lakefile.toml` is empty. With this the trusted
    closure and main's top theorems are the same bytes; the gate of 15
    November's guard for them is not needed;
  - the standard axioms: a file `Audit1116.lean` with `#print axioms`
    for each `t_...` theorem; only `propext`, `Classical.choice` and
    `Quot.sound` may show;
  - the fixed statements: `git diff P0B -- lean/SIS/Tree/MtRun.lean
    lean/SIS/Tree/MtSub.lean` (P0B the setup's commit) is printed into
    the summary; the coordinator reads it against the GATED message.
- **The provers' brief** is /Users/f/fl/bench/2026-11-15/day/common.md
  with these changes, written by the coordinator: read this entry
  (sections 2, 3, 5 and 6) and 026-17's section 3 first; add files
  named `Mt*.lean` only; the gate is `gate-1116.sh`; nothing lands on
  main; a GATED message names the target (`T_...`), the premises left
  and every changed working statement; the stop rules are section
  6.3's; commits are "026-19: ..." in Frans Lundberg's name.


# 6. The steps

## 6.1 The steps in order

Sizes are lines of Lean and prover-hours. On 15 November a prover on a
planned route with many copies wrote about 2,750 lines in 54 minutes
(fit, 025-05's part 1); new arguments go slower. I plan with 400 to 800
lines an hour. Every prover is Opus 5.5 at xhigh (Frans, 13 November:
"when tokens are the limit all agents Opus xhigh").

**Tier 1 and 2, the night's aim.**

- **P0a, the setup.** The coordinator, by shell, before the start: the
  directory, the two clones, the build (section 5). Check: `lake build`
  and `lake build SIS.Tree.Mt` exit 0 in both; the two `git diff`
  checks. No model usage. If the copied `.lake` is not accepted, a full
  build runs first; its time is not known (section 11).
- **P0b, the statements and the gate.** Prover B first; 300 lines, 0.5
  hours. MtRun.lean and MtSub.lean from the two drafts, checked against
  the real definitions (the drafts' stand-ins go); `gate-1116.sh` and
  its self-test; `Audit1116.lean`. Check: the gate passes on the two
  files; every statement changed from the draft is in the GATED
  message. Prover A starts A1 at the same time and pulls P0b's commit
  when it is gated.
- **A1, the bridge.** Prover A; 300 to 700 lines, 0.75 hours.
  MtBridge.lean: a successful run of `Mt.merge x d` from a state where
  the two nodes have a live klong and no klong of the step's time is a
  run of `merge x d` to the same state but `madeFor` and `trail`;
  `Mt.putKv (.put key h) = putKv (.put key h)`; a state after `path key`
  from a `FixStart` state is again `FixStart`. Check: the gate.
- **A2, the path and the target.** Prover A; 400 to 900 lines, 1 hour.
  MtPath.lean: after `path key` the writer's path is `PathOK` down to
  its last node, its nodes are `fromVisits`'s, and the state reads as
  before; if `target` returns `merge x d` then x is the path's node at
  depth d, d is above 0, the node above is inner with two live klongs
  or more, and x has fewer than m. Check: the gate.
- **A3, a merge keeps the fill with holes.** Prover A; 600 to 1,500
  lines, 2 hours. MtMergeLive.lean: `FixW`'s line about `LiveCountsH`
  for a merge of two nodes with a live klong, by 3.3's argument. This
  is E2. Before the proof, a test on runs (rule 5 of the brief): after
  each merge step of 026-17's small guards (`Mt.Small`), the walk's
  fill faults lie on the step's key's path, by a scratch program.
  Check: the gate; the GATED message gives the lines and the time.
- **A4, the other parts through the bridge.** Prover A; 300 to 900
  lines, 1 hour. MtMerge.lean: `PutInv`, `PutInvG`, the ranges and the
  reading after `Mt.merge`, from 2.3's lemmas; then `t_fixW_merge` for
  nodes with a live klong. The kinds, heights, dead klongs and leftmost
  klong likewise, each if it is an application. This is E3. Check: the
  gate.
- **A5, the empty leaf (R3).** Prover A; 300 to 1,200 lines, 1.5
  hours. MtMergeEmpty.lean: `FixW` for a merge where a leaf is empty,
  where the bridge does not apply. If it stops by size, `t_fixW_merge`
  keeps the premise "no merged node is empty", and the report says so.
- **B1, the lift.** Prover B; 500 to 1,200 lines, 1.5 hours.
  MtLift.lean: for `commit P i w` after `runWith`, the structure reads
  as the writer's nodes (`commitLiftAt_of_links`'s content for any P
  with `RunLinksOK`), a get through it is the writer's, and the run's
  facts (`StructTimesLE`, `HighKindsOK`, `DataEntriesOK`,
  `ViewEncoded`) are kept. Check: the gate.
- **B2, the readers.** Prover B; 200 to 500 lines, 0.75 hours.
  MtReaders.lean: `t_scans_of_full`. This is E4. Check: the gate.
- **B3, the step at the structure.** Prover B; 500 to 1,500 lines, 2
  hours. MtStep.lean: `FixW p C → FrameW p → FixStepOK p C`, with (a1)
  to (a3). B works against `FixW` and `FrameW` as hypotheses, so it
  does not wait for A. A part of `Sub` whose step does not come in time
  is a named premise of this theorem, said in the GATED message. Check:
  the gate.
- **B4, the induction and the top.** Prover B; 150 to 400 lines, 0.5
  hours. MtTop.lean: `t_reached_inv`, `t_visible`. Check: the gate, and
  the coordinator reads `t_visible`'s statement against 3.7.
- **C1, the frame.** The prover who is free first; 400 to 1,200 lines,
  1.5 hours. MtFrame.lean: `FrameW` for the merge. If it stops by size
  it stays a premise of `t_fixStep_merge`, the first candidate for
  "what is left".
- **E, the driver's end.** The prover who is free; 300 to 800 lines, 1
  hour. MtDone.lean: `DoneOK`. Before the proof, a test: `DoneOK`'s
  moment is not one of K5's boundaries (section 9).

**Tier 3, if time allows, in this order:** unlink (MtUnlink.lean,
`FixW p IsUnlink`, 300 to 900 lines, 1 hour); collapse (MtCollapse.lean,
300 to 900, 1 hour); the user's delete (MtUserDel.lean, `DelW`, 500 to
1,200, 1.5 hours).

Sums: tiers 1 and 2 are 4,200 to 11,000 lines and about 14 prover-hours
(A 6.25, B 5.25, C1 and E 2.5); tier 3 adds 3.5 hours.

## 6.2 What runs at the same time

- Two provers at most: A on the writer's state, B on the run. They
  share only MtRun.lean and MtSub.lean (B's, P0b); after P0b a change of
  a working statement goes by a message to the other prover and the
  coordinator, and the other pulls the commit.
- Builds are single modules while a prover works (`lake build
  SIS.Tree.MtX`, `lake env lean F`); a gate takes the one heavy slot.
- The coordinator runs in unattended mode (013-02) with check-ins, as
  on 006-09's night: it starts the provers, reads each GATED message
  against section 3, logs it here, restarts a prover that a session
  limit stopped, and merges at the end.

## 6.3 The stop rules

Each is checked by the prover before each build and every 20 minutes,
with `date`, and by the coordinator at each check-in.

- **A step much larger than planned:** at twice the upper line count or
  twice the hours of 6.1, the prover stops the step, commits what
  builds, writes in his next message what blocks (the goal that does
  not close, in Lean), and goes to the next step that does not need it.
  The unproved statement becomes a named premise.
- **A fixed statement found false:** the prover stops the step and
  writes the counterexample as a Lean file that computes it on a run
  (kept in the evidence directory), and the strongest true form he
  sees. He does not change the fixed statement. He messages the
  coordinator at once and goes on only with steps that do not use it.
- **A working statement found false:** no stop. He restates it with the
  book it needs (section 3's second rule) and says so.
- **The clock:** no new step after 04:30; the provers stop at 05:30 and
  write their final messages; all ends at 06:00 on Tuesday 17 November.
- **Usage:** the provers stop when the new week reaches 9 %; the
  write-up may take it to 10 % (question 2). The coordinator reads the
  usage at each check-in.
- **The STOP file:** /Users/f/fl/bench/2026-11-16/pt/STOP. When it is
  there: no new build, the slot released, a commit on the branch, the
  final message.
- **At any stop** the final message is as rule 7 of 15 November's
  brief: about 20 lines; proved, reduced to what, refuted, open; the
  targets with their premises.

When the trial ends, the coordinator (or one Opus agent at xhigh) writes
this entry's "Result" section, first in the file, with E1 to E7, and
fills the evidence directory: the trial's Lean files as text, the gates'
summaries, `counts.sh` and its output, the provers' final messages.


# 7. Out of scope, and what follows

**Out of scope.**

- Java: no line of `java/` is read or changed; the trial says nothing of
  a commit's time or the bytes.
- The stream format: how a group's end shows in the stream, and what a
  start does with a group that did not end (026-18, section 4).
- Restarts and P2: every statement is about runs with no crash.
- Reclaim and eviction over the in-between states, and reclaim's
  argument from TP27.
- The abstract model's bridges: `RunOK` (TP14) for MT's transactions,
  and with it T1, T2 and T13.
- The fixing's bound (026-17's S3): that the driver ends. `Reached`
  takes a `done` step when `runFix` returns false; nothing says it
  comes.
- That `Mt.fixAll` follows `SubStep`'s order (by reading).
- The user subtransaction's puts with holes (3.4); the merges off;
  `NoBug` (TP8) for MT's errors, the `MT:` ones too; a scan at an
  untidy boundary (A1); NW.

**What follows.**

- Frans decides MT, NW or neither, with 026-17's result and this
  trial's measures.
- If MT: 026-18's design note (visible times, the group in the stream,
  the names), then the premises left here, in this order: the user
  subtransaction, unlink and collapse if not done, the fixing's bound;
  then the cut of the take-back's branches from the lemmas the bridge
  uses, which is where lines would go.
- If not: the branch stays as a record; `l4` and `htbL` go on by their
  plans (024-12, section 1; 025-05, section 8).


# 8. The cost and the start

- **Prover-hours:** about 14 for tiers 1 and 2, at most 16 in the night
  (two provers, 22:05 to 06:00).
- **Usage:** about 10 % of the week. On 15 November the week went from
  82 % to 90 % between 08:54 and 14:40 with at most two provers at a
  time, five in all, and two planning agents (006-27, section 8): about
  0.7 points a prover-hour if two provers ran all that time, more if
  they did not. One day's figure; the 9 % stop rule holds whatever the
  rate turns out to be.
- **The start:** the week resets on Monday 2026-11-16 at 22:00. On
  Frans's go the coordinator makes the setup (P0a) before 22:00 and
  starts the two provers at 22:05, unattended. Without his go nothing
  starts.
- **The end:** 06:00 on Tuesday; the result section the same morning.


# 9. The risks

**A statement false as stated.** On 15 November three premises were
false because they spoke of any state, not of the states that runs
reach. What the plan does against it:

- **The fixed targets speak only of reached states with the
  invariant.** `FixStepOK`, `UserStepOK` and `DoneOK` each take
  `Reached p s` and `StInv p s`. A prover may use any fact he proves of
  reached states, and may add a book to `StInv`.
- **The working statements do speak of any state** of the writer
  (`FixW`, `FrameW`, `DelW`), as today's lemmas do. That is where the
  trap is. So they are the prover's to restate (6.3), and A3 tests its
  statement on runs first.
- **Each fixed target is tested on MT's runs**, 32,017 boundaries at
  node size 30 and 298,235 at 8 (026-17), with two gaps:
  - `FixStepOK` and `UserStepOK` are K5 at each boundary, with the
    pending keys from the step's key on; `ReadsOK` is K1; `Full` at a
    visible time is K4.
  - Gap 1: `Sub` is K5 in other words (parts, not fault texts;
    `fromVisits`, not `Mt.pathAt`). That they agree is by reading.
  - Gap 2: `DoneOK` speaks of the moment a key leaves. K5 was run after
    each fix step, with the step's key still pending, and K4 at the
    group's end; the moment between is not a boundary of the test. Step
    E tests it first.
  - MT's test gave the writer its own table as the view; the statements
    give it `view (treeSpec p) P t`, as `Within` does. I expect no
    difference at the last time; not checked.

**The parts most likely to grow.**

- **The run's layer (B1, B3).** Today's lift and the steps of the
  invariant's parts are stated for `treeRun`; I read their statements,
  not their proofs. If the proofs lean on `treeRun` deeply, B3 is
  copies of several files (LatestJoint, LatestTop, TakeBackRun,
  DeadRun, OverlayLift, KeyHistRun, RunEncoding, NodeKinds, DataEntries,
  GetCommit: about 2,600 lines together). This is the number 006-28
  could not give; a large B3 is a finding, not a failure.
- **The fuel.** `writerWP_merge_get_inv` keeps the reading "when the
  state after fits the fuel". Today the fit comes from the heights'
  walk (29 files, 11,357 lines). In the trial the fit at a fix step's
  end should come from `HeightAllOK` after the step; if it does not in
  time, it is a named premise.
- **The bridge (A1).** If today's whole-merge lemmas ask for a book of
  the take-back that a fix step's first state does not give by itself,
  A4 grows.
- **The empty leaf (A5)**: no lemma of today's covers it.
- **The frame (C1)**: new, over every kind of split of the parent.
- **Small conversions** that add up: `KNode.cnt` against `liveAt`; the
  writer's time t + 1 against the structure's time t; `Mt.path` against
  `fromVisits`.

**Other risks.**

- **The two provers drift apart** on `FixW`. The plan fixes its text
  first (P0b) and makes every change a message.
- **The evidence reads weaker than hoped.** A proved merge step shows
  that MT's fill is local and what the new layer costs. It does not
  shrink today's proofs by itself (section 1's limit).
- **Usage and the clock**: the stop rules; the tiers say what goes
  first.


# 10. Questions for Frans

Each has a default; the work does not wait.

1. **The go.** Start at 22:05 tonight, unattended? Default: the
   coordinator asks once in the evening; without a go nothing starts.
2. **The usage.** A stop at 9 % of the new week for the provers, 10 %
   with the write-up? Default: yes.
3. **One night.** End at 06:00, and no second night without a new go?
   Default: yes.
4. **The path in I_sub.** The reader's `fromVisits`, with a lemma that
   `Mt.path` visits the same nodes, or `Mt.pathAt` itself as in K5?
   Default: `fromVisits`; today's frame lemmas speak of it.
5. **The bridge.** Prove MT's merge through today's `merge` lemmas
   (fast; the take-back's branches stay under it), or anew without them
   (the true size without the take-back, several times the work)?
   Default: the bridge, with E6 to show what stays under it.
6. **The reading of the result.** Section 4's rule for "supported",
   "not supported" and "open"? Default: as written.
7. **The order when time is short.** The fill first (A3), then the run
   (B), then the frame and the driver's end? Default: yes; the fill is
   where today's proof is open.
8. **The branch.** Kept in the main repo as `026-19-proof-trial`, not
   pushed? Default: yes, as `026-17-mt-trial`; a push is Frans's.


# 11. What I could not check

- **MtSub.lean's statements against the real definitions.** The clone
  of 026-17 has not built the modules of `FReach`, `LiveCounts`,
  `RangeOrder`, `PutInv`, `PutInvG`, `RunLinksOK`, `KindsAllOK`,
  `HeightAllOK`, `LeftAllOK`, `DeadAllOK`, `RangeAtOK`, `RunTreeQ` and
  `LatestQD`. I checked the draft with stand-ins of the same signatures
  (`19-proof-trial/standins.lean.txt`; `FReach` and `LiveCounts` are
  copies), by `lake env lean` from that clone. MtRun.lean's draft is
  checked as it is. P0b checks the rest.
- **That any target is true.** Nothing is proved. The reasoning of 3.3
  and 3.6 is mine, by reading; the tests are 026-17's, with section 9's
  gaps.
- **2.4's comparison** of `Mt.merge` with `merge`, and the put's
  equation: by reading the two texts.
- **That today's lemmas' hypotheses hold at a fix step's start**
  (`PutInvG`, `PathOK` from `Mt.path`, the kinds' and heights' books): I
  read the statements of `writerWP_merge_tree_inv2`,
  `writerWP_merge_range_inv` and `writerWP_merge_get_inv`, and the
  first lines only of `kd_merge`, `ht_merge`, `dw_merge`.
- **The build:** how long a full `lake build` takes in a new clone, and
  whether a copied `.lake` is accepted as built. 15 November's gates
  show only builds from a warm cache (0.3 to 14 seconds).
- **`Reach.lean` for E6**: not read.
- **The hours:** from one day's rates.
- **What I read in part:** 024-12, section 1 (its first 200 lines);
  006-28, sections 3.2, 3.3 and 7.5; 025-05's layout only; 006-27,
  sections 3, 7 (parts) and 8.

**The files in `19-proof-trial/`:** MtRun.lean.txt (3.1's text, checked);
MtSub.lean.txt (3.2 to 3.7's text); standins.lean.txt (the stand-ins of
the check). The scratch files of the check are in
/Users/f/fl/bench/2026-11-16/ptplan/.


# Log

2026-11-16. Registered by coord-1116 at 13:48 (Frans: "Plane the short
proof trial (3). Use a Fable High agent."). The plan written by an agent
of coord-1116 (Fable, high), 13:49 to 14:15: the statements, the
measures, the steps, the stop rules, the questions; the drafts of
MtRun.lean and MtSub.lean in `19-proof-trial/`, type-checked by
`lake env lean` from the clone of 026-17 (MtSub against stand-ins).
Nothing proved, nothing built; the trial not started. Status: open (the
plan written; the trial not started).
