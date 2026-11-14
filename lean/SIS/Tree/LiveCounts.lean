/-
TP7's conditions on live klongs, `NonEmptyOK`, `RootsOK` and `FillOK`, as an
invariant of the writer's tree (bergdb 024-12, TP7, `InvAssembly.lean`'s parts).

`LiveCounts` says, of every node reached from the space root through live
klongs, with the walk's flags (`FReach`: the root of its segment tree, of the
first segment's):

* a node has a live klong, unless it is the space root and a segment leaf;
* an inner segment root has two live klongs;
* with the merges on, a node an inner node names has m live klongs.

At a transaction's first state `LiveCounts` follows from TP7's invariant at
the time before (`liveCounts_init`). Every operation keeps it, as the
obligation `QLive` of the operation cases (`OpCaseOK`, as TP10's three
posts). Then `live_reached` gives it at every state between the operations.
At the transaction's end, the commit's lift turns it into `NonEmptyOK`,
`RootsOK` and `FillOK` of the structure after the run (`liveCounts_commit`).
In the same way `joint_reached`'s `RangeOrder` becomes `RangeAtOK`
(`rangeAtOK_commit`).

TP7 is assembled by induction on the runs (LatestJoint.lean, LatestTop.lean),
from:

* TP4 and the bound on dead klongs;
* cost's live heights and P's tree;
* the operation cases (1) to (4), with the merges on: TP10's three posts and
  `QLive`.
-/
import SIS.Tree.InvAssembly
import SIS.Tree.GetOpAssembly
import SIS.Tree.TakeBackRun

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## Reach with the walk's flags -/

/-- The nodes reached from r at t through live klongs, each with the walk's
flags: the root of its segment tree (a node a segment leaf names, or r), and of
the first segment's (no segment leaf on the way). -/
inductive FReach (N : NodeId → Option KNode) (t : Time) (r : NodeId) : NodeId → Bool → Bool → Prop
  | root : FReach N t r r true true
  | inner (x : NodeId) (b s : Bool) (n : KNode) (c : Nat) (y : NodeId) :
      FReach N t r x b s → N x = some n → n.leaf = false → (c, y) ∈ n.liveAt t →
      FReach N t r y false s
  | seg (x : NodeId) (b s : Bool) (n : KNode) (c : Nat) (y : NodeId) :
      FReach N t r x b s → N x = some n → n.leaf = true → (c, y) ∈ n.liveAt t →
      FReach N t r y true false

/-- The conditions of TP7 on live klongs, of the tree reached from r at t: a
live klong, but in the space root as a segment leaf; two in an inner segment
root; with the merges on, m in a node an inner node names. -/
def LiveCounts (p : Params) (N : NodeId → Option KNode) (t : Time) (r : NodeId) : Prop :=
  ∀ x b s n, FReach N t r x b s → N x = some n →
    (n.liveAt t = [] → b = true ∧ s = true ∧ n.leaf = true) ∧
    (n.leaf = false → b = true → 2 ≤ (n.liveAt t).length) ∧
    (p.merges = true → b = false → p.mergeBelow ≤ (n.liveAt t).length)

theorem fReach_space_root {N : NodeId → Option KNode} {t : Time} {r x : NodeId}
    (h : FReach N t r x true true) : x = r := by
  cases h
  rfl

/-- The walk's nodes with their flags are reached with them. -/
theorem nodesRoots_fReach (p : Params) (v : View BVal) (t : Time) (r : NodeId) :
    ∀ f y b s, FReach (knodeOf p v) t r y b s → ∀ q ∈ nodesRoots p v t f y b,
      ∃ s', FReach (knodeOf p v) t r q.1 q.2 s' := by
  intro f
  induction f with
  | zero => intro y b s _ q hq; simp [nodesRoots] at hq
  | succ f ih =>
    intro y b s hy q hq
    cases hn : knodeOf p v y with
    | none => simp [nodesRoots, hn] at hq
    | some n =>
      simp only [nodesRoots, hn, List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact ⟨s, hy⟩
      · obtain ⟨⟨c, z⟩, hcz, hq⟩ := List.mem_flatMap.mp hq
        cases hl : n.leaf with
        | true =>
          simp only [hl, ↓reduceIte] at hq
          split at hq
          · simp at hq
          · exact ih z true false (FReach.seg y b s n c z hy hn hl hcz) q hq
        | false =>
          simp only [hl, Bool.false_eq_true, ↓reduceIte] at hq
          exact ih z false s (FReach.inner y b s n c z hy hn hl hcz) q hq

/-- `LiveCounts` of P's key nodes from its space root gives `NonEmptyOK`,
`RootsOK` and `FillOK`. -/
theorem liveCounts_parts (p : Params) (P : Struct BVal) (t : Time) (r : NodeId)
    (hr : rootAt (viewOf P) t = some r) (hL : LiveCounts p (knodeOf p (viewOf P)) t r) :
    NonEmptyOK p P t ∧ RootsOK p P t ∧ FillOK p P t := by
  have hroots : nodesRootsAt p P t = nodesRoots p (viewOf P) t p.fuel r true := by
    unfold nodesRootsAt; rw [hr]
  have hnodes : keyNodesAt p P t = (nodesRoots p (viewOf P) t p.fuel r true).map Prod.fst := by
    unfold keyNodesAt; rw [hr, nodesRoots_map_fst]
  have hmem : ∀ q ∈ nodesRootsAt p P t, ∃ s, FReach (knodeOf p (viewOf P)) t r q.1 q.2 s := by
    intro q hq
    rw [hroots] at hq
    exact nodesRoots_fReach p (viewOf P) t r p.fuel r true true FReach.root q hq
  refine ⟨?_, ?_, ?_⟩
  · intro x hx n hn hne hE
    rw [hnodes, ← hroots] at hx
    obtain ⟨q, hq, hqx⟩ := List.mem_map.mp hx
    subst hqx
    obtain ⟨s, hs⟩ := hmem q hq
    rw [keyNodeAt_eq_knodeOf] at hn
    obtain ⟨hb, hs', _⟩ := (hL _ _ _ n hs hn).1 hE
    rw [hb, hs'] at hs
    exact hne (by rw [hr, fReach_space_root hs])
  · intro q hq hq2 n hn hl
    obtain ⟨s, hs⟩ := hmem q hq
    rw [keyNodeAt_eq_knodeOf] at hn
    exact (hL _ _ _ n hs hn).2.1 hl hq2
  · intro hm q hq hq2 n hn
    obtain ⟨s, hs⟩ := hmem q hq
    rw [keyNodeAt_eq_knodeOf] at hn
    exact (hL _ _ _ n hs hn).2.2 hm hq2

/-! ## The transaction's first state -/

/-- Every node reached with its flags from P's space root at t + 1 (P without
entries after t) has a walk without faults with those flags. -/
theorem walk_of_fReach (p : Params) (P : Struct BVal) (t : Time) (hP : StructTimesLE P t)
    (r : NodeId) (hr : rootAt (viewOf P) t = some r) (hI : InvOK p P t) :
    ∀ x b s, FReach (knodeOf p (viewOf P)) (t + 1) r x b s →
      ∀ m, knodeOf p (viewOf P) x = some m →
        ∃ f lo hi, walk p (viewOf P) t (f + 1) x lo hi b s = [] := by
  intro x b s hx
  induction hx with
  | root =>
    intro m _
    unfold InvOK faultsAt at hI
    rw [hr] at hI
    simp only at hI
    have hf : p.fuel = (p.G + 1) * (p.H + 2) + 1 + 1 := by unfold Params.fuel; omega
    rw [hf] at hI
    exact ⟨_, 0, none, hI⟩
  | inner x b s n c y _ hn hl hc ih =>
    intro m hm
    obtain ⟨f, lo, hi, hw⟩ := ih n hn
    rw [liveAt_succ_of_timesLE p P t hP x n hn] at hc
    obtain ⟨b', hb'⟩ := childBounds_exists (n.liveAt t) hi (c, y) hc
    have h := walk_child p P t f x lo hi b s n hn hw (c, y) b' hb' m hm
    simp only [hl, Bool.false_eq_true, ↓reduceIte] at h
    obtain ⟨f', hf'⟩ := walk_succ_of_nil p _ t f _ _ _ _ _ h
    subst hf'
    exact ⟨f', _, _, h⟩
  | seg x b s n c y _ hn hl hc ih =>
    intro m hm
    obtain ⟨f, lo, hi, hw⟩ := ih n hn
    rw [liveAt_succ_of_timesLE p P t hP x n hn] at hc
    obtain ⟨b', hb'⟩ := childBounds_exists (n.liveAt t) hi (c, y) hc
    have h := walk_child p P t f x lo hi b s n hn hw (c, y) b' hb' m hm
    simp only [hl, ↓reduceIte] at h
    obtain ⟨f', hf'⟩ := walk_succ_of_nil p _ t f _ _ _ _ _ h
    subst hf'
    exact ⟨f', _, _, h⟩

/-- `LiveCounts` at a transaction's first state, from TP7's invariant at the
time before. -/
theorem liveCounts_init (p : Params) (ts : List Tx) (tx : Tx) (hI : InvOK p (treeRun p ts) ts.length)
    (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top) :
    LiveCounts p (wNode p (viewOf (treeRun p ts)) (wInit tx top)) (ts.length + 1)
      (wInit tx top).top.rootKey := by
  have hlook : wNode p (viewOf (treeRun p ts)) (wInit tx top) = knodeOf p (viewOf (treeRun p ts)) := by
    funext x
    simp [wNode, wInit]
  have hroot := rootAt_of_writerTop p ts z top hz htop
  have hP := treeRun_timesLE p ts
  rw [hlook]
  intro x b s n hx hn
  obtain ⟨f, lo, hi, hw⟩ := walk_of_fReach p (treeRun p ts) ts.length hP top.rootKey hroot hI
    x b s hx n hn
  obtain ⟨nd, hg, hd, _, hnd⟩ := knodeOf_viewOf p _ x n hn
  obtain ⟨_, ⟨t1, _, t3, t4, _⟩, _⟩ :=
    (walk_succ_eq_nil_iff p _ ts.length f x lo hi b s nd hg hd).mp hw
  rw [liveAt_succ_of_timesLE p _ ts.length hP x n hn]
  have hnk : n = nodeK p nd := hnd
  subst hnk
  generalize (nodeK p nd).liveAt ts.length = lv at t1 t3 t4 ⊢
  generalize (nodeK p nd).leaf = lf at t1 t3 t4 ⊢
  refine ⟨fun hE => ?_, fun hl hb => ?_, fun hm hb => ?_⟩
  · subst hE
    cases b <;> cases s <;> cases lf <;> simp_all
  · subst hl hb
    simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not] at t3
    omega
  · subst hb
    simp only [hm, Bool.not_false, Bool.true_and, decide_eq_false_iff_not] at t4
    omega

/-! ## Along the transaction -/

/-- `LiveCounts` kept by an operation, the writer's tree after it given. -/
def QLive (p : Params) : List Tx → Op → W → W → Prop :=
  fun ts _ w w' => WriterTreeOK p (treeRun p ts) (ts.length + 1) w' →
    LiveCounts p (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey →
    LiveCounts p (wNode p (viewOf (treeRun p ts)) w') (ts.length + 1) w'.top.rootKey

/-- `LiveCounts` at every state that a prefix of a transaction's operations
reaches: from its first state (`liveCounts_init`) and `QLive` at every
operation, with `PutInv` and the walk's ranges there from `joint_reached`. -/
theorem live_reached (p : Params) (R : Struct BVal → Time → Prop)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hT : OpCaseOK p R (QTree p) AnyOp) (hP : OpCaseOK p R (QPutInv p) AnyOp)
    (hO : OpCaseOK p R (QRange p) AnyOp) (hLv : OpCaseOK p R (QLive p) AnyOp)
    (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx])) (hr : R (treeRun p ts) ts.length)
    (hTA : TreeAt p (treeRun p ts) ts.length) (hI : InvOK p (treeRun p ts) ts.length)
    (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top) :
    ∀ pre post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      LiveCounts p (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey := by
  intro pre
  suffices hk : ∀ k, ∀ pre : List Op, pre.length = k → ∀ post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      LiveCounts p (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey
    from hk pre.length pre rfl
  intro k
  induction k with
  | zero =>
    intro pre hl _ _ r w h
    have hnil : pre = [] := List.eq_nil_of_length_eq_zero hl
    subst hnil
    simp only [List.mapM_nil, pure, ReaderT.pure, StateT.pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at h
    rw [← h.2]
    exact liveCounts_init p ts tx hI z top hz htop
  | succ k ih =>
    intro pre hl post hsplit r w h
    rcases List.eq_nil_or_concat pre with hnil | ⟨pre', op, hpre⟩
    · subst hnil; simp at hl
    · rw [List.concat_eq_append] at hpre
      subst hpre
      have hl' : pre'.length = k := by simp at hl; omega
      rw [List.mapM_append] at h
      simp only [List.mapM_cons, List.mapM_nil, bind, ReaderT.bind, StateT.bind, Except.bind] at h
      cases h1 : (pre'.mapM putKv) (ctxOf p ts) (wInit tx top) with
      | error e => rw [h1] at h; cases h
      | ok rw1 =>
        rcases rw1 with ⟨r1, w1⟩
        rw [h1] at h
        simp only at h
        cases h2 : putKv op (ctxOf p ts) w1 with
        | error e => rw [h2] at h; cases h
        | ok aw =>
          rcases aw with ⟨a, w2⟩
          rw [h2] at h
          simp only [pure, ReaderT.pure, StateT.pure, Except.pure, Except.ok.injEq,
            Prod.mk.injEq] at h
          have hsplit' : tx.ops = pre' ++ op :: post := by rw [hsplit]; simp
          obtain ⟨hI1, hR1⟩ := joint_reached p R hRL hT hP hO ts tx hw hr hTA hI z top hz htop
            pre' (op :: post) hsplit' r1 w1 h1
          have hL1 := ih pre' hl' (op :: post) hsplit' r1 w1 h1
          have hT2 : WriterTreeOK p (treeRun p ts) (ts.length + 1) w2 :=
            hT ts tx hw hr z top hz htop pre' op post hsplit' r1 w1 h1 hI1 hR1 trivial a w2 h2
          have hL2 := hLv ts tx hw hr z top hz htop pre' op post hsplit' r1 w1 h1 hI1 hR1 trivial a
            w2 h2 hT2 hL1
          rw [← h.2]
          exact hL2

/-! ## Into the structure after the run -/

/-- `LiveCounts` at the transaction's last state gives `NonEmptyOK`, `RootsOK`
and `FillOK` of the structure after it, by the commit's lift. -/
theorem liveCounts_commit (p : Params) (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx]))
    (hl : CommitLiftAt p ts tx) (noops : List Bool) (w : W)
    (hrun : runOps p tx.base tx.ops (ts.length + 1)
      (view (treeSpec p) (treeRun p ts) ts.length) = .ok (noops, w))
    (hL : LiveCounts p (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey) :
    NonEmptyOK p (treeRun p (ts ++ [tx])) (ts.length + 1) ∧
      RootsOK p (treeRun p (ts ++ [tx])) (ts.length + 1) ∧
      FillOK p (treeRun p (ts ++ [tx])) (ts.length + 1) := by
  obtain ⟨hK, htaken, htopt⟩ := hl noops w hrun
  have hroot := rootAt_commit_of_lift p ts tx hw noops w hrun hK htaken htopt
  have hN : knodeOf p (viewOf (treeRun p (ts ++ [tx]))) = wNode p (viewOf (treeRun p ts)) w :=
    funext hK
  apply liveCounts_parts p _ _ w.top.rootKey hroot
  rw [hN]
  exact hL

/-- The walk's ranges at the transaction's last state give `RangeAtOK` of the
structure after it, by the commit's lift. -/
theorem rangeAtOK_commit (p : Params) (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx]))
    (hl : CommitLiftAt p ts tx) (noops : List Bool) (w : W)
    (hrun : runOps p tx.base tx.ops (ts.length + 1)
      (view (treeSpec p) (treeRun p ts) ts.length) = .ok (noops, w))
    (hR : RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey) :
    RangeAtOK p (treeRun p (ts ++ [tx])) (ts.length + 1) := by
  obtain ⟨hK, htaken, htopt⟩ := hl noops w hrun
  have hroot := rootAt_commit_of_lift p ts tx hw noops w hrun hK htaken htopt
  have hN : keyNodeAt p (treeRun p (ts ++ [tx])) = wNode p (viewOf (treeRun p ts)) w :=
    funext (fun x => (keyNodeAt_eq_knodeOf p _ x).trans (hK x))
  intro r hr
  rw [hroot] at hr
  cases hr
  rw [hN]
  exact hR

end SIS.Tree
