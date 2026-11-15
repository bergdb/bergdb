/-
Three premises of the top theorems are false as stated (bergdb 024-22, section 11.1):
`hCoU` (`CollapseUnlinkAllOK`), `hU` (`UpUnlinkTreeOK`) and `hHL` (`UpHolderLiveRunOK`).
Each speaks of every writer state that meets a local invariant (`CollGetInvF` and
`SegDesc`; `PutInv` and `UpLoopEnd`), and those invariants carry none of the writer's
books: nothing ties a cached node's previous version, the next id or the nodes taken back
to the run. The runs checked the premises only at the states that runs reach. Each
counterexample is a small state at the first run (ts = []), for every parameter set, so
`invGetScanOK_merges` and `invGetScanOK_merges_noOutside` hold vacuously as they stand.
-/
import SIS.Tree.LatestTop

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## `hCoU`: a segment root's previous version naming an id at or above the next id -/

/-- A space root of time 0 with a klong of time 1, over the leaf 11. -/
def cxN : KNode := { leaf := false, ks := [.time 0, .key 0 11, .time 1, .key 0 11] }
def cxY : KNode := { leaf := true, ks := [] }
def cxTop : Top := ⟨2, 0, 0, 10, []⟩
/-- A state with the next id 0: the root's version before time 1 names 11, not below it. -/
def cxV : W := { next := 0, top := cxTop, nodes := [(10, cxN), (11, cxY)], path := [(none, 10)] }

theorem cx_liveN : cxN.liveAt 1 = [(0, 11)] := by decide +kernel
theorem cx_prevN : (cxN.toPrev 0).liveAt 1 = [(0, 11)] := by decide +kernel
theorem cx_liveY : cxY.liveAt 1 = [] := by decide +kernel

theorem cx_w10 (p : Params) (base : View BVal) : wNode p base cxV 10 = some cxN := by
  simp [wNode, cxV]
theorem cx_w11 (p : Params) (base : View BVal) : wNode p base cxV 11 = some cxY := by
  simp [wNode, cxV, List.lookup]

theorem cx_reach (p : Params) (base : View BVal) (z : NodeId)
    (h : TReach (wNode p base cxV) 1 10 z) : z = 10 ∨ z = 11 := by
  induction h with
  | root => exact Or.inl rfl
  | link _ hl ih =>
    obtain ⟨n, hn, hm⟩ := hl
    rcases ih with rfl | rfl
    · rw [cx_w10] at hn; cases hn; rw [cx_liveN] at hm; simp at hm; exact Or.inr hm.2
    · rw [cx_w11] at hn; cases hn; rw [cx_liveY] at hm; simp at hm

theorem cx_reachS (p : Params) (base : View BVal) (z : NodeId)
    (h : ReachS (wNode p base cxV) 1 10 z) : z = 10 ∨ z = 11 := by
  induction h with
  | root => exact Or.inl rfl
  | step x n c z _ hn hm ih =>
    rcases ih with rfl | rfl
    · rw [cx_w10] at hn; cases hn; rw [cx_liveN] at hm; simp at hm; exact Or.inr hm.2
    · rw [cx_w11] at hn; cases hn; rw [cx_liveY] at hm; simp at hm

theorem cx_tlink (p : Params) (base : View BVal) (x : NodeId) (c : Nat) (y : NodeId)
    (hx : x = 10 ∨ x = 11) (h : TLink (wNode p base cxV) 1 x c y) : x = 10 ∧ c = 0 ∧ y = 11 := by
  obtain ⟨n, hn, hm⟩ := h
  rcases hx with rfl | rfl
  · rw [cx_w10] at hn; cases hn; rw [cx_liveN] at hm; simp at hm; exact ⟨rfl, hm⟩
  · rw [cx_w11] at hn; cases hn; rw [cx_liveY] at hm; simp at hm

theorem cx_tree (p : Params) (base : View BVal) : TreeOK (wNode p base cxV) 1 10 where
  rootKey := ⟨cxN, cx_w10 p base⟩
  rootFree := fun x c hx hl => by
    have := cx_tlink p base x c 10 (cx_reach p base x hx) hl; omega
  oneLink := fun x c x' c' y hx hx' hl hl' => by
    have h1 := cx_tlink p base x c y (cx_reach p base x hx) hl
    have h2 := cx_tlink p base x' c' y (cx_reach p base x' hx') hl'
    omega

theorem cx_val (p : Params) (z : NodeId) (hz : z = 10 ∨ z = 11) :
    wValue (viewOf (treeRun p [])) cxV z = none := by
  rcases hz with rfl | rfl <;> simp [wValue, cxV, valueOf, viewOf, treeRun, initStruct, Struct.get?, root, List.lookup]

theorem cx_node (p : Params) (base : View BVal) (z : NodeId) (zn : KNode) (hz : z = 10 ∨ z = 11)
    (h : wNode p base cxV z = some zn) : zn = cxN ∨ zn = cxY := by
  rcases hz with rfl | rfl
  · rw [cx_w10] at h; cases h; exact Or.inl rfl
  · rw [cx_w11] at h; cases h; exact Or.inr rfl

theorem cx_collGetInvF (p : Params) (vw : View BVal) :
    CollGetInvF ⟨p, 1, vw⟩ (viewOf (treeRun p [])) cxV cxV (p.fuel + 1) := by
  have hr : cxV.top.rootKey = 10 := rfl
  show CollInv ⟨p, 1, vw⟩ _ _ ∧ _
  unfold CollInv
  simp only [hr]
  refine ⟨⟨cx_tree p _, fun y _ => by simp [cxV], fun y yn hy hyn s hs => ?_,
    fun y yn cc z hy hyn hl hm => ?_⟩, fun _ => trivial, ?_, fun y yn hy hyn => ?_,
    fun y yn hy hyn => cx_val p y (cx_reach p _ y hy)⟩
  · rcases cx_node p _ y yn (cx_reach p _ y hy) hyn with rfl | rfl
    · simp [cxN] at hs; omega
    · simp [cxY] at hs
  · rcases cx_reach p _ y hy with rfl | rfl
    · rw [cx_w10] at hyn; cases hyn; rw [cx_liveN] at hm; simp at hm
      rw [hm.2]; exact ⟨cxY, cx_w11 p _⟩
    · rw [cx_w11] at hyn; cases hyn; cases hl
  · intro z hz
    have hf : p.fuel + 1 - 1 = (p.fuel - 1) + 1 := by unfold Params.fuel; omega
    rw [hf]
    rcases cx_reachS p _ z hz with rfl | rfl
    · intro n hn hl c y hm
      rw [cx_w10] at hn; cases hn; rw [cx_liveN] at hm; simp at hm; rw [hm.2]
      cases p.fuel - 1 with
      | zero => intro n hn; rw [cx_w11] at hn; cases hn; rfl
      | succ d => intro n hn hl; rw [cx_w11] at hn; cases hn; cases hl
    · intro n hn hl; rw [cx_w11] at hn; cases hn; cases hl
  · rcases cx_node p _ y yn (cx_reach p _ y hy) hyn with rfl | rfl <;> decide +kernel

theorem cx_segDesc (p : Params) (vw : View BVal) : SegDesc ⟨p, 1, vw⟩ (viewOf (treeRun p [])) 10 cxV := by
  refine ⟨TReach.root, [], rfl, LinkedFrom.nil _, rfl, fun z hz => by simp at hz, Or.inl rfl⟩

/-- `CollapseUnlinkAllOK`, the top theorem's `hCoU`, is false at the first run, for every
parameter set: its states need not have the writer's books, so a cached segment root's
previous version may name ids at or above the next id. -/
theorem collapseUnlinkAllOK_false (p : Params) :
    ¬ ∀ ts, CollapseUnlinkAllOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1) := by
  intro h
  have h1 := h [] cxV cxV 10 cxN (cx_collGetInvF p _) (cx_segDesc p _) (by simp [cxV]) rfl
    (show cxN.firstTime ≠ some 1 by decide +kernel) (show cxN.lastTime = some 1 by decide +kernel)
  have h2 := h1.2 0 11 (by show (0, 11) ∈ (cxN.toPrev 0).liveAt 1; rw [cx_prevN]; simp)
  simp [cxV] at h2

/-! ## `hU` and `hHL`: the upward loop's end with a leaf unlinked, and a node nothing reaches -/

/-- The upward delete's states, at time 1: a space root 10 over a leaf 11; 11's klong of
time 1 deletes its klong of time 0, which names 10. -/
def cuA : KNode := { leaf := false, ks := [.time 1, .key 0 11] }
def cuL : KNode := { leaf := true, ks := [.time 0, .key 0 10, .time 1, .del [1]] }
def cuH : KNode := { leaf := false, ks := [.time 1, .key 0 13] }
/-- The state before the upward loop's end: a space root 10 over a leaf 11 whose klong of
the transaction deletes its klong of before; a node 12 that nothing reaches, naming 13,
which is taken back. -/
def cuW : W := { next := 14, top := cxTop, nodes := [(10, cuA), (11, cuL), (12, cuH)], taken := [1, 13] }
/-- The loop's end: the leaf 11 unlinked to its previous version. -/
def cuW2 : W := { cuW with nodes := (11, cuL.toPrev 0) :: cuW.nodes }

theorem cu_get_none (p : Params) (z : NodeId) (hz : 3 ≤ z) : (treeRun p []).get? z = none := by
  have e0 : (z == root) = false := by simp [root]; omega
  have e1 : (z == 1) = false := by simp; omega
  have e2 : (z == 2) = false := by simp; omega
  simp [treeRun, initStruct, Struct.get?, List.lookup, e0, e1, e2]

theorem cu_knode (p : Params) (z : NodeId) (hz : z ≠ 1) : knodeOf p (viewOf (treeRun p [])) z = none := by
  by_cases h3 : 3 ≤ z
  · simp [knodeOf, viewOf, cu_get_none p z h3]
  simp only [knodeOf, viewOf, treeRun, initStruct, Struct.get?, List.zipIdx_nil, List.foldl_nil]
  by_cases h0 : z = 0
  · subst h0; simp [List.lookup, root, Params.rootLevel]; omega
  have h2 : z = 2 := by omega
  subst h2; simp [List.lookup, root, Params.topLevel]

theorem cu_view (p : Params) (z : NodeId) (h : ((ctxOf p []).view z).isSome = true) : z < 3 := by
  apply Classical.byContradiction
  intro hz
  have hn := cu_get_none p z (by omega)
  simp only [ctxOf, rootless, view] at h
  split at h
  · simp at h
  · split at h
    · rw [hn] at h; simp at h
    · simp at h

theorem cu_value (p : Params) (z : NodeId) (hz : 3 ≤ z) : valueOf (viewOf (treeRun p [])) z = none := by
  simp [valueOf, viewOf, cu_get_none p z hz]

/-- The key nodes of w through the writer's lookup. -/
theorem cu_wNode (p : Params) (w : W) (hw : w.taken = [1, 13]) (z : NodeId) (n : KNode)
    (h : wNode p (viewOf (treeRun p [])) w z = some n) : w.nodes.lookup z = some n := by
  unfold wNode at h
  by_cases h1 : z = 1
  · subst h1; simp [hw] at h
  · rw [hw] at h
    split at h
    · simp at h
    · split at h
      · rename_i m hm; cases h; exact hm
      · rw [cu_knode p z h1] at h; cases h

theorem cu_lookW (z : NodeId) (n : KNode) (h : cuW.nodes.lookup z = some n) :
    (z = 10 ∧ n = cuA) ∨ (z = 11 ∧ n = cuL) ∨ (z = 12 ∧ n = cuH) := by
  simp only [cuW, List.lookup] at h
  by_cases h10 : z = 10
  · subst h10; simp at h; exact Or.inl ⟨rfl, h.symm⟩
  by_cases h11 : z = 11
  · subst h11; simp at h; exact Or.inr (Or.inl ⟨rfl, h.symm⟩)
  by_cases h12 : z = 12
  · subst h12; simp at h; exact Or.inr (Or.inr ⟨rfl, h.symm⟩)
  have e0 : (z == 10) = false := by simp; omega
  have e1 : (z == 11) = false := by simp; omega
  have e2 : (z == 12) = false := by simp; omega
  simp [e0, e1, e2] at h

theorem cu_liveA : cuA.liveAt 1 = [(0, 11)] := by decide +kernel
theorem cu_liveL : cuL.liveAt 1 = [] := by decide +kernel

theorem cu_w10 (p : Params) : wNode p (viewOf (treeRun p [])) cuW 10 = some cuA := by
  simp [wNode, cuW]
theorem cu_w11 (p : Params) : wNode p (viewOf (treeRun p [])) cuW 11 = some cuL := by
  simp [wNode, cuW, List.lookup]

theorem cu_reachS (p : Params) (z : NodeId) (h : ReachS (wNode p (viewOf (treeRun p [])) cuW) 1 10 z) :
    z = 10 ∨ z = 11 := by
  induction h with
  | root => exact Or.inl rfl
  | step x n c z _ hn hm ih =>
    rcases ih with rfl | rfl
    · rw [cu_w10] at hn; cases hn; rw [cu_liveA] at hm; simp at hm; exact Or.inr hm.2
    · rw [cu_w11] at hn; cases hn; rw [cu_liveL] at hm; simp at hm

theorem cu_reach (p : Params) (z : NodeId) (h : TReach (wNode p (viewOf (treeRun p [])) cuW) 1 10 z) :
    z = 10 ∨ z = 11 := by
  induction h with
  | root => exact Or.inl rfl
  | link _ hl ih =>
    obtain ⟨n, hn, hm⟩ := hl
    rcases ih with rfl | rfl
    · rw [cu_w10] at hn; cases hn; rw [cu_liveA] at hm; simp at hm; exact Or.inr hm.2
    · rw [cu_w11] at hn; cases hn; rw [cu_liveL] at hm; simp at hm

theorem cu_tlink (p : Params) (x : NodeId) (c : Nat) (y : NodeId) (hx : x = 10 ∨ x = 11)
    (h : TLink (wNode p (viewOf (treeRun p [])) cuW) 1 x c y) : x = 10 ∧ c = 0 ∧ y = 11 := by
  obtain ⟨n, hn, hm⟩ := h
  rcases hx with rfl | rfl
  · rw [cu_w10] at hn; cases hn; rw [cu_liveA] at hm; simp at hm; exact ⟨rfl, hm⟩
  · rw [cu_w11] at hn; cases hn; rw [cu_liveL] at hm; simp at hm

theorem cu_putInv (p : Params) : PutInv (ctxOf p []) (viewOf (treeRun p [])) cuW := by
  have hc : (ctxOf p []).i = 1 := rfl
  have hcp : (ctxOf p []).p = p := rfl
  have hr : cuW.top.rootKey = 10 := rfl
  have hn : ∀ z n, wNode p (viewOf (treeRun p [])) cuW z = some n →
      (z = 10 ∧ n = cuA) ∨ (z = 11 ∧ n = cuL) ∨ (z = 12 ∧ n = cuH) :=
    fun z n h => cu_lookW z n (cu_wNode p cuW rfl z n h)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [hc, hcp, hr]
  · exact ⟨⟨cuA, cu_w10 p⟩, fun x c hx hl => by have := cu_tlink p x c 10 (cu_reach p x hx) hl; omega,
      fun x c x' c' y hx hx' hl hl' => by
        have h1 := cu_tlink p x c y (cu_reach p x hx) hl
        have h2 := cu_tlink p x' c' y (cu_reach p x' hx') hl'
        omega⟩
  · intro x xn h
    rcases hn x xn h with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> decide +kernel
  · intro x xn h s hs
    rcases hn x xn h with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp [cuA, cuL, cuH] at hs <;> omega
  · refine ⟨fun z hz => ?_, fun z hz => by have := cu_view p z hz; simp [cuW]; omega,
      fun z hz => ?_, fun q hq => by simp [cuW] at hq, by simp [cuW, cxTop]⟩
    · simp only [cuW] at hz ⊢
      by_cases h10 : z = 10
      · subst h10; decide
      by_cases h11 : z = 11
      · subst h11; decide
      by_cases h12 : z = 12
      · subst h12; decide
      have e0 : (z == 10) = false := by simp; omega
      have e1 : (z == 11) = false := by simp; omega
      have e2 : (z == 12) = false := by simp; omega
      simp [List.lookup, e0, e1, e2] at hz
    · simp [cuW] at hz ⊢; omega
  · intro z hz
    simp only [cuW] at hz
    exact ⟨cu_knode p z (by omega), cu_value p z (by omega)⟩
  · intro x xn cc z hx h hm
    rcases cu_reachS p x hx with rfl | rfl
    · rw [cu_w10] at h; cases h; rw [cu_liveA] at hm; simp at hm; simp [cuW]; omega
    · rw [cu_w11] at h; cases h; rw [cu_liveL] at hm; simp at hm
  · intro x hx
    rcases cu_reachS p x hx with rfl | rfl <;> decide
  · intro x xn h
    have hx : x ≠ 1 ∧ x ≠ 13 ∧ 3 ≤ x := by
      rcases hn x xn h with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
    simp [wValue, cuW, cu_value p x hx.2.2]
  · intro q qn L n k1 hq hqn hql hL hLl hk
    rcases cu_reachS p q hq with rfl | rfl
    · intro c' z hz
      rcases hn L n hL with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩
      · simp [cuA] at hLl
      · have : cuL.live = [] := by decide +kernel
        rw [this] at hz; simp at hz
      · simp [cuH] at hLl
    · rw [cu_w11] at hqn; cases hqn; simp [cuL] at hql

/-- The chain: the root 10 is the stop node, the leaf 11 the emptied node. -/
def cuX (i : Nat) : NodeId := if i = 0 then 10 else 11
def cuN (i : Nat) : KNode := if i = 0 then cuA else cuL

theorem cu_loopEnd (p : Params) : UpLoopEnd (ctxOf p []) 0 cuX cuN 1 0 cuW cuW2 cuA := by
  have hc : (ctxOf p []).i = 1 := rfl
  have hL1 : unlinkedNode cuL 1 = cuL.toPrev 0 := by decide +kernel
  refine ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl, fun y _ hy => ?_, by simp [cuW2, cuW, cuX, List.lookup],
    Or.inl rfl, Or.inl rfl, fun h => ?_, fun k hk hk1 => ?_, fun k hk hk1 => ?_⟩
  · have h11 : y ≠ 11 := hy 1 (by omega) (Nat.le_refl _)
    have e : (y == 11) = false := by simp; omega
    simp [cuW2, List.lookup, e]
  · rw [hc] at h
    have : cuN (0 + 1) = cuL := rfl
    rw [this] at h
    exact absurd h (by decide +kernel)
  · have hk' : k = 1 := by omega
    subst hk'
    rw [hc]
    exact Or.inr ⟨cuL.toPrev 0, by simp [cuW2, cuX], by decide +kernel⟩
  · have hk' : k = 1 := by omega
    subst hk'
    rw [hc]
    refine ⟨fun h => absurd h (by decide +kernel), fun _ => ⟨by decide, cuL, Or.inl rfl, ?_⟩⟩
    rw [hL1]; simp [cuW2, cuX]

theorem cu_chain (p : Params) :
    (∀ i, i ≤ 1 → cuW.nodes.lookup (cuX i) = some (cuN i)) ∧
    (∀ i, 0 < i → i ≤ 1 → ((fun _ => 0 : Nat → Nat) i, cuX i) ∈ (cuN (i - 1)).liveAt (ctxOf p []).i) := by
  refine ⟨fun i hi => ?_, fun i hi hi1 => ?_⟩
  · rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> simp [cuW, cuX, cuN, List.lookup]
  · have : i = 1 := by omega
    subst this
    show (0, 11) ∈ cuA.liveAt 1
    rw [cu_liveA]; simp

/-- `UpUnlinkTreeOK`, the top theorem's `hU`, is false at the first run, for every
parameter set: its states need not have the writer's books, so a leaf unlinked at the
upward loop's end may come back as a previous version that names the space root. -/
theorem upUnlinkTreeOK_false (p : Params) :
    ¬ ∀ ts, UpUnlinkTreeOK (ctxOf p ts) (viewOf (treeRun p ts)) := by
  intro h
  have hT := h [] cuW cuW 0 cuX cuN (fun _ => 0) 1 0 cuW2 cuA (cu_putInv p) (ReadsAs.refl _ _ _)
    (cu_chain p).1 (cu_chain p).2 (by omega) (cu_loopEnd p)
  have hc : (ctxOf p []).i = 1 := rfl
  have hcp : (ctxOf p []).p = p := rfl
  rw [hc, hcp] at hT
  have h10 : wNode p (viewOf (treeRun p [])) cuW2 10 = some cuA := by simp [wNode, cuW2, cuW, List.lookup]
  have h11 : wNode p (viewOf (treeRun p [])) cuW2 11 = some (cuL.toPrev 0) := by simp [wNode, cuW2, cuW]
  have hr11 : TReach (wNode p (viewOf (treeRun p [])) cuW2) 1 cuW2.top.rootKey 11 :=
    TReach.link (c := 0) TReach.root ⟨cuA, h10, by rw [cu_liveA]; simp⟩
  exact hT.rootFree 11 0 hr11 ⟨cuL.toPrev 0, h11, by
    show (0, 10) ∈ (cuL.toPrev 0).liveAt 1
    rw [show (cuL.toPrev 0).liveAt 1 = [(0, 10)] by decide +kernel]; simp⟩

/-- `UpHolderLiveRunOK`, the top theorem's `hHL`, is false at the first run, for every
parameter set: its states need not have the writer's books, so a cached node that nothing
reaches may name a node taken back. -/
theorem upHolderLiveRunOK_false (p : Params) :
    ¬ ∀ ts, UpHolderLiveRunOK (ctxOf p ts) (viewOf (treeRun p ts)) := by
  intro h
  have hH := h [] cuW cuW 0 cuX cuN (fun _ => 0) 1 0 cuW2 cuA (cu_putInv p) (ReadsAs.refl _ _ _)
    (cu_chain p).1 (cu_chain p).2 (by omega) (cu_loopEnd p) 12 cuH (by simp [cuW2, cuW, List.lookup])
    (by decide) 0 13 (Or.inl (by rw [show cuH.live = [(0, 13)] by decide +kernel]; simp))
  simp [cuW2, cuW] at hH

end SIS.Tree
