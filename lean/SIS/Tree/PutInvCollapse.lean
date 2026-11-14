import SIS.Tree.WriterTreeCollapse
import SIS.Tree.PutInvDelSpaceCascade

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! Root collapse at the space root keeps the parts of `PutInv` about the tree
(bergdb 024-12, TP10; `collapseRoot` with segment 0): cost's `CollInv` (the
writer's tree, its reached nodes not taken back and of no later time, the live
klongs of its reached inner nodes naming nodes) with `PutInv`'s order at the
leaves (`CollInvP`). A collapse step replaces the root by its only live child:
every node reached after it was reached before and is not the old root, so its
node and its leaf children's are unchanged. -/

/-- `CollInv` with `PutInv`'s order at the leaves. -/
def CollInvP (c : Ctx) (base : View BVal) (w : W) : Prop :=
  CollInv c base w ∧
  (∀ q qn L n k1, ReachS (wNode c.p base w) c.i w.top.rootKey q →
    wNode c.p base w q = some qn → qn.leaf = false → wNode c.p base w L = some n →
    n.leaf = true → (k1, L) ∈ qn.live → LeafOrderAt qn k1 n)

theorem collInvP_of_readsAs (c : Ctx) (base : View BVal) (w v : W) (hr : ReadsAs c.p base w v)
    (h : CollInvP c base w) : CollInvP c base v := by
  refine ⟨collInv_of_readsAs c base w v hr h.1, ?_⟩
  rw [hr.1, hr.2.1]
  exact h.2

/-- One collapse step keeps `CollInvP` (`collInv_step`'s premises). -/
theorem collInvP_step (c : Ctx) (base : View BVal) (w w' : W) (y : NodeId) (cc : Nat)
    (h : CollInvP c base w) (hl : TLink (wNode c.p base w) c.i w.top.rootKey cc y)
    (hrn : ∀ m, wNode c.p base w w.top.rootKey = some m → m.leaf = false)
    (htop : w'.top.rootKey = y)
    (ht : ∀ z, z ≠ w.top.rootKey → w'.taken.contains z = w.taken.contains z)
    (hn : ∀ z, z ≠ w.top.rootKey → w'.nodes.lookup z = w.nodes.lookup z) : CollInvP c base w' := by
  refine ⟨collInv_step c base w w' y cc h.1 hl hrn htop ht hn, ?_⟩
  obtain ⟨⟨hT, _, hTi, hL⟩, hO⟩ := h
  have hN : ∀ z, z ≠ w.top.rootKey → wNode c.p base w' z = wNode c.p base w z := by
    intro z hz; simp only [wNode, ht z hz, hn z hz]
  have hy : ∃ m, wNode c.p base w y = some m := by
    obtain ⟨m, hm, hc⟩ := hl
    exact hL _ m cc y TReach.root hm (hrn m hm) hc
  obtain ⟨_, hreach⟩ := treeOK_collapse_reach (wNode c.p base w) (wNode c.p base w') c.i
    w.top.rootKey y cc hT hl hy hN
  intro q qn L n k1 hq hqn hql hLn hnl hk
  rw [htop] at hq
  have hq' := reachS_tReach _ _ _ _ hq
  obtain ⟨hq1, hq2⟩ := hreach q hq'
  have hqn0 : wNode c.p base w q = some qn := by rw [← hN q hq2]; exact hqn
  have hqt := hTi q qn hq1 hqn0
  have hk' : (k1, L) ∈ qn.liveAt c.i := by rw [KNode.liveAt_of_times qn c.i hqt]; exact hk
  have hL' : TReach (wNode c.p base w') c.i y L := TReach.link hq' ⟨qn, hqn, hk'⟩
  obtain ⟨_, hL2⟩ := hreach L hL'
  have hLn0 : wNode c.p base w L = some n := by rw [← hN L hL2]; exact hLn
  exact hO q qn L n k1 (tReach_reachS _ _ _ _ hq1) hqn0 hql hLn0 hnl hk

/-- `CollInvP` gives the parts of `PutInv` about the tree. -/
theorem putInvT_of_collInvP (c : Ctx) (base : View BVal) (w : W) (h : CollInvP c base w) :
    PutInvT c base w :=
  ⟨fun x hx => h.1.2.1 x (reachS_tReach _ _ _ _ hx), h.2⟩

/-- Root collapse at the space root keeps `CollInvP`: `CollInv` and the order at the leaves. -/
theorem writerWP_collapseRoot_spaceP (key : Key) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) :
    ∀ (fuel : Nat) (w : W), CollInvP c base w →
      WriterWP (collapseRoot key 0 fuel) c w (fun _ w' => CollInvP c base w') := by
  intro fuel
  induction fuel with
  | zero => intro w _; exact writerWP_throw _ _ _ _
  | succ f ih =>
    intro w hI
    unfold collapseRoot descendToSegmentRoot pathClear findRoot pathAdd
    simp only [writerWP_bind, writerWP_read, writerWP_modify, writerWP_get, List.take_zero,
      List.foldlM_nil, writerWP_pure]
    generalize hw1 : ({ ({ w with path := [] } : W) with
      path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w1
    have hr01 : ReadsAs c.p base w w1 := by subst hw1; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    have hp1 : w1.path = [(none, w.top.rootKey)] := by subst hw1; rfl
    have hI1 := collInvP_of_readsAs c base w w1 hr01 hI
    refine writerWP_mono (writerWP_and (writerWP_getNode_all _ c w1 base hvc)
      (writerWP_getNode_cache w.top.rootKey c w1)) ?_
    intro n w2 ⟨⟨hr12, hlk2, hwn2, _, _⟩, ⟨_, _, hp2⟩⟩
    have hr02 := ReadsAs.trans _ _ _ _ _ hr01 hr12
    have hI2 := collInvP_of_readsAs c base w w2 hr02 hI
    have htop2 : w2.top.rootKey = w.top.rootKey := by rw [hr02.2.1]
    have htop1 : w1.top.rootKey = w.top.rootKey := by rw [hr01.2.1]
    have hroot0 : wNode c.p base w2 w.top.rootKey = some n := by
      rw [hr12.1]
      exact hwn2 (by have := hI1.1.2.1 _ TReach.root; rw [htop1] at this; exact this)
    have hroot : wNode c.p base w2 w2.top.rootKey = some n := by rw [htop2]; exact hroot0
    by_cases hleaf : n.leaf = true
    · simp only [hleaf, ↓reduceIte, writerWP_pure]; exact hI2
    · have hleaf' : n.leaf = false := by simpa using hleaf
      simp only [hleaf', Bool.false_eq_true, ↓reduceIte]
      unfold replacedBy
      simp only [writerWP_bind, writerWP_get, writerWP_pure]
      split
      · simp only [writerWP_pure]; exact hI2
      · split
        · simp only [writerWP_pure]; exact hI2
        · rename_i only honly
          split
          · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
          · unfold pathSize
            simp only [writerWP_bind, writerWP_get, writerWP_pure, hp2, hp1, List.length_singleton]
            -- the step's facts
            have hstep : ∀ child, n.ptr? only = some child → ∀ w3 : W, w3.top.rootKey = child →
                (∀ z, z ≠ w.top.rootKey → w3.taken.contains z = w2.taken.contains z) →
                (∀ z, z ≠ w.top.rootKey → w3.nodes.lookup z = w2.nodes.lookup z) →
                CollInvP c base w3 := by
              intro child hptr w3 h3top h3t h3n
              have hnt := hI2.1.2.2.1 _ n TReach.root hroot
              obtain ⟨cc, hcc⟩ := onlyLiveKlong_link n c.i only child hnt honly hptr
              apply collInvP_step c base w2 w3 child cc hI2 ⟨n, hroot, hcc⟩
                (fun m hm => by rw [hroot] at hm; cases hm; exact hleaf') h3top
              · intro z hz; rw [htop2] at hz; exact h3t z hz
              · intro z hz; rw [htop2] at hz; exact h3n z hz
            simp only [Nat.sub_self]
            split
            · cases hp : n.ptr? only with
              | none =>
                rw [writerWP_bind]
                unfold takeBackRoot
                simp only [writerWP_bind, writerWP_read]
                rw [writerWP_getNode_known _ n c w2 hlk2, hp]
                exact writerWP_throw _ _ _ _
              | some child =>
                rw [writerWP_bind]
                refine writerWP_mono (writerWP_takeBackRoot_space _ only n child c w2 hlk2 hp) ?_
                intro _ w3 ⟨h3top, h3t, h3n⟩
                apply ih
                apply hstep child hp w3 h3top
                · intro z hz
                  rw [h3t, List.contains_cons]
                  have : (z == w.top.rootKey) = false := by simpa using hz
                  simp [this]
                · intro z _; rw [h3n]
            · cases hp : n.ptr? only with
              | none =>
                rw [writerWP_bind]
                unfold replaceRoot
                simp only [writerWP_bind, writerWP_read]
                rw [writerWP_getNode_known _ n c w2 hlk2, hp]
                exact writerWP_throw _ _ _ _
              | some child =>
                rw [writerWP_bind]
                refine writerWP_mono (writerWP_replaceRoot_space _ only n child c w2 hlk2 hp) ?_
                intro _ w3 ⟨h3top, h3t, h3n⟩
                apply ih
                apply hstep child hp w3 h3top
                · intro z _; rw [h3t]
                · intro z hz; exact h3n z hz


end SIS.Tree
