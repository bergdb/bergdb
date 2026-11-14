/-
The tree model (bergdb 024-12, TP2): the empty key first, read from `Live0`,
and the step of a run. A node with a klong of the empty key that its last
bitmap does not delete, and no time klong after t, has the empty key's klong
first among its live klongs at t (`Live0.liveAt_head`). A transaction keeps
`LeftAllOK` when the writer's overlay has `LeftCache` (`leftAllOK_step`), and
`LeftAllOK` gives the leftmost rule at the latest time
(`leftmostOK_of_leftAll`).
-/
import SIS.Tree.OverlayLeft
import SIS.Tree.OverlayLift
import SIS.Tree.InvInit
import SIS.Tree.IntervalSearchProof
import SIS.Tree.SegmentRange

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## 1. The node's reading -/

/-- With no time klong after t, a node with the empty key live has the empty
key's klong first among its live klongs at t. -/
theorem Live0.liveAt_head (n : KNode) (t : Time) (h : Live0 n)
    (ht : ∀ u, Klong.time u ∈ n.ks → u ≤ t) :
    ((n.liveAt t).head?.map (·.1)) = some 0 := by
  obtain ⟨i, y, hi, hb⟩ := h
  have hpre := prefixAt_eq_self n.ks t ht
  have hmem : 0 ∈ (n.liveAt t).map Prod.fst := by
    apply (n.liveAt_has_key t 0).mpr
    refine ⟨y, i, ?_, ?_⟩
    · rw [hpre]
      exact List.mk_mem_zipIdx_iff_getElem?.mpr hi
    · intro hc
      unfold KNode.delAt at hc
      rw [hpre] at hc
      unfold KNode.lastBitmap at hb
      simp [hc] at hb
  have hord := n.liveAt_order t
  generalize n.liveAt t = l at hmem hord ⊢
  cases l with
  | nil => simp at hmem
  | cons a r =>
    simp only [List.map_cons, List.mem_cons] at hmem
    rcases hmem with h0 | h0
    · simp [h0]
    · obtain ⟨b, hbm, hb0⟩ := List.mem_map.mp h0
      have := (List.pairwise_cons.mp hord).1 b hbm
      omega

/-! ## 2. The step of a run -/

/-- A transaction keeps `LeftAllOK`: a key node of the structure after it is
a node of P as it was, or a node of the writer's overlay, which `LeftCache`
covers. -/
theorem leftAllOK_step (p : Params) (P : Struct BVal) (i : Time) (tx : Tx) (bs : List Bool) (w : W)
    (hpos : 0 < i) (hfresh : ∀ q ∈ P, q.1 < tx.base) (htimes : StructTimesLE P (i - 1))
    (hroot : ∃ r, P.get? root = some r ∧ p.keyMax < r.level) (hH : KeyHistOK p P)
    (hl : ViewLinksOK tx.base p (view (treeSpec p) P (i - 1)))
    (he : execW p tx i (view (treeSpec p) P (i - 1)) = .ok (bs, w))
    (hbook : Book tx.base { p := p, i := i, view := rootless (view (treeSpec p) P (i - 1)) } w)
    (htaken : TakenAbove tx.base w)
    (hL : LeftAllOK p P) (hLW : LeftCache w) :
    LeftAllOK p (P.apply i (changesOf i w)) := by
  intro x nd hx hd hlv
  rcases apply_keyNode p P i tx bs w hpos hfresh htimes hroot hH hl he x nd hx hd hlv with
    ⟨n, hlook, hnt, _, _, _⟩ | ⟨hP, _⟩
  · have hk := (overlayLift_of_book p P i tx bs w hpos hfresh htimes hroot hH hl he hbook
      htaken).1 x n hlook hnt
    have hlv' : ¬ p.keyMax < nd.level := by omega
    have hn : n = ⟨p.heightOf nd.level == 0, klongsOf nd.hist⟩ := by
      simp only [knodeOf, viewOf, hx, hd, hlv', Bool.false_or, decide_false, Bool.false_eq_true,
        ↓reduceIte, Option.some.injEq] at hk
      exact hk.symm
    rw [← hn]
    exact hLW (x, n) (mem_ids_of_lookup w.nodes x n hlook)
  · exact hL x nd hP hd hlv

/-- The view at t of a structure without later entries has the empty key live
in every inner key node. -/
theorem viewLeftOK_of_leftAll (p : Params) (P : Struct BVal) (t : Time)
    (htimes : StructTimesLE P t) (hL : LeftAllOK p P) :
    ViewLeftOK p (view (treeSpec p) P t) := by
  intro x nd hv hd hlv
  exact hL x nd (view_eq_get? p P t htimes x nd hv) hd hlv

/-- The structure at the start: its only key node is a segment leaf. -/
theorem leftAllOK_init (p : Params) : LeftAllOK p (initStruct p) := by
  intro x nd hx hd hlv
  have hm := mem_of_get? hx
  rcases mem_init p (x, nd) hm with h | h | h
  · simp only [Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    simp only [Params.rootLevel] at hlv
    omega
  · simp only [Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    intro hleaf
    simp [heightOf_initial_key] at hleaf
  · simp only [Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    simp only [Params.topLevel] at hlv
    omega

/-! ## 3. TP2 at the latest time -/

/-- TP2 at a time with no later entry in P, from `LeftAllOK`. -/
theorem leftmostOK_of_leftAll (p : Params) (P : Struct BVal) (t : Time)
    (htimes : StructTimesLE P t) (_hH : KeyHistOK p P) (hL : LeftAllOK p P) :
    LeftmostOK p P t := by
  intro x _ n hn hleaf
  unfold keyNodeAt at hn
  cases hx : P.get? x with
  | none => simp [hx] at hn
  | some nd =>
    simp only [hx] at hn
    by_cases hc : (!nd.isData && decide (nd.level ≤ p.keyMax)) = true
    · simp only [hc, ↓reduceIte, Option.some.injEq] at hn
      subst hn
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
      obtain ⟨hd, hlv⟩ := hc
      have hnode := hL x nd hx hd hlv hleaf
      apply Live0.liveAt_head _ t hnode.2
      intro u hu
      obtain ⟨e, he, het⟩ := klongsOf_time_mem nd.hist u hu
      rw [← het]
      exact htimes _ (mem_of_get? hx) e he
    · simp only [hc, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hn

end SIS.Tree
