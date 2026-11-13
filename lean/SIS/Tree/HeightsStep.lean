/-
The heights of P's key nodes along a run (bergdb 024-22, step 4; 024-12, TP7's
open (b)). `HeightAllOK`: every inner key node of P has its live children at
time t that are nodes of P one height below it. It is stronger than TP7's
`HeightLiveOK`, which asks it of the key nodes reached from the root
(`heightLiveOK_of_all`). A transaction keeps it when the writer's overlay at its
end has `HtCache` (`heightAllOK_step`): a key node after it is an overlay node
not taken back, with the overlay's klongs, or a node of P unchanged.
-/
import SIS.Tree.WriterHeightsPut
import SIS.Tree.KindsStep

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- Every inner key node of P has its live children at time t that are nodes
of P one height below it. -/
def HeightAllOK (p : Params) (P : Struct BVal) (t : Time) : Prop :=
  ∀ x nd, P.get? x = some nd → nd.isData = false → nd.level ≤ p.keyMax →
    p.heightOf nd.level ≠ 0 →
    ∀ c y, (c, y) ∈ (nodeK p nd).liveAt t → ∀ ny, P.get? y = some ny →
      p.heightOf ny.level + 1 = p.heightOf nd.level

/-- The heights of P's key nodes, as the walk's oracle. -/
def htOracleOf (p : Params) (P : Struct BVal) : NodeId → Nat → Prop :=
  fun y h => ∃ ny, P.get? y = some ny ∧ ny.isData = false ∧ ny.level ≤ p.keyMax ∧
    p.heightOf ny.level = h

/-- A node of P reached from the root at time t is a key node of P. -/
theorem ht_key_of_knodeOf {p : Params} {P : Struct BVal} {x : NodeId} {n : KNode}
    (h : knodeOf p (viewOf P) x = some n) :
    ∃ nd, P.get? x = some nd ∧ nd.isData = false ∧ nd.level ≤ p.keyMax ∧ n = nodeK p nd := by
  obtain ⟨nd, hnd, hd, hlv, rfl⟩ := ht_knodeOf_some h
  exact ⟨nd, hnd, hd, hlv, rfl⟩

/-- The live klongs of a node do not depend on its leaf flag. -/
theorem ht_liveAt_leaf (l1 l2 : Bool) (ks : List Klong) (t : Time) :
    (⟨l1, ks⟩ : KNode).liveAt t = (⟨l2, ks⟩ : KNode).liveAt t := rfl

section Step

variable (p : Params) (P : Struct BVal) (i : Time) (tx : Tx) (bs : List Bool) (w : W)

/-- A node of height h in the writer's books keeps it after the transaction. -/
theorem heightsStep_hasHt (hfresh : ∀ q ∈ P, q.1 < tx.base) (htimes : StructTimesLE P (i - 1))
    (he : execW p tx i (view (treeSpec p) P (i - 1)) = .ok (bs, w))
    (hbook : Book tx.base { p := p, i := i, view := rootless (view (treeSpec p) P (i - 1)) } w)
    (y : NodeId) (h : Nat)
    (hy : HasHt (htOracleOf p P) w y h)
    (ny : Node BVal) (hny : (P.apply i (changesOf i w)).get? y = some ny) :
    p.heightOf ny.level = h := by
  rcases hy with ⟨g, hgh⟩ | ⟨nd, hPy, _, _, hh⟩
  · exact (kindsStep_gh p P i tx bs w hfresh htimes he hbook y g h hgh ny hny).2.2.2
  · obtain ⟨h1, _⟩ := kindsStep_old P i _ y nd ny hPy hny
    rw [h1]
    exact hh

/-- A transaction keeps `HeightAllOK` when the writer's overlay at its end has
`HtCache`. -/
theorem heightAllOK_step (hpos : 0 < i) (hfresh : ∀ q ∈ P, q.1 < tx.base)
    (htimes : StructTimesLE P (i - 1))
    (hroot : ∃ r, P.get? root = some r ∧ p.keyMax < r.level) (hH : KeyHistOK p P)
    (hl : ViewLinksOK tx.base p (view (treeSpec p) P (i - 1)))
    (hP : PointersOK P)
    (he : execW p tx i (view (treeSpec p) P (i - 1)) = .ok (bs, w))
    (hbook : Book tx.base { p := p, i := i, view := rootless (view (treeSpec p) P (i - 1)) } w)
    (hA : HeightAllOK p P (i - 1))
    (hHt : HtCache { p := p, i := i, view := rootless (view (treeSpec p) P (i - 1)) }
      (htOracleOf p P) w) :
    HeightAllOK p (P.apply i (changesOf i w)) i := by
  intro x nd' hx hd hlv h0 cv y hlive ny' hy
  rcases apply_keyNode p P i tx bs w hpos hfresh htimes hroot hH hl he x nd' hx hd hlv with
    ⟨n, hlook, htk, _, hks, _⟩ | ⟨hPx, _⟩
  · have hmem := mem_ids_of_lookup w.nodes x n hlook
    have hxg : x ∈ (w.gh.map (·.1)).reverse := by
      rw [← hbook.ids]
      exact List.mem_map.mpr ⟨(x, n), hmem, rfl⟩
    obtain ⟨⟨x', g, h⟩, hgh, hx'⟩ := List.mem_map.mp (List.mem_reverse.mp hxg)
    have hxx : x' = x := hx'
    rw [hxx] at hgh
    obtain ⟨_, _, _, hh⟩ := kindsStep_gh p P i tx bs w hfresh htimes he hbook x g h hgh nd' hx
    have hN := hHt x n g h hmem hgh htk
    have hnk : nodeK p nd' = ⟨p.heightOf nd'.level == 0, n.ks⟩ := by
      unfold nodeK; rw [hks]
    rw [hnk, ht_liveAt_leaf _ n.leaf] at hlive
    have hlive' : (cv, y) ∈ n.liveAt i := hlive
    rw [KNode.liveAt_of_times n i hN.3] at hlive'
    have hh0 : h ≠ 0 := by rw [← hh]; exact h0
    have hy' := (hN.1 cv y hlive').2 hh0
    have := heightsStep_hasHt p P i tx bs w hfresh htimes he hbook y (h - 1) hy' ny' hy
    omega
  · have hkx : knodeOf p (viewOf P) x = some (nodeK p nd') := by
      unfold knodeOf viewOf
      rw [hPx]
      have : ¬ (nd'.isData || decide (p.keyMax < nd'.level)) = true := by
        simp only [hd, Bool.false_or, decide_eq_true_eq]; omega
      simp only [this]
      rfl
    have hi1 : i = (i - 1) + 1 := by omega
    have hlive0 : (cv, y) ∈ (nodeK p nd').liveAt (i - 1) := by
      rw [← liveAt_succ_of_timesLE p P (i - 1) htimes x _ hkx, ← hi1]
      exact hlive
    obtain ⟨ny, hPy⟩ := kindsStep_ptr P hP x nd' hPx cv y
      (KNode.liveAt_key_mem _ _ _ _ hlive0)
    obtain ⟨h1, _⟩ := kindsStep_old P i _ y ny ny' hPy hy
    rw [h1]
    exact hA x nd' hPx hd hlv h0 cv y hlive0 ny hPy

end Step

/-- The walk's premises on the view at a transaction's start, from P: its key
nodes' heights from `HeightAllOK`, the children's existence from `PointersOK`
and their kind from `KindsAllOK`. -/
theorem viewHeights_of (p : Params) (P : Struct BVal) (t : Time) (B : NodeId)
    (hfresh : ∀ q ∈ P, q.1 < B) (htimes : StructTimesLE P t) (hP : PointersOK P)
    (hK : KindsAllOK p P) (hA : HeightAllOK p P t) :
    ViewHeights (htOracleOf p P) B { p := p, i := t + 1, view := rootless (view (treeSpec p) P t) } := by
  have hlive : ∀ x nd, P.get? x = some nd → nd.isData = false → nd.level ≤ p.keyMax →
      p.heightOf nd.level ≠ 0 → ∀ cv y, (cv, y) ∈ (nodeK p nd).live →
      htOracleOf p P y (p.heightOf nd.level - 1) := by
    intro x nd hx hd hlv h0 cv y hy
    have htm : ∀ s, Klong.time s ∈ (nodeK p nd).ks → s ≤ t := fun s hs =>
      klongsOf_times nd.hist t (htimes _ (mem_of_get? hx)) _ hs s rfl
    have hyt : (cv, y) ∈ (nodeK p nd).liveAt t := by
      rw [KNode.liveAt_of_times _ t htm]; exact hy
    obtain ⟨ny, hPy⟩ := kindsStep_ptr P hP x nd hx cv y (KNode.liveAt_key_mem _ _ _ _ hyt)
    have hk := (hK x nd hx hd hlv cv y (KNode.liveAt_key_mem _ _ _ _ hyt) ny hPy).1 h0
    have hh := hA x nd hx hd hlv h0 cv y hyt ny hPy
    exact ⟨ny, hPy, hk.1, hk.2.1, by omega⟩
  have hget : ∀ x nd, (rootless (view (treeSpec p) P t)) x = some nd → P.get? x = some nd :=
    fun x nd hv => view_eq_get? p P t htimes x nd (rootless_some_eq _ x nd hv)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro y h ⟨ny, hy, _, _, _⟩
    exact hfresh _ (mem_of_get? hy)
  · rintro y h h' ⟨ny, hy, _, _, hh⟩ ⟨ny', hy', _, _, hh'⟩
    rw [hy] at hy'
    obtain rfl := Option.some.inj hy'
    rw [← hh, ← hh']
  · intro x nd hv hd hlv
    exact ⟨nd, hget x nd hv, hd, hlv, rfl⟩
  · intro x nd hv hd hlv h0 cv y hy
    exact hlive x nd (hget x nd hv) hd hlv h0 cv y hy
  · intro x nd hv hd hlv h0 cv y hy
    have hx := hget x nd hv
    have htm : ∀ s, Klong.time s ∈ (nodeK p nd).ks → s ≤ t := fun s hs =>
      klongsOf_times nd.hist t (htimes _ (mem_of_get? hx)) _ hs s rfl
    have he : (nodeK p nd).toPrev (t + 1 - 1) = nodeK p nd := by
      unfold KNode.toPrev
      rw [Nat.add_sub_cancel, prefixAt_eq_self _ t htm]
    rw [he] at hy
    exact hlive x nd hx hd hlv h0 cv y hy

/-- The reading's premise on its base P: every key node has its height, is a
segment leaf exactly at 0, and an inner one has its live children one height
below it. -/
theorem baseHeights_of (p : Params) (P : Struct BVal) (t : Time) (c : Ctx) (hcp : c.p = p)
    (hct : t ≤ c.i) (htimes : StructTimesLE P t) (hP : PointersOK P) (hK : KindsAllOK p P)
    (hA : HeightAllOK p P t) :
    BaseHeights c (htOracleOf p P) (viewOf P) := by
  intro x n hk
  subst hcp
  obtain ⟨nd, hx, hd, hlv, rfl⟩ := ht_knodeOf_some hk
  have htm : ∀ s, Klong.time s ∈ klongsOf nd.hist → s ≤ t := fun s hs =>
    klongsOf_times nd.hist t (htimes _ (mem_of_get? hx)) _ hs s rfl
  refine ⟨c.p.heightOf nd.level, ⟨nd, hx, hd, hlv, rfl⟩, rfl, fun s hs => Nat.le_trans (htm s hs) hct,
    fun h0 cv y hy => ?_⟩
  have hyt : (cv, y) ∈ (nodeK c.p nd).liveAt t := by
    rw [KNode.liveAt_of_times _ t htm]; exact hy
  obtain ⟨ny, hPy⟩ := kindsStep_ptr P hP x nd hx cv y (KNode.liveAt_key_mem _ _ _ _ hyt)
  have hk := (hK x nd hx hd hlv cv y (KNode.liveAt_key_mem _ _ _ _ hyt) ny hPy).1 h0
  have hh := hA x nd hx hd hlv h0 cv y hyt ny hPy
  exact ⟨ny, hPy, hk.1, hk.2.1, by omega⟩

/-- The primordial structure has no inner key node with a live klong. -/
theorem heightAllOK_init (p : Params) (t : Time) : HeightAllOK p (initStruct p) t := by
  intro x nd hx hd hlv _ c y hk
  rcases mem_init p (x, nd) (mem_of_get? hx) with h | h | h
  · simp only [Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    simp only [Params.rootLevel] at hlv
    omega
  · simp only [Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    have hz : klongsOf [(⟨0, marker⟩ : Entry BVal)] = [Klong.time 0] := by decide
    have hm := KNode.liveAt_key_mem _ _ _ _ hk
    simp only [nodeK, hz, List.mem_singleton, reduceCtorEq] at hm
  · simp only [Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    simp only [Params.topLevel] at hlv
    omega

/-- TP7's (b) at time t from `HeightAllOK`: the key nodes reached from the root
are key nodes of P. -/
theorem heightLiveOK_of_all (p : Params) (P : Struct BVal) (t : Time)
    (hA : HeightAllOK p P t)
    (hkey : ∀ x ∈ keyNodesAt p P t, ∀ nd, P.get? x = some nd →
      nd.isData = false ∧ nd.level ≤ p.keyMax) :
    HeightLiveOK p P t := by
  intro x hx nd hnd h0 c y hy ny hny
  obtain ⟨hd, hlv⟩ := hkey x hx nd hnd
  exact hA x nd hnd hd hlv h0 c y hy ny hny

end SIS.Tree
