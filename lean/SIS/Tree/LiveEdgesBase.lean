/-
`LiveCounts` edge by edge, its basic part (bergdb 024-12, TP7): `LiveEdges`
states the conditions of `LiveCounts` on the root and on each link of the tree
reached. The space root has a live klong unless it is a segment leaf, and two
if it is inner (`RootOK`). The node a link names has a live klong; two if a
segment leaf names it and it is inner; m if an inner node names it and the
merges are on (`ChildOK`). A step of the writer then checks only the links it
changes: a node that keeps its kind and live pointees and loses no live klong
(`liveEdges_updN_grow`), a fresh copy, a change off the tree, and the halves of a
space split (`HalfOK`). The equivalence with `LiveCounts` is in `LiveEdges.lean`;
this part sits below the writer's cascade walk (`WriterTreeChainG.lean`).
-/
import SIS.Tree.WriterTreeChainTree

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The conditions on a node named by a live klong of un. -/
def ChildOK (p : Params) (t : Time) (un yn : KNode) : Prop :=
  yn.liveAt t ≠ [] ∧ (un.leaf = true → yn.leaf = false → 2 ≤ (yn.liveAt t).length) ∧
    (un.leaf = false → p.merges = true → p.mergeBelow ≤ (yn.liveAt t).length)

/-- The conditions on the space root. -/
def RootOK (t : Time) (rn : KNode) : Prop :=
  (rn.liveAt t = [] → rn.leaf = true) ∧ (rn.leaf = false → 2 ≤ (rn.liveAt t).length)

/-- `LiveCounts` link by link. -/
def LiveEdges (p : Params) (N : NodeId → Option KNode) (t : Time) (r : NodeId) : Prop :=
  (∀ rn, N r = some rn → RootOK t rn) ∧
  ∀ u un c y yn, TReach N t r u → N u = some un → (c, y) ∈ un.liveAt t → N y = some yn →
    ChildOK p t un yn

theorem childOK_grow (p : Params) (t : Time) (un un' yn yn' : KNode) (h : ChildOK p t un yn)
    (hu : un'.leaf = un.leaf) (hy : yn'.leaf = yn.leaf)
    (hlen : (yn.liveAt t).length ≤ (yn'.liveAt t).length) : ChildOK p t un' yn' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun hE => ?_, fun hl hyl => ?_, fun hl hm => ?_⟩
  · have h0 : (yn'.liveAt t).length = 0 := by rw [hE]; rfl
    exact h1 (List.eq_nil_of_length_eq_zero (by omega))
  · rw [hu] at hl; rw [hy] at hyl; have := h2 hl hyl; omega
  · rw [hu] at hl; have := h3 hl hm; omega

/-- A node x whose klongs keep its kind, name live only what it named live or
no node, and lose no live klong keeps `LiveEdges`. -/
theorem liveEdges_updN_grow (p : Params) (N : NodeId → Option KNode) (t : Time) (r x : NodeId)
    (n n' : KNode) (hx : N x = some n) (hl : n'.leaf = n.leaf)
    (hch : ∀ c y, (c, y) ∈ n'.liveAt t → (∃ c', (c', y) ∈ n.liveAt t) ∨ updN N x n' y = none)
    (hlen : (n.liveAt t).length ≤ (n'.liveAt t).length) (h : LiveEdges p N t r) :
    LiveEdges p (updN N x n') t r := by
  have hreach : ∀ u, TReach (updN N x n') t r u → TReach N t r u ∨ updN N x n' u = none := by
    intro u hu
    induction hu with
    | root => exact Or.inl TReach.root
    | @link u c y _ hl' ih =>
      obtain ⟨m, hm, hc⟩ := hl'
      rcases ih with ih | ih
      · by_cases hux : u = x
        · subst hux
          rw [updN_self] at hm
          cases hm
          rcases hch c y hc with ⟨c', hc'⟩ | hy
          · exact Or.inl (TReach.link ih ⟨n, hx, hc'⟩)
          · exact Or.inr hy
        · rw [updN_ne _ _ _ _ hux] at hm
          exact Or.inl (TReach.link ih ⟨m, hm, hc⟩)
      · rw [hm] at ih; cases ih
  refine ⟨fun rn hrn => ?_, fun u un c y yn hu hun hc hyn => ?_⟩
  · by_cases hrx : r = x
    · subst hrx
      rw [updN_self] at hrn
      cases hrn
      obtain ⟨h1, h2⟩ := h.1 n hx
      refine ⟨fun hE => ?_, fun hl' => ?_⟩
      · have h0 : (n'.liveAt t).length = 0 := by rw [hE]; rfl
        rw [hl]; exact h1 (List.eq_nil_of_length_eq_zero (by omega))
      · rw [hl] at hl'; have := h2 hl'; omega
    · rw [updN_ne _ _ _ _ hrx] at hrn
      exact h.1 rn hrn
  · have hu' : TReach N t r u := by
      rcases hreach u hu with h' | h'
      · exact h'
      · rw [hun] at h'; cases h'
    by_cases hux : u = x
    · subst hux
      rw [updN_self] at hun
      cases hun
      rcases hch c y hc with ⟨c', hc'⟩ | hy
      · by_cases hyx : y = u
        · subst hyx
          rw [updN_self] at hyn
          cases hyn
          exact childOK_grow p t n n' n n' (h.2 y n c' y n hu' hx hc' hx) hl hl hlen
        · rw [updN_ne _ _ _ _ hyx] at hyn
          exact childOK_grow p t n n' yn yn (h.2 u n c' y yn hu' hx hc' hyn) hl rfl (Nat.le_refl _)
      · rw [hy] at hyn; cases hyn
    · rw [updN_ne _ _ _ _ hux] at hun
      by_cases hyx : y = x
      · subst hyx
        rw [updN_self] at hyn
        cases hyn
        exact childOK_grow p t un un n n' (h.2 u un c y n hu' hun hc hx) rfl hl hlen
      · rw [updN_ne _ _ _ _ hyx] at hyn
        exact h.2 u un c y yn hu' hun hc hyn

/-! ## Agreement, and the space splits -/

/-- A node any parent may name: a live klong, two at least, and m with the
merges on (a space split's half). -/
def HalfOK (p : Params) (t : Time) (zn : KNode) : Prop :=
  zn.liveAt t ≠ [] ∧ 2 ≤ (zn.liveAt t).length ∧
    (p.merges = true → p.mergeBelow ≤ (zn.liveAt t).length)

theorem childOK_half (p : Params) (t : Time) (un zn : KNode) (h : HalfOK p t zn) :
    ChildOK p t un zn :=
  ⟨h.1, fun _ _ => h.2.1, fun _ hm => h.2.2 hm⟩

theorem rootOK_half (p : Params) (t : Time) (zn : KNode) (h : HalfOK p t zn) : RootOK t zn :=
  ⟨fun hE => absurd hE h.1, fun _ => h.2.1⟩

end SIS.Tree
