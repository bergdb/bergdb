/-
The fuel of a reading and the depth of the writer's tree (bergdb 024-12, TP10's
`OpGetOK`; 024-22): `PathsFit N t r fuel`, every path from r (by the live
klongs, through all segments) is shorter than `fuel`, so a search with one more
fuel finds the same (`getEqR_fuel_succ`). Superseded (2026-11-13, coordinator's
decision): the bounds G and H are checked at a transaction's end, so within it a
segment tree may grow above H and the whole path is not capped; the reader's fuel
is per segment, and the premise is latest's `SegFits N t (p.fuel - 1) r`
(`GetFuel.lean`), every path inside one segment tree shorter than the fuel. Here:
`SegDepthLe.of_inner`, `segFits_transfer`.
-/
import SIS.Tree.WriterTreeDepth
import SIS.Tree.GetFuel

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- Every path from r is shorter than `fuel`. -/
def PathsFit (N : NodeId → Option KNode) (t : Time) (r : NodeId) (fuel : Nat) : Prop :=
  ∀ z k, PathLen N t r z k → k < fuel

/-- A path from the root r of a tree read from r is a path from r. -/
theorem PathLen.toFrom {N : NodeId → Option KNode} {t : Time} {r z : NodeId} {k : Nat}
    (h : PathLen N t r z k) : PathFromLen N t r z k := by
  induction h with
  | root => exact PathFromLen.refl _
  | link _ hl ih => exact PathFromLen.link ih hl

theorem PathsFit.pos {N : NodeId → Option KNode} {t : Time} {r : NodeId} {fuel : Nat}
    (h : PathsFit N t r fuel) : 0 < fuel := h r 0 PathLen.root

/-- An inner node of segment depth at most d: d is one more than its live
children's bound. -/
theorem SegDepthLe.of_inner {N : NodeId → Option KNode} {t : Time} {d : Nat} {x : NodeId}
    {n : KNode} (h : SegDepthLe N t d x) (hn : N x = some n) (hl : n.leaf = false) :
    ∃ d', d = d' + 1 ∧ ∀ c y, (c, y) ∈ n.liveAt t → SegDepthLe N t d' y := by
  cases d with
  | zero => have := h n hn; rw [hl] at this; cases this
  | succ d' => exact ⟨d', rfl, fun c y hy => h n hn hl c y hy⟩

/-- `SegFits` carried to another node map: every node that N' reaches from r'
was reached by N from r, and every reached inner node of N' was an inner node
of N whose live klongs name what the new one's name. -/
theorem segFits_transfer (N N' : NodeId → Option KNode) (t : Time) (d : Nat) (r r' : NodeId)
    (h : SegFits N t d r) (hR : ∀ u, ReachS N' t r' u → ReachS N t r u)
    (hI : ∀ u un', ReachS N' t r' u → N' u = some un' → un'.leaf = false →
      ∃ un, N u = some un ∧ un.leaf = false ∧ ∀ c y, (c, y) ∈ un'.liveAt t → ∃ c0, (c0, y) ∈ un.liveAt t) :
    SegFits N' t d r' := by
  have key : ∀ e u, ReachS N' t r' u → SegDepthLe N t e u → SegDepthLe N' t e u := by
    intro e
    induction e with
    | zero =>
      intro u hu hd un' hun'
      cases hl : un'.leaf with
      | true => rfl
      | false =>
        obtain ⟨un, hun, hunl, _⟩ := hI u un' hu hun' hl
        have := hd un hun
        rw [hunl] at this; cases this
    | succ e ih =>
      intro u hu hd un' hun' hl c y hy
      obtain ⟨un, hun, hunl, hlk⟩ := hI u un' hu hun' hl
      obtain ⟨c0, hc0⟩ := hlk c y hy
      exact ih y (ReachS.step u un' c y hu hun' hy) (hd un hun hunl c0 y hc0)
  intro u hu
  exact key d u hu (h u (hR u hu))

end SIS.Tree
