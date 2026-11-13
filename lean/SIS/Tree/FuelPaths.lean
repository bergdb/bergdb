/-
The fuel of a reading and the depth of the writer's tree (bergdb 024-12, TP10's
`OpGetOK`; 024-22): `PathsFit N t r fuel`, every path from r (by the live
klongs, through all segments) is shorter than `fuel`, so a search with one more
fuel finds the same (`getEqR_fuel_succ`).
-/
import SIS.Tree.WriterTreeDepth

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

/-- A node at depth a of a tree whose paths fit `fuel`: its paths fit `fuel - a`. -/
theorem PathsFit.reached {N : NodeId → Option KNode} {t : Time} {r : NodeId} {fuel : Nat}
    (h : PathsFit N t r fuel) (x : NodeId) (a : Nat) (hx : PathLen N t r x a) :
    PathsFit N t x (fuel - a) := by
  intro z k hz
  have := h z (a + k) (hx.append hz.toFrom)
  omega

/-- A search with one more fuel finds the same, when the tree below is shallow. -/
theorem getEqR_fuel_succ (N : NodeId → Option KNode) (t : Time) (r : NodeId) (cv : Nat) :
    ∀ f x a, PathLen N t r x a → (∀ z k, PathLen N t r z k → k < a + f) →
      getEqR N t cv (f + 1) x = getEqR N t cv f x := by
  intro f
  induction f with
  | zero => intro x a hx hall; have := hall x a hx; omega
  | succ f ih =>
    intro x a hx hall
    cases hN : N x with
    | none => simp only [getEqR, hN]
    | some n =>
      simp only [getEqR, hN]
      split
      · rfl
      · cases hfd : n.searchLte t cv with
        | none => rfl
        | some fd =>
          simp only
          exact ih fd.y (a + 1) (PathLen.link hx ⟨n, hN, KNode.searchLte_mem n t cv fd hfd⟩)
            (fun z k hz => by have := hall z k hz; omega)

end SIS.Tree
