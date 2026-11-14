import SIS.Tree.NormalizedDead
import SIS.Tree.SpaceSplitMap

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- Ordered merge outputs contain no dead key klong. The hypotheses are
exactly the local order/range conditions of TP38, without fill thresholds. -/
theorem mergeKlongs_deadCount (inner : Bool) (cap cR : Nat)
    (left right : List (Nat × NodeId)) (hcap : 1 ≤ cap)
    (hL : CvSorted left) (hR : CvSorted right) (hLc : ∀ q ∈ left, q.1 < cR)
    (hRt : ∀ q ∈ right.tail, cR < q.1)
    (hRl : inner = false → ∀ q ∈ right, cR ≤ q.1) (t : Time) :
    (⟨!inner, newKlongs t (mergeKlongs inner cap cR left right).1⟩ : KNode).deadCount = 0 ∧
      ∀ rest g, (mergeKlongs inner cap cR left right).2 = some (rest, g) →
        (⟨!inner, newKlongs t rest⟩ : KNode).deadCount = 0 := by
  obtain ⟨hfirst, hsecond⟩ := mergeOrderOK inner cap cR left right hcap hL hR hLc hRt hRl
  constructor
  · apply KNode.newKlongs_deadCount
    exact List.pairwise_map.mpr (hfirst.imp (by intro a b h; omega))
  · intro rest g hr
    apply KNode.newKlongs_deadCount
    exact List.pairwise_map.mpr ((hsecond rest g hr).2.imp (by intro a b h; omega))

end SIS.Tree
