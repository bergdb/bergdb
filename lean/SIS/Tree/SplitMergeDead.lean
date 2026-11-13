import SIS.Tree.NormalizedDead
import SIS.Tree.SpaceSplitMap

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- With no upward klongs to append, the actual split outputs are the two
normalized sublists, including the inner second half's empty-key rename. -/
theorem halves_no_inserts_shape (leaf : Bool) (t : Time) (pairs : List (Nat × NodeId)) :
    (halves leaf t ⟨leaf, newKlongs t pairs⟩ []).1 =
      ⟨leaf, newKlongs t (pairs.take (pairs.length / 2))⟩ ∧
    (halves leaf t ⟨leaf, newKlongs t pairs⟩ []).2.1 =
      ⟨leaf, newKlongs t (secondSplitPairs leaf pairs)⟩ := by
  cases hd : pairs.drop (pairs.length / 2) with
  | nil =>
    cases leaf <;> simp [halves, newKlongs, KNode.size, ← List.map_take,
      ← List.map_drop, hd, secondSplitPairs, renameHead]
  | cons q rest =>
    cases leaf <;> simp [halves, newKlongs, KNode.size, ← List.map_take,
      ← List.map_drop, hd, secondSplitPairs, renameHead]

theorem halves_no_inserts_deadCount (leaf : Bool) (t : Time) (pairs : List (Nat × NodeId))
    (hs : CvSorted pairs) :
    (halves leaf t ⟨leaf, newKlongs t pairs⟩ []).1.deadCount = 0 ∧
      (halves leaf t ⟨leaf, newKlongs t pairs⟩ []).2.1.deadCount = 0 := by
  obtain ⟨hf, hsecond⟩ := halves_no_inserts_shape leaf t pairs
  rw [hf, hsecond]
  constructor
  · apply KNode.newKlongs_deadCount
    apply List.pairwise_map.mpr
    exact (hs.sublist (List.take_sublist _ _)).imp (by intro a b h; omega)
  · apply KNode.newKlongs_deadCount
    apply List.pairwise_map.mpr
    exact (secondSplitPairs_order leaf pairs hs).imp (by intro a b h; omega)

/-- A delete's space-split outputs contain no dead physical key. No
parameter, fill, input-history or supplied-bitmap premise is needed. -/
theorem halves_normalized_no_inserts_deadCount (n : KNode) (t : Time) (bits : List Nat) :
    (halves n.leaf t (n.lastVersionGivenDel t bits) []).1.deadCount = 0 ∧
      (halves n.leaf t (n.lastVersionGivenDel t bits) []).2.1.deadCount = 0 := by
  obtain ⟨pairs, hks, hs⟩ := n.lastVersionGivenDel_order t bits
  have he : n.lastVersionGivenDel t bits = ⟨n.leaf, newKlongs t pairs⟩ := by
    have hl : (n.lastVersionGivenDel t bits).leaf = n.leaf := rfl
    cases ho : n.lastVersionGivenDel t bits
    simp_all [newKlongs]
  rw [he]
  exact halves_no_inserts_deadCount n.leaf t pairs hs

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
