/-
The upward delete keeps the walk's ranges (bergdb 024-12, TP10; `RangeOrder`):
prover cost's upward walk with the ranges as its postcondition. At tree level the
stop node loses its klong to the emptied chain (`rangeOrder_up_bitmap`) or, the
empty key's, moves its next klong to the empty key (`rangeOrder_up_leb`); root
collapse at the space root keeps `CollInv` and the ranges.
-/
import SIS.Tree.WriterGetUpAll
import SIS.Tree.RangeLeb
import SIS.Tree.RangeCollapse
import SIS.Tree.RangeChainG

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A node in place of itself: the lookup unchanged. -/
theorem updN_self_eq (N : NodeId → Option KNode) (x : NodeId) (n : KNode) (hx : N x = some n) :
    updN N x n = N := by
  funext z
  by_cases hz : z = x
  · rw [hz, updN_self, hx]
  · exact updN_ne _ _ _ _ hz

/-- The walk's ranges after the upward delete at tree level, the stop node X s
losing its klong K (s + 1) to the chain X (s + 1) .. X D (a bitmap), the chain
left out (as `treeOK_up_tr`). -/
theorem rangeOrder_up_bitmap (N N' : NodeId → Option KNode) (t : Time) (r : NodeId)
    (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (s D : Nat) (hsD : s < D)
    (hR : RangeOrder N t r) (hT : TreeOK N t r) (hXs : TReach N t r (X s))
    (hN : ∀ i, s ≤ i → i ≤ D → N (X i) = some (Nn i))
    (hlinkK : ∀ i, s < i → i ≤ D → (K i, X i) ∈ (Nn (i - 1)).liveAt t)
    (hdist : ∀ i i', s ≤ i → i ≤ D → s ≤ i' → i' ≤ D → X i = X i' → i = i')
    (hagree : ∀ u, u ≠ X s → (∀ i, s < i → i ≤ D → u ≠ X i) → N' u = N u)
    (sn' : KNode) (hsn' : N' (X s) = some sn') (hleaf' : sn'.leaf = (Nn s).leaf)
    (hlive' : ∀ c z, (c, z) ∈ sn'.liveAt t → (c, z) ∈ (Nn s).liveAt t ∧ c ≠ K (s + 1)) :
    RangeOrder N' t r := by
  have hNs := hN s (Nat.le_refl _) (by omega)
  have hR1 : RangeOrder (updN N (X s) sn') t r :=
    rangeOrder_updN_sub N t r (X s) (Nn s) sn' (by rw [updN_self_eq N (X s) (Nn s) hNs]; exact hR)
      hleaf' (fun c z h => (hlive' c z h).1)
  refine rangeOrder_agree _ N' t r hR1 ?_
  intro z hz
  have hsub := tReach_up_sub_tr N (updN N (X s) sn') t r X Nn K s D hsD hT hXs hN hlinkK hdist
    (fun u hu _ => updN_ne _ _ _ _ hu) sn' (updN_self _ _ _)
    (fun c z h => ⟨c, (hlive' c z h).1, (hlive' c z h).2⟩) z hz
  by_cases hzs : z = X s
  · rw [hzs, hsn', updN_self]
  · rw [hagree z hzs hsub.2, updN_ne _ _ _ _ hzs]

/-- The walk's ranges after the upward delete at tree level whose stop node X s,
inner, loses the empty key K (s + 1) = 0 to the chain and moves its next klong
(jcv, jy) to the empty key (LE-b), the chain left out. -/
theorem rangeOrder_up_leb (N N' : NodeId → Option KNode) (t : Time) (r : NodeId)
    (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (s D : Nat) (hsD : s < D)
    (hR : RangeOrder N t r) (hT : TreeOK N t r) (hXs : TReach N t r (X s))
    (hN : ∀ i, s ≤ i → i ≤ D → N (X i) = some (Nn i))
    (hlinkK : ∀ i, s < i → i ≤ D → (K i, X i) ∈ (Nn (i - 1)).liveAt t)
    (hdist : ∀ i i', s ≤ i → i ≤ D → s ≤ i' → i' ≤ D → X i = X i' → i = i')
    (hagree : ∀ u, u ≠ X s → (∀ i, s < i → i ≤ D → u ≠ X i) → N' u = N u)
    (sn' : KNode) (hsn' : N' (X s) = some sn') (hsl : (Nn s).leaf = false)
    (hleaf' : sn'.leaf = (Nn s).leaf) (hK0 : K (s + 1) = 0)
    (jcv : Nat) (jy : NodeId) (hj : (jcv, jy) ∈ (Nn s).liveAt t) (hj0 : 0 < jcv)
    (hmin : ∀ c z, (c, z) ∈ (Nn s).liveAt t → c ≠ 0 → jcv ≤ c)
    (hlive' : ∀ c z, (c, z) ∈ sn'.liveAt t ↔
      (c = 0 ∧ z = jy) ∨ ((c, z) ∈ (Nn s).liveAt t ∧ c ≠ 0 ∧ c ≠ jcv)) :
    RangeOrder N' t r := by
  have hNs := hN s (Nat.le_refl _) (by omega)
  have hR1 : RangeOrder (updN N (X s) sn') t r :=
    rangeOrder_leb N (updN N (X s) sn') t r (X s) (Nn s) sn' jcv jy hR hNs hsl (updN_self _ _ _)
      (by rw [hleaf', hsl]) (fun z hz => updN_ne _ _ _ _ hz) hj (by omega) hmin
      (fun cc z h => by
        rcases (hlive' cc z).mp h with h1 | ⟨h1, _, h3⟩
        · exact Or.inl h1
        · exact Or.inr ⟨h1, h3⟩)
  refine rangeOrder_agree _ N' t r hR1 ?_
  intro z hz
  have hsub := tReach_up_sub_tr N (updN N (X s) sn') t r X Nn K s D hsD hT hXs hN hlinkK hdist
    (fun u hu _ => updN_ne _ _ _ _ hu) sn' (updN_self _ _ _)
    (fun c z h => by
      rcases (hlive' c z).mp h with ⟨_, h2⟩ | ⟨h1, h2, _⟩
      · exact ⟨jcv, by rw [h2]; exact hj, by omega⟩
      · exact ⟨c, h1, by omega⟩) z hz
  by_cases hzs : z = X s
  · rw [hzs, hsn', updN_self]
  · rw [hagree z hzs hsub.2, updN_ne _ _ _ _ hzs]

end SIS.Tree
