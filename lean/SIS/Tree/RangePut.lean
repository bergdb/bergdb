import SIS.Tree.GetCascadePut
import SIS.Tree.RangeChain

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! A put keeps the walk's ranges (bergdb 024-12, TP10; `RangeOrder`): the
leaf with the put's klong (`rangeOrder_leafPut`: the key's compare value lies
in the leaf's range, `leaf_range`), then the cascade above it
(`writerWP_appendKlongs_chainRange`). -/

/-- The walk's ranges after a key klong (cv, v) is put in the leaf L of the
key's last segment cv, v no node. -/
theorem rangeOrder_leafPut (N : NodeId → Option KNode) (t : Time) (r : NodeId)
    (hR : RangeOrder N t r) (hT : TreeOK N t r) (hwf : ∀ x xn, N x = some xn → klongsWf xn.ks = true)
    (htimes : ∀ x xn, N x = some xn → ∀ s, Klong.time s ∈ xn.ks → s ≤ t)
    (fuel : Nat) (pre : List Nat) (cv : Nat) (rk L v : NodeId) (n : KNode)
    (hrk : segRootR N t fuel pre r = some rk) (hL : (L, cv) ∈ eqVisits N t cv fuel rk)
    (hn : N L = some n) (hnl : n.leaf = true) (hv : N v = none) :
    RangeOrder (updN N L (n.add t (.key cv v))) t r := by
  have hvL : v ≠ L := by intro h; rw [h, hn] at hv; cases hv
  have hlf : (n.add t (.key cv v)).leaf = true := by rw [KNode.add_leaf]; exact hnl
  apply rangeOrder_nodeChange N _ t r L n (n.add t (.key cv v)) hR hn (updN_self _ _ _)
    (KNode.add_leaf _ _ _) (fun z hz => updN_ne _ _ _ _ hz)
  · intro lo hi hLr
    obtain ⟨hlo, hhi⟩ := leaf_range N t r hT hwf fuel pre cv rk L hrk hL lo hi hLr
    intro q hq
    obtain ⟨c', z⟩ := q
    simp only [hlf, ↓reduceIte]
    rcases KNode.add_key_liveAt_mem n t cv v (hwf L n hn) (htimes L n hn) c' z hq with
      ⟨h1, _⟩ | ⟨_, h2⟩
    · rw [h1]; exact ⟨hlo, hhi⟩
    · have := hR L lo hi n hLr hn (c', z) h2
      simp only [hnl, ↓reduceIte] at this
      exact this
  · intro c' z hz
    rcases KNode.add_key_liveAt_mem n t cv v (hwf L n hn) (htimes L n hn) c' z hz with
      ⟨_, h2⟩ | ⟨_, h2⟩
    · right; rw [h2, updN_ne _ _ _ _ hvL]; exact hv
    · exact Or.inl h2
  · intro h; rw [hlf] at h; cases h

end SIS.Tree
