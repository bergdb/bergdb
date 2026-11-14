import SIS.Tree.GetDelCascade

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The cascades into a parent the transaction made (bergdb 024-12, TP10): its
time split in place, with the writer's cache kept, and a node replaced by one with the
same live klongs (`getFromR_congr_node`). -/

/-- Two readers that differ only at q, whose nodes there have the same kind and
the same live klongs at t, read alike. -/
theorem getFromR_congr_node (N1 N2 : NodeId → Option KNode) (V : NodeId → Option Nat) (t : Time)
    (fuel : Nat) (q : NodeId) (a b : KNode)
    (hsame : ∀ x, x ≠ q → N1 x = N2 x) (ha : N1 q = some a) (hb : N2 q = some b)
    (hleaf : a.leaf = b.leaf) (hwa : klongsWf a.ks = true) (hwb : klongsWf b.ks = true)
    (hta : ∀ s, Klong.time s ∈ a.ks → s ≤ t) (htb : ∀ s, Klong.time s ∈ b.ks → s ≤ t)
    (hl : ∀ c, a.live.lookup c = b.live.lookup c) :
    ∀ key r, getFromR N1 V t fuel key r = getFromR N2 V t fuel key r := by
  have hid : ∀ z : NodeId, (if z = q then q else z) = z := fun z => by
    by_cases h : z = q <;> simp [h]
  have hS : RenSim N1 N2 t (fun _ => True) q q := by
    intro x _
    simp only [hid]
    by_cases hx : x = q
    · subst hx
      rw [ha, hb]
      refine ⟨rfl, ?_⟩
      intro n1 n2 h1 h2
      cases h1; cases h2
      refine ⟨hleaf, fun c => ⟨fun _ => ⟨?_, fun _ _ => trivial⟩, fun _ => ⟨?_, fun _ _ => trivial⟩⟩⟩
      · simp only [Option.map_id']
        rw [KNode.searchEq_live _ t hwa hta, KNode.searchEq_live _ t hwb htb, hl]
      · simp only [Option.map_id']
        exact KNode.searchLte_congr _ _ t hta htb hl c
    · rw [hsame x hx]
      refine ⟨rfl, ?_⟩
      intro n1 n2 h1 h2
      rw [h1] at h2; cases h2
      exact ⟨rfl, fun c => ⟨fun _ => ⟨by simp [Function.comp_def], fun _ _ => trivial⟩,
        fun _ => ⟨by simp [Function.comp_def], fun _ _ => trivial⟩⟩⟩
  intro key r
  have := getFromR_ren N1 N2 V V t fuel _ q q hS (fun a => by simp [hid]) key r trivial
  simpa [hid] using this

end SIS.Tree
