import SIS.Tree.PutInvSplit
import SIS.Tree.WriterTreeSpace

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! Facts of the halves for `PutInv` kept by the space splits of a put below an
inner parent with room (bergdb 024-12, TP10): of a leaf that existed before the
transaction (two new halves) and in place (the leaf keeps the first half). The
halves' compare values lie on either side of the divider sc, the second half's
first compare value, a live compare value of the leaf; the parent's klong k1 names the
first half and a klong sc the second. -/

/-! ## The rules -/

theorem flatAt_times (i : Time) (ks : List Klong) (h : FlatAt i ks) :
    ∀ s, Klong.time s ∈ ks → s ≤ i := by
  obtain ⟨r, rfl, hr⟩ := h
  intro s hs
  rcases List.mem_cons.mp hs with h1 | h1
  · cases h1; exact Nat.le_refl _
  · obtain ⟨cv, y, he⟩ := hr _ h1; cases he

theorem halves_leaf_flags (leaf : Bool) (t : Time) (last : KNode) (ins : List (Nat × NodeId)) :
    (halves leaf t last ins).1.leaf = leaf ∧ (halves leaf t last ins).2.1.leaf = leaf := by
  unfold halves
  simp only []
  constructor <;> (split <;> (try split) <;> (try split) <;> simp_all)

theorem halves_times (leaf : Bool) (n : KNode) (t : Time) (ins : List (Nat × NodeId)) :
    (∀ s, Klong.time s ∈ (halves leaf t (n.lastVersion t) ins).1.ks → s ≤ t) ∧
    (∀ s, Klong.time s ∈ (halves leaf t (n.lastVersion t) ins).2.1.ks → s ≤ t) := by
  have h := halves_flatAt leaf t (n.lastVersion t) ins (KNode.lastVersion_flat n t)
  exact ⟨flatAt_times t _ h.1, flatAt_times t _ h.2⟩

end SIS.Tree
