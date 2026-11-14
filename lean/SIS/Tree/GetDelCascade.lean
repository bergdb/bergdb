import SIS.Tree.GetFinal

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The delete into a full leaf whose parent is full too (bergdb 024-12, TP10;
the cascades): the descent of a delete with its last three nodes g, q, L
(`writerWP_del_path`). -/

/-! ## The writer: a delete's time split of a leaf whose parent is full and time split -/

/-! ## The reading after a delete's time split and its parent's -/

/-! ## The bitmap of a delete whose leaf's parent is full -/

/-! ## The rule: a delete into a leaf whose parent is full and time split -/

/-! ## The bitmap of a delete, the leaf's time split given -/

/-! ## The writer: a delete's time split of a leaf whose parent is full and space split -/

/-! ## The reading after a delete's time split and its parent's space split -/

/-! ## The rule: a delete into a leaf whose parent is full and space split -/

/-! ## The writer: a delete's space split of a leaf whose parent is full and time split -/

/-! ## The writer: a delete's space split of a leaf whose parent is full and space split -/

/-- The halves of a last version with nothing put have klongs of no later
time. -/
theorem halves_nil_times (t : Time) (pairs : List (Nat × NodeId)) :
    (∀ s, Klong.time s ∈ (halves true t ⟨true, newKlongs t pairs⟩ []).1.ks → s ≤ t) ∧
    (∀ s, Klong.time s ∈ (halves true t ⟨true, newKlongs t pairs⟩ []).2.1.ks → s ≤ t) := by
  obtain ⟨first, hfirst⟩ := halves_first_shape true t pairs []
  obtain ⟨extra, hsecond⟩ := halves_second_shape true t pairs []
  rw [hfirst, hsecond]
  exact ⟨newKlongs_times t _, newKlongs_times t _⟩

/-! ## The reading after a delete's space split and its parent's time split -/

/-! ## The bitmap of a delete, the leaf's space split given -/

/-! ## The rule: a delete's space split of a leaf whose parent is full and time split -/

/-! ## The reading after a delete's space split and its parent's space split -/

/-! ## The rule: a delete's space split of a leaf whose parent is full and space split -/

end SIS.Tree
