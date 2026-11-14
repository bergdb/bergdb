import SIS.Tree.GetRootSplit

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! Every put of a key whose prefix is there, into a leaf below inner nodes with
room for two klongs (bergdb 024-12, TP10; `OpGetOK`'s rules together): with
room, or by a time split or a space split, in place for a leaf the transaction
made, the reading changes by the put alone. -/

/-- A descent's visits hold one leaf at most. -/
theorem eqVisits_leaf_unique (N : NodeId → Option KNode) (t : Time) (cv : Nat) :
    ∀ (f : Nat) (x L1 L2 : NodeId) (n1 n2 : KNode),
      (L1, cv) ∈ eqVisits N t cv f x → (L2, cv) ∈ eqVisits N t cv f x →
      N L1 = some n1 → n1.leaf = true → N L2 = some n2 → n2.leaf = true → L1 = L2 := by
  intro f
  induction f with
  | zero => intro x L1 L2 n1 n2 h1; simp [eqVisits] at h1
  | succ f ih =>
    intro x L1 L2 n1 n2 h1 h2 hn1 hl1 hn2 hl2
    simp only [eqVisits, List.mem_cons, Prod.mk.injEq, and_true] at h1 h2
    cases hx : N x with
    | none =>
      rw [hx] at h1 h2
      simp only [List.not_mem_nil, or_false] at h1 h2
      rw [h1, h2]
    | some n =>
      rw [hx] at h1 h2
      simp only at h1 h2
      by_cases hl : n.leaf = true
      · simp only [hl, ↓reduceIte, List.not_mem_nil, or_false] at h1 h2
        rw [h1, h2]
      · simp only [hl, Bool.false_eq_true, ↓reduceIte] at h1 h2
        have hx1 : L1 ≠ x := by
          intro he; subst he; rw [hn1] at hx; cases hx; exact hl hl1
        have hx2 : L2 ≠ x := by
          intro he; subst he; rw [hn2] at hx; cases hx; exact hl hl2
        rcases h1 with h1 | h1
        · exact absurd h1 hx1
        rcases h2 with h2 | h2
        · exact absurd h2 hx2
        cases hs : n.searchLte t cv with
        | none => rw [hs] at h1; cases h1
        | some fd =>
          rw [hs] at h1 h2
          exact ih fd.y L1 L2 n1 n2 h1 h2 hn1 hl1 hn2 hl2

end SIS.Tree
