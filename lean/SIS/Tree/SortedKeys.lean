import SIS.Tree.Spec

namespace SIS.Tree

theorem keyLt_irrefl (key : Key) : keyLt key key = false := by
  induction key with
  | nil => rfl
  | cons a rest ih => simp [keyLt, ih]

theorem keyLt_trans (a b c : Key) (hab : keyLt a b = true) (hbc : keyLt b c = true) :
    keyLt a c = true := by
  induction a generalizing b c with
  | nil =>
    cases c with
    | nil => cases b <;> simp [keyLt] at hbc
    | cons _ _ => rfl
  | cons x xs ih =>
    cases b with
    | nil => simp [keyLt] at hab
    | cons y ys =>
      cases c with
      | nil => simp [keyLt] at hbc
      | cons z zs =>
        simp only [keyLt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
          beq_iff_eq] at hab hbc ⊢
        rcases hab with hab | ⟨hab, htail⟩ <;>
          rcases hbc with hbc | ⟨hbc, htail'⟩
        · exact Or.inl (Nat.lt_trans hab hbc)
        · exact Or.inl (by omega)
        · exact Or.inl (by omega)
        · exact Or.inr ⟨hab.trans hbc, ih ys zs htail htail'⟩

theorem sortedKeys_head (a : Key) (keys : List Key) (hs : sortedKeys (a :: keys) = true) :
    ∀ b ∈ keys, keyLt a b = true := by
  induction keys generalizing a with
  | nil => simp
  | cons b keys ih =>
    have hh : keyLt a b = true ∧ sortedKeys (b :: keys) = true := by
      simpa only [sortedKeys, Bool.and_eq_true] using hs
    intro c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact hh.1
    · exact keyLt_trans a b c hh.1 (ih b hh.2 c hc)

theorem sortedKeys_pairwise (keys : List Key) (hs : sortedKeys keys = true) :
    keys.Pairwise (fun a b => keyLt a b = true) := by
  induction keys with
  | nil => exact .nil
  | cons a keys ih =>
    apply List.pairwise_cons.mpr
    refine ⟨sortedKeys_head a keys hs, ih ?_⟩
    cases keys with
    | nil => rfl
    | cons b keys =>
      have hh : keyLt a b = true ∧ sortedKeys (b :: keys) = true := by
        simpa only [sortedKeys, Bool.and_eq_true] using hs
      exact hh.2

theorem sortedKeys_nodup (keys : List Key) (hs : sortedKeys keys = true) : keys.Nodup := by
  apply List.Pairwise.imp _ (sortedKeys_pairwise keys hs)
  intro a b hab heq
  subst b
  rw [keyLt_irrefl] at hab
  cases hab

/-- Strict key order already contains the one-operation-per-key premise. -/
theorem Tx.keys_nodup (tx : Tx) (hs : tx.sorted = true) : (tx.ops.map (·.key)).Nodup :=
  sortedKeys_nodup _ hs

end SIS.Tree
