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

/-- Reading keys in strict order reads their segment prefixes in
nondecreasing order, including prefixes shared by several operations. -/
theorem keyLt_take (n : Nat) (a b : Key) (hs : keyLt a b = true) :
    a.take n = b.take n ∨ keyLt (a.take n) (b.take n) = true := by
  induction n generalizing a b with
  | zero => exact Or.inl rfl
  | succ n ih =>
    cases a with
    | nil =>
      cases b with
      | nil => simp [keyLt] at hs
      | cons _ _ => exact Or.inr rfl
    | cons x xs =>
      cases b with
      | nil => simp [keyLt] at hs
      | cons y ys =>
        simp only [keyLt, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
          beq_iff_eq] at hs
        rcases hs with hxy | ⟨rfl,htail⟩
        · right
          simp [keyLt,hxy]
        · rcases ih xs ys htail with he | he
          · exact Or.inl (by simp [he])
          · exact Or.inr (by simp [keyLt,he])

/-- A prefix group is contiguous in strict key order. Once an operation has
left a segment-prefix group, no later operation can return to it. -/
theorem keyLt_prefix_between (n : Nat) (a b c : Key)
    (hab : keyLt a b = true) (hbc : keyLt b c = true) (he : a.take n = c.take n) :
    b.take n = a.take n := by
  have hab' := keyLt_take n a b hab
  have hbc' := keyLt_take n b c hbc
  rw [← he] at hbc'
  rcases hab' with hab' | hab'
  · exact hab'.symm
  · rcases hbc' with hbc' | hbc'
    · exact hbc'
    · have hh := keyLt_trans _ _ _ hab' hbc'
      rw [keyLt_irrefl] at hh
      cases hh


/-- Later full keys in the same segment-prefix group have a nondecreasing
compare value in that segment. -/
theorem keyLt_segment_mono (g : Nat) (a b : Key) (ca cb : Nat)
    (hs : keyLt a b = true) (hp : a.take g = b.take g)
    (ha : a[g]? = some ca) (hb : b[g]? = some cb) : ca ≤ cb := by
  induction g generalizing a b with
  | zero =>
    cases a with
    | nil => simp at ha
    | cons x xs =>
      cases b with
      | nil => simp at hb
      | cons y ys =>
        simp only [List.getElem?_cons_zero,Option.some.injEq] at ha hb
        subst ca
        subst cb
        simp only [keyLt,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq] at hs
        omega
  | succ g ih =>
    cases a with
    | nil => simp at ha
    | cons x xs =>
      cases b with
      | nil => simp at hb
      | cons y ys =>
        simp only [List.take_succ_cons,List.cons.injEq] at hp
        rcases hp with ⟨rfl,hp⟩
        have ht : keyLt xs ys = true := by simpa only [keyLt,Nat.lt_irrefl,decide_false,BEq.rfl,Bool.true_and,Bool.false_or] using hs
        exact ih xs ys ht hp ha hb

end SIS.Tree
