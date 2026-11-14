import SIS.Tree.HistoricalGetDirect

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The reader-visible facts retained from an old structure. Only existing
key nodes, values and roots are constrained. -/
structure ReadExtension (p : Params) (t : Time) (P Q : Struct BVal) : Prop where
  key : ∀ x n, knodeOf p (viewOf P) x = some n →
    ∃ next, knodeOf p (viewOf Q) x = some next ∧ next.leaf = n.leaf ∧
      prefixAt next.ks t = prefixAt n.ks t
  value : ∀ y value, valueOf (viewOf P) y = some value → valueOf (viewOf Q) y = some value
  root : ∀ r, rootAt (viewOf P) t = some r → rootAt (viewOf Q) t = some r

theorem readExtension_refl (p : Params) (t : Time) (P : Struct BVal) : ReadExtension p t P P :=
  ⟨by intro x n hn; exact ⟨n, hn, rfl, rfl⟩,
   by intro y value hv; exact hv,
   by intro r hr; exact hr⟩

theorem ReadExtension.trans (p : Params) (t : Time) (P Q R : Struct BVal)
    (hPQ : ReadExtension p t P Q) (hQR : ReadExtension p t Q R) : ReadExtension p t P R := by
  constructor
  · intro x n hn
    obtain ⟨mid, hm, hleaf, hpre⟩ := hPQ.key x n hn
    obtain ⟨last, hl, hleaf', hpre'⟩ := hQR.key x mid hm
    exact ⟨last, hl, hleaf'.trans hleaf, hpre'.trans hpre⟩
  · intro y value hv
    exact hQR.value y value (hPQ.value y value hv)
  · intro r hr
    exact hQR.root r (hPQ.root r hr)

theorem readExtension_apply_past (p : Params) (P : Struct BVal) (i t : Time)
    (changes : Changes BVal) (ht : t < i) : ReadExtension p t P (P.apply i changes) :=
  ⟨knodeOf_apply_past p P i t changes ht,
   valueOf_apply_some P i changes,
   rootAt_apply_some_past P i t changes ht⟩

/-- Every prefix is extended at its own time by the complete run. This is
an unconditional consequence of structure application, including runs with
rejected transactions. -/
theorem treeRun_readExtension_prefix (p : Params) (ts : List Tx) (t : Time)
    (ht : t ≤ ts.length) :
    ReadExtension p t (treeRun p (ts.take t)) (treeRun p ts) := by
  have hf : ∀ revts : List Tx, ∀ u ≤ revts.reverse.length,
      ReadExtension p u (treeRun p (revts.reverse.take u)) (treeRun p revts.reverse) := by
    intro revts
    induction revts with
    | nil =>
      intro u hu
      simp only [List.reverse_nil, List.take_nil]
      exact readExtension_refl p u (treeRun p [])
    | cons tx revts ih =>
      intro u hu
      simp only [List.reverse_cons] at hu ⊢
      by_cases hle : u ≤ revts.reverse.length
      · rw [List.take_append_of_le_length hle, treeRun_snoc]
        exact ReadExtension.trans p u _ _ _ (ih u hle)
          (readExtension_apply_past p _ (revts.reverse.length + 1) u _ (by omega))
      · have he : u = (revts.reverse ++ [tx]).length := by
          simp only [List.length_append, List.length_singleton] at hu ⊢
          omega
        rw [he, List.take_length]
        exact readExtension_refl p _ _
  simpa only [List.reverse_reverse] using hf ts.reverse t (by simpa using ht)

/-- Latest-time structural correctness, without the historical or global
pointer-closure clauses of TP7. -/
def LatestInvOK (p : Params) : Prop :=
  ∀ ts, Within p ts → InvOK p (treeRun p ts) ts.length

end SIS.Tree
