/-
Proofs, part 7: small facts used by the step proof.
-/
import SIS.Proof.Init

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ### Lists -/

theorem flatMap_congr_mem {α β : Type} {l : List α} {f g : α → List β}
    (h : ∀ a ∈ l, f a = g a) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.flatMap_cons]
    rw [h a (List.mem_cons_self), ih (fun b hb => h b (List.mem_cons_of_mem a hb))]

theorem flatMap_filter_ite {α β : Type} (l : List α) (p : α → Bool) (f : α → List β) :
    (l.filter p).flatMap f = l.flatMap (fun a => if p a then f a else []) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases ha : p a = true
    · simp [ha, ih]
    · simp [ha, ih]

theorem nodup_eraseDups_aux : ∀ (b : Nat) (l : List Nat), l.length < b → l.eraseDups.Nodup := by
  intro b
  induction b with
  | zero => intro l h; omega
  | succ b ih =>
    intro l hl
    cases l with
    | nil => simp
    | cons a l =>
      rw [List.eraseDups_cons, List.nodup_cons]
      constructor
      · rw [List.mem_eraseDups]
        simp
      · apply ih
        have := List.length_filter_le (fun b => !b == a) l
        simp at hl
        omega

theorem nodup_eraseDups (l : List Nat) : l.eraseDups.Nodup :=
  nodup_eraseDups_aux (l.length + 1) l (by omega)

theorem nodup_filter {l : List Nat} (h : l.Nodup) (p : Nat → Bool) : (l.filter p).Nodup :=
  List.Pairwise.filter p h

theorem mem_allIds (P : Struct V) (x : NodeId) : x ∈ allIds P ↔ (P.get? x).isSome := by
  simp only [allIds, List.mem_eraseDups, List.mem_map]
  constructor
  · rintro ⟨⟨y, n⟩, h, rfl⟩
    exact get?_isSome_of_mem h
  · intro h
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp h
    exact ⟨(x, n), mem_of_get? hn, rfl⟩

theorem inD_iff (D : Dirty) (x : NodeId) : inD D x = true ↔ ∃ d, (x, d) ∈ D := by
  simp only [inD, List.any_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨y, d⟩, h, rfl⟩; exact ⟨d, h⟩
  · rintro ⟨d, h⟩; exact ⟨(x, d), h, rfl⟩

theorem mem_of_nodup_keys {D : Dirty} (h : (D.map (·.1)).Nodup) {x : NodeId} {d d' : Nat}
    (h1 : (x, d) ∈ D) (h2 : (x, d') ∈ D) : d = d' := by
  induction D with
  | nil => simp at h1
  | cons e D ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at h
    rcases List.mem_cons.mp h1 with rfl | h1 <;> rcases List.mem_cons.mp h2 with h2e | h2
    · simp at h2e; exact h2e.symm
    · exact absurd ⟨(x, d'), h2, rfl⟩ h.1
    · rw [← h2e] at h; exact absurd ⟨(x, d), h1, rfl⟩ h.1
    · exact ih h.2 h1 h2

theorem range'_filter_gt (a n s : Nat) (h1 : a ≤ s + 1) (h2 : s + 1 ≤ a + n) :
    (List.range' a n).filter (fun j => decide (s < j)) = List.range' (s + 1) (a + n - (s + 1)) := by
  have hsplit : List.range' a n = List.range' a (s + 1 - a) ++ List.range' (s + 1) (a + n - (s + 1)) := by
    have := @List.range'_append_1 a (s + 1 - a) (n - (s + 1 - a))
    have e3 : (s + 1 - a) + (n - (s + 1 - a)) = n := by omega
    have e1 : a + (s + 1 - a) = s + 1 := by omega
    have e2 : n - (s + 1 - a) = a + n - (s + 1) := by omega
    rw [e3, e1, e2] at this
    exact this.symm
  rw [hsplit, List.filter_append]
  rw [List.filter_eq_nil_iff.mpr, List.nil_append, List.filter_eq_self.mpr]
  · intro j hj
    simp only [List.mem_range'_1] at hj
    simp; omega
  · intro j hj
    simp only [List.mem_range'_1] at hj
    simp; omega

/-! ### The startup's D after one more record -/

theorem sectionD_eq (S : Stream V T) :
    sectionD S = (sectionIdx S (lastSp S)).flatMap (fun j =>
      match S[j]? with
      | some R => R.gd.map (fun x => (x, j))
      | none => []) := rfl

theorem lastSp_append (S : Stream V T) (R : Record V T) : lastSp (S ++ [R]) = R.sp := by
  simp [lastSp]

theorem sectionD_append (S : Stream V T) (R : Record V T) (k : Nat) (hlen : S.length = k + 1)
    (hs0 : lastSp S ≤ R.sp) (hs : R.sp ≤ k) :
    sectionD (S ++ [R]) =
      (sectionD S).filter (fun e : NodeId × Nat => decide (R.sp < e.2)) ++
        R.gd.map (fun x => (x, k + 1)) := by
  have hblock : ∀ j, j ≤ k →
      (match (S ++ [R])[j]? with
        | some R => R.gd.map (fun x => (x, j))
        | none => []) =
      (match S[j]? with
        | some R => R.gd.map (fun x => (x, j))
        | none => []) := by
    intro j hj
    rw [List.getElem?_append_left (by omega)]
  -- The new section.
  rw [sectionD_eq, sectionD_eq, lastSp_append]
  simp only [sectionIdx, List.length_append, List.length_singleton]
  rw [hlen]
  have hn : k + 1 + 1 - 1 - R.sp = (k - R.sp) + 1 := by omega
  rw [hn, List.range'_concat]
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have hlast : R.sp + 1 + 1 * (k - R.sp) = k + 1 := by omega
  rw [hlast]
  have hk1 : (S ++ [R])[k + 1]? = some R := by
    rw [List.getElem?_append_right (by omega)]
    simp [hlen]
  rw [hk1]
  simp only
  congr 1
  -- The old section, filtered.
  rw [List.filter_flatMap]
  have hold : k + 1 - 1 - lastSp S = k - lastSp S := by omega
  rw [hold]
  have hfilt : ∀ j ∈ List.range' (lastSp S + 1) (k - lastSp S),
      ((match S[j]? with
        | some R => R.gd.map (fun x => (x, j))
        | none => []).filter (fun e : NodeId × Nat => decide (R.sp < e.2))) =
      (if R.sp < j then
        (match S[j]? with
          | some R => R.gd.map (fun x => (x, j))
          | none => []) else []) := by
    intro j _
    split
    · rename_i R' _
      by_cases hj : R.sp < j
      · simp only [hj, ite_true]
        apply List.filter_eq_self.mpr
        intro e he
        simp only [List.mem_map] at he
        obtain ⟨x, -, rfl⟩ := he
        simp [hj]
      · simp only [hj, ite_false]
        apply List.filter_eq_nil_iff.mpr
        intro e he
        simp only [List.mem_map] at he
        obtain ⟨x, -, rfl⟩ := he
        simp [hj]
    · simp
  rw [flatMap_congr_mem hfilt]
  have hsplit := range'_filter_gt (lastSp S + 1) (k - lastSp S) R.sp (by omega) (by omega)
  have hn2 : lastSp S + 1 + (k - lastSp S) - (R.sp + 1) = k - R.sp := by omega
  rw [hn2] at hsplit
  rw [← hsplit, flatMap_filter_ite]
  apply flatMap_congr_mem
  intro j hj
  simp only [List.mem_range'_1] at hj
  rw [hblock j (by omega)]
  by_cases h : R.sp < j <;> simp [h]

end SIS
