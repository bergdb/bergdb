import SIS.Tree.KlongAppend
import SIS.Tree.NodeMap

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem nat_pairwise_adjacent (xs : List Nat) (hs : xs.Pairwise (· < ·)) :
    (xs.zip (xs.drop 1)).all (fun q => decide (q.1 < q.2)) = true := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    obtain ⟨ha, ht⟩ := List.pairwise_cons.mp hs
    cases xs with
    | nil => rfl
    | cons b rest =>
      simp only [List.drop_succ_cons, List.drop_zero, List.zip_cons_cons, List.all_cons,
        Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨ha b List.mem_cons_self, ih ht⟩

theorem lastBitmapFold_origin (ks : List Klong) (old : List Nat) :
    ks.foldl (fun bits k => match k with | .del more => more | _ => bits) old = old ∨
    .del (ks.foldl (fun bits k => match k with | .del more => more | _ => bits) old) ∈ ks := by
  induction ks generalizing old with
  | nil => exact Or.inl rfl
  | cons k ks ih =>
    cases k with
    | time t =>
      rcases ih old with hh | hh
      · exact Or.inl hh
      · exact Or.inr (List.mem_cons_of_mem _ hh)
    | key cv y =>
      rcases ih old with hh | hh
      · exact Or.inl hh
      · exact Or.inr (List.mem_cons_of_mem _ hh)
    | del bits =>
      rcases ih bits with hh | hh
      · apply Or.inr
        simp only [List.foldl_cons]
        rw [hh]
        exact List.mem_cons_self
      · exact Or.inr (List.mem_cons_of_mem _ hh)

theorem lastBitmapOf_pairwise (ks : List Klong) (hw : klongsWf ks = true) :
    (lastBitmapOf ks).Pairwise (· < ·) := by
  rcases lastBitmapFold_origin ks [] with he | hm
  · change lastBitmapOf ks = [] at he
    rw [he]
    exact List.Pairwise.nil
  · change .del (lastBitmapOf ks) ∈ ks at hm
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hm
    exact (klongsWf_bitmap_order ks hw i (lastBitmapOf ks) hi).2

theorem bitsUnion_length_gt_of_ne (old more : List Nat) (hs : old.Pairwise (· < ·))
    (hne : bitsUnion old more ≠ old) : old.length < (bitsUnion old more).length := by
  have hunion := bitsUnion_pairwise old more
  have hsub : old ⊆ bitsUnion old more := by
    intro a ha
    exact (mem_bitsUnion_iff old more a).mpr (Or.inl ha)
  have hex : ∃ a ∈ bitsUnion old more, a ∉ old := by
    apply Classical.byContradiction
    intro hn
    apply hne
    apply sorted_nat_lists_eq _ _ hunion hs
    intro a
    constructor
    · intro ha
      apply Classical.byContradiction
      intro hno
      exact hn ⟨a, ha, hno⟩
    · intro ha
      exact hsub ha
  obtain ⟨a, ha, hnot⟩ := hex
  have hnd : (old ++ [a]).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨hs.imp (by intro x y h; omega), by simp, ?_⟩
    intro x hx y hy he
    have hy' := List.mem_singleton.mp hy
    subst y
    subst x
    exact hnot hx
  have hh := hnd.length_le_of_subset (l₂ := bitsUnion old more) (by
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact hsub hb
    · have he := List.mem_singleton.mp hb
      subst b
      exact ha)
  simp only [List.length_append, List.length_singleton] at hh
  omega

theorem klongsWf_fold_lastBitmap (ks : List Klong) :
    (ks.zipIdx.foldl (klongsWfStep ks) (true, none, [])).2.2 = lastBitmapOf ks := by
  simpa only [klongsWfState, List.take_length] using klongsWfState_bitmap ks ks.length

/-- The exact local conditions for a new physical bitmap. All positions
and compare values are read from the existing prefix. -/
theorem klongsWf_append_bitmap (ks : List Klong) (bits : List Nat)
    (hw : klongsWf ks = true) (ht : (lastTimeOf ks).isSome = true)
    (horder : bits.Pairwise (· < ·))
    (hmono : ∀ b ∈ lastBitmapOf ks, b ∈ bits)
    (hsize : (lastBitmapOf ks).length < bits.length)
    (hbits : ∀ b ∈ bits, b < ks.length ∧ (cvAt ks b).isSome = true)
    (hclosed : ∀ b ∈ bits, b ∉ lastBitmapOf ks → ∀ cv, cvAt ks b = some cv →
      ∀ j < ks.length, cvAt ks j = some cv → j ∈ bits) :
    klongsWf (ks ++ [.del bits]) = true := by
  have hm : (lastBitmapOf ks).all (fun b => bits.contains b) = true := by
    apply List.all_eq_true.mpr
    intro b hb
    simpa using hmono b hb
  have hb : bits.all (fun b => decide (b < ks.length) && (cvAt (ks ++ [.del bits]) b).isSome) = true := by
    apply List.all_eq_true.mpr
    intro b hb
    obtain ⟨hlt, hcv⟩ := hbits b hb
    rw [cvAt_append_left ks [.del bits] b hlt]
    simp [hlt, hcv]
  have hc : (List.range ks.length).all (fun j => match cvAt (ks ++ [.del bits]) j with
      | some cv => !((bits.filter (fun b => !(lastBitmapOf ks).contains b)).filterMap
          (cvAt (ks ++ [.del bits]))).contains cv || bits.contains j
      | none => true) = true := by
    apply List.all_eq_true.mpr
    intro j hj
    have hj' := List.mem_range.mp hj
    rw [cvAt_append_left ks [.del bits] j hj']
    cases hcv : cvAt ks j with
    | none => rfl
    | some cv =>
      by_cases hnew : cv ∈ (bits.filter (fun b => !(lastBitmapOf ks).contains b)).filterMap
          (cvAt (ks ++ [.del bits]))
      · obtain ⟨b, hb, hbcv⟩ := List.mem_filterMap.mp hnew
        have hbit := (List.mem_filter.mp hb).1
        have hnot : b ∉ lastBitmapOf ks := by simpa using (List.mem_filter.mp hb).2
        rw [cvAt_append_left ks [.del bits] b (hbits b hbit).1] at hbcv
        have hh := hclosed b hbit hnot cv hbcv j hj' hcv
        simp [hh]
      · have hn : ((bits.filter (fun b => !(lastBitmapOf ks).contains b)).filterMap
            (cvAt (ks ++ [.del bits]))).contains cv = false := by
          simpa only [List.contains_eq_mem, decide_eq_false_iff_not] using hnew
        simp only [hn, Bool.not_false, Bool.true_or]
  rw [klongsWf_eq_fold, List.zipIdx_append, List.foldl_append,
    klongsWf_fold_append_source ks [.del bits] hw]
  simp only [List.zipIdx_cons, List.zipIdx_nil, List.foldl_cons, List.foldl_nil,
    klongsWfStep, Nat.zero_add]
  rw [← klongsWf_eq_fold, hw, klongsWf_fold_lastTime, klongsWf_fold_lastBitmap]
  have hs := nat_pairwise_adjacent bits horder
  simp only [ht, hm, show decide ((lastBitmapOf ks).length < bits.length) = true by simp [hsize],
    hs, hb, Bool.and_self]
  exact hc

/-- Appending the union with every physical occurrence of the requested
compare value preserves klong well-formedness whenever it changes the bitmap. -/
theorem KNode.append_delete_wf (n : KNode) (cv : Nat) (hw : klongsWf n.ks = true)
    (ht : n.lastTime.isSome = true)
    (hne : bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap) :
    klongsWf (n.ks ++ [.del (bitsUnion n.lastBitmap (n.bitsOf cv))]) = true := by
  apply klongsWf_append_bitmap n.ks _ hw ht
  · exact bitsUnion_pairwise _ _
  · intro b hb
    exact (mem_bitsUnion_iff _ _ _).mpr (Or.inl hb)
  · exact bitsUnion_length_gt_of_ne _ _ (lastBitmapOf_pairwise n.ks hw) hne
  · intro b hb
    rcases (mem_bitsUnion_iff _ _ _).mp hb with hb | hb
    · change b ∈ lastBitmapOf n.ks at hb
      have hh := bitmapRules_bounds n.ks (klongsWf_bitmapRules n.ks hw) n.ks.length
        (Nat.le_refl _) b (by simpa only [List.take_length] using hb)
      exact hh
    · obtain ⟨y, hy⟩ := (n.mem_bitsOf_iff cv b).mp hb
      have hk := List.mem_zipIdx_iff_getElem?.mp hy
      exact ⟨(List.getElem?_eq_some_iff.mp hk).1,
        by simp only [cvAt, hk, Option.isSome_some]⟩
  · intro b hb hnot a hcv j hj hjcv
    have hbit : b ∈ n.bitsOf cv := by
      rcases (mem_bitsUnion_iff _ _ _).mp hb with hb | hb
      · exact (hnot hb).elim
      · exact hb
    obtain ⟨y, hy⟩ := (n.mem_bitsOf_iff cv b).mp hbit
    have hbcv : cvAt n.ks b = some cv :=
      (cvAt_eq_some_iff n.ks b cv).mpr ⟨y, List.mem_zipIdx_iff_getElem?.mp hy⟩
    have hac : a = cv := Option.some.inj (hcv.symm.trans hbcv)
    subst a
    obtain ⟨z, hz⟩ := (cvAt_eq_some_iff n.ks j cv).mp hjcv
    apply (mem_bitsUnion_iff _ _ _).mpr
    exact Or.inr ((n.mem_bitsOf_iff cv j).mpr ⟨z, List.mem_zipIdx_iff_getElem?.mpr hz⟩)

end SIS.Tree
