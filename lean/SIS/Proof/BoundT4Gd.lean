/-
Proofs for T4's records with all of gd(i) counted (bergdb item 007;
SIS/BoundT4Gd.lean). Added 2026-11-13.

gd(i) is step 3's nodes (not in D, distinct, on the access path of the change,
`onAccessPath_gd3`) followed by step 7's (taken, so in D, at most |D|).
-/
import SIS.BoundT4Gd
import SIS.Proof.BoundHeight

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

theorem recordGd_run (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hst : AlgOK sp al) (i : Nat) (hi : i < ts.length) :
    ∃ R, (run sp al ts).S[i + 1]? = some R ∧ RecordBound sp (run sp al (ts.take i)) ts[i] R ∧
      RecordGdBound sp al ts i R ∧
      (R.gd.filter (fun x => !inD (run sp al (ts.take i)).D x)) =
        (parts sp al (st sp al ts i) ts[i]).gd3 := by
  have hlen : (st sp al ts i).S.length = i + 1 := by
    rw [st, run_length, List.length_take]; omega
  let R := (parts sp al (st sp al ts i) ts[i]).R
  obtain ⟨R', hR', hb⟩ := recordByDebt_step sp al (st sp al ts i) ts[i] hlen
  have hRR : R' = R := by
    have h2 : (step sp al (st sp al ts i) ts[i]).S = (st sp al ts i).S ++ [R] := rfl
    rw [hR'] at h2
    simpa using h2
  subst hRR
  have hgd : R.gd = (parts sp al (st sp al ts i) ts[i]).gd3 ++
      (parts sp al (st sp al ts i) ts[i]).r7.2 := rfl
  have hsub : (parts sp al (st sp al ts i) ts[i]).r7.2.Sublist
      (parts sp al (st sp al ts i) ts[i]).taken := by
    obtain ⟨M, hM, h⟩ := stillDirtyOf_shape al (parts sp al (st sp al ts i) ts[i]).S'
      (parts sp al (st sp al ts i) ts[i]).P (parts sp al (st sp al ts i) ts[i]).D2
      (st sp al ts i).S.length (parts sp al (st sp al ts i) ts[i]).taken
    rw [← parts_r7] at h
    rw [h]; exact hM
  have hr7D : ∀ x ∈ (parts sp al (st sp al ts i) ts[i]).r7.2, inD (st sp al ts i).D x = true :=
    fun x hx => step_taken_of sp al (st sp al ts i) ts[i] hlen (hsub.subset hx)
  have hfilt : R.gd.filter (fun x => !inD (run sp al (ts.take i)).D x) =
      (parts sp al (st sp al ts i) ts[i]).gd3 := by
    rw [hgd, List.filter_append]
    have h1 : (parts sp al (st sp al ts i) ts[i]).gd3.filter
        (fun x => !inD (run sp al (ts.take i)).D x) = (parts sp al (st sp al ts i) ts[i]).gd3 := by
      rw [List.filter_eq_self]
      intro x hx
      have := step_gd3_not_inD sp al (st sp al ts i) ts[i] hx
      simp only [st] at this
      simp [this]
    have h2 : (parts sp al (st sp al ts i) ts[i]).r7.2.filter
        (fun x => !inD (run sp al (ts.take i)).D x) = [] := by
      rw [List.filter_eq_nil_iff]
      intro x hx
      have := hr7D x hx
      simp only [st] at this
      simp [this]
    rw [h1, h2, List.append_nil]
  have hpre := st_S_prefix sp al ts (j := i + 1) (j' := ts.length) (by omega) (Nat.le_refl _)
  rw [st_length, st_succ sp al ts hi, hR'] at hpre
  obtain ⟨L, hL⟩ := hpre
  refine ⟨R, ?_, hb, ⟨?_, ?_, ?_⟩, hfilt⟩
  · rw [← hL, List.getElem?_append_left (by simp; omega), List.getElem?_append_right (by omega), hlen]
    simp
  · show (R.gd.filter (fun x => !inD (run sp al (ts.take i)).D x)).Nodup
    rw [hfilt]; exact step_gd3_nodup sp al _ _
  · intro x hx
    rw [hgd] at hx
    rcases List.mem_append.mp hx with h | h
    · exact Or.inr (onAccessPath_gd3 hok hst hi h)
    · exact Or.inl (by simpa [st] using hr7D x h)
  · show R.gd.length ≤ (R.gd.filter (fun x => !inD (run sp al (ts.take i)).D x)).length +
      (run sp al (ts.take i)).D.length
    rw [hfilt, hgd, List.length_append]
    have := hsub.length_le
    have := step_taken_length sp al (st sp al ts i) ts[i] hlen
    simp only [st] at *
    omega

/-- With TREE after T(i + 1) and the root's live height at most H then, the
record's gd has at most (H + 1) (new nodes + entries) + touched nodes of
T(i + 1), plus |D| ids. -/
theorem recordGd_height (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hst : AlgOK sp al) (i : Nat) (hi : i < ts.length)
    (htree : treeAt sp (run sp al (ts.take (i + 1))).P (i + 1)) (H : Nat)
    (hH : LiveHeightLe sp (run sp al (ts.take (i + 1))).P (i + 1) H root) :
    ∃ R, (run sp al ts).S[i + 1]? = some R ∧ RecordBound sp (run sp al (ts.take i)) ts[i] R ∧
      R.gd.length ≤ (H + 1) * ((changeAt sp al ts (i + 1)).new.length +
          (changeAt sp al ts (i + 1)).adds.length) + (changeAt sp al ts (i + 1)).touch.length +
        (run sp al (ts.take i)).D.length := by
  obtain ⟨R, hR, hb, ⟨hnd, hacc, hlen⟩, hfilt⟩ := recordGd_run sp al ts hok hst i hi
  refine ⟨R, hR, hb, ?_⟩
  have hinv := inv_st sp al ts hok hst (i + 1) (by omega)
  obtain ⟨nr, hnr⟩ := Option.isSome_iff_exists.mp hinv.rootIn
  have hc := accessPath_count_height hok hst hi (by simpa [st] using htree) hnr
    (by simpa [st] using hH)
    (R.gd.filter (fun x => !inD (run sp al (ts.take i)).D x)) hnd (by
      intro x hx
      obtain ⟨hxg, hxn⟩ := List.mem_filter.mp hx
      rcases hacc x hxg with h | h
      · rw [h] at hxn; cases hxn
      · exact h)
  rw [changeAt_succ i hi]
  exact Nat.le_trans hlen (by omega)

end SIS
