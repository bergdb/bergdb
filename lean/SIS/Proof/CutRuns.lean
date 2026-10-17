/-
Proofs about reclaim, part 12 (bergdb item 001, WP R5): T12. A run that
restarts from safe cut streams stays related to the run without restarts
(`CutRel`): the same records but those before the largest cut so far, the
same D, the run's nodes for the lookups from the first available time of the
last restart on and for D.
-/
import SIS.Proof.CutRestart
import SIS.Proof.CutHistRead

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- A structure agrees with itself. -/
theorem Inv.cutAgree_refl {sp : Spec V T} {db : DB V T} {k : Nat} (hinv : Inv sp db k) (f : Time) :
    CutAgree sp f k db.P db.P where
  rootP := hinv.rootIn
  rootP' := hinv.rootIn
  rootLive := by
    intro _ n n' hn hn'
    rw [hn, Option.some.injEq] at hn'
    subst hn'
    exact ⟨rfl, fun _ _ _ => rfl⟩
  nodes := fun _ _ _ _ _ _ => rfl
  ids := fun _ h => h
  times' := hinv.times
  rootVals' := by
    intro hv n hn e he
    obtain ⟨z, m, -, hval⟩ := (hinv.vr hv).rootEntry n hn e he
    exact ⟨z, hval⟩

theorem cutMax_append_one (cs : List (Option Nat)) (c : Option Nat) :
    cutMax (cs ++ [c]) = max (cutMax cs) (c.getD 0) := by
  simp [cutMax, List.foldl_append]

section Run

variable (sp : Spec V T) (al : Algo V T)

/-- T12's induction: after each prefix, the run with restarts from cut streams
is related to the run without restarts, with the largest cut so far. A
transaction keeps the relation (`step_congr_cut`); a restart from the stream
cut at c is a startup from the run's stream cut at the larger of c and the
cuts before, safe by assumption, so T8 with D's nodes gives the relation
(`recoverCut_dNodes`). -/
theorem restartCut_rel (cs : List (T × Option Nat)) (hok : RunOK sp al (cs.map (·.1)))
    (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) (hex : ExecRootOK sp)
    (hvl : VirtLiveOK sp) (hpol : PolicyCutOK al)
    (hcut : ∀ j (h : j < cs.length) c, cs[j].2 = some c →
      CutOK sp (cutMax ((cs.take (j + 1)).map (·.2))) (run sp al ((cs.map (·.1)).take (j + 1)))
        (j + 1)) :
    ∀ j ≤ cs.length, ∃ f, CutRel sp (cutMax ((cs.take j).map (·.2))) f j
      (runRestartsCut sp al (cs.take j)) (st sp al (cs.map (·.1)) j) := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  intro j
  induction j with
  | zero =>
    intro _
    refine ⟨0, ?_⟩
    rw [st_zero]
    exact ⟨(cutStream_zero _).symm, rfl, (inv_init sp hok.1).cutAgree_refl 0, fun _ _ => rfl,
      Nat.le_refl _, Nat.zero_le _⟩
  | succ j ih =>
    intro hjl
    obtain ⟨f, hrel⟩ := ih (by omega)
    have hjl' : j < (cs.map (·.1)).length := by simp; omega
    have hinv := inv_st sp al (cs.map (·.1)) hok hst j (by omega)
    have htr : (cs.map (·.1))[j] = cs[j].1 := by simp
    have hstep : StepOK sp (st sp al (cs.map (·.1)) j).P (j + 1)
        (sp.exec cs[j].1 (j + 1) (view sp (st sp al (cs.map (·.1)) j).P j)) := by
      have h1 := hok.2 j hjl'
      rw [htr] at h1
      exact h1
    obtain ⟨-, -, -, -, -, -, hrel1⟩ := step_congr_cut sp al hok.1 hinv hj hmk hex hvl hpol hrel
      (st_fa_le sp al _ (by omega)) cs[j].1 hstep
    have hst1 : st sp al (cs.map (·.1)) (j + 1) = step sp al (st sp al (cs.map (·.1)) j) cs[j].1 := by
      rw [st_succ sp al _ hjl', htr]
    rw [← hst1] at hrel1
    have htake : cs.take (j + 1) = cs.take j ++ [cs[j]] := by
      rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some]
    have hrun : runRestartsCut sp al (cs.take (j + 1)) =
        (match cs[j].2 with
         | some c => startup sp (cutStream c (step sp al (runRestartsCut sp al (cs.take j)) cs[j].1).S)
         | none => step sp al (runRestartsCut sp al (cs.take j)) cs[j].1) := by
      rw [htake]
      unfold runRestartsCut
      rw [List.foldl_append]
      rfl
    have hcm : cutMax ((cs.take (j + 1)).map (·.2)) =
        max (cutMax ((cs.take j).map (·.2))) (cs[j].2.getD 0) := by
      rw [htake, List.map_append, List.map_singleton, cutMax_append_one]
    have hcut1 := hcut j (by omega)
    rw [hrun, hcm]
    cases hc : cs[j].2 with
    | none =>
      simp only [Option.getD_none, Nat.max_zero]
      exact ⟨f, hrel1⟩
    | some c =>
      simp only [Option.getD_some]
      have hk1 : j + 1 ≤ (cs.map (·.1)).length := by omega
      have hcut2 : CutOK sp (max (cutMax ((cs.take j).map (·.2))) c) (st sp al (cs.map (·.1)) (j + 1))
          (j + 1) := by
        have := hcut1 c hc
        rw [hcm, hc] at this
        exact this
      have hS : cutStream c (step sp al (runRestartsCut sp al (cs.take j)) cs[j].1).S =
          cutStream (max (cutMax ((cs.take j).map (·.2))) c) (st sp al (cs.map (·.1)) (j + 1)).S := by
        rw [hrel1.stream, cutStream_cutStream, Nat.max_comm]
      rw [hS]
      obtain ⟨hag, hdn⟩ := recoverCut_dNodes sp al (cs.map (·.1)) hok hj hmk hk1 hex hvl hcut2
      obtain ⟨-, hD⟩ := recoverCut sp al (cs.map (·.1)) hok hst hk1 hex hvl hcut2
      exact ⟨lastFa (st sp al (cs.map (·.1)) (j + 1)).S, rfl, hD, hag, hdn, hcut2.1, Nat.le_refl _⟩

/-- T12: after all of the run, the stream is the run's cut at the largest cut,
D is the run's, and so are the lookups from the run's first available time
on. -/
theorem restartCut (cs : List (T × Option Nat)) (hok : RunOK sp al (cs.map (·.1)))
    (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) (hex : ExecRootOK sp)
    (hvl : VirtLiveOK sp) (hpol : PolicyCutOK al)
    (hcut : ∀ j (h : j < cs.length) c, cs[j].2 = some c →
      CutOK sp (cutMax ((cs.take (j + 1)).map (·.2))) (run sp al ((cs.map (·.1)).take (j + 1)))
        (j + 1)) :
    (runRestartsCut sp al cs).S = cutStream (cutMax (cs.map (·.2))) (run sp al (cs.map (·.1))).S ∧
      (runRestartsCut sp al cs).D = (run sp al (cs.map (·.1))).D ∧
      SameFrom sp (lastFa (run sp al (cs.map (·.1))).S) cs.length (runRestartsCut sp al cs).P
        (run sp al (cs.map (·.1))).P := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  obtain ⟨f, hrel⟩ := restartCut_rel sp al cs hok hj hmk hex hvl hpol hcut cs.length (Nat.le_refl _)
  have hn : (cs.map (·.1)).take cs.length = cs.map (·.1) := List.take_of_length_le (by simp)
  have hst' : st sp al (cs.map (·.1)) cs.length = run sp al (cs.map (·.1)) := by
    show run sp al ((cs.map (·.1)).take cs.length) = _
    rw [hn]
  have hinv := inv_st sp al (cs.map (·.1)) hok hst cs.length (by simp)
  rw [List.take_length] at hrel
  rw [hst'] at hrel hinv
  refine ⟨hrel.stream, hrel.dirty, ?_⟩
  have hsf := hrel.agree.sameFrom hok.1.liveSub hinv.ptrs
  intro t h1 h2
  exact hsf t (Nat.le_trans hrel.fa h1) h2

end Run

end SIS
