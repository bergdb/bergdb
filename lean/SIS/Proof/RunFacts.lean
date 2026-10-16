/-
Proofs, part 13: how the states of a run relate to each other.
-/
import SIS.Proof.StepInv

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

section Run

variable (sp : Spec V T) (al : Algo V T) (ts : List T)

theorem st_len (hok : RunOK sp al ts) (hst : AlgOK sp al) {j : Nat}
    (hj : j ≤ ts.length) : (st sp al ts j).S.length = j + 1 :=
  (inv_st sp al ts hok hst j hj).len

theorem st_P_succ (hok : RunOK sp al ts) (hst : AlgOK sp al) {j : Nat}
    (hj : j < ts.length) :
    (st sp al ts (j + 1)).P =
      (st sp al ts j).P.apply (j + 1) (sp.exec ts[j] (j + 1) (view sp (st sp al ts j).P j)) := by
  rw [st_succ sp al ts hj, step_eq_parts]
  simp only
  rw [parts_P, parts_c, st_len sp al ts hok hst (by omega)]
  rfl

theorem st_S_succ {j : Nat} (hj : j < ts.length) :
    (st sp al ts (j + 1)).S = (st sp al ts j).S ++ [(parts sp al (st sp al ts j) ts[j]).R] := by
  rw [st_succ sp al ts hj, step_eq_parts]

theorem st_S_prefix : ∀ {j j' : Nat}, j ≤ j' → j' ≤ ts.length →
    (st sp al ts j).S <+: (st sp al ts j').S := by
  intro j j' hjj' hj'
  induction j' with
  | zero =>
    have : j = 0 := by omega
    subst this; exact List.prefix_refl _
  | succ j' ih =>
    rcases Nat.lt_or_ge j (j' + 1) with h | h
    · rw [st_S_succ sp al ts (by omega)]
      exact (ih (by omega) (by omega)).trans (List.prefix_append _ _)
    · have : j = j' + 1 := by omega
      subst this; exact List.prefix_refl _

theorem st_grow (hok : RunOK sp al ts) (hst : AlgOK sp al) :
    ∀ {j j' : Nat}, j ≤ j' → j' ≤ ts.length → Grow (st sp al ts j).P j (st sp al ts j').P := by
  intro j j' hjj' hj'
  induction j' with
  | zero =>
    have : j = 0 := by omega
    subst this; exact Grow.refl _ _
  | succ j' ih =>
    rcases Nat.lt_or_ge j (j' + 1) with h | h
    · have h1 := ih (by omega) (by omega)
      have hinv := inv_st sp al ts hok hst j' (by omega)
      have h2 : Grow (st sp al ts j').P j' (st sp al ts (j' + 1)).P := by
        rw [st_succ sp al ts (by omega)]
        exact step_grow sp al _ _ hinv.len
      exact h1.trans h2 (by omega)
    · have : j = j' + 1 := by omega
      subst this; exact Grow.refl _ _

/-- Record j of a later state holds transaction T(j). -/
theorem st_trans (hok : RunOK sp al ts) (hst : AlgOK sp al) {j k : Nat}
    (hj : 1 ≤ j) (hjk : j ≤ k) (hk : k ≤ ts.length) :
    ((st sp al ts k).S[j]?).bind (·.trans) = some ts[j - 1] := by
  have hpre := st_S_prefix sp al ts (j := j) (j' := k) hjk hk
  have hlen := st_len sp al ts hok hst (j := j) (by omega)
  obtain ⟨l, hl⟩ := hpre
  rw [← hl, List.getElem?_append_left (by omega)]
  have hj1 : j - 1 + 1 = j := by omega
  have hS := st_S_succ sp al ts (j := j - 1) (by omega)
  rw [hj1] at hS
  rw [hS]
  have hlen' := st_len sp al ts hok hst (j := j - 1) (by omega)
  rw [hj1] at hlen'
  rw [List.getElem?_append_right (by omega)]
  rw [hlen']
  simp [parts_R]

end Run

end SIS
