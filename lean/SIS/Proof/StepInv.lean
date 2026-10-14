/-
Proofs, part 12: the invariant holds after every transaction of a run.
-/
import SIS.Proof.StepD

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

theorem inv_step (sp : Spec V T) (al : Algo V T) (hex : al.stillDirty = exactTest sp)
    (hok : SpecOK sp) {db : DB V T} {k : Nat} (hinv : Inv sp db k) (tr : T)
    (hstep : StepOK sp db.P (k + 1) (sp.exec tr (k + 1) (view sp db.P k))) :
    Inv sp (step sp al db tr) (k + 1) := by
  have hc : (parts sp al db tr).c = sp.exec tr (k + 1) (view sp db.P k) := by
    rw [parts_c, hinv.len]; rfl
  rw [← hc] at hstep
  have hpf := step_pfacts sp al db tr hok hinv hstep
  rw [step_eq_parts]
  exact {
    len := step_Snew_len sp al db tr hinv
    recNo := step_recNo sp al db tr hinv
    versNodup := step_versNodup sp al db tr hinv hstep
    spLt := by
      left
      show lastSp (Snew sp al db tr) < k + 1
      rw [step_lastSp]
      have := step_s_le sp al db tr hinv.len
      omega
    vh := step_vh sp al db tr hok hinv hstep
    ref := step_ref sp al db tr hinv
    top := step_top sp al db tr
    times := hpf.times
    ptrs := hpf.ptrs
    data := hpf.data
    er := hpf.er
    rootIn := hpf.rootIn
    born := hpf.born
    inv1 := step_D_eq sp al db tr hex hinv
    dNodup := step_dNodup sp al db tr hex hinv
    dIndex := step_dIndex sp al db tr hex hinv
    inv2 := step_inv2 sp al db tr hex hinv hstep
    inv3 := step_inv3 sp al db tr hex hok hinv hstep
    inv4 := step_inv4 sp al db tr hex hok hinv hstep
    dataV := step_dataV sp al db tr hinv hstep }

/-- The invariant holds after every prefix of a run. -/
theorem inv_st (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hex : al.stillDirty = exactTest sp) : ∀ j ≤ ts.length, Inv sp (st sp al ts j) j := by
  intro j
  induction j with
  | zero => intro _; rw [st_zero]; exact inv_init sp hok.1
  | succ j ih =>
    intro hj
    rw [st_succ sp al ts (by omega)]
    apply inv_step sp al hex hok.1 (ih (by omega))
    have := hok.2 j (by omega)
    simpa [st] using this

end SIS
