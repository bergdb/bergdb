/-
Proofs, part 12: the invariant holds after every transaction of a run.
-/
import SIS.Proof.VStep

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

theorem inv_step (sp : Spec V T) (al : Algo V T) (hst : StillOK sp al)
    (hvj : sp.virt = true → al.stillDirty = javaTest sp)
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
    inv1 := step_D_eq sp al db tr hinv
    dNodup := step_dNodup sp al db tr hinv
    dIndex := step_dIndex sp al db tr hinv
    inv2 := step_inv2 sp al db tr hst hok hinv hstep
    inv3 := step_inv3 sp al db tr hok hinv hstep
    inv4 := step_inv4 sp al db tr hok hinv hstep
    dataV := step_dataV sp al db tr hinv hstep
    vr := fun hv => step_vinv sp al db tr hok hinv hstep hv (hvj hv) }

/-- What the proofs need of the algorithm: a still-dirty test with what
`StillOK` says, and, with a virtual root, BergDB's test, which also looks at the
dead pointers between root children (`VInv.fresh`). -/
structure AlgOK (sp : Spec V T) (al : Algo V T) : Prop where
  still : StillOK sp al
  virtJava : sp.virt = true → al.stillDirty = javaTest sp

/-- The algorithms the theorems are stated for: BergDB's still-dirty test, or,
without a virtual root, the exact one. -/
theorem algOK_of (sp : Spec V T) (al : Algo V T)
    (h : al.stillDirty = javaTest sp ∨ (sp.virt = false ∧ al.stillDirty = exactTest sp)) :
    AlgOK sp al where
  still := by
    rcases h with h | ⟨-, h⟩
    · exact java_stillOK sp al h
    · exact exact_stillOK sp al h
  virtJava := by
    intro hv
    rcases h with h | ⟨h1, -⟩
    · exact h
    · rw [hv] at h1; simp at h1

/-- The invariant holds after every prefix of a run. -/
theorem inv_st (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hst : AlgOK sp al) : ∀ j ≤ ts.length, Inv sp (st sp al ts j) j := by
  intro j
  induction j with
  | zero => intro _; rw [st_zero]; exact inv_init sp hok.1
  | succ j ih =>
    intro hj
    rw [st_succ sp al ts (by omega)]
    apply inv_step sp al hst.still hst.virtJava hok.1 (ih (by omega))
    have := hok.2 j (by omega)
    simpa [st] using this

end SIS
