/-
Proofs for stage 2 (bergdb item 001, WP E3), part 11: after the record, the
memory has the invariant of the next state (INV-SLOT across D's changes).
-/
import SIS.Proof.EvictWrites

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

section Final

variable {sp : Spec V T} {al : Algo V T} {db : DB V T} {tr : T} {S0 : Stream V T} {k : Nat}

theorem Inv.D_le {sp : Spec V T} {db : DB V T} {k : Nat} (hinv : Inv sp db k) {x : NodeId} {d : Nat}
    (h : (x, d) ∈ db.D) : d ≤ k := by
  rw [hinv.inv1] at h
  have := (sectionD_mem h).2.1
  rw [hinv.len] at this
  omega

end Final

end SIS
