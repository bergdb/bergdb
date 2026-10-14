/-
Self-indexed streams in Lean: the theorems T1 and T2.

Section numbers refer to theory/sis-model.md. Trusted part: the statements.
The proofs are in SIS/Proof/; the proofs here only connect them.
-/
import SIS.Assumptions
import SIS.Proof.Restart

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- T1 Recovery (9). After any run, startup from the stream gives an
equivalent P, the same at every time, and the same D. A crash keeps a prefix
of complete records, which is the stream of a shorter run, so this covers a
crash anywhere. -/
theorem T1_recovery (sp : Spec V T) (al : Algo V T) (ts : List T)
    (hok : RunOK sp al ts) (hex : al.stillDirty = exactTest sp) :
    Equiv sp ts.length (startup sp (run sp al ts).S).P (run sp al ts).P ∧
    (startup sp (run sp al ts).S).D = (run sp al ts).D := by
  have h := T1_strong sp al ts hok hex (k := ts.length) (Nat.le_refl _)
  rw [st_length] at h
  exact ⟨fun t _ => h.1.view t, h.2⟩

/-- T1, stronger: startup gives back every node of P, with its whole
history, not only what lookups see. -/
theorem T1_nodes (sp : Spec V T) (al : Algo V T) (ts : List T)
    (hok : RunOK sp al ts) (hex : al.stillDirty = exactTest sp) (x : NodeId) :
    (startup sp (run sp al ts).S).P.get? x = (run sp al ts).P.get? x := by
  have h := T1_strong sp al ts hok hex (k := ts.length) (Nat.le_refl _)
  rw [st_length] at h
  exact h.1 x

/-- T1 after a crash (9). A crash after T(k) keeps the first k+1 records of
the stream. Startup from them gives back the state after T(k): the same P at
every time, and the same D. -/
theorem T1_crash (sp : Spec V T) (al : Algo V T) (ts : List T)
    (hok : RunOK sp al ts) (hex : al.stillDirty = exactTest sp) (k : Nat) (hk : k ≤ ts.length) :
    Equiv sp k (startup sp ((run sp al ts).S.take (k + 1))).P (run sp al (ts.take k)).P ∧
    (startup sp ((run sp al ts).S.take (k + 1))).D = (run sp al (ts.take k)).D := by
  have hpre := st_S_prefix sp al ts (j := k) (j' := ts.length) hk (Nat.le_refl _)
  have hlen := st_len sp al ts hok hex hk
  rw [st_length] at hpre
  have htake : (run sp al ts).S.take (k + 1) = (st sp al ts k).S := by
    rw [← hlen]; exact (List.prefix_iff_eq_take.mp hpre).symm
  rw [htake]
  have h := T1_strong sp al ts hok hex hk
  exact ⟨fun t _ => h.1.view t, h.2⟩

/-- T2 Restart invariance (9). A run with restarts after any transactions
appends exactly the same records as the run without restarts. -/
theorem T2_restart (sp : Spec V T) (al : Algo V T) (ts : List (T × Bool))
    (hok : RunOK sp al (ts.map (·.1))) (hex : al.stillDirty = exactTest sp) :
    (runRestarts sp al ts).S = (run sp al (ts.map (·.1))).S := by
  have h := T2_strong sp al ts hok hex ts.length (Nat.le_refl _)
  rw [List.take_length] at h
  have hl : (ts.map (·.1)).length = ts.length := List.length_map _
  rw [← hl, st_length] at h
  exact h.1

end SIS
