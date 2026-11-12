/-
Self-indexed streams in Lean: the theorems T1 and T2.

Section numbers refer to sis-model.md (bergdb 027-01). Trusted part: the statements.
The proofs are in SIS/Proof/; the proofs here only connect them.
-/
import SIS.Assumptions
import SIS.Proof.Restart

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! The theorems hold for both ways of step 3 (testing, or marking with
`Algo.mark`), with a written root or a virtual one (`Spec.virt`), and for
BergDB's still-dirty test of step 7 (`javaTest`, Rule A over all pointers).
With a written root they also hold for the exact test (`exactTest`, the
definition of dirty); with a virtual root they need BergDB's, which keeps the
references between root children fresh. F1-008-11, WPs E1 to E3. -/

/-- T1 Recovery (9). After any run, startup from the stream gives an
equivalent P, the same at every time, and the same D. A crash keeps a prefix
of complete records, which is the stream of a shorter run, so this covers a
crash anywhere. -/
theorem T1_recovery (sp : Spec V T) (al : Algo V T) (ts : List T)
    (hok : RunOK sp al ts) (hst : al.stillDirty = javaTest sp ∨ (sp.virt = false ∧ al.stillDirty = exactTest sp)) :
    Equiv sp ts.length (startup sp (run sp al ts).S).P (run sp al ts).P ∧
    (startup sp (run sp al ts).S).D = (run sp al ts).D := by
  have h := T1_strong sp al ts hok (algOK_of sp al hst) (k := ts.length) (Nat.le_refl _)
  rw [st_length] at h
  exact ⟨fun t _ => h.1.view t, h.2⟩

/-- T1, stronger: startup gives back every node of P, with its whole
history, not only what lookups see. -/
theorem T1_nodes (sp : Spec V T) (al : Algo V T) (ts : List T)
    (hok : RunOK sp al ts) (hst : al.stillDirty = javaTest sp ∨ (sp.virt = false ∧ al.stillDirty = exactTest sp)) (x : NodeId) :
    (startup sp (run sp al ts).S).P.get? x = (run sp al ts).P.get? x := by
  have h := T1_strong sp al ts hok (algOK_of sp al hst) (k := ts.length) (Nat.le_refl _)
  rw [st_length] at h
  exact h.1 x

/-- T1 after a crash (9). A crash after T(k) keeps the first k+1 records of
the stream. Startup from them gives back the state after T(k): the same P at
every time, and the same D. -/
theorem T1_crash (sp : Spec V T) (al : Algo V T) (ts : List T)
    (hok : RunOK sp al ts) (hst : al.stillDirty = javaTest sp ∨ (sp.virt = false ∧ al.stillDirty = exactTest sp)) (k : Nat) (hk : k ≤ ts.length) :
    Equiv sp k (startup sp ((run sp al ts).S.take (k + 1))).P (run sp al (ts.take k)).P ∧
    (startup sp ((run sp al ts).S.take (k + 1))).D = (run sp al (ts.take k)).D := by
  have hpre := st_S_prefix sp al ts (j := k) (j' := ts.length) hk (Nat.le_refl _)
  have hlen := st_len sp al ts hok (algOK_of sp al hst) hk
  rw [st_length] at hpre
  have htake : (run sp al ts).S.take (k + 1) = (st sp al ts k).S := by
    rw [← hlen]; exact (List.prefix_iff_eq_take.mp hpre).symm
  rw [htake]
  have h := T1_strong sp al ts hok (algOK_of sp al hst) hk
  exact ⟨fun t _ => h.1.view t, h.2⟩

/-- T2 Restart invariance (9). A run with restarts after any transactions
appends exactly the same records as the run without restarts. -/
theorem T2_restart (sp : Spec V T) (al : Algo V T) (ts : List (T × Bool))
    (hok : RunOK sp al (ts.map (·.1))) (hst : al.stillDirty = javaTest sp ∨ (sp.virt = false ∧ al.stillDirty = exactTest sp)) :
    (runRestarts sp al ts).S = (run sp al (ts.map (·.1))).S := by
  have h := T2_strong sp al ts hok (algOK_of sp al hst) ts.length (Nat.le_refl _)
  rw [List.take_length] at h
  have hl : (ts.map (·.1)).length = ts.length := List.length_map _
  rw [← hl, st_length] at h
  exact h.1

/-- T13, marking is exact (F1-008-11, WP E1). In every transaction of a run,
an index node that is not in D, and not a virtual root, is on the access path of the change (it is
reachable now, and a node created or given an entry by the transaction is
reachable from it now) exactly when it is dirty. So step 3 may mark the access
path instead of testing every node (`Algo.mark`, BergDB's way), and T1 and T2
above hold for both: their proofs use this theorem when `al.mark` is true. -/
theorem T13_markExact (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hst : al.stillDirty = javaTest sp ∨ (sp.virt = false ∧ al.stillDirty = exactTest sp)) (j : Nat) (hj : j < ts.length) (x : NodeId) :
    let db := run sp al (ts.take j)
    let c := sp.exec ts[j] (j + 1) (view sp db.P j)
    let P := db.P.apply (j + 1) c
    let vs0 := writeAll sp db.S (j + 1) P ((c.new.filter (·.isData)).map (·.id)) []
    isIndex P x = true → inD db.D x = false → written sp x = true →
      marked sp P c (j + 1) x = dirty sp (db.S.building vs0) P (j + 1) x := by
  intro db c P vs0 hx hD hw
  have hinv : Inv sp db j := inv_st sp al ts hok (algOK_of sp al hst) j (by omega)
  have hlen := hinv.len
  have hc : (parts sp al db ts[j]).c = c := by rw [parts_c, hlen]; rfl
  have hP : (parts sp al db ts[j]).P = P := by rw [parts_P, hc, hlen]
  have hvs0 : (parts sp al db ts[j]).vs0 = vs0 := by rw [parts_vs0, hP, hc, hlen]
  have hstep : StepOK sp db.P (j + 1) (parts sp al db ts[j]).c := by
    rw [hc]; have := hok.2 j hj; simpa [st] using this
  have h := step_marked_iff sp al db ts[j] hok.1 hinv hstep (x := x) (by rw [hP]; exact hx) hD hw
  rw [hP, hc, hvs0] at h
  exact h

end SIS
