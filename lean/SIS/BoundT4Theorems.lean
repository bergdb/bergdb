/-
Self-indexed streams in Lean: bounds, part 2, the theorem T4 (bergdb item 007;
007-01, sections 5.1 and 6; 027-01, sis-model.md section 10).

Trusted part: the statements. The definitions they are about are in
SIS/BoundT4.lean (`RecordBound`, `RecordByDebt`, `DebtByChanges`), the proofs
in SIS/Proof/BoundT4.lean and SIS/Proof/BoundT4Debt.lean; the proofs here only
connect them. Added 2026-11-13.
-/
import SIS.Proof.BoundT4Debt

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- T4, the record of one transaction (007-01, 5.1): on any database with a
stream, which every state of a run and every startup has, the record that a
transaction appends holds the transaction, versions of the data nodes it
creates and of nodes of D before it, at most (its data nodes) + |D| of them,
and at most |D| nodes of D in its gd. Nothing else is assumed: not A1 to A5,
nor anything of the policy or the still-dirty test. -/
theorem T4_record (sp : Spec V T) (al : Algo V T) (db : DB V T) (tr : T) (hS : db.S ≠ []) :
    RecordByDebt sp al db tr := by
  obtain ⟨k, hk⟩ : ∃ k, db.S.length = k + 1 :=
    ⟨db.S.length - 1, by have := List.length_pos_iff.mpr hS; omega⟩
  exact recordByDebt_step sp al db tr hk

/-- T4, the records of a run: every record R(i + 1), 0 ≤ i < k, that the run
appends is bounded by the debt before T(i + 1) (`RecordBound`). Nothing else is
assumed. -/
theorem T4_records (sp : Spec V T) (al : Algo V T) (ts : List T) (i : Nat) (hi : i < ts.length) :
    ∃ R, (run sp al ts).S[i + 1]? = some R ∧ RecordBound sp (run sp al (ts.take i)) ts[i] R :=
  recordBound_run sp al ts i hi

/-- T4, the records at the ends of the startup section (007-01, 5.1: "So R(s)
and R(k) cost at most a transaction plus the debt"): after the run ts, with S
its stream, k = ts.length and s = s(k) its startup pos, R(s) (if s ≥ 1) and
R(k) (if k ≥ 1) are bounded by the debt before their transactions
(`RecordBound`). R(0) holds the initial structure. Nothing else is assumed. -/
theorem T4_ends (sp : Spec V T) (al : Algo V T) (ts : List T) :
    let S := (run sp al ts).S
    ∀ i (hi : i < ts.length), (i + 1 = lastSp S ∨ i + 1 = ts.length) →
      ∃ R, S[i + 1]? = some R ∧ RecordBound sp (run sp al (ts.take i)) ts[i] R :=
  fun i hi _ => recordBound_run sp al ts i hi

/-- T4, the debt of D (007-01, section 6), with the exact still-dirty test and
a written root: after a run that meets the assumptions (`RunOK`), every node
of D is on the access path of the change of a transaction (reachable then
with a node created or given an entry by it below, or touched by it) of the
last lev(x) + 1 startup sections, where lev(x) is the node's level
(`DebtByChanges`). -/
theorem T4_debt (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hex : al.stillDirty = exactTest sp) (hv : sp.virt = false) : DebtByChanges sp al ts :=
  debtByChanges_exact sp al ts hok hex hv

end SIS
