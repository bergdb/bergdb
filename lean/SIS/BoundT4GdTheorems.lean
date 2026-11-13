/-
Self-indexed streams in Lean: bounds, part 2, T4's records with all of gd(i)
counted (bergdb item 007; 007-01, section 5.1). Trusted part: the statements.
The definitions they are about are in SIS/BoundT4Gd.lean (`RecordGdBound`),
SIS/BoundT4.lean (`RecordBound`, `changeAt`) and SIS/BoundHeight.lean
(`LiveHeightLe`); the proofs in SIS/Proof/BoundT4Gd.lean. Added 2026-11-13.
-/
import SIS.Proof.BoundT4Gd

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- T4, a record with all of its gd counted: in a run with `RunOK` and BergDB's
still-dirty test (or the exact one with a written root), every record
R(i + 1) meets `RecordBound` and `RecordGdBound`: the ids of its gd that were
not in D are distinct and on the access path of T(i + 1)'s change, and the
rest are at most |D|. -/
theorem T4_record_gd (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hst : al.stillDirty = javaTest sp ∨ (sp.virt = false ∧ al.stillDirty = exactTest sp))
    (i : Nat) (hi : i < ts.length) :
    ∃ R, (run sp al ts).S[i + 1]? = some R ∧ RecordBound sp (run sp al (ts.take i)) ts[i] R ∧
      RecordGdBound sp al ts i R := by
  obtain ⟨R, h1, h2, h3, -⟩ := recordGd_run sp al ts hok (algOK_of sp al hst) i hi
  exact ⟨R, h1, h2, h3⟩

/-- T4, "R(s) and R(k) cost at most a transaction plus the debt" (007-01, 5.1),
counted in versions and ids: with the assumptions of `T4_record_gd`, TREE after
T(i + 1) and the root's live height at most H then, the record R(i + 1) holds
T(i + 1), at most (its new data nodes) + |D| versions (`RecordBound`), and a gd
of at most

  (H + 1) (new nodes + entries of T(i + 1)) + (touched nodes of T(i + 1)) + |D|

ids, with D the debt before T(i + 1). -/
theorem T4_record_gd_height (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hst : al.stillDirty = javaTest sp ∨ (sp.virt = false ∧ al.stillDirty = exactTest sp))
    (i : Nat) (hi : i < ts.length)
    (htree : treeAt sp (run sp al (ts.take (i + 1))).P (i + 1)) (H : Nat)
    (hH : LiveHeightLe sp (run sp al (ts.take (i + 1))).P (i + 1) H root) :
    ∃ R, (run sp al ts).S[i + 1]? = some R ∧ RecordBound sp (run sp al (ts.take i)) ts[i] R ∧
      R.gd.length ≤ (H + 1) * ((changeAt sp al ts (i + 1)).new.length +
          (changeAt sp al ts (i + 1)).adds.length) + (changeAt sp al ts (i + 1)).touch.length +
        (run sp al (ts.take i)).D.length :=
  recordGd_height sp al ts hok (algOK_of sp al hst) i hi htree H hH

end SIS
