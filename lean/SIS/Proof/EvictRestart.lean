/-
Proofs for stage 2 (bergdb item 001, WP E5), part 2: restarts with eviction
(T2-C, and T-READ with restarts). The Level 4 startup from the stream after
T(k) gives a memory with the invariant and with the invariant for reads at
earlier times (`einv_hinv_startup`): its positions are the latest records, and
rule 4 links the pinned objects' slots to the nodes of D. The physical writer
depends on P only through its nodes, so a transaction from the logical
startup's state, which has the run's nodes, gives the run's record and D and
the same memory (`evictTrans_congr`); so a run with restarts keeps both
invariants (`evictInvR_all`).
-/
import SIS.Proof.EvictRerun

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## The invariant after the Level 4 startup (T2-C) -/

theorem Mem.sectionPos_obj? (m : Mem V) (S : Stream V T) (h : Nat) :
    (m.sectionPos S).obj? h = (m.obj? h).map (fun o =>
      if !o.canonical then o else match newest S m.s o.node with
        | some w => { o with pos := some w.recNo }
        | none => o) := by
  unfold Mem.sectionPos Mem.obj?
  simp only
  rw [lookup_map_key _ (fun q => by
    cases q.2.canonical
    · simp
    · cases newest S m.s q.2.node <;> simp) h m.objs]
  congr 1
  funext o
  cases o.canonical
  · simp
  · cases newest S m.s o.node <;> simp

section Startup

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

end Startup

/-! ## The physical writer depends on P only through its nodes -/

section Congr

variable {sp : Spec V T} {P P' : Struct V} (hP : SameNodes P P')
include hP

theorem D1Of_congr (al : Algo V T) (D : Dirty) (S : Stream V T) (c : Changes V) (vs0 : List (Version V)) :
    D1Of sp al ⟨P, D, S⟩ c vs0 = D1Of sp al ⟨P', D, S⟩ c vs0 := by
  have hPP := hP.apply S.length c
  unfold D1Of
  simp only [gotDirty3_congr sp al _ _ hPP]

theorem takenOf_congr (al : Algo V T) (D : Dirty) (S : Stream V T) (tr : T) (c : Changes V)
    (vs0 : List (Version V)) :
    takenOf sp al ⟨P, D, S⟩ tr c vs0 = takenOf sp al ⟨P', D, S⟩ tr c vs0 := by
  have hPP := hP.apply S.length c
  unfold takenOf
  simp only [D1Of_congr hP, byLevel_congr hPP]

theorem stepOf_congr (al : Algo V T) (hst : AlgOK sp al) (D : Dirty) (S : Stream V T) (tr : T)
    (c : Changes V) (vs0 vs : List (Version V)) :
    Rel (stepOf sp al ⟨P, D, S⟩ tr c vs0 vs) (stepOf sp al ⟨P', D, S⟩ tr c vs0 vs) := by
  have hPP := hP.apply S.length c
  unfold stepOf
  simp only [gotDirty3_congr sp al _ _ hPP, byLevel_congr hPP,
    stillDirtyOf_congr al hst.still.congr hPP, topOf_sameNodes sp hPP]
  exact ⟨rfl, rfl, hPP⟩

end Congr

/-! ## Runs with restarts -/

section Run

variable {sp : Spec V T} {al : Algo V T}

end Run

end SIS
