/-
Proofs about reclaim, part 16 (bergdb item 001, WP R5, T12 with eviction): an
invariant on the slots for the states after a restart (`NInv`). Every slot of
a canonical object names a canonical object, or a record that is its
pointee's latest version in the stream of the last startup (S0), or one
written after S0; every slot of a snapshot does so too, or names what the
snapshot's version's reference names after Rule R. The startup gives it, and
the cache operations and the transactions keep it. A read from the first
available time on then follows only versions that the state of the last
startup may read, or versions written after it.
-/
import SIS.Proof.CutPhysTrans
import SIS.Proof.EvictRestart

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## The invariant -/

/-- Record r of node y is y's latest version in S0, or a record after S0. -/
def VOK (S0 : Stream V T) (y : NodeId) (r : Nat) : Prop :=
  (S0.lv y).map (·.recNo) = some r ∨ S0.length ≤ r

/-! ## Basic facts -/

section Basic

variable {S0 : Stream V T} {m m' : Mem V}

/-- Rule R of the stream's section takes nothing to y's latest version. -/
theorem ruleRRef_none_VOK {s : Nat} {y : NodeId} {r : Nat} (h : ruleRRef S0 s y none = some r) :
    VOK S0 y r := by
  unfold ruleRRef at h
  cases hn : newest S0 s y with
  | none => rw [hn] at h; cases h
  | some w =>
    rw [hn] at h
    simp only [Option.some.injEq] at h
    subst h
    left
    rw [newest_lv hn]
    rfl

end Basic

section Stream

variable {sp : Spec V T} {db : DB V T} {k : Nat} {S0 : Stream V T}

theorem versionAt_lt_length {S : Stream V T} {r : Nat} {y : NodeId} {w : Version V}
    (h : S.versionAt r y = some w) : r < S.length := by
  obtain ⟨R, hR, -, -⟩ := versionAt_spec h
  exact (List.getElem?_eq_some_iff.mp hR).1

/-- Rule R of S0's section leaves a record that `VOK` allows as it is (S0 a
prefix of the stream of a state with the invariant). -/
theorem Inv.ruleRRef_VOK (hinv : Inv sp db k) (hpre : S0 <+: db.S) (s : Nat) {y : NodeId} {r : Nat}
    (h : VOK S0 y r) : ruleRRef S0 s y (some r) = some r := by
  unfold ruleRRef
  cases hn : newest S0 s y with
  | none => rfl
  | some u =>
    simp only
    have hlv := newest_lv hn
    have hlt : ¬ r < u.recNo := by
      intro hlt
      rcases h with h | h
      · rw [hlv, Option.map_some, Option.some.injEq] at h; omega
      · obtain ⟨r0, -, hr0⟩ := newest_some hn
        have h1 := versionAt_lt_length hr0
        have h2 := (hinv.version_node (versionAt_prefix hpre hr0)).2.1
        omega
    simp [hlt]

/-- A node's latest version in a state with S0 as a prefix of its stream: its
latest version in S0, or one after S0. -/
theorem Inv.VOK_lv (hinv : Inv sp db k) (hpre : S0 <+: db.S) {y : NodeId} {u : Version V}
    (hu : db.S.lv y = some u) : VOK S0 y u.recNo := by
  by_cases hlt : u.recNo < S0.length
  · left
    have htake : S0 = db.S.take S0.length := List.prefix_iff_eq_take.mp hpre
    have hnone : ∀ r', S0.length ≤ r' → db.S.versionAt r' y = none := by
      intro r' hr'
      obtain ⟨r0, hr0, hlast⟩ := (lv_eq_some_iff db.S y u).mp hu
      have := (hinv.version_node hr0).2.1
      exact hlast r' (by omega)
    rw [htake, lv_take hnone, hu]
    rfl
  · right; omega

end Stream

/-! ## The startup and the cache operations -/

section Startup

variable {sp : Spec V T} {al : Algo V T}

end Startup

section Cache

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}


end Cache


/-! ## The writer's walk -/

section Walk

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}


end Walk


/-! ## The change and the writes -/

section Change

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V} {c : Changes V}



end Change

/-! ## One transaction, and runs -/

section Next

variable {sp : Spec V T} {al : Algo V T} {db : DB V T} {tr : T} {S0 : Stream V T} {k : Nat}

end Next

section Run

variable {sp : Spec V T} {al : Algo V T}

end Run

end SIS
