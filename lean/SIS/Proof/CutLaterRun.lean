/-
Proofs about reclaim, part 22 (bergdb item 001, WP R5, T12 with eviction): the
run with eviction that restarts from cut streams (`runEvictCut`, C) appends
the records of the run that restarts from cut streams without eviction
(`runRestartsCut`). C is compared with the run with eviction that restarts
from the whole streams at the same points (`runEvict`, E), whose cache
operations are C's with extra unswizzles of its root's slots before each
release (`esOf`).
-/
import SIS.Proof.CutLaterStart

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## E's schedule -/

section Defs

variable (sp : Spec V T) (al : Algo V T)

/-- The number of transactions before the last restart among the first j (0 if
none). -/
def lastR {C : Type} (cs : List (T × Option Nat × C)) : Nat → Nat
  | 0 => 0
  | i + 1 => if ((cs[i]?).bind (·.2.1)).isSome then i + 1 else lastR cs i

/-- The restarts of C's schedule, for `runRestartsCut`. -/
def logOf {C : Type} (cs : List (T × Option Nat × C)) : List (T × Option Nat) := cs.map (fun p => (p.1, p.2.1))

end Defs

/-! ## Facts about the schedules -/

section Facts

variable {sp : Spec V T} {al : Algo V T}

theorem lastR_le {C : Type} (cs : List (T × Option Nat × C)) : ∀ j, lastR cs j ≤ j := by
  intro j
  induction j with
  | zero => exact Nat.le_refl _
  | succ j ih => unfold lastR; split <;> omega

theorem lastR_succ_none {C : Type} (cs : List (T × Option Nat × C)) {j : Nat} (hj : j < cs.length)
    (h : cs[j].2.1 = none) : lastR cs (j + 1) = lastR cs j := by
  show (if ((cs[j]?).bind (·.2.1)).isSome then j + 1 else lastR cs j) = lastR cs j
  rw [List.getElem?_eq_getElem hj]
  simp [h]

theorem lastR_succ_some {C : Type} (cs : List (T × Option Nat × C)) {j : Nat} (hj : j < cs.length) {c : Nat}
    (h : cs[j].2.1 = some c) : lastR cs (j + 1) = j + 1 := by
  show (if ((cs[j]?).bind (·.2.1)).isSome then j + 1 else lastR cs j) = j + 1
  rw [List.getElem?_eq_getElem hj]
  simp [h]

theorem cutMax_take_succ {C : Type} (cs : List (T × Option Nat × C)) {j : Nat} (hj : j < cs.length) :
    cutMax ((cs.take (j + 1)).map (·.2.1)) = max (cutMax ((cs.take j).map (·.2.1))) (cs[j].2.1.getD 0) := by
  have h1 : cs.take (j + 1) = cs.take j ++ [cs[j]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj]; rfl
  rw [h1, List.map_append, List.map_singleton, cutMax_append_one]

theorem runRestartsCut_succ {C : Type} (cs : List (T × Option Nat × C)) {j : Nat} (hj : j < cs.length) :
    runRestartsCut sp al ((logOf cs).take (j + 1)) =
      (match cs[j].2.1 with
       | some c => startup sp (cutStream c (step sp al (runRestartsCut sp al ((logOf cs).take j)) cs[j].1).S)
       | none => step sp al (runRestartsCut sp al ((logOf cs).take j)) cs[j].1) := by
  have hj' : j < (logOf cs).length := by simp [logOf]; exact hj
  have h1 : (logOf cs).take (j + 1) = (logOf cs).take j ++ [(cs[j].1, cs[j].2.1)] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj']
    simp [logOf]
  unfold runRestartsCut
  rw [h1, List.foldl_append]
  rfl

theorem st_fa_mono {ts : List T} (hok : RunOK sp al ts) (hj : al.stillDirty = javaTest sp) :
    ∀ {j1 j : Nat}, j1 ≤ j → j ≤ ts.length → lastFa (st sp al ts j1).S ≤ lastFa (st sp al ts j).S := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  intro j1 j h1 hj'
  induction j with
  | zero =>
    have : j1 = 0 := by omega
    subst this; exact Nat.le_refl _
  | succ j ih =>
    rcases Nat.lt_or_ge j j1 with hlt | hge
    · have : j1 = j + 1 := by omega
      subst this; exact Nat.le_refl _
    · refine Nat.le_trans (ih hge (by omega)) ?_
      have hinv := inv_st sp al ts hok hst j (by omega)
      have hfs := st_fa_le sp al ts (k := j) (by omega)
      rw [st_succ sp al ts (by omega), step_eq_parts]
      simp only [lastFa, List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.map_some,
        Option.getD_some]
      rw [parts_R]
      simp only [parts_fa, firstAvail, parts_s, startupPos]
      rw [hinv.len]
      simp only [Nat.add_sub_cancel]
      unfold lastFa at hfs ⊢
      have hsk : lastSp (st sp al ts j).S ≤ j := by have := hinv.spLt; omega
      omega

end Facts

/-! ## The relation of the two runs -/

section RunProof

variable {sp : Spec V T} {al : Algo V T}

theorem logOf_fst {C : Type} (cs : List (T × Option Nat × C)) : (logOf cs).map (·.1) = cs.map (·.1) := by
  simp [logOf]

theorem logOf_snd {C : Type} (cs : List (T × Option Nat × C)) : (logOf cs).map (·.2) = cs.map (·.2.1) := by
  simp [logOf]

end RunProof

end SIS
