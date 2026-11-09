/-
The user indexes of BergDB 2026.4 in Lean: a run of the model (bergdb 020-29).

A check that the model is not empty: a database with the value 7 at key 0
creates an index, builds it in one step, activates it, and a writer then puts
9 at key 0; the index has the entry 9 and, by `index_is_function`, no longer
the entry 7.
-/
import BergDB.Index.Theorems

namespace BergDB.Index

/-- A spec for the example: values and levels are numbers, every key is an
object key, and the index function gives the value itself as its level. -/
def exSpec : Spec Nat Unit Nat where
  isObj := fun _ => true
  f := fun _ _ v => v
  f_none := fun _ _ => rfl
  f_suffix := fun _ _ _ h => by cases h
  lockedAfter := 3

/-- The data at the start: 7 at key 0. -/
def exData : Nat → Option Nat := fun k => if k = 0 then some 7 else none

theorem example_run :
    ∃ s : Sys Nat Unit Nat Unit, Reach exSpec s ∧ s.st.dfn = some ⟨0, (), true⟩ ∧
      s.st.data 0 = some 9 ∧ s.st.ent 0 0 9 ∧ ¬ s.st.ent 0 0 7 := by
  have r0 : Reach exSpec (Sys.init (F := Unit) (L := Nat) (W := Unit) exData) := Reach.init _
  -- the creation, G = 0, and its maps
  have r1 := Reach.step r0 (Step.aCreate _ () rfl rfl rfl)
  have r2 := Reach.step r1 (Step.aCreateMap _ 0 () rfl)
  -- the build: E = 0, one step of the keys below 1, its check and commit
  have r3 := Reach.step r2 (Step.bReadE _ 0 _ 0 rfl rfl (by
    intro k hk
    show (if k = 0 then some 7 else none) = none
    rw [ite_eq_right (by omega)]))
  have r4 := Reach.step r3 (Step.bRead _ 0 _ 0 1 rfl rfl rfl (by decide) (by decide))
  have r5 := Reach.step r4 (Step.bCheck _ 0 _ ⟨0, (), false⟩ rfl rfl (Or.inl rfl) rfl rfl)
  have r6 := Reach.step r5 (Step.bCommit _ 0 _ rfl rfl (by decide)
    (fun k _ _ _ => Nat.zero_le _))
  -- the activation
  have r7 := Reach.step r6 (Step.bActivate _ 0 _ ⟨0, (), false⟩ rfl rfl rfl rfl rfl)
  -- a writer puts 9 at key 0
  have r8 := Reach.step r7 (Step.wStart _ () (fun k => decide (k = 0)) (fun _ => some 9) rfl)
  have r9 := Reach.step r8 (Step.wReadS _ () _ _ _ _ rfl rfl)
  have r10 := Reach.step r9 (Step.wCommit _ () _ _ _ _ _ rfl (by decide)
    (fun _ _ _ => Nat.zero_le _))
  refine ⟨_, r10, rfl, rfl, ?_, ?_⟩
  · exact Or.inr ⟨rfl, rfl, rfl⟩
  · intro h7
    have := (index_is_function r10 (at_now _) rfl rfl 0 7).mp h7
    cases this

end BergDB.Index
