/-
The user indexes of BergDB 2026.4 in Lean: a run of the model (bergdb 020-29).

A check that the model is not empty: a database with the value 7 at key 0,
and no transaction yet, creates an index (G = 1), builds it in one step,
activates it, and a writer then puts 9 at key 0; the index has the entry 9
and, by `index_is_function`, no longer the entry 7.
-/
import BergDB.Index.Theorems

namespace BergDB.Index

/-- A spec for the example: values and levels are numbers, every key is an
object key of directory 0, and the index function gives the value itself as
its level. -/
def exSpec : Spec Nat Unit Nat where
  isObj := fun _ => true
  dirOf := fun _ => 0
  dirF := fun _ => 0
  f := fun _ _ v => v
  f_none := fun _ _ => rfl
  f_suffix := fun _ _ _ h => by cases h
  f_dir := fun _ _ _ h => absurd rfl h
  lockedAfter := 3

/-- The data at the start: 7 at key 0. -/
def exData : Nat → Option Nat := fun k => if k = 0 then some 7 else none

theorem example_run :
    ∃ s : Sys Nat Unit Nat Unit, Reach exSpec s ∧ s.st.dfn 0 = some ⟨1, (), true⟩ ∧
      s.st.data 0 = some 9 ∧ s.st.ent 0 1 0 9 ∧ ¬ s.st.ent 0 1 0 7 := by
  have r0 : Reach exSpec (Sys.init (F := Unit) (L := Nat) (W := Unit) exData) := Reach.init _
  -- the creation of the index named 0, G = max 1 0 = 1, and its maps
  have r1 := Reach.step r0 (Step.aCreate _ 0 () rfl rfl rfl)
  have r2 := Reach.step r1 (Step.aCreateMap _ 0 1 () rfl)
  -- the build: E = 0, one step of the keys below 1, its check and commit
  have r3 := Reach.step r2 (Step.bReadE _ 0 1 _ 0 rfl rfl (by
    intro k hk
    show (if k = 0 then some 7 else none) = none
    rw [ite_eq_right (by omega)]))
  have r4 := Reach.step r3 (Step.bRead _ 0 1 _ 0 1 rfl rfl rfl (by decide) (by decide))
  have r5 := Reach.step r4 (Step.bCheck _ 0 1 _ ⟨1, (), false⟩ rfl rfl (Or.inl rfl) rfl rfl)
  have r6 := Reach.step r5 (Step.bCommit _ 0 1 _ rfl rfl (by decide)
    (fun k _ _ _ => Nat.zero_le _))
  -- the activation
  have r7 := Reach.step r6 (Step.bActivate _ 0 1 _ ⟨1, (), false⟩ rfl rfl rfl rfl rfl)
  -- a writer puts 9 at key 0: R, the index set of key 0's directory, the commit
  have r8 := Reach.step r7 (Step.wStart _ () (fun k => decide (k = 0)) (fun _ => some 9) rfl)
  have r9 := Reach.step r8 (Step.wReadS _ () 0 _ _ _ _ _ rfl rfl)
  have r10 := Reach.step r9 (Step.wCommit _ () _ _ _ _ _ rfl (by
    intro k hk _
    have hk0 : k = 0 := of_decide_eq_true hk
    subst hk0
    exact ⟨_, rfl, by decide, fun _ => Nat.zero_le _⟩))
  refine ⟨_, r10, rfl, rfl, ?_, ?_⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · intro h7
    have := (index_is_function (n := 0) (d := ⟨1, (), true⟩) r10 (at_now _) rfl rfl 0 7).mp h7
    cases this

/-- A second run: the index of the first is deleted, its cleanup scans, deletes
its one entry, finds none left and deletes the marker; the name is created
again, with a new G (6, the latest time then). -/
theorem example_run2 :
    ∃ s : Sys Nat Unit Nat Unit, Reach exSpec s ∧ s.st.dfn 0 = some ⟨6, (), false⟩ ∧
      s.st.mark 0 1 = false ∧ s.m.cln 0 1 = none ∧ ∀ k l, ¬ s.st.ent 0 1 k l := by
  have r0 : Reach exSpec (Sys.init (F := Unit) (L := Nat) (W := Unit) exData) := Reach.init _
  have r1 := Reach.step r0 (Step.aCreate _ 0 () rfl rfl rfl)
  have r2 := Reach.step r1 (Step.aCreateMap _ 0 1 () rfl)
  have r3 := Reach.step r2 (Step.bReadE _ 0 1 _ 0 rfl rfl (by
    intro k hk
    show (if k = 0 then some 7 else none) = none
    rw [ite_eq_right (by omega)]))
  have r4 := Reach.step r3 (Step.bRead _ 0 1 _ 0 1 rfl rfl rfl (by decide) (by decide))
  have r5 := Reach.step r4 (Step.bCheck _ 0 1 _ ⟨1, (), false⟩ rfl rfl (Or.inl rfl) rfl rfl)
  have r6 := Reach.step r5 (Step.bCommit _ 0 1 _ rfl rfl (by decide)
    (fun k _ _ _ => Nat.zero_le _))
  have r7 := Reach.step r6 (Step.bActivate _ 0 1 _ ⟨1, (), false⟩ rfl rfl rfl rfl rfl)
  -- the deletion, its maps and its cleanup's thread
  have r8 := Reach.step r7 (Step.aDelete _ 0 ⟨1, (), true⟩ rfl rfl rfl)
  have r9 := Reach.step r8 (Step.aDeleteMap _ 0 1 rfl)
  -- the cleanup: a scan that finds the entry (7, key 0), its deletion
  have r10 := Reach.step r9 (Step.cScan _ 0 1 _ (fun k l => k = 0 ∧ l = 7) rfl rfl
    ⟨0, 7, rfl, rfl⟩ (by
      intro k l hkl
      obtain ⟨hk, hl⟩ := hkl
      subst hk; subst hl
      exact Or.inr ⟨rfl, rfl, Nat.le_refl 0, by decide, rfl⟩))
  have r11 := Reach.step r10 (Step.cDel _ 0 1 _ rfl rfl)
  -- a scan from the prefix that finds none, and the marker's deletion
  have r12 := Reach.step r11 (Step.cScanEnd _ 0 1 _ rfl rfl (by
    intro k l h
    obtain ⟨h1, h2⟩ := h
    rcases h1 with h1 | ⟨_, _, _, hk, hl⟩
    · exact h1
    · have hk0 : k = 0 := by change k < 1 at hk; omega
      subst hk0
      have hl7 : l = 7 := by
        change some 7 = some l at hl
        cases hl; rfl
      exact h2 ⟨rfl, rfl, rfl, hl7⟩))
  have r13 := Reach.step r12 (Step.cEnd _ 0 1 _ rfl rfl)
  -- the name created again: G = 6
  have r14 := Reach.step r13 (Step.aCreate _ 0 () rfl rfl rfl)
  refine ⟨_, r14, rfl, rfl, rfl, ?_⟩
  intro k l h
  obtain ⟨h1, h2⟩ := h
  rcases h1 with h1 | ⟨_, _, _, hk, hl⟩
  · exact h1
  · have hk0 : k = 0 := by change k < 1 at hk; omega
    subst hk0
    have hl7 : l = 7 := by
      change some 7 = some l at hl
      cases hl; rfl
    exact h2 ⟨rfl, rfl, rfl, hl7⟩

end BergDB.Index
