/-
`OpDelChkOK` implies `OpDelChk2OK` (bergdb 024-22, step 4): the copy without
`checkPathFree` succeeds wherever the copy with it does, with the same result
and state, as the check only reads.
-/
import SIS.Tree.HeightsPathFree

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- Every successful run of f is one of g. -/
def Refines {α : Type} (f g : M α) : Prop := ∀ c w x, f c w = .ok x → g c w = .ok x

theorem Refines.refl {α : Type} (f : M α) : Refines f f := fun _ _ _ h => h

/-- A successful bind: both parts succeed. -/
theorem m_bind_ok {α β : Type} (f : M α) (g : α → M β) (c : Ctx) (w : W) (x : β × W) :
    (f >>= g) c w = .ok x ↔ ∃ a w', f c w = .ok (a, w') ∧ g a c w' = .ok x := by
  simp only [bind, ReaderT.bind, StateT.bind]
  cases hf : f c w with
  | error e => simp [Except.bind]
  | ok aw =>
    rcases aw with ⟨a0, w0⟩
    simp only [Except.bind]
    constructor
    · intro h; exact ⟨a0, w0, rfl, h⟩
    · rintro ⟨a, w', h1, h2⟩
      cases h1
      exact h2

/-- Refinement goes through a bind. -/
theorem Refines.bind {α β : Type} {f f' : M α} {g g' : α → M β} (hf : Refines f f')
    (hg : ∀ a, Refines (g a) (g' a)) : Refines (f >>= g) (f' >>= g') := by
  intro c w x h
  obtain ⟨a, w', h1, h2⟩ := (m_bind_ok f g c w x).mp h
  exact (m_bind_ok f' g' c w x).mpr ⟨a, w', hf c w _ h1, hg a c w' x h2⟩

/-- Refinement goes through an if. -/
theorem Refines.ite {β : Type} {b : Prop} [Decidable b] {f f' g g' : M β} (h1 : b → Refines f f')
    (h2 : ¬ b → Refines g g') : Refines (if b then f else g) (if b then f' else g') := by
  by_cases hb : b
  · simp only [hb, ↓reduceIte]; exact h1 hb
  · simp only [hb, ↓reduceIte]; exact h2 hb

end SIS.Tree
