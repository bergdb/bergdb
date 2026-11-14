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

theorem Refines.bind_same {α β : Type} (f : M α) {g g' : α → M β}
    (hg : ∀ a, Refines (g a) (g' a)) : Refines (f >>= g) (f >>= g') :=
  Refines.bind (Refines.refl f) hg

/-- A passed `checkPathFree` changes nothing. -/
theorem Refines.drop_check {β : Type} (n : Nat) (g : Unit → M β) :
    Refines (checkPathFree n >>= g) (g ()) := by
  intro c w x h
  obtain ⟨a, w', h1, h2⟩ := (m_bind_ok _ g c w x).mp h
  have := writerWP_checkPathFree n c w a w' h1
  rw [this.1] at h2
  exact h2

/-- Refinement goes through an if. -/
theorem Refines.ite {β : Type} {b : Prop} [Decidable b] {f f' g g' : M β} (h1 : b → Refines f f')
    (h2 : ¬ b → Refines g g') : Refines (if b then f else g) (if b then f' else g') := by
  by_cases hb : b
  · simp only [hb, ↓reduceIte]; exact h1 hb
  · simp only [hb, ↓reduceIte]; exact h2 hb

set_option maxHeartbeats 3200000 in
/-- The upward delete: the copies agree up to the check, which reads only. -/
theorem refines_deleteUpward (leaf : NodeId) (depth cv : Nat) (key : Key) :
    Refines (deleteUpwardChk leaf depth cv key) (deleteUpwardChk2 leaf depth cv key) := by
  unfold deleteUpwardChk deleteUpwardChk2
  refine Refines.bind_same _ (fun c => ?_)
  refine Refines.bind_same _ (fun n => ?_)
  refine Refines.ite (fun _ => Refines.refl _) (fun _ => ?_)
  refine Refines.ite (fun _ => Refines.refl _) (fun _ => ?_)
  refine Refines.bind_same _ (fun stop => ?_)
  refine Refines.ite (fun _ => Refines.refl _) (fun _ => ?_)
  refine Refines.bind_same _ (fun _ => ?_)
  refine Refines.bind_same _ (fun w0 => ?_)
  refine Refines.bind_same _ (fun _ => ?_)
  refine Refines.bind_same _ (fun r => ?_)
  exact Refines.drop_check _ _

/-- The last segment of a delete. -/
theorem refines_setValueDel (segRoot : NodeId) (cv : Nat) (key : Key) :
    Refines (setValueDelChk segRoot cv key) (setValueDelChk2 segRoot cv key) := by
  unfold setValueDelChk setValueDelChk2
  refine Refines.bind_same _ (fun c => ?_)
  refine Refines.bind_same _ (fun leaf => ?_)
  refine Refines.bind_same _ (fun n => ?_)
  refine Refines.bind (refines_deleteUpward _ _ _ _) (fun noop => Refines.refl _)

/-- The segments of a delete's key. -/
theorem refines_putSegsDel (key : Key) : ∀ (segs : List Nat) (r : NodeId),
    Refines (putSegsDelChk key segs r) (putSegsDelChk2 key segs r) := by
  intro segs
  induction segs with
  | nil => intro r; unfold putSegsDelChk putSegsDelChk2; exact Refines.refl _
  | cons cv rest ih =>
    intro r
    cases rest with
    | nil => unfold putSegsDelChk putSegsDelChk2; exact refines_setValueDel r cv key
    | cons d rest' =>
      unfold putSegsDelChk putSegsDelChk2
      refine Refines.bind_same _ (fun res => ?_)
      cases res with
      | none => exact Refines.refl _
      | some next => exact ih next

/-- A delete. -/
theorem refines_putKvDel (key : Key) : Refines (putKvDelChk key) (putKvDelChk2 key) := by
  unfold putKvDelChk putKvDelChk2
  refine Refines.bind_same _ (fun _ => ?_)
  refine Refines.bind_same _ (fun root => ?_)
  exact refines_putSegsDel key key root

/-- `OpDelChkOK` implies `OpDelChk2OK`: the second asks less. -/
theorem opDelChk2OK_of_chk (p : Params) (h : OpDelChkOK p) : OpDelChk2OK p := by
  intro ts tx hw z top hz htop pre key post hsplit r w hpre r' v he
  exact refines_putKvDel key _ _ _ (h ts tx hw z top hz htop pre key post hsplit r w hpre r' v he)

end SIS.Tree
