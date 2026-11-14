/-
The upward delete with each chain node's fate and the stop node's node exactly
(bergdb 024-12, TP4; for the take-back's (C)): `ChainFateW` for the chain below
the stop node, and the stop node's node as its node, retargeted from the chain's
top if the transaction made that (`RetFormS`, `RetFrom`), then the bitmap
(`BitmapOf`) or LE-b (`lebNode`).
-/
import SIS.Tree.TakeDeadUp

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A chain node after the upward delete in the writer's state: taken back if the
transaction made it, else not taken and unlinked from its node, perhaps
retargeted. -/
def ChainFateW (t : Time) (B : NodeId) (v : W) (n : KNode) (x : NodeId) : Prop :=
  (n.firstTime = some t → v.taken.contains x = true) ∧
  (n.firstTime ≠ some t → v.taken.contains x = false ∧
    ∃ S, RetFormS t B n S ∧ v.nodes.lookup x = some (unlinkedNode S t))

theorem chainFateW_frame (t : Time) (B : NodeId) (v v' : W) (n : KNode) (x : NodeId)
    (h : ChainFateW t B v n x) (ht : v'.taken = v.taken) (hl : v'.nodes.lookup x = v.nodes.lookup x) :
    ChainFateW t B v' n x := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun hf => by rw [ht]; exact h1 hf, fun hf => ?_⟩
  obtain ⟨h3, S, hS, hl0⟩ := h2 hf
  exact ⟨by rw [ht]; exact h3, S, hS, by rw [hl]; exact hl0⟩

end SIS.Tree
