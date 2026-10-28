/-
Proofs for stage 2 (bergdb item 001, WP E3), part 2: the physical writer's loop
writes the model's versions (`Mem.writeNodes` against `writeAll`), given, for
each node it writes, its canonical object with the node's whole history; the
positions of the canonical objects at the latest versions so far; and slots that
serialize the latest versions of the pointees that are not pinned.
-/
import SIS.Proof.EvictLogic
import SIS.Proof.PhysMem
import SIS.Proof.VRead

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- The node table names objects of their node. -/
def TableNode (m : Mem V) : Prop :=
  ∀ y h, m.tableOf y = some h → ∃ o, m.obj? h = some o ∧ o.node = y

/-- A memory slot for y names an object of node y. -/
def SlotsNode (m : Mem V) : Prop :=
  ∀ h o, m.obj? h = some o → ∀ y h', o.slot? y = some (Slot.mem h') →
    ∃ o', m.obj? h' = some o' ∧ o'.node = y

theorem lookup_map_val {β : Type} (g : NodeId → β → β) :
    ∀ (l : List (NodeId × β)) (y : NodeId),
      (l.map (fun q => (q.1, g q.1 q.2))).lookup y = (l.lookup y).map (g y)
  | [], _ => rfl
  | (a, b) :: l, y => by
    simp only [List.map_cons, List.lookup_cons]
    by_cases hya : y = a
    · subst hya; simp
    · have : (y == a) = false := by simp [hya]
      simp only [this]
      exact lookup_map_val g l y

section

variable (sp : Spec V T) (S0 S : Stream V T) (P : Struct V) (D : Dirty) (i : Nat)

end

end SIS
