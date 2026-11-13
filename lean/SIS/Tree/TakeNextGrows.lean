/-
The writer's next id never shrinks (bergdb 024-12): `nextFromInvariant w0`
keeps w0's next id at or below the next id of every state after w0.
-/
import SIS.Tree.WriterStateInvariant

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- w0's next id is at or below w's. -/
def NextFrom (w0 : W) (_c : Ctx) (w : W) : Prop := w0.next ≤ w.next

@[instance_reducible]
def nextFromInvariant (w0 : W) : WriterStateInvariant where
  pred := NextFrom w0
  load := by
    intro x c w hw
    unfold getNode
    simp only [writerWP_bind, writerWP_get]
    split
    · simpa only [writerWP_pure] using hw
    · simp only [writerWP_bind, writerWP_read]
      split
      · split
        · exact writerWP_throw _ _ _ _
        · simp only [writerWP_bind, writerWP_set, writerWP_pure]
          exact hw
      · exact writerWP_throw _ _ _ _
  store := by
    intro x n c w hw
    simp only [putNode, writerWP_modify]
    exact hw
  create := by
    intro g h leaf ks c w hw
    unfold newKey fresh
    wpSimplify
    split <;> wpSimplify <;> (unfold NextFrom at hw ⊢; dsimp only; omega)
  value := by
    intro h c w hw
    unfold newValue fresh
    wpSimplify
    unfold NextFrom at hw ⊢; dsimp only; omega
  allocate := by
    intro c w hw
    unfold fresh
    wpSimplify
    unfold NextFrom at hw ⊢; dsimp only; omega
  trace := by
    intro s c w hw
    simp only [note, writerWP_modify]
    exact hw
  provenance := by
    intro x old c w hw
    unfold setMadeFor
    split
    · simp only [writerWP_modify]; exact hw
    · simpa only [writerWP_pure] using hw
  take := by
    intro x c w hw
    simp only [takenBack, writerWP_modify]
    exact hw
  clear := by
    intro c w hw
    simp only [pathClear, writerWP_modify]
    exact hw
  path := by
    intro cv x c w hw
    simp only [pathAdd, writerWP_modify]
    exact hw
  top := by
    intro x c w hw
    unfold newSuperRoot note fresh
    wpSimplify
    split
    · wpSimplify; exact hw
    · wpSimplify
      unfold NextFrom at hw ⊢; dsimp only; omega
  mergeCounter := by intro c w hw; exact hw
  splitCounter := by intro c w hw; exact hw

/-- A merge never shrinks the next id. -/
theorem writerWP_merge_next (x : NodeId) (d : Nat) (c : Ctx) (w : W) :
    WriterWP (merge x d) c w (fun _ w' => w.next ≤ w'.next) :=
  @state_merge (nextFromInvariant w) x d c w (Nat.le_refl _)

/-- The root collapse never shrinks the next id. -/
theorem writerWP_collapseRoot_next (key : Key) (seg fuel : Nat) (c : Ctx) (w : W) :
    WriterWP (collapseRoot key seg fuel) c w (fun _ w' => w.next ≤ w'.next) :=
  @state_collapseRoot (nextFromInvariant w) key seg fuel c w (Nat.le_refl _)

/-- A put or a delete never shrinks the next id. -/
theorem writerWP_putKv_next (op : Op) (c : Ctx) (w : W) :
    WriterWP (putKv op) c w (fun _ w' => w.next ≤ w'.next) :=
  @state_putKv (nextFromInvariant w) op c w (Nat.le_refl _)

end SIS.Tree
