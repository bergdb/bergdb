/-
The writer's code of the merge (bergdb 024-22, `OpTreeOK`): `mergeParent` with
room for its klongs and no compaction writes `mergeParentNode` at the parent
and changes nothing else (`writerWP_mergeParent_room`).
-/
import SIS.Tree.WriterTreeMergeLive

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem writerWP_ite_true {α : Type} (b : Prop) [Decidable b] (h : b) (x y : M α) (c : Ctx) (w : W)
    (post : α → W → Prop) (hx : WriterWP x c w post) : WriterWP (if b then x else y) c w post := by
  simp only [h, ↓reduceIte]; exact hx

theorem writerWP_ite_false {α : Type} (b : Prop) [Decidable b] (h : ¬ b) (x y : M α) (c : Ctx)
    (w : W) (post : α → W → Prop) (hy : WriterWP y c w post) :
    WriterWP (if b then x else y) c w post := by
  simp only [h, ↓reduceIte]; exact hy

/-- `newKey` makes the node at the next id. -/
theorem writerWP_newKey_frame (g h : Nat) (leaf : Bool) (ks : List Klong) (c : Ctx) (w : W) :
    WriterWP (newKey g h leaf ks) c w (fun x w' => x = w.next ∧
      w'.nodes = w.nodes ++ [(w.next, ⟨leaf, ks⟩)] ∧ w'.taken = w.taken ∧ w'.top = w.top ∧
      w'.next = w.next + 2 ∧ w'.vals = w.vals ∧ w'.path = w.path ∧ w'.madeFor = w.madeFor) := by
  unfold newKey fresh
  simp only [writerWP_bind, writerWP_read, writerWP_get, writerWP_set]
  split <;>
  · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial

theorem writerWP_setMadeFor_frame (m : NodeId) (o : Option NodeId) (c : Ctx) (w : W) :
    WriterWP (setMadeFor m o) c w (fun _ w' => w'.nodes = w.nodes ∧ w'.taken = w.taken ∧
      w'.top = w.top ∧ w'.next = w.next ∧ w'.vals = w.vals ∧ w'.path = w.path) := by
  unfold setMadeFor
  split
  · simp only [writerWP_modify]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial
  · simp only [writerWP_pure]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial

/-- `getNode` changes at most the lookup of the node it reads. -/
theorem writerWP_getNode_frame (x : NodeId) (c : Ctx) (w : W) :
    WriterWP (getNode x) c w (fun _ w' => w'.taken = w.taken ∧ w'.top = w.top ∧
      w'.next = w.next ∧ w'.vals = w.vals ∧ w'.path = w.path ∧ w'.madeFor = w.madeFor ∧
      ∀ y, y ≠ x → w'.nodes.lookup y = w.nodes.lookup y) := by
  unfold getNode
  simp only [writerWP_bind, writerWP_get]
  split
  · simp only [writerWP_pure]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun _ _ => ?_⟩ <;> first | rfl | trivial
  · simp only [writerWP_bind, writerWP_read]
    split
    · split
      · exact writerWP_throw _ _ _ _
      · simp only [writerWP_bind, writerWP_set, writerWP_pure]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun y hy => ?_⟩
        any_goals first | rfl | trivial
        simp only [List.lookup_append]
        cases h : w.nodes.lookup y with
        | some _ => rfl
        | none =>
          show (none : Option KNode).or ([(x, _)].lookup y) = none
          rw [lookup_cons_ne _ _ _ _ hy]; rfl
    · exact writerWP_throw _ _ _ _

/-- `unlink` changes at most the lookup of its node. -/
theorem writerWP_unlink_frame (o : NodeId) (c : Ctx) (w : W) :
    WriterWP (unlink o) c w (fun _ w' => w'.taken = w.taken ∧ w'.top = w.top ∧
      w'.next = w.next ∧ ∀ y, y ≠ o → w'.nodes.lookup y = w.nodes.lookup y) := by
  unfold unlink
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (writerWP_getNode_frame o c w) ?_
  intro n w1 ⟨h1t, h1top, h1n, _, _, _, h1l⟩
  split
  · simp only [putNode, writerWP_modify]
    refine ⟨h1t, h1top, h1n, fun y hy => ?_⟩
    simp only [lookup_upsert, hy, ↓reduceIte]
    exact h1l y hy
  · simp only [writerWP_pure]
    exact ⟨h1t, h1top, h1n, h1l⟩

end SIS.Tree
