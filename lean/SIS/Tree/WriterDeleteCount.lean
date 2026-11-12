import SIS.Tree.MergeProtectedDelete
import SIS.Tree.DeleteCount

namespace SIS.Tree

open SIS SIS.Check

def CountChangeOne (before after : Nat) : Prop := after ≤ before ∧ before ≤ after+1

theorem countChangeOne_of_exact (before after : Nat) (present : Prop) [Decidable present]
    (h : after + (if present then 1 else 0) = before) : CountChangeOne before after := by
  unfold CountChangeOne
  split at h <;> omega

/-- In a current-transaction node with room, the actual delete writer keeps
its id and height and decreases live count by at most one. Both bitmap modes
and both dead-compaction routes are included. -/
theorem writerWP_appendDeleteKlong_new_room_count (b : NodeGuard)
    (depth cv : Nat) (c : Ctx) (w : W)
    (hw : GuardHeld b w) (ht : b.node.firstTime = some c.i)
    (hroom : b.node.size+1 < c.p.M) :
    WriterWP (appendDeleteKlong b.id depth cv) c w (fun _ v =>
      ∃ after, GuardHeld {b with node := after} v ∧ CountChangeOne b.node.cnt after.cnt) := by
  have hold : CountChangeOne b.node.cnt b.node.cnt := by unfold CountChangeOne; omega
  have hadd := countChangeOne_of_exact _ _ _ (b.node.add_delete_count_exact c.i cv)
  have hset := fun old hl => countChangeOne_of_exact _ _ _
    (b.node.setAt_delete_count_exact cv old hl)
  have hcompact : CountChangeOne b.node.cnt
      (b.node.lastVersionGivenDel c.i (bitsUnion b.node.lastBitmap (b.node.bitsOf cv))).cnt :=
    b.node.delete_count_bounds c.i cv
  unfold appendDeleteKlong
  simp only [writerWP_bind,writerWP_read]
  rw [writerWP_getNode_known b.id b.node c w hw.1]
  repeat' first
    | wpSimplify
    | simp only [note,hroom,↓reduceIte]
    | (with_unfolding_none guard_target = WriterWP (handleFull _ _ _ true) _ _ _
       unfold handleFull
       refine writerWP_mono (writerWP_handleFullWith_compact_new_same b _ _ _ _ _ (by kgState) ht) ?_
       intro _ _ hv)
    | (with_unfolding_none guard_target = WriterWP (putNode _ _) _ _ _
       refine writerWP_mono (writerWP_putNode_guard_same b _ _ _ (by kgState)) ?_
       intro _ _ hv)
    | (exact ⟨b.node,by kgState,hold⟩)
    | (exact ⟨_,by kgState,hadd⟩)
    | (exact ⟨_,by kgState,hset _ (by assumption)⟩)
    | (refine ⟨_,?_,hcompact⟩; simpa only [KNode.lastVersionGivenDel] using hv)
    | exact writerWP_throw _ _ _ _
    | split

theorem writerWP_appendDeleteKlong_new_room_fill (b : NodeGuard)
    (depth cv : Nat) (c : Ctx) (w : W)
    (hw : GuardHeld b w) (ht : b.node.firstTime = some c.i)
    (hroom : b.node.size+1 < c.p.M) (hfill : c.p.mergeBelow+1 ≤ b.node.cnt) :
    WriterWP (appendDeleteKlong b.id depth cv) c w (fun _ v =>
      ∃ after, GuardHeld {b with node := after} v ∧ c.p.mergeBelow ≤ after.cnt) := by
  refine writerWP_mono
    (writerWP_appendDeleteKlong_new_room_count b depth cv c w hw ht hroom) ?_
  rintro _ v ⟨after,hguard,hcount⟩
  exact ⟨after,hguard,by have := hcount.2; omega⟩

end SIS.Tree
