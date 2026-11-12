import SIS.Tree.KlongShape
import SIS.Tree.WriterDeleteCount

namespace SIS.Tree

open SIS SIS.Check

/-- The successful time-split insertion loop only adds live compare values
or changes their pointers. It leaves the writer state unchanged. -/
theorem writerWP_replaceOrAdd_count (last : KNode) (ins : List (Nat × NodeId))
    (c : Ctx) (w : W) :
    WriterWP (replaceOrAdd last ins) c w (fun out v =>
      out.leaf = last.leaf ∧ last.cnt ≤ out.cnt ∧ v = w) := by
  unfold replaceOrAdd
  simp only [writerWP_bind,writerWP_read]
  induction ins generalizing last with
  | nil => simp [writerWP_pure]
  | cons q ins ih =>
    rcases q with ⟨cv,y⟩
    rw [List.foldlM_cons,writerWP_bind]
    cases hr : replaceKlong last.ks c.i cv y with
    | error e => exact writerWP_throw e c w _
    | ok result =>
      cases result with
      | none =>
        simp only [writerWP_pure]
        refine writerWP_mono (ih (last.add c.i (.key cv y))) ?_
        rintro out v ⟨hleaf,hcnt,rfl⟩
        refine ⟨?_,Nat.le_trans (last.add_key_cnt_ge c.i cv y) hcnt,rfl⟩
        simpa only [KNode.add_leaf] using hleaf
      | some ks =>
        simp only [writerWP_pure]
        have hcnt : ({last with ks := ks} : KNode).cnt = last.cnt :=
          KNode.cnt_eq_of_shape _ _ (replaceKlong_shape last.ks c.i cv y ks hr)
        refine writerWP_mono (ih {last with ks := ks}) ?_
        rintro out v ⟨hleaf,hcount,rfl⟩
        exact ⟨hleaf,by rwa [hcnt] at hcount,rfl⟩

/-- A time replacement of a guarded current-transaction node preserves its
id and height and never lowers the normalized input's live count. -/
theorem writerWP_handleFullWith_time_new_count (b : NodeGuard)
    (up : NodeId → List (Nat × NodeId) → M Unit) (depth : Nat)
    (ins : List (Nat × NodeId)) (last : KNode) (compact : Bool)
    (c : Ctx) (w : W) (hw : GuardHeld b w) (ht : b.node.firstTime = some c.i)
    (htime : compact = true ∨ last.size ≤ c.p.splitAbove) :
    WriterWP (handleFullWith up depth b.id ins last compact) c w (fun _ v =>
      ∃ after, GuardHeld {b with node := after} v ∧ last.cnt ≤ after.cnt) := by
  have hflag : (!compact && decide (last.size > c.p.splitAbove)) = false := by
    rcases htime with hc | hs
    · simp [hc]
    · simp [show ¬ last.size > c.p.splitAbove from by omega]
  unfold handleFullWith
  simp only [writerWP_bind,writerWP_read]
  rw [writerWP_getNode_known b.id b.node c w hw.1]
  refine writerWP_mono (guard_ghOf b b.id c w hw) ?_
  intro gh v hv
  simp only [ht,BEq.rfl]
  unfold parentAt pathNode
  repeat' first
    | wpSimplify
    | simp only [hflag,Bool.false_eq_true,Bool.not_true,note,↓reduceIte]
    | kgUse b using (guard_getNode b _)
    | (with_unfolding_none guard_target = WriterWP (replaceOrAdd _ _) _ _ _
       refine writerWP_mono (writerWP_replaceOrAdd_count _ _ _ _) ?_
       rintro out v ⟨hleaf,hcount,rfl⟩)
    | (with_unfolding_none guard_target = WriterWP (putNode _ _) _ _ _
       refine writerWP_mono (writerWP_putNode_guard_same b _ _ _ (by kgState)) ?_
       intro _ _ hguard)
    | (refine ⟨{out with leaf := b.node.leaf},hguard,?_⟩
       simpa only [KNode.cnt_with_leaf] using hcount)
    | exact writerWP_throw _ _ _ _
    | split

end SIS.Tree
