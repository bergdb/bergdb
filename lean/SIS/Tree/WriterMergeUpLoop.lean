/-
The merges' loop at the writer's level (bergdb 024-22): `mergeUp` keeps any
invariant that its descent, its node reads and the merge keep.
-/
import SIS.Tree.WriterGetCollapseLoop
import SIS.Tree.WriterTreeMergeFull

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- `afterDelete` keeps any invariant that `mergeUp` and `collapseRoot` keep. -/
theorem writerWP_afterDelete_inv (key : Key) (g h : Nat) (c : Ctx) (Inv : W → Prop)
    (hmu : ∀ v, Inv v → WriterWP (mergeUp key g c.p.fuel h false) c v (fun _ v' => Inv v'))
    (hcr : ∀ v, Inv v → WriterWP (collapseRoot key g c.p.fuel) c v (fun _ v' => Inv v')) :
    ∀ v, Inv v → WriterWP (afterDelete key g h) c v (fun _ v' => Inv v') := by
  intro v hI
  unfold afterDelete
  simp only [writerWP_bind, writerWP_read]
  split
  · rw [writerWP_bind]
    refine writerWP_mono (hmu v hI) ?_
    intro merged v1 hI1
    split
    · exact hcr v1 hI1
    · simp only [writerWP_pure]; exact hI1
  · simp only [writerWP_pure]; exact hI

/-- `descendLte` reads as before. -/
theorem writerWP_descendLte_readsU (cv : Nat) (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base) :
    ∀ (f : Nat) (x : NodeId) (w : W), WriterWP (descendLte cv f x) c w (fun _ v => ReadsAs c.p base w v) := by
  intro f
  induction f with
  | zero => intro x w; exact writerWP_throw _ _ _ _
  | succ f ih =>
    intro x w
    unfold descendLte
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_mono (writerWP_getNode_reads x c w base hvc) ?_
    intro n v ⟨hrv, _, _⟩
    split
    · simp only [writerWP_pure]; exact hrv
    · split
      · exact writerWP_throw _ _ _ _
      · rename_i fd _
        simp only [writerWP_bind]
        refine writerWP_mono (writerWP_pathAdd_reads (some fd.c) fd.y c v base) ?_
        intro _ v1 hr1
        exact writerWP_mono (ih fd.y v1) (fun _ v2 hr2 =>
          ReadsAs.trans _ _ _ _ _ hrv (ReadsAs.trans _ _ _ _ _ hr1 hr2))

/-- `descendHeight` reads as before. -/
theorem writerWP_descendHeight_readsU (cv h : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) :
    ∀ (f : Nat) (x : NodeId) (w : W), WriterWP (descendHeight cv h f x) c w
      (fun _ v => ReadsAs c.p base w v) := by
  intro f
  induction f with
  | zero => intro x w; exact writerWP_throw _ _ _ _
  | succ f ih =>
    intro x w
    unfold descendHeight
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_mono (writerWP_ghOf_reads x c w base hvc) ?_
    rintro ⟨_, hx⟩ v hrv
    split
    · simp only [writerWP_pure]; exact hrv
    · simp only [writerWP_bind]
      refine writerWP_mono (writerWP_getNode_reads x c v base hvc) ?_
      intro n v1 ⟨hr1, _, _⟩
      split
      · exact writerWP_throw _ _ _ _
      · split
        · exact writerWP_throw _ _ _ _
        · rename_i fd _
          simp only [writerWP_bind]
          refine writerWP_mono (writerWP_pathAdd_reads (some fd.c) fd.y c v1 base) ?_
          intro _ v2 hr2
          exact writerWP_mono (ih fd.y v2) (fun _ v3 hr3 =>
            ReadsAs.trans _ _ _ _ _ hrv (ReadsAs.trans _ _ _ _ _ hr1 (ReadsAs.trans _ _ _ _ _ hr2 hr3)))

/-- `descendToSegmentRoot` reads as before. -/
theorem writerWP_descendToSegmentRoot_readsU (key : Key) (seg : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (w : W) :
    WriterWP (descendToSegmentRoot key seg) c w (fun _ v => ReadsAs c.p base w v) := by
  unfold descendToSegmentRoot pathClear findRoot pathAdd
  simp only [writerWP_bind, writerWP_read, writerWP_modify, writerWP_get]
  generalize hw1 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w1
  have hr01 : ReadsAs c.p base w w1 := by subst hw1; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  simp only [writerWP_pure]
  refine writerWP_foldlM_state _ _ _ c w1 (fun _ v => ReadsAs c.p base w v) hr01 ?_
  intro a b v hv
  simp only [writerWP_bind]
  refine writerWP_mono (writerWP_descendLte_readsU b c base hvc _ a v) ?_
  intro L v1 hr1
  refine writerWP_mono (writerWP_getNode_reads L c v1 base hvc) ?_
  intro n v2 ⟨hr2, _, _⟩
  split
  · exact writerWP_throw _ _ _ _
  · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
    exact ReadsAs.trans _ _ _ _ _ hv (ReadsAs.trans _ _ _ _ _ hr1
      (ReadsAs.trans _ _ _ _ _ hr2 ⟨by funext y; rfl, rfl, rfl, rfl, rfl⟩))

/-- `descendToHeight` reads as before. -/
theorem writerWP_descendToHeight_readsU (key : Key) (g h : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (w : W) :
    WriterWP (descendToHeight key g h) c w (fun _ v => ReadsAs c.p base w v) := by
  unfold descendToHeight
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (writerWP_descendToSegmentRoot_readsU key g c base hvc w) ?_
  intro root v1 hr1
  split
  · exact writerWP_throw _ _ _ _
  · rename_i cv _
    simp only [writerWP_bind]
    refine writerWP_mono (writerWP_descendHeight_readsU cv h c base hvc _ root v1) ?_
    intro _ v2 hr2
    unfold pathSize
    simp only [writerWP_bind, writerWP_get, writerWP_pure]
    exact ReadsAs.trans _ _ _ _ _ hr1 hr2

end SIS.Tree
