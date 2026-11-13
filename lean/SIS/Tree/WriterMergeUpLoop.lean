/-
The merges' loop at the writer's level (bergdb 024-22): `mergeUp` keeps any
invariant that its descent, its node reads and the merge keep.
-/
import SIS.Tree.WriterGetCollapseLoop

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- `mergeUp` keeps any invariant Inv that its steps keep: the descent to the
height (`descendToHeight`), the reads of the parent's and the node's nodes, and
the merge of the node x at depth d of the path, d > 0, below an inner parent
q, x holding fewer live klongs than `mergeBelow`. -/
theorem writerWP_mergeUp_inv (key : Key) (g : Nat) (c : Ctx) (Inv : W → Prop)
    (hdesc : ∀ h v, Inv v → WriterWP (descendToHeight key g h) c v (fun _ v' => Inv v'))
    (hget : ∀ y v, Inv v → WriterWP (getNode y) c v (fun n v' =>
      Inv v' ∧ v'.path = v.path ∧ v'.nodes.lookup y = some n ∧
        ∀ z zn, v.nodes.lookup z = some zn → v'.nodes.lookup z = some zn))
    (hmerge : ∀ x q d v qn xn, Inv v → 0 < d → (v.path[d]?).map (·.2) = some x →
      (v.path[d - 1]?).map (·.2) = some q → v.nodes.lookup q = some qn → qn.leaf = false →
      v.nodes.lookup x = some xn → xn.cnt < c.p.mergeBelow →
      WriterWP (merge x d) c v (fun _ v' => Inv v')) :
    ∀ fuel h merged v, Inv v → WriterWP (mergeUp key g fuel h merged) c v (fun _ v' => Inv v') := by
  intro fuel
  induction fuel with
  | zero => intro h merged v _; exact writerWP_throw _ _ _ _
  | succ f ih =>
    intro h merged v hI
    unfold mergeUp
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_mono (hdesc h v hI) ?_
    intro d v1 hI1
    split
    · simp only [writerWP_pure]; exact hI1
    · rename_i hd0
      have hd : 0 < d := by
        cases d with
        | zero => simp at hd0
        | succ _ => omega
      unfold pathNode
      simp only [writerWP_bind, writerWP_get]
      cases hex : v1.path[d]? with
      | none => exact writerWP_throw _ _ _ _
      | some ex =>
        simp only [writerWP_pure]
        cases heq : v1.path[d - 1]? with
        | none => exact writerWP_throw _ _ _ _
        | some eq =>
          simp only [writerWP_pure]
          refine writerWP_mono (hget eq.2 v1 hI1) ?_
          rintro qn v2 ⟨hI2, hp2, hl2, _⟩
          split
          · simp only [writerWP_pure]; exact hI2
          · rename_i hql
            have hql' : qn.leaf = false := by simpa using hql
            rw [writerWP_bind]
            refine writerWP_mono (hget ex.2 v2 hI2) ?_
            rintro xn v3 ⟨hI3, hp3, hl3, hkeep3⟩
            split
            · simp only [writerWP_pure]; exact hI3
            · rename_i hcnt
              have hcnt' : xn.cnt < c.p.mergeBelow := by simpa using hcnt
              rw [writerWP_bind]
              refine writerWP_mono (hmerge ex.2 eq.2 d v3 qn xn hI3 hd
                (by rw [hp3, hp2, hex]; rfl) (by rw [hp3, hp2, heq]; rfl) (hkeep3 _ _ hl2) hql' hl3
                hcnt') ?_
              intro r v4 hI4
              split
              · simp only [writerWP_pure]; exact hI4
              · exact ih (h + 1) true v4 hI4

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

end SIS.Tree
