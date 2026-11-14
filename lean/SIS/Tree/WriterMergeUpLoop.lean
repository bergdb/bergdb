/-
The merges' loop at the writer's level (bergdb 024-22): `mergeUp` keeps any
invariant that its descent, its node reads and the merge keep.
-/
import SIS.Tree.WriterGetCollapseLoop
import SIS.Tree.WriterTreeMergeFull

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

/-- The merges' loop keeps the writer's tree and any invariant J of the
caller's that the reads keep, given that each merge of the loop keeps them
(`writerWP_merge_any_tree` gives the tree; J carries its premises). -/
theorem writerWP_mergeUp_tree (key : Key) (g : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (J : W → Prop)
    (hJra : ∀ v v', J v → ReadsAs c.p base v v' → J v')
    (hmerge : ∀ x q d v qn xn, TreeOK (wNode c.p base v) c.i v.top.rootKey → J v → 0 < d →
      (v.path[d]?).map (·.2) = some x → (v.path[d - 1]?).map (·.2) = some q →
      v.nodes.lookup q = some qn → qn.leaf = false → v.nodes.lookup x = some xn →
      xn.cnt < c.p.mergeBelow →
      WriterWP (merge x d) c v (fun _ v' => TreeOK (wNode c.p base v') c.i v'.top.rootKey ∧ J v')) :
    ∀ fuel h merged v, TreeOK (wNode c.p base v) c.i v.top.rootKey → J v →
      WriterWP (mergeUp key g fuel h merged) c v
        (fun _ v' => TreeOK (wNode c.p base v') c.i v'.top.rootKey ∧ J v') := by
  intro fuel h merged v hT hJ
  have hra : ∀ v v', (TreeOK (wNode c.p base v) c.i v.top.rootKey ∧ J v) → ReadsAs c.p base v v' →
      TreeOK (wNode c.p base v') c.i v'.top.rootKey ∧ J v' := by
    rintro v v' ⟨hT, hJ⟩ hr
    exact ⟨by rw [hr.1, hr.2.1]; exact hT, hJra v v' hJ hr⟩
  refine writerWP_mergeUp_inv key g c (fun v => TreeOK (wNode c.p base v) c.i v.top.rootKey ∧ J v)
    ?_ ?_ ?_ fuel h merged v ⟨hT, hJ⟩
  · intro h v hI
    exact writerWP_mono (writerWP_descendToHeight_readsU key g h c base hvc v)
      (fun _ v' hr => hra v v' hI hr)
  · intro y v hI
    refine writerWP_mono (writerWP_and (writerWP_getNode_all y c v base hvc)
      (writerWP_getNode_cache y c v)) ?_
    rintro n v' ⟨⟨hr, hl, _, hpre, _⟩, _, _, hp⟩
    exact ⟨hra v v' hI hr, hp, hl, fun z zn hz => lookup_of_prefix _ _ hpre z zn hz⟩
  · rintro x q d v qn xn ⟨hT, hJ⟩ hd hx hq hqn hql hxn hcnt
    exact hmerge x q d v qn xn hT hJ hd hx hq hqn hql hxn hcnt

end SIS.Tree
