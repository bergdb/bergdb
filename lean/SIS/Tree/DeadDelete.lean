/-
The dead klongs' bound through a delete's own writes (bergdb 024-12, section 1,
`d4`'s plan of 2026-11-15; `DW`, DeadLocal.lean): the bitmap goes in only when
`deadOver` lets it through, else its node's last version is split
(`dw_handleFull`); an unlink gives a node its version before the transaction, a
retarget and a take-back change only which nodes klongs name.
-/
import SIS.Tree.DeadSplit
import SIS.Tree.DeadMerge
import SIS.Tree.WriterMergeUpLoop
import SIS.Tree.MergeFullSorted
import SIS.Tree.TakeDeadMerge
import SIS.Tree.WriterKlongLEB

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## The delete's writes: the bitmap, unlink, retarget, take-back -/

set_option maxHeartbeats 4000000 in
/-- The bitmap of a delete keeps `DW`: the node with its bitmap only when
`deadOver` lets it through, else the split of its last version. -/
theorem dw_appendDeleteKlong (base : View BVal) (x : NodeId) (depth cv : Nat) :
    KeepsDW base (appendDeleteKlong x depth cv) := by
  intro c w hvc hth hw
  unfold appendDeleteKlong
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (dw_getNode base x c w hvc hw) ?_
  rintro n v ⟨hv, hn, _, _⟩
  have hfull : ∀ (bits : List Nat) (compact : Bool) (v' : W), DW c base v' →
      WriterWP (handleFull depth x (n.lastVersionGivenDel c.i bits) compact) c v'
        (fun _ v'' => DW c base v'') :=
    fun bits compact v' hv' => dw_handleFull base depth x _ compact c
      (normKs_lastVersionGivenDel n c.i bits) v' hvc hth hv'
  repeat' split
  all_goals first
    | exact writerWP_throw _ _ _ _
    | exact absurd ‹(false && _) = true› (by simp)
    | (simp only [writerWP_pure]; exact hv)
    | (simp only [note, writerWP_bind, writerWP_modify, writerWP_pure]
       exact hfull _ _ _ (dw_same rfl rfl hv))
    | (simp only [note, writerWP_bind, writerWP_modify, writerWP_pure]
       refine writerWP_mono (dw_putNode base x _ c _ (dw_same rfl rfl hv) ?_) (fun _ _ h => h.1)
       refine hn.imp (fun h => ⟨fun h0 => deadOver_false c.p _ (by simp_all) h0, ?_⟩) id
       first
         | exact KNode.setAt_delete_wf _ _ _ h.2 (by assumption)
         | (apply KNode.setAt_delete_wf_of_flag <;> first | exact h.2 | assumption)
         | (apply KNode.add_delete_wf
            · exact h.2
            · intro he; simp_all))

/-- `unlink` keeps `DW`: a node of before the transaction gets its version
before the transaction. -/
theorem dw_unlink (base : View BVal) (x : NodeId) : KeepsDW base (unlink x) := by
  intro c w hvc hth hw
  unfold unlink
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (dw_getNode base x c w hvc hw) ?_
  rintro n v ⟨hv, hn, _, _⟩
  refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_)
  · exact writerWP_mono (dw_putNode base x _ c v hv (dok_or_of (dok_toPrev _) hn)) (fun _ _ h => h.1)
  · simp only [writerWP_pure]; exact hv

/-- `retarget` keeps `DW`: the node's klongs of the transaction name another
node, with the same dead klongs. -/
theorem dw_retarget (base : View BVal) (q src dst : NodeId) : KeepsDW base (retarget q src dst) := by
  intro c w hvc hth hw
  unfold retarget
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (dw_getNode base q c w hvc hw) ?_
  rintro n v ⟨hv, hn, _, _⟩
  refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_)
  · refine writerWP_mono (dw_putNode base q _ c v hv (hn.imp (fun h => ⟨fun h0 => ?_, ?_⟩) id))
      (fun _ _ h => h.1)
    · have e := KNode.deadCount_retarget n (n.lastTimeIndex.getD 0) src dst
      change (⟨n.leaf, retargetKlongs n.ks _ src dst⟩ : KNode).deadCount ≤ _
      rw [e]; exact h.1 h0
    · change klongsWf (retargetKlongs n.ks _ src dst) = true
      rw [klongsWf_retargetKlongs]; exact h.2
  · simp only [writerWP_pure]; exact hv

/-- The take-back keeps `DW`: the parent is retargeted, the node taken back. -/
theorem dw_takeBack (base : View BVal) (x parent : NodeId) (cv : Nat) :
    KeepsDW base (takeBack x parent cv) := by
  intro c w hvc hth hw
  unfold takeBack
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (dw_getNode base parent c w hvc hw) ?_
  rintro pn v ⟨hv, _, _, _⟩
  refine writerWP_mono (dw_frame base _ c v (fr_replacedBy x c v) hv) ?_
  rintro o v1 ⟨hv1, _⟩
  split
  · refine writerWP_if _ _ _ _ _ _ (fun _ => writerWP_throw _ _ _ _) (fun _ => ?_)
    simp only [writerWP_bind]
    refine writerWP_mono (dw_retarget base parent x _ c v1 hvc hth hv1) ?_
    intro _ v2 hv2
    refine writerWP_mono (dw_takenBack base x c v2 hv2) ?_
    intro _ v3 hv3
    exact writerWP_mono (dw_frame base _ c v3 (fr_note _ c v3) hv3) (fun _ _ h => h.1)
  · exact writerWP_throw _ _ _ _

/-! ## Root collapse and the descents -/

/-- A function that reads only keeps `DW`, and the ids taken back. -/
theorem dw_of_reads {α : Type} (base : View BVal) (f : M α) (c : Ctx) (w : W)
    (h : WriterWP f c w (fun _ v => ReadsAs c.p base w v)) (hw : DW c base w) :
    WriterWP f c w (fun _ v => DW c base v ∧ v.taken = w.taken) :=
  writerWP_mono h (fun _ _ hr => ⟨dw_of_wNode hr.1 hw, hr.2.2.1⟩)

theorem fr_pathSize (c : Ctx) (w : W) :
    WriterWP pathSize c w (fun _ v => v.nodes = w.nodes ∧ v.taken = w.taken) := by
  unfold pathSize; simp only [writerWP_bind, writerWP_get, writerWP_pure]
  first | exact ⟨rfl, rfl⟩ | exact ⟨trivial, trivial⟩ | simp

theorem or_taken {P : Prop} {a b : W} {y : NodeId} (he : a.taken = b.taken) :
    P ∨ b.taken.contains y = true → P ∨ a.taken.contains y = true := by
  rw [he]; exact id

/-- The steps of root collapse and the upward delete beyond `dwStep`. -/
macro "dwStep2" : tactic => `(tactic| first
  | ((with_unfolding_none guard_target = WriterWP (putNode _ _) _ _ _)
     refine writerWP_mono (dw_putNode _ _ _ _ _ (by assumption)
       (dok_or_of (dok_repoint _ _) (or_taken (by assumption) (by assumption)))) ?_
     rintro _ _ ⟨_, _⟩)
  | ((with_unfolding_none guard_target = WriterWP (unlink _) _ _ _)
     refine writerWP_mono (dw_unlink _ _ _ _ (by assumption) (by assumption) (by assumption)) ?_
     intro _ _ _)
  | ((with_unfolding_none guard_target = WriterWP (takenBack _) _ _ _)
     refine writerWP_mono (dw_takenBack _ _ _ _ (by assumption)) ?_
     intro _ _ _)
  | ((with_unfolding_none guard_target = WriterWP (appendKlongs _ _ _) _ _ _)
     refine writerWP_mono (dw_appendKlongs _ _ _ _ (by simp) _ _ (by assumption) (by assumption)
       (by assumption)) ?_
     intro _ _ _)
  | ((with_unfolding_none guard_target = WriterWP pathSize _ _ _)
     refine writerWP_mono (dw_frame _ _ _ _ (fr_pathSize _ _) (by assumption)) ?_
     rintro _ _ ⟨_, _⟩)
  | ((with_unfolding_none guard_target = WriterWP (descendToSegmentRoot _ _) _ _ _)
     refine writerWP_mono (dw_of_reads _ _ _ _
       (writerWP_descendToSegmentRoot_readsU _ _ _ _ (by assumption) _) (by assumption)) ?_
     rintro _ _ ⟨_, _⟩))

theorem dw_replaceRoot (base : View BVal) (x : NodeId) (depth only : Nat) :
    KeepsDW base (replaceRoot x depth only) := by
  intro c w hvc hth hw
  unfold replaceRoot
  repeat' (first | dwStep | dwStep2 | split)

theorem dw_takeBackRoot (base : View BVal) (x : NodeId) (depth only : Nat) :
    KeepsDW base (takeBackRoot x depth only) := by
  intro c w hvc hth hw
  unfold takeBackRoot
  repeat' (first | dwStep | dwStep2 | split)

/-- Root collapse keeps `DW`. -/
theorem dw_collapseRoot (base : View BVal) (key : Key) (seg : Nat) :
    ∀ fuel, KeepsDW base (collapseRoot key seg fuel) := by
  intro fuel
  induction fuel with
  | zero => intro c w _ _ _; exact writerWP_throw _ _ _ _
  | succ f ih =>
    intro c w hvc hth hw
    unfold collapseRoot
    repeat' (first
      | dwStep
      | dwStep2
      | ((with_unfolding_none guard_target = WriterWP (takeBackRoot _ _ _) _ _ _)
         refine writerWP_mono (dw_takeBackRoot _ _ _ _ _ _ (by assumption) (by assumption)
           (by assumption)) ?_
         intro _ _ _)
      | ((with_unfolding_none guard_target = WriterWP (replaceRoot _ _ _) _ _ _)
         refine writerWP_mono (dw_replaceRoot _ _ _ _ _ _ (by assumption) (by assumption)
           (by assumption)) ?_
         intro _ _ _)
      | ((with_unfolding_none guard_target = WriterWP (collapseRoot _ _ _) _ _ _)
         exact ih _ _ (by assumption) (by assumption) (by assumption))
      | split)

/-! ## The merge's parent and its last loop -/

/-- The merge's parent keeps `DW`: in place only when `deadOver` lets it through
(well formed as the right child's compare value is live, `hcR`); else the split
of its last version with the new pointers, sorted when the second new node's
compare value, if not the right child's, is not live in the parent (`hg`). -/
theorem dw_mergeParent (base : View BVal) (p : NodeId) (pn : KNode) (depth il cL : Nat) (m1 : NodeId)
    (ir cR : Nat) (m2 : Option (NodeId × Nat)) (c : Ctx) (w : W) (hvc : ViewCoherent c base)
    (hth : 2 ≤ c.p.theta ∨ c.p.theta = 0) (hw : DW c base w) (hlk : w.nodes.lookup p = some pn)
    (hpn : DOK c.p pn ∨ w.taken.contains p = true) (hcR : cR ∈ pn.live.map Prod.fst)
    (hg : ∀ y g, m2 = some (y, g) → g ≠ cR → pn.live.lookup g = none) :
    WriterWP (mergeParent p depth il cL m1 ir cR m2) c w (fun _ v => DW c base v) := by
  refine writerWP_mergeParent_casesD p pn depth il cL m1 ir cR m2 c w _ hlk ?_ ?_
  · intro s hd
    refine (dw_putNode base p _ c ({ w with trail := s :: w.trail } : W) (dw_same rfl rfl hw) ?_ () _
      rfl).1
    exact hpn.imp (fun h => ⟨fun h0 => deadOver_false c.p _ hd h0,
      mergeParentNode_wf pn c.i il cL m1 ir cR m2 h.2 hcR⟩) id
  · intro last compact s hm
    obtain ⟨pairs, hks, hs⟩ := mergeFullLast_sorted pn c.i cL m1 cR m2 last hm hg
    exact dw_handleFull base depth p last compact c ⟨pairs, hks, hs⟩ _ hvc hth (dw_same rfl rfl hw)

/-- The merge's last loop keeps `DW`: each node taken back (its parent
retargeted) or unlinked. -/
theorem dw_mergeCleanup (base : View BVal) (p m1 : NodeId) (c : Ctx) (hvc : ViewCoherent c base)
    (hth : 2 ≤ c.p.theta ∨ c.p.theta = 0) :
    ∀ (xs : List (NodeId × Bool)) (w : W), DW c base w →
    WriterWP (forIn xs PUnit.unit (fun q _ => if q.2 = true then (do
        retarget p q.1 m1
        takenBack q.1
        note "merge.takeback"
        pure (ForInStep.yield PUnit.unit)) else (do
        unlink q.1
        pure (ForInStep.yield PUnit.unit)))) c w
      (fun _ w' => DW c base w') := by
  intro xs
  induction xs with
  | nil =>
    intro w hw
    rw [List.forIn_nil]
    exact (writerWP_pure _ c w _).mpr hw
  | cons q qs ih =>
    intro w hw
    rw [List.forIn_cons]
    by_cases hq2 : q.2 = true
    · simp only [writerWP_bind, hq2, ↓reduceIte]
      refine writerWP_mono (dw_retarget base p q.1 m1 c w hvc hth hw) ?_
      intro _ w1 h1
      refine writerWP_mono (dw_takenBack base q.1 c w1 h1) ?_
      intro _ w2 h2
      refine (writerWP_note_iff _ c _ _).mpr ?_
      refine (writerWP_pure _ c _ _).mpr ?_
      dsimp only
      exact ih _ (dw_same rfl rfl h2)
    · simp only [writerWP_bind, hq2, Bool.false_eq_true, ↓reduceIte]
      refine writerWP_mono (dw_unlink base q.1 c w hvc hth hw) ?_
      intro _ w1 h1
      refine (writerWP_pure _ c _ _).mpr ?_
      dsimp only
      exact ih _ h1

/-! ## LE-b: the empty key moved to the next child -/

theorem normKs_rename_head (t : Time) (t' : Klong) (c1 : Nat) (y1 : NodeId) (r : List Klong)
    (ks : List Klong) (hks : ks = t' :: .key c1 y1 :: r) (h : NormKs t ks) :
    NormKs t (t' :: .key 0 y1 :: r) := by
  obtain ⟨pairs, hp, hs⟩ := h
  cases pairs with
  | nil => rw [hks] at hp; simp [newKlongs] at hp
  | cons q rest =>
    rw [hks] at hp
    simp only [newKlongs, List.map_cons, List.cons.injEq] at hp
    obtain ⟨h1, h2, h3⟩ := hp
    refine ⟨(0, y1) :: rest, ?_, ?_⟩
    · simp only [newKlongs, List.map_cons, h1, h3]
    · have hq : q = (c1, y1) := by cases q; simp_all
      subst hq
      rw [CvSorted, List.pairwise_cons] at hs ⊢
      exact ⟨fun b hb => by have := hs.1 b hb; simp at this ⊢; omega, hs.2⟩

set_option maxHeartbeats 4000000 in
/-- LE-b keeps `DW`: the node with the next child's klong deleted and the empty
key named in its place only when `deadOver` lets it through, else the split of
its last version with the empty key first. -/
theorem dw_emptyKeyNext (base : View BVal) (x : NodeId) (depth : Nat) :
    KeepsDW base (emptyKeyNext x depth) := by
  intro c w hvc hth hw
  unfold emptyKeyNext
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (dw_getNode base x c w hvc hw) ?_
  rintro n v ⟨hv, hn, _, _⟩
  repeat' (first
    | exact writerWP_throw _ _ _ _
    | (simp only [writerWP_bind, writerWP_pure, note, writerWP_modify]; done)
    | ((with_unfolding_none guard_target = WriterWP (handleFull _ _ _ _) _ _ _)
       refine dw_handleFull base _ _ _ _ c ?_ _ hvc hth (dw_same rfl rfl hv)
       exact normKs_rename_head c.i _ _ _ _ _ (by assumption) (normKs_lastVersionGivenDel _ _ _))
    | ((with_unfolding_none guard_target = WriterWP (putNode _ _) _ _ _)
       refine writerWP_mono (dw_putNode base x _ c _ (dw_same rfl rfl hv) ?_) (fun _ _ h => h.1)
       refine hn.imp (fun h => ⟨fun h0 => deadOver_false c.p _ (by simp_all) h0, ?_⟩) id
       apply KNode.leb_write_wf
       · exact h.2
       · apply KNode.nextPhysical_delete_changes; assumption)
    | simp only [writerWP_bind, writerWP_pure, note, writerWP_modify]
    | wpSplit
    | split)

end SIS.Tree
