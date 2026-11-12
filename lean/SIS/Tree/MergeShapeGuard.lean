import SIS.Tree.KlongShape
import SIS.Tree.MergeProtectedDelete

namespace SIS.Tree

open SIS SIS.Check

/-- A retained node may change its pointers while keeping its physical
compare values, times, bitmaps, leaf flag, id, height and untaken status. -/
def ShapeGuardHeld (b : NodeGuard) (w : W) : Prop :=
  ∃ n, GuardHeld {b with node := n} w ∧ n.leaf = b.node.leaf ∧
    n.ks.map klongShape = b.node.ks.map klongShape

theorem shapeGuardHeld_of_guardHeld (b : NodeGuard) (w : W) (h : GuardHeld b w) :
    ShapeGuardHeld b w := ⟨b.node,h,rfl,rfl⟩

theorem shapeGuardHeld_count (b : NodeGuard) (w : W) (h : ShapeGuardHeld b w) :
    ∃ n, w.nodes.lookup b.id = some n ∧ n.cnt = b.node.cnt ∧
      klongsWf n.ks = klongsWf b.node.ks := by
  obtain ⟨n,hn,_,hshape⟩ := h
  exact ⟨n,hn.1,KNode.cnt_eq_of_shape n b.node hshape,klongsWf_of_shape_eq _ _ hshape⟩

theorem shapeGuardHeld_not_unary (b : NodeGuard) (w : W) (h : ShapeGuardHeld b w)
    (hc : 2 ≤ b.node.cnt) :
    ∃ n, w.nodes.lookup b.id = some n ∧ n.onlyLiveKlong = none := by
  obtain ⟨n,hn,hcnt,_⟩ := shapeGuardHeld_count b w h
  exact ⟨n,hn,n.onlyLiveKlong_none_of_cnt_ge_two (by omega)⟩

/-- Cleanup retargets preserve this guard even when they target the guarded
node itself. The earlier exact-node guard required different ids. -/
theorem writerWP_retarget_shapeGuard (b : NodeGuard) (q src dst : NodeId)
    (c : Ctx) (w : W) (hw : ShapeGuardHeld b w) :
    WriterWP (retarget q src dst) c w (fun _ v => ShapeGuardHeld b v) := by
  obtain ⟨n,hn,hleaf,hshape⟩ := hw
  by_cases hq : q = b.id
  · subst q
    unfold retarget
    simp only [writerWP_bind,writerWP_read]
    rw [writerWP_getNode_known b.id n c w hn.1]
    split
    · change WriterWP (putNode b.id
        {n with ks := retargetKlongs n.ks (n.lastTimeIndex.getD 0) src dst}) c w _
      refine writerWP_mono (writerWP_putNode_guard_same {b with node := n} _ c w hn) ?_
      intro _ v hv
      refine ⟨_,hv,hleaf,?_⟩
      exact (retargetKlongs_shape n.ks _ src dst).trans hshape
    · simp only [writerWP_pure]
      exact ⟨n,hn,hleaf,hshape⟩
  · refine writerWP_mono (guard_retarget {b with node := n} q src dst (Ne.symm hq) c w hn) ?_
    intro _ v hv
    exact ⟨n,hv,hleaf,hshape⟩

/-- Surviving high nodes contradict a successful final bounds check even
if cleanup has changed their pointers. -/
theorem execW_shapeGuard_height_le (p : Params) (tx : Tx) (i : Time) (view : View BVal)
    (bs : List Bool) (w : W) (b : NodeGuard)
    (he : execW p tx i view = .ok (bs,w)) (hb : ShapeGuardHeld b w) : b.h ≤ p.H := by
  obtain ⟨n,hn,_,_⟩ := hb
  exact execW_guard_height_le p tx i view bs w {b with node := n} he hn

end SIS.Tree
