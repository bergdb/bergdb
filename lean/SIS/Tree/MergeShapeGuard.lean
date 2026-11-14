import SIS.Tree.KlongShape
import SIS.Tree.MergeProtectedDelete

namespace SIS.Tree

open SIS SIS.Check

/-- A retained node may change its pointers while keeping its physical
compare values, times, bitmaps, leaf flag, id, height and untaken status. -/
def ShapeGuardHeld (b : NodeGuard) (w : W) : Prop :=
  ∃ n, GuardHeld {b with node := n} w ∧ n.leaf = b.node.leaf ∧
    n.ks.map klongShape = b.node.ks.map klongShape

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

end SIS.Tree
