import SIS.Tree.TreeReadModel
import SIS.Tree.ScanBoundary

namespace SIS.Tree

open SIS SIS.Check

attribute [local cbv_eval] appendKlongs_step_dead putSegs_scanBoundary_step
attribute [local cbv_opaque] appendKlongs putSegs

/-- Enumeration on an unrestricted view need not produce an encoded key.
Thus `treeContents_keyShape` does not hold with `keyWf` for an arbitrary
view; `treeRun_treeContents_keyWf` (RunEncoding.lean) states it for the views
of a run. -/
theorem treeContents_unrestricted_not_wf :
    ∃ q ∈ treeContents scanBoundaryParams
      (viewOf (treeRun scanBoundaryParams scanBoundaryHistory)) 1
      scanBoundaryParams.fuel 1, keyWf q.1 = false := by
  refine ⟨(scanBoundaryKey, 1), ?_, scanBoundaryKey_not_wf⟩
  cbv
  exact List.mem_cons_self

end SIS.Tree
