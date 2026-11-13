/-
The tree model (bergdb 024-12, TP4 and TP7): the writer keeps `PtrsOK`,
continued from SIS/Tree/WriterPtrsOps.lean: a merge, the merges after a
delete, the upward unlink, a put, and a transaction (`execW_ptrsOK`).
-/
import SIS.Tree.WriterPtrsOps

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

set_option maxHeartbeats 8000000 in
theorem ptrs_merge (Old : NodeId → Prop) (x : NodeId) (d : Nat) : KeepsPtrs Old (merge x d) := by
  intro c w hv hw
  unfold merge
  repeat' first
    | ptMergeLoop
    | wpSimplify
    | ptCore
    | ptUse (ptrs_unlink _ _)
    | ptUse1 (ptrs_retarget _ _ _ _)
    | ptSibling
    | ptUse2 (ptrs_mergeParent _ _ _ _ _ _ _ _ _)
    | wpSplit
    | split
    | contradiction

end SIS.Tree
