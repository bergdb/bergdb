/-
The space root is a key node at every time of every run (bergdb 024-12, TP7,
the root clause of the kinds): through the writer by the walk of the root
(`execW_rootWalk`), into the structure by the lift of the writer's space root
(`rootAt_commit_of_lift`), at the earlier times by `rootAt_apply_some_past`
(`treeRun_rootKeyOK`).
-/
import SIS.Tree.RootWalkRun
import SIS.Tree.KindsRun
import SIS.Tree.MergeNodeCountOps
import SIS.Tree.HistoricalRead
import SIS.Tree.InvInit

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The space root of P at time t is a key node of P. -/
def RootKeyOK (p : Params) (P : Struct BVal) (t : Time) : Prop :=
  ∃ r nd, rootAt (viewOf P) t = some r ∧ P.get? r = some nd ∧ nd.isData = false ∧
    nd.level ≤ p.keyMax

end SIS.Tree
