/-
`RootKeyOK`: the space root is a key node at every time of a run (bergdb
024-12, TP7, the root clause of the kinds). Its proof for every run, used by
no other theorem, went in bergdb 025-02.
-/
import SIS.Tree.RootWalkDelete
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
