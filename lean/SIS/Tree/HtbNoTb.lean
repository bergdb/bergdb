/-
The top theorem without `htb` (bergdb 025-05, step 9): `invGetScanOK_merges_tbL` with its
premise `htbL` proved (`takeBelowFuelDelSL_holds`, HtbTop.lean). TP7, TP10 and TP11 for
Java's parameters with the premises `hp`, `hth` and `l4` only.
-/
import SIS.Tree.HtbTop

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- TP7, TP10 and TP11 with no heights' premise (bergdb 025-05, step 9). -/
theorem invGetScanOK_merges_noTb (p : Params) (hp : MergeParamsOK p)
    (hth : 2 ≤ p.theta ∨ p.theta = 0)
    (l4 : OpCaseOK p (RunOK p) (QLive p) DelMergeOpenCase) :
    InvPreserved p ∧ GetOK p ∧ ScanOK p ∧ LatestGetOK p ∧ LatestScanOK p :=
  invGetScanOK_merges_tbL p hp hth (takeBelowFuelDelSL_holds p hp) l4

end SIS.Tree
