/-
TP10 and TP11 at the latest time with every put case proved (bergdb 024-12):
`LatestGetOK` and `LatestScanOK` for the parameters of `MergeParamsOK`, from
TP7 with every put case proved and TP10's cases
(`getOK_scanOK_of_cases_merges_open`). Left as premises: TP4, the bound on dead
klongs, P's tree, the fuel premise along transactions (`TxSegFitsOK`), cost's
`OpHtDelOK`, and the delete with the merges (4): TP10's three posts, its
reading and `QLive`.
-/
import SIS.Tree.LivePutNewSegFull
import SIS.Tree.ScanLatest

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem latestGetOK_of_getOK (p : Params) (h : GetOK p) : LatestGetOK p :=
  fun ts hw key hkey => h ts hw ts.length (Nat.le_refl _) key hkey

theorem latestScanOK_of_scanOK (p : Params) (h : ScanOK p) : LatestScanOK p :=
  fun ts hw req limit hreq => h ts hw ts.length (Nat.le_refl _) req limit hreq

end SIS.Tree
