/-
TP10 and TP11 at the latest time with every put case proved (bergdb 024-12):
`LatestGetOK` and `LatestScanOK` for the parameters of `MergeParamsOK`, from
TP7 with every put case proved (`invPreserved_of_open_del`) and TP10's cases
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

/-- TP10 and TP11 for the parameters of `MergeParamsOK` with every put case
proved: TP7 by `invPreserved_of_open_del`, the runs' links from TP4. -/
theorem getOK_scanOK_of_open_del (p : Params) (hp : MergeParamsOK p)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts))
    (hD : ∀ ts, Within p ts → DeadAllOK p (treeRun p ts))
    (hdel : OpHtDelOK p)
    (htree : ∀ ts, Within p ts → TreeAt p (treeRun p ts) ts.length)
    (hfit : TxSegFitsOK p (RunOK p))
    (t4 : OpCaseOK p (RunOK p) (QTree p) DelMergeCase)
    (i4 : OpCaseOK p (RunOK p) (QPutInv p) DelMergeCase)
    (r4 : OpCaseOK p (RunOK p) (QRange p) DelMergeCase)
    (l4 : OpCaseOK p (RunOK p) (QLive p) DelMergeCase)
    (c4 : OpGetCaseOK p (RunOK p) DelMergeCase) :
    GetOK p ∧ ScanOK p := by
  have hp' := hp
  unfold MergeParamsOK at hp'
  exact getOK_scanOK_of_cases_merges_open p hp
    (invPreserved_of_open_del p hp hP hD hdel htree t4 i4 r4 l4)
    (runLinksOK_of_pointers p (by omega) hP) htree hfit t4 i4 r4 c4

/-- latest's target, `LatestGetOK` and `LatestScanOK`, for the parameters of
`MergeParamsOK`, as `getOK_scanOK_of_open_del`. -/
theorem latestGetOK_latestScanOK_of_open_del (p : Params) (hp : MergeParamsOK p)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts))
    (hD : ∀ ts, Within p ts → DeadAllOK p (treeRun p ts))
    (hdel : OpHtDelOK p)
    (htree : ∀ ts, Within p ts → TreeAt p (treeRun p ts) ts.length)
    (hfit : TxSegFitsOK p (RunOK p))
    (t4 : OpCaseOK p (RunOK p) (QTree p) DelMergeCase)
    (i4 : OpCaseOK p (RunOK p) (QPutInv p) DelMergeCase)
    (r4 : OpCaseOK p (RunOK p) (QRange p) DelMergeCase)
    (l4 : OpCaseOK p (RunOK p) (QLive p) DelMergeCase)
    (c4 : OpGetCaseOK p (RunOK p) DelMergeCase) :
    LatestGetOK p ∧ LatestScanOK p :=
  have h := getOK_scanOK_of_open_del p hp hP hD hdel htree hfit t4 i4 r4 l4 c4
  ⟨latestGetOK_of_getOK p h.1, latestScanOK_of_scanOK p h.2⟩

end SIS.Tree
