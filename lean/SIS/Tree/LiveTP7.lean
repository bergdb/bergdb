/-
TP7 with the operation cases proved so far (bergdb 024-12, TP7):
`latestInvOK_of_cases` with the cases (1) to (3) of TP10's three posts
(`GetOpCases.lean`), `QLive` of (1), (2), (3a) and (3b) (`LiveCases.lean`,
`LivePutFull.lean`), and cost's live heights from the delete side of their walk
(`treeRun_heightLiveOK`, `OpHtDelOK`). Left as premises: TP4, the bound on dead
klongs, P's tree, `OpHtDelOK`, the case (4) of TP10's three posts, and `QLive`
of (3c) and (4).
-/
import SIS.Tree.LivePutFull
import SIS.Tree.GetOpCases
import SIS.Tree.HeightsRun

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- `LatestInvOK` under valid parameters from what is open: TP4, the bound on
dead klongs, P's tree, cost's `OpHtDelOK`, TP10's posts of the delete with the
merges (4), and `QLive` of the new segments below a full leaf (3c) and of (4). -/
theorem latestInvOK_of_open (p : Params) (hp : MergeParamsOK p)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts))
    (hD : ∀ ts, Within p ts → DeadAllOK p (treeRun p ts))
    (hdel : OpHtDelOK p)
    (htree : ∀ ts, Within p ts → TreeAt p (treeRun p ts) ts.length)
    (t4 : OpCaseOK p (RunOK p) (QTree p) DelMergeCase)
    (i4 : OpCaseOK p (RunOK p) (QPutInv p) DelMergeCase)
    (r4 : OpCaseOK p (RunOK p) (QRange p) DelMergeCase)
    (l3c : OpCaseOK p (RunOK p) (QLive p) PutNewSegFullCase)
    (l4 : OpCaseOK p (RunOK p) (QLive p) DelMergeCase) : LatestInvOK p := by
  have hp' := hp
  unfold MergeParamsOK at hp'
  have hM : 2 ≤ p.M := by omega
  have hsa : 2 ≤ p.splitAbove := by omega
  have hRL : ∀ P t, RunOK p P t → RunLinksOK p P t := fun _ _ h => h.1
  exact latestInvOK_of_cases p hp hP hD (treeRun_heightLiveOK p hM hP hdel) htree
    (treeCase_putLeafRoom p _) (treeCase_putLeafFull p _ hRL hsa)
    (opCaseOK_putNewSeg_of_parts p _ _ (treeCase_putNewSeg1Room p _ hM) (treeCase_putNewSegsRoom p _ hM)
      (treeCase_putNewSegFull p _ hRL hM hsa)) t4
    (putInvCase_putLeafRoom p _ hRL) (putInvCase_putLeafFull p _ hRL hsa)
    (opCaseOK_putNewSeg_of_parts p _ _ (putInvCase_putNewSeg1Room p _ hRL hM)
      (putInvCase_putNewSegsRoom p _ hRL hM) (putInvCase_putNewSegFull p _ hRL hM hsa)) i4
    (rangeCase_putLeafRoom p _) (rangeCase_putLeafFull p _ hRL hsa)
    (opCaseOK_putNewSeg_of_parts p _ _ (rangeCase_putNewSeg1Room p _ hM)
      (rangeCase_putNewSegsRoom p _ hM) (rangeCase_putNewSegFull p _ hRL hM hsa)) r4
    (liveCase_putLeafRoom p _) (liveCase_putLeafFull p _ hRL hsa hp)
    (opCaseOK_putNewSeg_of_parts p _ _ (liveCase_putNewSeg1Room p _ hM)
      (liveCase_putNewSegsRoom p _ hM) l3c) l4

/-- TP7 under valid parameters from what is open, as `latestInvOK_of_open`. -/
theorem invPreserved_of_open_cases (p : Params) (hp : MergeParamsOK p)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts))
    (hD : ∀ ts, Within p ts → DeadAllOK p (treeRun p ts))
    (hdel : OpHtDelOK p)
    (htree : ∀ ts, Within p ts → TreeAt p (treeRun p ts) ts.length)
    (t4 : OpCaseOK p (RunOK p) (QTree p) DelMergeCase)
    (i4 : OpCaseOK p (RunOK p) (QPutInv p) DelMergeCase)
    (r4 : OpCaseOK p (RunOK p) (QRange p) DelMergeCase)
    (l3c : OpCaseOK p (RunOK p) (QLive p) PutNewSegFullCase)
    (l4 : OpCaseOK p (RunOK p) (QLive p) DelMergeCase) : InvPreserved p :=
  invPreserved_of_latest_pointers p hp
    (latestInvOK_of_open p hp hP hD hdel htree t4 i4 r4 l3c l4) hP hD

end SIS.Tree
