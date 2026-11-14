/-
The top theorem of the key tree's proofs with the merges (bergdb 024-12):
TP7 (`InvPreserved`), TP10 (`GetOK`) and TP11 (`ScanOK`), and with them
`LatestGetOK` and `LatestScanOK`, for the parameters of `MergeParamsOK`, from
one flat list of named premises (`invGetScanOK_merges`). TP4 and P's tree at
every run are not premises: they come from the take-back's joint induction
(putinv's `runTreeQ_of_mergesF4`), which carries TP7's invariant and what its
step needs (`LatestQ`, `latestQ_snoc`). Every put case is proved; the
premises are about the delete with the merges (4), the fuel, the heights'
delete side and the bound on dead klongs. 024-12's section 1 lists them with
their owners and test evidence.
-/
import SIS.Tree.LatestJoint
import SIS.Tree.TakeRunQF4
import SIS.Tree.HeightsChkRun
import SIS.Tree.CollapseCascade
import SIS.Tree.DelStepsCascF3

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

set_option maxHeartbeats 800000 in
/-- TP7, TP10 and TP11, and the latest time's get and scan, for the parameters
of `MergeParamsOK`, from the named premises:

* `hD`: the bound on dead klongs at every run (void with theta 0);
* `hchk`: the delete runs as its copy with the take-backs' checks (cost's
  `OpDelChkOK`, for the heights);
* `hfit`: every state between operations fits the fuel (`TxSegFitsOK`);
* the delete with the merges (4): TP10's three posts (`t4`, `i4`, `r4`) and
  TP7's live counts (`l4`); the reading's obligations (the upward delete's
  stop node, `hUC` and `hULb`; a full leaf's split, `hFits`; the merge, `hMS`;
  the collapse, `hCo`); the take-back's (`hDS`, `hRJ`; `hMS` and `hCo`
  again). -/
theorem invGetScanOK_merges (p : Params) (hp : MergeParamsOK p)
    (hD : ∀ ts, Within p ts → DeadAllOK p (treeRun p ts))
    (hchk : OpDelChkOK p)
    (hfit : TxSegFitsOK p (RunOK p))
    (t4 : OpCaseOK p (RunOK p) (QTree p) DelMergeCase)
    (i4 : OpCaseOK p (RunOK p) (QPutInv p) DelMergeCase)
    (r4 : OpCaseOK p (RunOK p) (QRange p) DelMergeCase)
    (l4 : OpCaseOK p (RunOK p) (QLive p) DelMergeCase)
    (hUC : ∀ ts BK, UpCascOKF3 (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) BK)
    (hULb : ∀ ts BK, UpLebOKF3 (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) BK)
    (hFits : ∀ ts, DelFullFitsOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hMS : ∀ ts, MergeStepOKF3 (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hCo : ∀ ts, CollapseStepOKF4 (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hDS : DelStepsJ2OKF3 p (RunTreeQ p (LatestQ p)) (TakeS3 p))
    (hRJ : ∀ ts B, ReplaceRootFullJ2OK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1) B) :
    InvPreserved p ∧ GetOK p ∧ ScanOK p ∧ LatestGetOK p ∧ LatestScanOK p := by
  have hp' := hp
  unfold MergeParamsOK at hp'
  have hM := mergeParamsOK_M p hp
  have hm : p.merges = true := by
    unfold Params.merges; simp only [decide_eq_true_eq]; omega
  have hsa : 2 ≤ p.splitAbove := by omega
  have hcap : 1 ≤ p.mergeMax := by omega
  have hRL : ∀ P t, RunOK p P t → RunLinksOK p P t := fun _ _ h => h.1
  -- TP10's three posts and TP7's live counts for every operation
  have hT := opCaseOK_of_cases_merges p (RunOK p) _ hm (treeCase_putLeafRoom p _)
    (treeCase_putLeafFull p _ hRL hsa)
    (opCaseOK_putNewSeg_of_parts p _ _ (treeCase_putNewSeg1Room p _ (by omega))
      (treeCase_putNewSegsRoom p _ (by omega)) (treeCase_putNewSegFull p _ hRL (by omega) hsa)) t4
  have hPI := opCaseOK_of_cases_merges p (RunOK p) _ hm (putInvCase_putLeafRoom p _ hRL)
    (putInvCase_putLeafFull p _ hRL hsa)
    (opCaseOK_putNewSeg_of_parts p _ _ (putInvCase_putNewSeg1Room p _ hRL (by omega))
      (putInvCase_putNewSegsRoom p _ hRL (by omega)) (putInvCase_putNewSegFull p _ hRL (by omega) hsa))
    i4
  have hO := opCaseOK_of_cases_merges p (RunOK p) _ hm (rangeCase_putLeafRoom p _)
    (rangeCase_putLeafFull p _ hRL hsa)
    (opCaseOK_putNewSeg_of_parts p _ _ (rangeCase_putNewSeg1Room p _ (by omega))
      (rangeCase_putNewSegsRoom p _ (by omega)) (rangeCase_putNewSegFull p _ hRL (by omega) hsa)) r4
  have hLv := opCaseOK_of_cases_merges p (RunOK p) _ hm (liveCase_putLeafRoom p _)
    (liveCase_putLeafFull p _ hRL hsa hp)
    (opCaseOK_putNewSeg_of_parts p _ _ (liveCase_putNewSeg1Room p _ (by omega))
      (liveCase_putNewSegsRoom p _ (by omega)) (liveCase_putNewSegFull p _ hRL (by omega) hsa hp)) l4
  -- the run induction: TP4, P's tree and LatestQ at every run
  have hR : ∀ P t, RunTreeQ p (LatestQ p) P t → RunOK p P t := runOK_of_runTreeQ p
  have hRL' : ∀ P t, RunTreeQ p (LatestQ p) P t → RunLinksOK p P t := fun _ _ h => h.1
  have hRT' : ∀ P t, RunTreeQ p (LatestQ p) P t → TreeAt p P t := fun _ _ h => h.2.1
  have hRI' : ∀ P t, RunTreeQ p (LatestQ p) P t → InvOK p P t := fun _ _ h => h.2.2.1
  have hT' := opCaseOK_anti p _ _ hR _ _ hT
  have hPI' := opCaseOK_anti p _ _ hR _ _ hPI
  have hO' := opCaseOK_anti p _ _ hR _ _ hO
  have hJ := runTreeQ_of_mergesF4 p (by omega) hsa hcap hm (LatestQ p) (latestQ_init p (by omega))
    (latestQ_snoc p hp hD (opHtDelOK_of_chk p hchk) hT hPI hO hLv)
    (fun _ _ h => h.2.1) (fun _ _ h => h.2.2.1)
    (opTreeOKUnder_of_cases p _ hRL' hRT' hRI' hT' hPI' hO')
    (putInvStateOK_of_cases p _ hRL' hRT' hRI' hT' hPI' hO')
    (rangeStateOK_of_cases p _ hRL' hRT' hRI' hT' hPI' hO') hDS hMS hCo hRJ
  -- TP7, TP10 and TP11 from it
  have hP : ∀ ts, Within p ts → PointersOK (treeRun p ts) := fun ts hw => (hJ ts hw).1.1
  have hinv : InvPreserved p :=
    invPreserved_of_latest_pointers p hp (fun ts hw => (hJ ts hw).2.2.1) hP hD
  have h := getOK_scanOK_of_cases_merges_open p hp hinv (fun ts hw => (hJ ts hw).1)
    (fun ts hw => (hJ ts hw).2.1) hfit t4 i4 r4
    (opGetCaseOK_delMergeF4 p (RunOK p)
      (delStepsOKF3_of_open5 p (RunOK p) (by omega) hsa hRL hP hUC hULb hFits)
      hMS hCo hsa hcap (by omega) hP hfit)
  exact ⟨hinv, h.1, h.2, latestGetOK_of_getOK p h.1, latestScanOK_of_scanOK p h.2⟩

end SIS.Tree
