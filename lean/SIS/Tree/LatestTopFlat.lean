/-
The top theorem with the flattest list of named premises (bergdb 024-12):
`invGetScanOK_merges_flat`. It is `invGetScanOK_merges` with two premises
taken apart:

* the bound on dead klongs at every run (`hD`) comes from the operations: cases
  (1), (3a) and (3b) keep it (`deadCase_putLeafRoom`, `DeadCases.lean`), and
  `QDead` of (2), (3c) and (4) are premises (`DeadRun.lean`; the run induction
  carries `DeadAllOK` in `LatestQD`);
* the take-back's delete steps (`hDS`) come from their open pieces (putinv's
  `delStepsJ2OKF3_of_openR` over `TakeS4`, `runTreeQ_of_mergesF4S`): the
  upward delete's stop node for the take-back, the made-for ids at every state
  between operations, and the fuel there;
* the take-back through a replaceRoot whose segment leaf is full (`hRJ`) is
  proved (putinv's `replaceRootFullJ2OK_run`);
* the upward delete's cascade at the space root is proved, for the reading
  (putinv's `delStepsOKF3_of_open6`): `hUC` is `hBel`, `hL` and `hFit`;
* the fuel at every state between operations (`hfit`) comes from the heights
  (cost's `txSegFitsOK_of_takeBelowDelR`): every node a delete takes back has a
  height below the fuel (`TakeBelowFuelDelOK`; a put takes nothing back).

024-12's section 1 lists the premises with their owners and test evidence.
-/
import SIS.Tree.LatestTop
import SIS.Tree.DeadRun
import SIS.Tree.DeadCases
import SIS.Tree.TakeReplaceFull
import SIS.Tree.HeightsFit
import SIS.Tree.DelStepsCascRoot

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

set_option maxHeartbeats 800000 in
/-- TP7, TP10 and TP11, and the latest time's get and scan, for the parameters
of `MergeParamsOK`, from the flat list of named premises (section 1 of
024-12). -/
theorem invGetScanOK_merges_flat (p : Params) (hp : MergeParamsOK p)
    (hchk : OpDelChkOK p)
    (htb : TakeBelowFuelDelOK p)
    (d2 : OpCaseOK p (RunOK p) (QDead p) PutLeafFullCase)
    (d3c : OpCaseOK p (RunOK p) (QDead p) PutNewSegFullCase)
    (d4 : OpCaseOK p (RunOK p) (QDead p) DelMergeCase)
    (t4 : OpCaseOK p (RunOK p) (QTree p) DelMergeCase)
    (i4 : OpCaseOK p (RunOK p) (QPutInv p) DelMergeCase)
    (r4 : OpCaseOK p (RunOK p) (QRange p) DelMergeCase)
    (l4 : OpCaseOK p (RunOK p) (QLive p) DelMergeCase)
    (hBel : ∀ ts BK,
      UpCascBelowOKF3 (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) BK)
    (hL : ∀ ts, UpUnlinkLinksOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hFit : ∀ ts BK, UpCascFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) BK)
    (hULb : ∀ ts BK, UpLebOKF3 (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) BK)
    (hFits : ∀ ts, DelFullFitsOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hMS : ∀ ts, MergeStepOKF3 (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hCo : ∀ ts, CollapseStepOKF4 (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hUCJ : ∀ ts BK B,
      UpCascJ2OKF3 (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) BK B)
    (hULbJ : ∀ ts BK B,
      UpLebJ2OKF3 (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) BK B)
    (hMF : StateOK p (RunOK p) (fun _ tx w => ∀ x o, w.madeFor.lookup x = some o → o < tx.base)) :
    InvPreserved p ∧ GetOK p ∧ ScanOK p ∧ LatestGetOK p ∧ LatestScanOK p := by
  have hp' := hp
  unfold MergeParamsOK at hp'
  have hM := mergeParamsOK_M p hp
  have hm : p.merges = true := by
    unfold Params.merges; simp only [decide_eq_true_eq]; omega
  have hsa : 2 ≤ p.splitAbove := by omega
  have hcap : 1 ≤ p.mergeMax := by omega
  have hRL : ∀ P t, RunOK p P t → RunLinksOK p P t := fun _ _ h => h.1
  -- TP10's three posts, TP7's live counts and the dead bound for every operation
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
  have hDd := opCaseOK_of_cases_merges p (RunOK p) _ hm (deadCase_putLeafRoom p _) d2
    (opCaseOK_putNewSeg_of_parts p _ _ (deadCase_putNewSeg1Room p _ (by omega))
      (deadCase_putNewSegsRoom p _ (by omega)) d3c) d4
  -- the run induction: TP4, P's tree and LatestQD at every run
  have hR : ∀ P t, RunTreeQ p (LatestQD p) P t → RunOK p P t := runOK_of_runTreeQD p
  have hRL' : ∀ P t, RunTreeQ p (LatestQD p) P t → RunLinksOK p P t := fun _ _ h => h.1
  have hRT' : ∀ P t, RunTreeQ p (LatestQD p) P t → TreeAt p P t := fun _ _ h => h.2.1
  have hRI' : ∀ P t, RunTreeQ p (LatestQD p) P t → InvOK p P t := fun _ _ h => h.2.2.1.1
  have hRP' : ∀ P t, RunTreeQ p (LatestQD p) P t → PointersOK P := fun _ _ h => h.1.1
  have hRK' : ∀ P t, RunTreeQ p (LatestQD p) P t → KindsAllOK p P := fun _ _ h => h.2.2.1.2.2.1
  have hRH' : ∀ P t, RunTreeQ p (LatestQD p) P t → HeightAllOK p P t :=
    fun _ _ h => h.2.2.1.2.2.2.1
  -- the fuel at every state between operations (cost's `txSegFitsOK_of_takeBelowDelR`)
  have hfitQ : TxSegFitsOK p (RunTreeQ p (LatestQD p)) :=
    txSegFitsOK_of_takeBelowDelR p (by omega) _ hRL' hRK' hRH' hchk htb
  have hT' := opCaseOK_anti p _ _ hR _ _ hT
  have hPI' := opCaseOK_anti p _ _ hR _ _ hPI
  have hO' := opCaseOK_anti p _ _ hR _ _ hO
  have hJ := runTreeQ_of_mergesF4S p (by omega) hsa hcap hm (LatestQD p) (latestQD_init p (by omega))
    (latestQD_snoc p hp (opHtDelOK_of_chk p hchk) hT hPI hO hLv hDd)
    (fun _ _ h => h.1.2.1) (fun _ _ h => h.1.2.2.1)
    (opTreeOKUnder_of_cases p _ hRL' hRT' hRI' hT' hPI' hO')
    (putInvStateOK_of_cases p _ hRL' hRT' hRI' hT' hPI' hO')
    (rangeStateOK_of_cases p _ hRL' hRT' hRI' hT' hPI' hO')
    hfitQ
    (fun ts tx hw hr => hMF ts tx hw (hR _ _ hr))
    (delStepsJ2OKF3_of_openR p _ (TakeS4 p) (by omega) hsa hRL' hRP' hRK'
      (fun _ _ _ h => h.1.1.1.1) (fun _ _ _ h => h.1.1.1.2) (fun _ _ _ h => h.1.1.2)
      (fun _ _ _ h => h.1.2) (fun _ _ _ h => h.2.1) (fun _ _ _ h => h.2.2) hUCJ hULbJ hFits)
    hMS hCo (replaceRootFullJ2OK_run p hsa)
  -- TP7, TP10 and TP11 from it
  have hP : ∀ ts, Within p ts → PointersOK (treeRun p ts) := fun ts hw => (hJ ts hw).1.1
  have hfit : TxSegFitsOK p (RunOK p) :=
    fun ts tx hw _ => hfitQ ts tx hw (hJ ts (within_snoc_prefix p ts tx hw))
  have hinv : InvPreserved p :=
    invPreserved_of_latest_pointers p hp (fun ts hw => (hJ ts hw).2.2.1.1) hP
      (fun ts hw => (hJ ts hw).2.2.2)
  have h := getOK_scanOK_of_cases_merges_open p hp hinv (fun ts hw => (hJ ts hw).1)
    (fun ts hw => (hJ ts hw).2.1) hfit t4 i4 r4
    (opGetCaseOK_delMergeF4 p (RunOK p)
      (delStepsOKF3_of_open6 p (RunOK p) (by omega) hsa hRL hP hL hFit hBel hULb hFits)
      hMS hCo hsa hcap (by omega) hP hfit)
  exact ⟨hinv, h.1, h.2, latestGetOK_of_getOK p h.1, latestScanOK_of_scanOK p h.2⟩

/-- Java's parameters (record format 7's thresholds and option 2's theta, from
node size 8) are parameters of the top theorem. -/
theorem mergeParamsOK_java (q : Params) (h : 8 ≤ q.M) : MergeParamsOK q.withMerges.withTheta :=
  mergeParamsOK_withMerges q h

end SIS.Tree
