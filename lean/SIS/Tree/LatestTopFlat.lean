/-
The top theorem with the flattest list of named premises (bergdb 024-12):
`invGetScanOK_merges_flat`. It is `invGetScanOK_merges` with two premises
taken apart:

* the bound on dead klongs at every run (`hD`) comes from the operations: every
  put keeps it, for theta 0 or at least 2 (`hth`; `deadCase_putLeafRoom`,
  `DeadCases.lean`, `DeadPutFull.lean`, `DeadNewSegFull.lean`, with the cascade's
  dead counts `writerWP_appendKlongs_chainDead`), and `QDead` of (4) is a premise
  (`DeadRun.lean`; the run induction carries `DeadAllOK` in `LatestQD`);
* the take-back's delete steps (`hDS`) come from their open pieces (putinv's
  `delStepsJ2OKF3_of_openR` over `TakeS4`, `runTreeQ_of_mergesF4S`): the
  upward delete's stop node for the take-back, the made-for ids at every state
  between operations, and the fuel there;
* the take-back through a replaceRoot whose segment leaf is full (`hRJ`) is
  proved (putinv's `replaceRootFullJ2OK_run`);
* the upward delete's cascade at its stop node is proved, for the reading
  (putinv's `delStepsOKF3_of_open7`), and for the take-back
  (`delStepsJ2OKF3_of_openR2`): `hUC` and `hUCJ` are `hU`, `hL` and `hFit`, about
  the state after the upward loop and the fuel after the cascade; LE-b at the
  stop node is proved when the node has room (`delStepsOKF3_of_open8`,
  `delStepsJ2OKF3_of_openR3`), so its premises are about a full stop node;
* the fuel at every state between operations (`hfit`) comes from the heights
  (cost's `txSegFitsOK_of_takeBelowDelR`): every node a delete takes back has a
  height below the fuel (`TakeBelowFuelDelOK`; a put takes nothing back).

024-12's section 1 lists the premises with their owners and test evidence.
-/
import SIS.Tree.LatestTop
import SIS.Tree.DeadRun
import SIS.Tree.DeadCases
import SIS.Tree.DeadNewSegFull
import SIS.Tree.TakeReplaceFull
import SIS.Tree.HeightsFit
import SIS.Tree.HeightsUnder
import SIS.Tree.DelStepsCascRoot
import SIS.Tree.TakeUpCasc
import SIS.Tree.DelStepsLeb

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- `heightAllOK_snoc` with the delete side of the heights only at the runs that
R speaks of (cost's `OpHtDelOKUnder`, `execW_htCacheU`). -/
theorem heightAllOK_snocU (p : Params) (hM : 2 ≤ p.M) (R : Struct BVal → Time → Prop)
    (hdel : OpHtDelOKUnder p R) (ts : List Tx) (tx : Tx)
    (hw : Within p (ts ++ [tx])) (hr : R (treeRun p ts) ts.length)
    (hL : RunLinksOK p (treeRun p ts) ts.length)
    (hK : KindsAllOK p (treeRun p ts)) (hA : HeightAllOK p (treeRun p ts) ts.length) :
    HeightAllOK p (treeRun p (ts ++ [tx])) (ts.length + 1) := by
  obtain ⟨hP', hH, hN⟩ := hL
  obtain ⟨bs, w, he0⟩ := execW_success_of_within_snoc p ts tx hw
  have hfresh : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have := (hw.2 ts.length (by simp)).1
    simpa using this
  have htimes : StructTimesLE (treeRun p ts) (ts.length + 1 - 1) := treeRun_timesLE p ts
  have hl := viewLinksOK_of p _ _ tx.base hfresh htimes hP' hN
  have hrun : runOps p tx.base tx.ops (ts.length + 1)
      (view (treeSpec p) (treeRun p ts) ts.length) = .ok (bs, w) := he0
  have he : execW p tx (ts.length + 1)
      (view (treeSpec p) (treeRun p ts) (ts.length + 1 - 1)) = .ok (bs, w) := hrun
  have hbook := execW_book p tx (ts.length + 1) _ bs w
    (viewIdsBelow_view p (treeRun p ts) (ts.length + 1 - 1) tx.base hfresh) he
  have hHt := execW_htCacheU p hM R hdel ts tx hw hr ⟨hP', hH, hN⟩ hK hA bs w he0
  have hA' : HeightAllOK p (treeRun p ts) (ts.length + 1 - 1) := by simpa using hA
  have hstep := heightAllOK_step p _ (ts.length + 1) tx bs w (by omega) hfresh
    htimes (treeRun_root_level p _) hH hl hP' he hbook hA' hHt
  rw [treeRun_snoc_changes p ts tx bs w hrun]
  exact hstep

/-- `latestQD_snoc` with the delete side of the heights only at the runs of the
induction. -/
theorem latestQD_snocU (p : Params) (hp : MergeParamsOK p)
    (hdel : OpHtDelOKUnder p (RunTreeQ p (LatestQD p)))
    (hT : OpCaseOK p (RunOK p) (QTree p) AnyOp) (hPI : OpCaseOK p (RunOK p) (QPutInv p) AnyOp)
    (hO : OpCaseOK p (RunOK p) (QRange p) AnyOp) (hLv : OpCaseOK p (RunOK p) (QLive p) AnyOp)
    (hDd : OpCaseOK p (RunOK p) (QDead p) AnyOp) :
    ∀ ts tx, Within p (ts ++ [tx]) → RunTreeQ p (LatestQD p) (treeRun p ts) ts.length →
      RunLinksOK p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      TreeAt p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      LatestQD p (treeRun p (ts ++ [tx])) (ts.length + 1) := by
  intro ts tx hw hr hL' hT'
  have hM := mergeParamsOK_M p hp
  have hr0 := hr
  obtain ⟨hL, hTA, ⟨hI, _, hK, hA, hS, hLA⟩, hD⟩ := hr
  have hD' := deadAllOK_snoc p hT hPI hO hDd ts tx hw ⟨hL, hTA, hI⟩ hD
  have hK' := kindsAllOK_snoc p (by omega) ts tx hw hL hK
  have hA' := heightAllOK_snocU p (by omega) _ hdel ts tx hw hr0 hL hK hA
  have hS' := sizeOK_snoc p hp ts tx hw hL hS
  have hLA' := leftAllOK_snoc p hp ts tx hw hL hLA
  exact ⟨⟨invOK_snoc p hT hPI hO hLv ts tx hw ⟨hL, hTA, hI⟩ hL' hT' hK' hA' hS' hLA' hD',
    hL'.1, hK', hA', hS', hLA'⟩, hD'⟩

set_option maxHeartbeats 800000 in
/-- TP7, TP10 and TP11, and the latest time's get and scan, for the parameters
of `MergeParamsOK`, from the flat list of named premises (section 1 of
024-12). -/
theorem invGetScanOK_merges_flat (p : Params) (hp : MergeParamsOK p)
    (hth : 2 ≤ p.theta ∨ p.theta = 0)
    (hchk : OpDelChk2OK p)
    (htb : TakeBelowFuelDelOK p)
    (d4 : OpCaseOK p (RunOK p) (QDead p) DelMergeCase)
    (t4 : OpCaseOK p (RunOK p) (QTree p) DelMergeCase)
    (i4 : OpCaseOK p (RunOK p) (QPutInv p) DelMergeCase)
    (r4 : OpCaseOK p (RunOK p) (QRange p) DelMergeCase)
    (l4 : OpCaseOK p (RunOK p) (QLive p) DelMergeCase)
    (hU : ∀ ts, UpUnlinkOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hL : ∀ ts, UpUnlinkLinksOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hFit : ∀ ts BK, UpCascFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) BK)
    (hLbF : ∀ ts BK,
      UpLebFullOKF3 (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) BK)
    (hFits : ∀ ts, DelFullFitsOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hMS : ∀ ts, MergeStepOKF3 (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hCo : ∀ ts, CollapseStepOKF4 (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hLbFJ : ∀ ts BK B,
      UpLebFullJ2OK (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) BK B)
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
  have hDd := opCaseOK_of_cases_merges p (RunOK p) _ hm (deadCase_putLeafRoom p _)
    (deadCase_putLeafFull p _ hRL hsa hth)
    (opCaseOK_putNewSeg_of_parts p _ _ (deadCase_putNewSeg1Room p _ (by omega))
      (deadCase_putNewSegsRoom p _ (by omega)) (deadCase_putNewSegFull p _ hRL (by omega) hsa hth)) d4
  -- the run induction: TP4, P's tree and LatestQD at every run
  have hR : ∀ P t, RunTreeQ p (LatestQD p) P t → RunOK p P t := runOK_of_runTreeQD p
  have hRL' : ∀ P t, RunTreeQ p (LatestQD p) P t → RunLinksOK p P t := fun _ _ h => h.1
  have hRT' : ∀ P t, RunTreeQ p (LatestQD p) P t → TreeAt p P t := fun _ _ h => h.2.1
  have hRI' : ∀ P t, RunTreeQ p (LatestQD p) P t → InvOK p P t := fun _ _ h => h.2.2.1.1
  have hRP' : ∀ P t, RunTreeQ p (LatestQD p) P t → PointersOK P := fun _ _ h => h.1.1
  have hRK' : ∀ P t, RunTreeQ p (LatestQD p) P t → KindsAllOK p P := fun _ _ h => h.2.2.1.2.2.1
  have hRH' : ∀ P t, RunTreeQ p (LatestQD p) P t → HeightAllOK p P t :=
    fun _ _ h => h.2.2.1.2.2.2.1
  -- the fuel at every state between operations (cost's `txSegFitsOK_of_takeBelowDelR2U`)
  have hfitQ : TxSegFitsOK p (RunTreeQ p (LatestQD p)) :=
    txSegFitsOK_of_takeBelowDelR2U p (by omega) _ hRP' hRL' hRK' hRH' hchk htb
  have hT' := opCaseOK_anti p _ _ hR _ _ hT
  have hPI' := opCaseOK_anti p _ _ hR _ _ hPI
  have hO' := opCaseOK_anti p _ _ hR _ _ hO
  have hJ := runTreeQ_of_mergesF4S p (by omega) hsa hcap hm (LatestQD p) (latestQD_init p (by omega))
    (latestQD_snocU p hp (opHtDelOKUnder_of_chk2 p (by omega) _ hRP' hRK' hchk) hT hPI hO hLv hDd)
    (fun _ _ h => h.1.2.1) (fun _ _ h => h.1.2.2.1)
    (opTreeOKUnder_of_cases p _ hRL' hRT' hRI' hT' hPI' hO')
    (putInvStateOK_of_cases p _ hRL' hRT' hRI' hT' hPI' hO')
    (rangeStateOK_of_cases p _ hRL' hRT' hRI' hT' hPI' hO')
    hfitQ
    (fun ts tx hw hr => hMF ts tx hw (hR _ _ hr))
    (delStepsJ2OKF3_of_openR3 p _ (TakeS4 p) (by omega) hsa hRL' hRP' hRK'
      (fun _ _ _ h => h.1.1.1.1) (fun _ _ _ h => h.1.1.1.2) (fun _ _ _ h => h.1.1.2)
      (fun _ _ _ h => h.1.2) (fun _ _ _ h => h.2.1) (fun _ _ _ h => h.2.2) hU hL hFit hLbF hLbFJ hFits)
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
      (delStepsOKF3_of_open8 p (RunOK p) (by omega) hsa hRL hP hU hL hFit hLbF hFits)
      hMS hCo hsa hcap (by omega) hP hfit)
  exact ⟨hinv, h.1, h.2, latestGetOK_of_getOK p h.1, latestScanOK_of_scanOK p h.2⟩

/-- Java's parameters (record format 7's thresholds and option 2's theta, from
node size 8) are parameters of the top theorem. -/
theorem mergeParamsOK_java (q : Params) (h : 8 ≤ q.M) : MergeParamsOK q.withMerges.withTheta :=
  mergeParamsOK_withMerges q h

/-- Java's theta is at least 2 from node size 8, so the top theorem's `hth` holds
for Java's parameters. -/
theorem theta_java (q : Params) (h : 8 ≤ q.M) :
    2 ≤ q.withMerges.withTheta.theta ∨ q.withMerges.withTheta.theta = 0 :=
  Or.inl (thetaFor_pos q.M h)

end SIS.Tree
