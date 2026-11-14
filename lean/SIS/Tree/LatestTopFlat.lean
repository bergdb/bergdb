/-
The top theorem with the flattest list of named premises (bergdb 024-12):
`invGetScanOK_merges_flat`. It is `invGetScanOK_merges` with its premises
taken apart (10 named premises left, with `hp` and `hth` on the parameters):

* the bound on dead klongs at every run (`hD`) comes from the operations: every
  put keeps it, for theta 0 or at least 2 (`hth`; `deadCase_putLeafRoom`,
  `DeadCases.lean`, `DeadPutFull.lean`, `DeadNewSegFull.lean`, with the cascade's
  dead counts `writerWP_appendKlongs_chainDead`), and `QDead` of (4) is a premise
  (`DeadRun.lean`; the run induction carries `DeadAllOK` in `LatestQD`);
* the take-back's delete steps (`hDS`) come from their open pieces (putinv's
  `delStepsJ2OKF3_of_openR9` over `TakeS4`, `runTreeQ_of_mergesF4S`): the
  upward delete's stop node for the take-back, the made-for ids at every state
  between operations (`hMF`), and the fuel there;
* the take-back through a replaceRoot whose segment leaf is full (`hRJ`) is
  proved (putinv's `replaceRootFullJ2OK_run`);
* the upward delete's stop node is proved, its cascade and its LE-b with room
  or full, for the reading (putinv's `delStepsOKF3_of_open14`, at the runs of
  the induction, every run within reach) and for the take-back
  (`delStepsJ2OKF3_of_openR9`), from `hU` (the state after the upward loop is a
  tree), `hHo` (cost's `UpHolderOK` at the loop's end) and `hG` (the loop keeps
  the heights' cache), which give the fuel after the stop node's cascade
  (cost's `upCascFitsOKR_of`); the links
  and klongs after the upward loop follow from the writer's books, and the
  cascade's ranges from the tree; the fuel after a full leaf's split comes from
  the heights (cost's `delFullFitsOKR_run`, through putinv's walk with the
  heights' invariant);
* the fuel at every state between operations (`hfit`) comes from the heights
  (cost's `txSegFitsOK_of_takeBelowDelR2U`): every node a delete takes back has a
  height below the fuel (`TakeBelowFuelDelOK`; a put takes nothing back).

* TP10's three posts for the delete with the merges (4), `t4`, `i4` and `r4`,
  are proved at the induction's runs (putinv's
  `opCaseOK_treeInvRange_delMergeR`), and carried with TP7's live counts along
  each transaction (`LiveJointL.lean`);
* LE-b at the upward delete's stop node never runs with the merges on, given
  TP7's live counts at the delete's start (cost's `stopLeaf_of_liveCounts`,
  putinv's `lebStop_false`; `delStepsOKF3_of_open13`,
  `delStepsJ2OKF3_of_openR8`, `delStepsQdL_of_openR`), which the joint
  induction along each transaction gives (`liveStateOK_of_L`).

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
import SIS.Tree.DelStepsLinks
import SIS.Tree.DelStepsUnlinkTree
import SIS.Tree.DelStepsFullH
import SIS.Tree.LiveJointL
import SIS.Tree.DelStepsTree
import SIS.Tree.DelStepsLive
import SIS.Tree.DelStepsHolder
import SIS.Tree.LiveDelRoom

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- `DelStepsOKF3` at the runs of R from it at the runs of R', where every run
within reach is one of R'. -/
theorem delStepsOKF3_of_within (p : Params) (R R' : Struct BVal → Time → Prop)
    (h : ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → R' (treeRun p ts) ts.length)
    (hS : DelStepsOKF3 p R') : DelStepsOKF3 p R :=
  fun ts tx hw hr => hS ts tx hw (h ts tx hw hr)

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

/-- `OpCaseOK` at the runs of R from it at the runs of R', where every run
within reach is one of R'. -/
theorem opCaseOK_of_within (p : Params) (R R' : Struct BVal → Time → Prop)
    (h : ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → R' (treeRun p ts) ts.length)
    (Q : List Tx → Op → W → W → Prop) (C : Ctx → View BVal → W → Op → Prop)
    (hC : OpCaseOK p R' Q C) : OpCaseOK p R Q C :=
  fun ts tx hw hr => hC ts tx hw (h ts tx hw hr)

/-- `latestQD_snoc` with the delete side of the heights, and the operations'
cases, only at the runs of the induction. -/
theorem latestQD_snocR (p : Params) (hp : MergeParamsOK p)
    (hdel : OpHtDelOKUnder p (RunTreeQ p (LatestQD p)))
    (hT : OpCaseOK p (RunTreeQ p (LatestQD p)) (QTree p) AnyOp)
    (hPI : OpCaseOK p (RunTreeQ p (LatestQD p)) (QPutInv p) AnyOp)
    (hO : OpCaseOK p (RunTreeQ p (LatestQD p)) (QRange p) AnyOp)
    (hLv : OpCaseOK p (RunTreeQ p (LatestQD p)) (QLive p) AnyOp)
    (hDd : OpCaseOK p (RunTreeQ p (LatestQD p)) (QDead p) AnyOp) :
    ∀ ts tx, Within p (ts ++ [tx]) → RunTreeQ p (LatestQD p) (treeRun p ts) ts.length →
      RunLinksOK p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      TreeAt p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      LatestQD p (treeRun p (ts ++ [tx])) (ts.length + 1) := by
  intro ts tx hw hr hL' hT'
  have hM := mergeParamsOK_M p hp
  have hr0 := hr
  have hRL : ∀ P t, RunTreeQ p (LatestQD p) P t → RunLinksOK p P t := fun _ _ h => h.1
  have hRT : ∀ P t, RunTreeQ p (LatestQD p) P t → TreeAt p P t := fun _ _ h => h.2.1
  have hRI : ∀ P t, RunTreeQ p (LatestQD p) P t → InvOK p P t := fun _ _ h => h.2.2.1.1
  obtain ⟨hL, _, ⟨_, _, hK, hA, hS, hLA⟩, hD⟩ := hr
  have hD' := deadAllOK_snocR p _ hRL hRT hRI hT hPI hO hDd ts tx hw hr0 hD
  have hK' := kindsAllOK_snoc p (by omega) ts tx hw hL hK
  have hA' := heightAllOK_snocU p (by omega) _ hdel ts tx hw hr0 hL hK hA
  have hS' := sizeOK_snoc p hp ts tx hw hL hS
  have hLA' := leftAllOK_snoc p hp ts tx hw hL hLA
  exact ⟨⟨invOK_snocR p _ hRL hRT hRI hT hPI hO hLv ts tx hw hr0 hL' hT' hK' hA' hS' hLA' hD',
    hL'.1, hK', hA', hS', hLA'⟩, hD'⟩

/-- `latestQD_snocR` with the operations' cases at `RunOK`. -/
theorem latestQD_snocU (p : Params) (hp : MergeParamsOK p)
    (hdel : OpHtDelOKUnder p (RunTreeQ p (LatestQD p)))
    (hT : OpCaseOK p (RunOK p) (QTree p) AnyOp) (hPI : OpCaseOK p (RunOK p) (QPutInv p) AnyOp)
    (hO : OpCaseOK p (RunOK p) (QRange p) AnyOp) (hLv : OpCaseOK p (RunOK p) (QLive p) AnyOp)
    (hDd : OpCaseOK p (RunOK p) (QDead p) AnyOp) :
    ∀ ts tx, Within p (ts ++ [tx]) → RunTreeQ p (LatestQD p) (treeRun p ts) ts.length →
      RunLinksOK p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      TreeAt p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      LatestQD p (treeRun p (ts ++ [tx])) (ts.length + 1) :=
  latestQD_snocR p hp hdel (opCaseOK_anti p _ _ (runOK_of_runTreeQD p) _ _ hT)
    (opCaseOK_anti p _ _ (runOK_of_runTreeQD p) _ _ hPI) (opCaseOK_anti p _ _ (runOK_of_runTreeQD p) _ _ hO)
    (opCaseOK_anti p _ _ (runOK_of_runTreeQD p) _ _ hLv) (opCaseOK_anti p _ _ (runOK_of_runTreeQD p) _ _ hDd)

set_option maxHeartbeats 800000 in
/-- TP7, TP10 and TP11, and the latest time's get and scan, for the parameters
of `MergeParamsOK`, from the flat list of named premises (section 1 of
024-12). -/
theorem invGetScanOK_merges_flat (p : Params) (hp : MergeParamsOK p)
    (hth : 2 ≤ p.theta ∨ p.theta = 0)
    (hchk : OpDelChk2OK p)
    (htb : TakeBelowFuelDelOK p)
    (d4 : OpCaseOK p (RunOK p) (QDead p) DelMergeCase)
    (l4 : OpCaseOK p (RunOK p) (QLive p) DelMergeRestCase)
    (hU : ∀ ts, UpUnlinkTreeOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hHo : ∀ ts B, UpHolderRunOK (ctxOf p ts) (viewOf (treeRun p ts)) B)
    (hG : ∀ ts, UpGhOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hMS : ∀ ts, MergeStepOKF3 (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hCo : ∀ ts, CollapseStepOKF4 (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
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
  -- the induction's runs: TP4, P's tree and LatestQD
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
  have hht : OpHtDelOKUnder p (RunTreeQ p (LatestQD p)) :=
    opHtDelOKUnder_of_chk2 p (by omega) _ hRP' hRK' hchk
  -- the delete with the merges (4) at the induction's runs
  have hTIR := opCaseOK_treeInvRange_delMergeRL p _
    (delStepsQdL_of_openR2 p _ (by omega) hsa hRL' hRP' hRK' hRH' hht htb hU hHo hG) hMS hCo hsa hcap
    hRP' hRK' hfitQ
  have l4' := opCaseOK_anti p _ _ hR _ _
    (liveCase_delMerge_of_rest p (RunOK p) hRL (by omega) l4)
  have d4' := opCaseOK_anti p _ _ hR _ _ d4
  -- TP10's three posts for every operation from a state with TP7's live counts
  have hTL := opCaseOK_of_cases_mergesL p _ _ hm (treeCase_putLeafRoom p _)
    (treeCase_putLeafFull p _ hRL' hsa)
    (opCaseOK_putNewSeg_of_parts p _ _ (treeCase_putNewSeg1Room p _ (by omega))
      (treeCase_putNewSegsRoom p _ (by omega)) (treeCase_putNewSegFull p _ hRL' (by omega) hsa))
    hTIR.1
  have hPIL := opCaseOK_of_cases_mergesL p _ _ hm (putInvCase_putLeafRoom p _ hRL')
    (putInvCase_putLeafFull p _ hRL' hsa)
    (opCaseOK_putNewSeg_of_parts p _ _ (putInvCase_putNewSeg1Room p _ hRL' (by omega))
      (putInvCase_putNewSegsRoom p _ hRL' (by omega)) (putInvCase_putNewSegFull p _ hRL' (by omega) hsa))
    hTIR.2.1
  have hOL := opCaseOK_of_cases_mergesL p _ _ hm (rangeCase_putLeafRoom p _)
    (rangeCase_putLeafFull p _ hRL' hsa)
    (opCaseOK_putNewSeg_of_parts p _ _ (rangeCase_putNewSeg1Room p _ (by omega))
      (rangeCase_putNewSegsRoom p _ (by omega)) (rangeCase_putNewSegFull p _ hRL' (by omega) hsa))
    hTIR.2.2
  have hLv := opCaseOK_of_cases_merges p _ _ hm (liveCase_putLeafRoom p _)
    (liveCase_putLeafFull p _ hRL' hsa hp)
    (opCaseOK_putNewSeg_of_parts p _ _ (liveCase_putNewSeg1Room p _ (by omega))
      (liveCase_putNewSegsRoom p _ (by omega)) (liveCase_putNewSegFull p _ hRL' (by omega) hsa hp)) l4'
  have hDd := opCaseOK_of_cases_merges p _ _ hm (deadCase_putLeafRoom p _)
    (deadCase_putLeafFull p _ hRL' hsa hth)
    (opCaseOK_putNewSeg_of_parts p _ _ (deadCase_putNewSeg1Room p _ (by omega))
      (deadCase_putNewSegsRoom p _ (by omega)) (deadCase_putNewSegFull p _ hRL' (by omega) hsa hth)) d4'
  -- the live counts at every operation's start, and so the cases at every operation
  have hLvL := opCaseOK_L_of_any p _ _ hLv
  have hT := opCaseOK_any_of_L p _ hRL' hRT' hRI' hTL hPIL hOL hLvL _ hTL
  have hPI := opCaseOK_any_of_L p _ hRL' hRT' hRI' hTL hPIL hOL hLvL _ hPIL
  have hO := opCaseOK_any_of_L p _ hRL' hRT' hRI' hTL hPIL hOL hLvL _ hOL
  have hLC := liveStateOK_of_L p _ hRL' hRT' hRI' hTL hPIL hOL hLvL
  -- the run induction
  have hJ := runTreeQ_of_mergesF4S p (by omega) hsa hcap hm (LatestQD p) (latestQD_init p (by omega))
    (latestQD_snocR p hp hht hT hPI hO hLv hDd)
    (fun _ _ h => h.1.2.1) (fun _ _ h => h.1.2.2.1)
    (opTreeOKUnder_of_cases p _ hRL' hRT' hRI' hT hPI hO)
    (putInvStateOK_of_cases p _ hRL' hRT' hRI' hT hPI hO)
    (rangeStateOK_of_cases p _ hRL' hRT' hRI' hT hPI hO)
    hfitQ
    (fun ts tx hw hr => hMF ts tx hw (hR _ _ hr))
    (delStepsJ2OKF3_of_openR9 p _ (TakeS4 p) (by omega) hsa hRL' hRP' hRK'
      (fun _ _ _ h => h.1.1.1.1) (fun _ _ _ h => h.1.1.1.2) (fun _ _ _ h => h.1.1.2)
      (fun _ _ _ h => h.1.2) (fun _ _ _ h => h.2.1) (fun _ _ _ h => h.2.2) hRH' hht htb hU hHo hG hLC)
    hMS hCo (replaceRootFullJ2OK_run p hsa)
  have hW : ∀ ts tx, Within p (ts ++ [tx]) → RunOK p (treeRun p ts) ts.length →
      RunTreeQ p (LatestQD p) (treeRun p ts) ts.length :=
    fun ts tx hw _ => hJ ts (within_snoc_prefix p ts tx hw)
  -- TP7, TP10 and TP11 from it
  have hP : ∀ ts, Within p ts → PointersOK (treeRun p ts) := fun ts hw => (hJ ts hw).1.1
  have hfit : TxSegFitsOK p (RunOK p) :=
    fun ts tx hw _ => hfitQ ts tx hw (hJ ts (within_snoc_prefix p ts tx hw))
  have hinv : InvPreserved p :=
    invPreserved_of_latest_pointers p hp (fun ts hw => (hJ ts hw).2.2.1.1) hP
      (fun ts hw => (hJ ts hw).2.2.2)
  have h := getOK_scanOK_of_cases_merges_open p hp hinv (fun ts hw => (hJ ts hw).1)
    (fun ts hw => (hJ ts hw).2.1) hfit
    (opCaseOK_of_within p _ _ hW _ _ (opCaseOK_of_any p _ _ _ hT))
    (opCaseOK_of_within p _ _ hW _ _ (opCaseOK_of_any p _ _ _ hPI))
    (opCaseOK_of_within p _ _ hW _ _ (opCaseOK_of_any p _ _ _ hO))
    (opGetCaseOK_delMergeF4 p (RunOK p)
      (delStepsOKF3_of_within p (RunOK p) _ hW
        (delStepsOKF3_of_open14 p _ (by omega) hsa hRL' hP hRK' hRH' hht htb hU hHo hG hLC))
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
