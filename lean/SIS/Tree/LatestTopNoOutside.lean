/-
The proof for the runs with no key node outside the level bounds (bergdb 025-03,
F1 of 026-16, section 4.2): `N.invGetScanOK_merges`, TP7, TP10 and TP11 for the
runs of `N.Within` (within reach and with `NoOutside`), from the premises of the
top theorem as it stood on 2026-11-14 (025-02) but `htb` (`TakeBelowFuelDelOK`).
In such a run every height the writer knows is at most H, so below the fuel
(`heights_le_H_of_noOutside`), which is what `htb` gave; the proof is that top
theorem's, over the run machinery for these runs (NoOutsideRun*.lean). The route's
top theorem, `invGetScanOK_merges_noOutside`, is in LatestTopMadeFor.lean.
-/
import SIS.Tree.NoOutsideRun3

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

namespace N

set_option maxHeartbeats 800000 in
/-- The top theorem as it stood on 2026-11-14 (025-02), for the runs of
`N.Within`, without its premise `htb`; its other premises as there. -/
theorem invGetScanOK_merges (p : Params) (hp : MergeParamsOK p)
    (hth : 2 ≤ p.theta ∨ p.theta = 0)
    (hchk : OpDelChk2OK p)
    (d4 : SIS.Tree.OpCaseOK p (RunOK p) (QDead p) DelMergeDOpenCase)
    (l4 : SIS.Tree.OpCaseOK p (RunOK p) (QLive p) DelMergeOpenCase)
    (hU : ∀ ts, UpUnlinkTreeOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hHL : ∀ ts, UpHolderLiveRunOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hMSF : ∀ ts, MergeFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hCoF : ∀ ts, CollapseFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hCoU : ∀ ts, CollapseUnlinkAllOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hMF : SIS.Tree.StateOK p (RunOK p) (fun _ tx w => ∀ x o, w.madeFor.lookup x = some o → o < tx.base)) :
    InvPreserved p ∧ GetOK p ∧ ScanOK p ∧ LatestGetOK p ∧ LatestScanOK p := by
  have hp' := hp
  unfold MergeParamsOK at hp'
  have hM := mergeParamsOK_M p hp
  have hm : p.merges = true := by
    unfold Params.merges; simp only [decide_eq_true_eq]; omega
  have hsa : 2 ≤ p.splitAbove := by omega
  have hcap : 1 ≤ p.mergeMax := by omega
  have hRL : ∀ P t, RunOK p P t → RunLinksOK p P t := fun _ _ h => h.1
  -- a merge's and a collapse's steps: the untaken part proved, the fuel and unlink parts named
  have hMS : ∀ ts, MergeStepOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1) :=
    fun ts => mergeStepOK_of_segFits (ctxOf p ts) _ _ (Nat.succ_pos _) hcap hsa (hMSF ts)
  have hCo : ∀ ts, CollapseStepOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1) :=
    fun ts => ⟨hCoF ts, hCoU ts⟩
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
    txSegFitsOK_of_takeBelowDelR2U p (by omega) _ hRP' hRL' hRK' hRH' hchk
  have hht : OpHtDelOKUnder p (RunTreeQ p (LatestQD p)) :=
    opHtDelOKUnder_of_chk2 p (by omega) _ hRP' hRK' hchk
  -- the delete with the merges (4) at the induction's runs
  have hTIR := opCaseOK_treeInvRange_delMergeRL p _
    (delStepsQdL_of_openR p _ (by omega) hsa hRL' hRP' hRK' hRH' hht hU hHL) hMS hCo hsa hcap
    hRP' hRK' hfitQ
  -- the premises over every run, for the runs of `N.Within`
  have l4N : OpCaseOK p (RunOK p) (QLive p) DelMergeOpenCase := OpCaseOK.ofOld l4
  have d4N : OpCaseOK p (RunOK p) (QDead p) DelMergeDOpenCase := OpCaseOK.ofOld d4
  have l4' := opCaseOK_anti p _ _ hR _ _
    (liveCase_delMerge_of_rest p (RunOK p) hRL
      (opCaseOK_of_open p (RunOK p) (QLive p) (keptByReads_live p) DelMergeRestCase l4N))
  have d4' := opCaseOK_anti p _ _ hR _ _ (deadCase_delMergeL_of_rest p (RunOK p) hRL
    (opCaseOK_of_open p (RunOK p) (QDead p) (keptByReads_dead p) DelMergeDRestCase d4N))
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
  have hDdL := opCaseOK_of_cases_mergesL p _ _ hm (deadCase_putLeafRoom p _)
    (deadCase_putLeafFull p _ hRL' hsa hth)
    (opCaseOK_putNewSeg_of_parts p _ _ (deadCase_putNewSeg1Room p _ (by omega))
      (deadCase_putNewSegsRoom p _ (by omega)) (deadCase_putNewSegFull p _ hRL' (by omega) hsa hth)) d4'
  -- the live counts at every operation's start, and so the cases at every operation
  have hLvL := opCaseOK_L_of_any p _ _ hLv
  have hT := opCaseOK_any_of_L p _ hRL' hRT' hRI' hTL hPIL hOL hLvL _ hTL
  have hPI := opCaseOK_any_of_L p _ hRL' hRT' hRI' hTL hPIL hOL hLvL _ hPIL
  have hO := opCaseOK_any_of_L p _ hRL' hRT' hRI' hTL hPIL hOL hLvL _ hOL
  have hLC := liveStateOK_of_L p _ hRL' hRT' hRI' hTL hPIL hOL hLvL
  have hDd := opCaseOK_any_of_L p _ hRL' hRT' hRI' hTL hPIL hOL hLvL _ hDdL
  -- the run induction
  have hJ := runTreeQ_of_mergesS p (by omega) hsa hcap hm (LatestQD p) (latestQD_init p (by omega))
    (latestQD_snocR p hp hht hT hPI hO hLv hDd)
    (fun _ _ h => h.1.2.1) (fun _ _ h => h.1.2.2.1)
    (opTreeOKUnder_of_cases p _ hRL' hRT' hRI' hT hPI hO)
    (putInvStateOK_of_cases p _ hRL' hRT' hRI' hT hPI hO)
    (rangeStateOK_of_cases p _ hRL' hRT' hRI' hT hPI hO)
    hfitQ
    (fun ts tx hw hr => hMF ts tx hw.w (hR _ _ hr))
    (delStepsJ2OK_of_openR p _ (TakeS4 p) (by omega) hsa hRL' hRP' hRK'
      (fun _ _ _ h => h.1.1.1.1) (fun _ _ _ h => h.1.1.1.2) (fun _ _ _ h => h.1.1.2)
      (fun _ _ _ h => h.1.2) (fun _ _ _ h => h.2.1) (fun _ _ _ h => h.2.2) hRH' hht hU hHL hLC)
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
    (opGetCaseOK_delMerge p (RunOK p)
      (delStepsOK_of_within p (RunOK p) _ hW
        (delStepsOK_of_open p _ (by omega) hsa hRL' hP hRK' hRH' hht hU hHL hLC))
      hMS hCo hsa hcap (by omega) hP hfit)
  exact ⟨hinv, h.1, h.2, latestGetOK_of_getOK p h.1, latestScanOK_of_scanOK p h.2⟩

end N

end SIS.Tree
