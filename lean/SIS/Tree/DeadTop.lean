/-
The joint route's top theorem without `hU` and `d4` (bergdb 024-12, section 1,
`d4`'s plan of 2026-11-15): `invGetScanOK_merges_noU` with the dead klongs' bound
of a delete with the merges proved in the joint induction (`DW`, DeadLocal.lean
to DeadDelCases.lean) in place of its premise `d4`.
-/
import SIS.Tree.DeadDelCases
import SIS.Tree.CollapseCommuteTop
import SIS.Tree.DelMergeUp
import SIS.Tree.FuelNext
import SIS.Tree.StratumChk

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- `htb` at the deletes of the runs of R whose start has the first stratum's facts
(bergdb 025-05, step 8's claim): every node the delete finds at its start and takes
back has a cached height below the fuel. -/
def TakeBelowFuelDelS (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre key post, tx.ops = pre ++ Op.del key :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w →
    RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey →
    LiveCounts p (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey →
    HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) w →
    WriterTreeOK p (treeRun p ts) (ts.length + 1) w →
    J2At p (treeRun p ts) (ts.length + 1) tx.base w →
    ∀ a v, putKv (.del key) (ctxOf p ts) w = .ok (a, v) →
    ∀ x g h, (x, g, h) ∈ w.gh → w.taken.contains x = false → v.taken.contains x = true →
      h < p.fuel

/-- `TakeBelowFuelDelS` at the induction's runs. -/
def TakeBelowFuelDelSL (p : Params) : Prop := TakeBelowFuelDelS p (RunTreeQ p (LatestQD p))

/-- `htb` gives its case at the induction's runs. -/
theorem takeBelowFuelDelSL_of (p : Params) (h : TakeBelowFuelDelOK p) : TakeBelowFuelDelSL p :=
  fun ts tx hw _ z top hz htop pre key post hs r w hpre _ _ _ _ _ _ a v he x g h' hm hx hv =>
    h ts tx hw z top hz htop pre key post hs r w hpre a v he x g h' hm hx hv

set_option maxHeartbeats 3200000 in
/-- The joint route's top theorem with `htb` reduced to its case at one delete (bergdb
025-05, step 9): TP7, TP10 and TP11 for Java's parameters from `hp`, `hth`, `l4` and
`htbL`, `htb` at the deletes of the induction's runs whose start has the first
stratum's facts (`TakeBelowFuelDelSL`). The first stratum (`jointHtJ_reached1`) gives
`PutInv`, the ranges, the fill, the heights' walk, the writer's tree and the take-back's
node facts at every state with no `htb`, and `hchk` with no `htb` (`opDelChk5OKR_T`);
with them `htbL` gives `htb` at the run (`TakeBelowFuelDelR`), from which the bound
between operations and the fit follow as before (`htStart_reachedUR`). -/
theorem invGetScanOK_merges_tbL (p : Params) (hp : MergeParamsOK p)
    (hth : 2 ≤ p.theta ∨ p.theta = 0)
    (htbL : TakeBelowFuelDelSL p)
    (l4 : OpCaseOK p (RunOK p) (QLive p) DelMergeOpenCase) :
    InvPreserved p ∧ GetOK p ∧ ScanOK p ∧ LatestGetOK p ∧ LatestScanOK p := by
  have hp' := hp
  unfold MergeParamsOK at hp'
  have hM := mergeParamsOK_M p hp
  have hM4 := four_le_M p hp
  have hm : p.merges = true := by
    unfold Params.merges; simp only [decide_eq_true_eq]; omega
  have hsa : 2 ≤ p.splitAbove := by omega
  have hcap : 1 ≤ p.mergeMax := by omega
  have hRL : ∀ P t, RunOK p P t → RunLinksOK p P t := fun _ _ h => h.1
  have hR : ∀ P t, RunTreeQ p (LatestQD p) P t → RunOK p P t := runOK_of_runTreeQD p
  have hRL' : ∀ P t, RunTreeQ p (LatestQD p) P t → RunLinksOK p P t := fun _ _ h => h.1
  have hRT' : ∀ P t, RunTreeQ p (LatestQD p) P t → TreeAt p P t := fun _ _ h => h.2.1
  have hRI' : ∀ P t, RunTreeQ p (LatestQD p) P t → InvOK p P t := fun _ _ h => h.2.2.1.1
  have hRP' : ∀ P t, RunTreeQ p (LatestQD p) P t → PointersOK P := fun _ _ h => h.1.1
  have hRK' : ∀ P t, RunTreeQ p (LatestQD p) P t → KindsAllOK p P := fun _ _ h => h.2.2.1.2.2.1
  have hRH' : ∀ P t, RunTreeQ p (LatestQD p) P t → HeightAllOK p P t :=
    fun _ _ h => h.2.2.1.2.2.2.1
  have hchk5 : OpDelChk5OKL p := opDelChk5OKR_T p _ hM4 hsa hcap hm hRL' hRP' hRK'
  have l4' := opCaseOK_anti p _ _ hR _ _
    (liveCase_delMerge_of_rest p (RunOK p) hRL
      (opCaseOK_of_open p (RunOK p) (QLive p) (keptByReads_live p) DelMergeRestCase l4))
  -- the joint induction's cases
  have hLv := opCaseOK_of_cases_merges p _ _ hm (liveCase_putLeafRoom p _)
    (liveCase_putLeafFull p _ hRL' hsa hp)
    (opCaseOK_putNewSeg_of_parts p _ _ (liveCase_putNewSeg1Room p _ (by omega))
      (liveCase_putNewSegsRoom p _ (by omega)) (liveCase_putNewSegFull p _ hRL' (by omega) hsa hp)) l4'
  have hTp := opCaseOK_put_of_cases p _ _ hm (treeCase_putLeafRoom p _)
    (treeCase_putLeafFull p _ hRL' hsa)
    (opCaseOK_putNewSeg_of_parts p _ _ (treeCase_putNewSeg1Room p _ (by omega))
      (treeCase_putNewSegsRoom p _ (by omega)) (treeCase_putNewSegFull p _ hRL' (by omega) hsa))
  have hPp := opCaseOK_put_of_cases p _ _ hm (putInvCase_putLeafRoom p _ hRL')
    (putInvCase_putLeafFull p _ hRL' hsa)
    (opCaseOK_putNewSeg_of_parts p _ _ (putInvCase_putNewSeg1Room p _ hRL' (by omega))
      (putInvCase_putNewSegsRoom p _ hRL' (by omega)) (putInvCase_putNewSegFull p _ hRL' (by omega) hsa))
  have hOp := opCaseOK_put_of_cases p _ _ hm (rangeCase_putLeafRoom p _)
    (rangeCase_putLeafFull p _ hRL' hsa)
    (opCaseOK_putNewSeg_of_parts p _ _ (rangeCase_putNewSeg1Room p _ (by omega))
      (rangeCase_putNewSegsRoom p _ (by omega)) (rangeCase_putNewSegFull p _ hRL' (by omega) hsa))
  have hchkR := opDelChk2ORJ_of_chk5 p _ hm hM4 hRL' hchk5
  have joint := jointHtJ_reached1 p _ hm (by omega) hM4 hsa hcap (baseStartOK_runTreeQ p (LatestQD p)) hRL' hRT'
    hRI' hRP' hRK' hRH' hTp hPp hOp hLv
  -- from the joint induction: the heights' delete side, the fuel, the cases at every operation
  have hht : OpHtDelOKUnder p (RunTreeQ p (LatestQD p)) := by
    intro ts tx hw hr z top hz htop pre key post hsplit r w hpre hvo hkw hb hwf hi r' v he
    obtain ⟨hI, hRo, hL, _, _, hJ⟩ := joint ts tx hw hr z top hz htop pre (Op.del key :: post) hsplit r w hpre
    have hc := hchkR ts tx hw hr z top hz htop pre key post hsplit r w hpre hI hRo hL hi hJ r' v he
    obtain ⟨-, hk, -, hki⟩ := kd_contextR p (by omega) ts tx (hRP' _ _ hr) (hRK' _ _ hr) hw top pre
      (Op.del key :: post) hsplit r w hpre
    exact (ht_putKvDelChk2 tx.base key (ctxOf p ts) w hvo (by simp [ctxOf]) hkw hb hi hwf hk hki
      (by simpa [ctxOf] using (show 2 ≤ p.M by omega)) r' v hc).2.1
  have htbR : TakeBelowFuelDelR p (RunTreeQ p (LatestQD p)) := by
    intro ts tx hw hr z top hz htop pre key post hs r w hpre a v he x g h hm' hx hv
    obtain ⟨hI, hRo, hL, hH, hT, hJ⟩ := joint ts tx hw hr z top hz htop pre (Op.del key :: post) hs r w hpre
    exact htbL ts tx hw hr z top hz htop pre key post hs r w hpre hI hRo hL hH hT hJ a v he x g h hm' hx hv
  have hfitQ : TxSegFitsOK p (RunTreeQ p (LatestQD p)) :=
    txSegFitsOK_of_takeBelowDelRHUR p (by omega) _ hRL' hRK' hRH' hht htbR
  have hnext : ∀ ts tx, Within p (ts ++ [tx]) → RunTreeQ p (LatestQD p) (treeRun p ts) ts.length →
      ∀ z top, lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
      topOf p (ctxOf p ts).view z = .ok top →
      ∀ pre op post, tx.ops = pre ++ op :: post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) → ∀ a w', putKv op (ctxOf p ts) w = .ok (a, w') →
      WriterTreeOK p (treeRun p ts) (ts.length + 1) w' ∧
        PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w' ∧
        RangeOrder (wNode p (viewOf (treeRun p ts)) w') (ts.length + 1) w'.top.rootKey := by
    intro ts tx hw hr z top hz htop pre op post hs r w hpre a w' he
    obtain ⟨hI', hR', _, _, hT', _⟩ := joint ts tx hw hr z top hz htop (pre ++ [op]) post (by rw [hs]; simp)
      (r ++ [a]) w' (mapM_snoc_ok _ _ pre op r w a w' hpre he)
    exact ⟨hT', hI', hR'⟩
  have hT : OpCaseOK p (RunTreeQ p (LatestQD p)) (QTree p) AnyOp :=
    fun ts tx hw hr z top hz htop pre op post hs r w hpre _ _ _ a w' he =>
      (hnext ts tx hw hr z top hz htop pre op post hs r w hpre a w' he).1
  have hPI : OpCaseOK p (RunTreeQ p (LatestQD p)) (QPutInv p) AnyOp :=
    fun ts tx hw hr z top hz htop pre op post hs r w hpre _ _ _ a w' he _ =>
      (hnext ts tx hw hr z top hz htop pre op post hs r w hpre a w' he).2.1
  have hO : OpCaseOK p (RunTreeQ p (LatestQD p)) (QRange p) AnyOp :=
    fun ts tx hw hr z top hz htop pre op post hs r w hpre _ _ _ a w' he _ =>
      (hnext ts tx hw hr z top hz htop pre op post hs r w hpre a w' he).2.2
  have hLC : StateOK p (RunTreeQ p (LatestQD p)) (fun ts _ w => LiveCountsW p ts w) :=
    fun ts tx hw hr z top hz htop pre post hs r w hpre =>
      (joint ts tx hw hr z top hz htop pre post hs r w hpre).2.2.1
  have hJ2S : StateOK p (RunTreeQ p (LatestQD p))
      (fun ts tx w => TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w) :=
    fun ts tx hw hr z top hz htop pre post hs r w hpre =>
      (joint ts tx hw hr z top hz htop pre post hs r w hpre).2.2.2.2.2
  have hMFS := stateOK_madeFor p hM4 (RunTreeQ p (LatestQD p)) hRL'
  -- the delete's steps without `hHL`
  have d4' : OpCaseOK p (RunTreeQ p (LatestQD p)) (QDead p) (fun c base w op =>
      DelMergeCase c base w op ∧ LiveCounts c.p (wNode c.p base w) c.i w.top.rootKey) :=
    fun ts tx hw hr z top hz htop pre op post hops r w hpre hI hRo hP =>
      opCaseOK_dead_delMergeA p _ (delStepsCaseDOK_mergeGR p _ (by omega) hsa hRL' hRP' hRK' hRH' hht htbR
        hLC hJ2S hMFS _) hsa hcap hRP' hRK' hfitQ hth ts tx hw hr z top hz htop pre op post hops
        r w hpre hI hRo hP.1
  have hTL := opCaseOK_L_of_any p _ _ hT
  have hPIL := opCaseOK_L_of_any p _ _ hPI
  have hOL := opCaseOK_L_of_any p _ _ hO
  have hLvL := opCaseOK_L_of_any p _ _ hLv
  have hDdL := opCaseOK_of_cases_mergesL p _ _ hm (deadCase_putLeafRoom p _)
    (deadCase_putLeafFull p _ hRL' hsa hth)
    (opCaseOK_putNewSeg_of_parts p _ _ (deadCase_putNewSeg1Room p _ (by omega))
      (deadCase_putNewSegsRoom p _ (by omega)) (deadCase_putNewSegFull p _ hRL' (by omega) hsa hth)) d4'
  have hDd := opCaseOK_any_of_L p _ hRL' hRT' hRI' hTL hPIL hOL hLvL _ hDdL
  have hJ := runTreeQ_of_mergesSA p (by omega) hsa hcap hm (LatestQD p) (latestQD_init p (by omega))
    (latestQD_snocR p hp hht hT hPI hO hLv hDd)
    (fun _ _ h => h.1.2.1) (fun _ _ h => h.1.2.2.1)
    (opTreeOKUnder_of_cases p _ hRL' hRT' hRI' hT hPI hO)
    (putInvStateOK_of_cases p _ hRL' hRT' hRI' hT hPI hO)
    (rangeStateOK_of_cases p _ hRL' hRT' hRI' hT hPI hO)
    hfitQ hMFS
    (delStepsJ2OKJ_of_openR_noUGR p _ (TakeS4 p) (by omega) hsa hRL' hRP' hRK'
      (fun _ _ _ h => h.1.1.1.1) (fun _ _ _ h => h.1.1.1.2) (fun _ _ _ h => h.1.1.2)
      (fun _ _ _ h => h.1.2) (fun _ _ _ h => h.2.1) (fun _ _ _ h => h.2.2) hRH' hht htbR hLC _)
  have hW : ∀ ts tx, Within p (ts ++ [tx]) → RunOK p (treeRun p ts) ts.length →
      RunTreeQ p (LatestQD p) (treeRun p ts) ts.length :=
    fun ts tx hw _ => hJ ts (within_snoc_prefix p ts tx hw)
  have hP : ∀ ts, Within p ts → PointersOK (treeRun p ts) := fun ts hw => (hJ ts hw).1.1
  have hfit : TxSegFitsOK p (RunOK p) :=
    fun ts tx hw _ => hfitQ ts tx hw (hJ ts (within_snoc_prefix p ts tx hw))
  have hSA : DelStepsOKA p (RunOK p) := fun ts tx hw hr =>
    delStepsOKJ_of_open_noUGR p _ (by omega) hsa hRL' hP hRK' hRH' hht htbR hLC hJ2S hMFS
      (fun ts tx w key v => DelInvA (ctxOf p ts) (viewOf (treeRun p ts)) w key
        (kindOracleOf p (treeRun p ts)) tx.base v) ts tx hw (hW ts tx hw hr)
  have hinv : InvPreserved p :=
    invPreserved_of_latest_pointers p hp (fun ts hw => (hJ ts hw).2.2.1.1) hP
      (fun ts hw => (hJ ts hw).2.2.2)
  have h := getOK_scanOK_of_cases_merges_open p hp hinv (fun ts hw => (hJ ts hw).1)
    (fun ts hw => (hJ ts hw).2.1) hfit
    (opCaseOK_of_within p _ _ hW _ _ (opCaseOK_of_any p _ _ _ hT))
    (opCaseOK_of_within p _ _ hW _ _ (opCaseOK_of_any p _ _ _ hPI))
    (opCaseOK_of_within p _ _ hW _ _ (opCaseOK_of_any p _ _ _ hO))
    (opGetCaseOK_delMergeA p (RunOK p) hSA hsa hcap (by omega) hP hfit)
  exact ⟨hinv, h.1, h.2, latestGetOK_of_getOK p h.1, latestScanOK_of_scanOK p h.2⟩


/-- The joint route's top theorem without `hMSF` and `hCoF` (bergdb 025-05, route P):
TP7, TP10 and TP11 for Java's parameters from `hp`, `hth`, `htb` and `l4`. Every
writer state with `PutInv` fits its next id (FuelNext.lean, P1), so inside a delete
each family reads at every fuel above p.fuel and the next id (`DelInvA`), which the
merges' loop and root collapse keep with no fit premise; the fit p.fuel - 1 is asked
only at the operation's end, where it holds between operations. As
`invGetScanOK_merges_noU_noD4` with `hchk5` discharged as in
`invGetScanOK_merges_free_noD4`, each consumer of `MergeStepOK` and `CollapseFitsOK`
replaced by its route P form. -/
theorem invGetScanOK_merges_noFit (p : Params) (hp : MergeParamsOK p)
    (hth : 2 ≤ p.theta ∨ p.theta = 0)
    (htb : TakeBelowFuelDelOK p)
    (l4 : OpCaseOK p (RunOK p) (QLive p) DelMergeOpenCase) :
    InvPreserved p ∧ GetOK p ∧ ScanOK p ∧ LatestGetOK p ∧ LatestScanOK p :=
  invGetScanOK_merges_tbL p hp hth (takeBelowFuelDelSL_of p htb) l4

set_option maxHeartbeats 3200000 in
/-- `invGetScanOK_merges_noU` without `d4` (bergdb 024-12, section 1, `d4`'s plan
of 2026-11-15): the dead klongs' bound of a delete with the merges is proved at
the runs of the joint induction (`opCaseOK_dead_delMerge`, DeadDelCases.lean),
from the merges' step (`hMSF`), the fuel inside the transaction and the
take-back's facts that the induction gives. Premises `hp`, `hth`, `hchk5`,
`htb`, `l4`, `hMSF`, `hCoF`. -/
theorem invGetScanOK_merges_noU_noD4 (p : Params) (hp : MergeParamsOK p)
    (hth : 2 ≤ p.theta ∨ p.theta = 0)
    (hchk5 : OpDelChk5OKL p)
    (htb : TakeBelowFuelDelOK p)
    (l4 : OpCaseOK p (RunOK p) (QLive p) DelMergeOpenCase)
    (hMSF : ∀ ts, MergeFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hCoF : ∀ ts, CollapseFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1)) :
    InvPreserved p ∧ GetOK p ∧ ScanOK p ∧ LatestGetOK p ∧ LatestScanOK p := by
  have hp' := hp
  unfold MergeParamsOK at hp'
  have hM := mergeParamsOK_M p hp
  have hM4 := four_le_M p hp
  have hm : p.merges = true := by
    unfold Params.merges; simp only [decide_eq_true_eq]; omega
  have hsa : 2 ≤ p.splitAbove := by omega
  have hcap : 1 ≤ p.mergeMax := by omega
  have hRL : ∀ P t, RunOK p P t → RunLinksOK p P t := fun _ _ h => h.1
  have hMS : ∀ ts, MergeStepOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1) :=
    fun ts => mergeStepOK_of_segFits (ctxOf p ts) _ _ (Nat.succ_pos _) hcap hsa (hMSF ts)
  have hCo : ∀ ts, CollapseFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1) := hCoF
  have hR : ∀ P t, RunTreeQ p (LatestQD p) P t → RunOK p P t := runOK_of_runTreeQD p
  have hRL' : ∀ P t, RunTreeQ p (LatestQD p) P t → RunLinksOK p P t := fun _ _ h => h.1
  have hRT' : ∀ P t, RunTreeQ p (LatestQD p) P t → TreeAt p P t := fun _ _ h => h.2.1
  have hRI' : ∀ P t, RunTreeQ p (LatestQD p) P t → InvOK p P t := fun _ _ h => h.2.2.1.1
  have hRP' : ∀ P t, RunTreeQ p (LatestQD p) P t → PointersOK P := fun _ _ h => h.1.1
  have hRK' : ∀ P t, RunTreeQ p (LatestQD p) P t → KindsAllOK p P := fun _ _ h => h.2.2.1.2.2.1
  have hRH' : ∀ P t, RunTreeQ p (LatestQD p) P t → HeightAllOK p P t :=
    fun _ _ h => h.2.2.1.2.2.2.1
  have l4' := opCaseOK_anti p _ _ hR _ _
    (liveCase_delMerge_of_rest p (RunOK p) hRL
      (opCaseOK_of_open p (RunOK p) (QLive p) (keptByReads_live p) DelMergeRestCase l4))
  -- the joint induction's cases
  have hLv := opCaseOK_of_cases_merges p _ _ hm (liveCase_putLeafRoom p _)
    (liveCase_putLeafFull p _ hRL' hsa hp)
    (opCaseOK_putNewSeg_of_parts p _ _ (liveCase_putNewSeg1Room p _ (by omega))
      (liveCase_putNewSegsRoom p _ (by omega)) (liveCase_putNewSegFull p _ hRL' (by omega) hsa hp)) l4'
  have hTp := opCaseOK_put_of_cases p _ _ hm (treeCase_putLeafRoom p _)
    (treeCase_putLeafFull p _ hRL' hsa)
    (opCaseOK_putNewSeg_of_parts p _ _ (treeCase_putNewSeg1Room p _ (by omega))
      (treeCase_putNewSegsRoom p _ (by omega)) (treeCase_putNewSegFull p _ hRL' (by omega) hsa))
  have hPp := opCaseOK_put_of_cases p _ _ hm (putInvCase_putLeafRoom p _ hRL')
    (putInvCase_putLeafFull p _ hRL' hsa)
    (opCaseOK_putNewSeg_of_parts p _ _ (putInvCase_putNewSeg1Room p _ hRL' (by omega))
      (putInvCase_putNewSegsRoom p _ hRL' (by omega)) (putInvCase_putNewSegFull p _ hRL' (by omega) hsa))
  have hOp := opCaseOK_put_of_cases p _ _ hm (rangeCase_putLeafRoom p _)
    (rangeCase_putLeafFull p _ hRL' hsa)
    (opCaseOK_putNewSeg_of_parts p _ _ (rangeCase_putNewSeg1Room p _ (by omega))
      (rangeCase_putNewSegsRoom p _ (by omega)) (rangeCase_putNewSegFull p _ hRL' (by omega) hsa))
  have hTIRJ := opCaseOKJ_treeInvRange_delMergeRLC p _
    (delStepsQdLJ_of_openR_noU p _ (by omega) hsa hRL' hRP' hRK' hRH') hMS hCo hsa hcap hRP' hRK'
  have hSI : ∀ ts tx w, SJ p ts tx w → PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w :=
    fun _ _ _ h => h.1.1.1.1.1
  have hSV : ∀ ts tx w, SJ p ts tx w → LeafVals (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w :=
    fun _ _ _ h => h.1.1.1.1.2
  have hSB : ∀ ts tx w, SJ p ts tx w → tx.base ≤ w.next := fun _ _ _ h => h.1.1.1.2
  have hSR : ∀ ts tx w, SJ p ts tx w →
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey := fun _ _ _ h => h.1.1.2
  have hSF : ∀ ts tx w, SJ p ts tx w →
      SegFits (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) (p.fuel - 1) w.top.rootKey :=
    fun _ _ _ h => h.1.2.1
  have hSM : ∀ ts tx w, SJ p ts tx w → ∀ x o, w.madeFor.lookup x = some o → o < tx.base :=
    fun _ _ _ h => h.1.2.2
  have hDSJ : DelStepsJ2OK p (RunTreeQ p (LatestQD p)) (SJ p) :=
    delStepsJ2OKS_of_openR_noU p _ (SJ p) (by omega) hsa hRL' hRP' hRK' hSI hSV hSB hSR hSF hSM hRH'
      (fun _ _ _ h => h.2.1) (fun _ _ _ h => h.2.2)
  have hJ2O : OpJ2OK p (RunTreeQ p (LatestQD p)) (SJ p) :=
    opJ2OK_of_cases p _ _ (opJ2Case_putLeafRoom p _ _ hSI hSV)
      (opJ2Case_putLeafFull p _ _ hRL' hsa hSI hSV hSB hSR)
      (opJ2Case_putNewSeg p _ _ (by omega) hSI hSB (opJ2Case_putNewSegFull p _ _ hRL' (by omega) hsa hSI hSB hSR))
      (opJ2Case_delMergeRC p _ _ hDSJ hMS hCo (replaceRootFullJ2OKC_run p hsa) hsa hcap hRP' hRK')
      (opJ2Case_delNoLeaf p _ _ hSI) (opJ2Case_delNoop p _ _ hSI)
      (opJ2CaseOK_void p _ _ _ hm delEmptyCase_merges) (opJ2Case_delRoom p _ _ hSI hSV)
      (opJ2CaseOK_void p _ _ _ hm delFullCase_merges)
  have hchkR := opDelChk2ORJ_of_chk5 p _ hm hM4 hRL' hchk5
  have joint := jointHtJ_reachedJ p _ hm (by omega) hM4 (baseStartOK_runTreeQ p (LatestQD p)) hRL' hRT' hRI'
    hRP' hRK' hRH' htb hTp hPp hOp hTIRJ.1 hTIRJ.2.1 hTIRJ.2.2 hJ2O hLv hchkR
  -- from the joint induction: the heights' delete side, the fuel, the cases at every operation
  have hht : OpHtDelOKUnder p (RunTreeQ p (LatestQD p)) := by
    intro ts tx hw hr z top hz htop pre key post hsplit r w hpre hvo hkw hb hwf hi r' v he
    obtain ⟨hI, hRo, hL, _, _, hJ⟩ := joint ts tx hw hr z top hz htop pre (Op.del key :: post) hsplit r w hpre
    have hc := hchkR ts tx hw hr z top hz htop pre key post hsplit r w hpre hI hRo hL hi hJ r' v he
    obtain ⟨-, hk, -, hki⟩ := kd_contextR p (by omega) ts tx (hRP' _ _ hr) (hRK' _ _ hr) hw top pre
      (Op.del key :: post) hsplit r w hpre
    exact (ht_putKvDelChk2 tx.base key (ctxOf p ts) w hvo (by simp [ctxOf]) hkw hb hi hwf hk hki
      (by simpa [ctxOf] using (show 2 ≤ p.M by omega)) r' v hc).2.1
  have hfitQ : TxSegFitsOK p (RunTreeQ p (LatestQD p)) :=
    txSegFitsOK_of_takeBelowDelRHU p (by omega) _ hRL' hRK' hRH' hht htb
  have hnext : ∀ ts tx, Within p (ts ++ [tx]) → RunTreeQ p (LatestQD p) (treeRun p ts) ts.length →
      ∀ z top, lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
      topOf p (ctxOf p ts).view z = .ok top →
      ∀ pre op post, tx.ops = pre ++ op :: post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) → ∀ a w', putKv op (ctxOf p ts) w = .ok (a, w') →
      WriterTreeOK p (treeRun p ts) (ts.length + 1) w' ∧
        PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w' ∧
        RangeOrder (wNode p (viewOf (treeRun p ts)) w') (ts.length + 1) w'.top.rootKey := by
    intro ts tx hw hr z top hz htop pre op post hs r w hpre a w' he
    obtain ⟨hI', hR', _, _, hT', _⟩ := joint ts tx hw hr z top hz htop (pre ++ [op]) post (by rw [hs]; simp)
      (r ++ [a]) w' (mapM_snoc_ok _ _ pre op r w a w' hpre he)
    exact ⟨hT', hI', hR'⟩
  have hT : OpCaseOK p (RunTreeQ p (LatestQD p)) (QTree p) AnyOp :=
    fun ts tx hw hr z top hz htop pre op post hs r w hpre _ _ _ a w' he =>
      (hnext ts tx hw hr z top hz htop pre op post hs r w hpre a w' he).1
  have hPI : OpCaseOK p (RunTreeQ p (LatestQD p)) (QPutInv p) AnyOp :=
    fun ts tx hw hr z top hz htop pre op post hs r w hpre _ _ _ a w' he _ =>
      (hnext ts tx hw hr z top hz htop pre op post hs r w hpre a w' he).2.1
  have hO : OpCaseOK p (RunTreeQ p (LatestQD p)) (QRange p) AnyOp :=
    fun ts tx hw hr z top hz htop pre op post hs r w hpre _ _ _ a w' he _ =>
      (hnext ts tx hw hr z top hz htop pre op post hs r w hpre a w' he).2.2
  have hLC : StateOK p (RunTreeQ p (LatestQD p)) (fun ts _ w => LiveCountsW p ts w) :=
    fun ts tx hw hr z top hz htop pre post hs r w hpre =>
      (joint ts tx hw hr z top hz htop pre post hs r w hpre).2.2.1
  have hJ2S : StateOK p (RunTreeQ p (LatestQD p))
      (fun ts tx w => TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w) :=
    fun ts tx hw hr z top hz htop pre post hs r w hpre =>
      (joint ts tx hw hr z top hz htop pre post hs r w hpre).2.2.2.2.2
  have hMFS := stateOK_madeFor p hM4 (RunTreeQ p (LatestQD p)) hRL'
  -- the delete's steps without `hHL`
  have d4' : OpCaseOK p (RunTreeQ p (LatestQD p)) (QDead p) (fun c base w op =>
      DelMergeCase c base w op ∧ LiveCounts c.p (wNode c.p base w) c.i w.top.rootKey) :=
    fun ts tx hw hr z top hz htop pre op post hops r w hpre hI hRo hP =>
      opCaseOK_dead_delMerge p _ (delStepsCaseDOK_merge p _ (by omega) hsa hRL' hRP' hRK' hRH' hht htb
        hLC hJ2S hMFS) hMS hsa hcap (by omega) hRP' hRK' hfitQ hth ts tx hw hr z top hz htop pre op post hops
        r w hpre hI hRo hP.1
  have hTL := opCaseOK_L_of_any p _ _ hT
  have hPIL := opCaseOK_L_of_any p _ _ hPI
  have hOL := opCaseOK_L_of_any p _ _ hO
  have hLvL := opCaseOK_L_of_any p _ _ hLv
  have hDdL := opCaseOK_of_cases_mergesL p _ _ hm (deadCase_putLeafRoom p _)
    (deadCase_putLeafFull p _ hRL' hsa hth)
    (opCaseOK_putNewSeg_of_parts p _ _ (deadCase_putNewSeg1Room p _ (by omega))
      (deadCase_putNewSegsRoom p _ (by omega)) (deadCase_putNewSegFull p _ hRL' (by omega) hsa hth)) d4'
  have hDd := opCaseOK_any_of_L p _ hRL' hRT' hRI' hTL hPIL hOL hLvL _ hDdL
  have hJ := runTreeQ_of_mergesSC p (by omega) hsa hcap hm (LatestQD p) (latestQD_init p (by omega))
    (latestQD_snocR p hp hht hT hPI hO hLv hDd)
    (fun _ _ h => h.1.2.1) (fun _ _ h => h.1.2.2.1)
    (opTreeOKUnder_of_cases p _ hRL' hRT' hRI' hT hPI hO)
    (putInvStateOK_of_cases p _ hRL' hRT' hRI' hT hPI hO)
    (rangeStateOK_of_cases p _ hRL' hRT' hRI' hT hPI hO)
    hfitQ hMFS
    (delStepsJ2OKJ_of_openR_noU p _ (TakeS4 p) (by omega) hsa hRL' hRP' hRK'
      (fun _ _ _ h => h.1.1.1.1) (fun _ _ _ h => h.1.1.1.2) (fun _ _ _ h => h.1.1.2)
      (fun _ _ _ h => h.1.2) (fun _ _ _ h => h.2.1) (fun _ _ _ h => h.2.2) hRH' hht htb hLC)
    hMS hCo (replaceRootFullJ2OKC_run p hsa)
  have hW : ∀ ts tx, Within p (ts ++ [tx]) → RunOK p (treeRun p ts) ts.length →
      RunTreeQ p (LatestQD p) (treeRun p ts) ts.length :=
    fun ts tx hw _ => hJ ts (within_snoc_prefix p ts tx hw)
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
    (opGetCaseOK_delMergeC p (RunOK p)
      (delStepsOK_of_within p (RunOK p) _ hW
        (delStepsOKJ_of_open_noU p _ (by omega) hsa hRL' hP hRK' hRH' hht htb hLC hJ2S hMFS))
      hMS hCo hsa hcap (by omega) hP hfit)
  exact ⟨hinv, h.1, h.2, latestGetOK_of_getOK p h.1, latestScanOK_of_scanOK p h.2⟩

set_option linter.unusedVariables false in
/-- The joint route's top theorem without `hU`, `hchk5` and `d4`:
`invGetScanOK_merges_noU_noD4` with `hchk5` discharged as in
`invGetScanOK_merges_free` (`opDelChk8OKR_holds` and the three steps down to
`OpDelChk5OKL`). Premises `hp`, `hth`, `htb`, `l4`, `hMSF`, `hCoF`; since 2026-11-15 (bergdb 025-05) the corollary of
`invGetScanOK_merges_noFit`, which needs neither `hMSF` nor `hCoF`. -/
theorem invGetScanOK_merges_free_noD4 (p : Params) (hp : MergeParamsOK p)
    (hth : 2 ≤ p.theta ∨ p.theta = 0)
    (htb : TakeBelowFuelDelOK p)
    (l4 : OpCaseOK p (RunOK p) (QLive p) DelMergeOpenCase)
    (hMSF : ∀ ts, MergeFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hCoF : ∀ ts, CollapseFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1)) :
    InvPreserved p ∧ GetOK p ∧ ScanOK p ∧ LatestGetOK p ∧ LatestScanOK p :=
  invGetScanOK_merges_noFit p hp hth htb l4
end SIS.Tree
