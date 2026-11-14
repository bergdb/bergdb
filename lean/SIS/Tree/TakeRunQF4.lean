/-
TP7's take-back induction itself with the merges on, on the F4 route (bergdb
024-12, for latest's top theorem): `takeBackOK_of_mergesF4`'s premises without
TP4 at every run (`hPtr`), concluding `RunTreeQ p Q` at every run within reach
(`runTree_jointJ2`'s conclusion) instead of `TakeBackOKUnder`. Case (4) takes
the run's pointers and kinds from the run premise (`opJ2Case_delMergeF4R`).
-/
import SIS.Tree.TakeDelStepsF4

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- `takeBackOK_of_cases3` concluding the induction (`runTree_jointJ2`). -/
theorem runTreeQ_of_cases3 (p : Params) (hM : 2 ≤ p.M) (hsa : 2 ≤ p.splitAbove)
    (Q : Struct BVal → Time → Prop) (hQ0 : Q (initStruct p) 0)
    (hQs : ∀ ts tx, Within p (ts ++ [tx]) → RunTreeQ p Q (treeRun p ts) ts.length →
      RunLinksOK p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      TreeAt p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      Q (treeRun p (ts ++ [tx])) (ts.length + 1))
    (hQP : ∀ P t, Q P t → PointersOK P) (hQK : ∀ P t, Q P t → KindsAllOK p P)
    (ho : OpTreeOKUnder p (RunTreeQ p Q))
    (hPI : StateOK p (RunTreeQ p Q) (fun ts _ w => PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w))
    (hRO : StateOK p (RunTreeQ p Q) (fun ts _ w =>
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey))
    (hB : BaseStartOK p (RunTreeQ p Q))
    (c3 : OpJ2CaseOK p (RunTreeQ p Q) (TakeS3 p) PutNewSegFullCase)
    (c4 : OpJ2CaseOK p (RunTreeQ p Q) (TakeS3 p) DelMergeCase)
    (c7 : OpJ2CaseOK p (RunTreeQ p Q) (TakeS3 p) DelEmptyCase)
    (c9 : OpJ2CaseOK p (RunTreeQ p Q) (TakeS3 p) DelFullCase) :
    ∀ ts, Within p ts → RunTreeQ p Q (treeRun p ts) ts.length := by
  have hSI : ∀ ts tx w, TakeS3 p ts tx w → PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w :=
    fun _ _ _ h => h.1.1.1
  have hSV : ∀ ts tx w, TakeS3 p ts tx w → LeafVals (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w :=
    fun _ _ _ h => h.1.1.2
  have hSB : ∀ ts tx w, TakeS3 p ts tx w → tx.base ≤ w.next := fun _ _ _ h => h.1.2
  have hSR : ∀ ts tx w, TakeS3 p ts tx w →
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey := fun _ _ _ h => h.2
  have hS : StateOK p (RunTreeQ p Q) (TakeS3 p) := by
    intro ts tx hw hr z top hz htop pre post hsplit r w h
    exact ⟨⟨⟨hPI ts tx hw hr z top hz htop pre post hsplit r w h,
      leafVals_reached p hM ts tx hw top pre post hsplit r w h (hQP _ _ hr.2.2) (hQK _ _ hr.2.2)⟩,
      base_le_next_reached p hM ts tx hw top pre post hsplit r w h (hQP _ _ hr.2.2) (hQK _ _ hr.2.2)⟩,
      hRO ts tx hw hr z top hz htop pre post hsplit r w h⟩
  have hSRF : ∀ ts tx w, TakeS3 p ts tx w → ReachedFree p (treeRun p ts) (ts.length + 1) w :=
    fun ts _ w h y hy => h.1.1.1.untaken y (tReach_reachS _ _ _ _ hy)
  have hO : OpJ2OK p (RunTreeQ p Q) (TakeS3 p) :=
    opJ2OK_of_cases p _ _ (opJ2Case_putLeafRoom p _ _ hSI hSV)
      (opJ2Case_putLeafFull p _ _ (fun _ _ h => h.1) hsa hSI hSV hSB hSR)
      (opJ2Case_putNewSeg p _ _ hM hSI hSB c3) c4
      (opJ2Case_delNoLeaf p _ _ hSI) (opJ2Case_delNoop p _ _ hSI) c7 (opJ2Case_delRoom p _ _ hSI hSV) c9
  exact runTree_jointJ2 p hM Q hQ0 hQs ho (TakeS3 p) hO hS hSRF hB
    (takenNotValOK_of p hM _ (fun _ _ h => hQP _ _ h.2.2) (fun _ _ h => hQK _ _ h.2.2))

/-- `takeBackOK_of_cases4` concluding the induction. -/
theorem runTreeQ_of_cases4 (p : Params) (hM : 2 ≤ p.M) (hsa : 2 ≤ p.splitAbove)
    (Q : Struct BVal → Time → Prop) (hQ0 : Q (initStruct p) 0)
    (hQs : ∀ ts tx, Within p (ts ++ [tx]) → RunTreeQ p Q (treeRun p ts) ts.length →
      RunLinksOK p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      TreeAt p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      Q (treeRun p (ts ++ [tx])) (ts.length + 1))
    (hQP : ∀ P t, Q P t → PointersOK P) (hQK : ∀ P t, Q P t → KindsAllOK p P)
    (ho : OpTreeOKUnder p (RunTreeQ p Q))
    (hPI : StateOK p (RunTreeQ p Q) (fun ts _ w => PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w))
    (hRO : StateOK p (RunTreeQ p Q) (fun ts _ w =>
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey))
    (hB : BaseStartOK p (RunTreeQ p Q))
    (c4 : OpJ2CaseOK p (RunTreeQ p Q) (TakeS3 p) DelMergeCase)
    (c7 : OpJ2CaseOK p (RunTreeQ p Q) (TakeS3 p) DelEmptyCase)
    (c9 : OpJ2CaseOK p (RunTreeQ p Q) (TakeS3 p) DelFullCase) :
    ∀ ts, Within p ts → RunTreeQ p Q (treeRun p ts) ts.length :=
  runTreeQ_of_cases3 p hM hsa Q hQ0 hQs hQP hQK ho hPI hRO hB
    (opJ2Case_putNewSegFull p _ _ (fun _ _ h => h.1) hM hsa (fun _ _ _ h => h.1.1.1)
      (fun _ _ _ h => h.1.2) (fun _ _ _ h => h.2)) c4 c7 c9

/-- `takeBackOK_of_cases_merges4` concluding the induction. -/
theorem runTreeQ_of_cases_merges4 (p : Params) (hM : 2 ≤ p.M) (hsa : 2 ≤ p.splitAbove)
    (hm : p.merges = true) (Q : Struct BVal → Time → Prop) (hQ0 : Q (initStruct p) 0)
    (hQs : ∀ ts tx, Within p (ts ++ [tx]) → RunTreeQ p Q (treeRun p ts) ts.length →
      RunLinksOK p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      TreeAt p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      Q (treeRun p (ts ++ [tx])) (ts.length + 1))
    (hQP : ∀ P t, Q P t → PointersOK P) (hQK : ∀ P t, Q P t → KindsAllOK p P)
    (ho : OpTreeOKUnder p (RunTreeQ p Q))
    (hPI : StateOK p (RunTreeQ p Q) (fun ts _ w => PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w))
    (hRO : StateOK p (RunTreeQ p Q) (fun ts _ w =>
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey))
    (hB : BaseStartOK p (RunTreeQ p Q))
    (c4 : OpJ2CaseOK p (RunTreeQ p Q) (TakeS3 p) DelMergeCase) :
    ∀ ts, Within p ts → RunTreeQ p Q (treeRun p ts) ts.length :=
  runTreeQ_of_cases4 p hM hsa Q hQ0 hQs hQP hQK ho hPI hRO hB c4
    (opJ2CaseOK_void p _ _ _ hm delEmptyCase_merges) (opJ2CaseOK_void p _ _ _ hm delFullCase_merges)

/-- `opJ2Case_delMergeF4` with the run's pointers and kinds from the run premise R
(`hRP`, `hRK`) instead of TP4 at every run. -/
theorem opJ2Case_delMergeF4R (p : Params) (R : Struct BVal → Time → Prop) (S : List Tx → Tx → W → Prop)
    (hS : DelStepsJ2OKF3 p R S)
    (hM : ∀ ts, MergeStepOKF3 (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hC : ∀ ts, CollapseStepOKF4 (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hRJ : ∀ ts B, ReplaceRootFullJ2OK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1) B)
    (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P) :
    OpJ2CaseOK p R S DelMergeCase := by
  have hf2 : 2 ≤ p.fuel + 1 := by unfold Params.fuel; omega
  intro ts tx hw hr z top hz htop pre op post hops r w hpre _ hSw hJ hPc
  obtain ⟨key, hop, hmerges⟩ := hPc
  have hpos : 0 < (ctxOf p ts).i := by simp [ctxOf]
  have hwts : Within p ts := by
    have := within_take p (ts ++ [tx]) hw ts.length
    simpa using this
  have hfresh : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have := (hw.2 ts.length (by simp)).1
    simpa using this
  have hK := hRK _ _ hr
  have hv : ViewIdsBelow tx.base (ctxOf p ts).view :=
    viewIdsBelow_rootless _ _ (viewIdsBelow_view p (treeRun p ts) ts.length tx.base hfresh)
  have hk : ViewKinds (kindOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) :=
    viewKinds_of p (treeRun p ts) ts.length tx.base hfresh (treeRun_timesLE p ts) (hRP _ _ hr) hK
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl hK
      (hRP _ _ hr) hb hi.cache hun
  refine writerWP_mono (hS ts tx hw hr z top hz htop pre op post hops r w hpre hSw hJ key hop hmerges
    (fun g h v hv' => writerWP_afterDelete_delJF4 key g h (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hM ts) (hC ts) _ _ hv hk hICEk hsa2 hcap tx.base hpos (hRJ ts tx.base) w key v hv')
    (fun g h merged v hv' => writerWP_mergeUp_delJF3 key g (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hM ts) _ _ hv hk hICEk hsa2 hcap tx.base hpos w key p.fuel h merged v hv')
    (fun seg v hv' => writerWP_collapseRoot_delJF4 key seg (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hC ts) w key _ _ hv hk hICEk hsa2 tx.base hpos (hRJ ts tx.base) v hv')) ?_
  intro _ w' h' _
  exact h'

/-- TP7's take-back induction with the merges on, on the F4 route:
`takeBackOK_of_mergesF4`'s premises without TP4 at every run; every run within
reach meets `RunTreeQ p Q` (its links, `TreeAt` and Q). -/
theorem runTreeQ_of_mergesF4 (p : Params) (hM : 2 ≤ p.M) (hsa : 2 ≤ p.splitAbove)
    (hcap : 1 ≤ p.mergeMax) (hm : p.merges = true)
    (Q : Struct BVal → Time → Prop) (hQ0 : Q (initStruct p) 0)
    (hQs : ∀ ts tx, Within p (ts ++ [tx]) → RunTreeQ p Q (treeRun p ts) ts.length →
      RunLinksOK p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      TreeAt p (treeRun p (ts ++ [tx])) (ts.length + 1) →
      Q (treeRun p (ts ++ [tx])) (ts.length + 1))
    (hQP : ∀ P t, Q P t → PointersOK P) (hQK : ∀ P t, Q P t → KindsAllOK p P)
    (ho : OpTreeOKUnder p (RunTreeQ p Q))
    (hPI : StateOK p (RunTreeQ p Q) (fun ts _ w => PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w))
    (hRO : StateOK p (RunTreeQ p Q) (fun ts _ w =>
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey))
    (hDS : DelStepsJ2OKF3 p (RunTreeQ p Q) (TakeS3 p))
    (hMS : ∀ ts, MergeStepOKF3 (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hCo : ∀ ts, CollapseStepOKF4 (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hRJ : ∀ ts B, ReplaceRootFullJ2OK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1) B) :
    ∀ ts, Within p ts → RunTreeQ p Q (treeRun p ts) ts.length :=
  runTreeQ_of_cases_merges4 p hM hsa hm Q hQ0 hQs hQP hQK ho hPI hRO (baseStartOK_runTreeQ p Q)
    (opJ2Case_delMergeF4R p _ _ hDS hMS hCo hRJ hsa hcap (fun _ _ h => hQP _ _ h.2.2) (fun _ _ h => hQK _ _ h.2.2))

end SIS.Tree
