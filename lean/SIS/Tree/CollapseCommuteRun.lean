/-
The take-back's and the reading's delete cases with the merges on, with
`CollapseFitsOK` alone in place of `CollapseStepOK` and `ReplaceRootFullJ2OKC` in
place of `ReplaceRootFullJ2OK` (bergdb 024-22, section 11.1): the same proofs as
`opJ2Case_delMergeR`, `runTreeQ_of_mergesS`, `opCaseOKJ_qdW_delMergeRL` and
`opCaseOKJ_treeInvRange_delMergeRL`, through the collapse's steps without
`CollapseUnlinkOK` (CollapseCommuteStep.lean, CollapseCommuteJ2.lean).
-/
import SIS.Tree.HeightsFillHolder
import SIS.Tree.TakeRunQ
import SIS.Tree.CollapseCommuteJ2

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- (4) A delete with the merges on keeps `J2At`, with the run's pointers and
kinds from the run premise R
(`hRP`, `hRK`) instead of TP4 at every run. -/
theorem opJ2Case_delMergeRC (p : Params) (R : Struct BVal → Time → Prop) (S : List Tx → Tx → W → Prop)
    (hS : DelStepsJ2OK p R S)
    (hM : ∀ ts, MergeStepOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hC : ∀ ts, CollapseFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hRJ : ∀ ts B, ReplaceRootFullJ2OKC (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1) B)
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
    (fun g h v hv' => writerWP_afterDelete_delJC key g h (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hM ts) (hC ts) _ _ hv hk hICEk hsa2 hcap tx.base hpos (hRJ ts tx.base) w key v hv')
    (fun g h merged v hv' => writerWP_mergeUp_delJ key g (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hM ts) _ _ hv hk hICEk hsa2 hcap tx.base hpos w key p.fuel h merged v hv')
    (fun seg v hv' => writerWP_collapseRoot_delJC key seg (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hC ts) w key _ _ hv hk hICEk hsa2 tx.base hpos (hRJ ts tx.base) v hv')) ?_
  intro _ w' h' _
  exact h'

/-- TP7's take-back induction with the merges on, without TP4 at every run,
with `TakeS4` for `DelStepsJ2OK`'s S: the state
fits the fuel and the replaced ids are below the transaction's first id at
every state between operations (`hFS`, `hMF`). -/
theorem runTreeQ_of_mergesSC (p : Params) (hM : 2 ≤ p.M) (hsa : 2 ≤ p.splitAbove)
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
    (hFS : StateOK p (RunTreeQ p Q) (fun ts _ w =>
      SegFits (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) (p.fuel - 1) w.top.rootKey))
    (hMF : StateOK p (RunTreeQ p Q) (fun _ tx w => ∀ x o, w.madeFor.lookup x = some o → o < tx.base))
    (hDS : DelStepsJ2OK p (RunTreeQ p Q) (TakeS4 p))
    (hMS : ∀ ts, MergeStepOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hCo : ∀ ts, CollapseFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hRJ : ∀ ts B, ReplaceRootFullJ2OKC (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1) B) :
    ∀ ts, Within p ts → RunTreeQ p Q (treeRun p ts) ts.length :=
  runTreeQ_of_cases_merges4S p hM hsa hm Q hQ0 hQs hQP hQK ho hPI hRO (baseStartOK_runTreeQ p Q) hFS hMF
    (opJ2Case_delMergeRC p _ _ hDS hMS hCo hRJ hsa hcap (fun _ _ h => hQP _ _ h.2.2) (fun _ _ h => hQK _ _ h.2.2))

theorem opCaseOKJ_qdW_delMergeRLC (p : Params) (R : Struct BVal → Time → Prop) (hS : DelStepsQdLJ p R)
    (hM : ∀ ts, MergeStepOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hC : ∀ ts, CollapseFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P) :
    OpCaseOKJ p R (fun ts _ _ w' => QdW p ts w') DelMergeCaseL := by
  have hf2 : 2 ≤ p.fuel + 1 := by unfold Params.fuel; omega
  intro ts tx hw hr z top hz htop pre op post hops r w hpre hH hI hRO hP
  obtain ⟨⟨key, hop, hmerges⟩, hLCw⟩ := hP
  have hF0 := segFits_of_htStart p ts tx w hH.1
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
  exact hS ts tx hw hr z top hz htop pre op post hops r w hpre hH hI hRO hF0 key hop ⟨⟨key, hop, hmerges⟩, hLCw⟩
    (fun g h v hv' => writerWP_afterDelete_delC key g h (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hM ts) (hC ts) _ _ hv hk hICEk hsa2 hcap w key v hv')
    (fun g h merged v hv' => writerWP_mergeUp_del key g (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hM ts) _ _ hv hk hICEk hsa2 hcap w key p.fuel h merged v hv')
    (fun seg v hv' => writerWP_collapseRoot_delC key seg (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hC ts) w key _ _ hv hk hICEk hsa2 v hv')

theorem opCaseOKJ_treeInvRange_delMergeRLC (p : Params) (R : Struct BVal → Time → Prop) (hS : DelStepsQdLJ p R)
    (hM : ∀ ts, MergeStepOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hC : ∀ ts, CollapseFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P) :
    OpCaseOKJ p R (QTree p) DelMergeCaseL ∧ OpCaseOKJ p R (QPutInv p) DelMergeCaseL ∧
      OpCaseOKJ p R (QRange p) DelMergeCaseL := by
  have h := opCaseOKJ_qdW_delMergeRLC p R hS hM hC hsa2 hcap hRP hRK
  refine ⟨?_, ?_, ?_⟩
  · intro ts tx hw hr z top hz htop pre op post hops r w hpre hH hI hRO hP
    exact writerWP_mono (h ts tx hw hr z top hz htop pre op post hops r w hpre hH hI hRO hP)
      (fun _ w' hq => hq.1.tree)
  · intro ts tx hw hr z top hz htop pre op post hops r w hpre hH hI hRO hP
    exact writerWP_mono (h ts tx hw hr z top hz htop pre op post hops r w hpre hH hI hRO hP)
      (fun _ w' hq _ => hq.1)
  · intro ts tx hw hr z top hz htop pre op post hops r w hpre hH hI hRO hP
    exact writerWP_mono (h ts tx hw hr z top hz htop pre op post hops r w hpre hH hI hRO hP)
      (fun _ w' hq _ => hq.2)

/-! ## The take-back's steps, the heights and the fill at the start from S -/

end SIS.Tree
