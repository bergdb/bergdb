/-
TP7's take-back statement with `BaseStartOK` discharged (bergdb 024-12,
`baseStartOK_runTreeQ`): with the merges off, open are cases (4) void, (7) and
(9); with the merges on, case (4)'s obligations alone.
-/
import SIS.Tree.TakeBaseStart
import SIS.Tree.TakeDelMerge

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- `takeBackOK_of_cases4` without `BaseStartOK`. -/
theorem takeBackOK_of_cases4B (p : Params) (hM : 2 ≤ p.M) (hsa : 2 ≤ p.splitAbove)
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
    (c4 : OpJ2CaseOK p (RunTreeQ p Q) (TakeS3 p) DelMergeCase)
    (c7 : OpJ2CaseOK p (RunTreeQ p Q) (TakeS3 p) DelEmptyCase)
    (c9 : OpJ2CaseOK p (RunTreeQ p Q) (TakeS3 p) DelFullCase) :
    TakeBackOKUnder p (RunLinksOK p) :=
  takeBackOK_of_cases4 p hM hsa Q hQ0 hQs hQP hQK ho hPI hRO (baseStartOK_runTreeQ p Q) c4 c7 c9

/-- `takeBackOK_of_mergesF` without `BaseStartOK`: with the merges on, TP7's
take-back from case (4)'s obligations (cost's `MergeStepOKF`,
`CollapseStepOKF`; `MergeFullJ2OKF`, `DelStepsJ2OKF`) and the named inputs. -/
theorem takeBackOK_of_mergesFB (p : Params) (hM : 2 ≤ p.M) (hsa : 2 ≤ p.splitAbove)
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
    (hDS : DelStepsJ2OKF p (RunTreeQ p Q) (TakeS3 p))
    (hMS : ∀ ts, MergeStepOKF (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hCo : ∀ ts, CollapseStepOKF (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hMF : ∀ ts B, MergeFullJ2OKF (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1) B) :
    TakeBackOKUnder p (RunLinksOK p) :=
  takeBackOK_of_mergesF p hM hsa hcap hm Q hQ0 hQs hQP hQK ho hPI hRO (baseStartOK_runTreeQ p Q)
    hDS hMS hCo hMF

end SIS.Tree
