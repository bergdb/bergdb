import SIS.Tree.MergeHeightExec

namespace SIS.Tree

open SIS SIS.Check

attribute [local cbv_eval] appendKlongs_step_dead
attribute [local cbv_opaque] appendKlongs putSegs

@[local cbv_eval] theorem putSegs_sortedTight_step (key : Key) (value : Option Nat)
    (segs : List Nat) (x : NodeId) :
    putSegs key value segs x = putSegs._sunfold key value segs x := by
  cases segs with
  | nil => rfl
  | cons cv rest => cases rest <;> rfl

def sortedTightParams : Params :=
  ({M := 8, G := 0, H := 0} : Params).withMerges.withTheta

def sortedTightHistory : List Tx :=
  [{base := 100, ops := [72,136,200,264].map (fun cv => .put [cv] 1)},
   {base := 300, ops := [.put [72] 2]}]

def sortedTightTx : Tx := {base := 500, ops := [.put [8] 1, .del [264]]}

def sortedTightHistoryChecks : Bool :=
  (List.range sortedTightHistory.length).all (fun j =>
    let P := treeRun sortedTightParams (sortedTightHistory.take j)
    let tx := sortedTightHistory[j]!
    P.all (fun q => decide (q.1 < tx.base)) &&
      isOk (exec? sortedTightParams tx (j+1)
        (view (treeSpec sortedTightParams) P j)))

set_option maxRecDepth 100000 in
set_option cbv.maxSteps 2000000 in
theorem sortedTightHistoryChecks_eq : sortedTightHistoryChecks = true := by cbv

theorem sortedTightParams_ok : MergeParamsOK sortedTightParams := by
  have hp := mergeParamsOK_withMerges ({M := 8,G := 0,H := 0} : Params) (by decide)
  exact hp

theorem sortedTightHistory_within : Within sortedTightParams sortedTightHistory := by
  constructor
  · have hc : sortedTightHistory.all (fun tx => tx.sorted && tx.wf) = true := by decide +kernel
    intro tx htx
    simpa only [Bool.and_eq_true] using List.all_eq_true.mp hc tx htx
  · intro j hj
    have hc := List.all_eq_true.mp sortedTightHistoryChecks_eq j (List.mem_range.mpr hj)
    have hc' :
        (treeRun sortedTightParams (sortedTightHistory.take j)).all
          (fun q => decide (q.1 < sortedTightHistory[j].base)) = true ∧
        isOk (exec? sortedTightParams sortedTightHistory[j] (j+1)
          (view (treeSpec sortedTightParams)
            (treeRun sortedTightParams (sortedTightHistory.take j)) j)) = true := by
      simpa only [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem hj,
        Option.getD_some,Bool.and_eq_true] using hc
    refine ⟨?_,hc'.2⟩
    intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp hc'.1 q hq)

theorem sortedTightTx_sorted : sortedTightTx.sorted = true := by decide +kernel
theorem sortedTightTx_wf : sortedTightTx.wf = true := by decide +kernel
theorem sortedTightTx_length : sortedTightTx.ops.length = 2 := by decide +kernel
theorem sortedTightTx_within_limits : sortedTightTx.within Limits.user = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option cbv.maxSteps 2000000 in
theorem sortedTightTx_fresh :
    ∀ q ∈ treeRun sortedTightParams sortedTightHistory, q.1 < sortedTightTx.base := by
  have hc : (treeRun sortedTightParams sortedTightHistory).all
      (fun q => decide (q.1 < sortedTightTx.base)) = true := by cbv
  intro q hq
  exact of_decide_eq_true (List.all_eq_true.mp hc q hq)

def sortedTightStats : Except String (Nat × Nat × Nat) := do
  let (bs,w) ← execW sortedTightParams sortedTightTx 3
    (view (treeSpec sortedTightParams) (treeRun sortedTightParams sortedTightHistory) 2)
  pure (w.merges,deletesOf sortedTightTx bs,maxSeenHeight w.gh)

set_option maxRecDepth 100000 in
set_option cbv.maxSteps 2000000 in
theorem sortedTightStats_eq : sortedTightStats = .ok (1,1,1) := by cbv

/-- A sorted two-operation transaction attains the H+1 coefficient. The
history and the final transaction have well-formed keys and fresh ids, and
the parameters include dead-klong compaction. -/
theorem sorted_merge_bound_can_be_tight :
    ∃ bs w,
      execW sortedTightParams sortedTightTx 3
        (view (treeSpec sortedTightParams) (treeRun sortedTightParams sortedTightHistory) 2) = .ok (bs,w) ∧
      deletesOf sortedTightTx bs = 1 ∧ w.merges = 1 ∧
      w.merges = deletesOf sortedTightTx bs * (sortedTightParams.H+1) ∧
      ¬ w.merges ≤ deletesOf sortedTightTx bs * sortedTightParams.H := by
  have hc := sortedTightStats_eq
  unfold sortedTightStats at hc
  cases he : execW sortedTightParams sortedTightTx 3
      (view (treeSpec sortedTightParams) (treeRun sortedTightParams sortedTightHistory) 2) with
  | error e =>
    simp only [he] at hc
    change Except.error e = Except.ok (1,1,1) at hc
    cases hc
  | ok result =>
    rcases result with ⟨bs,w⟩
    have hs : w.merges = 1 ∧ deletesOf sortedTightTx bs = 1 ∧ maxSeenHeight w.gh = 1 := by
      simpa only [he,bind,Except.bind,pure,Except.pure,Except.ok.injEq,Prod.mk.injEq] using hc
    refine ⟨bs,w,rfl,hs.2.1,hs.1,?_,?_⟩
    · change w.merges = deletesOf sortedTightTx bs * 1
      omega
    · change ¬ w.merges ≤ deletesOf sortedTightTx bs * 0
      omega

/-- All the intended transaction preconditions hold for the tight witness: TP32's
(`MergeOpBound`, restated 2026-11-12) and TP28. Thus H cannot replace H+1 in
TP32. -/
theorem sorted_merge_bound_sharp_witness :
    MergeParamsOK sortedTightParams ∧ Within sortedTightParams sortedTightHistory ∧
    sortedTightTx.sorted = true ∧ sortedTightTx.wf = true ∧
    (∀ q ∈ treeRun sortedTightParams sortedTightHistory, q.1 < sortedTightTx.base) ∧
    ∃ bs w,
      execW sortedTightParams sortedTightTx (sortedTightHistory.length+1)
        (view (treeSpec sortedTightParams)
          (treeRun sortedTightParams sortedTightHistory) sortedTightHistory.length) = .ok (bs,w) ∧
      deletesOf sortedTightTx bs = 1 ∧ w.merges = 1 ∧
      w.merges = deletesOf sortedTightTx bs * (sortedTightParams.H+1) ∧
      ¬ w.merges ≤ deletesOf sortedTightTx bs * sortedTightParams.H := by
  exact ⟨sortedTightParams_ok,sortedTightHistory_within,sortedTightTx_sorted,
    sortedTightTx_wf,sortedTightTx_fresh,sorted_merge_bound_can_be_tight⟩

end SIS.Tree
