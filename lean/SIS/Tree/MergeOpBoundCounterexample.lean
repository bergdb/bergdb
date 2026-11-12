import SIS.Tree.WriterSteps

namespace SIS.Tree

open SIS SIS.Check

attribute [local cbv_eval] appendKlongs_step_dead
attribute [local cbv_opaque] appendKlongs putSegs

@[local cbv_eval] theorem putSegs_cbv_step (key : Key) (value : Option Nat)
    (segs : List Nat) (x : NodeId) :
    putSegs key value segs x = putSegs._sunfold key value segs x := by
  cases segs with
  | nil => rfl
  | cons cv rest => cases rest <;> rfl

/-- Standard merge thresholds, with the final tree restricted to a leaf. -/
def tp32CounterexampleParams : Params :=
  ({ M := 8, G := 0, H := 0 } : Params).withMerges

def tp32CounterexampleKey (j : Nat) : Key := [64 * j + 8]

def tp32CounterexamplePuts : List Tree.Op :=
  (List.range 12).map (fun j => .put (tp32CounterexampleKey j) 1)

/-- Restoring the deleted key and overwriting keys can split the tree again. -/
def tp32CounterexampleCycle (j : Nat) : List Tree.Op :=
  let k := tp32CounterexampleKey (if j < 3 then 0 else if j % 2 == 1 then 8 else 0)
  [.del k, .put k 1] ++ tp32CounterexamplePuts

def tp32CounterexampleTx : Tx :=
  { base := 100,
    ops := tp32CounterexamplePuts ++
      (List.range 15).flatMap tp32CounterexampleCycle ++
      ((List.range 12).drop 1).map (fun j => .del (tp32CounterexampleKey j)) }

/-- Counts only a successful result, including the final bounds check. -/
def tp32CounterexampleStats : Except String (Nat × Nat) := do
  let (noops, w) ← execW tp32CounterexampleParams tp32CounterexampleTx 1
    (view (treeSpec tp32CounterexampleParams) (treeRun tp32CounterexampleParams []) 0)
  pure (w.merges, deletesOf tp32CounterexampleTx noops)

set_option cbv.maxSteps 20000000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 200000000 in
theorem tp32CounterexampleStats_eq : tp32CounterexampleStats = .ok (27, 26) := by
  cbv

theorem tp32CounterexampleParams_ok : MergeParamsOK tp32CounterexampleParams := by
  exact mergeParamsOK_withMerges _ (by decide)

theorem tp32CounterexampleTx_wf : tp32CounterexampleTx.wf = true := by decide +kernel

theorem tp32CounterexampleTx_not_sorted : tp32CounterexampleTx.sorted = false := by decide +kernel

theorem tp32CounterexampleTx_fresh :
    ∀ q ∈ treeRun tp32CounterexampleParams [], q.1 < tp32CounterexampleTx.base := by
  have hf : (treeRun tp32CounterexampleParams []).all
      (fun q => decide (q.1 < tp32CounterexampleTx.base)) = true := by cbv
  intro q hq
  exact of_decide_eq_true (List.all_eq_true.mp hf q hq)

/-- TP32 permits a final transaction with repeated, unordered keys. -/
theorem not_mergeOpBound_counterexample : ¬ MergeOpBound tp32CounterexampleParams := by
  intro hb
  have hi : Within tp32CounterexampleParams [] := by simp [Within]
  have hc := tp32CounterexampleStats_eq
  unfold tp32CounterexampleStats at hc
  cases hr : execW tp32CounterexampleParams tp32CounterexampleTx 1
      (view (treeSpec tp32CounterexampleParams) (treeRun tp32CounterexampleParams []) 0) with
  | error e =>
    simp only [hr] at hc
    change Except.error e = Except.ok (27, 26) at hc
    cases hc
  | ok result =>
    rcases result with ⟨noops, w⟩
    have hstats : w.merges = 27 ∧ deletesOf tp32CounterexampleTx noops = 26 := by
      simpa only [hr, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] using hc
    have hle := hb [] hi tp32CounterexampleTx noops w hr
    simp only [tp32CounterexampleParams, Params.withMerges] at hle
    omega

end SIS.Tree
