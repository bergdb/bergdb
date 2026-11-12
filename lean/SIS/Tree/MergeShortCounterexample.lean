import SIS.Tree.WriterSteps

namespace SIS.Tree

open SIS SIS.Check

attribute [local cbv_eval] appendKlongs_step_dead
attribute [local cbv_opaque] appendKlongs putSegs

@[local cbv_eval] theorem putSegs_shortCounterexample_step (key : Key) (value : Option Nat)
    (segs : List Nat) (x : NodeId) :
    putSegs key value segs x = putSegs._sunfold key value segs x := by
  cases segs with
  | nil => rfl
  | cons cv rest => cases rest <;> rfl

def shortCounterexampleParams : Params := ({M := 8, G := 0, H := 0} : Params).withMerges
def shortCounterexampleKey (j : Nat) : Key := [64*j+8]
def shortCounterexamplePuts (js : List Nat) : List Tree.Op :=
  js.map (fun j => .put (shortCounterexampleKey j) 1)
def shortCounterexampleDeletes (js : List Nat) : List Tree.Op :=
  js.map (fun j => .del (shortCounterexampleKey j))

def shortCounterexampleCycle : List Tree.Op :=
  shortCounterexampleDeletes [0] ++ shortCounterexamplePuts [0,0,1,2] ++
    shortCounterexampleDeletes [8] ++ shortCounterexamplePuts [8,9,10,11]

/-- Fifty-six operations with repeated keys. All segments are well formed. -/
def shortCounterexampleTx : Tx :=
  {base := 100,
   ops := shortCounterexamplePuts [6,7,8,9,10,11,0,0,1,2,3,8,9,11] ++
     shortCounterexampleCycle ++ shortCounterexampleCycle ++
     shortCounterexampleDeletes [0] ++ shortCounterexamplePuts [0,0,1,2] ++
     shortCounterexampleDeletes [8] ++ shortCounterexamplePuts [4,5,8,9,10,11] ++
     shortCounterexampleDeletes [8] ++ shortCounterexamplePuts [3,4] ++
     shortCounterexampleDeletes [3,4,5,6,7,9,10]}

def shortCounterexampleStats : Except String (Nat × Nat) := do
  let (bs,w) ← execW shortCounterexampleParams shortCounterexampleTx 1
    (view (treeSpec shortCounterexampleParams) (treeRun shortCounterexampleParams []) 0)
  pure (w.merges, deletesOf shortCounterexampleTx bs)

set_option cbv.maxSteps 5000000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem shortCounterexampleStats_eq : shortCounterexampleStats = .ok (15,14) := by cbv

theorem shortCounterexampleParams_ok : MergeParamsOK shortCounterexampleParams :=
  mergeParamsOK_withMerges _ (by decide)

theorem shortCounterexampleTx_wf : shortCounterexampleTx.wf = true := by decide +kernel
theorem shortCounterexampleTx_not_sorted : shortCounterexampleTx.sorted = false := by decide +kernel
theorem shortCounterexampleTx_length : shortCounterexampleTx.ops.length = 56 := by decide +kernel
theorem shortCounterexampleTx_within_limits :
    shortCounterexampleTx.within Limits.user = true := by decide +kernel

theorem shortCounterexampleTx_fresh :
    ∀ q ∈ treeRun shortCounterexampleParams [], q.1 < shortCounterexampleTx.base := by
  have hf : (treeRun shortCounterexampleParams []).all
      (fun q => decide (q.1 < shortCounterexampleTx.base)) = true := by cbv
  intro q hq
  exact of_decide_eq_true (List.all_eq_true.mp hf q hq)

/-- TP32 fails even with merge thresholds satisfying TP28, well-formed keys,
and fresh ids. The final transaction lacks strict key order and uniqueness. -/
theorem not_mergeOpBound_shortCounterexample : ¬ MergeOpBound shortCounterexampleParams := by
  intro hb
  have hi : Within shortCounterexampleParams [] := by simp [Within]
  have hc := shortCounterexampleStats_eq
  unfold shortCounterexampleStats at hc
  cases hr : execW shortCounterexampleParams shortCounterexampleTx 1
      (view (treeSpec shortCounterexampleParams) (treeRun shortCounterexampleParams []) 0) with
  | error e =>
    simp only [hr] at hc
    change Except.error e = Except.ok (15,14) at hc
    cases hc
  | ok result =>
    rcases result with ⟨bs,w⟩
    have hstats : w.merges = 15 ∧ deletesOf shortCounterexampleTx bs = 14 := by
      simpa only [hr, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] using hc
    have hle := hb [] hi shortCounterexampleTx bs w hr
    simp only [shortCounterexampleParams, Params.withMerges] at hle
    omega

end SIS.Tree
