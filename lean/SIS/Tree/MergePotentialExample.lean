import SIS.Tree.MergePotential
import SIS.Tree.InvInit
import SIS.Tree.WriterSteps

namespace SIS.Tree

open SIS SIS.Check

attribute [local cbv_eval] appendKlongs_step_dead
attribute [local cbv_opaque] appendKlongs putSegs

@[local cbv_eval] theorem putSegs_potentialExample_step (key : Key) (value : Option Nat)
    (segs : List Nat) (x : NodeId) :
    putSegs key value segs x = putSegs._sunfold key value segs x := by
  cases segs with
  | nil => rfl
  | cons cv rest => cases rest <;> rfl

def potentialExampleParams : Params :=
  {M := 8,G := 0,H := 1,mergeBelow := 2,mergeMax := 3,splitAbove := 4,theta := 2}

def potentialExampleHistory : List Tx :=
  [{base := 100,ops := [0,64,128,192,256].map (fun cv => .put [cv] 1)},
   {base := 200,ops := [.put [0] 2]},
   {base := 300,ops := [.del [0]]}]

def potentialExampleChecks : Bool :=
  (List.range potentialExampleHistory.length).all (fun j =>
    let P := treeRun potentialExampleParams (potentialExampleHistory.take j)
    let tx := potentialExampleHistory[j]!
    P.all (fun q => decide (q.1 < tx.base)) &&
      isOk (exec? potentialExampleParams tx (j+1)
        (view (treeSpec potentialExampleParams) P j)))

set_option maxRecDepth 100000 in
set_option cbv.maxSteps 2000000 in
theorem potentialExampleChecks_eq : potentialExampleChecks = true := by cbv

theorem potentialExampleParams_ok : MergeParamsOK potentialExampleParams := by
  unfold MergeParamsOK
  decide +kernel

theorem potentialExampleHistory_within : Within potentialExampleParams potentialExampleHistory := by
  constructor
  · have hh : potentialExampleHistory.all (fun tx => tx.sorted && tx.wf) = true := by decide +kernel
    intro tx htx
    simpa only [Bool.and_eq_true] using List.all_eq_true.mp hh tx htx
  · intro j hj
    have hc := List.all_eq_true.mp potentialExampleChecks_eq j (List.mem_range.mpr hj)
    have hc' :
        (treeRun potentialExampleParams (potentialExampleHistory.take j)).all
          (fun q => decide (q.1 < potentialExampleHistory[j].base)) = true ∧
        isOk (exec? potentialExampleParams potentialExampleHistory[j] (j+1)
          (view (treeSpec potentialExampleParams)
            (treeRun potentialExampleParams (potentialExampleHistory.take j)) j)) = true := by
      simpa only [List.getElem!_eq_getElem?_getD,List.getElem?_eq_getElem hj,
        Option.getD_some,Bool.and_eq_true] using hc
    refine ⟨?_,hc'.2⟩
    intro q hq
    exact of_decide_eq_true (List.all_eq_true.mp hc'.1 q hq)

def commentTreePotential (p : Params) (P : Struct BVal) (t : Time) : Nat :=
  ((nodesRootsAt p P t).map (fun q => if q.2 then 0 else
    ((keyNodeAt p P q.1).map (fun n => p.mergeBelow+1-(n.liveAt t).length)).getD 0)).sum

def potentialExampleStats : Except String (Nat × Nat × Nat × Nat × Nat × Nat × Nat) := do
  let before := treeRun potentialExampleParams (potentialExampleHistory.take 2)
  let after := treeRun potentialExampleParams potentialExampleHistory
  let tx : Tx := {base := 300,ops := [.del [0]]}
  let (bs,w) ← execW potentialExampleParams tx 3
    (view (treeSpec potentialExampleParams) before 2)
  pure (w.merges,deletesOf tx bs,w.spaceSplits,
    commentTreePotential potentialExampleParams before 2,
    commentTreePotential potentialExampleParams after 3,
    treeFillPotential potentialExampleParams before 2,
    treeFillPotential potentialExampleParams after 3)

set_option maxRecDepth 100000 in
set_option cbv.maxSteps 2000000 in
theorem potentialExampleStats_eq : potentialExampleStats = .ok (1,1,0,1,2,2,2) := by cbv

/-- The comment potential fails the per-transaction potential inequality on
a reachable sorted run at valid thresholds, while the replacement pays it.
This is not a counterexample to TP33's aggregate cost inequality. -/
theorem commentPotential_reachable_step_witness :
    MergeParamsOK potentialExampleParams ∧ Within potentialExampleParams potentialExampleHistory ∧
    ∃ bs w,
      execW potentialExampleParams {base := 300,ops := [.del [0]]} 3
        (view (treeSpec potentialExampleParams)
          (treeRun potentialExampleParams (potentialExampleHistory.take 2)) 2) = .ok (bs,w) ∧
      w.merges = 1 ∧ deletesOf {base := 300,ops := [.del [0]]} bs = 1 ∧ w.spaceSplits = 0 ∧
      ¬ commentTreePotential potentialExampleParams (treeRun potentialExampleParams potentialExampleHistory) 3 + w.merges ≤
        commentTreePotential potentialExampleParams (treeRun potentialExampleParams (potentialExampleHistory.take 2)) 2 +
          deletesOf {base := 300,ops := [.del [0]]} bs + 2*w.spaceSplits ∧
      treeFillPotential potentialExampleParams (treeRun potentialExampleParams potentialExampleHistory) 3 + w.merges ≤
        treeFillPotential potentialExampleParams (treeRun potentialExampleParams (potentialExampleHistory.take 2)) 2 +
          deletesOf {base := 300,ops := [.del [0]]} bs + 2*w.spaceSplits := by
  refine ⟨potentialExampleParams_ok,potentialExampleHistory_within,?_⟩
  have hc := potentialExampleStats_eq
  unfold potentialExampleStats at hc
  cases he : execW potentialExampleParams {base := 300,ops := [.del [0]]} 3
      (view (treeSpec potentialExampleParams)
        (treeRun potentialExampleParams (potentialExampleHistory.take 2)) 2) with
  | error e =>
    simp only [he] at hc
    cases hc
  | ok result =>
    rcases result with ⟨bs,w⟩
    have hs : w.merges = 1 ∧ deletesOf {base := 300,ops := [.del [0]]} bs = 1 ∧ w.spaceSplits = 0 ∧
        commentTreePotential potentialExampleParams
          (treeRun potentialExampleParams (potentialExampleHistory.take 2)) 2 = 1 ∧
        commentTreePotential potentialExampleParams
          (treeRun potentialExampleParams potentialExampleHistory) 3 = 2 ∧
        treeFillPotential potentialExampleParams
          (treeRun potentialExampleParams (potentialExampleHistory.take 2)) 2 = 2 ∧
        treeFillPotential potentialExampleParams
          (treeRun potentialExampleParams potentialExampleHistory) 3 = 2 := by
      simpa only [he,bind,Except.bind,pure,Except.pure,Except.ok.injEq,Prod.mk.injEq] using hc
    refine ⟨bs,w,rfl,hs.1,hs.2.1,hs.2.2.1,?_,?_⟩ <;> omega

end SIS.Tree
