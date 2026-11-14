import SIS.Tree.MergeProps
import SIS.Tree.WriterSteps

namespace SIS.Tree

open SIS SIS.Check

attribute [local cbv_eval] appendKlongs_step_dead
attribute [local cbv_opaque] appendKlongs putSegs

@[local cbv_eval] theorem putSegs_scanBoundary_step (key : Key) (value : Option Nat)
    (segs : List Nat) (x : NodeId) :
    putSegs key value segs x = putSegs._sunfold key value segs x := by
  cases segs with
  | nil => rfl
  | cons cv rest => cases rest <;> rfl

/-- The scan's upper sentinel is finite. This example uses an unrestricted
writer input, excluded by the corrected key predicate. -/
def scanBoundaryParams : Params :=
  ({ M := 8, G := 0, H := 0 } : Params).withMerges.withTheta

def scanBoundaryKey : Key := [2 ^ 63]

def scanBoundaryTx : Tx := { base := 3, ops := [.put scanBoundaryKey 1] }

def scanBoundaryHistory : List Tx := [scanBoundaryTx]

/-- This unrestricted writer input is excluded by the corrected key predicate. -/
theorem scanBoundaryKey_not_wf : keyWf scanBoundaryKey = false := by
  decide +kernel

theorem scanBoundaryHistory_not_within : ¬ Within scanBoundaryParams scanBoundaryHistory := by
  intro h
  have hw := (h.1 scanBoundaryTx (by simp [scanBoundaryHistory])).2
  have hn : scanBoundaryTx.wf = false := by decide +kernel
  rw [hn] at hw
  cases hw

end SIS.Tree
