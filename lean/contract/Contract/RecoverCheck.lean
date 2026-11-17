/-
The contract package (bergdb 030-14): K-LEVEL on a trace, computed, for the
bridge checker (BridgeCheck.lean). The kind function of a trace is the TREE
line's (`kindOfHeight h`, Recover.lean). The verdict on a whole trace
(`kindsHistoryOk`) gives the clause for the history that the checker builds
from the trace's lines (`kindsHistoryOk_meets`), the history that
`fullHistoryOk_meets` speaks of.
-/
import Mathlib.Tactic
import Contract.Recover
import Contract.BridgeHeap
import Contract.Proof.BridgeInv

namespace Contract

/-- K-LEVEL at the start, computed over the nodes of the heap. -/
def startKindsOk (kind : Nat → Bool) (h0 : Heap) : Bool :=
  h0.objs.toList.all (fun xo => match xo.2 with
    | .key n => n.leaf == kind n.level
    | _ => true)

/-- K-LEVEL for the key nodes of D after every traced transaction. -/
def kindsStepsOk (kind : Nat → Bool) (steps : List TStep) : Bool :=
  steps.all (fun st => kindsOk kind st.heap.tree st.D)

/-- K-LEVEL on a whole trace. -/
def kindsHistoryOk (kind : Nat → Bool) (h0 : Heap) (steps : List TStep) : Bool :=
  startKindsOk kind h0 && kindsStepsOk kind steps

/-- The verdict gives the clause for the trace's history. -/
theorem kindsHistoryOk_meets (kind : Nat → Bool) (h0 : Heap) (c0 : SIS.Changes SIS.Check.BVal)
    (steps : List TStep) (hc : kindsHistoryOk kind h0 steps = true) :
    KindsOK kind (histOf h0 c0 steps) := by
  simp only [kindsHistoryOk, Bool.and_eq_true] at hc
  obtain ⟨h1, h2⟩ := hc
  constructor
  · intro x n hx
    have hm : (x, Obj.key n) ∈ h0.objs.toList :=
      Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hx
    have := List.all_eq_true.mp h1 _ hm
    simpa using this
  · intro j hj
    have hj' : j < steps.length := by simpa [histOf] using hj
    have := List.all_eq_true.mp h2 steps[j] (List.getElem_mem hj')
    have ht : (histOf h0 c0 steps).tree (j + 1) = steps[j].heap.tree := by
      rw [BHist.tree_succ _ hj]
      simp [histOf]
    rw [ht]
    simpa [histOf] using this

end Contract
