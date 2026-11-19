/-
The contract package (bergdb 030-14): K-LEVEL on a trace, computed, for the
bridge checker (BridgeCheck.lean). The kind function of a trace is the TREE
line's (`kindOfHeight h`, Recover.lean). The verdict on a whole trace
(`kindsHistoryOk`) gives the clause for the history that the checker builds
from the trace's lines (`kindsHistoryOk_meets`, RecoverCheckTheorems.lean),
the history that `fullHistoryOk_meets` speaks of. No Mathlib: the checkers
build without it (bergdb 028-24).
-/
import Contract.Recover
import Contract.BridgeHeap

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

end Contract
