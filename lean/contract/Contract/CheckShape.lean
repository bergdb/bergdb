/-
The contract package (bergdb 030-08): the shape clauses on a heap that a
program holds, for the trace checker. `checkShapeTx` is the writer's contract
(`checkTx`, Check.lean) and TREE after the transaction at its time, and
`checkShapeTx_sound` proves that it gives both. Nothing here needs Mathlib.
-/
import Contract.Check
import Contract.Reach

namespace Contract

/-- The contract and TREE for one traced transaction, computed. -/
def checkShapeTx (p : Params) (i : Time) (h : Heap) (ops : List Op) (D : List NodeId)
    (h' : Heap) : Bool :=
  checkTx p i h ops D h' && treeOkB (h'.tree.at i)

/-- What the trace checker computes for a transaction is the contract with
TREE. -/
theorem checkShapeTx_sound (p : Params) (i : Time) (h : Heap) (ops : List Op)
    (D : List NodeId) (h' : Heap) (hc : checkShapeTx p i h ops D h' = true) :
    Contract p i h.tree ops D h'.tree ∧ TreeOk (h'.tree.at i) := by
  simp only [checkShapeTx, Bool.and_eq_true] at hc
  exact ⟨checkTx_sound p i h ops D h' hc.1, treeOkB_sound _ hc.2⟩

end Contract
