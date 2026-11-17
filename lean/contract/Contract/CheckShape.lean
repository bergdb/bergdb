/-
The contract package (bergdb 030-08): the shape clauses on a heap that a
program holds, for the trace checker. `checkShapeTx` is the writer's contract
(`checkTx`, Check.lean) and TREE after the transaction at its time, and
`checkShapeTx_sound` proves that it gives both. `checkTopTx` adds the top's
clauses and the link of the tree's space roots to the top: with it, a
transaction gives every premise of a step of `MeetsTop`
(`checkTopTx_sound`). Nothing here needs Mathlib.
-/
import Contract.Check
import Contract.Top

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

/-- The contract, TREE and the top for one traced transaction, computed: the
top tp before it, tp' after it. -/
def checkTopTx (p : Params) (i : Time) (h : Heap) (tp : Top) (ops : List Op) (D : List NodeId)
    (h' : Heap) (tp' : Top) : Bool :=
  checkShapeTx p i h ops D h' && topStepB i tp tp' && h'.roots == rootsOf tp'

/-- What the trace checker computes for a transaction is a step of
`MeetsTop`: the contract, TREE, the top's clauses and the roots' link. -/
theorem checkTopTx_sound (p : Params) (i : Time) (h : Heap) (tp : Top) (ops : List Op)
    (D : List NodeId) (h' : Heap) (tp' : Top) (hc : checkTopTx p i h tp ops D h' tp' = true) :
    Contract p i h.tree ops D h'.tree ∧ TreeOk (h'.tree.at i) ∧ TopStep i tp tp' ∧
      h'.tree.roots = rootsOf tp' := by
  simp only [checkTopTx, Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨h1, h2⟩, h3⟩ := hc
  obtain ⟨h4, h5⟩ := checkShapeTx_sound p i h ops D h' h1
  exact ⟨h4, h5, topStepB_sound i tp tp' h2, h3⟩

end Contract
