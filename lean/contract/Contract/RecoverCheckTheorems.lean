/-
The contract package (bergdb 030-14, 028-24): the verdict on K-LEVEL
(`kindsHistoryOk`, RecoverCheck.lean, computed by the bridge checker) gives
the clause for the trace's history. Apart from RecoverCheck.lean so that the
checkers build without Mathlib.
-/
import Mathlib.Tactic
import Contract.RecoverCheck
import Contract.Proof.BridgeInv

namespace Contract

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
