/-
bergdb 030-35: a nonempty users-only reference, two genuine steps, a
namespace-only store, intervening user puts and a delete. Since bergdb 031-06
(one record an action) the copies are marked per operation, and the second step
rides in a commit's record beside its action, a delete of an old KV the step
meets and a put above the iteration's end. A copy with a wrong value, a copy of
a KV the scan did not meet and a delete as a copy are rejected (`StepOpOK`); a
step's record that leaves out the row or an old KV met is rejected (`StepTx`).
And the key at which the trace checker's C-STEP checks a step's row is the
model's `reclaimRow` (`checker_row`; bergdb 030-39, F1).
-/
import Contract.ReclaimValues
import Contract.ReclaimStepsExample
import Check.Steps

namespace Contract.ValuesExample

open Contract Contract.PE Contract.PE.Example Contract.StepsExample

/-- The copy marks: the two copies of the first step (transaction 3, zero-based 2).
The second step (zero-based 4) has none: the action deletes the old KV it meets. -/
def maintenance (j : Nat) (op : Op) : Bool :=
  j == 2 && (op == .put [72] 5 || op == .put [80] 6)

theorem maintenanceOK : MaintenanceOK hS maintenance := by
  intro j hj
  refine ⟨by decide +kernel +revert, ?_⟩
  intro op hop hm
  have hj2 : j = 2 := by
    simp only [maintenance, Bool.and_eq_true, beq_iff_eq] at hm
    exact hm.1
  subst hj2
  refine ⟨2, endKey ((hS.tree 1).at 1), none, fun met _ => (false, met.length == 1), ?_⟩
  decide +kernel +revert

/-- The users-only reference: no operation at the namespace store and at the first
step; the users' value change and delete remain, and the action of the second
step's record, its delete and its put. -/
theorem users_only : userTransactions hS maintenance =
    [[.put [72] 5, .put [80] 6, .put [88] 7, .put [96] 8], [], [],
     [.put [76] 9, .put [88] 10, .del [80]], [.del [96], .put [100] 11]] := by
  decide +kernel

theorem preserves_at_every_time : ∀ t, t ≤ hS.txs.length →
    (contents ((hS.tree t).at t)).filter (fun kv => userKey kv.1) =
      refMap ((userTransactions hS maintenance).take t) :=
  user_contents_at (pe_full cfE_ok FullExample.capE lenS keysS histS).1 (by decide) maintenanceOK

/-- The final values are users' values, including the changed value 10, the
absence of the deleted keys and the put of the step's record's action; neither row
version enters the reference. -/
theorem final_users : (contents ((hS.tree 5).at 5)).filter (fun kv => userKey kv.1) =
    [([72], 5), ([76], 9), ([88], 10), ([100], 11)] := by
  rw [preserves_at_every_time 5 (by decide +kernel), users_only]
  decide

def firstScan : ScanOut := stepScan hS (endKey ((hS.tree 1).at 1)) none
  ⟨2, fun met _ => (false, met.length == 1)⟩

/-- A copy with another value than the key's before the record is rejected. -/
theorem wrong_value_rejected : ¬ StepOpOK hS 2 2 firstScan (.put [72] 999) := by
  decide +kernel

/-- A copy of a KV that the step's scan did not meet is rejected. -/
theorem unmet_copy_rejected : ¬ StepOpOK hS 2 2 firstScan (.put [88] 7) := by
  decide +kernel

/-- A copy is never a delete. -/
theorem delete_copy_rejected : ¬ StepOpOK hS 2 2 firstScan (.del [88]) := by
  decide +kernel

theorem missing_row_rejected : ¬ StepTx hS 2 2 firstScan
    [.put [72] 5, .put [80] 6] := by
  decide +kernel

/-- A step's record that writes neither a copy nor an action's operation at an
old KV met ([80]) is rejected. -/
theorem unwritten_rejected : ¬ StepTx hS 2 2 firstScan
    [.put [72] 5, .put reclaimRow 2] := by
  decide +kernel

/-- The second step's record, a commit's, meets `StepTx`: the old KV [96] that
its scan meets is written by the action's delete (bergdb 031-06). -/
theorem mixed_step : StepTx hS 2 4
    (stepScan hS (endKey ((hS.tree 1).at 1)) (some [80]) ⟨4, fun _ _ => (false, false)⟩)
    [.del [96], .put [100] 11, .put reclaimRow 3] := by
  decide +kernel

/-- The trace checker's C-STEP checks each step's row at the model's key
(`SIS.Check.reclaimRowKey`, lean/Check/Tree.lean since bergdb 031-06; bergdb
030-39, F1). -/
theorem checker_row : SIS.Check.reclaimRowKey = reclaimRow := rfl

end Contract.ValuesExample
