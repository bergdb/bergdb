/-
bergdb 030-35: a nonempty users-only reference, two genuine steps, a
namespace-only store, intervening user puts and a delete. Wrong-value
rewrites, extra puts and deletes are rejected by the strengthened model.
-/
import Contract.ReclaimValues
import Contract.ReclaimStepsExample

namespace Contract.ValuesExample

open Contract Contract.PE Contract.PE.Example Contract.StepsExample

/-- The namespace store and both reclaim steps are maintenance. -/
def maintenance (j : Nat) : Bool := j == 1 || j == 2 || j == 4

theorem marked : ∀ st ∈ itS.steps, maintenance st.j = true := by decide

theorem maintenanceOK : MaintenanceOK hS maintenance := by
  intro j hj hm
  have hcases : j = 1 ∨ j = 2 ∨ j = 4 := by
    simpa [maintenance, Bool.or_eq_true, beq_iff_eq, or_assoc] using hm
  rcases hcases with rfl | rfl | rfl
  · left
    decide +kernel +revert
  · right
    refine ⟨2, endKey ((hS.tree 1).at 1), none, fun met _ => (false, met.length == 1), ?_⟩
    decide +kernel +revert
  · right
    refine ⟨2, endKey ((hS.tree 1).at 1), some [80], fun _ _ => (false, false), ?_⟩
    decide +kernel +revert

/-- The users-only reference has empty transactions at all maintenance
times; the users' value change and delete remain. -/
theorem users_only : userTransactions hS maintenance =
    [[.put [72] 5, .put [80] 6, .put [88] 7, .put [96] 8], [], [],
     [.put [76] 9, .put [88] 10, .del [80]], []] := by
  decide +kernel

theorem preserves_at_every_time : ∀ t, t ≤ hS.txs.length →
    (contents ((hS.tree t).at t)).filter (fun kv => userKey kv.1) =
      refMap ((userTransactions hS maintenance).take t) :=
  user_contents_at (pe_full cfE_ok FullExample.capE lenS keysS histS).1 (by decide) maintenanceOK

/-- The final values are users' values, including the changed value 10 and
the absence of the deleted key; neither row version enters the reference. -/
theorem final_users : (contents ((hS.tree 5).at 5)).filter (fun kv => userKey kv.1) =
    [([72], 5), ([76], 9), ([88], 10), ([96], 8)] := by
  rw [preserves_at_every_time 5 (by decide +kernel), users_only]
  decide

def firstScan : ScanOut := stepScan hS (endKey ((hS.tree 1).at 1)) none
  ⟨2, fun met _ => (false, met.length == 1)⟩

/-- The formerly permitted wrong-value maintenance put is now rejected,
even with the required old keys, row and distinct operation keys. -/
theorem wrong_value_rejected : ¬ StepTx hS 2 2 firstScan
    [.put [72] 999, .put [80] 6, .put reclaimRow 2] := by
  decide +kernel

theorem extra_put_rejected : ¬ StepTx hS 2 2 firstScan
    [.put [72] 5, .put [80] 6, .put [88] 7, .put reclaimRow 2] := by
  decide +kernel

theorem extra_delete_rejected : ¬ StepTx hS 2 2 firstScan
    [.put [72] 5, .put [80] 6, .del [88], .put reclaimRow 2] := by
  decide +kernel

theorem missing_row_rejected : ¬ StepTx hS 2 2 firstScan
    [.put [72] 5, .put [80] 6] := by
  decide +kernel

end Contract.ValuesExample
