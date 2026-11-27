/-
bergdb 030-25: the model of reclaim's steps is not vacuous. A history that PE
writes from the empty tree, of five transactions, with an iteration of two
steps that follow the model (`StepsOK`): the cut 2, so the four values put by
transaction 1 are old; the start t0 = 1, so E = [96]; transaction 2 puts a key
above E (as reclaim's table store does); the first step (transaction 3) stops
after two KVs and rewrites them, with its row; a user transaction (4) puts a
key behind the cursor, puts again a key ahead of it, and deletes a key
already rewritten; the last step
(transaction 5) meets the rest up to E, [88], whose node is new, and [96], old,
which the record's action deletes, so that no copy of it is made (bergdb 031-06:
a step rides in a commit's record, and Java leaves out a copy at a key that the
action writes); the action also puts [100], above E, and the record puts the row.
Every key live before the first step is old, and each is written from the first
step to the last: `IterationOK` from 3 to 5, by `iterationOK_steps`.
-/
import Contract.ReclaimSteps
import Contract.PeFullExample

namespace Contract.StepsExample

open Contract Contract.PE Contract.PE.Example

/-- The operations: four keys put; a reserved key above them; step 1 (two
copies and the current row); user puts behind and ahead of the cursor and
a delete; step 2 in a commit's record (bergdb 031-06): the action's delete of
the old KV [96] and its put of [100], and the row. -/
def txs5 : List (List Op) :=
  [[.put [72] 5, .put [80] 6, .put [88] 7, .put [96] 8],
   [.put [0x495ac0599d19f8, 0x195b98dadbc04030] 1],
   [.put [72] 5, .put [80] 6, .put reclaimRow 2],
   [.put [76] 9, .put [88] 10, .del [80]],
   [.del [96], .put [100] 11, .put reclaimRow 3]]

theorem accS : (peHist cfE txs5).isSome = true := by decide +kernel

/-- The history and its tops. -/
def hS : BHist := ((peHist cfE txs5).get accS).1

def topS : Nat → Top := ((peHist cfE txs5).get accS).2

theorem histS : peHist cfE txs5 = some (hS, topS) := by
  rw [← Option.some_get accS]
  rfl

theorem keysS : ∀ ops ∈ txs5, (ops.map Op.key).Nodup := by decide

theorem lenS : txs5.length < 2 ^ 48 - 1 := by decide

/-- The iteration: cut 2, start 1; step 1 is transaction 3 and stops after its
second KV; step 2 is transaction 5, a commit's record, and does not stop. -/
def itS : Iteration :=
  { c := 2, t0 := 1,
    steps := [⟨2, fun met _ => (false, met.length == 1)⟩, ⟨4, fun _ _ => (false, false)⟩] }

instance (h : BHist) (c : Nat) (out : ScanOut) (ops : List Op) :
    Decidable (StepTx h c out ops) := by
  unfold StepTx
  infer_instance

/-- The steps follow the model. -/
theorem stepsOK : StepsOK hS itS := by
  refine ⟨by simp [itS], by decide, ?_⟩
  simp only [itS, StepsFrom, reduceCtorEq, false_implies, true_implies, and_true, true_and]
  decide +kernel

/-- Before the first step, the four keys of transaction 1 are live, each with
its old value node. -/
theorem old_before : ((idContents ((hS.tree 2).at 2)).filter (fun kv => oldNode hS 2 kv.2)).map
    Prod.fst = [[72], [80], [88], [96]] := by
  decide +kernel

/-- What each step's scan met. -/
theorem met1 : (stepScan hS (endKey ((hS.tree 1).at 1)) none ⟨2, fun met _ =>
    (false, met.length == 1)⟩).met.map Prod.fst = [[72], [80]] := by
  decide +kernel

theorem met2 : (stepScan hS (endKey ((hS.tree 1).at 1)) (some [80]) ⟨4, fun _ _ =>
    (false, false)⟩).met.map Prod.fst = [[88], [96]] := by
  decide +kernel

/-- The iteration meets `IterationOK`, from the first step (3) to the last (5). -/
theorem iterationOK : IterationOK hS 2 3 5 := by
  have hf := pe_full cfE_ok FullExample.capE lenS keysS histS
  exact iterationOK_steps hf.1 (by decide) (pe_valNew cfE_ok FullExample.capE lenS keysS histS)
    stepsOK

end Contract.StepsExample
