import SIS.Tree.GetLatest
import SIS.Tree.WriterSteps

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

attribute [local cbv_eval] appendKlongs_step_dead
attribute [local cbv_opaque] appendKlongs putSegs

@[local cbv_eval] theorem putSegs_one_cbv (key : Key) (value : Option Nat) (cv : Nat)
    (x : NodeId) : putSegs key value [cv] x = setValue x cv key value := putSegs.eq_2 key value x cv

@[local cbv_eval] theorem putSegs_two_cbv (key : Key) (value : Option Nat) (cv d : Nat)
    (rest : List Nat) (x : NodeId) :
    putSegs key value (cv :: d :: rest) x = (do
      let r ← setNode x cv value.isSome
      match r with
      | none => pure true
      | some next => putSegs key value (d :: rest) next) :=
  putSegs.eq_3 key value x cv (d :: rest) (by simp)

theorem pointersOK_of_all (P : Struct BVal)
    (h : P.all (fun q => q.2.hist.all (fun e => (bptrs e.val).all (fun y => (P.get? y).isSome))) =
      true) : PointersOK P := by
  intro q hq e he y hy
  have h1 := List.all_eq_true.mp h q hq
  have h2 := List.all_eq_true.mp h1 e he
  exact List.all_eq_true.mp h2 y hy

/-- Node size 8, two segments, height 0. -/
def shP : Params := { M := 8, G := 1, H := 0 }

/-- The space root (node 1, a segment leaf) holds the long segments 56 and
120, both naming the tree of node 3 (a leaf of the second segment), which
holds the short segment 8 with value 5 (hash 100). -/
def shStruct : Struct BVal :=
  [(root, { level := shP.rootLevel, isData := false, hist := [⟨0, .top 2⟩] }),
   (1, { level := shP.keyLevel 0 0, isData := false,
         hist := [⟨1, .key 56 3⟩, ⟨1, .key 120 3⟩] }),
   (2, { level := shP.topLevel 0, isData := false, hist := [⟨0, .rootKey 1⟩] }),
   (3, { level := shP.keyLevel 1 0, isData := false, hist := [⟨1, .key 8 5⟩] }),
   (5, { level := 0, isData := true, hist := [⟨1, .data 100⟩] })]

/-- A put of the key [56, 8] with the hash 200. -/
def shTx : Tx := { base := 6, ops := [.put [56, 8] 200] }

/-- The transaction's change at time 2. -/
def shChanges : Changes BVal :=
  match exec? shP shTx 2 (view (treeSpec shP) shStruct 1) with
  | .ok c => c
  | .error _ => { new := [], adds := [] }

theorem shExec_isOk : isOk (exec? shP shTx 2 (view (treeSpec shP) shStruct 1)) = true := by
  decide +kernel

theorem shExec : exec? shP shTx 2 (view (treeSpec shP) shStruct 1) = .ok shChanges := by
  have h := shExec_isOk
  unfold shChanges
  revert h
  cases exec? shP shTx 2 (view (treeSpec shP) shStruct 1) with
  | error e => intro h; simp [isOk] at h
  | ok c => intro _; rfl

set_option cbv.maxSteps 20000000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem shBefore_inv : InvOK shP shStruct 1 := by
  unfold InvOK
  cbv

theorem shBefore_ptrs : PointersOK shStruct := by
  unfold PointersOK
  decide +kernel

theorem shBefore_times : StructTimesLE shStruct 1 := by
  unfold StructTimesLE
  decide +kernel

set_option cbv.maxSteps 20000000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem shAfter_inv : InvOK shP (shStruct.apply 2 shChanges) 2 := by
  unfold InvOK
  cbv

set_option cbv.maxSteps 20000000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem shAfter_ptrs : PointersOK (shStruct.apply 2 shChanges) := by
  apply pointersOK_of_all
  cbv

theorem shGet_before : get shP (viewOf shStruct) 1 [120, 8] = some 100 := by
  decide +kernel

set_option cbv.maxSteps 20000000 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 20000000 in
theorem shGet_after : get shP (viewOf (shStruct.apply 2 shChanges)) 2 [120, 8] = some 200 := by
  cbv

/-- A transaction from a fault-free structure, with every premise `Within`
asks of a transaction (keys in order and well formed, a fresh base, no
error), gives a fault-free structure in which a key that no operation names
has another value. -/
theorem sharedSegment_changes_other_key :
    ∃ (p : Params) (P : Struct BVal) (tx : Tx) (c : Changes BVal),
      InvOK p P 1 ∧ PointersOK P ∧ StructTimesLE P 1 ∧
      tx.sorted = true ∧ tx.wf = true ∧ (∀ q ∈ P, q.1 < tx.base) ∧
      exec? p tx 2 (view (treeSpec p) P 1) = .ok c ∧
      InvOK p (P.apply 2 c) 2 ∧ PointersOK (P.apply 2 c) ∧
      keyWf [120, 8] = true ∧ (∀ op ∈ tx.ops, op.key ≠ [120, 8]) ∧
      get p (viewOf (P.apply 2 c)) 2 [120, 8] ≠ get p (viewOf P) 1 [120, 8] := by
  refine ⟨shP, shStruct, shTx, shChanges, shBefore_inv, shBefore_ptrs, shBefore_times,
    by decide, by decide, by decide, shExec, shAfter_inv, shAfter_ptrs, by decide, by decide, ?_⟩
  rw [shGet_before, shGet_after]
  decide

end SIS.Tree
