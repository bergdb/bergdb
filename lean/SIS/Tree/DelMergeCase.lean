/-
Case 4 of 024-12's assembly, a delete with the merges on (bergdb 024-22): the
parts of the merge's and the collapse's steps that the books, the tree lemmas
and the reading do not give (`StepInv`, `CollRange`), `PutInv` after a step
from them, and the path facts carried over. The reduction is at a reading fuel
above the writer's (`DelMergeCaseF.lean`, `DelMergeCaseF3.lean`,
`CollapseCascade.lean`).
-/
import SIS.Tree.GetMergeInv
import SIS.Tree.MergeTreeInv
import SIS.Tree.WriterMergeUpLoop

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- `PutInv` and `PutInvG` after a step, from the books after it and the step's
tree facts. -/
theorem putInv_after_step (c : Ctx) (base : View BVal) (v : W) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (hb : PutBook c B top0 v)
    (hT : TreeOK (wNode c.p base v) c.i v.top.rootKey)
    (hu : ∀ y, ReachS (wNode c.p base v) c.i v.top.rootKey y → v.taken.contains y = false)
    (hR : RangeOrder (wNode c.p base v) c.i v.top.rootKey) :
    PutInv c base v ∧ PutInvG c base v := by
  have hG := putInvG_of_book c base B top0 v hB hb
  exact ⟨putInv_of_parts c base v hG hT hu (leafOrder_of_rangeOrder _ _ _ hR hG.times), hG⟩

/-- The path facts carry over to a state with the same path, top and taken ids
and the overlay's nodes kept. -/
theorem pathOK_transport (c : Ctx) (v v' : W) (d : Nat) (X : Nat → NodeId) (K : Nat → Nat)
    (Nn : Nat → KNode) (h : PathOK c v d X K Nn) (hp : v'.path = v.path)
    (hl : ∀ z zn, v.nodes.lookup z = some zn → v'.nodes.lookup z = some zn)
    (ht : v'.taken = v.taken) (htop : v'.top = v.top) : PathOK c v' d X K Nn := by
  obtain ⟨hX, hK, hS2, hlink, h0⟩ := h
  refine ⟨fun i hi => by rw [hp]; exact hX i hi, fun i h1 h2 => by rw [hp]; exact hK i h1 h2,
    fun i hi => ⟨hl _ _ (hS2 i hi).1, by rw [ht]; exact (hS2 i hi).2⟩, hlink, by rw [htop]; exact h0⟩

/-! ## The obligations are not void

A run within reach (`Within`'s conditions as a Bool) of two transactions, twelve
puts and then ten deletes of them, node size 8, G 1, H 2, the merges on
(mergeBelow 2, mergeMax 3, splitAbove 4): every state between the deletes'
operations fits the fuel, and the writer merges in the deletes. So the
hypotheses of `OpGetCaseOK p R DelMergeCase` and of `MergeStepOKF` (a merge of
the loop inside a delete) are met by a run. -/

/-- `Within p ts` as a Bool, and the run's last transaction tx = ts's last: every
state between its operations fits the fuel, its deletes run with the merges on,
and the writer merged at least once in it. -/
def dmCheck (p : Params) (ts : List Tx) (tx : Tx) : Bool :=
  let all := ts ++ [tx]
  all.all (fun t => t.sorted && t.wf) &&
  (List.range all.length).all (fun j =>
    match all[j]? with
    | none => false
    | some tj => (treeRun p (all.take j)).all (fun q => decide (q.1 < tj.base)) &&
        isOk (exec? p tj (j + 1) (view (treeSpec p) (treeRun p (all.take j)) j))) &&
  p.merges &&
  let v := view (treeSpec p) (treeRun p ts) ts.length
  match lastTop v with
  | none => false
  | some z =>
    match topOf p (ctxOf p ts).view z with
    | .error _ => false
    | .ok top =>
      (List.range (tx.ops.length + 1)).all (fun k =>
        match ((tx.ops.take k).mapM putKv) (ctxOf p ts) (wInit tx top) with
        | .ok (_, w) => asmFitsB p (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey
        | .error _ => false) &&
      tx.ops.any (fun o => match o with | .del _ => true | _ => false) &&
      match (tx.ops.mapM putKv) (ctxOf p ts) (wInit tx top) with
      | .ok (_, w) => decide (0 < w.merges)
      | .error _ => false
def dmP : Params := {M := 8, G := 1, H := 2, mergeBelow := 2, mergeMax := 3, splitAbove := 4}
def dmTs : List Tx := [{base := 1000, ops := (List.range 12).map (fun j => .put [120, 64*j+8] (j+1))}]
def dmTx : Tx := {base := 2000, ops := (List.range 10).map (fun j => .del [120, 64*j+8])}
#guard dmCheck dmP dmTs dmTx

end SIS.Tree
