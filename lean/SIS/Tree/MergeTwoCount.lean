/-
The merges into two nodes of a transaction (bergdb 024-22, TP33): at most one
a delete that deletes. `mergeUp` returns after a merge into two nodes, and a
delete runs `mergeUp` at most once; a put runs none. With the frame lemmas of
`MergeTwoFrame.lean`.
-/
import SIS.Tree.MergeTwoFrame

namespace SIS.Tree

open SIS SIS.Check

/-- The loop makes at most one merge into two nodes: after one it returns. -/
theorem twoLe_mergeUp (key : Key) (g fuel h : Nat) (merged : Bool) :
    TwoLe 1 (mergeUp key g fuel h merged) := by
  induction fuel generalizing h merged with
  | zero => exact twoLe_throw _ _
  | succ fuel ih =>
    apply twoLe_of_wp
    intro c w
    unfold mergeUp
    repeat' first
      | wpSimplify
      | twFrame5
      | (with_unfolding_none refine writerWP_mono (writerWP_merge_two _ _ _ _) ?_; intro _ _ _)
      | (with_unfolding_none refine writerWP_of_twoLe (ih _ _) _ _ _ ?_; intro _ _ _)
      | wpSplit
      | split
      | contradiction
      | ((try simp_all) <;> omega)

theorem twoLe_afterDelete (key : Key) (g h : Nat) : TwoLe 1 (afterDelete key g h) := by
  apply twoLe_of_wp
  intro c w
  unfold afterDelete
  repeat' first
    | wpSimplify
    | twFrame5
    | (with_unfolding_none refine writerWP_of_twoLe (twoLe_mergeUp _ _ _ _ _) _ _ _ ?_; intro _ _ _)
    | wpSplit
    | split
    | contradiction
    | ((try simp_all) <;> omega)

/-- A noop delete makes no merge into two nodes; a delete that deletes, at most one. -/
theorem writerWP_deleteUpward_two (c : Ctx) (w : W) (leaf : NodeId) (depth cv : Nat) (key : Key) :
    WriterWP (deleteUpward leaf depth cv key) c w
      (fun noop v => twoNotes v ≤ twoNotes w + if noop then 0 else 1) := by
  unfold deleteUpward
  repeat' first
    | wpSimplify
    | twFrame5
    | (refine writerWP_of_twoLe (twoLe_segmentCount _ _) _ _ _ ?_; intro _ _ _)
    | (refine writerWP_of_twoLe (twoLe_unlinkLoop _ _ _) _ _ _ ?_; intro _ _ _)
    | (with_unfolding_none refine writerWP_of_twoLe (twoLe_climb _) _ _ _ ?_; intro _ _ _)
    | (with_unfolding_none refine writerWP_of_twoLe (twoLe_appendDeleteKlong _ _ _) _ _ _ ?_; intro _ _ _)
    | (with_unfolding_none refine writerWP_of_twoLe (twoLe_emptyKeyNext _ _) _ _ _ ?_; intro _ _ _)
    | (with_unfolding_none refine writerWP_of_twoLe (twoLe_afterDelete _ _ _) _ _ _ ?_; intro _ _ _)
    | (with_unfolding_none refine writerWP_of_twoLe (twoLe_mergeUp _ _ _ _ _) _ _ _ ?_; intro _ _ _)
    | wpSplit
    | split
    | contradiction
    | ((try simp_all) <;> omega)

/-- The merges into two nodes an operation may make, with its noop result. -/
def opTwoBudget (op : Tree.Op) (noop : Bool) : Nat :=
  match op with
  | .put _ _ => 0
  | .del _ => if noop then 0 else 1

theorem writerWP_setValue_two (c : Ctx) (w : W) (segRoot : NodeId) (cv : Nat)
    (key : Key) (value : Option Nat) :
    WriterWP (setValue segRoot cv key value) c w
      (fun noop v => twoNotes v ≤ twoNotes w + match value with
        | some _ => 0
        | none => if noop then 0 else 1) := by
  unfold setValue
  repeat' first
    | wpSimplify
    | twFrame5
    | (refine writerWP_mono (writerWP_deleteUpward_two _ _ _ _ _ _) ?_; intro _ _ _)
    | wpSplit
    | split
    | contradiction
    | ((try simp_all) <;> omega)

theorem writerWP_putSegs_two (c : Ctx) (w : W) (key : Key) (value : Option Nat)
    (segs : List Nat) (segRoot : NodeId) :
    WriterWP (putSegs key value segs segRoot) c w
      (fun noop v => twoNotes v ≤ twoNotes w + match value with
        | some _ => 0
        | none => if noop then 0 else 1) := by
  induction segs generalizing w segRoot with
  | nil => exact writerWP_throw _ _ _ _
  | cons cv rest ih =>
    cases rest with
    | nil => exact writerWP_setValue_two _ _ _ _ _ _
    | cons next rest =>
      unfold putSegs
      repeat' first
        | wpSimplify
        | twFrame5
        | (refine writerWP_of_twoLe (twoLe_setNode _ _ _) _ _ _ ?_; intro _ _ _)
        | (refine writerWP_mono (ih _ _) ?_; intro _ _ _)
        | wpSplit
        | split
        | contradiction
        | ((try simp_all) <;> omega)

theorem writerWP_putKv_two (c : Ctx) (w : W) (op : Tree.Op) :
    WriterWP (putKv op) c w (fun noop v => twoNotes v ≤ twoNotes w + opTwoBudget op noop) := by
  unfold putKv
  repeat' first
    | wpSimplify
    | twFrame5
    | (refine writerWP_of_twoLe twoLe_findRoot _ _ _ ?_; intro _ _ _)
    | (refine writerWP_mono (writerWP_putSegs_two _ _ _ _ _ _) ?_; intro _ _ _)
    | wpSplit
    | split
    | contradiction
    | ((try simp_all [opTwoBudget]) <;> omega)

theorem deletesOf_cons_two (op : Tree.Op) (ops : List Tree.Op) (noop : Bool) (noops : List Bool) :
    deletesOf { base := 0, ops := op :: ops } (noop :: noops) =
      opTwoBudget op noop + deletesOf { base := 0, ops := ops } noops := by
  cases op <;> cases noop <;> simp [deletesOf, opTwoBudget, Nat.add_comm]

theorem writerWP_ops_two (c : Ctx) (w : W) (ops : List Tree.Op) :
    WriterWP (ops.mapM putKv) c w
      (fun noops v => twoNotes v ≤ twoNotes w + deletesOf { base := 0, ops := ops } noops) := by
  induction ops generalizing w with
  | nil => simp [List.mapM_nil, writerWP_pure, deletesOf]
  | cons op ops ih =>
    rw [List.mapM_cons]
    simp only [writerWP_bind]
    refine writerWP_mono (writerWP_putKv_two c w op) ?_
    intro noop v hhead
    refine writerWP_mono (ih v) ?_
    intro noops v1 htail
    simp only [writerWP_pure, deletesOf_cons_two]
    omega

/-- The merges into two nodes of a successful transaction are at most its
deletes that deleted (those that changed a node). No premise on the
transaction, the run or the parameters. -/
theorem execW_twoMerges_le_deletes (p : Params) (tx : Tx) (i : Time) (v : View BVal)
    (noops : List Bool) (w : W) (h : execW p tx i v = .ok (noops, w)) :
    twoNotes w ≤ deletesOf tx noops := by
  unfold execW runOps runOpsFrom at h
  cases hz : lastTop v with
  | none => simp [hz] at h
  | some z =>
    simp only [hz] at h
    cases ht : topOf p (rootless v) z with
    | error e => simp [ht] at h
    | ok top =>
      simp only [ht] at h
      have hr := boundsOK_ok p _ noops w h
      have hb := writerWP_ops_two { p := p, i := i, view := rootless v }
        { next := tx.base, top := top } tx.ops noops w hr
      simpa [deletesOf, twoNotes] using hb

end SIS.Tree
