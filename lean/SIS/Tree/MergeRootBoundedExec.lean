import SIS.Tree.MergeRootHeight

namespace SIS.Tree

open SIS SIS.Check

theorem writerWP_afterDelete_rootHeightBound (c : Ctx) (w : W) (key : Key) (g h cap : Nat) :
    WriterWP (afterDelete key g h) c w
      (fun _ v => SeenHeightBound cap v → v.merges ≤ w.merges + cap) := by
  unfold afterDelete
  repeat' first
    | wpSimplify
    | whFrame
    | whBound (writerWP_mergeUp_rootHeightBound _ _ _ _ _ cap _ _) using (fields_mergeUp _ _ _ _ _)
    | wpSplit
    | split
    | contradiction
    | (intro hb; ((try simp_all) <;> grind only [seenHeightBound_of_sublist]))

theorem writerWP_deleteUpward_rootHeightBound (c : Ctx) (w : W) (leaf : NodeId)
    (depth cv : Nat) (key : Key) (cap : Nat) :
    WriterWP (deleteUpward leaf depth cv key) c w
      (fun noop v => SeenHeightBound cap v →
        v.merges ≤ w.merges + if noop then 0 else cap) := by
  unfold deleteUpward
  repeat' first
    | wpSimplify
    | whFrame
    | whBound (writerWP_afterDelete_rootHeightBound _ _ _ _ _ cap) using (fields_afterDelete _ _ _)
    | (refine writerWP_of_frame_growth (mergesLe_unlinkLoop _ _ _)
        (by growthFrom (fields_unlinkLoop _ _ _)) _ _ _ ?_; intro _ _ _ _)
    | whBound (writerWP_mergeUp_rootHeightBound _ _ _ _ _ cap _ _) using (fields_mergeUp _ _ _ _ _)
    | wpSplit
    | split
    | contradiction
    | (intro hb; ((try simp_all) <;> grind only [seenHeightBound_of_sublist]))

theorem writerWP_setValue_rootHeightBound (c : Ctx) (w : W) (root : NodeId) (cv : Nat)
    (key : Key) (value : Option Nat) (cap : Nat) :
    WriterWP (setValue root cv key value) c w
      (fun noop v => SeenHeightBound cap v → v.merges ≤ w.merges + match value with
        | some _ => 0
        | none => if noop then 0 else cap) := by
  unfold setValue
  repeat' first
    | wpSimplify
    | whFrame
    | whBound (writerWP_deleteUpward_rootHeightBound _ _ _ _ _ _ cap) using (fields_deleteUpward _ _ _ _)
    | wpSplit
    | split
    | contradiction
    | (intro hb; ((try simp_all) <;> grind only [seenHeightBound_of_sublist]))

theorem writerWP_putSegs_rootHeightBound (c : Ctx) (w : W) (key : Key) (value : Option Nat)
    (segs : List Nat) (root : NodeId) (cap : Nat) :
    WriterWP (putSegs key value segs root) c w
      (fun noop v => SeenHeightBound cap v → v.merges ≤ w.merges + match value with
        | some _ => 0
        | none => if noop then 0 else cap) := by
  induction segs generalizing w root with
  | nil => exact writerWP_throw _ _ _ _
  | cons cv rest ih =>
    cases rest with
    | nil => exact writerWP_setValue_rootHeightBound _ _ _ _ _ _ _
    | cons cv2 rest =>
      unfold putSegs
      repeat' first
        | wpSimplify
        | whFrame
        | whBound (ih _ _) using (fields_putSegs _ _ _ _)
        | wpSplit
        | split
        | contradiction
        | (intro hb; ((try simp_all) <;> grind only [seenHeightBound_of_sublist]))

def rootMergeBudget (cap : Nat) (op : Tree.Op) (noop : Bool) : Nat :=
  match op with
  | .put _ _ => 0
  | .del _ => if noop then 0 else cap

theorem writerWP_putKv_rootHeightBound (c : Ctx) (w : W) (op : Tree.Op) (cap : Nat) :
    WriterWP (putKv op) c w
      (fun noop v => SeenHeightBound cap v → v.merges ≤ w.merges + rootMergeBudget cap op noop) := by
  unfold putKv
  repeat' first
    | wpSimplify
    | whFrame
    | whBound (writerWP_putSegs_rootHeightBound _ _ _ _ _ _ cap) using (fields_putSegs _ _ _ _)
    | wpSplit
    | split
    | contradiction
    | (intro hb; ((try simp_all [rootMergeBudget]) <;> grind only [seenHeightBound_of_sublist]))

theorem deletesOf_cons_rootBudget (cap : Nat) (op : Tree.Op) (ops : List Tree.Op)
    (noop : Bool) (noops : List Bool) :
    deletesOf { base := 0, ops := op :: ops } (noop :: noops) * cap =
      rootMergeBudget cap op noop + deletesOf { base := 0, ops := ops } noops * cap := by
  cases op <;> cases noop <;>
    simp [deletesOf, rootMergeBudget, Nat.add_mul, Nat.add_comm]

theorem writerWP_ops_rootHeightBound (c : Ctx) (w : W) (ops : List Tree.Op) (cap : Nat) :
    WriterWP (ops.mapM putKv) c w
      (fun noops v => SeenHeightBound cap v →
        v.merges ≤ w.merges + deletesOf { base := 0, ops := ops } noops * cap) := by
  induction ops generalizing w with
  | nil => simp [List.mapM_nil, writerWP_pure, deletesOf]
  | cons op ops ih =>
    rw [List.mapM_cons, writerWP_bind]
    whBound (writerWP_putKv_rootHeightBound _ _ _ cap) using (fields_putKv _)
    simp only [writerWP_bind]
    whBound (ih _) using (fields_ops _)
    simp only [writerWP_pure, deletesOf_cons_rootBudget]
    intro hb
    grind only [seenHeightBound_of_sublist]

end SIS.Tree
