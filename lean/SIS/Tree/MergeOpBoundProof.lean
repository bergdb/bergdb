/-
Merge counts in the writer (bergdb 024-22, TP32).
-/
import SIS.Tree.MergeFrame
import SIS.Tree.MergeHeightTags

namespace SIS.Tree

open SIS SIS.Check

/-- The loop makes at most one merge per unit of fuel. -/
theorem mergesLe_mergeUp (key : Key) (g fuel h : Nat) (merged : Bool) :
    MergesLe fuel (mergeUp key g fuel h merged) := by
  induction fuel generalizing h merged with
  | zero => exact mergesLe_throw _ _
  | succ fuel ih =>
    apply mergesLe_of_wp
    intro c w
    unfold mergeUp
    repeat' first
      | wpSimplify
      | wpFrame5
      | (with_unfolding_none refine writerWP_of_mergesLe (mergesLe_merge _ _) _ _ _ ?_; intro _ _ _)
      | (with_unfolding_none refine writerWP_of_mergesLe (ih _ _) _ _ _ ?_; intro _ _ _)
      | wpSplit
      | split
      | contradiction
      | ((try simp_all) <;> omega)

/-- A bound with the reader fixed, so its parameters can set the cost. -/
def MergesLeAt {α : Type} (c : Ctx) (k : Nat) (f : M α) : Prop :=
  ∀ w, WriterWP f c w (fun _ v => v.merges ≤ w.merges + k)

theorem writerWP_of_mergesLeAt {α : Type} {c : Ctx} {k : Nat} {f : M α}
    (hf : MergesLeAt c k f) (w : W) (post : α → W → Prop)
    (hp : ∀ r v, v.merges ≤ w.merges + k → post r v) : WriterWP f c w post := by
  intro r v h
  exact hp r v (hf w r v h)

theorem mergesLeAt_afterDelete (c : Ctx) (key : Key) (g h : Nat) :
    MergesLeAt c c.p.fuel (afterDelete key g h) := by
  intro w
  unfold afterDelete
  repeat' first
    | wpSimplify
    | wpFrame5
    | (with_unfolding_none refine writerWP_of_mergesLe (mergesLe_mergeUp _ _ _ _ _) _ _ _ ?_; intro _ _ _)
    | wpSplit
    | split
    | contradiction
    | ((try simp_all) <;> omega)

/-- A noop delete makes no merges; a delete that changes a node runs one loop. -/
theorem writerWP_deleteUpward (c : Ctx) (w : W) (leaf : NodeId) (depth cv : Nat) (key : Key) :
    WriterWP (deleteUpward leaf depth cv key) c w
      (fun noop v => v.merges ≤ w.merges + if noop then 0 else c.p.fuel) := by
  unfold deleteUpward
  repeat' first
    | wpSimplify
    | wpFrame5
    | (refine writerWP_of_mergesLe (mergesLe_segmentCount _ _) _ _ _ ?_; intro _ _ _)
    | (refine writerWP_of_mergesLe (mergesLe_unlinkLoop _ _ _) _ _ _ ?_; intro _ _ _)
    | (with_unfolding_none refine writerWP_of_mergesLe (mergesLe_climb _) _ _ _ ?_; intro _ _ _)
    | (with_unfolding_none refine writerWP_of_mergesLe (mergesLe_appendDeleteKlong _ _ _) _ _ _ ?_; intro _ _ _)
    | (with_unfolding_none refine writerWP_of_mergesLe (mergesLe_emptyKeyNext _ _) _ _ _ ?_; intro _ _ _)
    | (with_unfolding_none refine writerWP_of_mergesLeAt (mergesLeAt_afterDelete _ _ _ _) _ _ ?_; intro _ _ _)
    | (with_unfolding_none refine writerWP_of_mergesLe (mergesLe_mergeUp _ _ _ _ _) _ _ _ ?_; intro _ _ _)
    | wpSplit
    | split
    | contradiction
    | ((try simp_all) <;> omega)

theorem writerWP_setValue (c : Ctx) (w : W) (segRoot : NodeId) (cv : Nat)
    (key : Key) (value : Option Nat) :
    WriterWP (setValue segRoot cv key value) c w
      (fun noop v => v.merges ≤ w.merges + match value with
        | some _ => 0
        | none => if noop then 0 else c.p.fuel) := by
  unfold setValue
  repeat' first
    | wpSimplify
    | wpFrame5
    | (refine writerWP_mono (writerWP_deleteUpward _ _ _ _ _ _) ?_; intro _ _ _)
    | wpSplit
    | split
    | contradiction
    | ((try simp_all) <;> omega)

theorem writerWP_putSegs (c : Ctx) (w : W) (key : Key) (value : Option Nat)
    (segs : List Nat) (segRoot : NodeId) :
    WriterWP (putSegs key value segs segRoot) c w
      (fun noop v => v.merges ≤ w.merges + match value with
        | some _ => 0
        | none => if noop then 0 else c.p.fuel) := by
  induction segs generalizing w segRoot with
  | nil => exact writerWP_throw _ _ _ _
  | cons cv rest ih =>
    cases rest with
    | nil => exact writerWP_setValue _ _ _ _ _ _
    | cons next rest =>
      unfold putSegs
      repeat' first
        | wpSimplify
        | wpFrame5
        | (refine writerWP_of_mergesLe (mergesLe_setNode _ _ _) _ _ _ ?_; intro _ _ _)
        | (refine writerWP_mono (ih _ _) ?_; intro _ _ _)
        | wpSplit
        | split
        | contradiction
        | ((try simp_all) <;> omega)

/-- The merge budget of one operation, with its actual noop result. -/
def opMergeBudget (p : Params) (op : Tree.Op) (noop : Bool) : Nat :=
  match op with
  | .put _ _ => 0
  | .del _ => if noop then 0 else p.fuel

theorem writerWP_putKv (c : Ctx) (w : W) (op : Tree.Op) :
    WriterWP (putKv op) c w (fun noop v => v.merges ≤ w.merges + opMergeBudget c.p op noop) := by
  unfold putKv
  repeat' first
    | wpSimplify
    | wpFrame5
    | (refine writerWP_of_mergesLe mergesLe_findRoot _ _ _ ?_; intro _ _ _)
    | (refine writerWP_mono (writerWP_putSegs _ _ _ _ _ _) ?_; intro _ _ _)
    | wpSplit
    | split
    | contradiction
    | ((try simp_all [opMergeBudget]) <;> omega)

theorem deletesOf_cons_budget (p : Params) (op : Tree.Op) (ops : List Tree.Op)
    (noop : Bool) (noops : List Bool) :
    deletesOf { base := 0, ops := op :: ops } (noop :: noops) * p.fuel =
      opMergeBudget p op noop + deletesOf { base := 0, ops := ops } noops * p.fuel := by
  cases op <;> cases noop <;>
    simp [deletesOf, opMergeBudget, Nat.add_mul, Nat.add_comm]

theorem writerWP_ops (c : Ctx) (w : W) (ops : List Tree.Op) :
    WriterWP (ops.mapM putKv) c w
      (fun noops v => v.merges ≤ w.merges + deletesOf { base := 0, ops := ops } noops * c.p.fuel) := by
  induction ops generalizing w with
  | nil => simp [List.mapM_nil, writerWP_pure, deletesOf]
  | cons op ops ih =>
    rw [List.mapM_cons]
    simp only [writerWP_bind]
    refine writerWP_mono (writerWP_putKv c w op) ?_
    intro noop v hhead
    refine writerWP_mono (ih v) ?_
    intro noops v1 htail
    simp only [writerWP_pure, deletesOf_cons_budget]
    omega

theorem boundsOK_ok (p : Params) (r : Except String (List Bool × W))
    (noops : List Bool) (w : W) (h : boundsOK p r = .ok (noops, w)) :
    r = .ok (noops, w) := by
  cases r with
  | error e => simp [boundsOK] at h
  | ok v =>
    rcases v with ⟨bs, v⟩
    cases hf : v.outside.find? (fun q => !v.taken.contains q.1) with
    | none => simpa only [boundsOK, hf] using h
    | some q =>
      rcases q with ⟨x, g, height⟩
      simp only [boundsOK, hf] at h
      cases h

/-- The unconditional bound supplied by the merge loop's fuel. -/
theorem execW_mergeFuelBound (p : Params) (tx : Tx) (i : Time) (v : View BVal)
    (noops : List Bool) (w : W) (h : execW p tx i v = .ok (noops, w)) :
    w.merges ≤ deletesOf tx noops * p.fuel := by
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
      have hb := writerWP_ops { p := p, i := i, view := rootless v }
        { next := tx.base, top := top } tx.ops noops w hr
      simpa [deletesOf] using hb

theorem boundsOK_outside_taken (p : Params) (r : Except String (List Bool × W))
    (noops : List Bool) (w : W) (h : boundsOK p r = .ok (noops, w)) :
    ∀ q ∈ w.outside, w.taken.contains q.1 = true := by
  have hr := boundsOK_ok p r noops w h
  rw [hr] at h
  cases hf : w.outside.find? (fun q => !w.taken.contains q.1) with
  | some q =>
    rcases q with ⟨x, g, height⟩
    simp only [boundsOK, hf] at h
    cases h
  | none =>
    have hn := List.find?_eq_none.mp hf
    intro q hq
    simpa using hn q hq

/-- A height above H is checked at the transaction's end. -/
theorem execW_heightTagged (p : Params) (tx : Tx) (i : Time) (v : View BVal)
    (noops : List Bool) (w : W) (h : execW p tx i v = .ok (noops, w)) :
    HeightTagged p w := by
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
      exact heightTagged_ops tx.ops { p := p, i := i, view := rootless v }
        { next := tx.base, top := top } (by simp [HeightTagged]) noops w hr

/-- Every cached node above H was taken back in a successful transaction. -/
theorem execW_heightsTaken (p : Params) (tx : Tx) (i : Time) (v : View BVal)
    (noops : List Bool) (w : W) (h : execW p tx i v = .ok (noops, w)) :
    ∀ x g height, (x, g, height) ∈ w.gh → p.H < height →
      w.taken.contains x = true := by
  have tagged := execW_heightTagged p tx i v noops w h
  unfold execW runOps runOpsFrom at h
  cases hz : lastTop v with
  | none => simp [hz] at h
  | some z =>
    simp only [hz] at h
    cases ht : topOf p (rootless v) z with
    | error e => simp [ht] at h
    | ok top =>
      simp only [ht] at h
      intro x g height hx hh
      obtain ⟨q, hq, heq⟩ := tagged x g height hx hh
      have htaken := boundsOK_outside_taken p _ noops w h q hq
      simpa only [heq] using htaken

end SIS.Tree
