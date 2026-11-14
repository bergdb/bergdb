/-
The tree model (bergdb 024-12, TP4 and TP7): the writer keeps `PtrsOK`,
continued from SIS/Tree/WriterPtrsMerge.lean: the merges after a delete, the
upward unlink, a put, and a transaction (`execW_ptrsOK`).
-/
import SIS.Tree.WriterPtrsMerge
import SIS.Tree.MergeOpBoundProof

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem ptrs_mergeUp (Old : NodeId → Prop) (key : Key) (g fuel h : Nat) (merged : Bool) :
    KeepsPtrs Old (mergeUp key g fuel h merged) := by
  induction fuel generalizing h merged with
  | zero => exact ptrs_throw Old _
  | succ fuel ih =>
    intro c w hv hw
    unfold mergeUp
    repeat' first
      | wpSimplify
      | ptCore
      | ptUse (ptrs_descendToHeight _ _ _ _)
      | ptUse (ptrs_merge _ _ _)
      | ptUse (ih _ _)
      | wpSplit
      | split
      | contradiction

theorem ptrs_afterDelete (Old : NodeId → Prop) (key : Key) (g h : Nat) :
    KeepsPtrs Old (afterDelete key g h) := by
  intro c w hv hw
  unfold afterDelete
  repeat' first
    | wpSimplify
    | ptCore
    | ptUse (ptrs_mergeUp _ _ _ _ _ _)
    | ptUse (ptrs_collapseRoot _ _ _ _)
    | wpSplit
    | split
    | contradiction

/-! ## The upward unlink, a put, a transaction -/

theorem ptrs_climb (Old : NodeId → Prop) (depth : Nat) : KeepsPtrs Old (climb depth) := by
  induction depth with
  | zero =>
    intro c w hv hw
    unfold climb
    repeat' first | wpSimplify | ptCore | wpSplit | split | contradiction
  | succ depth ih =>
    intro c w hv hw
    unfold climb
    repeat' first
      | wpSimplify
      | ptCore
      | ptUse (ptrs_canTakeBack _ _ _ _)
      | ptUse ih
      | wpSplit
      | split
      | contradiction

macro "ptFoldWith " b:term " using " extra:tactic : tactic => `(tactic| (
  (with_reducible refine ptrs_writerWP (ptrs_foldlM $b _ _ _ ?ptBody) _ _ _ ?ptView ?ptState ?ptPost)
  case ptBody =>
    intro b a c w hv hw
    repeat' first
      | wpSimplify
      | ptCore
      | ($extra:tactic)
      | wpSplit
      | split
      | contradiction
  case ptView => assumption
  case ptState => ptState
  intro _ _ _ _))

macro "ptForWith " b:term " using " extra:tactic : tactic => `(tactic| (
  (with_reducible refine ptrs_writerWP (ptrs_forIn $b _ _ _ ?ptBody) _ _ _ ?ptView ?ptState ?ptPost)
  case ptBody =>
    intro a b c w hv hw
    repeat' first
      | wpSimplify
      | ptCore
      | ($extra:tactic)
      | wpSplit
      | split
      | contradiction
  case ptView => assumption
  case ptState => ptState
  intro _ _ _ _))

set_option maxHeartbeats 4000000 in
theorem ptrs_deleteUpward (Old : NodeId → Prop) (leaf : NodeId) (depth cv : Nat) (key : Key) :
    KeepsPtrs Old (deleteUpward leaf depth cv key) := by
  intro c w hv hw
  unfold deleteUpward
  repeat' first
    | wpSimplify
    | ptCore
    | ptUse (ptrs_appendDeleteKlong _ _ _ _)
    | ptUse (ptrs_emptyKeyNext _ _ _)
    | ptUse (ptrs_afterDelete _ _ _ _)
    | ptFoldWith Old using fail
    | ptForWith Old using (first | ptUse (ptrs_takeBack _ _ _ _) | ptUse (ptrs_unlink _ _))
    | ptUse (ptrs_climb _ _)
    | ptUse (ptrs_mergeUp _ _ _ _ _ _)
    | ptUse (ptrs_collapseRoot _ _ _ _)
    | wpSplit
    | split
    | contradiction

theorem ptrs_setValue (Old : NodeId → Prop) (segRoot : NodeId) (cv : Nat) (key : Key)
    (value : Option Nat) : KeepsPtrs Old (setValue segRoot cv key value) := by
  intro c w hv hw
  unfold setValue
  repeat' first
    | wpSimplify
    | ptCore
    | ptAppend
    | ptUse (ptrs_deleteUpward _ _ _ _ _)
    | wpSplit
    | split
    | contradiction

theorem ptrs_setNode (Old : NodeId → Prop) (segRoot : NodeId) (cv : Nat) (create : Bool) :
    KeepsPtrs Old (setNode segRoot cv create) := by
  intro c w hv hw
  unfold setNode
  repeat' first
    | wpSimplify
    | ptCore
    | ptAppend
    | wpSplit
    | split
    | contradiction

theorem ptrs_putSegs (Old : NodeId → Prop) (key : Key) (value : Option Nat) (segs : List Nat)
    (segRoot : NodeId) : KeepsPtrs Old (putSegs key value segs segRoot) := by
  induction segs generalizing segRoot with
  | nil => exact ptrs_throw Old _
  | cons cv rest ih =>
    cases rest with
    | nil => exact ptrs_setValue Old _ _ _ _
    | cons cv2 rest =>
      intro c w hv hw
      unfold putSegs
      repeat' first
        | wpSimplify
        | ptCore
        | ptUse (ptrs_setNode _ _ _ _)
        | ptUse (ih _)
        | wpSplit
        | split
        | contradiction

theorem ptrs_putKv (Old : NodeId → Prop) (op : Op) : KeepsPtrs Old (putKv op) := by
  cases op <;> (intro c w hv hw; unfold putKv)
  all_goals
    repeat' first
      | wpSimplify
      | ptCore
      | ptUse (ptrs_putSegs _ _ _ _ _)
      | wpSplit
      | split
      | contradiction

theorem ptrs_ops (Old : NodeId → Prop) (ops : List Op) : KeepsPtrs Old (ops.mapM putKv) := by
  induction ops with
  | nil =>
    intro c w hv hw
    simpa only [List.mapM_nil, writerWP_pure] using ⟨hw, MadeKept.refl w⟩
  | cons op ops ih =>
    intro c w hv hw
    rw [List.mapM_cons, writerWP_bind]
    refine writerWP_mono (ptrs_putKv Old op c w hv hw) ?_
    rintro noop v ⟨hwv, hk⟩
    simp only [writerWP_bind, writerWP_pure]
    exact writerWP_mono (ih c v hv hwv) (fun _ u h => ⟨h.1, hk.trans h.2⟩)

/-- The view without the root names nodes of P only if the view does. -/
theorem ptrs_viewRootless (Old : NodeId → Prop) (v : View BVal) (hv : ViewPtrsOld Old v) :
    ViewPtrsOld Old (rootless v) := by
  refine ⟨?_, ?_⟩
  · intro x nd hx
    unfold rootless at hx
    split at hx
    · cases hx
    · exact hv.1 x nd hx
  · intro x nd hx
    unfold rootless at hx
    split at hx
    · cases hx
    · exact hv.2 x nd hx

/-- The first state of a transaction, from a super root of P. -/
theorem ptrs_start (Old : NodeId → Prop) (c : Ctx) (base : NodeId) (top : Top)
    (htop : Old top.id ∧ Old top.rootKey ∧ (∀ q ∈ top.skips, Old q.2)) :
    PtrsOK Old c { next := base, top := top } := by
  refine ⟨?_, ?_, Or.inl htop.2.1, htop.2.2, fun _ => htop.1, ?_, ?_⟩
  · intro q hq; cases hq
  · intro q hq; cases hq
  · intro h; cases h
  · intro q hq; cases hq

/-- A successful transaction of the writer keeps `PtrsOK`: every pointer of
its overlay, its space root, the node each made node replaces, and the super
root's skip pointers name nodes of P (`Old`) or nodes that the transaction
made; the super root is one of P unless the transaction made it at its own
time. Premises: P's view names nodes of P only (`ViewPtrsOld`), and so does
P's super root. -/
theorem execW_ptrsOK (Old : NodeId → Prop) (p : Params) (tx : Tx) (i : Time) (v : View BVal)
    (bs : List Bool) (w : W) (hv : ViewPtrsOld Old v)
    (htop : ∀ z top, lastTop v = some z → topOf p (rootless v) z = .ok top →
      Old top.id ∧ Old top.rootKey ∧ (∀ q ∈ top.skips, Old q.2))
    (he : execW p tx i v = .ok (bs, w)) :
    PtrsOK Old { p := p, i := i, view := rootless v } w := by
  unfold execW runOps runOpsFrom at he
  cases hz : lastTop v with
  | none => simp [hz] at he
  | some z =>
    simp only [hz] at he
    cases ht : topOf p (rootless v) z with
    | error e => simp [ht] at he
    | ok top =>
      simp only [ht] at he
      have hr := boundsOK_ok p _ bs w he
      exact (ptrs_ops Old tx.ops { p := p, i := i, view := rootless v }
        { next := tx.base, top := top } (ptrs_viewRootless Old v hv)
        (ptrs_start Old _ tx.base top (htop z top hz ht)) bs w hr).1

end SIS.Tree
