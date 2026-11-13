import SIS.Tree.WriterEncoding

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem encoded_mergeUp (key : Key) (g fuel h : Nat) (merged : Bool) :
    KeepsEncoded (mergeUp key g fuel h merged) := by
  induction fuel generalizing h merged with
  | zero => exact encoded_throw _
  | succ fuel ih =>
    intro c w hv hw
    unfold mergeUp
    repeat' first
      | wpSimplify
      | encCore
      | encUse (encoded_descendToHeight _ _ _)
      | encUse (encoded_merge _ _)
      | encUse (ih _ _)
      | wpSplit
      | split
      | contradiction

theorem encoded_afterDelete (key : Key) (g h : Nat) : KeepsEncoded (afterDelete key g h) := by
  intro c w hv hw
  unfold afterDelete
  repeat' first
    | wpSimplify
    | encCore
    | encUse (encoded_mergeUp _ _ _ _ _)
    | encUse (encoded_collapseRoot _ _ _)
    | wpSplit
    | split
    | contradiction

theorem encoded_climb (depth : Nat) : KeepsEncoded (climb depth) := by
  induction depth with
  | zero =>
    intro c w hv hw
    unfold climb
    repeat' first | wpSimplify | encCore | wpSplit | split | contradiction
  | succ depth ih =>
    intro c w hv hw
    unfold climb
    repeat' first
      | wpSimplify
      | encCore
      | encUse (encoded_canTakeBack _ _ _)
      | encUse ih
      | wpSplit
      | split
      | contradiction

macro "encForWith " extra:tactic : tactic => `(tactic| (
  (with_reducible refine writerWP_of_encoded (encoded_forIn _ _ _ ?encBody) _ _ _ ?encView ?encState ?encPost)
  case encBody =>
    intro a b c w hv hw
    repeat' first
      | wpSimplify
      | encCore
      | encAppend
      | ($extra:tactic)
      | wpSplit
      | split
      | contradiction
  case encView => assumption
  case encState => encHeld
  intro _ _ _))

set_option maxHeartbeats 1600000 in
theorem encoded_deleteUpward (leaf : NodeId) (depth cv : Nat) (key : Key) :
    KeepsEncoded (deleteUpward leaf depth cv key) := by
  intro c w hv hw
  unfold deleteUpward
  repeat' first
    | wpSimplify
    | encCore
    | encAppend
    | encFoldWith fail
    | encForWith (first | encUse (encoded_takeBack _ _ _) | encUse (encoded_unlink _))
    | encUse (encoded_climb _)
    | encUse (encoded_appendDeleteKlong _ _ _)
    | encUse (encoded_afterDelete _ _ _)
    | encUse (encoded_mergeUp _ _ _ _ _)
    | encUse (encoded_collapseRoot _ _ _)
    | encUse (encoded_emptyKeyNext _ _)
    | wpSplit
    | split
    | contradiction

theorem encoded_setValue (segRoot : NodeId) (cv : Nat) (key : Key) (value : Option Nat)
    (hcv : CompareValueOK cv) : KeepsEncoded (setValue segRoot cv key value) := by
  intro c w hv hw
  unfold setValue
  repeat' first
    | wpSimplify
    | encCore
    | encAppend
    | encUse (encoded_descendLte _ _ _)
    | encUse (encoded_deleteUpward _ _ _ _)
    | wpSplit
    | split
    | contradiction

theorem encoded_setNode (segRoot : NodeId) (cv : Nat) (create : Bool)
    (hcv : CompareValueOK cv) : KeepsEncoded (setNode segRoot cv create) := by
  intro c w hv hw
  unfold setNode
  repeat' first
    | wpSimplify
    | encCore
    | encAppend
    | encUse (encoded_descendLte _ _ _)
    | wpSplit
    | split
    | contradiction

theorem encoded_putSegs (key : Key) (value : Option Nat) (segs : List Nat) (segRoot : NodeId)
    (hs : ∀ c ∈ segs, CompareValueOK c) : KeepsEncoded (putSegs key value segs segRoot) := by
  induction segs generalizing segRoot with
  | nil => exact encoded_throw _
  | cons cv rest ih =>
    have hcv := hs cv List.mem_cons_self
    have hrest : ∀ c ∈ rest, CompareValueOK c := fun c hc => hs c (List.mem_cons_of_mem cv hc)
    cases rest with
    | nil => exact encoded_setValue _ _ _ _ hcv
    | cons cv2 rest =>
      intro c w hv hw
      unfold putSegs
      repeat' first
        | wpSimplify
        | encCore
        | encUse (encoded_setNode _ _ _ hcv)
        | encUse (ih _ hrest)
        | wpSplit
        | split
        | contradiction

macro "encSegs" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (putSegs _ _ _ _) _ _ _)
  (with_reducible refine writerWP_of_encoded (encoded_putSegs _ _ _ _ ?encKeys) _ _ _ ?encView ?encState ?encPost)
  case encKeys => assumption
  case encView => assumption
  case encState => encHeld
  intro _ _ _))

theorem encoded_putKv (op : Op) (hs : ∀ c ∈ op.key, CompareValueOK c) : KeepsEncoded (putKv op) := by
  cases op with
  | put key value =>
    change (∀ cv ∈ key, CompareValueOK cv) at hs
    intro c w hv hw
    unfold putKv
    repeat' first
      | wpSimplify
      | encCore
      | encSegs
      | wpSplit
      | split
      | contradiction
  | del key =>
    change (∀ cv ∈ key, CompareValueOK cv) at hs
    intro c w hv hw
    unfold putKv
    repeat' first
      | wpSimplify
      | encCore
      | encSegs
      | wpSplit
      | split
      | contradiction

theorem encoded_ops (ops : List Op) (hs : ∀ op ∈ ops, ∀ c ∈ op.key, CompareValueOK c) :
    KeepsEncoded (ops.mapM putKv) := by
  induction ops with
  | nil => intro c w hv hw; simpa only [List.mapM_nil, writerWP_pure] using hw
  | cons op ops ih =>
    intro c w hv hw
    rw [List.mapM_cons, writerWP_bind]
    refine writerWP_mono (encoded_putKv op (hs op List.mem_cons_self) c w hv hw) ?_
    intro noop v hh
    have hi := ih (fun q hq => hs q (List.mem_cons_of_mem op hq)) c v hv hh
    simpa only [writerWP_bind, writerWP_pure] using hi

theorem viewEncoded_rootless (v : View BVal) (hv : ViewEncoded v) : ViewEncoded (rootless v) := by
  intro x n hn
  unfold rootless at hn
  split at hn
  · cases hn
  · exact hv x n hn

/-- Successful writers preserve the compare-value encoding, independently
of sorting, fresh ids, threshold choices and tree-shape invariants. -/
theorem execW_encoded (p : Params) (tx : Tx) (i : Time) (v : View BVal)
    (bs : List Bool) (w : W) (hv : ViewEncoded v) (hwf : tx.wf = true)
    (he : execW p tx i v = .ok (bs, w)) : WriterEncoded w := by
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
      have hs : ∀ op ∈ tx.ops, ∀ c ∈ op.key, CompareValueOK c := by
        intro op hop
        exact keyWf_pairs_encoded op.key (List.all_eq_true.mp hwf op hop)
      exact encoded_ops tx.ops hs {p := p, i := i, view := rootless v}
        {next := tx.base, top := top} (viewEncoded_rootless v hv)
        (by constructor <;> simp) bs w hr

end SIS.Tree
