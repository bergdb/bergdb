import SIS.Tree.WriterKlongMerge

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem klongsWf_descendHeight (cv h fuel : Nat) (x : NodeId) :
    KeepsKlongsWf (descendHeight cv h fuel x) := by
  induction fuel generalizing x with
  | zero => exact klongsWf_throw _
  | succ fuel ih =>
    intro c w hv hw
    unfold descendHeight
    repeat' first
      | wpSimplify
      | kwCore
      | kwUse (ih _)
      | wpSplit
      | split
      | contradiction

theorem klongsWf_descendToHeight (key : Key) (g h : Nat) :
    KeepsKlongsWf (descendToHeight key g h) := by
  intro c w hv hw
  unfold descendToHeight
  repeat' first
    | wpSimplify
    | kwCore
    | kwUse (klongsWf_descendToSegmentRoot _ _)
    | kwUse (klongsWf_descendHeight _ _ _ _)
    | wpSplit
    | split
    | contradiction

theorem klongsWf_mergeUp (key : Key) (g fuel h : Nat) (merged : Bool) :
    KeepsKlongsWf (mergeUp key g fuel h merged) := by
  induction fuel generalizing h merged with
  | zero => exact klongsWf_throw _
  | succ fuel ih =>
    intro c w hv hw
    unfold mergeUp
    repeat' first
      | wpSimplify
      | kwCore
      | kwUse (klongsWf_descendToHeight _ _ _)
      | kwUse (klongsWf_merge _ _)
      | kwUse (ih _ _)
      | wpSplit
      | split
      | contradiction

theorem klongsWf_afterDelete (key : Key) (g h : Nat) : KeepsKlongsWf (afterDelete key g h) := by
  intro c w hv hw
  unfold afterDelete
  repeat' first
    | wpSimplify
    | kwCore
    | kwUse (klongsWf_mergeUp _ _ _ _ _)
    | kwUse (klongsWf_collapseRoot _ _ _)
    | wpSplit
    | split
    | contradiction

theorem klongsWf_climb (depth : Nat) : KeepsKlongsWf (climb depth) := by
  induction depth with
  | zero =>
    intro c w hv hw
    unfold climb
    repeat' first | wpSimplify | kwCore | wpSplit | split | contradiction
  | succ depth ih =>
    intro c w hv hw
    unfold climb
    repeat' first
      | wpSimplify
      | kwCore
      | kwUse (klongsWf_canTakeBack _ _ _)
      | kwUse ih
      | wpSplit
      | split
      | contradiction

macro "kwForWith " extra:tactic : tactic => `(tactic| (
  (with_reducible refine writerWP_of_klongsWf (klongsWf_forIn _ _ _ ?kwBody) _ _ _ ?kwView ?kwState ?kwPost)
  case kwBody =>
    intro a b c w hv hw
    repeat' first
      | wpSimplify
      | kwCore
      | kwAppend
      | ($extra:tactic)
      | wpSplit
      | split
      | contradiction
  case kwView => assumption
  case kwState => assumption
  intro _ _ _))

set_option maxHeartbeats 1600000 in
/-- The complete delete path preserves every cached physical history:
the upward unlink, LE-b, the merge loop and root cleanup are all included. -/
theorem klongsWf_deleteUpward (leaf : NodeId) (depth cv : Nat) (key : Key) :
    KeepsKlongsWf (deleteUpward leaf depth cv key) := by
  intro c w hv hw
  unfold deleteUpward
  repeat' first
    | wpSimplify
    | kwCore
    | kwAppend
    | kwFoldWith fail
    | kwForWith (first | kwUse (klongsWf_takeBack _ _ _) | kwUse (klongsWf_unlink _))
    | kwUse (klongsWf_climb _)
    | kwUse (klongsWf_appendDeleteKlong _ _ _)
    | kwUse (klongsWf_afterDelete _ _ _)
    | kwUse (klongsWf_mergeUp _ _ _ _ _)
    | kwUse (klongsWf_collapseRoot _ _ _)
    | kwUse (klongsWf_emptyKeyNext _ _)
    | wpSplit
    | split
    | contradiction

theorem klongsWf_setValue (segRoot : NodeId) (cv : Nat) (key : Key) (value : Option Nat) :
    KeepsKlongsWf (setValue segRoot cv key value) := by
  intro c w hv hw
  unfold setValue
  repeat' first
    | wpSimplify
    | kwCore
    | kwAppend
    | kwUse (klongsWf_descendLte _ _ _)
    | kwUse (klongsWf_deleteUpward _ _ _ _)
    | wpSplit
    | split
    | contradiction

theorem klongsWf_setNode (segRoot : NodeId) (cv : Nat) (create : Bool) :
    KeepsKlongsWf (setNode segRoot cv create) := by
  intro c w hv hw
  unfold setNode
  repeat' first
    | wpSimplify
    | kwCore
    | kwAppend
    | kwUse (klongsWf_descendLte _ _ _)
    | wpSplit
    | split
    | contradiction

theorem klongsWf_putSegs (key : Key) (value : Option Nat) (segs : List Nat) (segRoot : NodeId) :
    KeepsKlongsWf (putSegs key value segs segRoot) := by
  induction segs generalizing segRoot with
  | nil => exact klongsWf_throw _
  | cons cv rest ih =>
    cases rest with
    | nil => exact klongsWf_setValue _ _ _ _
    | cons cv2 rest =>
      intro c w hv hw
      unfold putSegs
      repeat' first
        | wpSimplify
        | kwCore
        | kwUse (klongsWf_setNode _ _ _)
        | kwUse (ih _)
        | wpSplit
        | split
        | contradiction

theorem klongsWf_putKv (op : Op) : KeepsKlongsWf (putKv op) := by
  cases op <;> (intro c w hv hw; unfold putKv)
  all_goals
    repeat' first
      | wpSimplify
      | kwCore
      | kwUse (klongsWf_putSegs _ _ _ _)
      | wpSplit
      | split
      | contradiction

theorem klongsWf_ops (ops : List Op) : KeepsKlongsWf (ops.mapM putKv) := by
  induction ops with
  | nil => intro c w hv hw; simpa only [List.mapM_nil, writerWP_pure] using hw
  | cons op ops ih =>
    intro c w hv hw
    rw [List.mapM_cons, writerWP_bind]
    refine writerWP_mono (klongsWf_putKv op c w hv hw) ?_
    intro noop v hh
    have hi := ih c v hv hh
    simpa only [writerWP_bind, writerWP_pure] using hi

theorem viewKlongsWf_rootless (p : Params) (v : View BVal) (hv : ViewKlongsWf p v) :
    ViewKlongsWf p (rootless v) := by
  intro x n hn hd hl
  unfold rootless at hn
  split at hn
  · cases hn
  · exact hv x n hn hd hl

/-- Every successful writer transaction leaves all its cached key histories
well formed. The sole input premise is well-formed readable key histories;
sorting, key encoding, fresh ids and parameter validity are unnecessary for
this physical-history component of invariant preservation. -/
theorem execW_klongsWf (p : Params) (tx : Tx) (i : Time) (v : View BVal)
    (bs : List Bool) (w : W) (hv : ViewKlongsWf p v)
    (he : execW p tx i v = .ok (bs, w)) : WriterKlongsWf w := by
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
      exact klongsWf_ops tx.ops {p := p, i := i, view := rootless v}
        {next := tx.base, top := top} (viewKlongsWf_rootless p v hv)
        (by intro q hq; cases hq) bs w hr

end SIS.Tree
