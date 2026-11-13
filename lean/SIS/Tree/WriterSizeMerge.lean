/-
The tree model (bergdb 024-12, TP5's writer part): a key node holds at most M
klongs, continued from SIS/Tree/WriterSizeOps.lean: the merges, the upward
unlink, a put, and a transaction (`execW_sizeOK`).
-/
import SIS.Tree.WriterSizeOps

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- `sibling`: the node read has at most M klongs. -/
theorem sized_sibling (q : NodeId) (pn : KNode) (i : Nat) (inner : Bool) (c : Ctx) (w : W)
    (hv : ViewSized c) (hw : CacheSized c w) :
    WriterWP (sibling q pn i inner) c w (fun r v => CacheSized c v ∧ SizedNode c.p r.2) := by
  unfold sibling
  repeat' first
    | wpSimplify
    | szCore
    | (refine ⟨?_, ?_⟩ <;> assumption)
    | wpSplit
    | split
    | contradiction

macro "szSib" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (sibling _ _ _ _) _ _ _)
  (refine writerWP_mono (sized_sibling _ _ _ _ _ _ ?szView ?szState) ?szPost)
  case szView => assumption
  case szState => assumption
  rintro ⟨_, _⟩ _ ⟨_, _⟩))

/-- The new nodes of a merge. -/
macro "szNewKlongs" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (newKey _ _ _ (newKlongs _ _)) _ _ _)
  (with_unfolding_none refine sized_newKey _ _ _ _ _ _ _ ?szState ?szInput ?szPost)
  case szState => assumption
  case szInput =>
    refine sized_newKlongs _ _ _ _ ?_
    first
      | ((refine mergeKlongs_first _ _ _ _ _ _ ?_ ?_ ?_ _) <;>
          first | szArith | (refine SizedNode.live _ _ (by assumption) ?_; szArith))
      | ((refine mergeKlongs_second _ _ _ _ _ _ ?_ ?_ _ _ (by assumption) _) <;>
          first | szArith | (refine SizedNode.live _ _ (by assumption) ?_; szArith))
  intro _ _ _))

set_option maxHeartbeats 1600000 in
theorem sized_merge (x : NodeId) (d : Nat) : KeepsSized (merge x d) := by
  intro c w hv hw
  obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6⟩ := hv.params
  unfold merge
  repeat' first
    | wpSimplify
    | simp only [List.forIn_cons, List.forIn_nil]
    | szNewKlongs
    | szSib
    | szCore
    | szUse (sized_unlink _)
    | szUse (sized_retarget _ _ _)
    | szUse (sized_mergeParent _ _ _ _ _ _ _ _)
    | wpSplit
    | split
    | contradiction

theorem sized_mergeUp (key : Key) (g fuel h : Nat) (merged : Bool) :
    KeepsSized (mergeUp key g fuel h merged) := by
  induction fuel generalizing h merged with
  | zero => exact sized_throw _
  | succ fuel ih =>
    intro c w hv hw
    unfold mergeUp
    repeat' first
      | wpSimplify
      | szCore
      | szUse (sized_descendToHeight _ _ _)
      | szUse (sized_merge _ _)
      | szUse (ih _ _)
      | wpSplit
      | split
      | contradiction

theorem sized_afterDelete (key : Key) (g h : Nat) : KeepsSized (afterDelete key g h) := by
  intro c w hv hw
  unfold afterDelete
  repeat' first
    | wpSimplify
    | szCore
    | szUse (sized_mergeUp _ _ _ _ _)
    | szUse (sized_collapseRoot _ _ _)
    | wpSplit
    | split
    | contradiction

/-! ## The upward unlink, a put, a transaction -/

theorem sized_climb (depth : Nat) : KeepsSized (climb depth) := by
  induction depth with
  | zero =>
    intro c w hv hw
    unfold climb
    repeat' first | wpSimplify | szCore | wpSplit | split | contradiction
  | succ depth ih =>
    intro c w hv hw
    unfold climb
    repeat' first
      | wpSimplify
      | szCore
      | szUse (sized_canTakeBack _ _ _)
      | szUse ih
      | wpSplit
      | split
      | contradiction

macro "szFoldWith " extra:tactic : tactic => `(tactic| (
  (with_reducible refine writerWP_of_sized (sized_foldlM _ _ _ ?szBody) _ _ _ ?szView ?szState ?szPost)
  case szBody =>
    intro b a c w hv hw
    repeat' first
      | wpSimplify
      | szCore
      | ($extra:tactic)
      | wpSplit
      | split
      | contradiction
  case szView => assumption
  case szState => assumption
  intro _ _ _))

macro "szForWith " extra:tactic : tactic => `(tactic| (
  (with_reducible refine writerWP_of_sized (sized_forIn _ _ _ ?szBody) _ _ _ ?szView ?szState ?szPost)
  case szBody =>
    intro a b c w hv hw
    repeat' first
      | wpSimplify
      | szCore
      | ($extra:tactic)
      | wpSplit
      | split
      | contradiction
  case szView => assumption
  case szState => assumption
  intro _ _ _))

set_option maxHeartbeats 1600000 in
theorem sized_deleteUpward (leaf : NodeId) (depth cv : Nat) (key : Key) :
    KeepsSized (deleteUpward leaf depth cv key) := by
  intro c w hv hw
  unfold deleteUpward
  repeat' first
    | wpSimplify
    | szCore
    | szUse (sized_appendDeleteKlong _ _ _)
    | szUse (sized_emptyKeyNext _ _)
    | szUse (sized_afterDelete _ _ _)
    | szFoldWith fail
    | szForWith (first | szUse (sized_takeBack _ _ _) | szUse (sized_unlink _))
    | szUse (sized_climb _)
    | szUse (sized_mergeUp _ _ _ _ _)
    | szUse (sized_collapseRoot _ _ _)
    | wpSplit
    | split
    | contradiction

theorem sized_setValue (segRoot : NodeId) (cv : Nat) (key : Key) (value : Option Nat) :
    KeepsSized (setValue segRoot cv key value) := by
  intro c w hv hw
  unfold setValue
  repeat' first
    | wpSimplify
    | szWrite
    | szCore
    | szAppend
    | szUse (sized_deleteUpward _ _ _ _)
    | wpSplit
    | split
    | contradiction

theorem sized_setNode (segRoot : NodeId) (cv : Nat) (create : Bool) :
    KeepsSized (setNode segRoot cv create) := by
  intro c w hv hw
  unfold setNode
  repeat' first
    | wpSimplify
    | szWrite
    | szCore
    | szAppend
    | wpSplit
    | split
    | contradiction

theorem sized_putSegs (key : Key) (value : Option Nat) (segs : List Nat) (segRoot : NodeId) :
    KeepsSized (putSegs key value segs segRoot) := by
  induction segs generalizing segRoot with
  | nil => exact sized_throw _
  | cons cv rest ih =>
    cases rest with
    | nil => exact sized_setValue _ _ _ _
    | cons cv2 rest =>
      intro c w hv hw
      unfold putSegs
      repeat' first
        | wpSimplify
        | szCore
        | szUse (sized_setNode _ _ _)
        | szUse (ih _)
        | wpSplit
        | split
        | contradiction

theorem sized_putKv (op : Op) : KeepsSized (putKv op) := by
  cases op <;> (intro c w hv hw; unfold putKv)
  all_goals
    repeat' first
      | wpSimplify
      | szCore
      | szUse (sized_putSegs _ _ _ _)
      | wpSplit
      | split
      | contradiction

theorem sized_ops (ops : List Op) : KeepsSized (ops.mapM putKv) := by
  induction ops with
  | nil => intro c w hv hw; simpa only [List.mapM_nil, writerWP_pure] using hw
  | cons op ops ih =>
    intro c w hv hw
    rw [List.mapM_cons, writerWP_bind]
    refine writerWP_mono (sized_putKv op c w hv hw) ?_
    intro noop v hh
    have hi := ih c v hv hh
    simpa only [writerWP_bind, writerWP_pure] using hi

/-- TP5's writer part: a successful transaction of the writer, with the
thresholds of TP28, leaves every key node of its overlay with at most M klongs
and a time klong first, if every key node of the view has at most M klongs. -/
theorem execW_sizeOK (p : Params) (tx : Tx) (i : Time) (v : View BVal) (bs : List Bool) (w : W)
    (hp : MergeParamsOK p) (hv : ViewSizeOK p v) (he : execW p tx i v = .ok (bs, w)) :
    WriterSizeOK p w := by
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
      exact sized_ops tx.ops { p := p, i := i, view := rootless v }
        { next := tx.base, top := top } ⟨hp, viewSizeOK_rootless p v hv⟩
        (by intro q hq; cases hq) bs w hr

end SIS.Tree
