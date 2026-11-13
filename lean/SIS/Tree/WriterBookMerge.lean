/-
The tree model (bergdb 024-12, TP7): the writer keeps its books (`Book`),
continued from SIS/Tree/WriterBookOps.lean: a merge, the merges after a delete,
the upward unlink, a put, and a transaction (`execW_book`).
-/
import SIS.Tree.WriterBookOps

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

set_option maxHeartbeats 4000000 in
theorem book_merge (B : NodeId) (x : NodeId) (d : Nat) : KeepsBook B (merge x d) := by
  intro c w hv hb
  unfold merge
  repeat' first
    | bkMergeLoop
    | wpSimplify
    | bkCore
    | bkUse (book_unlink _ _)
    | bkUse (book_retarget _ _ _ _)
    | bkSibling
    | bkUse (book_mergeParent _ _ _ _ _ _ _ _ _)
    | wpSplit
    | split
    | contradiction

theorem book_mergeUp (B : NodeId) (key : Key) (g fuel h : Nat) (merged : Bool) :
    KeepsBook B (mergeUp key g fuel h merged) := by
  induction fuel generalizing h merged with
  | zero => exact book_throw B _
  | succ fuel ih =>
    intro c w hv hb
    unfold mergeUp
    repeat' first
      | wpSimplify
      | bkCore
      | bkUse (book_descendToHeight _ _ _ _)
      | bkUse (book_merge _ _ _)
      | bkUse (ih _ _)
      | wpSplit
      | split
      | contradiction

theorem book_afterDelete (B : NodeId) (key : Key) (g h : Nat) :
    KeepsBook B (afterDelete key g h) := by
  intro c w hv hb
  unfold afterDelete
  repeat' first
    | wpSimplify
    | bkCore
    | bkUse (book_mergeUp _ _ _ _ _ _)
    | bkUse (book_collapseRoot _ _ _ _)
    | wpSplit
    | split
    | contradiction

/-! ## The upward unlink, a put, a transaction -/

theorem book_climb (B : NodeId) (depth : Nat) : KeepsBook B (climb depth) := by
  induction depth with
  | zero =>
    intro c w hv hb
    unfold climb
    repeat' first | wpSimplify | bkCore | wpSplit | split | contradiction
  | succ depth ih =>
    intro c w hv hb
    unfold climb
    repeat' first
      | wpSimplify
      | bkCore
      | bkUse (book_canTakeBack _ _ _ _)
      | bkUse ih
      | wpSplit
      | split
      | contradiction

macro "bkFoldWith " b:term " using " extra:tactic : tactic => `(tactic| (
  (with_reducible refine book_writerWP (book_foldlM $b _ _ _ ?bkBody) _ _ _ ?bkView ?bkState ?bkPost)
  case bkBody =>
    intro b a c w hv hb
    repeat' first
      | wpSimplify
      | bkCore
      | ($extra:tactic)
      | wpSplit
      | split
      | contradiction
  case bkView => assumption
  case bkState => bkState
  intro _ _ _ _))

macro "bkForWith " b:term " using " extra:tactic : tactic => `(tactic| (
  (with_reducible refine book_writerWP (book_forIn $b _ _ _ ?bkBody) _ _ _ ?bkView ?bkState ?bkPost)
  case bkBody =>
    intro a b c w hv hb
    repeat' first
      | wpSimplify
      | bkCore
      | ($extra:tactic)
      | wpSplit
      | split
      | contradiction
  case bkView => assumption
  case bkState => bkState
  intro _ _ _ _))

set_option maxHeartbeats 1600000 in
theorem book_deleteUpward (B : NodeId) (leaf : NodeId) (depth cv : Nat) (key : Key) :
    KeepsBook B (deleteUpward leaf depth cv key) := by
  intro c w hv hb
  unfold deleteUpward
  repeat' first
    | wpSimplify
    | bkCore
    | bkUse (book_appendDeleteKlong _ _ _ _)
    | bkUse (book_emptyKeyNext _ _ _)
    | bkUse (book_afterDelete _ _ _ _)
    | bkFoldWith B using fail
    | bkForWith B using (first | bkTakeBack | bkUse (book_unlink _ _))
    | bkUse (book_climb _ _)
    | bkUse (book_mergeUp _ _ _ _ _ _)
    | bkUse (book_collapseRoot _ _ _ _)
    | wpSplit
    | split
    | contradiction

theorem book_setValue (B : NodeId) (segRoot : NodeId) (cv : Nat) (key : Key) (value : Option Nat) :
    KeepsBook B (setValue segRoot cv key value) := by
  intro c w hv hb
  unfold setValue
  repeat' first
    | wpSimplify
    | bkCore
    | bkAppend
    | bkUse (book_deleteUpward _ _ _ _ _)
    | wpSplit
    | split
    | contradiction

theorem book_setNode (B : NodeId) (segRoot : NodeId) (cv : Nat) (create : Bool) :
    KeepsBook B (setNode segRoot cv create) := by
  intro c w hv hb
  unfold setNode
  repeat' first
    | wpSimplify
    | bkCore
    | bkAppend
    | wpSplit
    | split
    | contradiction

theorem book_putSegs (B : NodeId) (key : Key) (value : Option Nat) (segs : List Nat)
    (segRoot : NodeId) : KeepsBook B (putSegs key value segs segRoot) := by
  induction segs generalizing segRoot with
  | nil => exact book_throw B _
  | cons cv rest ih =>
    cases rest with
    | nil => exact book_setValue B _ _ _ _
    | cons cv2 rest =>
      intro c w hv hb
      unfold putSegs
      repeat' first
        | wpSimplify
        | bkCore
        | bkUse (book_setNode _ _ _ _)
        | bkUse (ih _)
        | wpSplit
        | split
        | contradiction

theorem book_putKv (B : NodeId) (op : Op) : KeepsBook B (putKv op) := by
  cases op <;> (intro c w hv hb; unfold putKv)
  all_goals
    repeat' first
      | wpSimplify
      | bkCore
      | bkUse (book_putSegs _ _ _ _ _)
      | wpSplit
      | split
      | contradiction

theorem book_ops (B : NodeId) (ops : List Op) : KeepsBook B (ops.mapM putKv) := by
  induction ops with
  | nil => intro c w hv hb; simpa only [List.mapM_nil, writerWP_pure] using ⟨hb, Kept.refl w⟩
  | cons op ops ih =>
    intro c w hv hb
    rw [List.mapM_cons, writerWP_bind]
    refine writerWP_mono (book_putKv B op c w hv hb) ?_
    rintro noop v ⟨hbv, hk⟩
    simp only [writerWP_bind, writerWP_pure]
    exact writerWP_mono (ih c v hv hbv) (fun _ u h => ⟨h.1, hk.trans h.2⟩)

/-- The first state of a transaction has its books. -/
theorem book_start (B : NodeId) (c : Ctx) (top : Top) : Book B c { next := B, top := top } := by
  refine ⟨Nat.le_refl _, rfl, ?_, List.nodup_nil, ?_, ?_, ?_, ?_⟩
  · intro q hq; cases hq
  · intro x n g h hn; cases hn
  · intro x g h hq; cases hq
  · intro x hx; cases hx
  · intro ht; cases ht

/-- A successful transaction of the writer keeps its books: the overlay holds
a key node for each entry of `gh`, each id once, with the leaf flag of its
height; a node of the view has the segment and height of its level, a node of
the transaction is made with its level and noted if it is outside G and H; a
node taken back is in the overlay; the new top node is not. -/
theorem execW_book (p : Params) (tx : Tx) (i : Time) (v : View BVal) (bs : List Bool) (w : W)
    (hv : ViewIdsBelow tx.base v) (he : execW p tx i v = .ok (bs, w)) :
    Book tx.base { p := p, i := i, view := rootless v } w := by
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
      exact (book_ops tx.base tx.ops { p := p, i := i, view := rootless v }
        { next := tx.base, top := top } (viewIdsBelow_rootless tx.base v hv)
        (book_start _ _ top) bs w hr).1

end SIS.Tree
