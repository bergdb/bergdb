import SIS.Tree.WriterKlongs

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

set_option maxHeartbeats 1200000 in
/-- Every route of a full-node replacement preserves physical histories,
provided the supplied last version has its one-time shape and the upward
callback preserves the same invariant. -/
theorem klongsWf_handleFullWith (up : NodeId → List (Nat × NodeId) → M Unit)
    (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) (last : KNode) (compact : Bool)
    (hlast : FlatKlongs last.ks) (hup : ∀ q more, KeepsKlongsWf (up q more)) :
    KeepsKlongsWf (handleFullWith up depth x ins last compact) := by
  intro c w hv hw
  unfold handleFullWith
  repeat' first
    | wpSimplify
    | kwCore
    | kwReplace
    | kwUse (hup _ _)
    | wpSplit
    | split
    | contradiction

macro "kwAdd" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (addKeys _ _) _ _ _)
  kwUse (klongsWf_addKeys _ _)))

macro "kwFullWith " hup:term : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (handleFullWith _ _ _ _ _ _) _ _ _)
  (with_unfolding_none refine writerWP_of_klongsWf (klongsWf_handleFullWith _ _ _ _ _ _ ?kwLast ?kwUp) _ _ _ ?kwView ?kwState ?kwPost)
  case kwLast => first | assumption | exact KNode.lastVersion_flat _ _
  case kwUp => exact $hup
  case kwView => assumption
  case kwState => assumption
  intro _ _ _))

theorem klongsWf_throw {α : Type} (e : String) : KeepsKlongsWf (throw e : M α) := by
  intro c w hv hw
  exact writerWP_throw _ _ _ _

set_option maxHeartbeats 1200000 in
/-- The complete upward insertion recursion, including old/new time splits,
all three space-split positions and dead compaction, keeps every cached
physical history well formed. There are no range or threshold hypotheses. -/
theorem klongsWf_appendKlongs (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) :
    KeepsKlongsWf (appendKlongs depth x ins) := by
  induction depth generalizing x ins with
  | zero =>
    intro c w hv hw
    rw [appendKlongs_step_dead]
    repeat' first
      | wpSimplify
      | kwCore
      | kwAdd
      | kwFullWith (fun _ _ => klongsWf_throw _)
      | wpSplit
      | split
      | contradiction
  | succ depth ih =>
    intro c w hv hw
    rw [appendKlongs_step_dead]
    repeat' first
      | wpSimplify
      | kwCore
      | kwAdd
      | kwFullWith (fun q more => ih q more)
      | wpSplit
      | split
      | contradiction

theorem klongsWf_handleFull (depth : Nat) (x : NodeId) (last : KNode) (compact : Bool)
    (hlast : FlatKlongs last.ks) : KeepsKlongsWf (handleFull depth x last compact) := by
  unfold handleFull
  refine klongsWf_handleFullWith _ _ _ _ _ _ hlast ?_
  intro q more
  cases depth with
  | zero => exact klongsWf_throw _
  | succ depth => exact klongsWf_appendKlongs depth q more

end SIS.Tree
