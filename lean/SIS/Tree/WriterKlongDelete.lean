import SIS.Tree.WriterKlongSplits

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

syntax "kwFlat" : tactic
macro_rules
  | `(tactic| kwFlat) => `(tactic| first
  | assumption
  | exact KNode.lastVersionGivenDel_flat _ _ _
  | exact KNode.lastVersion_flat _ _
  | ((with_unfolding_none guard_target = FlatKlongs (.time _ :: .key _ _ :: _))
     apply flatKlongs_rename_first; kwFlat)
  | (refine flatKlongs_replaceKlong _ _ _ _ _ ?_ (by assumption); kwFlat)
  | ((with_unfolding_none guard_target = FlatKlongs (insertSorted _ _ _))
     apply flatKlongs_insertSorted; kwFlat))

theorem KNode.setAt_delete_wf_of_flag (n : KNode) (t : Time) (cv : Nat)
    (hw : klongsWf n.ks = true)
    (hflag : ((match n.ks.getLast? with | some (.del _) => true | _ => false) &&
      n.lastTime == some t) = true) :
    klongsWf (n.setAt (n.size - 1)
      (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))).ks = true := by
  cases hh : n.ks.getLast? with
  | none => simp [hh] at hflag
  | some k =>
    cases k with
    | time u => simp [hh] at hflag
    | key a y => simp [hh] at hflag
    | del old => exact n.setAt_delete_wf cv old hw hh

macro "kwHandle" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (handleFull _ _ _ _) _ _ _)
  (with_unfolding_none refine writerWP_of_klongsWf (klongsWf_handleFull _ _ _ _ ?kwLast) _ _ _ ?kwView ?kwState ?kwPost)
  case kwLast => kwFlat
  case kwView => assumption
  case kwState => assumption
  intro _ _ _))

macro "kwAppend" : tactic => `(tactic| first
  | kwHandle
  | kwAdd
  | ((with_unfolding_none guard_target = WriterWP (appendKlongs _ _ _) _ _ _)
     kwUse (klongsWf_appendKlongs _ _ _)))

macro "kwBitmapStore" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (putNode _ _) _ _ _)
  (with_unfolding_none refine writerWP_of_klongsWf (klongsWf_putNode _ _ ?kwInput) _ _ _ ?kwView ?kwState ?kwPost)
  case kwInput => first
    | (apply KNode.setAt_delete_wf_of_flag <;> assumption)
    | (apply KNode.add_delete_wf
       · assumption
       · intro he; simp_all)
  case kwView => assumption
  case kwState => assumption
  intro _ _ _))

set_option maxHeartbeats 1000000 in
/-- Both bitmap modes and every full/dead replacement route preserve all
cached physical histories. The writer's own noop test provides the strict
bitmap-growth premise. No current-transaction-node or room premise is needed. -/
theorem klongsWf_appendDeleteKlong (x : NodeId) (depth cv : Nat) :
    KeepsKlongsWf (appendDeleteKlong x depth cv) := by
  intro c w hv hw
  unfold appendDeleteKlong
  repeat' first
    | wpSimplify
    | kwBitmapStore
    | kwCore
    | kwAppend
    | wpSplit
    | split
    | contradiction

theorem klongsWf_unlink (x : NodeId) : KeepsKlongsWf (unlink x) := by
  intro c w hv hw
  unfold unlink
  repeat' first | wpSimplify | kwCore | wpSplit | split | contradiction

theorem klongsWf_retarget (q src dst : NodeId) : KeepsKlongsWf (retarget q src dst) := by
  intro c w hv hw
  unfold retarget
  repeat' first
    | wpSimplify
    | kwCore
    | ((with_unfolding_none guard_target = WriterWP (putNode _ _) _ _ _)
       refine writerWP_of_klongsWf (klongsWf_putNode _ _ ?kwInput) _ _ _ hv (by assumption) ?kwPost
       case kwInput =>
         change klongsWf (retargetKlongs _ _ _ _) = true
         rw [klongsWf_retargetKlongs]
         assumption
       intro _ _ _)
    | wpSplit
    | split
    | contradiction

theorem klongsWf_canTakeBack (x parent : NodeId) (cv : Nat) :
    KeepsKlongsWf (canTakeBack x parent cv) := by
  intro c w hv hw
  unfold canTakeBack
  repeat' first | wpSimplify | kwCore | wpSplit | split | contradiction

theorem klongsWf_takeBack (x parent : NodeId) (cv : Nat) :
    KeepsKlongsWf (takeBack x parent cv) := by
  intro c w hv hw
  unfold takeBack
  repeat' first
    | wpSimplify
    | kwCore
    | kwUse (klongsWf_retarget _ _ _)
    | wpSplit
    | split
    | contradiction

theorem klongsWf_takeBackRoot (x : NodeId) (depth only : Nat) :
    KeepsKlongsWf (takeBackRoot x depth only) := by
  intro c w hv hw
  unfold takeBackRoot
  repeat' first | wpSimplify | kwCore | wpSplit | split | contradiction

theorem klongsWf_replaceRoot (x : NodeId) (depth only : Nat) :
    KeepsKlongsWf (replaceRoot x depth only) := by
  intro c w hv hw
  unfold replaceRoot
  repeat' first
    | wpSimplify
    | kwCore
    | kwAppend
    | kwUse (klongsWf_unlink _)
    | wpSplit
    | split
    | contradiction

theorem klongsWf_descendLte (cv fuel : Nat) (x : NodeId) :
    KeepsKlongsWf (descendLte cv fuel x) := by
  induction fuel generalizing x with
  | zero => exact klongsWf_throw _
  | succ fuel ih =>
    intro c w hv hw
    unfold descendLte
    repeat' first
      | wpSimplify
      | kwCore
      | kwUse (ih _)
      | wpSplit
      | split
      | contradiction

theorem klongsWf_foldlM {α β : Type} (xs : List α) (f : β → α → M β) (init : β)
    (hf : ∀ b a, KeepsKlongsWf (f b a)) : KeepsKlongsWf (xs.foldlM f init) := by
  induction xs generalizing init with
  | nil => intro c w hv hw; simpa only [List.foldlM_nil, writerWP_pure] using hw
  | cons a xs ih =>
    intro c w hv hw
    rw [List.foldlM_cons, writerWP_bind]
    exact writerWP_mono (hf init a c w hv hw) (fun b v hh => ih b c v hv hh)

macro "kwFoldWith " extra:tactic : tactic => `(tactic| (
  (with_reducible refine writerWP_of_klongsWf (klongsWf_foldlM _ _ _ ?kwBody) _ _ _ ?kwView ?kwState ?kwPost)
  case kwBody =>
    intro b a c w hv hw
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

theorem klongsWf_descendToSegmentRoot (key : Key) (segment : Nat) :
    KeepsKlongsWf (descendToSegmentRoot key segment) := by
  intro c w hv hw
  unfold descendToSegmentRoot
  repeat' first
    | wpSimplify
    | kwCore
    | kwFoldWith (kwUse (klongsWf_descendLte _ _ _))
    | wpSplit
    | split
    | contradiction

theorem klongsWf_collapseRoot (key : Key) (segment fuel : Nat) :
    KeepsKlongsWf (collapseRoot key segment fuel) := by
  induction fuel with
  | zero => exact klongsWf_throw _
  | succ fuel ih =>
    intro c w hv hw
    unfold collapseRoot
    repeat' first
      | wpSimplify
      | kwCore
      | kwUse (klongsWf_descendToSegmentRoot _ _)
      | kwUse (klongsWf_takeBackRoot _ _ _)
      | kwUse (klongsWf_replaceRoot _ _ _)
      | kwUse ih
      | wpSplit
      | split
      | contradiction

theorem klongsWf_forIn {α β : Type} (xs : List α) (init : β)
    (f : α → β → M (ForInStep β)) (hf : ∀ a b, KeepsKlongsWf (f a b)) :
    KeepsKlongsWf (forIn xs init f) := by
  induction xs generalizing init with
  | nil => intro c w hv hw; simpa only [List.forIn_nil, writerWP_pure] using hw
  | cons a xs ih =>
    intro c w hv hw
    rw [List.forIn_cons, writerWP_bind]
    refine writerWP_mono (hf a init c w hv hw) ?_
    intro step v hh
    cases step with
    | done b => simpa only [writerWP_pure] using hh
    | yield b => exact ih b c v hv hh

end SIS.Tree
