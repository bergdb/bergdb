/-
A put takes nothing back (bergdb 024-22, step 4; 024-12's `hchk`): the writer's
functions that never take a node back keep any property of the list of nodes
taken back (`KeepsTakenP`, the frame of WriterTaken.lean for any property in
place of `TakenAbove`), and a put is made of them only (`takenP_putKv_put`), so
it leaves the list as it is (`putKv_put_taken`), with no premise on the state.
The fuel at a state between operations then needs the heights at that state
only, not at later ones (HeightsFill.lean).
-/
import SIS.Tree.OverlayBook
import SIS.Tree.WriterSteps
import SIS.Tree.MergeFrameDead

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- f keeps a property of the list of nodes taken back. -/
def KeepsTakenP (Pt : List NodeId → Prop) {α : Type} (f : M α) : Prop :=
  ∀ c w, Pt w.taken → WriterWP f c w (fun _ v => Pt v.taken)

theorem writerWP_of_takenP {α : Type} {Pt : List NodeId → Prop} {f : M α} (hf : KeepsTakenP Pt f)
    (c : Ctx) (w : W) (post : α → W → Prop) (hw : Pt w.taken)
    (hp : ∀ r v, Pt v.taken → post r v) : WriterWP f c w post :=
  writerWP_mono (hf c w hw) hp

/-- A step that changes no node taken back. -/
macro "tkPrimP" : tactic => `(tactic| (
  intro c w hw
  repeat' first
    | simp only [writerWP_bind, writerWP_pure, writerWP_read, writerWP_get, writerWP_set,
        writerWP_modify]
    | exact writerWP_throw _ _ _ _
    | split
    | exact hw))

theorem takenP_getNode (Pt : List NodeId → Prop) (x : NodeId) : KeepsTakenP Pt (getNode x) := by
  unfold getNode; tkPrimP
theorem takenP_putNode (Pt : List NodeId → Prop) (x : NodeId) (n : KNode) : KeepsTakenP Pt (putNode x n) := by
  unfold putNode; tkPrimP
theorem takenP_fresh (Pt : List NodeId → Prop) : KeepsTakenP Pt fresh := by
  unfold fresh; tkPrimP
theorem takenP_newKey (Pt : List NodeId → Prop) (g h : Nat) (leaf : Bool) (ks : List Klong) :
    KeepsTakenP Pt (newKey g h leaf ks) := by
  unfold newKey fresh; tkPrimP
theorem takenP_newValue (Pt : List NodeId → Prop) (h : Nat) : KeepsTakenP Pt (newValue h) := by
  unfold newValue fresh; tkPrimP
theorem takenP_note (Pt : List NodeId → Prop) (s : String) : KeepsTakenP Pt (note s) := by
  unfold note; tkPrimP
theorem takenP_setMadeFor (Pt : List NodeId → Prop) (x : NodeId) (old : Option NodeId) :
    KeepsTakenP Pt (setMadeFor x old) := by
  unfold setMadeFor; tkPrimP
theorem takenP_replacedBy (Pt : List NodeId → Prop) (x : NodeId) : KeepsTakenP Pt (replacedBy x) := by
  unfold replacedBy; tkPrimP
theorem takenP_pathClear (Pt : List NodeId → Prop) : KeepsTakenP Pt pathClear := by
  unfold pathClear; tkPrimP
theorem takenP_pathAdd (Pt : List NodeId → Prop) (cv : Option Nat) (x : NodeId) :
    KeepsTakenP Pt (pathAdd cv x) := by
  unfold pathAdd; tkPrimP
theorem takenP_pathSize (Pt : List NodeId → Prop) : KeepsTakenP Pt pathSize := by
  unfold pathSize; tkPrimP
theorem takenP_pathNode (Pt : List NodeId → Prop) (d : Nat) : KeepsTakenP Pt (pathNode d) := by
  unfold pathNode; tkPrimP
theorem takenP_klongAt (Pt : List NodeId → Prop) (d : Nat) : KeepsTakenP Pt (klongAt d) := by
  unfold klongAt; tkPrimP
theorem takenP_parentAt (Pt : List NodeId → Prop) (d : Nat) : KeepsTakenP Pt (parentAt d) := by
  unfold parentAt pathNode; tkPrimP
theorem takenP_newSuperRoot (Pt : List NodeId → Prop) (x : NodeId) : KeepsTakenP Pt (newSuperRoot x) := by
  unfold newSuperRoot note fresh; tkPrimP
theorem takenP_findRoot (Pt : List NodeId → Prop) : KeepsTakenP Pt findRoot := by
  unfold findRoot pathAdd; tkPrimP

theorem takenP_throw (Pt : List NodeId → Prop) {α : Type} (e : String) : KeepsTakenP Pt (throw e : M α) := by
  intro c w _
  exact writerWP_throw _ _ _ _

macro "tkUseP " h:term : tactic => `(tactic| (
  (with_unfolding_none refine' writerWP_of_takenP $h _ _ _ ?tkState ?tkPost)
  case tkState => assumption
  intro _ _ _))

macro "tkSimplifyP" : tactic => `(tactic|
  simp only [writerWP_bind, writerWP_pure, writerWP_read, writerWP_get,
    writerWP_set, writerWP_modify])

macro "tkCoreP" : tactic => `(tactic| first
  | exact writerWP_throw _ _ _ _
  | tkUseP (takenP_getNode _ _)
  | tkUseP (takenP_newKey _ _ _ _ _)
  | tkUseP (takenP_note _ _)
  | tkUseP (takenP_fresh _)
  | tkUseP (takenP_putNode _ _ _)
  | tkUseP (takenP_newValue _ _)
  | tkUseP (takenP_setMadeFor _ _ _)
  | tkUseP (takenP_replacedBy _ _)
  | tkUseP (takenP_pathClear _)
  | tkUseP (takenP_pathAdd _ _ _)
  | tkUseP (takenP_pathSize _)
  | tkUseP (takenP_pathNode _ _)
  | tkUseP (takenP_klongAt _ _)
  | tkUseP (takenP_parentAt _ _)
  | tkUseP (takenP_newSuperRoot _ _)
  | tkUseP (takenP_findRoot _)
  | assumption)

theorem takenP_ghOf (Pt : List NodeId → Prop) (x : NodeId) : KeepsTakenP Pt (ghOf x) := by
  intro c w hw
  unfold ghOf
  repeat' first | tkSimplifyP | tkCoreP | split

theorem takenP_addKeys (Pt : List NodeId → Prop) (x : NodeId) (ins : List (Nat × NodeId)) :
    KeepsTakenP Pt (addKeys x ins) := by
  intro c w hw
  unfold addKeys
  repeat' first | tkSimplifyP | tkCoreP | split

theorem takenP_foldlM (Pt : List NodeId → Prop) {α β : Type} (xs : List α) (f : β → α → M β) (init : β)
    (hf : ∀ b a, KeepsTakenP Pt (f b a)) : KeepsTakenP Pt (xs.foldlM f init) := by
  induction xs generalizing init with
  | nil => intro c w hw; simpa only [List.foldlM_nil, writerWP_pure] using hw
  | cons a xs ih =>
    intro c w hw
    rw [List.foldlM_cons, writerWP_bind]
    exact writerWP_mono (hf init a c w hw) (fun b v hv => ih b c v hv)

macro "tkFoldWithP " extra:tactic : tactic => `(tactic| (
  (with_unfolding_none refine' writerWP_of_takenP (takenP_foldlM _ _ _ _ ?tkBody) _ _ _ ?tkState ?tkPost)
  case tkBody =>
    intro b a c w hw
    repeat' first
      | tkSimplifyP
      | tkCoreP
      | ($extra:tactic)
      | wpSplit
      | split
      | contradiction
  case tkState => assumption
  intro _ _ _))

theorem takenP_replaceOrAdd (Pt : List NodeId → Prop) (last : KNode) (ins : List (Nat × NodeId)) :
    KeepsTakenP Pt (replaceOrAdd last ins) := by
  intro c w hw
  unfold replaceOrAdd
  repeat' first
    | tkSimplifyP
    | tkCoreP
    | tkFoldWithP fail
    | wpSplit
    | split
    | contradiction

theorem takenP_handleFullWith (Pt : List NodeId → Prop) (up : NodeId → List (Nat × NodeId) → M Unit)
    (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) (last : KNode) (compact : Bool)
    (hup : ∀ q more, KeepsTakenP Pt (up q more)) :
    KeepsTakenP Pt (handleFullWith up depth x ins last compact) := by
  intro c w hw
  unfold handleFullWith
  repeat' first
    | tkSimplifyP
    | tkCoreP
    | tkUseP (takenP_ghOf _ _)
    | tkUseP (takenP_replaceOrAdd _ _ _)
    | tkUseP (hup _ _)
    | wpSplit
    | split
    | contradiction

theorem takenP_appendKlongs (Pt : List NodeId → Prop) (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) :
    KeepsTakenP Pt (appendKlongs depth x ins) := by
  induction depth generalizing x ins with
  | zero =>
    intro c w hw
    rw [appendKlongs_step_dead]
    repeat' first
      | tkSimplifyP
      | tkCoreP
      | tkUseP (takenP_handleFullWith _ _ _ _ _ _ _ (fun _ _ => takenP_throw _ _))
      | tkUseP (takenP_addKeys _ _ _)
      | wpSplit
      | split
      | contradiction
  | succ depth ih =>
    intro c w hw
    rw [appendKlongs_step_dead]
    repeat' first
      | tkSimplifyP
      | tkCoreP
      | tkUseP (takenP_handleFullWith _ _ _ _ _ _ _ (fun q more => ih q more))
      | tkUseP (takenP_addKeys _ _ _)
      | wpSplit
      | split
      | contradiction

theorem takenP_handleFull (Pt : List NodeId → Prop) (depth : Nat) (x : NodeId) (last : KNode) (compact : Bool) :
    KeepsTakenP Pt (handleFull depth x last compact) := by
  unfold handleFull
  refine takenP_handleFullWith Pt _ _ _ _ _ _ ?_
  intro q more
  cases depth with
  | zero => exact takenP_throw _ _
  | succ d => exact takenP_appendKlongs _ _ _ _

theorem takenP_descendLte (Pt : List NodeId → Prop) (cv fuel : Nat) (x : NodeId) :
    KeepsTakenP Pt (descendLte cv fuel x) := by
  induction fuel generalizing x with
  | zero => exact takenP_throw _ _
  | succ fuel ih =>
    intro c w hw
    unfold descendLte
    repeat' first
      | tkSimplifyP
      | tkCoreP
      | tkUseP (ih _)
      | wpSplit
      | split
      | contradiction

macro "tkAppendP" : tactic => `(tactic| first
  | tkUseP (takenP_handleFull _ _ _ _ _)
  | tkUseP (takenP_appendKlongs _ _ _ _)
  | tkUseP (takenP_addKeys _ _ _)
  | tkUseP (takenP_ghOf _ _)
  | tkUseP (takenP_descendLte _ _ _ _))

theorem takenP_descendToSegmentRoot (Pt : List NodeId → Prop) (key : Key) (segment : Nat) :
    KeepsTakenP Pt (descendToSegmentRoot key segment) := by
  intro c w hw
  unfold descendToSegmentRoot
  repeat' first
    | tkSimplifyP
    | tkCoreP
    | tkFoldWithP tkAppendP
    | tkAppendP
    | wpSplit
    | split
    | contradiction

theorem takenP_appendDeleteKlong (Pt : List NodeId → Prop) (x : NodeId) (depth cv : Nat) :
    KeepsTakenP Pt (appendDeleteKlong x depth cv) := by
  intro c w hw
  unfold appendDeleteKlong
  repeat' first
    | tkSimplifyP
    | tkCoreP
    | tkAppendP
    | wpSplit
    | split
    | contradiction

theorem takenP_emptyKeyNext (Pt : List NodeId → Prop) (x : NodeId) (depth : Nat) :
    KeepsTakenP Pt (emptyKeyNext x depth) := by
  intro c w hw
  unfold emptyKeyNext
  repeat' first
    | tkSimplifyP
    | tkCoreP
    | tkAppendP
    | wpSplit
    | split
    | contradiction

theorem takenP_unlink (Pt : List NodeId → Prop) (x : NodeId) : KeepsTakenP Pt (unlink x) := by
  intro c w hw
  unfold unlink
  repeat' first | tkSimplifyP | tkCoreP | wpSplit | split | contradiction

theorem takenP_retarget (Pt : List NodeId → Prop) (q src dst : NodeId) : KeepsTakenP Pt (retarget q src dst) := by
  intro c w hw
  unfold retarget
  repeat' first | tkSimplifyP | tkCoreP | wpSplit | split | contradiction

theorem takenP_canTakeBack (Pt : List NodeId → Prop) (x parent : NodeId) (cv : Nat) :
    KeepsTakenP Pt (canTakeBack x parent cv) := by
  intro c w hw
  unfold canTakeBack
  repeat' first | tkSimplifyP | tkCoreP | wpSplit | split | contradiction

theorem takenP_replaceRoot (Pt : List NodeId → Prop) (x : NodeId) (depth only : Nat) :
    KeepsTakenP Pt (replaceRoot x depth only) := by
  intro c w hw
  unfold replaceRoot
  repeat' first
    | tkSimplifyP
    | tkCoreP
    | tkAppendP
    | tkUseP (takenP_unlink _ _)
    | wpSplit
    | split
    | contradiction

theorem takenP_descendHeight (Pt : List NodeId → Prop) (cv h fuel : Nat) (x : NodeId) :
    KeepsTakenP Pt (descendHeight cv h fuel x) := by
  induction fuel generalizing x with
  | zero => exact takenP_throw _ _
  | succ fuel ih =>
    intro c w hw
    unfold descendHeight
    repeat' first
      | tkSimplifyP
      | tkCoreP
      | tkUseP (takenP_ghOf _ _)
      | tkUseP (ih _)
      | wpSplit
      | split
      | contradiction

theorem takenP_descendToHeight (Pt : List NodeId → Prop) (key : Key) (g h : Nat) :
    KeepsTakenP Pt (descendToHeight key g h) := by
  intro c w hw
  unfold descendToHeight
  repeat' first
    | tkSimplifyP
    | tkCoreP
    | tkUseP (takenP_descendToSegmentRoot _ _ _)
    | tkUseP (takenP_descendHeight _ _ _ _ _)
    | wpSplit
    | split
    | contradiction

set_option maxHeartbeats 800000 in
theorem takenP_mergeParent (Pt : List NodeId → Prop) (q : NodeId) (depth il cL : Nat) (m1 : NodeId)
    (ir cR : Nat) (m2 : Option (NodeId × Nat)) :
    KeepsTakenP Pt (mergeParent q depth il cL m1 ir cR m2) := by
  intro c w hw
  unfold mergeParent
  repeat' first
    | tkSimplifyP
    | tkCoreP
    | tkAppendP
    | wpSplit
    | split
    | contradiction

theorem takenP_sibling (Pt : List NodeId → Prop) (q : NodeId) (pn : KNode) (i : Nat) (inner : Bool) :
    KeepsTakenP Pt (sibling q pn i inner) := by
  intro c w hw
  unfold sibling
  repeat' first | tkSimplifyP | tkCoreP | wpSplit | split | contradiction

theorem takenP_climb (Pt : List NodeId → Prop) (depth : Nat) : KeepsTakenP Pt (climb depth) := by
  induction depth with
  | zero =>
    intro c w hw
    unfold climb
    repeat' first | tkSimplifyP | tkCoreP | wpSplit | split | contradiction
  | succ depth ih =>
    intro c w hw
    unfold climb
    repeat' first
      | tkSimplifyP
      | tkCoreP
      | tkUseP (takenP_canTakeBack _ _ _ _)
      | tkUseP ih
      | wpSplit
      | split
      | contradiction

theorem takenP_setNode (Pt : List NodeId → Prop) (segRoot : NodeId) (cv : Nat) (create : Bool) :
    KeepsTakenP Pt (setNode segRoot cv create) := by
  intro c w hw
  unfold setNode
  repeat' first
    | tkSimplifyP
    | tkCoreP
    | tkAppendP
    | wpSplit
    | split
    | contradiction

theorem takenP_setValue_put (Pt : List NodeId → Prop) (segRoot : NodeId) (cv : Nat) (key : Key)
    (h : Nat) : KeepsTakenP Pt (setValue segRoot cv key (some h)) := by
  intro c w hw
  unfold setValue
  repeat' first
    | tkSimplifyP
    | tkCoreP
    | tkAppendP
    | wpSplit
    | split
    | contradiction

theorem takenP_putSegs_put (Pt : List NodeId → Prop) (key : Key) (h : Nat) :
    ∀ (segs : List Nat) (segRoot : NodeId), KeepsTakenP Pt (putSegs key (some h) segs segRoot) := by
  intro segs
  induction segs with
  | nil => intro segRoot; unfold putSegs; exact takenP_throw _ _
  | cons cv rest ih =>
    intro segRoot
    cases rest with
    | nil => unfold putSegs; exact takenP_setValue_put Pt segRoot cv key h
    | cons cv2 rest2 =>
      intro c w hw
      unfold putSegs
      repeat' first
        | tkSimplifyP
        | tkCoreP
        | tkUseP (takenP_setNode _ _ _ _)
        | tkUseP (ih _)
        | wpSplit
        | split
        | contradiction

theorem takenP_putKv_put (Pt : List NodeId → Prop) (key : Key) (h : Nat) :
    KeepsTakenP Pt (putKv (.put key h)) := by
  intro c w hw
  unfold putKv
  repeat' first
    | tkSimplifyP
    | tkCoreP
    | tkUseP (takenP_putSegs_put _ _ _ _ _)
    | wpSplit
    | split
    | contradiction

/-- A put takes nothing back: the list of nodes taken back is as before. -/
theorem putKv_put_taken (key : Key) (h : Nat) (c : Ctx) (w : W) (a : Bool) (v : W)
    (he : putKv (.put key h) c w = .ok (a, v)) : v.taken = w.taken :=
  takenP_putKv_put (fun l => l = w.taken) key h c w rfl a v he

end SIS.Tree
