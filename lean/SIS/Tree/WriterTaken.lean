/-
The tree model (bergdb 024-12, TP7): the nodes taken back are nodes of the
transaction (`TakenAbove`, SIS/Tree/OverlayBook.lean). This file: the writer's
functions that never take a node back keep the list of nodes taken back as it
is, so they keep `TakenAbove` with no premise. The functions that take nodes
back are in SIS/Tree/WriterTakenOps.lean.
-/
import SIS.Tree.OverlayBook
import SIS.Tree.WriterSteps
import SIS.Tree.MergeFrameDead

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- f keeps the nodes taken back at or above B. -/
def KeepsTaken (B : NodeId) {α : Type} (f : M α) : Prop :=
  ∀ c w, TakenAbove B w → WriterWP f c w (fun _ v => TakenAbove B v)

theorem writerWP_of_taken {α : Type} {B : NodeId} {f : M α} (hf : KeepsTaken B f)
    (c : Ctx) (w : W) (post : α → W → Prop) (hw : TakenAbove B w)
    (hp : ∀ r v, TakenAbove B v → post r v) : WriterWP f c w post :=
  writerWP_mono (hf c w hw) hp

/-- A step that changes no node taken back. -/
macro "tkPrim" : tactic => `(tactic| (
  intro c w hw
  repeat' first
    | simp only [writerWP_bind, writerWP_pure, writerWP_read, writerWP_get, writerWP_set,
        writerWP_modify]
    | exact writerWP_throw _ _ _ _
    | split
    | exact hw))

theorem taken_getNode (B : NodeId) (x : NodeId) : KeepsTaken B (getNode x) := by
  unfold getNode; tkPrim
theorem taken_putNode (B : NodeId) (x : NodeId) (n : KNode) : KeepsTaken B (putNode x n) := by
  unfold putNode; tkPrim
theorem taken_fresh (B : NodeId) : KeepsTaken B fresh := by
  unfold fresh; tkPrim
theorem taken_newKey (B : NodeId) (g h : Nat) (leaf : Bool) (ks : List Klong) :
    KeepsTaken B (newKey g h leaf ks) := by
  unfold newKey fresh; tkPrim
theorem taken_newValue (B : NodeId) (h : Nat) : KeepsTaken B (newValue h) := by
  unfold newValue fresh; tkPrim
theorem taken_note (B : NodeId) (s : String) : KeepsTaken B (note s) := by
  unfold note; tkPrim
theorem taken_setMadeFor (B : NodeId) (x : NodeId) (old : Option NodeId) :
    KeepsTaken B (setMadeFor x old) := by
  unfold setMadeFor; tkPrim
theorem taken_replacedBy (B : NodeId) (x : NodeId) : KeepsTaken B (replacedBy x) := by
  unfold replacedBy; tkPrim
theorem taken_pathClear (B : NodeId) : KeepsTaken B pathClear := by
  unfold pathClear; tkPrim
theorem taken_pathAdd (B : NodeId) (cv : Option Nat) (x : NodeId) :
    KeepsTaken B (pathAdd cv x) := by
  unfold pathAdd; tkPrim
theorem taken_pathSize (B : NodeId) : KeepsTaken B pathSize := by
  unfold pathSize; tkPrim
theorem taken_pathNode (B : NodeId) (d : Nat) : KeepsTaken B (pathNode d) := by
  unfold pathNode; tkPrim
theorem taken_klongAt (B : NodeId) (d : Nat) : KeepsTaken B (klongAt d) := by
  unfold klongAt; tkPrim
theorem taken_parentAt (B : NodeId) (d : Nat) : KeepsTaken B (parentAt d) := by
  unfold parentAt pathNode; tkPrim
theorem taken_newSuperRoot (B : NodeId) (x : NodeId) : KeepsTaken B (newSuperRoot x) := by
  unfold newSuperRoot note fresh; tkPrim
theorem taken_findRoot (B : NodeId) : KeepsTaken B findRoot := by
  unfold findRoot pathAdd; tkPrim

theorem taken_throw (B : NodeId) {α : Type} (e : String) : KeepsTaken B (throw e : M α) := by
  intro c w _
  exact writerWP_throw _ _ _ _

macro "tkUse " h:term : tactic => `(tactic| (
  (with_unfolding_none refine' writerWP_of_taken $h _ _ _ ?tkState ?tkPost)
  case tkState => assumption
  intro _ _ _))

macro "tkSimplify" : tactic => `(tactic|
  simp only [writerWP_bind, writerWP_pure, writerWP_read, writerWP_get,
    writerWP_set, writerWP_modify])

macro "tkCore" : tactic => `(tactic| first
  | exact writerWP_throw _ _ _ _
  | tkUse (taken_getNode _ _)
  | tkUse (taken_newKey _ _ _ _ _)
  | tkUse (taken_note _ _)
  | tkUse (taken_fresh _)
  | tkUse (taken_putNode _ _ _)
  | tkUse (taken_newValue _ _)
  | tkUse (taken_setMadeFor _ _ _)
  | tkUse (taken_replacedBy _ _)
  | tkUse (taken_pathClear _)
  | tkUse (taken_pathAdd _ _ _)
  | tkUse (taken_pathSize _)
  | tkUse (taken_pathNode _ _)
  | tkUse (taken_klongAt _ _)
  | tkUse (taken_parentAt _ _)
  | tkUse (taken_newSuperRoot _ _)
  | tkUse (taken_findRoot _)
  | assumption)

theorem taken_ghOf (B : NodeId) (x : NodeId) : KeepsTaken B (ghOf x) := by
  intro c w hw
  unfold ghOf
  repeat' first | tkSimplify | tkCore | split

theorem taken_addKeys (B : NodeId) (x : NodeId) (ins : List (Nat × NodeId)) :
    KeepsTaken B (addKeys x ins) := by
  intro c w hw
  unfold addKeys
  repeat' first | tkSimplify | tkCore | split

theorem taken_foldlM (B : NodeId) {α β : Type} (xs : List α) (f : β → α → M β) (init : β)
    (hf : ∀ b a, KeepsTaken B (f b a)) : KeepsTaken B (xs.foldlM f init) := by
  induction xs generalizing init with
  | nil => intro c w hw; simpa only [List.foldlM_nil, writerWP_pure] using hw
  | cons a xs ih =>
    intro c w hw
    rw [List.foldlM_cons, writerWP_bind]
    exact writerWP_mono (hf init a c w hw) (fun b v hv => ih b c v hv)

theorem taken_forIn (B : NodeId) {α β : Type} (xs : List α) (init : β)
    (f : α → β → M (ForInStep β)) (hf : ∀ a b, KeepsTaken B (f a b)) :
    KeepsTaken B (forIn xs init f) := by
  induction xs generalizing init with
  | nil => intro c w hw; simpa only [List.forIn_nil, writerWP_pure] using hw
  | cons a xs ih =>
    intro c w hw
    rw [List.forIn_cons, writerWP_bind]
    refine writerWP_mono (hf a init c w hw) ?_
    intro step v hv
    cases step with
    | done b => simpa only [writerWP_pure] using hv
    | yield b => exact ih b c v hv

macro "tkFoldWith " extra:tactic : tactic => `(tactic| (
  (with_unfolding_none refine' writerWP_of_taken (taken_foldlM _ _ _ _ ?tkBody) _ _ _ ?tkState ?tkPost)
  case tkBody =>
    intro b a c w hw
    repeat' first
      | tkSimplify
      | tkCore
      | ($extra:tactic)
      | wpSplit
      | split
      | contradiction
  case tkState => assumption
  intro _ _ _))

theorem taken_replaceOrAdd (B : NodeId) (last : KNode) (ins : List (Nat × NodeId)) :
    KeepsTaken B (replaceOrAdd last ins) := by
  intro c w hw
  unfold replaceOrAdd
  repeat' first
    | tkSimplify
    | tkCore
    | tkFoldWith fail
    | wpSplit
    | split
    | contradiction

theorem taken_handleFullWith (B : NodeId) (up : NodeId → List (Nat × NodeId) → M Unit)
    (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) (last : KNode) (compact : Bool)
    (hup : ∀ q more, KeepsTaken B (up q more)) :
    KeepsTaken B (handleFullWith up depth x ins last compact) := by
  intro c w hw
  unfold handleFullWith
  repeat' first
    | tkSimplify
    | tkCore
    | tkUse (taken_ghOf _ _)
    | tkUse (taken_replaceOrAdd _ _ _)
    | tkUse (hup _ _)
    | wpSplit
    | split
    | contradiction

theorem taken_appendKlongs (B : NodeId) (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) :
    KeepsTaken B (appendKlongs depth x ins) := by
  induction depth generalizing x ins with
  | zero =>
    intro c w hw
    rw [appendKlongs_step_dead]
    repeat' first
      | tkSimplify
      | tkCore
      | tkUse (taken_handleFullWith _ _ _ _ _ _ _ (fun _ _ => taken_throw _ _))
      | tkUse (taken_addKeys _ _ _)
      | wpSplit
      | split
      | contradiction
  | succ depth ih =>
    intro c w hw
    rw [appendKlongs_step_dead]
    repeat' first
      | tkSimplify
      | tkCore
      | tkUse (taken_handleFullWith _ _ _ _ _ _ _ (fun q more => ih q more))
      | tkUse (taken_addKeys _ _ _)
      | wpSplit
      | split
      | contradiction

theorem taken_handleFull (B : NodeId) (depth : Nat) (x : NodeId) (last : KNode) (compact : Bool) :
    KeepsTaken B (handleFull depth x last compact) := by
  unfold handleFull
  refine taken_handleFullWith B _ _ _ _ _ _ ?_
  intro q more
  cases depth with
  | zero => exact taken_throw _ _
  | succ d => exact taken_appendKlongs _ _ _ _

theorem taken_descendLte (B : NodeId) (cv fuel : Nat) (x : NodeId) :
    KeepsTaken B (descendLte cv fuel x) := by
  induction fuel generalizing x with
  | zero => exact taken_throw _ _
  | succ fuel ih =>
    intro c w hw
    unfold descendLte
    repeat' first
      | tkSimplify
      | tkCore
      | tkUse (ih _)
      | wpSplit
      | split
      | contradiction

macro "tkAppend" : tactic => `(tactic| first
  | tkUse (taken_handleFull _ _ _ _ _)
  | tkUse (taken_appendKlongs _ _ _ _)
  | tkUse (taken_addKeys _ _ _)
  | tkUse (taken_ghOf _ _)
  | tkUse (taken_descendLte _ _ _ _))

theorem taken_descendToSegmentRoot (B : NodeId) (key : Key) (segment : Nat) :
    KeepsTaken B (descendToSegmentRoot key segment) := by
  intro c w hw
  unfold descendToSegmentRoot
  repeat' first
    | tkSimplify
    | tkCore
    | tkFoldWith tkAppend
    | tkAppend
    | wpSplit
    | split
    | contradiction

theorem taken_appendDeleteKlong (B : NodeId) (x : NodeId) (depth cv : Nat) :
    KeepsTaken B (appendDeleteKlong x depth cv) := by
  intro c w hw
  unfold appendDeleteKlong
  repeat' first
    | tkSimplify
    | tkCore
    | tkAppend
    | wpSplit
    | split
    | contradiction

theorem taken_emptyKeyNext (B : NodeId) (x : NodeId) (depth : Nat) :
    KeepsTaken B (emptyKeyNext x depth) := by
  intro c w hw
  unfold emptyKeyNext
  repeat' first
    | tkSimplify
    | tkCore
    | tkAppend
    | wpSplit
    | split
    | contradiction

theorem taken_unlink (B : NodeId) (x : NodeId) : KeepsTaken B (unlink x) := by
  intro c w hw
  unfold unlink
  repeat' first | tkSimplify | tkCore | wpSplit | split | contradiction

theorem taken_retarget (B : NodeId) (q src dst : NodeId) : KeepsTaken B (retarget q src dst) := by
  intro c w hw
  unfold retarget
  repeat' first | tkSimplify | tkCore | wpSplit | split | contradiction

theorem taken_canTakeBack (B : NodeId) (x parent : NodeId) (cv : Nat) :
    KeepsTaken B (canTakeBack x parent cv) := by
  intro c w hw
  unfold canTakeBack
  repeat' first | tkSimplify | tkCore | wpSplit | split | contradiction

theorem taken_replaceRoot (B : NodeId) (x : NodeId) (depth only : Nat) :
    KeepsTaken B (replaceRoot x depth only) := by
  intro c w hw
  unfold replaceRoot
  repeat' first
    | tkSimplify
    | tkCore
    | tkAppend
    | tkUse (taken_unlink _ _)
    | wpSplit
    | split
    | contradiction

theorem taken_descendHeight (B : NodeId) (cv h fuel : Nat) (x : NodeId) :
    KeepsTaken B (descendHeight cv h fuel x) := by
  induction fuel generalizing x with
  | zero => exact taken_throw _ _
  | succ fuel ih =>
    intro c w hw
    unfold descendHeight
    repeat' first
      | tkSimplify
      | tkCore
      | tkUse (taken_ghOf _ _)
      | tkUse (ih _)
      | wpSplit
      | split
      | contradiction

theorem taken_descendToHeight (B : NodeId) (key : Key) (g h : Nat) :
    KeepsTaken B (descendToHeight key g h) := by
  intro c w hw
  unfold descendToHeight
  repeat' first
    | tkSimplify
    | tkCore
    | tkUse (taken_descendToSegmentRoot _ _ _)
    | tkUse (taken_descendHeight _ _ _ _ _)
    | wpSplit
    | split
    | contradiction

set_option maxHeartbeats 800000 in
theorem taken_mergeParent (B : NodeId) (q : NodeId) (depth il cL : Nat) (m1 : NodeId)
    (ir cR : Nat) (m2 : Option (NodeId × Nat)) :
    KeepsTaken B (mergeParent q depth il cL m1 ir cR m2) := by
  intro c w hw
  unfold mergeParent
  repeat' first
    | tkSimplify
    | tkCore
    | tkAppend
    | wpSplit
    | split
    | contradiction

theorem taken_sibling (B : NodeId) (q : NodeId) (pn : KNode) (i : Nat) (inner : Bool) :
    KeepsTaken B (sibling q pn i inner) := by
  intro c w hw
  unfold sibling
  repeat' first | tkSimplify | tkCore | wpSplit | split | contradiction

theorem taken_climb (B : NodeId) (depth : Nat) : KeepsTaken B (climb depth) := by
  induction depth with
  | zero =>
    intro c w hw
    unfold climb
    repeat' first | tkSimplify | tkCore | wpSplit | split | contradiction
  | succ depth ih =>
    intro c w hw
    unfold climb
    repeat' first
      | tkSimplify
      | tkCore
      | tkUse (taken_canTakeBack _ _ _ _)
      | tkUse ih
      | wpSplit
      | split
      | contradiction

theorem taken_setNode (B : NodeId) (segRoot : NodeId) (cv : Nat) (create : Bool) :
    KeepsTaken B (setNode segRoot cv create) := by
  intro c w hw
  unfold setNode
  repeat' first
    | tkSimplify
    | tkCore
    | tkAppend
    | wpSplit
    | split
    | contradiction

end SIS.Tree
