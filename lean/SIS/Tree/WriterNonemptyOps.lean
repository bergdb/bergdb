/-
The tree model (bergdb 024-12, TP7): every key node of the writer's overlay has
a klong, but the pending ones, continued from SIS/Tree/WriterNonempty.lean:
`appendKlongs`, the descents, the delete with LE-b, the take-back and root
collapse.
-/
import SIS.Tree.WriterNonempty

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

macro "neFullWith " hup:term : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (handleFullWith _ _ _ _ _ _) _ _ _)
  (with_unfolding_none refine writerWP_mono (nex_handleFullWith _ _ _ _ _ _ _ ?neE _ _ ?gdView ?gdState ?neState ?gdLast $hup) ?gdPost)
  case neState => assumption
  case gdView => assumption
  case gdState => assumption
  case gdLast => gdFlat
  rintro _ _ ⟨_, _⟩))

theorem nex_appendKlongs (B : NodeId) (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) :
    KeepsNE B (appendKlongs depth x ins) := by
  induction depth generalizing x ins with
  | zero =>
    intro E c w hv hw hn
    rw [appendKlongs_step_dead]
    repeat' first
      | wpSimplify
      | neNode
      | neFullWith (fun _ _ => nex_throw B _)
      | neUse (nex_addKeys _ _ _)
      | neDone
      | wpSplit
      | split
  | succ depth ih =>
    intro E c w hv hw hn
    rw [appendKlongs_step_dead]
    repeat' first
      | wpSimplify
      | neNode
      | neFullWith (fun q more => ih q more)
      | neUse (nex_addKeys _ _ _)
      | neDone
      | wpSplit
      | split

/-- A full node's replacement by a last version at the transaction's time. -/
theorem nex_handleFull (B : NodeId) (depth : Nat) (x : NodeId) (last : KNode) (compact : Bool)
    (E : List NodeId) (c : Ctx) (w : W) (hv : ViewGood B c) (hw : CacheGood B c w)
    (hn : NEx E w) (hlast : FlatAt c.i last.ks) :
    WriterWP (handleFull depth x last compact) c w (fun _ v => CacheGood B c v ∧ NEx E v) := by
  unfold handleFull
  refine nex_handleFullWith B _ depth x [] last compact E c w hv hw hn hlast ?_
  intro q more
  cases depth with
  | zero => exact nex_throw B _
  | succ d => exact nex_appendKlongs B _ _ _

theorem nex_descendLte (B : NodeId) (cv fuel : Nat) (x : NodeId) :
    KeepsNE B (descendLte cv fuel x) := by
  induction fuel generalizing x with
  | zero => exact nex_throw B _
  | succ fuel ih =>
    intro E c w hv hw hn
    unfold descendLte
    repeat' first
      | wpSimplify
      | neCore
      | neUse (ih _)
      | wpSplit
      | split
      | contradiction

theorem nex_foldlM (B : NodeId) {α β : Type} (xs : List α) (f : β → α → M β) (init : β)
    (hf : ∀ b a, KeepsNE B (f b a)) : KeepsNE B (xs.foldlM f init) := by
  induction xs generalizing init with
  | nil => intro E c w hv hw hn; simpa only [List.foldlM_nil, writerWP_pure] using ⟨hw, hn⟩
  | cons a xs ih =>
    intro E c w hv hw hn
    rw [List.foldlM_cons, writerWP_bind]
    exact writerWP_mono (hf init a E c w hv hw hn) (fun b v hh => ih b E c v hv hh.1 hh.2)

theorem nex_descendToSegmentRoot (B : NodeId) (key : Key) (segment : Nat) :
    KeepsNE B (descendToSegmentRoot key segment) := by
  intro E c w hv hw hn
  unfold descendToSegmentRoot
  wpSimplify
  neUse (nex_pathClear _)
  neUse (nex_findRoot _)
  refine nex_foldlM B _ _ _ ?_ E c _ hv (by assumption) (by assumption)
  intro node cv E c w hv hw hn
  repeat' first
    | wpSimplify
    | neCore
    | neUse (nex_descendLte _ _ _ _)
    | wpSplit
    | split
    | contradiction

/-! ## The delete -/

macro "neHandle" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (handleFull _ _ _ _) _ _ _)
  (with_unfolding_none refine writerWP_mono (nex_handleFull ?gdB _ _ _ _ ?neE _ _ ?gdView ?gdState ?neState ?gdLast) ?gdPost)
  case neState => assumption
  case gdView => assumption
  case gdState => assumption
  case gdLast => first
    | gdFlat
    | (refine flatAt_rename_after_head _ _ _ _ _ _ _ (by assumption) ?_; gdFlat)
  rintro _ _ ⟨_, _⟩))

macro "neAppend" : tactic => `(tactic| first
  | neHandle
  | neUse (nex_appendKlongs _ _ _ _)
  | neUse (nex_addKeys _ _ _)
  | neUse (nex_descendLte _ _ _ _))

set_option maxHeartbeats 1000000 in
theorem nex_appendDeleteKlong (B : NodeId) (x : NodeId) (depth cv : Nat) :
    KeepsNE B (appendDeleteKlong x depth cv) := by
  intro E c w hv hw hn
  have hpos := hv.pos
  unfold appendDeleteKlong
  repeat' first
    | wpSimplify
    | neCore
    | neAppend
    | wpSplit
    | split
    | contradiction

set_option maxHeartbeats 1400000 in
theorem nex_emptyKeyNext (B : NodeId) (x : NodeId) (depth : Nat) :
    KeepsNE B (emptyKeyNext x depth) := by
  intro E c w hv hw hn
  have hpos := hv.pos
  unfold emptyKeyNext
  repeat' first
    | wpSimplify
    | neCore
    | neAppend
    | wpSplit
    | split
    | contradiction

/-- `unlink x` stores x's klongs of P@(i-1): x keeps a klong if it has one in
P@(i-1), or it is pending. -/
theorem nex_unlink (B : NodeId) (x : NodeId) (E : List NodeId) (c : Ctx) (w : W)
    (hv : ViewGood B c) (hw : CacheGood B c w) (hn : NEx E w)
    (hx : baseKlongs c.view x ≠ [] ∨ x ∈ E) :
    WriterWP (unlink x) c w (fun _ v => CacheGood B c v ∧ NEx E v) := by
  unfold unlink
  repeat' first
    | wpSimplify
    | (refine nex_putNode_toPrev B E x _ c _ _ (by assumption) (by assumption) (by assumption) hx ?_
       intro _ _ _ _)
    | neCore
    | wpSplit
    | split
    | contradiction

/-- The premise of `unlink x` and `replaceRoot x`, from a read of x and the
writer's test that the transaction did not make it. -/
macro "neBase" : tactic => `(tactic| first
  | exact Or.inr (by assumption)
  | solve_by_elim)

macro "neUnlink" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (unlink _) _ _ _)
  (with_unfolding_none refine writerWP_mono (nex_unlink ?gdB _ ?neE _ _ ?gdView ?gdState ?neState ?neX) ?gdPost)
  case neState => assumption
  case gdView => assumption
  case gdState => assumption
  case neX => neBase
  rintro _ _ ⟨_, _⟩))

theorem nex_retarget (B : NodeId) (q src dst : NodeId) : KeepsNE B (retarget q src dst) := by
  intro E c w hv hw hn
  have hpos := hv.pos
  unfold retarget
  repeat' first
    | wpSimplify
    | neCore
    | wpSplit
    | split
    | contradiction

theorem nex_canTakeBack (B : NodeId) (x parent : NodeId) (cv : Nat) :
    KeepsNE B (canTakeBack x parent cv) := by
  intro E c w hv hw hn
  unfold canTakeBack
  repeat' first | wpSimplify | neCore | wpSplit | split | contradiction

theorem nex_takeBack (B : NodeId) (x parent : NodeId) (cv : Nat) :
    KeepsNE B (takeBack x parent cv) := by
  intro E c w hv hw hn
  unfold takeBack
  repeat' first
    | wpSimplify
    | neCore
    | neUse (nex_retarget _ _ _ _)
    | wpSplit
    | split
    | contradiction

/-- `takeBackRoot` of a node of the transaction. -/
theorem nex_takeBackRoot (B : NodeId) (x : NodeId) (depth only : Nat) (E : List NodeId)
    (c : Ctx) (w : W) (hv : ViewGood B c) (hw : CacheGood B c w) (hn : NEx E w) (hx : B ≤ x) :
    WriterWP (takeBackRoot x depth only) c w (fun _ v => CacheGood B c v ∧ NEx E v) := by
  have hpos := hv.pos
  unfold takeBackRoot
  repeat' first
    | wpSimplify
    | neCore
    | wpSplit
    | split
    | contradiction

/-- `replaceRoot x` unlinks x: x keeps a klong if it has one in P@(i-1), or
it is pending. -/
theorem nex_replaceRoot (B : NodeId) (x : NodeId) (depth only : Nat) (E : List NodeId)
    (c : Ctx) (w : W) (hv : ViewGood B c) (hw : CacheGood B c w) (hn : NEx E w)
    (hx : baseKlongs c.view x ≠ [] ∨ x ∈ E) :
    WriterWP (replaceRoot x depth only) c w (fun _ v => CacheGood B c v ∧ NEx E v) := by
  unfold replaceRoot
  repeat' first
    | wpSimplify
    | neCore
    | neAppend
    | neUnlink
    | wpSplit
    | split
    | contradiction

theorem nex_collapseRoot (B : NodeId) (key : Key) (segment fuel : Nat) :
    KeepsNE B (collapseRoot key segment fuel) := by
  induction fuel with
  | zero => exact nex_throw B _
  | succ fuel ih =>
    intro E c w hv hw hn
    have hpos := hv.pos
    unfold collapseRoot
    repeat' first
      | wpSimplify
      | neCore
      | neUse (nex_descendToSegmentRoot _ _ _)
      | ((with_unfolding_none guard_target = WriterWP (takeBackRoot _ _ _) _ _ _)
         refine writerWP_mono (nex_takeBackRoot B _ _ _ _ _ _ hv (by assumption) (by assumption) (Blank.ge B _ _ hv (blank_of_firstTime B _ _ _ hpos (by assumption) (by assumption)))) ?_
         rintro _ _ ⟨_, _⟩)
      | ((with_unfolding_none guard_target = WriterWP (replaceRoot _ _ _) _ _ _)
         refine writerWP_mono (nex_replaceRoot B _ _ _ _ _ _ hv (by assumption) (by assumption) (by neBase)) ?_
         rintro _ _ ⟨_, _⟩)
      | neUse ih
      | wpSplit
      | split
      | contradiction

end SIS.Tree
