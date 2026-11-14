/-
The tree model (bergdb 024-12, TP7): every key node of the writer's overlay has
a klong, but the pending ones, continued from SIS/Tree/WriterNonemptyOps.lean:
the merges, the upward unlink, `setValue`, and `setNode`, whose new segment
leaf stays pending for the next step of the put.
-/
import SIS.Tree.WriterNonemptyOps

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## The merges -/

theorem nex_descendHeight (B : NodeId) (cv h fuel : Nat) (x : NodeId) :
    KeepsNE B (descendHeight cv h fuel x) := by
  induction fuel generalizing x with
  | zero => exact nex_throw B _
  | succ fuel ih =>
    intro E c w hv hw hn
    unfold descendHeight
    repeat' first
      | wpSimplify
      | neCore
      | neUse (ih _)
      | wpSplit
      | split
      | contradiction

theorem nex_descendToHeight (B : NodeId) (key : Key) (g h : Nat) :
    KeepsNE B (descendToHeight key g h) := by
  intro E c w hv hw hn
  unfold descendToHeight
  repeat' first
    | wpSimplify
    | neCore
    | neUse (nex_descendToSegmentRoot _ _ _)
    | neUse (nex_descendHeight _ _ _ _ _)
    | wpSplit
    | split
    | contradiction

set_option maxHeartbeats 1600000 in
theorem nex_mergeParent (B : NodeId) (q : NodeId) (depth il cL : Nat) (m1 : NodeId) (ir cR : Nat)
    (m2 : Option (NodeId × Nat)) :
    KeepsNE B (mergeParent q depth il cL m1 ir cR m2) := by
  intro E c w hv hw hn
  have hpos := hv.pos
  unfold mergeParent
  repeat' first
    | wpSimplify
    | neCore
    | neAppend
    | wpSplit
    | split
    | contradiction

/-- The sibling read: `Good`, with a klong unless it is pending, and with
klongs of P@(i-1) unless the transaction made it or it is pending. -/
theorem nex_sibling (B : NodeId) (q : NodeId) (pn : KNode) (i : Nat) (inner : Bool)
    (E : List NodeId) (c : Ctx) (w : W) (hv : ViewGood B c) (hw : CacheGood B c w)
    (hn : NEx E w) :
    WriterWP (sibling q pn i inner) c w (fun r v => CacheGood B c v ∧ NEx E v ∧
      Good B c r.1 r.2 ∧ (r.2.ks = [] → r.1 ∈ E) ∧
      (¬ (r.2.firstTime == some c.i) = true → baseKlongs c.view r.1 ≠ [] ∨ r.1 ∈ E)) := by
  unfold sibling
  repeat' first
    | wpSimplify
    | neNode
    | exact writerWP_throw _ _ _ _
    | wpSplit
    | split
    | contradiction
    | exact ⟨by assumption, by assumption, by assumption, by assumption, by assumption⟩

macro "neSibling" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (sibling _ _ _ _) _ _ _)
  (refine writerWP_mono (nex_sibling ?gdB _ _ _ _ ?neE _ _ ?gdView ?gdState ?neState) ?gdPost)
  case gdView => assumption
  case gdState => assumption
  case neState => assumption
  rintro ⟨_, _⟩ _ ⟨_, _, _, _, _⟩))

set_option maxHeartbeats 1600000 in
theorem nex_merge (B : NodeId) (x : NodeId) (d : Nat) : KeepsNE B (merge x d) := by
  intro E c w hv hw hn
  have hpos := hv.pos
  unfold merge
  repeat' first
    | wpSimplify
    | simp only [List.forIn_cons, List.forIn_nil]
    | neCore
    | neUnlink
    | neUse (nex_retarget _ _ _ _)
    | neSibling
    | neUse (nex_mergeParent _ _ _ _ _ _ _ _ _)
    | wpSplit
    | split
    | contradiction

theorem nex_mergeUp (B : NodeId) (key : Key) (g fuel h : Nat) (merged : Bool) :
    KeepsNE B (mergeUp key g fuel h merged) := by
  induction fuel generalizing h merged with
  | zero => exact nex_throw B _
  | succ fuel ih =>
    intro E c w hv hw hn
    unfold mergeUp
    repeat' first
      | wpSimplify
      | neCore
      | neUse (nex_descendToHeight _ _ _ _)
      | neUse (nex_merge _ _ _)
      | neUse (ih _ _)
      | wpSplit
      | split
      | contradiction

theorem nex_afterDelete (B : NodeId) (key : Key) (g h : Nat) :
    KeepsNE B (afterDelete key g h) := by
  intro E c w hv hw hn
  unfold afterDelete
  repeat' first
    | wpSimplify
    | neCore
    | neUse (nex_mergeUp _ _ _ _ _ _)
    | neUse (nex_collapseRoot _ _ _ _)
    | wpSplit
    | split
    | contradiction

/-! ## The upward unlink, a put -/

theorem nex_climb (B : NodeId) (depth : Nat) : KeepsNE B (climb depth) := by
  induction depth with
  | zero =>
    intro E c w hv hw hn
    unfold climb
    repeat' first | wpSimplify | neCore | wpSplit | split | contradiction
  | succ depth ih =>
    intro E c w hv hw hn
    unfold climb
    repeat' first
      | wpSimplify
      | neCore
      | neUse (nex_canTakeBack _ _ _ _)
      | neUse ih
      | wpSplit
      | split
      | contradiction

macro "neFoldWith " b:term " using " extra:tactic : tactic => `(tactic| (
  (with_reducible refine writerWP_of_ne (nex_foldlM $b _ _ _ ?neBody) ?neE _ _ _ ?gdView ?gdState ?neState ?gdPost)
  case neBody =>
    intro b a E c w hv hw hn
    repeat' first
      | wpSimplify
      | neCore
      | ($extra:tactic)
      | wpSplit
      | split
      | contradiction
  case neState => assumption
  case gdView => assumption
  case gdState => assumption
  intro _ _ _ _))

/-- The invariant kept by a step in the context c of its caller (a loop's
body tests the caller's time). -/
def KeepsNEAt (B : NodeId) (c : Ctx) {α : Type} (f : M α) : Prop :=
  ∀ (E : List NodeId) w, CacheGood B c w → NEx E w →
    WriterWP f c w (fun _ v => CacheGood B c v ∧ NEx E v)

theorem nex_forIn_at (B : NodeId) (c : Ctx) {α β : Type} (xs : List α) (init : β)
    (f : α → β → M (ForInStep β)) (hf : ∀ a b, KeepsNEAt B c (f a b)) :
    KeepsNEAt B c (forIn xs init f) := by
  induction xs generalizing init with
  | nil => intro E w hw hn; simpa only [List.forIn_nil, writerWP_pure] using ⟨hw, hn⟩
  | cons a xs ih =>
    intro E w hw hn
    rw [List.forIn_cons, writerWP_bind]
    refine writerWP_mono (hf a init E w hw hn) ?_
    intro step v hh
    cases step with
    | done b => simpa only [writerWP_pure] using hh
    | yield b => exact ih b E v hh.1 hh.2

macro "neForWith " b:term " using " extra:tactic : tactic => `(tactic| (
  (refine writerWP_mono (nex_forIn_at $b _ _ _ _ ?neBody ?neE _ ?gdState ?neState) ?gdPost)
  case neBody =>
    intro a b E w hw hn
    repeat' first
      | wpSimplify
      | neCore
      | ($extra:tactic)
      | wpSplit
      | split
      | contradiction
  case neState => assumption
  case gdState => assumption
  rintro _ _ ⟨_, _⟩))

set_option maxHeartbeats 1600000 in
theorem nex_deleteUpward (B : NodeId) (leaf : NodeId) (depth cv : Nat) (key : Key) :
    KeepsNE B (deleteUpward leaf depth cv key) := by
  intro E c w hv hw hn
  unfold deleteUpward
  repeat' first
    | wpSimplify
    | neCore
    | neUse (nex_appendDeleteKlong _ _ _ _)
    | neUse (nex_emptyKeyNext _ _ _)
    | neUse (nex_afterDelete _ _ _ _)
    | neFoldWith B using fail
    | neForWith B using (first | neUse (nex_takeBack _ _ _ _) | neUnlink)
    | neUse (nex_climb _ _)
    | neUse (nex_mergeUp _ _ _ _ _ _)
    | neUse (nex_collapseRoot _ _ _ _)
    | wpSplit
    | split
    | contradiction

theorem nex_setValue (B : NodeId) (segRoot : NodeId) (cv : Nat) (key : Key) (value : Option Nat) :
    KeepsNE B (setValue segRoot cv key value) := by
  intro E c w hv hw hn
  have hpos := hv.pos
  unfold setValue
  repeat' first
    | wpSimplify
    | neCore
    | neAppend
    | neUse (nex_deleteUpward _ _ _ _ _)
    | wpSplit
    | split
    | contradiction

end SIS.Tree
