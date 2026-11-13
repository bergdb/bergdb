/-
The tree model (bergdb 024-12, TP7): the writer keeps its books (`Book`),
continued from SIS/Tree/WriterBook.lean: `appendKlongs`, the descents, the
delete with LE-b, the take-back and root collapse, the merges, a put, and a
transaction (`execW_book`).
-/
import SIS.Tree.WriterBook

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

macro "bkFullWith " hup:term : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (handleFullWith _ _ _ _ _ _) _ _ _)
  bkUse (book_handleFullWith _ _ _ _ _ _ _ $hup)))

theorem book_appendKlongs (B : NodeId) (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) :
    KeepsBook B (appendKlongs depth x ins) := by
  induction depth generalizing x ins with
  | zero =>
    intro c w hv hb
    rw [appendKlongs_step_dead]
    repeat' first
      | wpSimplify
      | bkNode
      | bkFullWith (fun _ _ => book_throw B _)
      | bkUse (book_addKeys _ _ _)
      | bkDone
      | wpSplit
      | split
  | succ depth ih =>
    intro c w hv hb
    rw [appendKlongs_step_dead]
    repeat' first
      | wpSimplify
      | bkNode
      | bkFullWith (fun q more => ih q more)
      | bkUse (book_addKeys _ _ _)
      | bkDone
      | wpSplit
      | split

theorem book_handleFull (B : NodeId) (depth : Nat) (x : NodeId) (last : KNode) (compact : Bool) :
    KeepsBook B (handleFull depth x last compact) := by
  unfold handleFull
  refine book_handleFullWith B _ depth x [] last compact ?_
  intro q more
  cases depth with
  | zero => exact book_throw B _
  | succ d => exact book_appendKlongs B _ _ _

theorem book_descendLte (B : NodeId) (cv fuel : Nat) (x : NodeId) :
    KeepsBook B (descendLte cv fuel x) := by
  induction fuel generalizing x with
  | zero => exact book_throw B _
  | succ fuel ih =>
    intro c w hv hb
    unfold descendLte
    repeat' first
      | wpSimplify
      | bkCore
      | bkUse (ih _)
      | wpSplit
      | split
      | contradiction

theorem book_foldlM (B : NodeId) {α β : Type} (xs : List α) (f : β → α → M β) (init : β)
    (hf : ∀ b a, KeepsBook B (f b a)) : KeepsBook B (xs.foldlM f init) := by
  induction xs generalizing init with
  | nil => intro c w hv hb; simpa only [List.foldlM_nil, writerWP_pure] using ⟨hb, Kept.refl w⟩
  | cons a xs ih =>
    intro c w hv hb
    rw [List.foldlM_cons, writerWP_bind]
    refine writerWP_mono (hf init a c w hv hb) ?_
    rintro b v ⟨hbv, hk⟩
    exact writerWP_mono (ih b c v hv hbv) (fun _ u h => ⟨h.1, hk.trans h.2⟩)

theorem book_forIn (B : NodeId) {α β : Type} (xs : List α) (init : β)
    (f : α → β → M (ForInStep β)) (hf : ∀ a b, KeepsBook B (f a b)) :
    KeepsBook B (forIn xs init f) := by
  induction xs generalizing init with
  | nil => intro c w hv hb; simpa only [List.forIn_nil, writerWP_pure] using ⟨hb, Kept.refl w⟩
  | cons a xs ih =>
    intro c w hv hb
    rw [List.forIn_cons, writerWP_bind]
    refine writerWP_mono (hf a init c w hv hb) ?_
    rintro step v ⟨hbv, hk⟩
    cases step with
    | done b => simpa only [writerWP_pure] using ⟨hbv, hk⟩
    | yield b => exact writerWP_mono (ih b c v hv hbv) (fun _ u h => ⟨h.1, hk.trans h.2⟩)

theorem book_descendToSegmentRoot (B : NodeId) (key : Key) (segment : Nat) :
    KeepsBook B (descendToSegmentRoot key segment) := by
  intro c w hv hb
  unfold descendToSegmentRoot
  wpSimplify
  bkUse (book_pathClear _)
  bkUse (book_findRoot _)
  refine book_writerWP (book_foldlM B _ _ _ ?_) c _ _ hv (by assumption) ?_
  · intro node cv c w hv hb
    repeat' first
      | wpSimplify
      | bkCore
      | bkUse (book_descendLte _ _ _ _)
      | wpSplit
      | split
      | contradiction
  · intro _ _ _ _
    bkDone

/-! ## The delete -/

macro "bkAppend" : tactic => `(tactic| first
  | bkUse (book_handleFull _ _ _ _ _)
  | bkUse (book_appendKlongs _ _ _ _)
  | bkUse (book_addKeys _ _ _)
  | bkUse (book_descendLte _ _ _ _))

set_option maxHeartbeats 1000000 in
theorem book_appendDeleteKlong (B : NodeId) (x : NodeId) (depth cv : Nat) :
    KeepsBook B (appendDeleteKlong x depth cv) := by
  intro c w hv hb
  unfold appendDeleteKlong
  repeat' first
    | wpSimplify
    | bkCore
    | bkAppend
    | wpSplit
    | split
    | contradiction

set_option maxHeartbeats 1400000 in
theorem book_emptyKeyNext (B : NodeId) (x : NodeId) (depth : Nat) :
    KeepsBook B (emptyKeyNext x depth) := by
  intro c w hv hb
  unfold emptyKeyNext
  repeat' first
    | wpSimplify
    | bkCore
    | bkAppend
    | wpSplit
    | split
    | contradiction

theorem book_unlink (B : NodeId) (x : NodeId) : KeepsBook B (unlink x) := by
  intro c w hv hb
  unfold unlink
  repeat' first | wpSimplify | bkCore | wpSplit | split | contradiction

theorem book_retarget (B : NodeId) (q src dst : NodeId) : KeepsBook B (retarget q src dst) := by
  intro c w hv hb
  unfold retarget
  repeat' first | wpSimplify | bkCore | wpSplit | split | contradiction

theorem book_canTakeBack (B : NodeId) (x parent : NodeId) (cv : Nat) :
    KeepsBook B (canTakeBack x parent cv) := by
  intro c w hv hb
  unfold canTakeBack
  repeat' first | wpSimplify | bkCore | wpSplit | split | contradiction

/-- `takeBack` of a node of the overlay, read at an earlier state. -/
theorem book_takeBack (B x parent : NodeId) (cv : Nat) (c : Ctx) (w vr : W) (n : KNode)
    (hv : ViewIdsBelow B c.view) (hb : Book B c w) (hl : vr.nodes.lookup x = some n)
    (hk : Kept vr w) :
    WriterWP (takeBack x parent cv) c w (fun _ v => Book B c v ∧ Kept w v) := by
  unfold takeBack
  repeat' first
    | wpSimplify
    | bkCore
    | bkUse (book_retarget _ _ _ _)
    | wpSplit
    | split
    | contradiction

macro "bkTakeBack" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (takeBack _ _ _) _ _ _)
  (refine writerWP_mono (book_takeBack ?bkB _ _ _ _ _ ?bkVr ?bkN ?bkView ?bkState ?bkLook ?bkKept)
    ?bkPost)
  case bkView => assumption
  case bkState => bkState
  case bkLook => assumption
  case bkKept => bkChain
  rintro _ _ ⟨_, _⟩))

theorem book_takeBackRoot (B : NodeId) (x : NodeId) (depth only : Nat) :
    KeepsBook B (takeBackRoot x depth only) := by
  intro c w hv hb
  unfold takeBackRoot
  repeat' first | wpSimplify | bkCore | wpSplit | split | contradiction

theorem book_replaceRoot (B : NodeId) (x : NodeId) (depth only : Nat) :
    KeepsBook B (replaceRoot x depth only) := by
  intro c w hv hb
  unfold replaceRoot
  repeat' first
    | wpSimplify
    | bkCore
    | bkAppend
    | bkUse (book_unlink _ _)
    | wpSplit
    | split
    | contradiction

theorem book_collapseRoot (B : NodeId) (key : Key) (segment fuel : Nat) :
    KeepsBook B (collapseRoot key segment fuel) := by
  induction fuel with
  | zero => exact book_throw B _
  | succ fuel ih =>
    intro c w hv hb
    unfold collapseRoot
    repeat' first
      | wpSimplify
      | bkCore
      | bkUse (book_descendToSegmentRoot _ _ _)
      | bkUse (book_takeBackRoot _ _ _ _)
      | bkUse (book_replaceRoot _ _ _ _)
      | bkUse ih
      | wpSplit
      | split
      | contradiction

/-! ## The merges -/

theorem book_descendHeight (B : NodeId) (cv h fuel : Nat) (x : NodeId) :
    KeepsBook B (descendHeight cv h fuel x) := by
  induction fuel generalizing x with
  | zero => exact book_throw B _
  | succ fuel ih =>
    intro c w hv hb
    unfold descendHeight
    repeat' first
      | wpSimplify
      | bkCore
      | bkUse (ih _)
      | wpSplit
      | split
      | contradiction

theorem book_descendToHeight (B : NodeId) (key : Key) (g h : Nat) :
    KeepsBook B (descendToHeight key g h) := by
  intro c w hv hb
  unfold descendToHeight
  repeat' first
    | wpSimplify
    | bkCore
    | bkUse (book_descendToSegmentRoot _ _ _)
    | bkUse (book_descendHeight _ _ _ _ _)
    | wpSplit
    | split
    | contradiction

set_option maxHeartbeats 1600000 in
theorem book_mergeParent (B : NodeId) (q : NodeId) (depth il cL : Nat) (m1 : NodeId) (ir cR : Nat)
    (m2 : Option (NodeId × Nat)) :
    KeepsBook B (mergeParent q depth il cL m1 ir cR m2) := by
  intro c w hv hb
  unfold mergeParent
  repeat' first
    | wpSimplify
    | bkCore
    | bkAppend
    | wpSplit
    | split
    | contradiction

/-- `sibling`: a read of the node that klong i of q names. -/
theorem book_sibling (B : NodeId) (q : NodeId) (pn : KNode) (i : Nat) (inner : Bool) (c : Ctx)
    (w : W) (hv : ViewIdsBelow B c.view) (hb : Book B c w) :
    WriterWP (sibling q pn i inner) c w (fun r v =>
      Book B c v ∧ Kept w v ∧ v.nodes.lookup r.1 = some r.2) := by
  unfold sibling
  repeat' first
    | wpSimplify
    | bkNode
    | exact writerWP_throw _ _ _ _
    | (refine ⟨?_, ?_, ?_⟩ <;> first | bkState | bkChain | assumption)
    | wpSplit
    | split
    | contradiction

macro "bkSibling" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (sibling _ _ _ _) _ _ _)
  (refine writerWP_mono (book_sibling ?bkB _ _ _ _ _ _ ?bkView ?bkState) ?bkPost)
  case bkView => assumption
  case bkState => bkState
  rintro ⟨_, _⟩ _ ⟨_, _, _⟩))

/-- A loop over nodes of the overlay. -/
theorem book_forIn_mem (B : NodeId) {β : Type} (xs : List (NodeId × Bool)) (init : β)
    (f : NodeId × Bool → β → M (ForInStep β))
    (hf : ∀ a b c w, ViewIdsBelow B c.view → Book B c w → (∃ n, w.nodes.lookup a.1 = some n) →
      WriterWP (f a b) c w (fun _ v => Book B c v ∧ Kept w v))
    (c : Ctx) (w : W) (hv : ViewIdsBelow B c.view) (hb : Book B c w)
    (hm : ∀ a ∈ xs, ∃ n, w.nodes.lookup a.1 = some n) :
    WriterWP (forIn xs init f) c w (fun _ v => Book B c v ∧ Kept w v) := by
  induction xs generalizing init w with
  | nil => simpa only [List.forIn_nil, writerWP_pure] using ⟨hb, Kept.refl w⟩
  | cons a xs ih =>
    rw [List.forIn_cons, writerWP_bind]
    refine writerWP_mono (hf a init c w hv hb (hm a List.mem_cons_self)) ?_
    rintro step v ⟨hbv, hk⟩
    cases step with
    | done b => simpa only [writerWP_pure] using ⟨hbv, hk⟩
    | yield b =>
      refine writerWP_mono (ih b v hbv ?_) (fun _ u h => ⟨h.1, hk.trans h.2⟩)
      intro e he
      obtain ⟨n, hn⟩ := hm e (List.mem_cons_of_mem _ he)
      exact hk.has hn

/-- An id read at an earlier state is in the overlay now. -/
macro "bkHas" : tactic => `(tactic| (
  (refine Kept.has (a := ?bkVr) (n := ?bkN) ?bkKept ?bkLook)
  case bkLook => assumption
  case bkKept => bkChain))

/-- The loop of a merge over the two nodes merged, both read. -/
macro "bkMergeLoop" : tactic => `(tactic| (
  (refine writerWP_mono (book_forIn_mem ?bkB _ _ _ ?bkBody _ _ ?bkView ?bkState ?bkMem) ?bkPost)
  case bkBody =>
    rintro ⟨_, _⟩ _ c w hv hb ⟨_, _⟩
    repeat' first
      | wpSimplify
      | bkCore
      | bkUse (book_unlink _ _)
      | bkUse (book_retarget _ _ _ _)
      | wpSplit
      | split
      | contradiction
  case bkView => assumption
  case bkState => bkState
  case bkMem =>
    intro _ hbkMem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hbkMem
    rcases hbkMem with hbkMem | hbkMem <;> subst hbkMem <;> bkHas
  rintro _ _ ⟨_, _⟩))

end SIS.Tree
