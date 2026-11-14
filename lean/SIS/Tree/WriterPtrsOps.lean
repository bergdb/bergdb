/-
The tree model (bergdb 024-12, TP4 and TP7): the writer keeps `PtrsOK`,
continued from SIS/Tree/WriterPtrs.lean: `appendKlongs`, the descents, the
delete with LE-b, the take-back and root collapse, and a merge's parent.
-/
import SIS.Tree.WriterPtrs
import SIS.Tree.WriterSteps

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

macro "ptUse1 " h:term : tactic => `(tactic| (
  (refine' writerWP_mono ($h _ _ ?ptView ?ptState ?ptA) ?ptPost)
  case ptView => assumption
  case ptState => ptState
  case ptA => ptPre
  rintro _ _ ⟨_, _⟩))

macro "ptUse2 " h:term : tactic => `(tactic| (
  (refine' writerWP_mono ($h _ _ ?ptView ?ptState ?ptA ?ptB) ?ptPost)
  case ptView => assumption
  case ptState => ptState
  case ptA => ptPre
  case ptB => ptPre
  rintro _ _ ⟨_, _⟩))

theorem ptrsUp_throw (Old : NodeId → Prop) (e : String) :
    ptrsUp Old (fun _ _ => (throw e : M Unit)) := by
  intro q more c w _ _ _
  exact writerWP_throw _ _ _ _

theorem ptrs_appendKlongs (Old : NodeId → Prop) (depth : Nat) :
    ptrsUp Old (appendKlongs depth) := by
  induction depth with
  | zero =>
    intro x ins c w hv hw hi
    rw [appendKlongs_step_dead]
    repeat' first
      | wpSimplify
      | ptNode
      | ptUse2 (ptrs_handleFullWith _ _ _ _ _ _ _ (ptrsUp_throw Old _))
      | ptUse1 (ptrs_addKeys _ _ _)
      | ptDone
      | wpSplit
      | split
  | succ depth ih =>
    intro x ins c w hv hw hi
    rw [appendKlongs_step_dead]
    repeat' first
      | wpSimplify
      | ptNode
      | ptUse2 (ptrs_handleFullWith _ _ _ _ _ _ _ (fun q more => ih q more))
      | ptUse1 (ptrs_addKeys _ _ _)
      | ptDone
      | wpSplit
      | split

theorem ptrs_handleFull (Old : NodeId → Prop) (depth : Nat) (x : NodeId) (last : KNode)
    (compact : Bool) (c : Ctx) (w : W) (hv : ViewPtrsOld Old c.view) (hw : PtrsOK Old c w)
    (hl : ptrsKs (ptrsId Old w) last.ks) :
    WriterWP (handleFull depth x last compact) c w (fun _ v => PtrsOK Old c v ∧ MadeKept w v) := by
  unfold handleFull
  refine ptrs_handleFullWith Old _ depth x [] last compact ?_ c w hv hw hl (ptrsPairs_nil _)
  cases depth with
  | zero => exact ptrsUp_throw Old _
  | succ d => exact ptrs_appendKlongs Old d

theorem ptrs_descendLte (Old : NodeId → Prop) (cv fuel : Nat) (x : NodeId) :
    KeepsPtrs Old (descendLte cv fuel x) := by
  induction fuel generalizing x with
  | zero => exact ptrs_throw Old _
  | succ fuel ih =>
    intro c w hv hw
    unfold descendLte
    repeat' first
      | wpSimplify
      | ptCore
      | ptUse (ih _)
      | wpSplit
      | split
      | contradiction

theorem ptrs_foldlM (Old : NodeId → Prop) {α β : Type} (xs : List α) (f : β → α → M β)
    (init : β) (hf : ∀ b a, KeepsPtrs Old (f b a)) : KeepsPtrs Old (xs.foldlM f init) := by
  induction xs generalizing init with
  | nil =>
    intro c w hv hw
    simpa only [List.foldlM_nil, writerWP_pure] using ⟨hw, MadeKept.refl w⟩
  | cons a xs ih =>
    intro c w hv hw
    rw [List.foldlM_cons, writerWP_bind]
    refine writerWP_mono (hf init a c w hv hw) ?_
    rintro b v ⟨hwv, hk⟩
    exact writerWP_mono (ih b c v hv hwv) (fun _ u h => ⟨h.1, hk.trans h.2⟩)

theorem ptrs_forIn (Old : NodeId → Prop) {α β : Type} (xs : List α) (init : β)
    (f : α → β → M (ForInStep β)) (hf : ∀ a b, KeepsPtrs Old (f a b)) :
    KeepsPtrs Old (forIn xs init f) := by
  induction xs generalizing init with
  | nil =>
    intro c w hv hw
    simpa only [List.forIn_nil, writerWP_pure] using ⟨hw, MadeKept.refl w⟩
  | cons a xs ih =>
    intro c w hv hw
    rw [List.forIn_cons, writerWP_bind]
    refine writerWP_mono (hf a init c w hv hw) ?_
    rintro step v ⟨hwv, hk⟩
    cases step with
    | done b => simpa only [writerWP_pure] using ⟨hwv, hk⟩
    | yield b => exact writerWP_mono (ih b c v hv hwv) (fun _ u h => ⟨h.1, hk.trans h.2⟩)

theorem ptrs_descendToSegmentRoot (Old : NodeId → Prop) (key : Key) (segment : Nat) :
    KeepsPtrs Old (descendToSegmentRoot key segment) := by
  intro c w hv hw
  unfold descendToSegmentRoot
  wpSimplify
  ptUse (ptrs_pathClear _)
  ptUse (ptrs_findRoot _)
  refine ptrs_writerWP (ptrs_foldlM Old _ _ _ ?_) c _ _ hv (by assumption) ?_
  · intro node cv c w hv hw
    repeat' first
      | wpSimplify
      | ptCore
      | ptUse (ptrs_descendLte _ _ _ _)
      | wpSplit
      | split
      | contradiction
  · intro _ _ _ _
    ptDone

/-! ## The delete -/

macro "ptAppend" : tactic => `(tactic| first
  | ptUse1 (ptrs_handleFull _ _ _ _ _)
  | ptUp (ptrs_appendKlongs _ _)
  | ptUse1 (ptrs_addKeys _ _ _)
  | ptUse (ptrs_descendLte _ _ _ _))

set_option maxHeartbeats 1000000 in
theorem ptrs_appendDeleteKlong (Old : NodeId → Prop) (x : NodeId) (depth cv : Nat) :
    KeepsPtrs Old (appendDeleteKlong x depth cv) := by
  intro c w hv hw
  unfold appendDeleteKlong
  repeat' first
    | wpSimplify
    | ptCore
    | ptAppend
    | wpSplit
    | split
    | contradiction

set_option maxHeartbeats 1400000 in
theorem ptrs_emptyKeyNext (Old : NodeId → Prop) (x : NodeId) (depth : Nat) :
    KeepsPtrs Old (emptyKeyNext x depth) := by
  intro c w hv hw
  unfold emptyKeyNext
  repeat' first
    | wpSimplify
    | ptCore
    | ptAppend
    | wpSplit
    | split
    | contradiction

theorem ptrs_unlink (Old : NodeId → Prop) (x : NodeId) : KeepsPtrs Old (unlink x) := by
  intro c w hv hw
  unfold unlink
  repeat' first | wpSimplify | ptCore | wpSplit | split | contradiction

theorem ptrs_retarget (Old : NodeId → Prop) (q src dst : NodeId) (c : Ctx) (w : W)
    (hv : ViewPtrsOld Old c.view) (hw : PtrsOK Old c w) (hd : ptrsId Old w dst) :
    WriterWP (retarget q src dst) c w (fun _ v => PtrsOK Old c v ∧ MadeKept w v) := by
  unfold retarget
  repeat' first | wpSimplify | ptCore | wpSplit | split | contradiction

theorem ptrs_canTakeBack (Old : NodeId → Prop) (x parent : NodeId) (cv : Nat) :
    KeepsPtrs Old (canTakeBack x parent cv) := by
  intro c w hv hw
  unfold canTakeBack
  repeat' first | wpSimplify | ptCore | wpSplit | split | contradiction

theorem ptrs_takeBack (Old : NodeId → Prop) (x parent : NodeId) (cv : Nat) :
    KeepsPtrs Old (takeBack x parent cv) := by
  intro c w hv hw
  unfold takeBack
  repeat' first
    | wpSimplify
    | ptCore
    | ptUse1 (ptrs_retarget _ _ _ _)
    | wpSplit
    | split
    | contradiction

theorem ptrs_takeBackRoot (Old : NodeId → Prop) (x : NodeId) (depth only : Nat) :
    KeepsPtrs Old (takeBackRoot x depth only) := by
  intro c w hv hw
  unfold takeBackRoot
  repeat' first | wpSimplify | ptCore | wpSplit | split | contradiction

theorem ptrs_replaceRoot (Old : NodeId → Prop) (x : NodeId) (depth only : Nat) :
    KeepsPtrs Old (replaceRoot x depth only) := by
  intro c w hv hw
  unfold replaceRoot
  repeat' first
    | wpSimplify
    | ptCore
    | ptAppend
    | ptUse (ptrs_unlink _ _)
    | wpSplit
    | split
    | contradiction

theorem ptrs_collapseRoot (Old : NodeId → Prop) (key : Key) (segment fuel : Nat) :
    KeepsPtrs Old (collapseRoot key segment fuel) := by
  induction fuel with
  | zero => exact ptrs_throw Old _
  | succ fuel ih =>
    intro c w hv hw
    unfold collapseRoot
    repeat' first
      | wpSimplify
      | ptCore
      | ptUse (ptrs_descendToSegmentRoot _ _ _)
      | ptUse (ptrs_takeBackRoot _ _ _ _)
      | ptUse (ptrs_replaceRoot _ _ _ _)
      | ptUse ih
      | wpSplit
      | split
      | contradiction

/-! ## The merges -/

theorem ptrs_descendHeight (Old : NodeId → Prop) (cv h fuel : Nat) (x : NodeId) :
    KeepsPtrs Old (descendHeight cv h fuel x) := by
  induction fuel generalizing x with
  | zero => exact ptrs_throw Old _
  | succ fuel ih =>
    intro c w hv hw
    unfold descendHeight
    repeat' first
      | wpSimplify
      | ptCore
      | ptUse (ih _)
      | wpSplit
      | split
      | contradiction

theorem ptrs_descendToHeight (Old : NodeId → Prop) (key : Key) (g h : Nat) :
    KeepsPtrs Old (descendToHeight key g h) := by
  intro c w hv hw
  unfold descendToHeight
  repeat' first
    | wpSimplify
    | ptCore
    | ptUse (ptrs_descendToSegmentRoot _ _ _)
    | ptUse (ptrs_descendHeight _ _ _ _ _)
    | wpSplit
    | split
    | contradiction

set_option maxHeartbeats 8000000 in
theorem ptrs_mergeParent (Old : NodeId → Prop) (q : NodeId) (depth il cL : Nat) (m1 : NodeId)
    (ir cR : Nat) (m2 : Option (NodeId × Nat)) (c : Ctx) (w : W) (hv : ViewPtrsOld Old c.view)
    (hw : PtrsOK Old c w) (h1 : ptrsId Old w m1) (h2 : ptrsOpt Old w (m2.map (·.1))) :
    WriterWP (mergeParent q depth il cL m1 ir cR m2) c w
      (fun _ v => PtrsOK Old c v ∧ MadeKept w v) := by
  unfold mergeParent
  repeat' first
    | wpSimplify
    | ptCore
    | ptAppend
    | wpSplit
    | split
    | contradiction

/-- `sibling`: a read of the node that klong i of q names. -/
theorem ptrs_sibling (Old : NodeId → Prop) (q : NodeId) (pn : KNode) (i : Nat) (inner : Bool)
    (c : Ctx) (w : W) (hv : ViewPtrsOld Old c.view) (hw : PtrsOK Old c w) :
    WriterWP (sibling q pn i inner) c w (fun r v =>
      PtrsOK Old c v ∧ MadeKept w v ∧ ptrsKs (ptrsId Old v) r.2.ks ∧ ptrsId Old v r.1) := by
  unfold sibling
  repeat' first
    | wpSimplify
    | ptNode
    | exact writerWP_throw _ _ _ _
    | (refine ⟨?_, ?_, ?_, ?_⟩ <;> first | ptState | ptChain | assumption)
    | wpSplit
    | split
    | contradiction

macro "ptSibling" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (sibling _ _ _ _) _ _ _)
  (refine writerWP_mono (ptrs_sibling ?ptOld _ _ _ _ _ _ ?ptView ?ptState) ?ptPost)
  case ptView => assumption
  case ptState => ptState
  rintro ⟨_, _⟩ _ ⟨_, _, _, _⟩))

/-- A loop whose steps keep `PtrsOK` for states after w0. -/
theorem ptrs_forIn_from (Old : NodeId → Prop) {α β : Type} (xs : List α) (init : β)
    (f : α → β → M (ForInStep β)) (c : Ctx) (w0 : W)
    (hf : ∀ a b w, PtrsOK Old c w → MadeKept w0 w →
      WriterWP (f a b) c w (fun _ v => PtrsOK Old c v ∧ MadeKept w v))
    (w : W) (hw : PtrsOK Old c w) (hk : MadeKept w0 w) :
    WriterWP (forIn xs init f) c w (fun _ v => PtrsOK Old c v ∧ MadeKept w v) := by
  induction xs generalizing init w with
  | nil => simpa only [List.forIn_nil, writerWP_pure] using ⟨hw, MadeKept.refl w⟩
  | cons a xs ih =>
    rw [List.forIn_cons, writerWP_bind]
    refine writerWP_mono (hf a init w hw hk) ?_
    rintro step v ⟨hwv, hkv⟩
    cases step with
    | done b => simpa only [writerWP_pure] using ⟨hwv, hkv⟩
    | yield b =>
      exact writerWP_mono (ih b v hwv (hk.trans hkv)) (fun _ u h => ⟨h.1, hkv.trans h.2⟩)

/-- The loop of a merge over the two nodes merged. -/
macro "ptMergeLoop" : tactic => `(tactic| (
  (refine writerWP_mono (ptrs_forIn_from ?ptOld _ _ _ _ _ ?ptBody _ ?ptState (MadeKept.refl _))
    ?ptPost)
  case ptState => ptState
  case ptBody =>
    rintro ⟨_, _⟩ _ w hw _
    repeat' first
      | wpSimplify
      | ptCore
      | ptUse (ptrs_unlink _ _)
      | ptUse1 (ptrs_retarget _ _ _ _)
      | wpSplit
      | split
      | contradiction
  rintro _ _ ⟨_, _⟩))

end SIS.Tree
