/-
The tree model (bergdb 024-12, TP5's writer part): a key node holds at most M
klongs, continued from SIS/Tree/WriterSize.lean: the descents, the delete with
LE-b, the take-back and root collapse, the merges, a put, and a transaction
(`execW_sizeOK`).
-/
import SIS.Tree.WriterSize

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem sized_descendLte (cv fuel : Nat) (x : NodeId) : KeepsSized (descendLte cv fuel x) := by
  induction fuel generalizing x with
  | zero => exact sized_throw _
  | succ fuel ih =>
    intro c w hv hw
    unfold descendLte
    repeat' first
      | wpSimplify
      | szCore
      | szUse (ih _)
      | wpSplit
      | split
      | contradiction

theorem sized_foldlM {α β : Type} (xs : List α) (f : β → α → M β) (init : β)
    (hf : ∀ b a, KeepsSized (f b a)) : KeepsSized (xs.foldlM f init) := by
  induction xs generalizing init with
  | nil => intro c w hv hw; simpa only [List.foldlM_nil, writerWP_pure] using hw
  | cons a xs ih =>
    intro c w hv hw
    rw [List.foldlM_cons, writerWP_bind]
    exact writerWP_mono (hf init a c w hv hw) (fun b v hh => ih b c v hv hh)

theorem sized_forIn {α β : Type} (xs : List α) (init : β)
    (f : α → β → M (ForInStep β)) (hf : ∀ a b, KeepsSized (f a b)) :
    KeepsSized (forIn xs init f) := by
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

theorem sized_descendToSegmentRoot (key : Key) (segment : Nat) :
    KeepsSized (descendToSegmentRoot key segment) := by
  intro c w hv hw
  unfold descendToSegmentRoot
  wpSimplify
  szUse sized_pathClear
  szUse sized_findRoot
  refine sized_foldlM _ _ _ ?_ c _ hv (by assumption)
  intro node cv c w hv hw
  repeat' first
    | wpSimplify
    | szCore
    | szUse (sized_descendLte _ _ _)
    | wpSplit
    | split
    | contradiction

/-! ## Last versions of a delete -/

/-- LE-b's last version: the next child's klong becomes the empty key's. -/
theorem lvRename_le (n : KNode) (t : Time) (d : List Nat) (m : Nat) (k0 k1 k : Klong)
    (r : List Klong) (b : Bool) (h : (n.lastVersionGivenDel t d).ks = k0 :: k1 :: r)
    (hf : TimeFirst n.ks) (hs : n.size ≤ m) (h1 : 1 ≤ m) :
    ({ leaf := b, ks := k0 :: k :: r } : KNode).size ≤ m := by
  have := n.lastVersionGivenDel_le t d m hf hs h1
  unfold KNode.size at *
  rw [h] at this
  simpa using this

/-- The merge parent's last version, its left child's klong pointed to the
first new node. -/
theorem rk1_le (n : KNode) (t t' : Time) (d : List Nat) (m cv : Nat) (y : NodeId)
    (ks : List Klong) (b : Bool)
    (h : replaceKlong (n.lastVersionGivenDel t d).ks t' cv y = .ok (some ks))
    (hf : TimeFirst n.ks) (hs : n.size ≤ m) (h1 : 1 ≤ m) :
    ({ leaf := b, ks := ks } : KNode).size ≤ m := by
  have := n.lastVersionGivenDel_le t d m hf hs h1
  have he := replaceKlong_length _ _ _ _ _ h
  unfold KNode.size at *
  show ks.length ≤ m
  omega

/-- And the right child's klong pointed to the second new node. -/
theorem rk2_le (n : KNode) (t t' t'' : Time) (d : List Nat) (m cv cv' : Nat) (y y' : NodeId)
    (ks ks2 : List Klong) (b : Bool)
    (h2 : replaceKlong ks t'' cv' y' = .ok (some ks2))
    (h : replaceKlong (n.lastVersionGivenDel t d).ks t' cv y = .ok (some ks))
    (hf : TimeFirst n.ks) (hs : n.size ≤ m) (h1 : 1 ≤ m) :
    ({ leaf := b, ks := ks2 } : KNode).size ≤ m := by
  have := n.lastVersionGivenDel_le t d m hf hs h1
  have he := replaceKlong_length _ _ _ _ _ h
  have he2 := replaceKlong_length _ _ _ _ _ h2
  unfold KNode.size at *
  show ks2.length ≤ m
  omega

/-- Or a new klong for the second new node. -/
theorem rkIns_le (n : KNode) (t t' : Time) (d : List Nat) (m cv g : Nat) (y y' : NodeId)
    (ks : List Klong) (b : Bool)
    (h : replaceKlong (n.lastVersionGivenDel t d).ks t' cv y = .ok (some ks))
    (hf : TimeFirst n.ks) (hs : n.size + 1 ≤ m) (h1 : 2 ≤ m) :
    ({ leaf := b, ks := insertSorted ks g y' } : KNode).size ≤ m := by
  have := n.lastVersionGivenDel_add_le t d 1 m hf hs (by omega)
  have he := replaceKlong_length _ _ _ _ _ h
  unfold KNode.size at *
  rw [insertSorted_length]
  omega

/-- The merge parent's need when a klong is inserted for the second new node:
one klong at least. -/
theorem need_pos (s m A B C : Nat) (d o a : Bool) (m2 : Option (NodeId × Nat))
    (q : NodeId × Nat)
    (hroom : s + (A + B + (if (m2.isNone || (!d && o && a)) = true then 0 else 1) + C) ≤ m)
    (hd : d = true) (hm : m2 = some q) : s + 1 ≤ m := by
  subst hd hm
  simp only [Option.isNone_some, Bool.not_true, Bool.false_and, Bool.or_false,
    Bool.false_eq_true, ↓reduceIte] at hroom
  omega

macro "szLast" : tactic => `(tactic| first
  | szLV
  | ((refine lvRename_le _ _ _ _ _ _ _ _ _ (by assumption) ?_ ?_ ?_) <;> first | assumption | szArith)
  | ((refine rk1_le _ _ _ _ _ _ _ _ _ (by assumption) ?_ ?_ ?_) <;> first | assumption | szArith)
  | ((refine rk2_le _ _ _ _ _ _ _ _ _ _ _ _ _ (by assumption) (by assumption) ?_ ?_ ?_) <;>
      first | assumption | szArith)
  | ((refine rkIns_le _ _ _ _ _ _ _ _ _ _ _ (by assumption) ?_ ?_ ?_) <;> first
      | assumption
      | szArith
      | (have := need_pos _ _ _ _ _ _ _ _ _ _ (by assumption) (by assumption)
           (by first | rfl | assumption)
         szArith)))

macro "szHandle" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (handleFull _ _ _ _) _ _ _)
  (with_unfolding_none refine writerWP_mono (sized_handleFull _ _ _ _ _ _ ?szView ?szState ?szLastFlat ?szL ?szC) ?szPost)
  case szView => assumption
  case szState => assumption
  case szLastFlat => first
    | gdFlat
    | (refine flatAt_rename_after_head _ _ _ _ _ _ _ (by assumption) ?_; gdFlat)
  case szL => szLast
  case szC => (intro _; szLast)
  intro _ _ _))

macro "szAppend" : tactic => `(tactic| first
  | szHandle
  | szUse (sized_appendKlongs _ _ _ (by simp))
  | szUse (sized_descendLte _ _ _))

/-- A node's klongs of the transaction changed in place, or klongs added. -/
macro "szWrite" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (putNode _ _) _ _ _)
  (with_unfolding_none refine sized_putNode _ _ _ _ _ ?szState ?szInput ?szPost)
  case szState => assumption
  case szInput => first
    | exact SizedNode.setLastDel _ _ _ _ (by assumption) (by assumption)
    | (refine SizedNode.add _ _ _ _ (by assumption) ?_; szArith)
    | exact SizedNode.add_and _ _ _ _ _ (by assumption) (by assumption)
    | (refine SizedNode.lebWrite _ _ _ _ _ _ _ _ _ (by assumption) rfl rfl (by assumption))
    | (refine SizedNode.mergeWrite _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by assumption) rfl rfl (by assumption))
  intro _ _ _))

set_option maxHeartbeats 1000000 in
theorem sized_appendDeleteKlong (x : NodeId) (depth cv : Nat) :
    KeepsSized (appendDeleteKlong x depth cv) := by
  intro c w hv hw
  obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6⟩ := hv.params
  unfold appendDeleteKlong
  repeat' first
    | wpSimplify
    | szWrite
    | szCore
    | szAppend
    | wpSplit
    | split
    | contradiction

set_option maxHeartbeats 1400000 in
theorem sized_emptyKeyNext (x : NodeId) (depth : Nat) : KeepsSized (emptyKeyNext x depth) := by
  intro c w hv hw
  obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6⟩ := hv.params
  unfold emptyKeyNext
  repeat' first
    | wpSimplify
    | szWrite
    | szCore
    | szAppend
    | wpSplit
    | split
    | contradiction

theorem sized_unlink (x : NodeId) : KeepsSized (unlink x) := by
  intro c w hv hw
  unfold unlink
  repeat' first | wpSimplify | szCore | wpSplit | split | contradiction

theorem sized_retarget (q src dst : NodeId) : KeepsSized (retarget q src dst) := by
  intro c w hv hw
  unfold retarget
  repeat' first
    | wpSimplify
    | ((with_unfolding_none guard_target = WriterWP (putNode _ _) _ _ _)
       refine sized_putNode _ _ _ _ _ (by assumption)
         (SizedNode.mapIdx _ _ _ (fun _ _ => rfl) (by assumption)) ?_
       intro _ _ _)
    | szCore
    | wpSplit
    | split
    | contradiction

theorem sized_canTakeBack (x parent : NodeId) (cv : Nat) : KeepsSized (canTakeBack x parent cv) := by
  intro c w hv hw
  unfold canTakeBack
  repeat' first | wpSimplify | szCore | wpSplit | split | contradiction

theorem sized_takeBack (x parent : NodeId) (cv : Nat) : KeepsSized (takeBack x parent cv) := by
  intro c w hv hw
  unfold takeBack
  repeat' first
    | wpSimplify
    | szCore
    | szUse (sized_retarget _ _ _)
    | wpSplit
    | split
    | contradiction

theorem sized_takeBackRoot (x : NodeId) (depth only : Nat) : KeepsSized (takeBackRoot x depth only) := by
  intro c w hv hw
  unfold takeBackRoot
  repeat' first | wpSimplify | szCore | wpSplit | split | contradiction

theorem sized_replaceRoot (x : NodeId) (depth only : Nat) : KeepsSized (replaceRoot x depth only) := by
  intro c w hv hw
  unfold replaceRoot
  repeat' first
    | wpSimplify
    | szCore
    | szAppend
    | szUse (sized_unlink _)
    | wpSplit
    | split
    | contradiction

theorem sized_collapseRoot (key : Key) (segment fuel : Nat) :
    KeepsSized (collapseRoot key segment fuel) := by
  induction fuel with
  | zero => exact sized_throw _
  | succ fuel ih =>
    intro c w hv hw
    unfold collapseRoot
    repeat' first
      | wpSimplify
      | szCore
      | szUse (sized_descendToSegmentRoot _ _)
      | szUse (sized_takeBackRoot _ _ _)
      | szUse (sized_replaceRoot _ _ _)
      | szUse ih
      | wpSplit
      | split
      | contradiction

/-! ## The merges -/

theorem sized_descendHeight (cv h fuel : Nat) (x : NodeId) :
    KeepsSized (descendHeight cv h fuel x) := by
  induction fuel generalizing x with
  | zero => exact sized_throw _
  | succ fuel ih =>
    intro c w hv hw
    unfold descendHeight
    repeat' first
      | wpSimplify
      | szCore
      | szUse (ih _)
      | wpSplit
      | split
      | contradiction

theorem sized_descendToHeight (key : Key) (g h : Nat) : KeepsSized (descendToHeight key g h) := by
  intro c w hv hw
  unfold descendToHeight
  repeat' first
    | wpSimplify
    | szCore
    | szUse (sized_descendToSegmentRoot _ _)
    | szUse (sized_descendHeight _ _ _ _)
    | wpSplit
    | split
    | contradiction

set_option maxHeartbeats 1600000 in
theorem sized_mergeParent (q : NodeId) (depth il cL : Nat) (m1 : NodeId) (ir cR : Nat)
    (m2 : Option (NodeId × Nat)) : KeepsSized (mergeParent q depth il cL m1 ir cR m2) := by
  intro c w hv hw
  obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6⟩ := hv.params
  unfold mergeParent
  repeat' first
    | wpSimplify
    | szWrite
    | szCore
    | szAppend
    | wpSplit
    | split
    | contradiction

end SIS.Tree
