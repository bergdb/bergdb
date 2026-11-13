/-
The tree model (bergdb 024-12, TP7): the empty key in every inner node of the
writer's overlay at a transaction's end (`execW_leftOK`), continued from
SIS/Tree/WriterLeftMerge.lean: the merges after a delete, the upward unlink,
a put, a transaction.
-/
import SIS.Tree.WriterLeftMerge

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## Facts read at an earlier state -/

theorem left_ne_of_bne {a b : Nat} (h : (a != b) = true) : a ≠ b := by
  simpa using h

theorem left_leaf_false {P : Prop} {n : KNode} (h : n.leaf = true) : n.leaf = false → P := by
  intro h'
  rw [h] at h'
  cases h'

theorem left_base_read (B : NodeId) (c : Ctx) (x : NodeId) (n : KNode) (hg : Good B c x n)
    (hpos : 0 < c.i) (hr : LeftRead [] x n) (hf : ¬ (n.firstTime == some c.i) = true) :
    n.leaf = false → baseKlongs c.view x ≠ [] :=
  fun h => nex_base B c x n hg hpos (hr.node h).1 hf

/-- The unlink of x, read at an earlier state as inner only if it has klongs in
the view. -/
theorem left_unlink' (B : NodeId) (x : NodeId) (c : Ctx) (w : W) (hv : ViewGood B c)
    (hp : MergeParamsOK c.p) (hl : ViewLeftOK c.p c.view) (hw : CacheGood B c w)
    (hb : Book B c w) (hn : LeftCacheE [] w)
    (hx : ∃ vr n0, vr.nodes.lookup x = some n0 ∧ Kept vr w ∧
      (n0.leaf = false → baseKlongs c.view x ≠ [])) :
    WriterWP (unlink x) c w (fun _ v => CacheGood B c v ∧ Book B c v ∧ Kept w v ∧
      LeftCacheE [] v) := by
  obtain ⟨vr, n0, hl0, hk0, hh0⟩ := hx
  obtain ⟨n1, hl1, hle⟩ := hk0.lookup hl0
  by_cases hlf : n1.leaf = true
  · exact left_unlink B x c w hv hp hl hw hb hn (Or.inr ⟨n1, hl1, hlf⟩)
  · have h0 : n0.leaf = false := by
      rw [← hle]; simpa using hlf
    exact left_unlink B x c w hv hp hl hw hb hn (Or.inl (hh0 h0))

/-- The delete's bitmap in x, read at an earlier state as a leaf or with a
compare value that is not the empty key's. -/
theorem left_appendDeleteKlong' (B : NodeId) (x : NodeId) (depth cv : Nat) (c : Ctx) (w : W)
    (hv : ViewGood B c) (hp : MergeParamsOK c.p) (hl : ViewLeftOK c.p c.view)
    (hw : CacheGood B c w) (hb : Book B c w) (hn : LeftCacheE [] w)
    (hx : ∃ vr n0, vr.nodes.lookup x = some n0 ∧ Kept vr w ∧ (n0.leaf = false → cv ≠ 0)) :
    WriterWP (appendDeleteKlong x depth cv) c w (fun _ v => CacheGood B c v ∧ Book B c v ∧
      Kept w v ∧ LeftCacheE [] v) := by
  obtain ⟨vr, n0, hl0, hk0, hh0⟩ := hx
  obtain ⟨n1, hl1, hle⟩ := hk0.lookup hl0
  exact left_appendDeleteKlong B x depth cv c w hv hp hl hw hb hn
    ⟨n1, hl1, fun h => hh0 (by rw [← hle]; exact h)⟩

macro "lfADK" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (appendDeleteKlong _ _ _) _ _ _)
  (refine writerWP_mono (left_appendDeleteKlong' ?gdB _ _ _ _ _ ?gdView ?lfP ?lfView ?gdState ?bkState ?lfState ?lfX) ?gdPost)
  case gdView => assumption
  case lfP => assumption
  case lfView => assumption
  case gdState => assumption
  case bkState => bkState
  case lfState => lfState
  case lfX => first
    | exact ⟨_, _, by assumption, by bkChain, left_leaf_false (by assumption)⟩
    | exact ⟨_, _, by assumption, by bkChain, fun _ => left_ne_of_bne (by assumption)⟩
  rintro _ _ ⟨_, _, _, _⟩))

macro "lfUnlinkR" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (unlink _) _ _ _)
  (refine writerWP_mono (left_unlink' ?gdB _ _ _ ?gdView ?lfP ?lfView ?gdState ?bkState ?lfState ?lfX) ?gdPost)
  case gdView => assumption
  case lfP => assumption
  case lfView => assumption
  case gdState => assumption
  case bkState => bkState
  case lfState => lfState
  case lfX => exact ⟨_, _, by assumption, by bkChain, left_base_read _ _ _ _ (by assumption) (by assumption) (by assumption) (by assumption)⟩
  rintro _ _ ⟨_, _, _, _⟩))

macro "lfTB" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (takeBack _ _ _) _ _ _)
  (refine writerWP_mono (left_takeBack ?gdB _ _ _ _ _ ?bkVr ?bkN ?gdView ?lfP ?lfView ?gdState ?bkState ?lfState ?bkLook ?bkKept) ?gdPost)
  case gdView => assumption
  case lfP => assumption
  case lfView => assumption
  case gdState => assumption
  case bkState => bkState
  case lfState => lfState
  case bkLook => assumption
  case bkKept => bkChain
  rintro _ _ ⟨_, _, _, _⟩))

/-! ## The merges after a delete -/

theorem left_mergeUp (B : NodeId) (key : Key) (g fuel h : Nat) (merged : Bool) :
    KeepsLeft0 B (mergeUp key g fuel h merged) := by
  induction fuel generalizing h merged with
  | zero => exact (left_throw B _).zero
  | succ fuel ih =>
    intro c w hv hp hl hw hb hn
    unfold mergeUp
    repeat' first
      | wpSimplify
      | lfCore
      | lfUse0 (left_descendToHeight _ _ _ _)
      | lfUse0 (left_merge _ _ _)
      | lfUse0 (ih _ _)
      | wpSplit
      | split
      | contradiction

theorem left_afterDelete (B : NodeId) (key : Key) (g h : Nat) :
    KeepsLeft0 B (afterDelete key g h) := by
  intro c w hv hp hl hw hb hn
  unfold afterDelete
  repeat' first
    | wpSimplify
    | lfCore
    | lfUse0 (left_mergeUp _ _ _ _ _ _)
    | lfUse0 (left_collapseRoot _ _ _ _)
    | wpSplit
    | split
    | contradiction

theorem left_climb (B : NodeId) (depth : Nat) : KeepsLeft0 B (climb depth) := by
  induction depth with
  | zero =>
    intro c w hv hp hl hw hb hn
    unfold climb
    repeat' first | wpSimplify | lfCore | wpSplit | split | contradiction
  | succ depth ih =>
    intro c w hv hp hl hw hb hn
    unfold climb
    repeat' first
      | wpSimplify
      | lfCore
      | lfUse0 (left_canTakeBack _ _ _ _)
      | lfUse0 ih
      | wpSplit
      | split
      | contradiction

theorem left_forIn (B : NodeId) {α β : Type} (xs : List α) (init : β)
    (f : α → β → M (ForInStep β)) (hf : ∀ a b, KeepsLeft0 B (f a b)) :
    KeepsLeft0 B (forIn xs init f) := by
  induction xs generalizing init with
  | nil =>
    intro c w hv hp hl hw hb hn
    simpa only [List.forIn_nil, writerWP_pure] using ⟨hw, hb, Kept.refl w, hn⟩
  | cons a xs ih =>
    intro c w hv hp hl hw hb hn
    rw [List.forIn_cons, writerWP_bind]
    refine writerWP_mono (hf a init c w hv hp hl hw hb hn) ?_
    rintro step v ⟨h1, h2, h3, h4⟩
    cases step with
    | done b => simpa only [writerWP_pure] using ⟨h1, h2, h3, h4⟩
    | yield b =>
      exact writerWP_mono (ih b c v hv hp hl h1 h2 h4)
        (fun r u h => ⟨h.1, h.2.1, h3.trans h.2.2.1, h.2.2.2⟩)

/-- A loop, its body at a fixed context. -/
theorem left_forInC (B : NodeId) {α β : Type} (xs : List α) (init : β)
    (f : α → β → M (ForInStep β)) (c : Ctx) (_hv : ViewGood B c) (_hp : MergeParamsOK c.p)
    (_hl : ViewLeftOK c.p c.view)
    (hf : ∀ a b w, CacheGood B c w → Book B c w → LeftCacheE [] w →
      WriterWP (f a b) c w (fun _ v => CacheGood B c v ∧ Book B c v ∧ Kept w v ∧ LeftCacheE [] v))
    (w : W) (hw : CacheGood B c w) (hb : Book B c w) (hn : LeftCacheE [] w) :
    WriterWP (forIn xs init f) c w
      (fun _ v => CacheGood B c v ∧ Book B c v ∧ Kept w v ∧ LeftCacheE [] v) := by
  induction xs generalizing init w with
  | nil =>
    simpa only [List.forIn_nil, writerWP_pure] using ⟨hw, hb, Kept.refl w, hn⟩
  | cons a xs ih =>
    rw [List.forIn_cons, writerWP_bind]
    refine writerWP_mono (hf a init w hw hb hn) ?_
    rintro step v ⟨h1, h2, h3, h4⟩
    cases step with
    | done b => simpa only [writerWP_pure] using ⟨h1, h2, h3, h4⟩
    | yield b =>
      exact writerWP_mono (ih b v h1 h2 h4)
        (fun r u h => ⟨h.1, h.2.1, h3.trans h.2.2.1, h.2.2.2⟩)

/-! ## The upward unlink -/

macro "lfFold" : tactic => `(tactic| (
  (with_reducible refine writerWP_of_left0 (left_foldlM ?gdB _ _ _ ?lfBody) _ _ _ ?gdView ?lfP ?lfView ?gdState ?bkState ?lfState ?gdPost)
  case gdView => assumption
  case lfP => assumption
  case lfView => assumption
  case gdState => assumption
  case bkState => bkState
  case lfState => lfState
  case lfBody =>
    intro _ _ c w hv hp hl hw hb hn
    repeat' first | wpSimplify | lfCore | wpSplit | split | contradiction
  intro _ _ _ _ _ _))

macro "lfFor" : tactic => `(tactic| (
  (with_reducible refine writerWP_mono (left_forInC ?gdB _ _ _ _ ?gdView ?lfP ?lfView ?lfBody _ ?gdState ?bkState ?lfState) ?gdPost)
  case gdView => assumption
  case lfP => assumption
  case lfView => assumption
  case gdState => assumption
  case bkState => bkState
  case lfState => lfState
  case lfBody =>
    intro _ _ w hw hb hn
    repeat' first
      | wpSimplify
      | lfCore
      | lfTB
      | lfUnlinkR
      | wpSplit
      | split
      | contradiction
  rintro _ _ ⟨_, _, _, _⟩))

set_option maxHeartbeats 3200000 in
/-- The delete in a segment leaf: its bitmaps are in segment leaves or delete a
compare value other than the empty key's; LE-b keeps the empty key live; the
nodes below the stop node are left out as nodes of the view, or taken back. -/
theorem left_deleteUpward (B : NodeId) (leaf : NodeId) (depth cv : Nat) (key : Key) (c : Ctx)
    (w : W) (hv : ViewGood B c) (hp : MergeParamsOK c.p) (hl : ViewLeftOK c.p c.view)
    (hw : CacheGood B c w) (hb : Book B c w) (hn : LeftCacheE [] w)
    (hx : ∃ vr n0, vr.nodes.lookup leaf = some n0 ∧ Kept vr w ∧ n0.leaf = true) :
    WriterWP (deleteUpward leaf depth cv key) c w (fun _ v => CacheGood B c v ∧ Book B c v ∧
      Kept w v ∧ LeftCacheE [] v) := by
  have hpos := hv.pos
  obtain ⟨vr, n0, hl0, hk0, hlf0⟩ := hx
  unfold deleteUpward
  wpSimplify
  refine writerWP_mono (left_getNode B [] leaf c w hv hl hw hb hn) ?_
  rintro n w1 ⟨hc1, hb1, hk1, hn1, hg1, hlk1, hr1⟩
  have hnl : n.leaf = true := by rw [nex_run_kept_leaf (hk0.trans hk1) hl0 hlk1]; exact hlf0
  clear hn
  repeat' first
    | wpSimplify
    | lfCore
    | lfADK
    | lfUse0 (left_afterDelete _ _ _ _)
    | lfUse0 (left_emptyKeyNext _ _ _)
    | lfUse0 (left_climb _ _)
    | lfUse0 (left_mergeUp _ _ _ _ _ _)
    | lfUse0 (left_collapseRoot _ _ _ _)
    | lfFold
    | lfFor
    | wpSplit
    | split
    | contradiction

/-! ## A put, a transaction -/

macro "lfDescL" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (descendLte _ _ _) _ _ _)
  (refine writerWP_mono (left_descendLte ?gdB _ _ _ _ _ ?gdView ?lfP ?lfView ?gdState ?bkState ?lfState) ?gdPost)
  case gdView => assumption
  case lfP => assumption
  case lfView => assumption
  case gdState => assumption
  case bkState => bkState
  case lfState => lfState
  rintro _ _ ⟨_, _, _, _, _, _, _⟩))

macro "lfDU" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (deleteUpward _ _ _ _) _ _ _)
  (refine writerWP_mono (left_deleteUpward ?gdB _ _ _ _ _ _ ?gdView ?lfP ?lfView ?gdState ?bkState ?lfState ?lfX) ?gdPost)
  case gdView => assumption
  case lfP => assumption
  case lfView => assumption
  case gdState => assumption
  case bkState => bkState
  case lfState => lfState
  case lfX => exact ⟨_, _, by assumption, by bkChain, by assumption⟩
  rintro _ _ ⟨_, _, _, _⟩))

theorem left_setValue (B : NodeId) (segRoot : NodeId) (cv : Nat) (key : Key) (value : Option Nat) :
    KeepsLeft0 B (setValue segRoot cv key value) := by
  intro c w hv hp hl hw hb hn
  have hpos := hv.pos
  unfold setValue
  repeat' first
    | wpSimplify
    | lfCore
    | lfDescL
    | lfDU
    | lfUse0 (left_appendKlongs _ _ _ _)
    | wpSplit
    | split
    | contradiction

/-- A new segment leaf without klongs: a leaf, so not pending. -/
theorem left_newKey_leaf (B : NodeId) (E : List NodeId) (g h : Nat) (c : Ctx) (w : W)
    (post : NodeId → W → Prop) (hv : ViewGood B c) (hw : CacheGood B c w) (hb : Book B c w)
    (hn : LeftCacheE E w) (hh : true = (h == 0))
    (hp : ∀ x v, CacheGood B c v → Blank B c x → Book B c v → Kept w v →
      v.nodes.lookup x = some ⟨true, []⟩ → LeftCacheE E v → post x v) :
    WriterWP (newKey g h true []) c w post := by
  refine writerWP_mono (writerWP_and (writerWP_and
    (good_newKey B g h true [] c w _ hv hw (Or.inl rfl) (fun x v hh => hh))
    (book_newKey B g h true [] c w hb hh))
    (left_newKey_only E g h true [] c w hn (left_leaf _ rfl))) ?_
  rintro x v ⟨⟨⟨hc, hbl⟩, hb', hk, hlk⟩, hn'⟩
  exact hp x v hc hbl hb' hk hlk hn'

macro "lfCreateLeaf" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (newKey _ _ true []) _ _ _)
  (refine left_newKey_leaf ?gdB ?lfE _ _ _ _ _ ?gdView ?gdState ?bkState ?lfState ?bkH ?gdPost)
  case gdView => assumption
  case gdState => assumption
  case bkState => bkState
  case lfState => lfState
  case bkH => bkHeight
  intro _ _ _ _ _ _ _ _))

theorem left_setNode (B : NodeId) (segRoot : NodeId) (cv : Nat) (create : Bool) :
    KeepsLeft0 B (setNode segRoot cv create) := by
  intro c w hv hp hl hw hb hn
  have hpos := hv.pos
  unfold setNode
  repeat' first
    | wpSimplify
    | lfCreateLeaf
    | lfCore
    | lfUse0 (left_descendLte0 _ _ _ _)
    | lfUse0 (left_appendKlongs _ _ _ _)
    | wpSplit
    | split
    | contradiction

theorem left_putSegs (B : NodeId) (key : Key) (value : Option Nat) (segs : List Nat)
    (segRoot : NodeId) : KeepsLeft0 B (putSegs key value segs segRoot) := by
  induction segs generalizing segRoot with
  | nil => exact (left_throw B _).zero
  | cons cv rest ih =>
    cases rest with
    | nil => exact left_setValue B _ _ _ _
    | cons cv2 rest =>
      intro c w hv hp hl hw hb hn
      unfold putSegs
      repeat' first
        | wpSimplify
        | lfCore
        | lfUse0 (left_setNode _ _ _ _)
        | lfUse0 (ih _)
        | wpSplit
        | split
        | contradiction

theorem left_putKv (B : NodeId) (op : Op) : KeepsLeft0 B (putKv op) := by
  cases op <;> (intro c w hv hp hl hw hb hn; unfold putKv)
  all_goals
    repeat' first
      | wpSimplify
      | lfCore
      | lfUse0 (left_putSegs _ _ _ _ _)
      | wpSplit
      | split
      | contradiction

theorem left_ops (B : NodeId) (ops : List Op) : KeepsLeft0 B (ops.mapM putKv) := by
  induction ops with
  | nil =>
    intro c w hv hp hl hw hb hn
    simpa only [List.mapM_nil, writerWP_pure] using ⟨hw, hb, Kept.refl w, hn⟩
  | cons op ops ih =>
    intro c w hv hp hl hw hb hn
    rw [List.mapM_cons, writerWP_bind]
    refine writerWP_mono (left_putKv B op c w hv hp hl hw hb hn) ?_
    rintro noop v ⟨h1, h2, h3, h4⟩
    have hi := ih c v hv hp hl h1 h2 h4
    have hi' : WriterWP (ops.mapM putKv) c v (fun r u => WriterWP (pure (noop :: r)) c u
        (fun _ u => CacheGood B c u ∧ Book B c u ∧ Kept w u ∧ LeftCacheE [] u)) :=
      writerWP_mono hi (fun r u h => by
        simp only [writerWP_pure]
        exact ⟨h.1, h.2.1, h3.trans h.2.2.1, h.2.2.2⟩)
    simpa only [writerWP_bind] using hi'

theorem left_viewLeft_rootless (p : Params) (v : View BVal) (h : ViewLeftOK p v) :
    ViewLeftOK p (rootless v) := by
  intro x nd hx hd hl
  unfold rootless at hx
  split at hx
  · cases hx
  · exact h x nd hx hd hl

/-- Every inner node of the writer's overlay has the empty key live at the end
of a successful transaction: a klong of compare value 0 that the node's last
bitmap does not delete. -/
theorem execW_leftOK (p : Params) (tx : Tx) (i : Time) (v : View BVal) (bs : List Bool) (w : W)
    (hp : MergeParamsOK p) (hv : ViewGood tx.base { p := p, i := i, view := rootless v })
    (hl : ViewLeftOK p v) (he : execW p tx i v = .ok (bs, w)) : LeftCache w := by
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
      have hn := (left_ops tx.base tx.ops { p := p, i := i, view := rootless v }
        { next := tx.base, top := top } hv hp (left_viewLeft_rootless p v hl)
        ⟨Nat.le_refl _, by intro q hq; cases hq⟩ (book_start _ _ top)
        (by intro q hq; cases hq) bs w hr).2.2.2
      exact leftCache_of_nil hn

end SIS.Tree
