/-
The tree model (bergdb 024-12, TP7): the empty key in every inner node of the
writer's overlay, continued from SIS/Tree/WriterLeftOps.lean: a full node's
replacement and `appendKlongs`.
-/
import SIS.Tree.WriterLeftOps

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The store of a node's klongs of P@(i-1), for a node read before as inner
only if it has klongs in the view (`h0`, `h1`). -/
macro "lfToPrev " h0:term:max h1:term:max : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (putNode _ (KNode.toPrev _ _)) _ _ _)
  (refine left_putNode_toPrev ?gdB ?lfE _ _ _ _ _ ?gdView ?lfView ?gdState ?bkState ?lfState ?gdG ?lfLook ?lfBase ?gdPost)
  case gdView => assumption
  case lfView => assumption
  case gdState => assumption
  case bkState => bkState
  case lfState => lfState
  case gdG => assumption
  case lfLook => assumption
  case lfBase => exact left_base_of_kept ($h0 (by assumption)) $h1 (by assumption) (by bkChain)
  intro _ _ _ _ _ _))

set_option maxHeartbeats 3200000 in
/-- Every route of a full node's replacement keeps the empty key live in every
inner node: the halves and the time split's last version start with it when
`last` does (which it must for an inner x), the new roots have it, and a node
that existed before the transaction gets its klongs of P@(i-1) back, which
have it. -/
theorem left_handleFullWith (B : NodeId) (up : NodeId → List (Nat × NodeId) → M Unit)
    (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) (last : KNode) (compact : Bool)
    (c : Ctx) (w : W) (hv : ViewGood B c) (hp : MergeParamsOK c.p) (hl : ViewLeftOK c.p c.view)
    (hw : CacheGood B c w) (hb : Book B c w) (hn : LeftCacheE [] w)
    (hlast : FlatAt c.i last.ks)
    (hx : ∃ n0, w.nodes.lookup x = some n0 ∧ (n0.leaf = false → Head0 last.ks))
    (hup : ∀ q more, KeepsLeft0 B (up q more)) :
    WriterWP (handleFullWith up depth x ins last compact) c w
      (fun _ v => CacheGood B c v ∧ Book B c v ∧ Kept w v ∧ LeftCacheE [] v) := by
  have hpos := hv.pos
  obtain ⟨n0, hl0, hH0⟩ := hx
  unfold handleFullWith
  wpSimplify
  refine writerWP_mono (left_getNode B [] x c w hv hl hw hb hn) ?_
  rintro n w1 ⟨hc1, hb1, hk1, hn1, hg1, hlk1, hr1⟩
  have hleaf1 : n.leaf = n0.leaf := nex_run_kept_leaf hk1 hl0 hlk1
  have hH : n.leaf = false → Head0 last.ks := fun h => hH0 (hleaf1 ▸ h)
  have hLN : LeftNode n := hr1.node
  have hbase0 : (!(n.firstTime == some c.i)) = true → n.leaf = false →
      baseKlongs c.view x ≠ [] := by
    intro hf hlf
    exact nex_base B c x n hg1 hpos (hLN hlf).1 (by simpa using hf)
  clear hn
  repeat' first
    | wpSimplify
    | lfToPrev hbase0 hlk1
    | lfReplace
    | lfCore
    | lfUse0 (hup _ _)
    | wpSplit
    | split
    | contradiction

macro "lfFullWith " hup:term:max : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (handleFullWith _ _ _ _ _ _) _ _ _)
  (refine writerWP_mono (left_handleFullWith _ _ _ _ _ _ _ _ _ ?gdView ?lfP ?lfView ?gdState ?bkState ?lfState ?gdLast ?lfX $hup) ?gdPost)
  case gdView => assumption
  case lfP => assumption
  case lfView => assumption
  case gdState => assumption
  case bkState => bkState
  case lfState => lfState
  case gdLast => gdFlat
  case lfX => exact ⟨_, by assumption, fun h => left_head0_lastVersion _ _ ((LeftRead.node (by assumption)) h).2⟩
  rintro _ _ ⟨_, _, _, _⟩))

theorem left_appendKlongs (B : NodeId) (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) :
    KeepsLeft0 B (appendKlongs depth x ins) := by
  induction depth generalizing x ins with
  | zero =>
    intro c w hv hp hl hw hb hn
    rw [appendKlongs_step_dead]
    repeat' first
      | wpSimplify
      | lfNode
      | lfFullWith (fun _ _ => (left_throw B _).zero)
      | lfUse0 (left_addKeys _ _ _)
      | lfClose
      | wpSplit
      | split
  | succ depth ih =>
    intro c w hv hp hl hw hb hn
    rw [appendKlongs_step_dead]
    repeat' first
      | wpSimplify
      | lfNode
      | lfFullWith (fun q more => ih q more)
      | lfUse0 (left_addKeys _ _ _)
      | lfClose
      | wpSplit
      | split

/-- A full node's replacement by a last version at the transaction's time,
which starts with the empty key if the node is inner. -/
theorem left_handleFull (B : NodeId) (depth : Nat) (x : NodeId) (last : KNode) (compact : Bool)
    (c : Ctx) (w : W) (hv : ViewGood B c) (hp : MergeParamsOK c.p) (hl : ViewLeftOK c.p c.view)
    (hw : CacheGood B c w) (hb : Book B c w) (hn : LeftCacheE [] w)
    (hlast : FlatAt c.i last.ks)
    (hx : ∃ vr n0, vr.nodes.lookup x = some n0 ∧ Kept vr w ∧ (n0.leaf = false → Head0 last.ks)) :
    WriterWP (handleFull depth x last compact) c w
      (fun _ v => CacheGood B c v ∧ Book B c v ∧ Kept w v ∧ LeftCacheE [] v) := by
  obtain ⟨vr, n0, hl0, hk0, hh0⟩ := hx
  obtain ⟨n1, hl1, hle⟩ := hk0.lookup hl0
  unfold handleFull
  refine left_handleFullWith B _ depth x [] last compact c w hv hp hl hw hb hn hlast
    ⟨n1, hl1, fun h => hh0 (by rw [← hle]; exact h)⟩ ?_
  intro q more
  cases depth with
  | zero => exact (left_throw B _).zero
  | succ d => exact left_appendKlongs B _ _ _

/-- The descent: the node it stops at is a segment leaf of the overlay. -/
theorem left_descendLte (B : NodeId) (cv fuel : Nat) (x : NodeId) (c : Ctx) (w : W)
    (hv : ViewGood B c) (hp : MergeParamsOK c.p) (hl : ViewLeftOK c.p c.view)
    (hw : CacheGood B c w) (hb : Book B c w) (hn : LeftCacheE [] w) :
    WriterWP (descendLte cv fuel x) c w (fun r v => CacheGood B c v ∧ Book B c v ∧ Kept w v ∧
      LeftCacheE [] v ∧ ∃ n, v.nodes.lookup r = some n ∧ n.leaf = true) := by
  induction fuel generalizing x w with
  | zero => exact writerWP_throw _ _ _ _
  | succ fuel ih =>
    unfold descendLte
    repeat' first
      | wpSimplify
      | lfNode
      | (refine writerWP_mono (ih _ _ ?ihW ?ihB ?ihN) ?ihPost
         case ihW => assumption
         case ihB => bkState
         case ihN => assumption
         rintro _ _ ⟨_, _, _, _, _⟩
         exact ⟨by assumption, by assumption, by bkChain, by assumption, by assumption⟩)
      | (exact ⟨by assumption, by assumption, by bkChain, by assumption, _, by assumption,
          by assumption⟩)
      | lfUse (left_pathAdd _ _ _)
      | exact writerWP_throw _ _ _ _
      | wpSplit
      | split

theorem left_descendLte0 (B : NodeId) (cv fuel : Nat) (x : NodeId) :
    KeepsLeft0 B (descendLte cv fuel x) := by
  intro c w hv hp hl hw hb hn
  exact writerWP_mono (left_descendLte B cv fuel x c w hv hp hl hw hb hn)
    (fun _ _ h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩)

theorem left_foldlM (B : NodeId) {α β : Type} (xs : List α) (f : β → α → M β) (init : β)
    (hf : ∀ b a, KeepsLeft0 B (f b a)) : KeepsLeft0 B (xs.foldlM f init) := by
  induction xs generalizing init with
  | nil =>
    intro c w hv hp hl hw hb hn
    simpa only [List.foldlM_nil, writerWP_pure] using ⟨hw, hb, Kept.refl w, hn⟩
  | cons a xs ih =>
    intro c w hv hp hl hw hb hn
    rw [List.foldlM_cons, writerWP_bind]
    refine writerWP_mono (hf init a c w hv hp hl hw hb hn) ?_
    rintro b v ⟨h1, h2, h3, h4⟩
    exact writerWP_mono (ih b c v hv hp hl h1 h2 h4)
      (fun r u h => ⟨h.1, h.2.1, h3.trans h.2.2.1, h.2.2.2⟩)

theorem left_descendToSegmentRoot (B : NodeId) (key : Key) (segment : Nat) :
    KeepsLeft0 B (descendToSegmentRoot key segment) := by
  intro c w hv hp hl hw hb hn
  unfold descendToSegmentRoot
  wpSimplify
  lfUse (left_pathClear _)
  lfUse (left_findRoot _)
  refine writerWP_of_left0 (left_foldlM B _ _ _ ?_) _ _ _ hv hp hl (by assumption)
    (by assumption) (by assumption) ?_
  · intro node cv c w hv hp hl hw hb hn
    repeat' first
      | wpSimplify
      | lfCore
      | lfUse0 (left_descendLte0 _ _ _ _)
      | wpSplit
      | split
      | contradiction
  · intro _ _ _ _ _ _
    lfClose

end SIS.Tree
