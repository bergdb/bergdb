/-
The tree model (bergdb 024-12, TP7): the nodes taken back are nodes of the
transaction (`TakenAbove`), continued from SIS/Tree/WriterTaken.lean: the
functions that take nodes back. Each takes back only a node whose first time
klong is the transaction's, which for a `Good` node of the overlay is a blank
node, one at or above B (`Blank.ge`). So the walk keeps `CacheGood` with
`TakenAbove`, up to a transaction (`execW_takenAbove`).
-/
import SIS.Tree.WriterTaken
import SIS.Tree.WriterGoodOps

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- f keeps the overlay's nodes `Good` and the nodes taken back at or above B. -/
def KeepsGoodTaken (B : NodeId) {α : Type} (f : M α) : Prop :=
  ∀ c w, ViewGood B c → CacheGood B c w → TakenAbove B w →
    WriterWP f c w (fun _ v => CacheGood B c v ∧ TakenAbove B v)

theorem writerWP_of_goodTaken {α : Type} {B : NodeId} {f : M α} (hf : KeepsGoodTaken B f)
    (c : Ctx) (w : W) (post : α → W → Prop) (hv : ViewGood B c) (hw : CacheGood B c w)
    (ht : TakenAbove B w) (hp : ∀ r v, CacheGood B c v → TakenAbove B v → post r v) :
    WriterWP f c w post :=
  writerWP_mono (hf c w hv hw ht) (fun r v h => hp r v h.1 h.2)

/-- A step that keeps the nodes taken back: its postcondition may assume them
at or above B. -/
theorem writerWP_taken_frame {α : Type} {B : NodeId} {f : M α} {c : Ctx} {w : W}
    {post : α → W → Prop} (ht : TakenAbove B w) (hf : KeepsTaken B f)
    (h : WriterWP f c w (fun r v => TakenAbove B v → post r v)) : WriterWP f c w post :=
  fun r v he => h r v he (hf c w ht r v he)

/-- A node of the overlay that the writer's test finds made by the transaction
is at or above B. -/
theorem taken_ge_of_firstTime {B : NodeId} {c : Ctx} {x : NodeId} {n : KNode}
    (hv : ViewGood B c) (hf : (n.firstTime == some c.i) = true) (h : Good B c x n) : B ≤ x :=
  Blank.ge B c x hv (blank_of_firstTime B c x n hv.pos h hf)

theorem goodTaken_takenBack (B : NodeId) (x : NodeId) (c : Ctx) (w : W)
    (hw : CacheGood B c w) (ht : TakenAbove B w) (hx : B ≤ x) :
    WriterWP (takenBack x) c w (fun _ v => CacheGood B c v ∧ TakenAbove B v) := by
  simp only [takenBack, writerWP_modify]
  refine ⟨hw, ?_⟩
  intro y hy
  rcases List.mem_cons.mp hy with hy | hy
  · subst hy; exact hx
  · exact ht y hy

/-- B ≤ x for a node to take back. -/
macro "tkGe" : tactic => `(tactic| first
  | assumption
  | (apply taken_ge_of_firstTime ‹ViewGood _ _› <;> assumption))

macro "tkTakenBack" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (takenBack _) _ _ _)
  (refine writerWP_mono (goodTaken_takenBack ?gtB _ _ _ ?gtState ?gtTaken ?gtGe) ?gtPost)
  case gtState => assumption
  case gtTaken => assumption
  case gtGe => tkGe
  rintro _ _ ⟨_, _⟩))

/-- A step of the first walk inside the second: the nodes taken back are
kept, and `CacheGood` by the walk of SIS/Tree/WriterGood.lean. -/
macro "tkFr " pat:term " => " h:term : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP $pat _ _ _)
  refine' writerWP_taken_frame ‹TakenAbove _ _› $h ?_))

macro "tkFrame" : tactic => `(tactic| first
  | tkFr (getNode _) => (taken_getNode _ _)
  | tkFr (putNode _ _) => (taken_putNode _ _ _)
  | tkFr (newKey _ _ _ _) => (taken_newKey _ _ _ _ _)
  | tkFr (newValue _) => (taken_newValue _ _)
  | tkFr fresh => (taken_fresh _)
  | tkFr (note _) => (taken_note _ _)
  | tkFr (setMadeFor _ _) => (taken_setMadeFor _ _ _)
  | tkFr (replacedBy _) => (taken_replacedBy _ _)
  | tkFr pathClear => (taken_pathClear _)
  | tkFr (pathAdd _ _) => (taken_pathAdd _ _ _)
  | tkFr pathSize => (taken_pathSize _)
  | tkFr (pathNode _) => (taken_pathNode _ _)
  | tkFr (klongAt _) => (taken_klongAt _ _)
  | tkFr (parentAt _) => (taken_parentAt _ _)
  | tkFr (newSuperRoot _) => (taken_newSuperRoot _ _)
  | tkFr findRoot => (taken_findRoot _)
  | tkFr (ghOf _) => (taken_ghOf _ _)
  | tkFr (addKeys _ _) => (taken_addKeys _ _ _)
  | tkFr (handleFull _ _ _ _) => (taken_handleFull _ _ _ _ _)
  | tkFr (appendKlongs _ _ _) => (taken_appendKlongs _ _ _ _)
  | tkFr (descendLte _ _ _) => (taken_descendLte _ _ _ _)
  | tkFr (descendToSegmentRoot _ _) => (taken_descendToSegmentRoot _ _ _)
  | tkFr (appendDeleteKlong _ _ _) => (taken_appendDeleteKlong _ _ _ _)
  | tkFr (emptyKeyNext _ _) => (taken_emptyKeyNext _ _ _)
  | tkFr (unlink _) => (taken_unlink _ _)
  | tkFr (retarget _ _ _) => (taken_retarget _ _ _ _)
  | tkFr (canTakeBack _ _ _) => (taken_canTakeBack _ _ _ _)
  | tkFr (replaceRoot _ _ _) => (taken_replaceRoot _ _ _ _)
  | tkFr (descendHeight _ _ _ _) => (taken_descendHeight _ _ _ _ _)
  | tkFr (descendToHeight _ _ _) => (taken_descendToHeight _ _ _ _)
  | tkFr (mergeParent _ _ _ _ _ _ _ _) => (taken_mergeParent _ _ _ _ _ _ _ _ _)
  | tkFr (sibling _ _ _ _) => (taken_sibling _ _ _ _ _)
  | tkFr (climb _) => (taken_climb _ _)
  | tkFr (setNode _ _ _) => (taken_setNode _ _ _ _))

macro "tkGood" : tactic => `(tactic| first
  | gdNode
  | gdWrite
  | gdCore
  | gdAppend
  | gdUse (good_unlink _ _)
  | gdUse (good_retarget _ _ _ _)
  | gdUse (good_canTakeBack _ _ _ _)
  | gdUse (good_replaceRoot _ _ _ _)
  | gdUse (good_descendToSegmentRoot _ _ _)
  | gdUse (good_descendHeight _ _ _ _ _)
  | gdUse (good_descendToHeight _ _ _ _)
  | gdUse (good_mergeParent _ _ _ _ _ _ _ _ _)
  | gdUse (good_sibling _ _ _ _ _)
  | gdUse (good_climb _ _)
  | gdUse (good_appendDeleteKlong _ _ _ _)
  | gdUse (good_emptyKeyNext _ _ _)
  | gdUse (good_setNode _ _ _ _))

macro "tkStep" : tactic => `(tactic| (tkFrame; tkGood; intro _))

macro "tkGUse " h:term : tactic => `(tactic| (
  (with_unfolding_none refine' writerWP_of_goodTaken $h _ _ _ ?gtView ?gtState ?gtTaken ?gtPost)
  case gtView => assumption
  case gtState => assumption
  case gtTaken => assumption
  intro _ _ _ _))

macro "tkDone" : tactic => `(tactic| (
  (with_unfolding_none guard_target = (CacheGood _ _ _ ∧ TakenAbove _ _))
  exact ⟨by assumption, by assumption⟩))

/-- `takeBack` of a node at or above B. -/
theorem goodTaken_takeBack (B : NodeId) (x parent : NodeId) (cv : Nat) (c : Ctx) (w : W)
    (hv : ViewGood B c) (hw : CacheGood B c w) (ht : TakenAbove B w) (hx : B ≤ x) :
    WriterWP (takeBack x parent cv) c w (fun _ v => CacheGood B c v ∧ TakenAbove B v) := by
  unfold takeBack
  repeat' first
    | wpSimplify
    | exact writerWP_throw _ _ _ _
    | tkTakenBack
    | tkStep
    | wpSplit
    | split
    | contradiction
    | tkDone

/-- `takeBackRoot` of a node at or above B. -/
theorem goodTaken_takeBackRoot (B : NodeId) (x : NodeId) (depth only : Nat) (c : Ctx) (w : W)
    (hv : ViewGood B c) (hw : CacheGood B c w) (ht : TakenAbove B w) (hx : B ≤ x) :
    WriterWP (takeBackRoot x depth only) c w (fun _ v => CacheGood B c v ∧ TakenAbove B v) := by
  unfold takeBackRoot
  repeat' first
    | wpSimplify
    | exact writerWP_throw _ _ _ _
    | tkTakenBack
    | (refine' writerWP_taken_frame ‹TakenAbove _ _› (taken_putNode _ _ _) ?_
       (with_unfolding_none guard_target = WriterWP (putNode _ (KNode.repoint _ _ _)) _ _ _)
       refine good_putNode B _ _ _ _ _ (by assumption)
         (Good.repointLink B _ _ _ _ _ _ _ hv (by assumption) (by assumption) hx) ?_
       intro _ _ _ _)
    | tkStep
    | wpSplit
    | split
    | contradiction
    | tkDone

theorem goodTaken_collapseRoot (B : NodeId) (key : Key) (segment fuel : Nat) :
    KeepsGoodTaken B (collapseRoot key segment fuel) := by
  induction fuel with
  | zero => intro c w _ _ _; exact writerWP_throw _ _ _ _
  | succ fuel ih =>
    intro c w hv hw ht
    unfold collapseRoot
    repeat' first
      | wpSimplify
      | exact writerWP_throw _ _ _ _
      | ((with_unfolding_none guard_target = WriterWP (takeBackRoot _ _ _) _ _ _)
         refine writerWP_mono (goodTaken_takeBackRoot B _ _ _ _ _ hv (by assumption)
           (by assumption) (by tkGe)) ?_
         rintro _ _ ⟨_, _⟩)
      | tkGUse ih
      | tkStep
      | wpSplit
      | split
      | contradiction
      | tkDone

/-! ## The merges -/

/-- The sibling that `sibling` returns is `Good`. -/
theorem goodTaken_sibling (B : NodeId) (q : NodeId) (pn : KNode) (i : Nat) (inner : Bool)
    (c : Ctx) (w : W) (hv : ViewGood B c) (hw : CacheGood B c w) :
    WriterWP (sibling q pn i inner) c w (fun r v => CacheGood B c v ∧ Good B c r.1 r.2) := by
  unfold sibling
  repeat' first
    | wpSimplify
    | exact writerWP_throw _ _ _ _
    | gdNode
    | wpSplit
    | split
    | contradiction
    | exact ⟨by assumption, by assumption⟩

macro "tkSibling" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (sibling _ _ _ _) _ _ _)
  refine' writerWP_taken_frame ‹TakenAbove _ _› (taken_sibling _ _ _ _ _) ?_
  refine writerWP_mono (goodTaken_sibling ?gtB _ _ _ _ _ _ ?gtView ?gtState) ?gtPost
  case gtView => assumption
  case gtState => assumption
  rintro ⟨_, _⟩ _ ⟨_, hgs⟩ _
  dsimp only at hgs))

macro "tkTakeBack" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (takeBack _ _ _) _ _ _)
  (refine writerWP_mono (goodTaken_takeBack ?gtB _ _ _ _ _ ?gtView ?gtState ?gtTaken ?gtGe) ?gtPost)
  case gtView => assumption
  case gtState => assumption
  case gtTaken => assumption
  case gtGe => tkGe
  rintro _ _ ⟨_, _⟩))

set_option maxHeartbeats 1600000 in
theorem goodTaken_merge (B : NodeId) (x : NodeId) (d : Nat) : KeepsGoodTaken B (merge x d) := by
  intro c w hv hw ht
  have hpos := hv.pos
  unfold merge
  repeat' first
    | wpSimplify
    | simp only [List.forIn_cons, List.forIn_nil]
    | exact writerWP_throw _ _ _ _
    | tkTakenBack
    | tkSibling
    | tkStep
    | wpSplit
    | split
    | contradiction
    | tkDone

theorem goodTaken_mergeUp (B : NodeId) (key : Key) (g fuel h : Nat) (merged : Bool) :
    KeepsGoodTaken B (mergeUp key g fuel h merged) := by
  induction fuel generalizing h merged with
  | zero => intro c w _ _ _; exact writerWP_throw _ _ _ _
  | succ fuel ih =>
    intro c w hv hw ht
    unfold mergeUp
    repeat' first
      | wpSimplify
      | exact writerWP_throw _ _ _ _
      | tkGUse (goodTaken_merge _ _ _)
      | tkGUse (ih _ _)
      | tkStep
      | wpSplit
      | split
      | contradiction
      | tkDone

theorem goodTaken_afterDelete (B : NodeId) (key : Key) (g h : Nat) :
    KeepsGoodTaken B (afterDelete key g h) := by
  intro c w hv hw ht
  unfold afterDelete
  repeat' first
    | wpSimplify
    | exact writerWP_throw _ _ _ _
    | tkGUse (goodTaken_mergeUp _ _ _ _ _ _)
    | tkGUse (goodTaken_collapseRoot _ _ _ _)
    | tkStep
    | wpSplit
    | split
    | contradiction
    | tkDone

/-! ## The upward unlink, a put, a transaction -/

theorem goodTaken_foldlM (B : NodeId) {α β : Type} (xs : List α) (f : β → α → M β) (init : β)
    (hf : ∀ b a, KeepsGoodTaken B (f b a)) : KeepsGoodTaken B (xs.foldlM f init) := by
  induction xs generalizing init with
  | nil => intro c w hv hw ht; simpa only [List.foldlM_nil, writerWP_pure] using ⟨hw, ht⟩
  | cons a xs ih =>
    intro c w hv hw ht
    rw [List.foldlM_cons, writerWP_bind]
    exact writerWP_mono (hf init a c w hv hw ht) (fun b v hh => ih b c v hv hh.1 hh.2)

/-- A loop at the context c: its body may read the transaction's time (the
writer's test of a node made by the transaction). -/
theorem goodTaken_forIn (B : NodeId) {α β : Type} (xs : List α) (init : β)
    (f : α → β → M (ForInStep β)) (c : Ctx)
    (hf : ∀ a b w, CacheGood B c w → TakenAbove B w →
      WriterWP (f a b) c w (fun _ v => CacheGood B c v ∧ TakenAbove B v))
    (w : W) (hw : CacheGood B c w) (ht : TakenAbove B w) :
    WriterWP (forIn xs init f) c w (fun _ v => CacheGood B c v ∧ TakenAbove B v) := by
  induction xs generalizing init w with
  | nil => simpa only [List.forIn_nil, writerWP_pure] using ⟨hw, ht⟩
  | cons a xs ih =>
    rw [List.forIn_cons, writerWP_bind]
    refine writerWP_mono (hf a init w hw ht) ?_
    intro step v hh
    cases step with
    | done b => simpa only [writerWP_pure] using hh
    | yield b => exact ih b v hh.1 hh.2

macro "tkGFoldWith " extra:tactic : tactic => `(tactic| (
  (with_unfolding_none refine' writerWP_of_goodTaken (goodTaken_foldlM _ _ _ _ ?gtBody) _ _ _ ?gtView ?gtState ?gtTaken ?gtPost)
  case gtBody =>
    intro b a c w hv hw ht
    repeat' first
      | wpSimplify
      | exact writerWP_throw _ _ _ _
      | ($extra:tactic)
      | tkStep
      | wpSplit
      | split
      | contradiction
      | tkDone
  case gtView => assumption
  case gtState => assumption
  case gtTaken => assumption
  intro _ _ _ _))

macro "tkForWith " extra:tactic : tactic => `(tactic| (
  (with_unfolding_none refine writerWP_mono (goodTaken_forIn ?gtB _ _ _ _ ?gtBody _ ?gtState ?gtTaken) ?gtPost)
  case gtBody =>
    intro a b w hw ht
    repeat' first
      | wpSimplify
      | exact writerWP_throw _ _ _ _
      | ($extra:tactic)
      | tkStep
      | wpSplit
      | split
      | contradiction
      | tkDone
  case gtState => assumption
  case gtTaken => assumption
  rintro _ _ ⟨_, _⟩))

set_option maxHeartbeats 1600000 in
theorem goodTaken_deleteUpward (B : NodeId) (leaf : NodeId) (depth cv : Nat) (key : Key) :
    KeepsGoodTaken B (deleteUpward leaf depth cv key) := by
  intro c w hv hw ht
  unfold deleteUpward
  repeat' first
    | wpSimplify
    | exact writerWP_throw _ _ _ _
    | tkGUse (goodTaken_afterDelete _ _ _ _)
    | tkGUse (goodTaken_mergeUp _ _ _ _ _ _)
    | tkGUse (goodTaken_collapseRoot _ _ _ _)
    | tkGFoldWith fail
    | tkForWith tkTakeBack
    | tkStep
    | wpSplit
    | split
    | contradiction
    | tkDone

theorem goodTaken_setValue (B : NodeId) (segRoot : NodeId) (cv : Nat) (key : Key)
    (value : Option Nat) : KeepsGoodTaken B (setValue segRoot cv key value) := by
  intro c w hv hw ht
  have hpos := hv.pos
  unfold setValue
  repeat' first
    | wpSimplify
    | exact writerWP_throw _ _ _ _
    | tkGUse (goodTaken_deleteUpward _ _ _ _ _)
    | tkStep
    | wpSplit
    | split
    | contradiction
    | tkDone

theorem goodTaken_putSegs (B : NodeId) (key : Key) (value : Option Nat) (segs : List Nat)
    (segRoot : NodeId) : KeepsGoodTaken B (putSegs key value segs segRoot) := by
  induction segs generalizing segRoot with
  | nil => intro c w _ _ _; exact writerWP_throw _ _ _ _
  | cons cv rest ih =>
    cases rest with
    | nil => exact goodTaken_setValue B _ _ _ _
    | cons cv2 rest =>
      intro c w hv hw ht
      unfold putSegs
      repeat' first
        | wpSimplify
        | exact writerWP_throw _ _ _ _
        | tkGUse (ih _)
        | tkStep
        | wpSplit
        | split
        | contradiction
        | tkDone

theorem goodTaken_putKv (B : NodeId) (op : Op) : KeepsGoodTaken B (putKv op) := by
  cases op <;> (intro c w hv hw ht; unfold putKv)
  all_goals
    repeat' first
      | wpSimplify
      | exact writerWP_throw _ _ _ _
      | tkGUse (goodTaken_putSegs _ _ _ _ _)
      | tkStep
      | wpSplit
      | split
      | contradiction
      | tkDone

theorem goodTaken_ops (B : NodeId) (ops : List Op) : KeepsGoodTaken B (ops.mapM putKv) := by
  induction ops with
  | nil => intro c w hv hw ht; simpa only [List.mapM_nil, writerWP_pure] using ⟨hw, ht⟩
  | cons op ops ih =>
    intro c w hv hw ht
    rw [List.mapM_cons, writerWP_bind]
    refine writerWP_mono (goodTaken_putKv B op c w hv hw ht) ?_
    intro noop v hh
    have hi := ih c v hv hh.1 hh.2
    simpa only [writerWP_bind, writerWP_pure] using hi

/-- TP7's `TakenAbove`: every node that a successful transaction of the
writer takes back is one of the transaction's, at or above its first id. -/
theorem execW_takenAbove (p : Params) (tx : Tx) (i : Time) (v : View BVal) (bs : List Bool) (w : W)
    (hv : ViewGood tx.base { p := p, i := i, view := rootless v })
    (he : execW p tx i v = .ok (bs, w)) : TakenAbove tx.base w := by
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
      exact (goodTaken_ops tx.base tx.ops { p := p, i := i, view := rootless v }
        { next := tx.base, top := top } hv
        ⟨Nat.le_refl _, by intro q hq; cases hq⟩ (by intro q hq; cases hq) bs w hr).2

end SIS.Tree
