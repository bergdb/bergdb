import SIS.Tree.MergeOpBoundProof

namespace SIS.Tree

open SIS SIS.Check

/-- Preservation of a predicate on the complete writer state. -/
def KeepsStatePred {α : Type} (pred : Ctx → W → Prop) (f : M α) : Prop :=
  ∀ c w, pred c w → WriterWP f c w (fun _ v => pred c v)

/-- Primitive proof obligations for a state predicate. Derived writer
operations are proved below by composition, including all recursive loops. -/
class WriterStateInvariant where
  pred : Ctx → W → Prop
  load : ∀ x, KeepsStatePred pred (getNode x)
  store : ∀ x n, KeepsStatePred pred (putNode x n)
  create : ∀ g h leaf ks, KeepsStatePred pred (newKey g h leaf ks)
  value : ∀ h, KeepsStatePred pred (newValue h)
  allocate : KeepsStatePred pred fresh
  trace : ∀ s, KeepsStatePred pred (note s)
  provenance : ∀ x old, KeepsStatePred pred (setMadeFor x old)
  take : ∀ x, KeepsStatePred pred (takenBack x)
  clear : KeepsStatePred pred pathClear
  path : ∀ cv x, KeepsStatePred pred (pathAdd cv x)
  top : ∀ x, KeepsStatePred pred (newSuperRoot x)
  mergeCounter : ∀ c w, pred c w → pred c {w with merges := w.merges+1}
  splitCounter : ∀ c w, pred c w → pred c {w with spaceSplits := w.spaceSplits+1}

abbrev KeepsState {α : Type} [inv : WriterStateInvariant] (f : M α) : Prop :=
  KeepsStatePred inv.pred f

variable [inv : WriterStateInvariant]

theorem writerWP_of_state {α : Type} {f : M α} (hf : KeepsState f)
    (c : Ctx) (w : W) (post : α → W → Prop) (hw : inv.pred c w)
    (hp : ∀ r v, inv.pred c v → post r v) : WriterWP f c w post :=
  writerWP_mono (hf c w hw) hp

theorem state_getNode (x : NodeId) : KeepsState (getNode x) := WriterStateInvariant.load x
theorem state_putNode (x : NodeId) (n : KNode) : KeepsState (putNode x n) := WriterStateInvariant.store x n
theorem state_newKey (g h : Nat) (leaf : Bool) (ks : List Klong) :
    KeepsState (newKey g h leaf ks) := WriterStateInvariant.create g h leaf ks
theorem state_newValue (h : Nat) : KeepsState (newValue h) := WriterStateInvariant.value h
theorem state_fresh : KeepsState fresh := WriterStateInvariant.allocate
theorem state_note (s : String) : KeepsState (note s) := WriterStateInvariant.trace s
theorem state_setMadeFor (x : NodeId) (old : Option NodeId) :
    KeepsState (setMadeFor x old) := WriterStateInvariant.provenance x old
theorem state_takenBack (x : NodeId) : KeepsState (takenBack x) := WriterStateInvariant.take x
theorem state_pathClear : KeepsState pathClear := WriterStateInvariant.clear
theorem state_pathAdd (cv : Option Nat) (x : NodeId) :
    KeepsState (pathAdd cv x) := WriterStateInvariant.path cv x
theorem state_newSuperRoot (x : NodeId) : KeepsState (newSuperRoot x) := WriterStateInvariant.top x

macro "siHeld" : tactic => `(tactic| first
  | assumption
  | (apply WriterStateInvariant.mergeCounter; assumption)
  | (apply WriterStateInvariant.splitCounter; assumption))

macro "siUse " h:term : tactic => `(tactic| (
  (with_reducible refine writerWP_of_state $h _ _ _ ?tagState ?tagPost)
  case tagState => siHeld
  intro _ _ _))

macro "siPrimitives" : tactic => `(tactic|
  simp only [writerWP_bind,writerWP_pure,writerWP_read,writerWP_get,
    writerWP_set,writerWP_modify])

macro "siNeutral" : tactic => `(tactic| (
  intro c w hw
  repeat' first
    | simp only [writerWP_bind,writerWP_pure,writerWP_read,writerWP_get,
        writerWP_set,writerWP_modify,ghOf,replacedBy,pathSize,pathNode,
        klongAt,parentAt,findRoot,addKeys]
    | exact writerWP_throw _ _ _ _
    | siUse (state_getNode _)
    | siUse (state_putNode _ _)
    | siUse (state_pathAdd _ _)
    | wpSplit
    | split
    | siHeld
    | contradiction))

theorem state_ghOf (x : NodeId) : KeepsState (ghOf x) := by siNeutral
theorem state_replacedBy (x : NodeId) : KeepsState (replacedBy x) := by siNeutral
theorem state_pathSize : KeepsState pathSize := by siNeutral
theorem state_pathNode (d : Nat) : KeepsState (pathNode d) := by siNeutral
theorem state_klongAt (d : Nat) : KeepsState (klongAt d) := by siNeutral
theorem state_parentAt (d : Nat) : KeepsState (parentAt d) := by siNeutral
theorem state_findRoot : KeepsState findRoot := by siNeutral
theorem state_addKeys (x : NodeId) (ins : List (Nat × NodeId)) :
    KeepsState (addKeys x ins) := by siNeutral

theorem state_foldlM {α β : Type} (xs : List α) (f : β → α → M β) (init : β)
    (hf : ∀ b a, KeepsState (f b a)) : KeepsState (xs.foldlM f init) := by
  induction xs generalizing init with
  | nil => intro c w hw; simpa only [List.foldlM_nil, writerWP_pure] using hw
  | cons a xs ih =>
    intro c w hw
    rw [List.foldlM_cons, writerWP_bind]
    exact writerWP_mono (hf init a c w hw) (fun b v hv => ih b c v hv)

theorem state_forIn {α β : Type} (xs : List α) (init : β)
    (f : α → β → M (ForInStep β)) (hf : ∀ a b, KeepsState (f a b)) :
    KeepsState (forIn xs init f) := by
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

macro "siSimplify" : tactic => `(tactic| siPrimitives)

macro "siCore" : tactic => `(tactic| first
  | exact writerWP_throw _ _ _ _
  | siUse (state_getNode _)
  | siUse (state_newKey _ _ _ _)
  | siUse (state_note _)
  | siUse (state_fresh)
  | siUse (state_putNode _ _)
  | siUse (state_ghOf _)
  | siUse (state_newValue _)
  | siUse (state_setMadeFor _ _)
  | siUse (state_replacedBy _)
  | siUse (state_takenBack _)
  | siUse (state_pathClear)
  | siUse (state_pathAdd _ _)
  | siUse (state_pathSize)
  | siUse (state_pathNode _)
  | siUse (state_klongAt _)
  | siUse (state_parentAt _)
  | siUse (state_newSuperRoot _)
  | siUse (state_findRoot)
  | siUse (state_addKeys _ _)
  | siHeld)

macro "siFoldWith " extra:tactic : tactic => `(tactic| (
  (with_reducible refine writerWP_of_state (state_foldlM _ _ _ ?tagBody) _ _ _ ?tagState ?tagPost)
  case tagBody =>
    intro b a c w hw
    repeat' first
      | siSimplify
      | siCore
      | ($extra:tactic)
      | wpSplit
      | split
      | contradiction
  case tagState => siHeld
  intro _ _ _))

macro "siFold" : tactic => `(tactic| siFoldWith fail)

theorem state_replaceOrAdd (last : KNode) (ins : List (Nat × NodeId)) :
    KeepsState (replaceOrAdd last ins) := by
  intro c w hw
  unfold replaceOrAdd
  repeat' first
    | siSimplify
    | siCore
    | siFold
    | wpSplit
    | split
    | contradiction

theorem state_handleFullWith_compact (up : NodeId → List (Nat × NodeId) → M Unit)
    (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) (last : KNode) (compact : Bool)
    (hup : ∀ q more, KeepsState (up q more)) :
    KeepsState (handleFullWith up depth x ins last compact) := by
  intro c w hw
  unfold handleFullWith
  repeat' first
    | siSimplify
    | siCore
    | siFold
    | siUse (state_replaceOrAdd _ _)
    | siUse (hup _ _)
    | wpSplit
    | split
    | contradiction

theorem state_handleFullWith (up : NodeId → List (Nat × NodeId) → M Unit)
    (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) (last : KNode)
    (hup : ∀ q more, KeepsState (up q more)) :
    KeepsState (handleFullWith up depth x ins last) := by
  exact state_handleFullWith_compact up depth x ins last false hup

theorem state_throw {α : Type} (e : String) : KeepsState (throw e : M α) := by
  intro c w hw
  exact writerWP_throw _ _ _ _

theorem state_appendKlongs (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) :
    KeepsState (appendKlongs depth x ins) := by
  induction depth generalizing x ins with
  | zero =>
    intro c w hw
    rw [appendKlongs_step_dead]
    repeat' first
      | siSimplify
      | siCore
      | siUse (state_handleFullWith_compact _ _ _ _ _ _ (fun _ _ => state_throw _))
      | wpSplit
      | split
      | contradiction
  | succ depth ih =>
    intro c w hw
    rw [appendKlongs_step_dead]
    repeat' first
      | siSimplify
      | siCore
      | siUse (state_handleFullWith_compact _ _ _ _ _ _ (fun q more => ih q more))
      | wpSplit
      | split
      | contradiction

theorem state_handleFull_compact (depth : Nat) (x : NodeId) (last : KNode) (compact : Bool) :
    KeepsState (handleFull depth x last compact) := by
  unfold handleFull
  refine state_handleFullWith_compact _ _ _ _ _ _ ?_
  intro q more
  cases depth with
  | zero => exact state_throw _
  | succ d => exact state_appendKlongs _ _ _

theorem state_handleFull (depth : Nat) (x : NodeId) (last : KNode) :
    KeepsState (handleFull depth x last) := by
  unfold handleFull
  refine state_handleFullWith _ _ _ _ _ ?_
  intro q more
  cases depth with
  | zero => exact state_throw _
  | succ d => exact state_appendKlongs _ _ _

theorem state_descendLte (cv fuel : Nat) (x : NodeId) :
    KeepsState (descendLte cv fuel x) := by
  induction fuel generalizing x with
  | zero => exact state_throw _
  | succ fuel ih =>
    intro c w hw
    unfold descendLte
    repeat' first
      | siSimplify
      | siCore
      | siUse (ih _)
      | wpSplit
      | split
      | contradiction

macro "siAppend" : tactic => `(tactic| first
  | siUse (state_handleFull_compact _ _ _ _)
  | siUse (state_appendKlongs _ _ _)
  | siUse (state_handleFull _ _ _)
  | siUse (state_descendLte _ _ _))

theorem state_descendToSegmentRoot (key : Key) (segment : Nat) :
    KeepsState (descendToSegmentRoot key segment) := by
  intro c w hw
  unfold descendToSegmentRoot
  repeat' first
    | siSimplify
    | siCore
    | siFoldWith siAppend
    | siAppend
    | wpSplit
    | split
    | contradiction

macro "siDeleteSimplify" : tactic => `(tactic|
  simp only [unlink, retarget, canTakeBack, takeBack, takeBackRoot, replaceRoot,
    appendDeleteKlong, emptyKeyNext])

theorem state_appendDeleteKlong (x : NodeId) (depth cv : Nat) : KeepsState (appendDeleteKlong x depth cv) := by
  intro c w hw
  unfold appendDeleteKlong
  repeat' first
    | siSimplify
    | siDeleteSimplify
    | siCore
    | siAppend
    | wpSplit
    | split
    | contradiction

theorem state_emptyKeyNext (x : NodeId) (depth : Nat) : KeepsState (emptyKeyNext x depth) := by
  intro c w hw
  unfold emptyKeyNext
  repeat' first
    | siSimplify
    | siDeleteSimplify
    | siCore
    | siAppend
    | wpSplit
    | split
    | contradiction

theorem state_collapseRoot (key : Key) (segment fuel : Nat) :
    KeepsState (collapseRoot key segment fuel) := by
  induction fuel with
  | zero => exact state_throw _
  | succ fuel ih =>
    intro c w hw
    unfold collapseRoot
    repeat' first
      | siSimplify
      | siDeleteSimplify
      | siCore
      | siAppend
      | siUse (state_descendToSegmentRoot _ _)
      | siUse ih
      | wpSplit
      | split
      | contradiction

theorem state_descendHeight (cv h fuel : Nat) (x : NodeId) :
    KeepsState (descendHeight cv h fuel x) := by
  induction fuel generalizing x with
  | zero => exact state_throw _
  | succ fuel ih =>
    intro c w hw
    unfold descendHeight
    repeat' first
      | siSimplify
      | siCore
      | siUse (ih _)
      | wpSplit
      | split
      | contradiction

theorem state_descendToHeight (key : Key) (g h : Nat) :
    KeepsState (descendToHeight key g h) := by
  intro c w hw
  unfold descendToHeight
  repeat' first
    | siSimplify
    | siCore
    | siUse (state_descendToSegmentRoot _ _)
    | siUse (state_descendHeight _ _ _ _)
    | wpSplit
    | split
    | contradiction

set_option maxHeartbeats 800000 in
theorem state_mergeParent (q : NodeId) (depth il cL : Nat) (m1 : NodeId) (ir cR : Nat)
    (m2 : Option (NodeId × Nat)) :
    KeepsState (mergeParent q depth il cL m1 ir cR m2) := by
  intro c w hw
  unfold mergeParent
  repeat' first
    | siSimplify
    | siCore
    | siAppend
    | wpSplit
    | split
    | contradiction

theorem state_unlink (x : NodeId) : KeepsState (unlink x) := by
  intro c w hw
  unfold unlink
  repeat' first
    | siSimplify
    | siCore
    | wpSplit
    | split
    | contradiction

theorem state_retarget (q src dst : NodeId) : KeepsState (retarget q src dst) := by
  intro c w hw
  unfold retarget
  repeat' first
    | siSimplify
    | siCore
    | wpSplit
    | split
    | contradiction

theorem state_sibling (q : NodeId) (pn : KNode) (i : Nat) (inner : Bool) : KeepsState (sibling q pn i inner) := by
  intro c w hw
  unfold sibling
  repeat' first
    | siSimplify
    | siCore
    | wpSplit
    | split
    | contradiction

set_option maxHeartbeats 800000 in
theorem state_merge (x : NodeId) (d : Nat) : KeepsState (merge x d) := by
  intro c w hw
  unfold merge
  repeat' first
    | siSimplify
    | simp only [List.forIn_cons, List.forIn_nil]
    | siCore
    | siUse (state_unlink _)
    | siUse (state_retarget _ _ _)
    | siUse (state_sibling _ _ _ _)
    | siUse (state_mergeParent _ _ _ _ _ _ _ _)
    | wpSplit
    | split
    | contradiction

theorem state_mergeUp (key : Key) (g fuel h : Nat) (merged : Bool) :
    KeepsState (mergeUp key g fuel h merged) := by
  induction fuel generalizing h merged with
  | zero => exact state_throw _
  | succ fuel ih =>
    intro c w hw
    unfold mergeUp
    repeat' first
      | siSimplify
      | siCore
      | siUse (state_descendToHeight _ _ _)
      | siUse (state_merge _ _)
      | siUse (ih _ _)
      | wpSplit
      | split
      | contradiction

theorem state_climb (depth : Nat) : KeepsState (climb depth) := by
  induction depth with
  | zero =>
    intro c w hw
    unfold climb
    repeat' first
      | siSimplify
      | siCore
      | wpSplit
      | split
      | contradiction
  | succ depth ih =>
    intro c w hw
    unfold climb
    repeat' first
      | siSimplify
      | siDeleteSimplify
      | siCore
      | siUse ih
      | wpSplit
      | split
      | contradiction

macro "siForWith " extra:tactic : tactic => `(tactic| (
  (with_reducible refine writerWP_of_state (state_forIn _ _ _ ?tagBody) _ _ _ ?tagState ?tagPost)
  case tagBody =>
    intro a b c w hw
    repeat' first
      | siSimplify
      | siDeleteSimplify
      | siCore
      | ($extra:tactic)
      | wpSplit
      | split
      | contradiction
  case tagState => siHeld
  intro _ _ _))

theorem state_deleteUpward (leaf : NodeId) (depth cv : Nat) (key : Key) :
    KeepsState (deleteUpward leaf depth cv key) := by
  intro c w hw
  unfold deleteUpward afterDelete
  repeat' first
    | siSimplify
    | siDeleteSimplify
    | siCore
    | siAppend
    | siFold
    | siForWith siAppend
    | siUse (state_climb _)
    | siUse (state_mergeUp _ _ _ _ _)
    | siUse (state_collapseRoot _ _ _)
    | wpSplit
    | split
    | contradiction

theorem state_setValue (segRoot : NodeId) (cv : Nat) (key : Key) (value : Option Nat) :
    KeepsState (setValue segRoot cv key value) := by
  intro c w hw
  unfold setValue
  repeat' first
    | siSimplify
    | siCore
    | siAppend
    | siUse (state_deleteUpward _ _ _ _)
    | wpSplit
    | split
    | contradiction

theorem state_setNode (segRoot : NodeId) (cv : Nat) (create : Bool) :
    KeepsState (setNode segRoot cv create) := by
  intro c w hw
  unfold setNode
  repeat' first
    | siSimplify
    | siCore
    | siAppend
    | wpSplit
    | split
    | contradiction

theorem state_putSegs (key : Key) (value : Option Nat) (segs : List Nat) (segRoot : NodeId) :
    KeepsState (putSegs key value segs segRoot) := by
  induction segs generalizing segRoot with
  | nil => exact state_throw _
  | cons cv rest ih =>
    cases rest with
    | nil => exact state_setValue _ _ _ _
    | cons cv2 rest =>
      intro c w hw
      unfold putSegs
      repeat' first
        | siSimplify
        | siCore
        | siUse (state_setNode _ _ _)
        | siUse (ih _)
        | wpSplit
        | split
        | contradiction

theorem state_putKv (op : Tree.Op) : KeepsState (putKv op) := by
  intro c w hw
  unfold putKv
  repeat' first
    | siSimplify
    | siCore
    | siUse (state_putSegs _ _ _ _)
    | wpSplit
    | split
    | contradiction

theorem state_ops (ops : List Tree.Op) : KeepsState (ops.mapM putKv) := by
  induction ops with
  | nil => intro c w hw; simpa only [List.mapM_nil, writerWP_pure] using hw
  | cons op ops ih =>
    intro c w hw
    rw [List.mapM_cons, writerWP_bind]
    refine writerWP_mono (state_putKv op c w hw) ?_
    intro noop v hv
    simpa only [writerWP_bind, writerWP_pure] using ih c v hv

end SIS.Tree
