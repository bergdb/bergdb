import SIS.Tree.MergeFrameDead

namespace SIS.Tree

open SIS SIS.Check

/-- A predicate on the fields that record key nodes and their bounds. -/
def KeepsFieldPred {α : Type}
    (pred : Params → List (NodeId × Nat × Nat) → List (NodeId × Nat × Nat) → Prop)
    (f : M α) : Prop :=
  ∀ c w, pred c.p w.gh w.outside →
    WriterWP f c w (fun _ v => pred c.p v.gh v.outside)

/-- The two actions that extend the cached heights. All other updates keep
these fields or are built from these actions. -/
class WriterFieldsInvariant where
  pred : Params → List (NodeId × Nat × Nat) → List (NodeId × Nat × Nat) → Prop
  load : ∀ x, KeepsFieldPred pred (getNode x)
  create : ∀ g h leaf ks, KeepsFieldPred pred (newKey g h leaf ks)

abbrev KeepsFields {α : Type} [inv : WriterFieldsInvariant] (f : M α) : Prop :=
  KeepsFieldPred inv.pred f

variable [inv : WriterFieldsInvariant]

theorem writerWP_of_fields {α : Type} {f : M α}
    (hf : KeepsFields f) (c : Ctx) (w : W) (post : α → W → Prop)
    (hw : inv.pred c.p w.gh w.outside)
    (hp : ∀ r v, inv.pred c.p v.gh v.outside → post r v) : WriterWP f c w post := by
  exact writerWP_mono (hf c w hw) hp

theorem fields_getNode (x : NodeId) : KeepsFields (getNode x) :=
  WriterFieldsInvariant.load x

theorem fields_newKey (g h : Nat) (leaf : Bool) (ks : List Klong) :
    KeepsFields (newKey g h leaf ks) := WriterFieldsInvariant.create g h leaf ks

theorem fields_foldlM {α β : Type} (xs : List α) (f : β → α → M β) (init : β)
    (hf : ∀ b a, KeepsFields (f b a)) : KeepsFields (xs.foldlM f init) := by
  induction xs generalizing init with
  | nil => intro c w hw; simpa only [List.foldlM_nil, writerWP_pure] using hw
  | cons a xs ih =>
    intro c w hw
    rw [List.foldlM_cons, writerWP_bind]
    exact writerWP_mono (hf init a c w hw) (fun b v hv => ih b c v hv)

theorem fields_forIn {α β : Type} (xs : List α) (init : β)
    (f : α → β → M (ForInStep β)) (hf : ∀ a b, KeepsFields (f a b)) :
    KeepsFields (forIn xs init f) := by
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

macro "fiUse " h:term : tactic => `(tactic| (
  (with_reducible refine writerWP_of_fields $h _ _ _ ?tagState ?tagPost)
  case tagState => assumption
  intro _ _ _))

macro "fiPrimitives" : tactic => `(tactic|
  simp only [writerWP_bind, writerWP_pure, writerWP_read, writerWP_get,
    writerWP_set, writerWP_modify])

macro "fiNeutral" : tactic => `(tactic| (
  intro c w hw
  repeat' first
    | simp only [writerWP_bind, writerWP_pure, writerWP_read, writerWP_get,
        writerWP_set, writerWP_modify, note, fresh, putNode, ghOf, newValue,
        setMadeFor, replacedBy, takenBack, pathClear, pathAdd, pathSize, pathNode,
        klongAt, parentAt, newSuperRoot, findRoot, addKeys, replaceOrAdd]
    | exact writerWP_throw _ _ _ _
    | fiUse (fields_getNode _)
    | wpSplit
    | split
    | assumption
    | contradiction))

theorem fields_note (s : String) : KeepsFields (note s) := by fiNeutral

theorem fields_fresh  : KeepsFields (fresh) := by fiNeutral

theorem fields_putNode (x : NodeId) (n : KNode) : KeepsFields (putNode x n) := by fiNeutral

theorem fields_ghOf (x : NodeId) : KeepsFields (ghOf x) := by fiNeutral

theorem fields_newValue (h : Nat) : KeepsFields (newValue h) := by fiNeutral

theorem fields_setMadeFor (x : NodeId) (old : Option NodeId) : KeepsFields (setMadeFor x old) := by fiNeutral

theorem fields_replacedBy (x : NodeId) : KeepsFields (replacedBy x) := by fiNeutral

theorem fields_takenBack (x : NodeId) : KeepsFields (takenBack x) := by fiNeutral

theorem fields_pathClear  : KeepsFields (pathClear) := by fiNeutral

theorem fields_pathAdd (a : Option Nat) (x : NodeId) : KeepsFields (pathAdd a x) := by fiNeutral

theorem fields_pathSize  : KeepsFields (pathSize) := by fiNeutral

theorem fields_pathNode (d : Nat) : KeepsFields (pathNode d) := by fiNeutral

theorem fields_klongAt (d : Nat) : KeepsFields (klongAt d) := by fiNeutral

theorem fields_parentAt (d : Nat) : KeepsFields (parentAt d) := by fiNeutral

theorem fields_newSuperRoot (x : NodeId) : KeepsFields (newSuperRoot x) := by fiNeutral

theorem fields_findRoot  : KeepsFields (findRoot) := by fiNeutral

theorem fields_addKeys (x : NodeId) (ins : List (Nat × NodeId)) : KeepsFields (addKeys x ins) := by fiNeutral

macro "fiSimplify" : tactic => `(tactic| fiPrimitives)

macro "fiCore" : tactic => `(tactic| first
  | exact writerWP_throw _ _ _ _
  | fiUse (fields_getNode _)
  | fiUse (fields_newKey _ _ _ _)
  | fiUse (fields_note _)
  | fiUse (fields_fresh)
  | fiUse (fields_putNode _ _)
  | fiUse (fields_ghOf _)
  | fiUse (fields_newValue _)
  | fiUse (fields_setMadeFor _ _)
  | fiUse (fields_replacedBy _)
  | fiUse (fields_takenBack _)
  | fiUse (fields_pathClear)
  | fiUse (fields_pathAdd _ _)
  | fiUse (fields_pathSize)
  | fiUse (fields_pathNode _)
  | fiUse (fields_klongAt _)
  | fiUse (fields_parentAt _)
  | fiUse (fields_newSuperRoot _)
  | fiUse (fields_findRoot)
  | fiUse (fields_addKeys _ _)
  | assumption)

macro "fiFoldWith " extra:tactic : tactic => `(tactic| (
  (with_reducible refine writerWP_of_fields (fields_foldlM _ _ _ ?tagBody) _ _ _ ?tagState ?tagPost)
  case tagBody =>
    intro b a c w hw
    repeat' first
      | fiSimplify
      | fiCore
      | ($extra:tactic)
      | wpSplit
      | split
      | contradiction
  case tagState => assumption
  intro _ _ _))

macro "fiFold" : tactic => `(tactic| fiFoldWith fail)

theorem fields_replaceOrAdd (last : KNode) (ins : List (Nat × NodeId)) :
    KeepsFields (replaceOrAdd last ins) := by
  intro c w hw
  unfold replaceOrAdd
  repeat' first
    | fiSimplify
    | fiCore
    | fiFold
    | wpSplit
    | split
    | contradiction

theorem fields_handleFullWith_compact (up : NodeId → List (Nat × NodeId) → M Unit)
    (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) (last : KNode) (compact : Bool)
    (hup : ∀ q more, KeepsFields (up q more)) :
    KeepsFields (handleFullWith up depth x ins last compact) := by
  intro c w hw
  unfold handleFullWith
  repeat' first
    | fiSimplify
    | fiCore
    | fiFold
    | fiUse (fields_replaceOrAdd _ _)
    | fiUse (hup _ _)
    | wpSplit
    | split
    | contradiction

theorem fields_handleFullWith (up : NodeId → List (Nat × NodeId) → M Unit)
    (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) (last : KNode)
    (hup : ∀ q more, KeepsFields (up q more)) :
    KeepsFields (handleFullWith up depth x ins last) := by
  exact fields_handleFullWith_compact up depth x ins last false hup

theorem fields_throw {α : Type} (e : String) : KeepsFields (throw e : M α) := by
  intro c w hw
  exact writerWP_throw _ _ _ _

theorem fields_appendKlongs (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) :
    KeepsFields (appendKlongs depth x ins) := by
  induction depth generalizing x ins with
  | zero =>
    intro c w hw
    rw [appendKlongs_step_dead]
    repeat' first
      | fiSimplify
      | fiCore
      | fiUse (fields_handleFullWith_compact _ _ _ _ _ _ (fun _ _ => fields_throw _))
      | wpSplit
      | split
      | contradiction
  | succ depth ih =>
    intro c w hw
    rw [appendKlongs_step_dead]
    repeat' first
      | fiSimplify
      | fiCore
      | fiUse (fields_handleFullWith_compact _ _ _ _ _ _ (fun q more => ih q more))
      | wpSplit
      | split
      | contradiction

theorem fields_handleFull_compact (depth : Nat) (x : NodeId) (last : KNode) (compact : Bool) :
    KeepsFields (handleFull depth x last compact) := by
  unfold handleFull
  refine fields_handleFullWith_compact _ _ _ _ _ _ ?_
  intro q more
  cases depth with
  | zero => exact fields_throw _
  | succ d => exact fields_appendKlongs _ _ _

theorem fields_handleFull (depth : Nat) (x : NodeId) (last : KNode) :
    KeepsFields (handleFull depth x last) := by
  unfold handleFull
  refine fields_handleFullWith _ _ _ _ _ ?_
  intro q more
  cases depth with
  | zero => exact fields_throw _
  | succ d => exact fields_appendKlongs _ _ _

theorem fields_descendLte (cv fuel : Nat) (x : NodeId) :
    KeepsFields (descendLte cv fuel x) := by
  induction fuel generalizing x with
  | zero => exact fields_throw _
  | succ fuel ih =>
    intro c w hw
    unfold descendLte
    repeat' first
      | fiSimplify
      | fiCore
      | fiUse (ih _)
      | wpSplit
      | split
      | contradiction

macro "fiAppend" : tactic => `(tactic| first
  | fiUse (fields_handleFull_compact _ _ _ _)
  | fiUse (fields_appendKlongs _ _ _)
  | fiUse (fields_handleFull _ _ _)
  | fiUse (fields_descendLte _ _ _))

theorem fields_descendToSegmentRoot (key : Key) (segment : Nat) :
    KeepsFields (descendToSegmentRoot key segment) := by
  intro c w hw
  unfold descendToSegmentRoot
  repeat' first
    | fiSimplify
    | fiCore
    | fiFoldWith fiAppend
    | fiAppend
    | wpSplit
    | split
    | contradiction

macro "fiDeleteSimplify" : tactic => `(tactic|
  simp only [unlink, retarget, canTakeBack, takeBack, takeBackRoot, replaceRoot,
    appendDeleteKlong, emptyKeyNext])

theorem fields_appendDeleteKlong (x : NodeId) (depth cv : Nat) : KeepsFields (appendDeleteKlong x depth cv) := by
  intro c w hw
  unfold appendDeleteKlong
  repeat' first
    | fiSimplify
    | fiDeleteSimplify
    | fiCore
    | fiAppend
    | wpSplit
    | split
    | contradiction

theorem fields_emptyKeyNext (x : NodeId) (depth : Nat) : KeepsFields (emptyKeyNext x depth) := by
  intro c w hw
  unfold emptyKeyNext
  repeat' first
    | fiSimplify
    | fiDeleteSimplify
    | fiCore
    | fiAppend
    | wpSplit
    | split
    | contradiction

theorem fields_collapseRoot (key : Key) (segment fuel : Nat) :
    KeepsFields (collapseRoot key segment fuel) := by
  induction fuel with
  | zero => exact fields_throw _
  | succ fuel ih =>
    intro c w hw
    unfold collapseRoot
    repeat' first
      | fiSimplify
      | fiDeleteSimplify
      | fiCore
      | fiAppend
      | fiUse (fields_descendToSegmentRoot _ _)
      | fiUse ih
      | wpSplit
      | split
      | contradiction

theorem fields_descendHeight (cv h fuel : Nat) (x : NodeId) :
    KeepsFields (descendHeight cv h fuel x) := by
  induction fuel generalizing x with
  | zero => exact fields_throw _
  | succ fuel ih =>
    intro c w hw
    unfold descendHeight
    repeat' first
      | fiSimplify
      | fiCore
      | fiUse (ih _)
      | wpSplit
      | split
      | contradiction

theorem fields_descendToHeight (key : Key) (g h : Nat) :
    KeepsFields (descendToHeight key g h) := by
  intro c w hw
  unfold descendToHeight
  repeat' first
    | fiSimplify
    | fiCore
    | fiUse (fields_descendToSegmentRoot _ _)
    | fiUse (fields_descendHeight _ _ _ _)
    | wpSplit
    | split
    | contradiction

set_option maxHeartbeats 800000 in
theorem fields_mergeParent (q : NodeId) (depth il cL : Nat) (m1 : NodeId) (ir cR : Nat)
    (m2 : Option (NodeId × Nat)) :
    KeepsFields (mergeParent q depth il cL m1 ir cR m2) := by
  intro c w hw
  unfold mergeParent
  repeat' first
    | fiSimplify
    | fiCore
    | fiAppend
    | wpSplit
    | split
    | contradiction

theorem fields_unlink (x : NodeId) : KeepsFields (unlink x) := by
  intro c w hw
  unfold unlink
  repeat' first
    | fiSimplify
    | fiCore
    | wpSplit
    | split
    | contradiction

theorem fields_retarget (q src dst : NodeId) : KeepsFields (retarget q src dst) := by
  intro c w hw
  unfold retarget
  repeat' first
    | fiSimplify
    | fiCore
    | wpSplit
    | split
    | contradiction

theorem fields_sibling (q : NodeId) (pn : KNode) (i : Nat) (inner : Bool) : KeepsFields (sibling q pn i inner) := by
  intro c w hw
  unfold sibling
  repeat' first
    | fiSimplify
    | fiCore
    | wpSplit
    | split
    | contradiction

set_option maxHeartbeats 800000 in
theorem fields_merge (x : NodeId) (d : Nat) : KeepsFields (merge x d) := by
  intro c w hw
  unfold merge
  repeat' first
    | fiSimplify
    | simp only [List.forIn_cons, List.forIn_nil]
    | fiCore
    | fiUse (fields_unlink _)
    | fiUse (fields_retarget _ _ _)
    | fiUse (fields_sibling _ _ _ _)
    | fiUse (fields_mergeParent _ _ _ _ _ _ _ _)
    | wpSplit
    | split
    | contradiction

theorem fields_mergeUp (key : Key) (g fuel h : Nat) (merged : Bool) :
    KeepsFields (mergeUp key g fuel h merged) := by
  induction fuel generalizing h merged with
  | zero => exact fields_throw _
  | succ fuel ih =>
    intro c w hw
    unfold mergeUp
    repeat' first
      | fiSimplify
      | fiCore
      | fiUse (fields_descendToHeight _ _ _)
      | fiUse (fields_merge _ _)
      | fiUse (ih _ _)
      | wpSplit
      | split
      | contradiction

theorem fields_afterDelete (key : Key) (g h : Nat) : KeepsFields (afterDelete key g h) := by
  intro c w hw
  unfold afterDelete
  repeat' first
    | fiSimplify
    | fiCore
    | fiUse (fields_mergeUp _ _ _ _ _)
    | fiUse (fields_collapseRoot _ _ _)
    | wpSplit
    | split
    | contradiction

theorem fields_climb (depth : Nat) : KeepsFields (climb depth) := by
  induction depth with
  | zero =>
    intro c w hw
    unfold climb
    repeat' first
      | fiSimplify
      | fiCore
      | wpSplit
      | split
      | contradiction
  | succ depth ih =>
    intro c w hw
    unfold climb
    repeat' first
      | fiSimplify
      | fiDeleteSimplify
      | fiCore
      | fiUse ih
      | wpSplit
      | split
      | contradiction

macro "fiForWith " extra:tactic : tactic => `(tactic| (
  (with_reducible refine writerWP_of_fields (fields_forIn _ _ _ ?tagBody) _ _ _ ?tagState ?tagPost)
  case tagBody =>
    intro a b c w hw
    repeat' first
      | fiSimplify
      | fiDeleteSimplify
      | fiCore
      | ($extra:tactic)
      | wpSplit
      | split
      | contradiction
  case tagState => assumption
  intro _ _ _))

theorem fields_segmentCount (path : List (Option Nat × NodeId)) (stop : Nat) :
    KeepsFields ((path.take stop).foldlM (fun s e => do
      let n ← getNode e.2
      pure (if n.leaf then s + 1 else s)) 0) := by
  intro c w hw
  fiFold
  assumption

theorem fields_unlinkLoop (depth tt : Nat) (js : List Nat) :
    KeepsFields (forIn js () (fun j _ => do
      let x ← pathNode (depth - j)
      let xn ← getNode x
      if xn.firstTime == some tt then
        let q ← pathNode (depth - j - 1)
        let k ← klongAt (depth - j)
        takeBack x q k
        pure (ForInStep.yield ())
      else
        note "up.unlink"
        unlink x
        pure (ForInStep.yield ()))) := by
  intro c w hw
  fiForWith fiAppend
  assumption

theorem fields_deleteUpward (leaf : NodeId) (depth cv : Nat) (key : Key) :
    KeepsFields (deleteUpward leaf depth cv key) := by
  intro c w hw
  unfold deleteUpward afterDelete
  repeat' first
    | fiSimplify
    | fiDeleteSimplify
    | fiCore
    | fiAppend
    | fiFold
    | fiForWith fiAppend
    | fiUse (fields_climb _)
    | fiUse (fields_mergeUp _ _ _ _ _)
    | fiUse (fields_collapseRoot _ _ _)
    | wpSplit
    | split
    | contradiction

theorem fields_setValue (segRoot : NodeId) (cv : Nat) (key : Key) (value : Option Nat) :
    KeepsFields (setValue segRoot cv key value) := by
  intro c w hw
  unfold setValue
  repeat' first
    | fiSimplify
    | fiCore
    | fiAppend
    | fiUse (fields_deleteUpward _ _ _ _)
    | wpSplit
    | split
    | contradiction

theorem fields_setNode (segRoot : NodeId) (cv : Nat) (create : Bool) :
    KeepsFields (setNode segRoot cv create) := by
  intro c w hw
  unfold setNode
  repeat' first
    | fiSimplify
    | fiCore
    | fiAppend
    | wpSplit
    | split
    | contradiction

theorem fields_putSegs (key : Key) (value : Option Nat) (segs : List Nat) (segRoot : NodeId) :
    KeepsFields (putSegs key value segs segRoot) := by
  induction segs generalizing segRoot with
  | nil => exact fields_throw _
  | cons cv rest ih =>
    cases rest with
    | nil => exact fields_setValue _ _ _ _
    | cons cv2 rest =>
      intro c w hw
      unfold putSegs
      repeat' first
        | fiSimplify
        | fiCore
        | fiUse (fields_setNode _ _ _)
        | fiUse (ih _)
        | wpSplit
        | split
        | contradiction

theorem fields_putKv (op : Tree.Op) : KeepsFields (putKv op) := by
  intro c w hw
  unfold putKv
  repeat' first
    | fiSimplify
    | fiCore
    | fiUse (fields_putSegs _ _ _ _)
    | wpSplit
    | split
    | contradiction

theorem fields_ops (ops : List Tree.Op) : KeepsFields (ops.mapM putKv) := by
  induction ops with
  | nil => intro c w hw; simpa only [List.mapM_nil, writerWP_pure] using hw
  | cons op ops ih =>
    intro c w hw
    rw [List.mapM_cons, writerWP_bind]
    refine writerWP_mono (fields_putKv op c w hw) ?_
    intro noop v hv
    simpa only [writerWP_bind, writerWP_pure] using ih c v hv

end SIS.Tree
