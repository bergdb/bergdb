/-
The tree model (bergdb 024-12, TP7): `appendKlongs` leaves alone an empty
segment leaf y of the overlay that is not the node appended to and not on the
key access path (`AppendFrameOK`, SIS/Tree/OverlayKinds.lean). It stores only
the node appended to, nodes it has just made (ids from `w.next` up, and y is
below `w.next`), and nodes of the key access path (the parents, through the
callback); a read of a node adds it at the end of the overlay; nothing
changes the path. The state of the walk: `frameInv`.
-/
import SIS.Tree.OverlayKinds
import SIS.Tree.WriterBook
import SIS.Tree.WriterSteps
import SIS.Tree.MergeFrameDead

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- y is below the next id, an empty segment leaf of the overlay, and not on
the key access path. -/
def frameInv (y : NodeId) (w : W) : Prop :=
  y < w.next ∧ w.nodes.lookup y = some ⟨true, []⟩ ∧ ∀ e ∈ w.path, e.2 ≠ y

/-- A parent read from the path is not y. -/
def frameNe (y : NodeId) : Option NodeId → Prop
  | some q => q ≠ y
  | none => True

/-- f keeps `frameInv y`. -/
def frameKeeps (y : NodeId) {α : Type} (f : M α) : Prop :=
  ∀ c w, frameInv y w → WriterWP f c w (fun _ v => frameInv y v)

theorem frameInv.of {y : NodeId} {w : W} (h : frameInv y w) (v : W)
    (hn : v.nodes = w.nodes) (hp : v.path = w.path) (hx : w.next ≤ v.next) :
    frameInv y v := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨Nat.lt_of_lt_of_le h1 hx, ?_, ?_⟩
  · rw [hn]; exact h2
  · rw [hp]; exact h3

theorem frame_writerWP {α : Type} {y : NodeId} {f : M α} (hf : frameKeeps y f)
    (c : Ctx) (w : W) (post : α → W → Prop) (hw : frameInv y w)
    (hp : ∀ r v, frameInv y v → post r v) : WriterWP f c w post :=
  writerWP_mono (hf c w hw) (fun r v h => hp r v h)

theorem frame_throw (y : NodeId) {α : Type} (e : String) : frameKeeps y (throw e : M α) := by
  intro c w _
  exact writerWP_throw _ _ _ _

theorem frame_lookup_upsert (ns : List (NodeId × KNode)) (x y : NodeId) (n m : KNode)
    (hxy : x ≠ y) (h : ns.lookup y = some m) : (upsert ns x n).lookup y = some m := by
  unfold upsert
  split
  · rw [bk_lookup_map_replace]
    have : ¬ y = x := fun e => hxy e.symm
    simp only [this, ↓reduceIte]
    exact h
  · exact bk_lookup_append_left _ _ _ _ h

/-! ## The primitive steps -/

theorem frame_getNode (y x : NodeId) : frameKeeps y (getNode x) := by
  intro c w hw
  unfold getNode
  simp only [writerWP_bind, writerWP_get]
  split
  · simp only [writerWP_pure]; exact hw
  · simp only [writerWP_bind, writerWP_read]
    split
    · split
      · exact writerWP_throw _ _ _ _
      · simp only [writerWP_bind, writerWP_set, writerWP_pure]
        obtain ⟨h1, h2, h3⟩ := hw
        exact ⟨h1, bk_lookup_append_left _ _ _ _ h2, h3⟩
    · exact writerWP_throw _ _ _ _

theorem frame_putNode (y x : NodeId) (n : KNode) (hxy : x ≠ y) : frameKeeps y (putNode x n) := by
  intro c w hw
  simp only [putNode, writerWP_modify]
  obtain ⟨h1, h2, h3⟩ := hw
  exact ⟨h1, frame_lookup_upsert _ _ _ _ _ hxy h2, h3⟩

theorem frame_fresh (y : NodeId) : frameKeeps y fresh := by
  intro c w hw
  simp only [fresh, writerWP_bind, writerWP_get, writerWP_set, writerWP_pure]
  exact hw.of _ rfl rfl (Nat.le_add_right _ 2)

/-- A new key node: its id is not y. -/
theorem frame_newKey (y : NodeId) (g h : Nat) (leaf : Bool) (ks : List Klong) (c : Ctx) (w : W)
    (hw : frameInv y w) :
    WriterWP (newKey g h leaf ks) c w (fun r v => r ≠ y ∧ frameInv y v) := by
  obtain ⟨h1, h2, h3⟩ := hw
  unfold newKey fresh
  simp only [writerWP_bind, writerWP_read, writerWP_get, writerWP_set, writerWP_pure]
  have hne : w.next ≠ y := fun e => by rw [e] at h1; exact Nat.lt_irrefl _ h1
  have hlt : y < w.next + 2 := by
    have := Nat.le_add_right w.next 2
    exact Nat.lt_of_lt_of_le h1 this
  split
  · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
    exact ⟨hne, hlt, bk_lookup_append_left _ _ _ _ h2, h3⟩
  · simp only [writerWP_bind, writerWP_modify, writerWP_pure, writerWP_pure]
    exact ⟨hne, hlt, bk_lookup_append_left _ _ _ _ h2, h3⟩

theorem frame_note (y : NodeId) (s : String) : frameKeeps y (note s) := by
  intro c w hw; simp only [note, writerWP_modify]; exact hw.of _ rfl rfl (Nat.le_refl _)

theorem frame_setMadeFor (y : NodeId) (x : NodeId) (old : Option NodeId) :
    frameKeeps y (setMadeFor x old) := by
  intro c w hw
  unfold setMadeFor
  split
  · simp only [writerWP_modify]; exact hw.of _ rfl rfl (Nat.le_refl _)
  · simp only [writerWP_pure]; exact hw

theorem frame_newSuperRoot (y : NodeId) (z : NodeId) : frameKeeps y (newSuperRoot z) := by
  intro c w hw
  unfold newSuperRoot
  simp only [note, fresh, writerWP_bind, writerWP_get, writerWP_read]
  split
  · simp only [writerWP_bind, writerWP_set, writerWP_modify]
    exact hw.of _ rfl rfl (Nat.le_refl _)
  · simp only [writerWP_bind, writerWP_modify, writerWP_get, writerWP_set, writerWP_pure]
    exact hw.of _ rfl rfl (Nat.le_add_right _ 2)

macro "fmNeutral" : tactic => `(tactic| (
  intro c w hw
  simp only [writerWP_bind, writerWP_get, writerWP_pure]
  repeat' first
    | split
    | exact writerWP_throw _ _ _ _
    | exact hw
    | simp only [writerWP_bind, writerWP_get, writerWP_pure]))

theorem frame_replacedBy (y : NodeId) (x : NodeId) : frameKeeps y (replacedBy x) := by
  unfold replacedBy; fmNeutral
theorem frame_klongAt (y : NodeId) (d : Nat) : frameKeeps y (klongAt d) := by
  unfold klongAt; fmNeutral

/-- A node of the path is not y. -/
theorem frame_pathNode (y : NodeId) (d : Nat) (c : Ctx) (w : W) (hw : frameInv y w) :
    WriterWP (pathNode d) c w (fun r v => r ≠ y ∧ frameInv y v) := by
  unfold pathNode
  simp only [writerWP_bind, writerWP_get]
  split
  · rename_i e he
    simp only [writerWP_pure]
    exact ⟨hw.2.2 e (List.mem_of_getElem? he), hw⟩
  · exact writerWP_throw _ _ _ _

theorem frame_parentAt (y : NodeId) (d : Nat) (c : Ctx) (w : W) (hw : frameInv y w) :
    WriterWP (parentAt d) c w (fun r v => frameNe y r ∧ frameInv y v) := by
  cases d with
  | zero => simp only [parentAt, writerWP_pure]; exact ⟨trivial, hw⟩
  | succ d =>
    unfold parentAt
    simp only [writerWP_bind]
    refine writerWP_mono (frame_pathNode y d c w hw) ?_
    intro r v h
    simp only [writerWP_pure]
    exact h

theorem frame_ghOf (y : NodeId) (x : NodeId) : frameKeeps y (ghOf x) := by
  intro c w hw
  unfold ghOf
  simp only [writerWP_bind]
  refine writerWP_mono (frame_getNode y x c w hw) ?_
  intro _ v hv
  simp only [writerWP_get]
  split
  · simp only [writerWP_pure]; exact hv
  · exact writerWP_throw _ _ _ _

theorem frameNe_some {y q : NodeId} (h : frameNe y (some q)) : q ≠ y := h

/-! ## The tactics of the walk -/

macro "fmState" : tactic => `(tactic| first
  | assumption
  | exact frameInv.of (by assumption) _ rfl rfl (Nat.le_refl _))

macro "fmUse " h:term : tactic => `(tactic| (
  (with_unfolding_none refine' frame_writerWP $h _ _ _ ?fmS ?fmPost)
  case fmS => fmState
  intro _ _ _))

macro "fmDone" : tactic => `(tactic| (
  (with_unfolding_none guard_target = frameInv _ _)
  fmState))

macro "fmStore" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (putNode _ _) _ _ _)
  (refine frame_writerWP (frame_putNode ?fmY _ _ ?fmNe) _ _ _ ?fmS ?fmPost)
  case fmS => fmState
  case fmNe => assumption
  intro _ _ _))

macro "fmCreate" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (newKey _ _ _ _) _ _ _)
  (refine writerWP_mono (frame_newKey ?fmY _ _ _ _ _ _ ?fmS) ?fmPost)
  case fmS => fmState
  rintro _ _ ⟨_, _⟩))

macro "fmParent" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (parentAt _) _ _ _)
  (refine writerWP_mono (frame_parentAt ?fmY _ _ _ ?fmS) ?fmPost)
  case fmS => fmState
  rintro _ _ ⟨_, _⟩))

macro "fmPath" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (pathNode _) _ _ _)
  (refine writerWP_mono (frame_pathNode ?fmY _ _ _ ?fmS) ?fmPost)
  case fmS => fmState
  rintro _ _ ⟨_, _⟩))

macro "fmReplace" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (replaceOrAdd _ _) _ _ _)
  refine writerWP_mono (bk_replaceOrAdd_same _ _ _ _) ?fmPost
  rintro _ _ hfmEq
  subst hfmEq))

/-- The callback at a parent q read from the path. -/
macro "fmUp " h:term : tactic => `(tactic| (
  (with_unfolding_none refine' frame_writerWP ($h _ _ ?fmQ) _ _ _ ?fmS ?fmPost)
  case fmQ => first | assumption | exact frameNe_some (by assumption)
  case fmS => fmState
  intro _ _ _))

macro "fmCore" : tactic => `(tactic| first
  | fmDone
  | fmStore
  | fmCreate
  | fmParent
  | fmPath
  | fmReplace
  | fmUse (frame_getNode _ _)
  | fmUse (frame_ghOf _ _)
  | fmUse (frame_replacedBy _ _)
  | fmUse (frame_klongAt _ _)
  | fmUse (frame_note _ _)
  | fmUse (frame_fresh _)
  | fmUse (frame_newSuperRoot _ _)
  | fmUse (frame_setMadeFor _ _ _)
  | exact writerWP_throw _ _ _ _)

/-! ## The splits -/

theorem frame_addKeys (y : NodeId) (x : NodeId) (ins : List (Nat × NodeId)) (hxy : x ≠ y) :
    frameKeeps y (addKeys x ins) := by
  intro c w hw
  unfold addKeys
  repeat' first | wpSimplify | fmCore

set_option maxHeartbeats 1600000 in
/-- Every route of a full node's replacement keeps y as it is, for a node x
that is not y and a callback that keeps it for every parent that is not y. -/
theorem frame_handleFullWith (y : NodeId) (up : NodeId → List (Nat × NodeId) → M Unit)
    (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) (last : KNode) (compact : Bool)
    (hxy : x ≠ y) (hup : ∀ q more, q ≠ y → frameKeeps y (up q more)) :
    frameKeeps y (handleFullWith up depth x ins last compact) := by
  intro c w hw
  unfold handleFullWith
  repeat' first
    | wpSimplify
    | fmCore
    | fmUp hup
    | wpSplit
    | split
    | contradiction

theorem frame_appendKlongs (y : NodeId) (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId))
    (hxy : x ≠ y) : frameKeeps y (appendKlongs depth x ins) := by
  induction depth generalizing x ins with
  | zero =>
    intro c w hw
    rw [appendKlongs_step_dead]
    repeat' first
      | wpSimplify
      | fmCore
      | fmUse (frame_handleFullWith _ _ _ _ _ _ _ hxy (fun _ _ _ => frame_throw _ _))
      | fmUse (frame_addKeys _ _ _ hxy)
      | wpSplit
      | split
  | succ depth ih =>
    intro c w hw
    rw [appendKlongs_step_dead]
    repeat' first
      | wpSimplify
      | fmCore
      | fmUse (frame_handleFullWith _ _ _ _ _ _ _ hxy (fun q more hq => ih q more hq))
      | fmUse (frame_addKeys _ _ _ hxy)
      | wpSplit
      | split

/-- An overlay node is below the next id. -/
theorem frame_lt_next {B : NodeId} {c : Ctx} {w : W} (hb : Book B c w) {y : NodeId} {n : KNode}
    (h : w.nodes.lookup y = some n) : y < w.next := by
  have hm := bk_mem_ids_of_lookup _ _ _ h
  rw [hb.ids] at hm
  obtain ⟨q, hq, he⟩ := List.mem_map.mp (List.mem_reverse.mp hm)
  have := hb.bound q hq
  rw [he] at this
  exact this

/-- An empty segment leaf of the overlay that is not the node appended to and
not on the key access path stays as it is through `appendKlongs`. -/
theorem appendFrameOK (B : NodeId) : AppendFrameOK B := by
  intro depth x ins c w y _ hb hy hxy hp
  refine writerWP_mono (frame_appendKlongs y depth x ins (fun e => hxy e.symm) c w
    ⟨frame_lt_next hb hy, hy, hp⟩) ?_
  intro _ _ h
  exact h.2.1

end SIS.Tree
