/-
`htb`'s sites (bergdb 025-05, step 8): a node y that a split's cascade does not reach.
`appendKlongs` at `depth` changes only the node it appends to, nodes it makes, and the key
access path's nodes above `depth`; a node y that is none of these keeps its overlay node
and stays not taken back (`FrameD`; `WriterFrame.lean` for an empty leaf off the path).
-/
import SIS.Tree.HtbLoop

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- y is below the next id, has the overlay node m, is not taken back, and is none of the
key access path's first k nodes. -/
def FrameD (y : NodeId) (m : KNode) (k : Nat) (N : Nat) (w : W) : Prop :=
  y < w.next ∧ w.nodes.lookup y = some m ∧ w.taken.contains y = false ∧
    (∀ j a z, j < k → w.path[j]? = some (a, z) → z ≠ y) ∧ N ≤ w.next

def FrameKeepsD (y : NodeId) (m : KNode) (k : Nat) (N : Nat) {α : Type} (f : M α) : Prop :=
  ∀ c w, FrameD y m k N w → WriterWP f c w (fun _ v => FrameD y m k N v)

section D

variable {y : NodeId} {m : KNode} {k : Nat} {N : Nat}

theorem FrameD.same {w v : W} (h : FrameD y m k N w)
    (hn : w.next ≤ v.next) (hl : v.nodes.lookup y = w.nodes.lookup y) (ht : v.taken = w.taken)
    (hp : v.path = w.path) : FrameD y m k N v := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨Nat.lt_of_lt_of_le h1 hn, by rw [hl]; exact h2, by rw [ht]; exact h3,
    fun j a z hj hz => h4 j a z hj (by rw [← hp]; exact hz), Nat.le_trans h5 hn⟩

theorem fd_getNode (x : NodeId) : FrameKeepsD y m k N (getNode x) := by
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
        exact hw.same (Nat.le_refl _) (bk_lookup_append_left _ _ _ _ hw.2.1 |>.trans hw.2.1.symm) rfl rfl
    · exact writerWP_throw _ _ _ _

theorem fd_putNode (x : NodeId) (n : KNode) (hxy : x ≠ y) : FrameKeepsD y m k N (putNode x n) := by
  intro c w hw
  simp only [putNode, writerWP_modify]
  exact hw.same (Nat.le_refl _) ((frame_lookup_upsert _ _ _ _ _ hxy hw.2.1).trans hw.2.1.symm) rfl rfl

theorem fd_modify (f : W → W) (hn : ∀ w, w.next ≤ (f w).next) (hl : ∀ w, (f w).nodes = w.nodes)
    (ht : ∀ w, (f w).taken = w.taken) (hp : ∀ w, (f w).path = w.path) :
    FrameKeepsD y m k N (modify f : M Unit) := by
  intro c w hw
  simp only [writerWP_modify]
  exact hw.same (hn w) (by rw [hl]) (ht w) (hp w)

theorem fd_fresh : FrameKeepsD y m k N fresh := by
  intro c w hw
  simp only [fresh, writerWP_bind, writerWP_get, writerWP_set, writerWP_pure]
  exact hw.same (Nat.le_add_right _ 2) rfl rfl rfl

theorem fd_newKey (g h : Nat) (leaf : Bool) (ks : List Klong) (c : Ctx) (w : W)
    (hw : FrameD y m k N w) :
    WriterWP (newKey g h leaf ks) c w (fun r v => r ≠ y ∧ FrameD y m k N v) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hw
  unfold newKey fresh
  simp only [writerWP_bind, writerWP_read, writerWP_get, writerWP_set, writerWP_pure]
  have hne : w.next ≠ y := fun e => by rw [e] at h1; exact Nat.lt_irrefl _ h1
  have hlt : y < w.next + 2 := Nat.lt_of_lt_of_le h1 (Nat.le_add_right w.next 2)
  split
  · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
    exact ⟨hne, hlt, bk_lookup_append_left _ _ _ _ h2, h3, h4, Nat.le_trans h5 (Nat.le_add_right _ 2)⟩
  · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
    exact ⟨hne, hlt, bk_lookup_append_left _ _ _ _ h2, h3, h4, Nat.le_trans h5 (Nat.le_add_right _ 2)⟩

theorem fd_note (s : String) : FrameKeepsD y m k N (note s) := by
  intro c w hw; simp only [note, writerWP_modify]; exact hw.same (Nat.le_refl _) rfl rfl rfl

theorem fd_setMadeFor (x : NodeId) (old : Option NodeId) : FrameKeepsD y m k N (setMadeFor x old) := by
  intro c w hw
  unfold setMadeFor
  split
  · simp only [writerWP_modify]; exact hw.same (Nat.le_refl _) rfl rfl rfl
  · simp only [writerWP_pure]; exact hw

theorem fd_newSuperRoot (z : NodeId) : FrameKeepsD y m k N (newSuperRoot z) := by
  intro c w hw
  unfold newSuperRoot
  simp only [note, fresh, writerWP_bind, writerWP_get, writerWP_read]
  split
  · simp only [writerWP_bind, writerWP_set, writerWP_modify]
    exact hw.same (Nat.le_refl _) rfl rfl rfl
  · simp only [writerWP_bind, writerWP_modify, writerWP_get, writerWP_set, writerWP_pure]
    exact hw.same (Nat.le_add_right _ 2) rfl rfl rfl

theorem fd_same {α : Type} (f : M α) (hf : ∀ c w, WriterWP f c w (fun _ v => v = w)) :
    FrameKeepsD y m k N f := fun c w hw => writerWP_mono (hf c w) (fun _ v hv => by rw [hv]; exact hw)

theorem fd_replacedBy (x : NodeId) : FrameKeepsD y m k N (replacedBy x) :=
  fd_same _ (fun c w => writerWP_mono (kd_replacedBy x c w) (fun _ _ h => h.1))
theorem fd_klongAt (d : Nat) : FrameKeepsD y m k N (klongAt d) :=
  fd_same _ (fun c w => writerWP_mono (kd_klongAt d c w) (fun _ _ h => h.1))

theorem fd_ghOf (x : NodeId) : FrameKeepsD y m k N (ghOf x) := by
  intro c w hw
  unfold ghOf
  simp only [writerWP_bind]
  refine writerWP_mono (fd_getNode x c w hw) ?_
  intro _ v hv
  simp only [writerWP_get]
  split
  · simp only [writerWP_pure]; exact hv
  · exact writerWP_throw _ _ _ _

theorem fd_pathNode (d : Nat) (c : Ctx) (w : W) (hw : FrameD y m k N w) (hd : d < k) :
    WriterWP (pathNode d) c w (fun r v => r ≠ y ∧ FrameD y m k N v) := by
  unfold pathNode
  simp only [writerWP_bind, writerWP_get]
  split
  · rename_i e he
    simp only [writerWP_pure]
    exact ⟨hw.2.2.2.1 d e.1 e.2 hd he, hw⟩
  · exact writerWP_throw _ _ _ _

theorem fd_parentAt (d : Nat) (c : Ctx) (w : W) (hw : FrameD y m k N w) (hd : d ≤ k) :
    WriterWP (parentAt d) c w (fun r v => frameNe y r ∧ FrameD y m k N v) := by
  cases d with
  | zero => simp only [parentAt, writerWP_pure]; exact ⟨trivial, hw⟩
  | succ d =>
    unfold parentAt
    simp only [writerWP_bind]
    refine writerWP_mono (fd_pathNode d c w hw (by omega)) ?_
    intro r v h
    simp only [writerWP_pure]
    exact h

theorem fd_replaceOrAdd (last : KNode) (ins : List (Nat × NodeId)) :
    FrameKeepsD y m k N (replaceOrAdd last ins) :=
  fd_same _ (fun c w => tk_replaceOrAdd last ins c w)

end D

macro "fdUse " h:term : tactic => `(tactic| (
  (refine writerWP_mono ($h _ _ (by assumption)) ?fdPost)
  intro _ _ _))

macro "fdCore" : tactic => `(tactic| first
  | exact writerWP_throw _ _ _ _
  | ((with_unfolding_none guard_target = WriterWP (putNode _ _) _ _ _)
     refine writerWP_mono (fd_putNode _ _ (by assumption) _ _ (by assumption)) ?fdPost
     intro _ _ _)
  | ((with_unfolding_none guard_target = WriterWP (newKey _ _ _ _) _ _ _)
     refine writerWP_mono (fd_newKey _ _ _ _ _ _ (by assumption)) ?fdPost
     rintro _ _ ⟨_, _⟩)
  | ((with_unfolding_none guard_target = WriterWP (parentAt _) _ _ _)
     refine writerWP_mono (fd_parentAt _ _ _ (by assumption) (by omega)) ?fdPost
     rintro _ _ ⟨_, _⟩)
  | ((with_unfolding_none guard_target = WriterWP (pathNode _) _ _ _)
     refine writerWP_mono (fd_pathNode _ _ _ (by assumption) (by omega)) ?fdPost
     rintro _ _ ⟨_, _⟩)
  | fdUse (fd_getNode _)
  | fdUse (fd_ghOf _)
  | fdUse (fd_replacedBy _)
  | fdUse (fd_klongAt _)
  | fdUse (fd_note _)
  | fdUse fd_fresh
  | fdUse (fd_newSuperRoot _)
  | fdUse (fd_setMadeFor _ _)
  | fdUse (fd_replaceOrAdd _ _))

section D2

variable {y : NodeId} {m : KNode} {k : Nat} {N : Nat}

theorem fd_addKeys (x : NodeId) (ins : List (Nat × NodeId)) (hxy : x ≠ y) :
    FrameKeepsD y m k N (addKeys x ins) := by
  intro c w hw
  unfold addKeys
  repeat' first | assumption | (simp only [writerWP_bind, writerWP_read, writerWP_get, writerWP_pure]) | fdCore

set_option maxHeartbeats 3200000 in
theorem fd_handleFullWith (up : NodeId → List (Nat × NodeId) → M Unit)
    (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) (last : KNode) (compact : Bool)
    (hxy : x ≠ y) (hdk : depth ≤ k) (hup : ∀ q more, q ≠ y → FrameKeepsD y m k N (up q more)) :
    FrameKeepsD y m k N (handleFullWith up depth x ins last compact) := by
  intro c w hw
  unfold handleFullWith
  repeat' first
    | assumption
    | (simp only [writerWP_bind, writerWP_read, writerWP_get, writerWP_pure, writerWP_modify])
    | (refine fd_modify _ (fun _ => Nat.le_refl _) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) _ _ (by assumption))
    | fdCore
    | (refine writerWP_mono (hup _ _ (by first | assumption | exact frameNe_some (by assumption)) _ _
        (by assumption)) ?_; intro _ _ _)
    | wpSplit
    | split
    | contradiction

theorem fd_appendKlongs (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId))
    (hxy : x ≠ y) (hdk : depth ≤ k) : FrameKeepsD y m k N (appendKlongs depth x ins) := by
  induction depth generalizing x ins with
  | zero =>
    intro c w hw
    rw [appendKlongs_step_dead]
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_mono (fd_getNode x c w hw) ?_
    intro _ v hv
    split
    · exact fd_handleFullWith _ _ _ _ _ _ hxy hdk (fun _ _ _ c w _ => writerWP_throw _ _ _ _) c v hv
    · split
      · exact fd_handleFullWith _ _ _ _ _ _ hxy hdk (fun _ _ _ c w _ => writerWP_throw _ _ _ _) c v hv
      · exact fd_addKeys x ins hxy c v hv
  | succ d ih =>
    intro c w hw
    rw [appendKlongs_step_dead]
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_mono (fd_getNode x c w hw) ?_
    intro _ v hv
    split
    · exact fd_handleFullWith _ _ _ _ _ _ hxy hdk (fun q more hq => ih q more hq (by omega)) c v hv
    · split
      · exact fd_handleFullWith _ _ _ _ _ _ hxy hdk (fun q more hq => ih q more hq (by omega)) c v hv
      · exact fd_addKeys x ins hxy c v hv

end D2

end SIS.Tree
