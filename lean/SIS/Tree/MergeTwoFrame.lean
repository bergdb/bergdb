/-
The merges into two nodes (bergdb 024-22, TP33): frame lemmas for the count
of the writer's note "merge.two" (`W.trail`), as `MergeFrameDead.lean` has
them for `W.merges`. Every action of the writer but `merge` keeps the count;
a merge adds one exactly when it makes two nodes.
-/
import SIS.Tree.MergeOpBoundProof

namespace SIS.Tree

open SIS SIS.Check

/-- The merges into two nodes so far: the notes "merge.two" in the trail. -/
def twoNotes (w : W) : Nat := w.trail.count "merge.two"

/-- An action of the writer adds at most k merges into two nodes. -/
def TwoLe {α : Type} (k : Nat) (f : M α) : Prop :=
  ∀ (c : Ctx) (w w' : W) (r : α), (f.run c).run w = .ok (r, w') → twoNotes w' ≤ twoNotes w + k

theorem twoLe_pure {α : Type} (k : Nat) (a : α) : TwoLe k (pure a : M α) := by
  intro c w w' r h
  simp only [pure, ReaderT.run, ReaderT.pure, StateT.run, StateT.pure, Except.pure,
    Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨_, rfl⟩ := h
  omega

theorem twoLe_throw {α : Type} (k : Nat) (e : String) : TwoLe k (throw e : M α) := by
  intro c w w' r h
  simp [throw, throwThe, MonadExceptOf.throw, ReaderT.run, StateT.run, liftM, monadLift,
    MonadLift.monadLift, StateT.lift, bind, Except.bind] at h

theorem twoLe_bind {α β : Type} {a b : Nat} {x : M α} {f : α → M β}
    (hx : TwoLe a x) (hf : ∀ v, TwoLe b (f v)) : TwoLe (a + b) (x >>= f) := by
  intro c w w' r h
  simp only [bind, ReaderT.bind, ReaderT.run, StateT.bind, StateT.run] at h
  cases hxr : x c w with
  | error e => rw [hxr] at h; simp [Except.bind] at h
  | ok p =>
    rw [hxr] at h
    simp only [Except.bind] at h
    have h1 := hx c w p.2 p.1 (by simp [ReaderT.run, StateT.run, hxr])
    have h2 := hf p.1 c p.2 w' r (by simpa [ReaderT.run, StateT.run] using h)
    omega

theorem twoLe_mono {α : Type} {k k' : Nat} {f : M α} (hk : k ≤ k') (h : TwoLe k f) :
    TwoLe k' f := by
  intro c w w' r hr
  have := h c w w' r hr
  omega

theorem twoLe_bind0 {α β : Type} {k : Nat} {x : M α} {f : α → M β}
    (hx : TwoLe 0 x) (hf : ∀ v, TwoLe k (f v)) : TwoLe k (x >>= f) := by
  have := twoLe_bind hx hf
  simpa using this

theorem writerWP_of_twoLe {α : Type} {k : Nat} {f : M α}
    (hf : TwoLe k f) (c : Ctx) (w : W) (post : α → W → Prop)
    (hp : ∀ r v, twoNotes v ≤ twoNotes w + k → post r v) : WriterWP f c w post := by
  intro r v h
  exact hp r v (hf c w v r h)

theorem twoLe_read (k : Nat) : TwoLe k (read : M Ctx) := by
  intro c w w' r h
  simp [read, readThe, MonadReaderOf.read, ReaderT.read, ReaderT.run, StateT.run, pure,
    StateT.pure, Except.pure] at h
  obtain ⟨_, rfl⟩ := h
  omega

theorem twoLe_get (k : Nat) : TwoLe k (MonadState.get : M W) := by
  intro c w w' r h
  simp [MonadState.get, getThe, MonadStateOf.get, StateT.get, ReaderT.run, StateT.run, liftM,
    monadLift, MonadLift.monadLift, pure, Except.pure] at h
  obtain ⟨_, rfl⟩ := h
  omega

theorem twoLe_modify (k : Nat) (f : W → W) (hf : ∀ w, twoNotes (f w) = twoNotes w) :
    TwoLe k (modify f : M Unit) := by
  intro c w w' r h
  simp [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, ReaderT.run, StateT.run,
    monadLift, MonadLift.monadLift, pure, Except.pure] at h
  rw [← h, hf]
  omega

/-- One step of the frame proofs: a bind, a leaf action, a branch. -/
macro "tstep" : tactic => `(tactic| first
  | apply twoLe_bind0
  | exact twoLe_pure _ _
  | exact twoLe_throw _ _
  | exact twoLe_read _
  | exact twoLe_get _
  | (apply twoLe_modify; intro _; rfl)
  | intro _
  | split)

theorem twoNotes_note (s : String) (w : W) :
    twoNotes { w with trail := s :: w.trail } =
      twoNotes w + if s = "merge.two" then 1 else 0 := by
  simp only [twoNotes, List.count_cons, beq_iff_eq]

/-- A note other than "merge.two" keeps the count. -/
theorem twoLe_note (k : Nat) (s : String) (hs : s ≠ "merge.two") : TwoLe k (note s) := by
  unfold note
  apply twoLe_modify
  intro w
  rw [twoNotes_note]
  simp [hs]

/-- A note of either of two texts, neither "merge.two", keeps the count. -/
theorem twoLe_note_ite (k : Nat) (b : Prop) [Decidable b] (s1 s2 : String)
    (h1 : s1 ≠ "merge.two") (h2 : s2 ≠ "merge.two") : TwoLe k (note (if b then s1 else s2)) := by
  by_cases hb : b
  · simp only [hb, if_true]; exact twoLe_note k s1 h1
  · simp only [hb, if_false]; exact twoLe_note k s2 h2

/-- A note of a text chosen by a condition, by cases. -/
theorem writerWP_note_ite (b : Prop) [Decidable b] (s1 s2 : String) (c : Ctx) (w : W)
    (post : Unit → W → Prop) (h1 : b → WriterWP (note s1) c w post)
    (h2 : ¬ b → WriterWP (note s2) c w post) :
    WriterWP (note (if b then s1 else s2)) c w post := by
  by_cases hb : b
  · rw [if_pos hb]; exact h1 hb
  · rw [if_neg hb]; exact h2 hb

/-- Any note adds at most one. -/
theorem twoLe_note_any (s : String) : TwoLe 1 (note s) := by
  intro c w w' r h
  simp [note, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, ReaderT.run, StateT.run,
    monadLift, MonadLift.monadLift, pure, Except.pure] at h
  rw [← h, twoNotes_note]
  split <;> omega

theorem twoLe_fresh (k : Nat) : TwoLe k fresh := by
  intro c w w' r h
  simp [fresh, MonadState.get, getThe, MonadStateOf.get, StateT.get, set, MonadStateOf.set,
    StateT.set, ReaderT.run, StateT.run, liftM, monadLift, MonadLift.monadLift, bind,
    ReaderT.bind, StateT.bind, Except.bind, pure, ReaderT.pure, StateT.pure, Except.pure] at h
  obtain ⟨_, rfl⟩ := h
  exact Nat.le_add_right _ _

theorem twoLe_getNode (k : Nat) (x : NodeId) : TwoLe k (getNode x) := by
  intro c w
  suffices hs : WriterWP (getNode x) c w (fun _ v => twoNotes v ≤ twoNotes w + k) by
    intro w' r h; exact hs r w' h
  unfold getNode
  simp only [writerWP_bind, writerWP_get]
  split
  · simp only [writerWP_pure]; simp only [twoNotes]; omega
  · simp only [writerWP_bind, writerWP_read]
    split
    · split
      · exact writerWP_throw _ _ _ _
      · simp only [writerWP_bind, writerWP_set, writerWP_pure]
        simp only [twoNotes]
        omega
    · exact writerWP_throw _ _ _ _

/-- The merge count is unchanged by the writer's leaves. -/
macro "tframeStep" : tactic => `(tactic| first
  | exact twoLe_pure _ _
  | exact twoLe_throw _ _
  | exact twoLe_read _
  | exact twoLe_get _
  | exact twoLe_fresh _
  | exact twoLe_getNode _ _
  | (solve | (apply twoLe_modify; intro _; rfl))
  | split
  | apply twoLe_bind0
  | intro _)

theorem twoLe_putNode (x : NodeId) (n : KNode) : TwoLe 0 (putNode x n) := by
  unfold putNode; repeat tframeStep

theorem twoLe_ghOf (x : NodeId) : TwoLe 0 (ghOf x) := by
  unfold ghOf; repeat tframeStep

theorem twoLe_newKey (g h : Nat) (leaf : Bool) (ks : List Klong) :
    TwoLe 0 (newKey g h leaf ks) := by
  unfold newKey; repeat tframeStep

theorem twoLe_newValue (h : Nat) : TwoLe 0 (newValue h) := by
  unfold newValue; repeat tframeStep

theorem twoLe_setMadeFor (x : NodeId) (old : Option NodeId) :
    TwoLe 0 (setMadeFor x old) := by
  unfold setMadeFor; repeat tframeStep

theorem twoLe_replacedBy (x : NodeId) : TwoLe 0 (replacedBy x) := by
  unfold replacedBy; repeat tframeStep

theorem twoLe_takenBack (x : NodeId) : TwoLe 0 (takenBack x) := by
  unfold takenBack; repeat tframeStep

theorem twoLe_pathClear : TwoLe 0 pathClear := by
  unfold pathClear; repeat tframeStep

theorem twoLe_pathAdd (cv : Option Nat) (x : NodeId) : TwoLe 0 (pathAdd cv x) := by
  unfold pathAdd; repeat tframeStep

theorem twoLe_pathSize : TwoLe 0 pathSize := by
  unfold pathSize; repeat tframeStep

theorem twoLe_pathNode (d : Nat) : TwoLe 0 (pathNode d) := by
  unfold pathNode; repeat tframeStep

theorem twoLe_klongAt (d : Nat) : TwoLe 0 (klongAt d) := by
  unfold klongAt; repeat tframeStep

theorem twoLe_parentAt (d : Nat) : TwoLe 0 (parentAt d) := by
  unfold parentAt
  cases d with
  | zero => exact twoLe_pure _ _
  | succ d =>
    apply twoLe_bind0 (twoLe_pathNode d)
    intro _; exact twoLe_pure _ _

theorem twoLe_newSuperRoot (x : NodeId) : TwoLe 0 (newSuperRoot x) := by
  intro c w
  suffices hs : WriterWP (newSuperRoot x) c w (fun _ v => twoNotes v ≤ twoNotes w + 0) by
    intro w' r h; exact hs r w' h
  unfold newSuperRoot fresh
  simp only [writerWP_bind, writerWP_read, writerWP_get]
  split
  · simp only [writerWP_bind, writerWP_set]
    refine writerWP_of_twoLe (twoLe_note 0 "top.inplace" (by decide)) _ _ _ ?_
    intro _ v hv
    simp only [twoNotes] at hv ⊢
    exact hv
  · simp only [writerWP_bind]
    refine writerWP_of_twoLe (twoLe_note 0 "top.new" (by decide)) _ _ _ ?_
    intro _ v hv
    simp only [writerWP_bind, writerWP_set, writerWP_modify, writerWP_get, writerWP_pure]
    simp only [twoNotes] at hv ⊢
    exact hv

macro "tframeStep2" : tactic => `(tactic| first
  | (refine twoLe_note _ _ ?_; decide)
  | exact twoLe_ghOf _
  | exact twoLe_newKey _ _ _ _
  | exact twoLe_newValue _
  | exact twoLe_setMadeFor _ _
  | exact twoLe_replacedBy _
  | exact twoLe_takenBack _
  | exact twoLe_pathClear
  | exact twoLe_pathAdd _ _
  | exact twoLe_pathSize
  | exact twoLe_pathNode _
  | exact twoLe_klongAt _
  | exact twoLe_parentAt _
  | exact twoLe_newSuperRoot _
  | tframeStep)

theorem twoLe_findRoot : TwoLe 0 findRoot := by
  unfold findRoot; repeat tframeStep2

theorem twoLe_addKeys (x : NodeId) (ins : List (Nat × NodeId)) :
    TwoLe 0 (addKeys x ins) := by
  unfold addKeys; repeat tframeStep2

theorem twoLe_foldlM {α β : Type} (xs : List α) (f : β → α → M β)
    (b : β) (hf : ∀ b a, TwoLe 0 (f b a)) : TwoLe 0 (xs.foldlM f b) := by
  induction xs generalizing b with
  | nil => exact twoLe_pure _ _
  | cons a xs ih =>
    simp only [List.foldlM_cons]
    exact twoLe_bind0 (hf b a) (fun b => ih b)

theorem twoLe_replaceOrAdd (last : KNode) (ins : List (Nat × NodeId)) :
    TwoLe 0 (replaceOrAdd last ins) := by
  unfold replaceOrAdd
  apply twoLe_bind0 (twoLe_read 0)
  intro c
  apply twoLe_foldlM
  intro last ins
  split <;> repeat tframeStep2


macro "twFrame" : tactic => `(tactic| first
  | (with_unfolding_none exact writerWP_throw _ _ _ _)
  | (with_unfolding_none refine writerWP_of_twoLe (twoLe_getNode 0 _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_twoLe (twoLe_ghOf _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_twoLe (twoLe_fresh 0) _ _ _ ?_; intro _ _ _)
  | ((with_unfolding_none refine writerWP_of_twoLe (twoLe_note 0 _ ?_) _ _ _ ?_) <;> first | decide | intro _ _ _)
  | ((with_unfolding_none refine writerWP_of_twoLe (twoLe_note_ite 0 _ _ _ ?_ ?_) _ _ _ ?_) <;> first | decide | intro _ _ _)
  | (with_unfolding_none refine writerWP_of_twoLe (twoLe_newKey _ _ _ _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_twoLe (twoLe_newValue _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_twoLe (twoLe_putNode _ _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_twoLe (twoLe_setMadeFor _ _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_twoLe (twoLe_replacedBy _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_twoLe (twoLe_takenBack _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_twoLe twoLe_pathClear _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_twoLe (twoLe_pathAdd _ _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_twoLe twoLe_pathSize _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_twoLe (twoLe_pathNode _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_twoLe (twoLe_klongAt _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_twoLe (twoLe_parentAt _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_twoLe (twoLe_newSuperRoot _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_twoLe (twoLe_replaceOrAdd _ _) _ _ _ ?_; intro _ _ _))

theorem twoLe_of_wp {α : Type} {k : Nat} {f : M α}
    (hf : ∀ c w, WriterWP f c w (fun _ v => twoNotes v ≤ twoNotes w + k)) : TwoLe k f := by
  intro c w v r h
  exact hf c w r v h

set_option maxHeartbeats 500000 in
theorem twoLe_handleFullWith_compact
    (up : NodeId → List (Nat × NodeId) → M Unit)
    (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) (last : KNode) (compact : Bool)
    (hup : ∀ q more, TwoLe 0 (up q more)) :
    TwoLe 0 (handleFullWith up depth x ins last compact) := by
  apply twoLe_of_wp
  intro c w
  unfold handleFullWith
  wpSimplify
  refine writerWP_of_twoLe (twoLe_getNode 0 x) _ _ _ ?_
  intro n v hn
  try wpSimplify
  refine writerWP_of_twoLe (twoLe_ghOf x) _ _ _ ?_
  intro gh v1 hg
  all_goals repeat first
    | wpSimplify
    | twFrame
    | (with_unfolding_none refine writerWP_of_twoLe (hup _ _) _ _ _ ?_; intro _ _ _)
    | wpSplit
    | split
    | ((try simp only [Nat.add_zero, twoNotes] at *); omega)

theorem twoLe_handleFullWith
    (up : NodeId → List (Nat × NodeId) → M Unit)
    (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) (last : KNode)
    (hup : ∀ q more, TwoLe 0 (up q more)) :
    TwoLe 0 (handleFullWith up depth x ins last) := by
  exact twoLe_handleFullWith_compact up depth x ins last false hup

theorem twoLe_appendKlongs (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) :
    TwoLe 0 (appendKlongs depth x ins) := by
  induction depth generalizing x ins with
  | zero =>
    apply twoLe_of_wp
    intro c w
    rw [appendKlongs_step_dead]
    wpSimplify
    refine writerWP_of_twoLe (twoLe_getNode 0 x) _ _ _ ?_
    intro n v hn
    split
    · refine writerWP_of_twoLe
        (twoLe_handleFullWith (fun _ _ => throw "corrupt: a split's parent above depth 0") _ x ins (n.lastVersion c.i) (fun _ _ => twoLe_throw _ _)) _ _ _ ?_
      intro r v1 h1
      simp only [Nat.add_zero, twoNotes] at *
      omega
    · split
      · refine writerWP_of_twoLe
          (twoLe_handleFullWith_compact (fun _ _ => throw "corrupt: a split's parent above depth 0")
            _ x ins (n.lastVersion c.i) true (fun _ _ => twoLe_throw _ _)) _ _ _ ?_
        intro r v1 h1
        simp only [Nat.add_zero, twoNotes] at *
        omega
      · refine writerWP_of_twoLe (twoLe_addKeys x ins) _ _ _ ?_
        intro r v1 h1
        simp only [Nat.add_zero, twoNotes] at *
        omega

  | succ depth ih =>
    apply twoLe_of_wp
    intro c w
    rw [appendKlongs_step_dead]
    wpSimplify
    refine writerWP_of_twoLe (twoLe_getNode 0 x) _ _ _ ?_
    intro n v hn
    split
    · refine writerWP_of_twoLe
        (twoLe_handleFullWith (fun q more => appendKlongs depth q more) _ x ins (n.lastVersion c.i) (fun q more => ih q more)) _ _ _ ?_
      intro r v1 h1
      simp only [Nat.add_zero, twoNotes] at *
      omega
    · split
      · refine writerWP_of_twoLe
          (twoLe_handleFullWith_compact (fun q more => appendKlongs depth q more)
            _ x ins (n.lastVersion c.i) true (fun q more => ih q more)) _ _ _ ?_
        intro r v1 h1
        simp only [Nat.add_zero, twoNotes] at *
        omega
      · refine writerWP_of_twoLe (twoLe_addKeys x ins) _ _ _ ?_
        intro r v1 h1
        simp only [Nat.add_zero, twoNotes] at *
        omega

theorem twoLe_handleFull_compact (d : Nat) (x : NodeId) (last : KNode) (compact : Bool) :
    TwoLe 0 (handleFull d x last compact) := by
  unfold handleFull
  refine twoLe_handleFullWith_compact _ _ _ _ _ _ ?_
  intro q more
  cases d with
  | zero => exact twoLe_throw _ _
  | succ d => exact twoLe_appendKlongs d q more

theorem twoLe_handleFull (d : Nat) (x : NodeId) (last : KNode) :
    TwoLe 0 (handleFull d x last) := by
  unfold handleFull
  refine twoLe_handleFullWith _ _ _ _ _ ?_
  intro q more
  cases d with
  | zero => exact twoLe_throw _ _
  | succ d => exact twoLe_appendKlongs d q more

macro "twFrame3" : tactic => `(tactic| first
  | (with_unfolding_none refine writerWP_of_twoLe (twoLe_appendKlongs _ _ _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_twoLe (twoLe_handleFull_compact _ _ _ _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_twoLe (twoLe_handleFull _ _ _) _ _ _ ?_; intro _ _ _)
  | twFrame)

theorem twoLe_appendDeleteKlong (x : NodeId) (depth cv : Nat) :
    TwoLe 0 (appendDeleteKlong x depth cv) := by
  apply twoLe_of_wp
  intro c w
  unfold appendDeleteKlong
  repeat' first
    | wpSimplify
    | twFrame3
    | wpSplit
    | split
    | ((try simp only [Nat.add_zero, twoNotes] at *); omega)

theorem twoLe_emptyKeyNext (x : NodeId) (depth : Nat) :
    TwoLe 0 (emptyKeyNext x depth) := by
  apply twoLe_of_wp
  intro c w
  unfold emptyKeyNext
  repeat' first
    | wpSimplify
    | twFrame3
    | wpSplit
    | split
    | ((try simp only [Nat.add_zero, twoNotes] at *); omega)

theorem twoLe_unlink (x : NodeId) : TwoLe 0 (unlink x) := by
  apply twoLe_of_wp
  intro c w
  unfold unlink
  repeat' first
    | wpSimplify
    | twFrame3
    | wpSplit
    | split
    | ((try simp only [Nat.add_zero, twoNotes] at *); omega)

theorem twoLe_retarget (p src dst : NodeId) : TwoLe 0 (retarget p src dst) := by
  apply twoLe_of_wp
  intro c w
  unfold retarget
  repeat' first
    | wpSimplify
    | twFrame3
    | wpSplit
    | split
    | ((try simp only [Nat.add_zero, twoNotes] at *); omega)

theorem twoLe_canTakeBack (x parent : NodeId) (cv : Nat) :
    TwoLe 0 (canTakeBack x parent cv) := by
  apply twoLe_of_wp
  intro c w
  unfold canTakeBack
  repeat' first
    | wpSimplify
    | twFrame3
    | wpSplit
    | split
    | ((try simp only [Nat.add_zero, twoNotes] at *); omega)

theorem twoLe_takeBack (x parent : NodeId) (cv : Nat) :
    TwoLe 0 (takeBack x parent cv) := by
  apply twoLe_of_wp
  intro c w
  unfold takeBack
  repeat' first
    | wpSimplify
    | twFrame3
    | (with_unfolding_none refine writerWP_of_twoLe (twoLe_retarget _ _ _) _ _ _ ?_; intro _ _ _)
    | wpSplit
    | split
    | ((try simp only [Nat.add_zero, twoNotes] at *); omega)

theorem twoLe_descendLte (cv fuel : Nat) (x : NodeId) :
    TwoLe 0 (descendLte cv fuel x) := by
  induction fuel generalizing x with
  | zero => exact twoLe_throw _ _
  | succ fuel ih =>
    apply twoLe_of_wp
    intro c w
    unfold descendLte
    repeat' first
      | wpSimplify
      | twFrame3
      | (with_unfolding_none refine writerWP_of_twoLe (ih _) _ _ _ ?_; intro _ _ _)
      | wpSplit
      | split
      | ((try simp only [Nat.add_zero, twoNotes] at *); omega)

theorem twoLe_descendToSegmentRoot (key : Key) (segment : Nat) :
    TwoLe 0 (descendToSegmentRoot key segment) := by
  unfold descendToSegmentRoot
  refine twoLe_bind0 (twoLe_read 0) ?_
  intro c
  refine twoLe_bind0 twoLe_pathClear ?_
  intro _
  refine twoLe_bind0 twoLe_findRoot ?_
  intro root
  apply twoLe_foldlM
  intro node cv
  refine twoLe_bind0 (twoLe_descendLte _ _ _) ?_
  intro leaf
  refine twoLe_bind0 (twoLe_getNode 0 leaf) ?_
  intro n
  split
  · exact twoLe_throw _ _
  · refine twoLe_bind0 (twoLe_pathAdd _ _) ?_
    intro _
    exact twoLe_pure _ _

macro "twFrame4" : tactic => `(tactic| first
  | (with_unfolding_none refine writerWP_of_twoLe (twoLe_unlink _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_twoLe (twoLe_retarget _ _ _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_twoLe (twoLe_canTakeBack _ _ _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_twoLe (twoLe_takeBack _ _ _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_twoLe (twoLe_descendLte _ _ _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_twoLe (twoLe_descendToSegmentRoot _ _) _ _ _ ?_; intro _ _ _)
  | twFrame3)

theorem twoLe_takeBackRoot (x : NodeId) (depth only : Nat) :
    TwoLe 0 (takeBackRoot x depth only) := by
  apply twoLe_of_wp
  intro c w
  unfold takeBackRoot
  repeat' first
    | wpSimplify
    | twFrame4
    | wpSplit
    | split
    | ((try simp only [Nat.add_zero, twoNotes] at *); omega)

theorem twoLe_replaceRoot (x : NodeId) (depth only : Nat) :
    TwoLe 0 (replaceRoot x depth only) := by
  apply twoLe_of_wp
  intro c w
  unfold replaceRoot
  repeat' first
    | wpSimplify
    | twFrame4
    | wpSplit
    | split
    | ((try simp only [Nat.add_zero, twoNotes] at *); omega)

theorem twoLe_collapseRoot (key : Key) (segment fuel : Nat) :
    TwoLe 0 (collapseRoot key segment fuel) := by
  induction fuel with
  | zero => exact twoLe_throw _ _
  | succ fuel ih =>
    apply twoLe_of_wp
    intro c w
    unfold collapseRoot
    repeat' first
      | wpSimplify
      | twFrame4
      | (with_unfolding_none refine writerWP_of_twoLe (twoLe_takeBackRoot _ _ _) _ _ _ ?_; intro _ _ _)
      | (with_unfolding_none refine writerWP_of_twoLe (twoLe_replaceRoot _ _ _) _ _ _ ?_; intro _ _ _)
      | (with_unfolding_none refine writerWP_of_twoLe ih _ _ _ ?_; intro _ _ _)
      | wpSplit
      | split
      | ((try simp only [Nat.add_zero, twoNotes] at *); omega)

theorem twoLe_descendHeight (cv h fuel : Nat) (x : NodeId) :
    TwoLe 0 (descendHeight cv h fuel x) := by
  induction fuel generalizing x with
  | zero => exact twoLe_throw _ _
  | succ fuel ih =>
    apply twoLe_of_wp
    intro c w
    unfold descendHeight
    repeat' first
      | wpSimplify
      | twFrame4
      | (with_unfolding_none refine writerWP_of_twoLe (ih _) _ _ _ ?_; intro _ _ _)
      | wpSplit
      | split
      | ((try simp only [Nat.add_zero, twoNotes] at *); omega)

theorem twoLe_descendToHeight (key : Key) (g h : Nat) :
    TwoLe 0 (descendToHeight key g h) := by
  apply twoLe_of_wp
  intro c w
  unfold descendToHeight
  repeat' first
    | wpSimplify
    | twFrame4
    | (with_unfolding_none refine writerWP_of_twoLe (twoLe_descendHeight _ _ _ _) _ _ _ ?_; intro _ _ _)
    | wpSplit
    | split
    | ((try simp only [Nat.add_zero, twoNotes] at *); omega)

theorem twoLe_forIn {α β : Type} (xs : List α) (init : β)
    (f : α → β → M (ForInStep β)) (hf : ∀ a b, TwoLe 0 (f a b)) :
    TwoLe 0 (forIn xs init f) := by
  induction xs generalizing init with
  | nil => exact twoLe_pure _ _
  | cons a xs ih =>
    rw [List.forIn_cons]
    refine twoLe_bind0 (hf a init) ?_
    intro step
    cases step with
    | done b => exact twoLe_pure _ _
    | yield b => exact ih b

set_option maxHeartbeats 800000 in
theorem twoLe_mergeParent (p : NodeId) (depth il cL : Nat) (m1 : NodeId) (ir cR : Nat)
    (m2 : Option (NodeId × Nat)) : TwoLe 0 (mergeParent p depth il cL m1 ir cR m2) := by
  apply twoLe_of_wp
  intro c w
  unfold mergeParent
  repeat' first
    | wpSimplify
    | twFrame4
    | wpSplit
    | split
    | ((try simp only [Nat.add_zero, twoNotes] at *); omega)

theorem twoLe_sibling (p : NodeId) (pn : KNode) (i : Nat) (inner : Bool) :
    TwoLe 0 (sibling p pn i inner) := by
  apply twoLe_of_wp
  intro c w
  unfold sibling
  repeat' first
    | wpSimplify
    | twFrame4
    | wpSplit
    | split
    | ((try simp only [Nat.add_zero, twoNotes] at *); omega)

macro "twFrame5" : tactic => `(tactic| first
  | (with_unfolding_none refine writerWP_of_twoLe (twoLe_mergeParent _ _ _ _ _ _ _ _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_twoLe (twoLe_sibling _ _ _ _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_twoLe (twoLe_descendToHeight _ _ _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_twoLe (twoLe_collapseRoot _ _ _) _ _ _ ?_; intro _ _ _)
  | twFrame4)

set_option maxHeartbeats 8000000 in
/-- A merge adds one merge into two nodes exactly when it makes two nodes: its
result is 2. -/
theorem writerWP_merge_two (x : NodeId) (d : Nat) (c : Ctx) (w : W) :
    WriterWP (merge x d) c w
      (fun r v => twoNotes v ≤ twoNotes w + (if r = 2 then 1 else 0)) := by
  unfold merge
  repeat' first
    | wpSimplify
    | simp only [List.forIn_cons, List.forIn_nil]
    | twFrame5
    | (with_unfolding_none refine writerWP_of_twoLe (twoLe_note_any "merge.two") _ _ _ ?_; intro _ _ _)
    | (refine writerWP_note_ite _ _ _ _ _ _ ?_ ?_ <;> intro _)
    | wpSplit
    | split
    | contradiction
    | ((try simp only [Nat.add_zero, twoNotes] at *); omega)

theorem twoLe_merge (x : NodeId) (d : Nat) : TwoLe 1 (merge x d) := by
  apply twoLe_of_wp
  intro c w
  refine writerWP_mono (writerWP_merge_two x d c w) ?_
  intro r v h
  split at h <;> omega

theorem twoLe_climb (depth : Nat) : TwoLe 0 (climb depth) := by
  induction depth with
  | zero =>
    apply twoLe_of_wp
    intro c w
    unfold climb
    repeat' first
      | wpSimplify
      | twFrame5
      | wpSplit
      | split
      | ((try simp only [Nat.add_zero, twoNotes] at *); omega)
  | succ depth ih =>
    apply twoLe_of_wp
    intro c w
    unfold climb
    repeat' first
      | wpSimplify
      | twFrame5
      | (with_unfolding_none refine writerWP_of_twoLe ih _ _ _ ?_; intro _ _ _)
      | wpSplit
      | split
      | ((try simp only [Nat.add_zero, twoNotes] at *); omega)

theorem twoLe_segmentCount (path : List (Option Nat × NodeId)) (stop : Nat) :
    TwoLe 0 ((path.take stop).foldlM (fun s e => do
      let n ← getNode e.2
      pure (if n.leaf then s + 1 else s)) 0) := by
  apply twoLe_foldlM
  intro s e
  refine twoLe_bind0 (twoLe_getNode 0 e.2) ?_
  intro n
  exact twoLe_pure _ _

theorem twoLe_unlinkLoop (depth tt : Nat) (js : List Nat) :
    TwoLe 0 (forIn js () (fun j _ => do
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
  apply twoLe_forIn
  intro j b
  apply twoLe_of_wp
  intro c w
  repeat' first
    | wpSimplify
    | twFrame5
    | wpSplit
    | split
    | ((try simp only [Nat.add_zero, twoNotes] at *); omega)

theorem twoLe_setNode (segRoot : NodeId) (cv : Nat) (create : Bool) :
    TwoLe 0 (setNode segRoot cv create) := by
  apply twoLe_of_wp
  intro c w
  unfold setNode
  repeat' first
    | wpSimplify
    | twFrame5
    | wpSplit
    | split
    | ((try simp only [Nat.add_zero, twoNotes] at *); omega)

end SIS.Tree
