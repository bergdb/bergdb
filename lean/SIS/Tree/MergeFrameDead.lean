/-
Frame lemmas for the writer, including dead-klong compaction.
-/
import SIS.Tree.MergeProps
import SIS.Tree.WriterWP
import SIS.Tree.WriterSteps

namespace SIS.Tree

open SIS SIS.Check

/-- An action of the writer adds at most k to the merge count. -/
def MergesLe {α : Type} (k : Nat) (f : M α) : Prop :=
  ∀ (c : Ctx) (w w' : W) (r : α), (f.run c).run w = .ok (r, w') → w'.merges ≤ w.merges + k

theorem mergesLe_pure {α : Type} (k : Nat) (a : α) : MergesLe k (pure a : M α) := by
  intro c w w' r h
  simp only [pure, ReaderT.run, ReaderT.pure, StateT.run, StateT.pure, Except.pure,
    Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨_, rfl⟩ := h
  omega

theorem mergesLe_throw {α : Type} (k : Nat) (e : String) : MergesLe k (throw e : M α) := by
  intro c w w' r h
  simp [throw, throwThe, MonadExceptOf.throw, ReaderT.run, StateT.run, liftM, monadLift,
    MonadLift.monadLift, StateT.lift, bind, Except.bind] at h

theorem mergesLe_bind {α β : Type} {a b : Nat} {x : M α} {f : α → M β}
    (hx : MergesLe a x) (hf : ∀ v, MergesLe b (f v)) : MergesLe (a + b) (x >>= f) := by
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

theorem mergesLe_bind0 {α β : Type} {k : Nat} {x : M α} {f : α → M β}
    (hx : MergesLe 0 x) (hf : ∀ v, MergesLe k (f v)) : MergesLe k (x >>= f) := by
  have := mergesLe_bind hx hf
  simpa using this

theorem writerWP_of_mergesLe {α : Type} {k : Nat} {f : M α}
    (hf : MergesLe k f) (c : Ctx) (w : W) (post : α → W → Prop)
    (hp : ∀ r v, v.merges ≤ w.merges + k → post r v) : WriterWP f c w post := by
  intro r v h
  exact hp r v (hf c w v r h)

theorem mergesLe_read (k : Nat) : MergesLe k (read : M Ctx) := by
  intro c w w' r h
  simp [read, readThe, MonadReaderOf.read, ReaderT.read, ReaderT.run, StateT.run, pure,
    StateT.pure, Except.pure] at h
  obtain ⟨_, rfl⟩ := h
  omega

theorem mergesLe_get (k : Nat) : MergesLe k (MonadState.get : M W) := by
  intro c w w' r h
  simp [MonadState.get, getThe, MonadStateOf.get, StateT.get, ReaderT.run, StateT.run, liftM,
    monadLift, MonadLift.monadLift, pure, Except.pure] at h
  obtain ⟨_, rfl⟩ := h
  omega

theorem mergesLe_modify (k : Nat) (f : W → W) (hf : ∀ w, (f w).merges = w.merges) :
    MergesLe k (modify f : M Unit) := by
  intro c w w' r h
  simp [modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, ReaderT.run, StateT.run,
    monadLift, MonadLift.monadLift, pure, Except.pure] at h
  rw [← h, hf]
  omega

/-- One step of the frame proofs: a bind, a leaf action, a branch. -/
macro "mstep" : tactic => `(tactic| first
  | apply mergesLe_bind0
  | exact mergesLe_pure _ _
  | exact mergesLe_throw _ _
  | exact mergesLe_read _
  | exact mergesLe_get _
  | (apply mergesLe_modify; intro _; rfl)
  | intro _
  | split)

theorem mergesLe_note (k : Nat) (s : String) : MergesLe k (note s) := by
  unfold note; repeat mstep

theorem mergesLe_fresh (k : Nat) : MergesLe k fresh := by
  intro c w w' r h
  simp [fresh, MonadState.get, getThe, MonadStateOf.get, StateT.get, set, MonadStateOf.set,
    StateT.set, ReaderT.run, StateT.run, liftM, monadLift, MonadLift.monadLift, bind,
    ReaderT.bind, StateT.bind, Except.bind, pure, ReaderT.pure, StateT.pure, Except.pure] at h
  obtain ⟨_, rfl⟩ := h
  simp

theorem mergesLe_getNode (k : Nat) (x : NodeId) : MergesLe k (getNode x) := by
  intro c w
  suffices hs : WriterWP (getNode x) c w (fun _ v => v.merges ≤ w.merges + k) by
    intro w' r h; exact hs r w' h
  unfold getNode
  simp only [writerWP_bind, writerWP_get]
  split
  · simp only [writerWP_pure]; omega
  · simp only [writerWP_bind, writerWP_read]
    split
    · split
      · exact writerWP_throw _ _ _ _
      · simp only [writerWP_bind, writerWP_set, writerWP_pure]
        omega
    · exact writerWP_throw _ _ _ _

/-- The merge count is unchanged by the writer's leaves. -/
macro "frameStep" : tactic => `(tactic| first
  | exact mergesLe_pure _ _
  | exact mergesLe_throw _ _
  | exact mergesLe_read _
  | exact mergesLe_get _
  | exact mergesLe_fresh _
  | exact mergesLe_getNode _ _
  | (solve | (apply mergesLe_modify; intro _; rfl))
  | split
  | apply mergesLe_bind0
  | intro _)

theorem mergesLe_putNode (x : NodeId) (n : KNode) : MergesLe 0 (putNode x n) := by
  unfold putNode; repeat frameStep

theorem mergesLe_ghOf (x : NodeId) : MergesLe 0 (ghOf x) := by
  unfold ghOf; repeat frameStep

theorem mergesLe_newKey (g h : Nat) (leaf : Bool) (ks : List Klong) :
    MergesLe 0 (newKey g h leaf ks) := by
  unfold newKey; repeat frameStep

theorem mergesLe_newValue (h : Nat) : MergesLe 0 (newValue h) := by
  unfold newValue; repeat frameStep

theorem mergesLe_setMadeFor (x : NodeId) (old : Option NodeId) :
    MergesLe 0 (setMadeFor x old) := by
  unfold setMadeFor; repeat frameStep

theorem mergesLe_replacedBy (x : NodeId) : MergesLe 0 (replacedBy x) := by
  unfold replacedBy; repeat frameStep

theorem mergesLe_takenBack (x : NodeId) : MergesLe 0 (takenBack x) := by
  unfold takenBack; repeat frameStep

theorem mergesLe_pathClear : MergesLe 0 pathClear := by
  unfold pathClear; repeat frameStep

theorem mergesLe_pathAdd (cv : Option Nat) (x : NodeId) : MergesLe 0 (pathAdd cv x) := by
  unfold pathAdd; repeat frameStep

theorem mergesLe_pathSize : MergesLe 0 pathSize := by
  unfold pathSize; repeat frameStep

theorem mergesLe_pathNode (d : Nat) : MergesLe 0 (pathNode d) := by
  unfold pathNode; repeat frameStep

theorem mergesLe_klongAt (d : Nat) : MergesLe 0 (klongAt d) := by
  unfold klongAt; repeat frameStep

theorem mergesLe_parentAt (d : Nat) : MergesLe 0 (parentAt d) := by
  unfold parentAt
  cases d with
  | zero => exact mergesLe_pure _ _
  | succ d =>
    apply mergesLe_bind0 (mergesLe_pathNode d)
    intro _; exact mergesLe_pure _ _

theorem mergesLe_newSuperRoot (x : NodeId) : MergesLe 0 (newSuperRoot x) := by
  intro c w
  suffices hs : WriterWP (newSuperRoot x) c w (fun _ v => v.merges ≤ w.merges + 0) by
    intro w' r h; exact hs r w' h
  unfold newSuperRoot note fresh
  simp only [writerWP_bind, writerWP_read, writerWP_get]
  split <;> simp only [writerWP_bind, writerWP_set, writerWP_modify, writerWP_get,
    writerWP_pure] <;> omega

macro "frameStep2" : tactic => `(tactic| first
  | exact mergesLe_note _ _
  | exact mergesLe_ghOf _
  | exact mergesLe_newKey _ _ _ _
  | exact mergesLe_newValue _
  | exact mergesLe_setMadeFor _ _
  | exact mergesLe_replacedBy _
  | exact mergesLe_takenBack _
  | exact mergesLe_pathClear
  | exact mergesLe_pathAdd _ _
  | exact mergesLe_pathSize
  | exact mergesLe_pathNode _
  | exact mergesLe_klongAt _
  | exact mergesLe_parentAt _
  | exact mergesLe_newSuperRoot _
  | frameStep)

theorem mergesLe_findRoot : MergesLe 0 findRoot := by
  unfold findRoot; repeat frameStep2

theorem mergesLe_addKeys (x : NodeId) (ins : List (Nat × NodeId)) :
    MergesLe 0 (addKeys x ins) := by
  unfold addKeys; repeat frameStep2

theorem mergesLe_foldlM {α β : Type} (xs : List α) (f : β → α → M β)
    (b : β) (hf : ∀ b a, MergesLe 0 (f b a)) : MergesLe 0 (xs.foldlM f b) := by
  induction xs generalizing b with
  | nil => exact mergesLe_pure _ _
  | cons a xs ih =>
    simp only [List.foldlM_cons]
    exact mergesLe_bind0 (hf b a) (fun b => ih b)

theorem mergesLe_replaceOrAdd (last : KNode) (ins : List (Nat × NodeId)) :
    MergesLe 0 (replaceOrAdd last ins) := by
  unfold replaceOrAdd
  apply mergesLe_bind0 (mergesLe_read 0)
  intro c
  apply mergesLe_foldlM
  intro last ins
  split <;> repeat frameStep2

macro "wpSimplify" : tactic => `(tactic|
  simp only [writerWP_bind, writerWP_read, writerWP_get, writerWP_set,
    writerWP_modify, writerWP_pure])

macro "wpSplit" : tactic => `(tactic|
  (with_unfolding_none refine writerWP_if _ _ _ _ _ _ ?_ ?_) <;> intro _)

macro "wpFrame" : tactic => `(tactic| first
  | (with_unfolding_none exact writerWP_throw _ _ _ _)
  | (with_unfolding_none refine writerWP_of_mergesLe (mergesLe_getNode 0 _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_mergesLe (mergesLe_ghOf _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_mergesLe (mergesLe_fresh 0) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_mergesLe (mergesLe_note 0 _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_mergesLe (mergesLe_newKey _ _ _ _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_mergesLe (mergesLe_newValue _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_mergesLe (mergesLe_putNode _ _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_mergesLe (mergesLe_setMadeFor _ _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_mergesLe (mergesLe_replacedBy _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_mergesLe (mergesLe_takenBack _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_mergesLe mergesLe_pathClear _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_mergesLe (mergesLe_pathAdd _ _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_mergesLe mergesLe_pathSize _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_mergesLe (mergesLe_pathNode _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_mergesLe (mergesLe_klongAt _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_mergesLe (mergesLe_parentAt _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_mergesLe (mergesLe_newSuperRoot _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_mergesLe (mergesLe_replaceOrAdd _ _) _ _ _ ?_; intro _ _ _))

theorem mergesLe_of_wp {α : Type} {k : Nat} {f : M α}
    (hf : ∀ c w, WriterWP f c w (fun _ v => v.merges ≤ w.merges + k)) : MergesLe k f := by
  intro c w v r h
  exact hf c w r v h

set_option maxHeartbeats 500000 in
theorem mergesLe_handleFullWith_compact
    (up : NodeId → List (Nat × NodeId) → M Unit)
    (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) (last : KNode) (compact : Bool)
    (hup : ∀ q more, MergesLe 0 (up q more)) :
    MergesLe 0 (handleFullWith up depth x ins last compact) := by
  apply mergesLe_of_wp
  intro c w
  unfold handleFullWith
  wpSimplify
  refine writerWP_of_mergesLe (mergesLe_getNode 0 x) _ _ _ ?_
  intro n v hn
  try wpSimplify
  refine writerWP_of_mergesLe (mergesLe_ghOf x) _ _ _ ?_
  intro gh v1 hg
  all_goals repeat first
    | wpSimplify
    | wpFrame
    | (with_unfolding_none refine writerWP_of_mergesLe (hup _ _) _ _ _ ?_; intro _ _ _)
    | wpSplit
    | split
    | ((try simp only [Nat.add_zero] at *); omega)

theorem mergesLe_handleFullWith
    (up : NodeId → List (Nat × NodeId) → M Unit)
    (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) (last : KNode)
    (hup : ∀ q more, MergesLe 0 (up q more)) :
    MergesLe 0 (handleFullWith up depth x ins last) := by
  exact mergesLe_handleFullWith_compact up depth x ins last false hup

theorem mergesLe_appendKlongs (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) :
    MergesLe 0 (appendKlongs depth x ins) := by
  induction depth generalizing x ins with
  | zero =>
    apply mergesLe_of_wp
    intro c w
    rw [appendKlongs_step_dead]
    wpSimplify
    refine writerWP_of_mergesLe (mergesLe_getNode 0 x) _ _ _ ?_
    intro n v hn
    split
    · refine writerWP_of_mergesLe
        (mergesLe_handleFullWith (fun _ _ => throw "corrupt: a split's parent above depth 0") _ x ins (n.lastVersion c.i) (fun _ _ => mergesLe_throw _ _)) _ _ _ ?_
      intro r v1 h1
      simp only [Nat.add_zero] at *
      omega
    · split
      · refine writerWP_of_mergesLe
          (mergesLe_handleFullWith_compact (fun _ _ => throw "corrupt: a split's parent above depth 0")
            _ x ins (n.lastVersion c.i) true (fun _ _ => mergesLe_throw _ _)) _ _ _ ?_
        intro r v1 h1
        simp only [Nat.add_zero] at *
        omega
      · refine writerWP_of_mergesLe (mergesLe_addKeys x ins) _ _ _ ?_
        intro r v1 h1
        simp only [Nat.add_zero] at *
        omega

  | succ depth ih =>
    apply mergesLe_of_wp
    intro c w
    rw [appendKlongs_step_dead]
    wpSimplify
    refine writerWP_of_mergesLe (mergesLe_getNode 0 x) _ _ _ ?_
    intro n v hn
    split
    · refine writerWP_of_mergesLe
        (mergesLe_handleFullWith (fun q more => appendKlongs depth q more) _ x ins (n.lastVersion c.i) (fun q more => ih q more)) _ _ _ ?_
      intro r v1 h1
      simp only [Nat.add_zero] at *
      omega
    · split
      · refine writerWP_of_mergesLe
          (mergesLe_handleFullWith_compact (fun q more => appendKlongs depth q more)
            _ x ins (n.lastVersion c.i) true (fun q more => ih q more)) _ _ _ ?_
        intro r v1 h1
        simp only [Nat.add_zero] at *
        omega
      · refine writerWP_of_mergesLe (mergesLe_addKeys x ins) _ _ _ ?_
        intro r v1 h1
        simp only [Nat.add_zero] at *
        omega

theorem mergesLe_handleFull_compact (d : Nat) (x : NodeId) (last : KNode) (compact : Bool) :
    MergesLe 0 (handleFull d x last compact) := by
  unfold handleFull
  refine mergesLe_handleFullWith_compact _ _ _ _ _ _ ?_
  intro q more
  cases d with
  | zero => exact mergesLe_throw _ _
  | succ d => exact mergesLe_appendKlongs d q more

theorem mergesLe_handleFull (d : Nat) (x : NodeId) (last : KNode) :
    MergesLe 0 (handleFull d x last) := by
  unfold handleFull
  refine mergesLe_handleFullWith _ _ _ _ _ ?_
  intro q more
  cases d with
  | zero => exact mergesLe_throw _ _
  | succ d => exact mergesLe_appendKlongs d q more

macro "wpFrame3" : tactic => `(tactic| first
  | (with_unfolding_none refine writerWP_of_mergesLe (mergesLe_appendKlongs _ _ _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_mergesLe (mergesLe_handleFull_compact _ _ _ _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_mergesLe (mergesLe_handleFull _ _ _) _ _ _ ?_; intro _ _ _)
  | wpFrame)

theorem mergesLe_appendDeleteKlong (x : NodeId) (depth cv : Nat) :
    MergesLe 0 (appendDeleteKlong x depth cv) := by
  apply mergesLe_of_wp
  intro c w
  unfold appendDeleteKlong
  repeat' first
    | wpSimplify
    | wpFrame3
    | wpSplit
    | split
    | ((try simp only [Nat.add_zero] at *); omega)

theorem mergesLe_emptyKeyNext (x : NodeId) (depth : Nat) :
    MergesLe 0 (emptyKeyNext x depth) := by
  apply mergesLe_of_wp
  intro c w
  unfold emptyKeyNext
  repeat' first
    | wpSimplify
    | wpFrame3
    | wpSplit
    | split
    | ((try simp only [Nat.add_zero] at *); omega)

theorem mergesLe_unlink (x : NodeId) : MergesLe 0 (unlink x) := by
  apply mergesLe_of_wp
  intro c w
  unfold unlink
  repeat' first
    | wpSimplify
    | wpFrame3
    | wpSplit
    | split
    | ((try simp only [Nat.add_zero] at *); omega)

theorem mergesLe_retarget (p src dst : NodeId) : MergesLe 0 (retarget p src dst) := by
  apply mergesLe_of_wp
  intro c w
  unfold retarget
  repeat' first
    | wpSimplify
    | wpFrame3
    | wpSplit
    | split
    | ((try simp only [Nat.add_zero] at *); omega)

theorem mergesLe_canTakeBack (x parent : NodeId) (cv : Nat) :
    MergesLe 0 (canTakeBack x parent cv) := by
  apply mergesLe_of_wp
  intro c w
  unfold canTakeBack
  repeat' first
    | wpSimplify
    | wpFrame3
    | wpSplit
    | split
    | ((try simp only [Nat.add_zero] at *); omega)

theorem mergesLe_takeBack (x parent : NodeId) (cv : Nat) :
    MergesLe 0 (takeBack x parent cv) := by
  apply mergesLe_of_wp
  intro c w
  unfold takeBack
  repeat' first
    | wpSimplify
    | wpFrame3
    | (with_unfolding_none refine writerWP_of_mergesLe (mergesLe_retarget _ _ _) _ _ _ ?_; intro _ _ _)
    | wpSplit
    | split
    | ((try simp only [Nat.add_zero] at *); omega)

theorem mergesLe_descendLte (cv fuel : Nat) (x : NodeId) :
    MergesLe 0 (descendLte cv fuel x) := by
  induction fuel generalizing x with
  | zero => exact mergesLe_throw _ _
  | succ fuel ih =>
    apply mergesLe_of_wp
    intro c w
    unfold descendLte
    repeat' first
      | wpSimplify
      | wpFrame3
      | (with_unfolding_none refine writerWP_of_mergesLe (ih _) _ _ _ ?_; intro _ _ _)
      | wpSplit
      | split
      | ((try simp only [Nat.add_zero] at *); omega)

theorem mergesLe_descendToSegmentRoot (key : Key) (segment : Nat) :
    MergesLe 0 (descendToSegmentRoot key segment) := by
  unfold descendToSegmentRoot
  refine mergesLe_bind0 (mergesLe_read 0) ?_
  intro c
  refine mergesLe_bind0 mergesLe_pathClear ?_
  intro _
  refine mergesLe_bind0 mergesLe_findRoot ?_
  intro root
  apply mergesLe_foldlM
  intro node cv
  refine mergesLe_bind0 (mergesLe_descendLte _ _ _) ?_
  intro leaf
  refine mergesLe_bind0 (mergesLe_getNode 0 leaf) ?_
  intro n
  split
  · exact mergesLe_throw _ _
  · refine mergesLe_bind0 (mergesLe_pathAdd _ _) ?_
    intro _
    exact mergesLe_pure _ _

macro "wpFrame4" : tactic => `(tactic| first
  | (with_unfolding_none refine writerWP_of_mergesLe (mergesLe_unlink _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_mergesLe (mergesLe_retarget _ _ _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_mergesLe (mergesLe_canTakeBack _ _ _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_mergesLe (mergesLe_takeBack _ _ _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_mergesLe (mergesLe_descendLte _ _ _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_mergesLe (mergesLe_descendToSegmentRoot _ _) _ _ _ ?_; intro _ _ _)
  | wpFrame3)

theorem mergesLe_takeBackRoot (x : NodeId) (depth only : Nat) :
    MergesLe 0 (takeBackRoot x depth only) := by
  apply mergesLe_of_wp
  intro c w
  unfold takeBackRoot
  repeat' first
    | wpSimplify
    | wpFrame4
    | wpSplit
    | split
    | ((try simp only [Nat.add_zero] at *); omega)

theorem mergesLe_replaceRoot (x : NodeId) (depth only : Nat) :
    MergesLe 0 (replaceRoot x depth only) := by
  apply mergesLe_of_wp
  intro c w
  unfold replaceRoot
  repeat' first
    | wpSimplify
    | wpFrame4
    | wpSplit
    | split
    | ((try simp only [Nat.add_zero] at *); omega)

theorem mergesLe_collapseRoot (key : Key) (segment fuel : Nat) :
    MergesLe 0 (collapseRoot key segment fuel) := by
  induction fuel with
  | zero => exact mergesLe_throw _ _
  | succ fuel ih =>
    apply mergesLe_of_wp
    intro c w
    unfold collapseRoot
    repeat' first
      | wpSimplify
      | wpFrame4
      | (with_unfolding_none refine writerWP_of_mergesLe (mergesLe_takeBackRoot _ _ _) _ _ _ ?_; intro _ _ _)
      | (with_unfolding_none refine writerWP_of_mergesLe (mergesLe_replaceRoot _ _ _) _ _ _ ?_; intro _ _ _)
      | (with_unfolding_none refine writerWP_of_mergesLe ih _ _ _ ?_; intro _ _ _)
      | wpSplit
      | split
      | ((try simp only [Nat.add_zero] at *); omega)

theorem mergesLe_descendHeight (cv h fuel : Nat) (x : NodeId) :
    MergesLe 0 (descendHeight cv h fuel x) := by
  induction fuel generalizing x with
  | zero => exact mergesLe_throw _ _
  | succ fuel ih =>
    apply mergesLe_of_wp
    intro c w
    unfold descendHeight
    repeat' first
      | wpSimplify
      | wpFrame4
      | (with_unfolding_none refine writerWP_of_mergesLe (ih _) _ _ _ ?_; intro _ _ _)
      | wpSplit
      | split
      | ((try simp only [Nat.add_zero] at *); omega)

theorem mergesLe_descendToHeight (key : Key) (g h : Nat) :
    MergesLe 0 (descendToHeight key g h) := by
  apply mergesLe_of_wp
  intro c w
  unfold descendToHeight
  repeat' first
    | wpSimplify
    | wpFrame4
    | (with_unfolding_none refine writerWP_of_mergesLe (mergesLe_descendHeight _ _ _ _) _ _ _ ?_; intro _ _ _)
    | wpSplit
    | split
    | ((try simp only [Nat.add_zero] at *); omega)

theorem mergesLe_forIn {α β : Type} (xs : List α) (init : β)
    (f : α → β → M (ForInStep β)) (hf : ∀ a b, MergesLe 0 (f a b)) :
    MergesLe 0 (forIn xs init f) := by
  induction xs generalizing init with
  | nil => exact mergesLe_pure _ _
  | cons a xs ih =>
    rw [List.forIn_cons]
    refine mergesLe_bind0 (hf a init) ?_
    intro step
    cases step with
    | done b => exact mergesLe_pure _ _
    | yield b => exact ih b

set_option maxHeartbeats 800000 in
theorem mergesLe_mergeParent (p : NodeId) (depth il cL : Nat) (m1 : NodeId) (ir cR : Nat)
    (m2 : Option (NodeId × Nat)) : MergesLe 0 (mergeParent p depth il cL m1 ir cR m2) := by
  apply mergesLe_of_wp
  intro c w
  unfold mergeParent
  repeat' first
    | wpSimplify
    | wpFrame4
    | wpSplit
    | split
    | ((try simp only [Nat.add_zero] at *); omega)

theorem mergesLe_sibling (p : NodeId) (pn : KNode) (i : Nat) (inner : Bool) :
    MergesLe 0 (sibling p pn i inner) := by
  apply mergesLe_of_wp
  intro c w
  unfold sibling
  repeat' first
    | wpSimplify
    | wpFrame4
    | wpSplit
    | split
    | ((try simp only [Nat.add_zero] at *); omega)

macro "wpFrame5" : tactic => `(tactic| first
  | (with_unfolding_none refine writerWP_of_mergesLe (mergesLe_mergeParent _ _ _ _ _ _ _ _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_mergesLe (mergesLe_sibling _ _ _ _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_mergesLe (mergesLe_descendToHeight _ _ _) _ _ _ ?_; intro _ _ _)
  | (with_unfolding_none refine writerWP_of_mergesLe (mergesLe_collapseRoot _ _ _) _ _ _ ?_; intro _ _ _)
  | wpFrame4)

set_option maxHeartbeats 800000 in
/-- A successful merge increments the counter at most once. -/
theorem mergesLe_merge (x : NodeId) (d : Nat) : MergesLe 1 (merge x d) := by
  apply mergesLe_of_wp
  intro c w
  unfold merge
  repeat' first
    | wpSimplify
    | simp only [List.forIn_cons, List.forIn_nil]
    | wpFrame5
    | wpSplit
    | split
    | ((try simp only [Nat.add_zero] at *); omega)

theorem mergesLe_climb (depth : Nat) : MergesLe 0 (climb depth) := by
  induction depth with
  | zero =>
    apply mergesLe_of_wp
    intro c w
    unfold climb
    repeat' first
      | wpSimplify
      | wpFrame5
      | wpSplit
      | split
      | ((try simp only [Nat.add_zero] at *); omega)
  | succ depth ih =>
    apply mergesLe_of_wp
    intro c w
    unfold climb
    repeat' first
      | wpSimplify
      | wpFrame5
      | (with_unfolding_none refine writerWP_of_mergesLe ih _ _ _ ?_; intro _ _ _)
      | wpSplit
      | split
      | ((try simp only [Nat.add_zero] at *); omega)

theorem mergesLe_segmentCount (path : List (Option Nat × NodeId)) (stop : Nat) :
    MergesLe 0 ((path.take stop).foldlM (fun s e => do
      let n ← getNode e.2
      pure (if n.leaf then s + 1 else s)) 0) := by
  apply mergesLe_foldlM
  intro s e
  refine mergesLe_bind0 (mergesLe_getNode 0 e.2) ?_
  intro n
  exact mergesLe_pure _ _

theorem mergesLe_unlinkLoop (depth tt : Nat) (js : List Nat) :
    MergesLe 0 (forIn js () (fun j _ => do
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
  apply mergesLe_forIn
  intro j b
  apply mergesLe_of_wp
  intro c w
  repeat' first
    | wpSimplify
    | wpFrame5
    | wpSplit
    | split
    | ((try simp only [Nat.add_zero] at *); omega)

theorem mergesLe_setNode (segRoot : NodeId) (cv : Nat) (create : Bool) :
    MergesLe 0 (setNode segRoot cv create) := by
  apply mergesLe_of_wp
  intro c w
  unfold setNode
  repeat' first
    | wpSimplify
    | wpFrame5
    | wpSplit
    | split
    | ((try simp only [Nat.add_zero] at *); omega)

end SIS.Tree
