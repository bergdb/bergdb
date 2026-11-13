/-
The tree model (bergdb 024-12, TP5's writer part): a key node holds at most M
klongs. Through every rule of the writer, each node of the overlay stays
`SizedNode` (SIS/Tree/SizeRules.lean). This file: the writer's primitive
steps, the splits and `appendKlongs`.
-/
import SIS.Tree.SizeRules
import SIS.Tree.WriterGood

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- What the writer's run needs: the thresholds of TP28, and key nodes of at
most M klongs in its view. -/
structure ViewSized (c : Ctx) : Prop where
  params : MergeParamsOK c.p
  view : ViewSizeOK c.p c.view

/-- Every node of the overlay has at most M klongs. -/
def CacheSized (c : Ctx) (w : W) : Prop := WriterSizeOK c.p w

def KeepsSized {α : Type} (f : M α) : Prop :=
  ∀ c w, ViewSized c → CacheSized c w → WriterWP f c w (fun _ v => CacheSized c v)

theorem cacheSized_lookup (c : Ctx) (w : W) (hw : CacheSized c w) (x : NodeId)
    (n : KNode) (hn : w.nodes.lookup x = some n) : SizedNode c.p n := by
  obtain ⟨pre, post, he, _⟩ := List.lookup_eq_some_iff.mp hn
  apply hw (x, n)
  rw [he]
  simp

/-- A node read: from the overlay or the view, at most M klongs; and the
overlay holds it. -/
theorem sized_getNode_lookup (x : NodeId) (c : Ctx) (w : W) (hv : ViewSized c)
    (hw : CacheSized c w) :
    WriterWP (getNode x) c w (fun n v => CacheSized c v ∧ SizedNode c.p n ∧
      v.nodes.lookup x = some n) := by
  unfold getNode
  simp only [writerWP_bind, writerWP_get]
  split
  · rename_i n hn
    simp only [writerWP_pure]
    exact ⟨hw, cacheSized_lookup c w hw x n hn, hn⟩
  · rename_i hnone
    simp only [writerWP_bind, writerWP_read]
    split
    · rename_i nd hn
      split
      · exact writerWP_throw _ _ _ _
      · rename_i hkind
        have hd : nd.isData = false := by cases hd : nd.isData <;> simp_all
        have hl : nd.level ≤ c.p.keyMax := by
          have hh : ¬ c.p.keyMax < nd.level := by
            intro h; simp [h] at hkind
          omega
        have hg := sized_load c.p c.view hv.view x nd (c.p.heightOf nd.level == 0) hn hd hl
        simp only [writerWP_bind, writerWP_set, writerWP_pure]
        refine ⟨?_, hg, by simp [List.lookup_append, hnone]⟩
        intro q hq
        rcases List.mem_append.mp hq with hq | hq
        · exact hw q hq
        · have heq := List.mem_singleton.mp hq
          subst q
          exact hg
    · exact writerWP_throw _ _ _ _

theorem sized_getNode (x : NodeId) (c : Ctx) (w : W) (hv : ViewSized c) (hw : CacheSized c w) :
    WriterWP (getNode x) c w (fun n v => CacheSized c v ∧ SizedNode c.p n ∧
      n.size ≤ c.p.M ∧ TimeFirst n.ks) :=
  writerWP_mono (sized_getNode_lookup x c w hv hw)
    (fun _ _ h => ⟨h.1, h.2.1, h.2.1.1, h.2.1.2⟩)

theorem sized_putNode (x : NodeId) (n : KNode) (c : Ctx) (w : W)
    (post : Unit → W → Prop) (hw : CacheSized c w) (hn : SizedNode c.p n)
    (hp : ∀ r v, CacheSized c v → post r v) : WriterWP (putNode x n) c w post := by
  simp only [putNode, writerWP_modify]
  apply hp
  intro q hq
  unfold upsert at hq
  split at hq
  · obtain ⟨a, ha, he⟩ := List.mem_map.mp hq
    split at he
    · cases he; exact hn
    · cases he; exact hw _ ha
  · rcases List.mem_append.mp hq with hq | hq
    · exact hw q hq
    · have he := List.mem_singleton.mp hq
      subst q; exact hn

theorem sized_newKey (g h : Nat) (leaf : Bool) (ks : List Klong) (c : Ctx) (w : W)
    (post : NodeId → W → Prop) (hw : CacheSized c w) (hks : SizedNode c.p ⟨leaf, ks⟩)
    (hp : ∀ x v, CacheSized c v → post x v) :
    WriterWP (newKey g h leaf ks) c w post := by
  unfold newKey fresh
  wpSimplify
  split <;> wpSimplify
  all_goals
    apply hp
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hw q hq
    · have he := List.mem_singleton.mp hq
      subst q; exact hks

theorem writerWP_of_sized {α : Type} {f : M α} (hf : KeepsSized f)
    (c : Ctx) (w : W) (post : α → W → Prop) (hv : ViewSized c)
    (hw : CacheSized c w) (hp : ∀ r v, CacheSized c v → post r v) :
    WriterWP f c w post := writerWP_mono (hf c w hv hw) hp

macro "szUse " h:term : tactic => `(tactic| (
  (with_unfolding_none refine' writerWP_of_sized $h _ _ _ ?szView ?szState ?szPost)
  case szView => assumption
  case szState => assumption
  intro _ _ _))

macro "szNode" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (getNode _) _ _ _)
  (refine writerWP_mono (sized_getNode _ _ _ ?szView ?szState) ?szPost)
  case szView => assumption
  case szState => assumption
  rintro _ _ ⟨_, _, _, _⟩))

macro "szNeutral" : tactic => `(tactic| (
  intro c w hv hw
  repeat' first
    | wpSimplify
    | szNode
    | exact writerWP_throw _ _ _ _
    | split
    | assumption
    | contradiction))

theorem sized_fresh : KeepsSized fresh := by
  intro c w _ hw
  unfold fresh
  wpSimplify
  exact hw

theorem sized_note (s : String) : KeepsSized (note s) := by
  intro c w _ hw
  simp only [note, writerWP_modify]
  exact hw

theorem sized_takenBack (x : NodeId) : KeepsSized (takenBack x) := by
  intro c w _ hw
  simp only [takenBack, writerWP_modify]
  exact hw

theorem sized_pathClear : KeepsSized pathClear := by
  intro c w _ hw
  simp only [pathClear, writerWP_modify]
  exact hw

theorem sized_pathAdd (cv : Option Nat) (x : NodeId) : KeepsSized (pathAdd cv x) := by
  intro c w _ hw
  simp only [pathAdd, writerWP_modify]
  exact hw

theorem sized_setMadeFor (x : NodeId) (old : Option NodeId) : KeepsSized (setMadeFor x old) := by
  intro c w _ hw
  unfold setMadeFor
  split
  · simp only [writerWP_modify]; exact hw
  · simpa only [writerWP_pure] using hw

theorem sized_newValue (h : Nat) : KeepsSized (newValue h) := by
  intro c w _ hw
  unfold newValue fresh
  wpSimplify
  exact hw

theorem sized_newSuperRoot (x : NodeId) : KeepsSized (newSuperRoot x) := by
  intro c w _ hw
  unfold newSuperRoot note fresh
  wpSimplify
  split <;> wpSimplify
  · exact hw
  · exact hw

theorem sized_ghOf (x : NodeId) : KeepsSized (ghOf x) := by unfold ghOf; szNeutral
theorem sized_replacedBy (x : NodeId) : KeepsSized (replacedBy x) := by
  unfold replacedBy; szNeutral
theorem sized_pathSize : KeepsSized pathSize := by unfold pathSize; szNeutral
theorem sized_pathNode (d : Nat) : KeepsSized (pathNode d) := by
  unfold pathNode; szNeutral
theorem sized_klongAt (d : Nat) : KeepsSized (klongAt d) := by
  unfold klongAt; szNeutral

theorem sized_parentAt (d : Nat) : KeepsSized (parentAt d) := by
  cases d with
  | zero => intro c w hv hw; simpa only [parentAt, writerWP_pure] using hw
  | succ d =>
    intro c w hv hw
    unfold parentAt
    simp only [writerWP_bind]
    szUse (sized_pathNode _)
    simpa only [writerWP_pure] using ‹CacheSized _ _›

theorem sized_findRoot : KeepsSized findRoot := by
  intro c w hv hw
  unfold findRoot
  wpSimplify
  exact sized_pathAdd none _ c w hv hw

theorem sized_throw {α : Type} (e : String) : KeepsSized (throw e : M α) := by
  intro c w hv hw
  exact writerWP_throw _ _ _ _

/-! ## Nodes stored -/

theorem sized_empty (p : Params) (leaf : Bool) : SizedNode p ⟨leaf, []⟩ :=
  ⟨Nat.zero_le _, Or.inl rfl⟩

theorem sized_root3 (p : Params) (leaf : Bool) (t : Time) (a b : Nat) (x y : NodeId)
    (h : 3 ≤ p.M) : SizedNode p ⟨leaf, [.time t, .key a x, .key b y]⟩ :=
  ⟨h, Or.inr ⟨t, _, rfl⟩⟩

theorem sized_halves1 (p : Params) (leaf : Bool) (t : Time) (last : KNode)
    (ins : List (Nat × NodeId)) (h : 1 + last.size / 2 + ins.length ≤ p.M) :
    SizedNode p (halves leaf t last ins).1 :=
  ⟨Nat.le_trans (halves_size leaf t last ins).1 h, (halves_timeFirst leaf t last ins).1⟩

theorem sized_halves2 (p : Params) (leaf : Bool) (t : Time) (last : KNode)
    (ins : List (Nat × NodeId)) (h : 1 + last.size / 2 + ins.length ≤ p.M) :
    SizedNode p (halves leaf t last ins).2.1 :=
  ⟨Nat.le_trans (halves_size leaf t last ins).2 h, (halves_timeFirst leaf t last ins).2⟩

theorem sized_flat (p : Params) (i : Time) (l : KNode) (leaf : Bool) (hf : FlatAt i l.ks)
    (hs : l.size ≤ p.M) : SizedNode p { l with leaf := leaf } := by
  obtain ⟨r, hr, _⟩ := hf
  exact ⟨hs, Or.inr ⟨i, r, hr⟩⟩

theorem sized_flat' (p : Params) (i : Time) (l : KNode) (leaf : Bool) (hf : FlatAt i l.ks)
    (hs : l.size ≤ p.M) : SizedNode p ⟨leaf, l.ks⟩ :=
  sized_flat p i l leaf hf hs

theorem sized_newKlongs (p : Params) (leaf : Bool) (t : Time) (l : List (Nat × NodeId))
    (h : (newKlongs t l).length ≤ p.M) : SizedNode p ⟨leaf, newKlongs t l⟩ :=
  ⟨h, Or.inr ⟨t, _, rfl⟩⟩

theorem sized_fold_add (p : Params) (ins : List (Nat × NodeId)) (t : Time) (n : KNode)
    (h : TimeFirst n.ks) (hs : n.size + ins.length + 1 ≤ p.M) :
    SizedNode p (ins.foldl (fun n (q : Nat × NodeId) => n.add t (.key q.1 q.2)) n) :=
  ⟨Nat.le_trans (fold_add_size ins t n) hs, timeFirst_fold_add ins t n h⟩

/-- Adds klongs to a node with room for them: the node read is the one that
the caller tested. -/
theorem sized_addKeys (x : NodeId) (ins : List (Nat × NodeId)) (c : Ctx) (w : W)
    (_hv : ViewSized c) (hw : CacheSized c w)
    (hroom : ∃ n, w.nodes.lookup x = some n ∧ n.size + ins.length + 1 ≤ c.p.M) :
    WriterWP (addKeys x ins) c w (fun _ v => CacheSized c v) := by
  obtain ⟨n, hn, hs⟩ := hroom
  have hsz := cacheSized_lookup c w hw x n hn
  unfold addKeys getNode
  simp only [writerWP_bind, writerWP_read, writerWP_get, hn, writerWP_pure]
  exact sized_putNode _ _ _ _ _ hw (sized_fold_add c.p ins c.i n hsz.2 hs) (fun _ _ h => h)

/-- The loop of a time split gives a last version at the transaction's
time, with a klong more at most for each klong to insert, and changes no
state. -/
theorem writerWP_replaceOrAdd_size (last : KNode) (ins : List (Nat × NodeId))
    (c : Ctx) (w : W) (hlast : FlatAt c.i last.ks) :
    WriterWP (replaceOrAdd last ins) c w (fun out v => FlatAt c.i out.ks ∧
      out.size ≤ last.size + ins.length ∧ v = w) := by
  unfold replaceOrAdd
  simp only [writerWP_bind, writerWP_read]
  induction ins generalizing last with
  | nil => simp only [List.foldlM_nil, writerWP_pure]; exact ⟨hlast, by simp, trivial⟩
  | cons q ins ih =>
    rw [List.foldlM_cons, writerWP_bind]
    cases hr : replaceKlong last.ks c.i q.1 q.2 with
    | error e => exact writerWP_throw _ _ _ _
    | ok result =>
      cases result with
      | none =>
        simp only [writerWP_pure]
        refine writerWP_mono (ih _ (FlatAt.add_key _ last _ _ hlast)) ?_
        intro out v ⟨h1, h2, h3⟩
        refine ⟨h1, ?_, h3⟩
        have hl := flatAt_lastTime c.i last hlast
        have ha := last.add_size c.i (.key q.1 q.2)
        have hs : last.slack c.i = 0 := by simp [KNode.slack, hl]
        simp only [List.length_cons]
        omega
      | some ks =>
        simp only [writerWP_pure]
        refine writerWP_mono (ih {last with ks := ks} (flatAt_replaceKlong _ _ _ _ _ _ hlast hr)) ?_
        intro out v ⟨h1, h2, h3⟩
        refine ⟨h1, ?_, h3⟩
        have := replaceKlong_length _ _ _ _ _ hr
        simp only [KNode.size, List.length_cons] at h2 this ⊢
        omega

macro "szReplace" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (replaceOrAdd _ _) _ _ _)
  refine writerWP_mono (writerWP_replaceOrAdd_size _ _ _ _ ?szLast) ?szPost
  case szLast => gdFlat
  rintro out v ⟨hout, hsize, heq⟩
  subst v))

/-- Numeric goals: the branch conditions as plain facts, then `omega`. -/
macro "szArith" : tactic => `(tactic| (
  (try simp only [Bool.not_false, Bool.not_true, Bool.true_and, Bool.false_and,
    Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not,
    Bool.false_eq_true, false_implies, true_implies, gt_iff_lt, KNode.size,
    List.length_cons, List.length_nil] at *) <;>
  omega))

syntax "szKs" : tactic
macro_rules
  | `(tactic| szKs) => `(tactic| first
    | assumption
    | exact sized_empty _ _
    | (refine sized_root3 _ _ _ _ _ _ _ ?_; szArith)
    | (refine sized_halves1 _ _ _ _ _ ?_; szArith)
    | (refine sized_halves2 _ _ _ _ _ ?_; szArith)
    | (refine sized_flat _ _ _ _ (by assumption) ?_; szArith)
    | (refine sized_flat' _ _ _ _ (by assumption) ?_; szArith)
    | (apply SizedNode.repoint; szKs)
    | (apply SizedNode.toPrev; szKs))

macro "szStore" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (putNode _ _) _ _ _)
  (with_unfolding_none refine sized_putNode _ _ _ _ _ ?szState ?szInput ?szPost)
  case szState => assumption
  case szInput => szKs
  intro _ _ _))

macro "szCreate" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (newKey _ _ _ _) _ _ _)
  (with_unfolding_none refine sized_newKey _ _ _ _ _ _ _ ?szState ?szInput ?szPost)
  case szState => assumption
  case szInput => szKs
  intro _ _ _))

macro "szCore" : tactic => `(tactic| first
  | szNode
  | szStore
  | szCreate
  | szUse (sized_pathAdd _ _)
  | szUse (sized_ghOf _)
  | szUse (sized_replacedBy _)
  | szUse sized_pathSize
  | szUse (sized_pathNode _)
  | szUse (sized_klongAt _)
  | szUse (sized_parentAt _)
  | szUse sized_findRoot
  | szUse (sized_note _)
  | szUse sized_fresh
  | szUse (sized_newValue _)
  | szUse (sized_newSuperRoot _)
  | szUse (sized_setMadeFor _ _)
  | szUse (sized_takenBack _)
  | szUse sized_pathClear
  | assumption
  | exact writerWP_throw _ _ _ _)

/-! ## A full node -/

set_option maxHeartbeats 1600000 in
/-- Every route of a full node's replacement keeps the overlay's nodes within
M klongs: a last version at the transaction's time, at most two klongs to
insert, at most M + 2 klongs with them, and at most M for a compaction. -/
theorem sized_handleFullWith (up : NodeId → List (Nat × NodeId) → M Unit)
    (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) (last : KNode) (compact : Bool)
    (c : Ctx) (w : W) (hv : ViewSized c) (hw : CacheSized c w)
    (hlast : FlatAt c.i last.ks) (hins : ins.length ≤ 2)
    (hL2 : last.size + ins.length ≤ c.p.M + 2)
    (hC : compact = true → last.size + ins.length ≤ c.p.M)
    (hup : ∀ q more, more.length ≤ 2 → KeepsSized (up q more)) :
    WriterWP (handleFullWith up depth x ins last compact) c w (fun _ v => CacheSized c v) := by
  obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6⟩ := hv.params
  cases compact
  all_goals (try have hC' := hC rfl); clear hC
  all_goals unfold handleFullWith
  all_goals repeat' first
    | wpSimplify
    | szCore
    | szReplace
    | szUse (hup _ _ (by simp))
    | wpSplit
    | split
    | contradiction

/-- Numeric goals on a last version's size. -/
macro "szLV" : tactic => `(tactic| first
  | szArith
  | (refine KNode.lastVersionGivenDel_le _ _ _ _ ?_ ?_ ?_ <;> first | assumption | szArith)
  | (refine KNode.lastVersionGivenDel_add_le _ _ _ _ _ ?_ ?_ ?_ <;> first | assumption | szArith))

macro "szFullWith " hup:term : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (handleFullWith _ _ _ _ _ _) _ _ _)
  (with_unfolding_none refine writerWP_mono (sized_handleFullWith _ _ _ _ _ _ _ _ ?szView ?szState ?szLast ?szIns ?szL2 ?szC $hup) ?szPost)
  case szView => assumption
  case szState => assumption
  case szLast => gdFlat
  case szIns => assumption
  case szL2 => szLV
  case szC => (intro _; szLV)
  intro _ _ _))

theorem sized_addKeys' (x : NodeId) (ins : List (Nat × NodeId)) (c : Ctx) (w : W) (n : KNode)
    (post : Unit → W → Prop) (hv : ViewSized c) (hw : CacheSized c w)
    (hl : w.nodes.lookup x = some n) (hroom : n.size + ins.length + 1 ≤ c.p.M)
    (hp : ∀ r v, CacheSized c v → post r v) : WriterWP (addKeys x ins) c w post :=
  writerWP_mono (sized_addKeys x ins c w hv hw ⟨n, hl, hroom⟩) hp

macro "szAdd" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (addKeys _ _) _ _ _)
  (with_unfolding_none refine sized_addKeys' _ _ _ _ _ _ ?szView ?szState (by assumption) ?szRoom ?szPost)
  case szView => assumption
  case szState => assumption
  case szRoom => szArith
  intro _ _ _))

theorem sized_appendKlongs (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId))
    (hins : ins.length ≤ 2) : KeepsSized (appendKlongs depth x ins) := by
  induction depth generalizing x ins with
  | zero =>
    intro c w hv hw
    rw [appendKlongs_step_dead]
    wpSimplify
    refine writerWP_mono (sized_getNode_lookup x c w hv hw) ?_
    rintro n v ⟨_, _, _⟩
    obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6⟩ := hv.params
    have := ‹SizedNode c.p n›.1
    have := ‹SizedNode c.p n›.2
    repeat' first
      | wpSimplify
      | szFullWith (fun _ _ _ => sized_throw _)
      | szAdd
      | assumption
      | wpSplit
      | split
  | succ depth ih =>
    intro c w hv hw
    rw [appendKlongs_step_dead]
    wpSimplify
    refine writerWP_mono (sized_getNode_lookup x c w hv hw) ?_
    rintro n v ⟨_, _, _⟩
    obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6⟩ := hv.params
    have := ‹SizedNode c.p n›.1
    have := ‹SizedNode c.p n›.2
    repeat' first
      | wpSimplify
      | szFullWith (fun q more hm => ih q more hm)
      | szAdd
      | assumption
      | wpSplit
      | split

/-- A full node's replacement by a last version at the transaction's time
(a delete): at most M + 1 klongs, at most M for a compaction. -/
theorem sized_handleFull (depth : Nat) (x : NodeId) (last : KNode) (compact : Bool)
    (c : Ctx) (w : W) (hv : ViewSized c) (hw : CacheSized c w) (hlast : FlatAt c.i last.ks)
    (hL : last.size ≤ c.p.M + 1) (hC : compact = true → last.size ≤ c.p.M) :
    WriterWP (handleFull depth x last compact) c w (fun _ v => CacheSized c v) := by
  unfold handleFull
  refine sized_handleFullWith _ depth x [] last compact c w hv hw hlast (by simp)
    (by simp only [List.length_nil]; omega) (by simpa using hC) ?_
  intro q more hm
  cases depth with
  | zero => exact sized_throw _
  | succ d => exact sized_appendKlongs _ _ _ hm

end SIS.Tree
