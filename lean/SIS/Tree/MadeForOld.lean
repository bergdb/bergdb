/-
The made-for ids name nodes of before the transaction (bergdb 024-12, the top
theorem's `hMF`): every pair (made, old) that `setMadeFor` records has old below
the transaction's first id B. `setMadeFor` passes `replacedBy x`, a recorded
old id, or `some x` for a node x that the transaction did not make: its first
time klong is not the transaction's, and a `Good` node with a klong whose id is
at or above B has its first time klong at the transaction's time (`lt_of_good`).
The one node of the transaction with no klong is a new segment leaf before its
first klong (`setNode`); no split or merge reaches it, by the sizes of the
callers (`appendKlongs`, at most two klongs at a time, node size at least 4).
-/
import SIS.Tree.WriterTakenOps
import SIS.Tree.MergeRootHeight

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- Every made-for pair names an old node below B. -/
def MFB (B : NodeId) (w : W) : Prop := ∀ q ∈ w.madeFor, q.2 < B

theorem mfb_lookup (B : NodeId) (w : W) (h : MFB B w) : ∀ x o, w.madeFor.lookup x = some o → o < B := by
  intro x o hl
  obtain ⟨pre, post, he, _⟩ := List.lookup_eq_some_iff.mp hl
  exact h (x, o) (by rw [he]; simp)

/-- f keeps `MFB`, with no premise (it records no made-for pair). -/
def KeepsMF (B : NodeId) {α : Type} (f : M α) : Prop :=
  ∀ c w, MFB B w → WriterWP f c w (fun _ v => MFB B v)

theorem writerWP_of_mf {α : Type} {B : NodeId} {f : M α} (hf : KeepsMF B f)
    (c : Ctx) (w : W) (post : α → W → Prop) (hw : MFB B w)
    (hp : ∀ r v, MFB B v → post r v) : WriterWP f c w post :=
  writerWP_mono (hf c w hw) hp

macro "mfPrim" : tactic => `(tactic| (
  intro c w hw
  repeat' first
    | simp only [writerWP_bind, writerWP_pure, writerWP_read, writerWP_get, writerWP_set,
        writerWP_modify]
    | exact writerWP_throw _ _ _ _
    | split
    | exact hw))

theorem mf_getNode (B : NodeId) (x : NodeId) : KeepsMF B (getNode x) := by
  unfold getNode; mfPrim
theorem mf_putNode (B : NodeId) (x : NodeId) (n : KNode) : KeepsMF B (putNode x n) := by
  unfold putNode; mfPrim
theorem mf_fresh (B : NodeId) : KeepsMF B fresh := by
  unfold fresh; mfPrim
theorem mf_newKey (B : NodeId) (g h : Nat) (leaf : Bool) (ks : List Klong) :
    KeepsMF B (newKey g h leaf ks) := by
  unfold newKey fresh; mfPrim
theorem mf_newValue (B : NodeId) (h : Nat) : KeepsMF B (newValue h) := by
  unfold newValue fresh; mfPrim
theorem mf_note (B : NodeId) (s : String) : KeepsMF B (note s) := by
  unfold note; mfPrim
theorem mf_replacedBy (B : NodeId) (x : NodeId) : KeepsMF B (replacedBy x) := by
  unfold replacedBy; mfPrim
theorem mf_pathClear (B : NodeId) : KeepsMF B pathClear := by
  unfold pathClear; mfPrim
theorem mf_pathAdd (B : NodeId) (cv : Option Nat) (x : NodeId) : KeepsMF B (pathAdd cv x) := by
  unfold pathAdd; mfPrim
theorem mf_pathSize (B : NodeId) : KeepsMF B pathSize := by
  unfold pathSize; mfPrim
theorem mf_pathNode (B : NodeId) (d : Nat) : KeepsMF B (pathNode d) := by
  unfold pathNode; mfPrim
theorem mf_klongAt (B : NodeId) (d : Nat) : KeepsMF B (klongAt d) := by
  unfold klongAt; mfPrim
theorem mf_parentAt (B : NodeId) (d : Nat) : KeepsMF B (parentAt d) := by
  unfold parentAt pathNode; mfPrim
theorem mf_newSuperRoot (B : NodeId) (x : NodeId) : KeepsMF B (newSuperRoot x) := by
  unfold newSuperRoot note fresh; mfPrim
theorem mf_findRoot (B : NodeId) : KeepsMF B findRoot := by
  unfold findRoot pathAdd; mfPrim
theorem mf_takenBack (B : NodeId) (x : NodeId) : KeepsMF B (takenBack x) := by
  unfold takenBack; mfPrim
theorem mf_throw (B : NodeId) {α : Type} (e : String) : KeepsMF B (throw e : M α) := by
  intro c w _
  exact writerWP_throw _ _ _ _

/-- `replacedBy x` gives a recorded old id. -/
theorem writerWP_replacedBy_mf (B : NodeId) (x : NodeId) (c : Ctx) (w : W) (hw : MFB B w) :
    WriterWP (replacedBy x) c w (fun r v => v = w ∧ ∀ o, r = some o → o < B) := by
  unfold replacedBy
  simp only [writerWP_bind, writerWP_get, writerWP_pure]
  exact ⟨trivial, fun o h => mfb_lookup B w hw x o h⟩

theorem writerWP_setMadeFor_mf (B : NodeId) (x : NodeId) (old : Option NodeId) (c : Ctx) (w : W)
    (hw : MFB B w) (ho : ∀ o, old = some o → o < B) :
    WriterWP (setMadeFor x old) c w (fun _ v => MFB B v) := by
  unfold setMadeFor
  cases old with
  | none => simp only [writerWP_pure]; exact hw
  | some o =>
    simp only [writerWP_modify]
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact ho o rfl
    · exact hw q hq

macro "mfUse " h:term : tactic => `(tactic| (
  (with_unfolding_none refine' writerWP_of_mf $h _ _ _ ?mfState ?mfPost)
  case mfState => assumption
  intro _ _ _))

macro "mfCore" : tactic => `(tactic| first
  | exact writerWP_throw _ _ _ _
  | mfUse (mf_getNode _ _)
  | mfUse (mf_newKey _ _ _ _ _)
  | mfUse (mf_note _ _)
  | mfUse (mf_fresh _)
  | mfUse (mf_putNode _ _ _)
  | mfUse (mf_newValue _ _)
  | mfUse (mf_replacedBy _ _)
  | mfUse (mf_pathClear _)
  | mfUse (mf_pathAdd _ _ _)
  | mfUse (mf_pathSize _)
  | mfUse (mf_pathNode _ _)
  | mfUse (mf_klongAt _ _)
  | mfUse (mf_parentAt _ _)
  | mfUse (mf_newSuperRoot _ _)
  | mfUse (mf_findRoot _)
  | mfUse (mf_takenBack _ _)
  | assumption)

theorem mf_ghOf (B : NodeId) (x : NodeId) : KeepsMF B (ghOf x) := by
  intro c w hw
  unfold ghOf
  repeat' first | tkSimplify | mfCore | split

theorem mf_addKeys (B : NodeId) (x : NodeId) (ins : List (Nat × NodeId)) :
    KeepsMF B (addKeys x ins) := by
  intro c w hw
  unfold addKeys
  repeat' first | tkSimplify | mfCore | split

theorem mf_foldlM (B : NodeId) {α β : Type} (xs : List α) (f : β → α → M β) (init : β)
    (hf : ∀ b a, KeepsMF B (f b a)) : KeepsMF B (xs.foldlM f init) := by
  induction xs generalizing init with
  | nil => intro c w hw; simpa only [List.foldlM_nil, writerWP_pure] using hw
  | cons a xs ih =>
    intro c w hw
    rw [List.foldlM_cons, writerWP_bind]
    exact writerWP_mono (hf init a c w hw) (fun b v hv => ih b c v hv)

macro "mfFoldWith " extra:tactic : tactic => `(tactic| (
  (with_unfolding_none refine' writerWP_of_mf (mf_foldlM _ _ _ _ ?mfBody) _ _ _ ?mfState ?mfPost)
  case mfBody =>
    intro b a c w hw
    repeat' first
      | tkSimplify
      | mfCore
      | ($extra:tactic)
      | wpSplit
      | split
      | contradiction
  case mfState => assumption
  intro _ _ _))

theorem mf_replaceOrAdd (B : NodeId) (last : KNode) (ins : List (Nat × NodeId)) :
    KeepsMF B (replaceOrAdd last ins) := by
  intro c w hw
  unfold replaceOrAdd
  repeat' first | tkSimplify | mfCore | mfFoldWith fail | wpSplit | split | contradiction

theorem mf_descendLte (B : NodeId) (cv fuel : Nat) (x : NodeId) :
    KeepsMF B (descendLte cv fuel x) := by
  induction fuel generalizing x with
  | zero => exact mf_throw _ _
  | succ fuel ih =>
    intro c w hw
    unfold descendLte
    repeat' first | tkSimplify | mfCore | mfUse (ih _) | wpSplit | split | contradiction

theorem mf_descendToSegmentRoot (B : NodeId) (key : Key) (segment : Nat) :
    KeepsMF B (descendToSegmentRoot key segment) := by
  intro c w hw
  unfold descendToSegmentRoot
  repeat' first
    | tkSimplify
    | mfCore
    | mfFoldWith (mfUse (mf_descendLte _ _ _ _))
    | wpSplit
    | split
    | contradiction

theorem mf_unlink (B : NodeId) (x : NodeId) : KeepsMF B (unlink x) := by
  intro c w hw
  unfold unlink
  repeat' first | tkSimplify | mfCore | wpSplit | split | contradiction

theorem mf_retarget (B : NodeId) (q src dst : NodeId) : KeepsMF B (retarget q src dst) := by
  intro c w hw
  unfold retarget
  repeat' first | tkSimplify | mfCore | wpSplit | split | contradiction

theorem mf_canTakeBack (B : NodeId) (x parent : NodeId) (cv : Nat) :
    KeepsMF B (canTakeBack x parent cv) := by
  intro c w hw
  unfold canTakeBack
  repeat' first | tkSimplify | mfCore | wpSplit | split | contradiction

theorem mf_takeBack (B : NodeId) (x parent : NodeId) (cv : Nat) : KeepsMF B (takeBack x parent cv) := by
  intro c w hw
  unfold takeBack
  repeat' first | tkSimplify | mfCore | mfUse (mf_retarget _ _ _ _) | wpSplit | split | contradiction

theorem mf_takeBackRoot (B : NodeId) (x : NodeId) (depth only : Nat) :
    KeepsMF B (takeBackRoot x depth only) := by
  intro c w hw
  unfold takeBackRoot
  repeat' first | tkSimplify | mfCore | mfUse (mf_retarget _ _ _ _) | wpSplit | split | contradiction

theorem mf_descendHeight (B : NodeId) (cv h fuel : Nat) (x : NodeId) :
    KeepsMF B (descendHeight cv h fuel x) := by
  induction fuel generalizing x with
  | zero => exact mf_throw _ _
  | succ fuel ih =>
    intro c w hw
    unfold descendHeight
    repeat' first
      | tkSimplify | mfCore | mfUse (mf_ghOf _ _) | mfUse (ih _) | wpSplit | split | contradiction

theorem mf_descendToHeight (B : NodeId) (key : Key) (g h : Nat) : KeepsMF B (descendToHeight key g h) := by
  intro c w hw
  unfold descendToHeight
  repeat' first
    | tkSimplify
    | mfCore
    | mfUse (mf_descendToSegmentRoot _ _ _)
    | mfUse (mf_descendHeight _ _ _ _ _)
    | wpSplit
    | split
    | contradiction

theorem mf_sibling (B : NodeId) (q : NodeId) (pn : KNode) (i : Nat) (inner : Bool) :
    KeepsMF B (sibling q pn i inner) := by
  intro c w hw
  unfold sibling
  repeat' first | tkSimplify | mfCore | wpSplit | split | contradiction

theorem mf_climb (B : NodeId) (depth : Nat) : KeepsMF B (climb depth) := by
  induction depth with
  | zero =>
    intro c w hw
    unfold climb
    repeat' first | tkSimplify | mfCore | wpSplit | split | contradiction
  | succ depth ih =>
    intro c w hw
    unfold climb
    repeat' first
      | tkSimplify | mfCore | mfUse (mf_canTakeBack _ _ _ _) | mfUse ih | wpSplit | split | contradiction

/-! ## The sites: a node not of the transaction is below B -/

/-- A `Good` node with a klong whose first time is not the transaction's is a
node of before it, below B. -/
theorem lt_of_good (B : NodeId) (c : Ctx) (x : NodeId) (n : KNode) (hv : ViewGood B c)
    (h : Good B c x n) (hks : n.ks ≠ []) (hf : (n.firstTime == some c.i) = false) : x < B := by
  apply Classical.byContradiction
  intro hx
  have hvx : c.view x = none := by
    cases hvx : c.view x with
    | none => rfl
    | some nd => exact absurd (hv.ids x nd hvx) hx
  have hold := h.old
  simp only [baseKlongs, hvx] at hold
  obtain ⟨k, r, hkr⟩ : ∃ k r, n.ks = k :: r := by
    cases hk : n.ks with
    | nil => exact absurd hk hks
    | cons k r => exact ⟨k, r, rfl⟩
  rw [hkr] at hold
  cases k with
  | time t =>
    simp only [prefixAt, List.takeWhile_cons] at hold
    by_cases ht : t ≤ c.i - 1
    · simp [ht] at hold
    · have hle := h.times t (by rw [hkr]; simp)
      have hpos := hv.pos
      have hti : t = c.i := by omega
      simp [KNode.firstTime, hkr, hti] at hf
  | key cv y => simp [prefixAt] at hold
  | del b => simp [prefixAt] at hold

/-- What a split of x needs of x's cached node: one with no klong is below B. -/
def XOK (B : NodeId) (w : W) (x : NodeId) : Prop :=
  ∀ n, w.nodes.lookup x = some n → n.ks = [] → x < B

/-- `getNode x` gives a node with a klong, or x is below B. -/
theorem writerWP_getNode_xok (B : NodeId) (x : NodeId) (c : Ctx) (w : W) (hv : ViewGood B c)
    (hx : XOK B w x) :
    WriterWP (getNode x) c w (fun n _ => n.ks ≠ [] ∨ x < B) := by
  unfold getNode
  simp only [writerWP_bind, writerWP_get]
  split
  · rename_i n hn
    simp only [writerWP_pure]
    by_cases hk : n.ks = []
    · exact Or.inr (hx n hn hk)
    · exact Or.inl hk
  · simp only [writerWP_bind, writerWP_read]
    split
    · rename_i nd hn
      split
      · exact writerWP_throw _ _ _ _
      · simp only [writerWP_bind, writerWP_set, writerWP_pure]
        exact Or.inr (hv.ids x nd hn)
    · exact writerWP_throw _ _ _ _

theorem mf_site_lt (B : NodeId) (c : Ctx) (x : NodeId) (n : KNode) (hv : ViewGood B c)
    (h : Good B c x n) (hne : n.ks ≠ [] ∨ x < B) (hf : ¬ (n.firstTime == some c.i) = true) : x < B := by
  rcases hne with hne | hlt
  · exact lt_of_good B c x n hv h hne (by simpa using hf)
  · exact hlt

theorem ks_ne_of_live_l (n m : KNode) (h : ¬ (n.live.isEmpty || m.live.isEmpty) = true) : n.ks ≠ [] := by
  intro hk
  obtain ⟨leaf, ks⟩ := n
  simp only at hk; subst hk
  apply h
  simp [KNode.live, KNode.lastVersion, KNode.lastVersionGivenDel]

theorem ks_ne_of_live_r (n m : KNode) (h : ¬ (n.live.isEmpty || m.live.isEmpty) = true) : m.ks ≠ [] := by
  intro hk
  obtain ⟨leaf, ks⟩ := m
  simp only at hk; subst hk
  apply h
  simp [KNode.live, KNode.lastVersion, KNode.lastVersionGivenDel]

/-! ## The walk with the overlay's books -/

/-- f keeps `CacheGood` and `MFB`, with node size at least 4. -/
def KeepsGMF (B : NodeId) {α : Type} (f : M α) : Prop :=
  ∀ c w, 4 ≤ c.p.M → ViewGood B c → CacheGood B c w → MFB B w →
    WriterWP f c w (fun _ v => CacheGood B c v ∧ MFB B v)

theorem keepsGMF_of {α : Type} {B : NodeId} {f : M α} (hg : KeepsGood B f) (hm : KeepsMF B f) :
    KeepsGMF B f :=
  fun c w _ hv hw hmw => writerWP_and (hg c w hv hw) (hm c w hmw)

theorem writerWP_of_gmf {α : Type} {B : NodeId} {f : M α} (hf : KeepsGMF B f)
    (c : Ctx) (w : W) (post : α → W → Prop) (hM : 4 ≤ c.p.M) (hv : ViewGood B c)
    (hw : CacheGood B c w) (hm : MFB B w) (hp : ∀ r v, CacheGood B c v → MFB B v → post r v) :
    WriterWP f c w post :=
  writerWP_mono (hf c w hM hv hw hm) (fun r v h => hp r v h.1 h.2)

theorem writerWP_mf_frame {α : Type} {B : NodeId} {f : M α} {c : Ctx} {w : W}
    {post : α → W → Prop} (hw : MFB B w) (hf : KeepsMF B f)
    (h : WriterWP f c w (fun r v => MFB B v → post r v)) : WriterWP f c w post :=
  fun r v he => h r v he (hf c w hw r v he)

macro "mfFr " pat:term " => " h:term : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP $pat _ _ _)
  refine' writerWP_mf_frame ‹MFB _ _› $h ?_))

macro "mfFrame" : tactic => `(tactic| first
  | mfFr (getNode _) => (mf_getNode _ _)
  | mfFr (putNode _ _) => (mf_putNode _ _ _)
  | mfFr (newKey _ _ _ _) => (mf_newKey _ _ _ _ _)
  | mfFr (newValue _) => (mf_newValue _ _)
  | mfFr fresh => (mf_fresh _)
  | mfFr (note _) => (mf_note _ _)
  | mfFr pathClear => (mf_pathClear _)
  | mfFr (pathAdd _ _) => (mf_pathAdd _ _ _)
  | mfFr pathSize => (mf_pathSize _)
  | mfFr (pathNode _) => (mf_pathNode _ _)
  | mfFr (klongAt _) => (mf_klongAt _ _)
  | mfFr (parentAt _) => (mf_parentAt _ _)
  | mfFr (newSuperRoot _) => (mf_newSuperRoot _ _)
  | mfFr findRoot => (mf_findRoot _)
  | mfFr (ghOf _) => (mf_ghOf _ _)
  | mfFr (addKeys _ _) => (mf_addKeys _ _ _)
  | mfFr (replaceOrAdd _ _) => (mf_replaceOrAdd _ _ _)
  | mfFr (descendLte _ _ _) => (mf_descendLte _ _ _ _)
  | mfFr (descendToSegmentRoot _ _) => (mf_descendToSegmentRoot _ _ _)
  | mfFr (unlink _) => (mf_unlink _ _)
  | mfFr (retarget _ _ _) => (mf_retarget _ _ _ _)
  | mfFr (canTakeBack _ _ _) => (mf_canTakeBack _ _ _ _)
  | mfFr (takeBack _ _ _) => (mf_takeBack _ _ _ _)
  | mfFr (takeBackRoot _ _ _) => (mf_takeBackRoot _ _ _ _)
  | mfFr (descendHeight _ _ _ _) => (mf_descendHeight _ _ _ _ _)
  | mfFr (descendToHeight _ _ _) => (mf_descendToHeight _ _ _ _)
  | mfFr (sibling _ _ _ _) => (mf_sibling _ _ _ _ _)
  | mfFr (climb _) => (mf_climb _ _)
  | mfFr (takenBack _) => (mf_takenBack _ _))

/-- A made-for pair of a node not of the transaction. -/
macro "mfSite" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (setMadeFor _ (some _)) _ _ _)
  (refine writerWP_mono (writerWP_and (good_setMadeFor _ _ _ _ _ (by assumption) (by assumption))
    (writerWP_setMadeFor_mf _ _ _ _ _ (by assumption) ?mfO)) ?mfPost)
  case mfO =>
    intro o ho
    simp only [Option.some.injEq] at ho
    subst ho
    first
      | exact mf_site_lt _ _ _ _ (by assumption) (by assumption) (by assumption) (by assumption)
      | exact mf_site_lt _ _ _ _ (by assumption) (by assumption)
          (Or.inl (ks_ne_of_live_l _ _ (by assumption))) (by assumption)
      | exact mf_site_lt _ _ _ _ (by assumption) (by assumption)
          (Or.inl (ks_ne_of_live_r _ _ (by assumption))) (by assumption)
  rintro _ _ ⟨_, _⟩))

/-- A made-for pair of a recorded old id. -/
macro "mfSiteOld" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (setMadeFor _ _) _ _ _)
  (refine writerWP_mono (writerWP_and (good_setMadeFor _ _ _ _ _ (by assumption) (by assumption))
    (writerWP_setMadeFor_mf _ _ _ _ _ (by assumption) (by assumption))) ?mfPost)
  rintro _ _ ⟨_, _⟩))

macro "mfRepl" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (replacedBy _) _ _ _)
  (refine writerWP_mono (writerWP_and (good_replacedBy _ _ _ _ (by assumption) (by assumption))
    (writerWP_replacedBy_mf _ _ _ _ (by assumption))) ?mfPost)
  rintro _ _ ⟨_, hmfEq, _⟩
  subst hmfEq))

macro "gmfUp " h:term : tactic => `(tactic| (
  (with_unfolding_none refine writerWP_of_gmf ($h _ _ ?gmfL) _ _ _ ?gmfM ?gmfV ?gmfS ?gmfF ?gmfPost)
  case gmfL => simp
  case gmfM => assumption
  case gmfV => assumption
  case gmfS => assumption
  case gmfF => assumption
  intro _ _ _ _))

macro "mfGood" : tactic => `(tactic| first
  | gdLink
  | gdReplace
  | tkGood
  | gdUse (good_takeBack _ _ _ _))

macro "mfStep" : tactic => `(tactic| (mfFrame; mfGood; intro _))

macro "mfDone" : tactic => `(tactic| (
  (with_unfolding_none guard_target = (CacheGood _ _ _ ∧ MFB _ _))
  exact ⟨by assumption, by assumption⟩))

macro "gmfUse " h:term : tactic => `(tactic| (
  (with_unfolding_none refine writerWP_of_gmf $h _ _ _ ?gmfM ?gmfV ?gmfS ?gmfF ?gmfPost)
  case gmfM => assumption
  case gmfV => assumption
  case gmfS => assumption
  case gmfF => assumption
  intro _ _ _ _))

set_option maxHeartbeats 3200000 in
/-- Every route of a full node's replacement keeps `CacheGood` and `MFB`, for a
last version at the transaction's time and a node x with a klong or below B. -/
theorem gmf_handleFullWith (B : NodeId) (up : NodeId → List (Nat × NodeId) → M Unit)
    (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) (last : KNode) (compact : Bool)
    (c : Ctx) (w : W) (hM : 4 ≤ c.p.M) (hv : ViewGood B c) (hw : CacheGood B c w) (hm : MFB B w)
    (hlast : FlatAt c.i last.ks) (hx : XOK B w x)
    (hup : ∀ q more, more.length ≤ 2 → KeepsGMF B (up q more)) :
    WriterWP (handleFullWith up depth x ins last compact) c w
      (fun _ v => CacheGood B c v ∧ MFB B v) := by
  have hpos := hv.pos
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (writerWP_and (writerWP_and (good_getNode B x c w hv hw) (mf_getNode B x c w hm))
    (writerWP_getNode_xok B x c w hv hx)) ?_
  rintro n v ⟨⟨⟨hv1, hgx⟩, hm1⟩, hne⟩
  repeat' first
    | wpSimplify
    | mfDone
    | mfSite
    | mfRepl
    | mfSiteOld
    | exact writerWP_throw _ _ _ _
    | mfStep
    | gmfUp hup
    | wpSplit
    | split
    | contradiction

/-- A node with no klong takes at most two key klongs without passing theta. -/
theorem deadOver_fold_nil (p : Params) (t : Time) (leaf : Bool) (ins : List (Nat × NodeId))
    (h : ins.length ≤ 2) :
    deadOver p (ins.foldl (fun n (q : Nat × NodeId) => n.add t (.key q.1 q.2)) ⟨leaf, []⟩) = false := by
  match ins, h with
  | [], _ => simp [deadOver, KNode.deadCount, lastBitmapOf, KNode.lastBitmap]
  | [(a, y)], _ =>
    simp [deadOver, KNode.deadCount, KNode.add, KNode.lastTime, lastBitmapOf, KNode.lastBitmap]
  | [(a, y), (b, z)], _ =>
    by_cases hab : b = a
    · subst hab
      simp [deadOver, KNode.deadCount, KNode.add, KNode.lastTime, lastBitmapOf, KNode.lastBitmap]
    · simp [deadOver, KNode.deadCount, KNode.add, KNode.lastTime, lastBitmapOf, KNode.lastBitmap, hab]

theorem gmf_throw (B : NodeId) {α : Type} (e : String) : KeepsGMF B (throw e : M α) :=
  fun _ _ _ _ _ _ => writerWP_throw _ _ _ _

/-- The klongs `ins` (at most two) into node x, full or not. -/
theorem gmf_appendKlongs (B : NodeId) (depth : Nat) :
    ∀ (x : NodeId) (ins : List (Nat × NodeId)), ins.length ≤ 2 → KeepsGMF B (appendKlongs depth x ins) := by
  induction depth with
  | zero =>
    intro x ins hl c w hM hv hw hm
    rw [appendKlongs_step_dead]
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_mono (writerWP_and (writerWP_and (good_getNode B x c w hv hw) (mf_getNode B x c w hm))
      (writerWP_getNode_cache x c w)) ?_
    rintro n v ⟨⟨⟨hv1, hgx⟩, hm1⟩, hlk, _, _⟩
    have hxok : (n.ks = [] → False) → XOK B v x := fun h n' hn' hk => by
      rw [hlk] at hn'; cases hn'; exact (h hk).elim
    refine writerWP_if _ _ _ _ _ _ (fun hs => ?_) (fun hs => writerWP_if _ _ _ _ _ _ (fun hd => ?_) (fun _ => ?_))
    · refine gmf_handleFullWith B _ 0 x ins _ false c v hM hv hv1 hm1 (KNode.lastVersion_flatAt _ _)
        (hxok (fun hk => ?_)) (fun _ _ _ => gmf_throw B _)
      simp only [KNode.size, hk, List.length_nil] at hs; omega
    · refine gmf_handleFullWith B _ 0 x ins _ true c v hM hv hv1 hm1 (KNode.lastVersion_flatAt _ _)
        (hxok (fun hk => ?_)) (fun _ _ _ => gmf_throw B _)
      obtain ⟨leaf, ks⟩ := n
      simp only at hk; subst hk
      rw [deadOver_fold_nil _ _ _ _ hl] at hd; cases hd
    · exact keepsGMF_of (good_addKeys B x ins) (mf_addKeys B x ins) c v hM hv hv1 hm1
  | succ depth ih =>
    intro x ins hl c w hM hv hw hm
    rw [appendKlongs_step_dead]
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_mono (writerWP_and (writerWP_and (good_getNode B x c w hv hw) (mf_getNode B x c w hm))
      (writerWP_getNode_cache x c w)) ?_
    rintro n v ⟨⟨⟨hv1, hgx⟩, hm1⟩, hlk, _, _⟩
    have hxok : (n.ks = [] → False) → XOK B v x := fun h n' hn' hk => by
      rw [hlk] at hn'; cases hn'; exact (h hk).elim
    refine writerWP_if _ _ _ _ _ _ (fun hs => ?_) (fun hs => writerWP_if _ _ _ _ _ _ (fun hd => ?_) (fun _ => ?_))
    · refine gmf_handleFullWith B _ (depth + 1) x ins _ false c v hM hv hv1 hm1 (KNode.lastVersion_flatAt _ _)
        (hxok (fun hk => ?_)) (fun q more hq => ih q more hq)
      simp only [KNode.size, hk, List.length_nil] at hs; omega
    · refine gmf_handleFullWith B _ (depth + 1) x ins _ true c v hM hv hv1 hm1 (KNode.lastVersion_flatAt _ _)
        (hxok (fun hk => ?_)) (fun q more hq => ih q more hq)
      obtain ⟨leaf, ks⟩ := n
      simp only at hk; subst hk
      rw [deadOver_fold_nil _ _ _ _ hl] at hd; cases hd
    · exact keepsGMF_of (good_addKeys B x ins) (mf_addKeys B x ins) c v hM hv hv1 hm1

theorem gmf_handleFull (B : NodeId) (depth : Nat) (x : NodeId) (last : KNode) (compact : Bool)
    (c : Ctx) (w : W) (hM : 4 ≤ c.p.M) (hv : ViewGood B c) (hw : CacheGood B c w) (hm : MFB B w)
    (hlast : FlatAt c.i last.ks) (hx : XOK B w x) :
    WriterWP (handleFull depth x last compact) c w (fun _ v => CacheGood B c v ∧ MFB B v) := by
  unfold handleFull
  refine gmf_handleFullWith B _ depth x [] last compact c w hM hv hw hm hlast hx ?_
  intro q more hq
  cases depth with
  | zero => exact gmf_throw B _
  | succ d => exact gmf_appendKlongs B d q more hq

theorem xok_of_lookup (B : NodeId) (w : W) (x : NodeId) (n : KNode) (hlk : w.nodes.lookup x = some n)
    (h : n.ks ≠ []) : XOK B w x := fun n' hn' hk => by
  rw [hlk] at hn'; cases hn'; exact (h hk).elim

theorem ks_ne_of_union (n : KNode) (cv : Nat)
    (h : (!(bitsUnion n.lastBitmap (n.bitsOf cv) == n.lastBitmap)) = true) : n.ks ≠ [] := by
  intro hk
  obtain ⟨leaf, ks⟩ := n
  simp only at hk; subst hk
  simp [KNode.lastBitmap, lastBitmapOf, KNode.bitsOf, bitsUnion] at h

theorem ks_ne_of_bits (n : KNode) (cv e : Nat) (h : (n.bitsOf cv).getLast? = some e) : n.ks ≠ [] := by
  intro hk
  obtain ⟨leaf, ks⟩ := n
  simp only at hk; subst hk
  simp [KNode.bitsOf] at h

theorem ks_ne_of_replace (n : KNode) (t t' : Time) (d : List Nat) (cv : Nat) (y : NodeId)
    (ks : List Klong) (h : replaceKlong (n.lastVersionGivenDel t d).ks t' cv y = .ok (some ks)) :
    n.ks ≠ [] := by
  intro hk
  obtain ⟨leaf, ks0⟩ := n
  simp only at hk; subst hk
  simp [KNode.lastVersionGivenDel, replaceKlong, replaceKlong.go] at h

macro "gmfHandle" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (handleFull _ _ _ _) _ _ _)
  (with_unfolding_none refine writerWP_mono (gmf_handleFull ?ghB _ _ _ _ _ _ ?ghM ?ghV ?ghS ?ghF ?ghL ?ghX) ?ghPost)
  case ghV => assumption
  case ghM => assumption
  case ghS => assumption
  case ghF => assumption
  case ghL => first
    | gdFlat
    | (refine flatAt_rename_after_head _ _ _ _ _ _ _ (by assumption) ?_; gdFlat)
  case ghX => first
    | (refine xok_of_lookup _ _ _ _ (by assumption) ?_
       first
        | exact ks_ne_of_union _ _ (by assumption)
        | exact ks_ne_of_bits _ _ _ (by assumption)
        | exact ks_ne_of_replace _ _ _ _ _ _ _ (by assumption)
        | assumption)
    | skip
  rintro _ _ ⟨_, _⟩))

theorem gmf_appendDeleteKlong (B : NodeId) (x : NodeId) (depth cv : Nat) :
    KeepsGMF B (appendDeleteKlong x depth cv) := by
  intro c w hM hv hw hm
  have hpos := hv.pos
  unfold appendDeleteKlong
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (writerWP_and (writerWP_and (good_getNode B x c w hv hw) (mf_getNode B x c w hm))
    (writerWP_getNode_cache x c w)) ?_
  rintro n v ⟨⟨⟨hv1, hgx⟩, hm1⟩, hlk, _, _⟩
  simp only [note]
  repeat' first
    | wpSimplify
    | mfDone
    | exact writerWP_throw _ _ _ _
    | gmfHandle
    | mfStep
    | wpSplit
    | split
    | contradiction

macro "gmfApp" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (appendKlongs _ _ _) _ _ _)
  (with_unfolding_none refine writerWP_of_gmf (gmf_appendKlongs ?gaB _ _ _ ?gaL) _ _ _ ?gaM ?gaV ?gaS ?gaF ?gaPost)
  case gaV => assumption
  case gaL => simp
  case gaM => assumption
  case gaS => assumption
  case gaF => assumption
  intro _ _ _ _))

theorem gmf_emptyKeyNext (B : NodeId) (x : NodeId) (depth : Nat) : KeepsGMF B (emptyKeyNext x depth) := by
  intro c w hM hv hw hm
  have hpos := hv.pos
  unfold emptyKeyNext
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (writerWP_and (writerWP_and (good_getNode B x c w hv hw) (mf_getNode B x c w hm))
    (writerWP_getNode_cache x c w)) ?_
  rintro n v ⟨⟨⟨hv1, hgx⟩, hm1⟩, hlk, _, _⟩
  simp only [note]
  repeat' first
    | wpSimplify
    | mfDone
    | exact writerWP_throw _ _ _ _
    | gmfHandle
    | mfStep
    | wpSplit
    | split
    | contradiction

set_option maxHeartbeats 1600000 in
theorem gmf_mergeParent (B : NodeId) (q : NodeId) (depth il cL : Nat) (m1 : NodeId) (ir cR : Nat)
    (m2 : Option (NodeId × Nat)) : KeepsGMF B (mergeParent q depth il cL m1 ir cR m2) := by
  intro c w hM hv hw hm
  have hpos := hv.pos
  unfold mergeParent
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (writerWP_and (writerWP_and (good_getNode B q c w hv hw) (mf_getNode B q c w hm))
    (writerWP_getNode_cache q c w)) ?_
  rintro n v ⟨⟨⟨hv1, hgx⟩, hm1⟩, hlk, _, _⟩
  simp only [note]
  repeat' first
    | wpSimplify
    | mfDone
    | exact writerWP_throw _ _ _ _
    | gmfHandle
    | mfStep
    | wpSplit
    | split
    | contradiction

theorem gmf_replaceRoot (B : NodeId) (x : NodeId) (depth only : Nat) : KeepsGMF B (replaceRoot x depth only) := by
  intro c w hM hv hw hm
  unfold replaceRoot
  repeat' first
    | wpSimplify
    | mfDone
    | exact writerWP_throw _ _ _ _
    | gmfApp
    | mfStep
    | wpSplit
    | split
    | contradiction

/-- `sibling` gives a `Good` node. -/
theorem good_sibling_res (B : NodeId) (q : NodeId) (pn : KNode) (i : Nat) (inner : Bool) (c : Ctx) (w : W)
    (hv : ViewGood B c) (hw : CacheGood B c w) :
    WriterWP (sibling q pn i inner) c w (fun r v => CacheGood B c v ∧ Good B c r.1 r.2) := by
  unfold sibling
  simp only [writerWP_bind, writerWP_read]
  split
  · exact writerWP_throw _ _ _ _
  · rename_i s _
    simp only [writerWP_bind]
    refine writerWP_mono (good_getNode B s c w hv hw) ?_
    rintro sn v ⟨hv1, hg⟩
    split
    · exact writerWP_throw _ _ _ _
    · simp only [writerWP_pure]; exact ⟨hv1, hg⟩

macro "gmfSib" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (sibling _ _ _ _) _ _ _)
  refine' writerWP_mf_frame ‹MFB _ _› (mf_sibling _ _ _ _ _) ?_
  (refine writerWP_mono (good_sibling_res _ _ _ _ _ _ _ (by assumption) (by assumption)) ?gsPost)
  rintro ⟨_, _⟩ _ ⟨_, _⟩ _))

set_option maxHeartbeats 3200000 in
theorem gmf_merge (B : NodeId) (x : NodeId) (d : Nat) : KeepsGMF B (merge x d) := by
  intro c w hM hv hw hm
  have hpos := hv.pos
  unfold merge
  repeat' first
    | wpSimplify
    | simp only [List.forIn_cons, List.forIn_nil]
    | mfDone
    | exact writerWP_throw _ _ _ _
    | mfSite
    | mfRepl
    | mfSiteOld
    | gmfSib
    | gmfUse (gmf_mergeParent B _ _ _ _ _ _ _ _)
    | mfStep
    | wpSplit
    | split
    | contradiction


theorem gmf_foldlM (B : NodeId) {α β : Type} (xs : List α) (f : β → α → M β) (init : β)
    (hf : ∀ b a, KeepsGMF B (f b a)) : KeepsGMF B (xs.foldlM f init) := by
  induction xs generalizing init with
  | nil => intro c w _ _ hw hm; simpa only [List.foldlM_nil, writerWP_pure] using ⟨hw, hm⟩
  | cons a xs ih =>
    intro c w hM hv hw hm
    rw [List.foldlM_cons, writerWP_bind]
    exact writerWP_mono (hf init a c w hM hv hw hm) (fun b v hh => ih b c v hM hv hh.1 hh.2)

theorem gmf_forIn (B : NodeId) {α β : Type} (xs : List α) (init : β)
    (f : α → β → M (ForInStep β)) (c : Ctx) (hM : 4 ≤ c.p.M) (hv : ViewGood B c)
    (hf : ∀ a b w, CacheGood B c w → MFB B w →
      WriterWP (f a b) c w (fun _ v => CacheGood B c v ∧ MFB B v))
    (w : W) (hw : CacheGood B c w) (hm : MFB B w) :
    WriterWP (forIn xs init f) c w (fun _ v => CacheGood B c v ∧ MFB B v) := by
  induction xs generalizing init w with
  | nil => simpa only [List.forIn_nil, writerWP_pure] using ⟨hw, hm⟩
  | cons a xs ih =>
    rw [List.forIn_cons, writerWP_bind]
    refine writerWP_mono (hf a init w hw hm) ?_
    intro step v hh
    cases step with
    | done b => simpa only [writerWP_pure] using hh
    | yield b => exact ih b v hh.1 hh.2

macro "gmfFoldWith " extra:tactic : tactic => `(tactic| (
  (with_unfolding_none refine' writerWP_of_gmf (gmf_foldlM _ _ _ _ ?gfBody) _ _ _ ?gfM ?gfV ?gfS ?gfF ?gfPost)
  case gfBody =>
    intro b a c w hM hv hw hm
    repeat' first
      | wpSimplify
      | exact writerWP_throw _ _ _ _
      | ($extra:tactic)
      | mfStep
      | wpSplit
      | split
      | contradiction
      | mfDone
  case gfM => assumption
  case gfV => assumption
  case gfS => assumption
  case gfF => assumption
  intro _ _ _ _))

macro "gmfForWith " extra:tactic : tactic => `(tactic| (
  (with_unfolding_none refine writerWP_mono (gmf_forIn ?gfB _ _ _ _ ?gfM ?gfV ?gfBody _ ?gfS ?gfF) ?gfPost)
  case gfV => assumption
  case gfM => assumption
  case gfBody =>
    intro a b w hw hm
    repeat' first
      | wpSimplify
      | exact writerWP_throw _ _ _ _
      | ($extra:tactic)
      | mfStep
      | wpSplit
      | split
      | contradiction
      | mfDone
  case gfS => assumption
  case gfF => assumption
  rintro _ _ ⟨_, _⟩))

theorem gmf_setNode (B : NodeId) (segRoot : NodeId) (cv : Nat) (create : Bool) :
    KeepsGMF B (setNode segRoot cv create) := by
  intro c w hM hv hw hm
  have hpos := hv.pos
  unfold setNode
  repeat' first
    | wpSimplify
    | mfDone
    | exact writerWP_throw _ _ _ _
    | gmfApp
    | mfStep
    | wpSplit
    | split
    | contradiction


theorem gmf_mergeUp (B : NodeId) (key : Key) (g : Nat) :
    ∀ fuel h merged, KeepsGMF B (mergeUp key g fuel h merged) := by
  intro fuel
  induction fuel with
  | zero => intro h merged; exact gmf_throw B _
  | succ fuel ih =>
    intro h merged c w hM hv hw hm
    unfold mergeUp
    repeat' first
      | wpSimplify
      | mfDone
      | exact writerWP_throw _ _ _ _
      | gmfUse (gmf_merge B _ _)
      | gmfUse (ih _ _)
      | mfStep
      | wpSplit
      | split
      | contradiction

theorem gmf_collapseRoot (B : NodeId) (key : Key) (segment : Nat) :
    ∀ fuel, KeepsGMF B (collapseRoot key segment fuel) := by
  intro fuel
  induction fuel with
  | zero => exact gmf_throw B _
  | succ fuel ih =>
    intro c w hM hv hw hm
    unfold collapseRoot
    repeat' first
      | wpSimplify
      | mfDone
      | exact writerWP_throw _ _ _ _
      | mfRepl
      | (mfFr (takeBackRoot _ _ _) => (mf_takeBackRoot _ _ _ _)
         refine writerWP_mono (good_takeBackRoot B _ _ _ _ _ hv (by assumption)
           (Blank.ge B _ _ hv (blank_of_firstTime B _ _ _ hv.pos (by assumption) (by assumption)))) ?_
         intro _ _ _ _)
      | gmfUse (gmf_replaceRoot B _ _ _)
      | gmfUse ih
      | mfStep
      | wpSplit
      | split
      | contradiction

theorem gmf_afterDelete (B : NodeId) (key : Key) (g h : Nat) : KeepsGMF B (afterDelete key g h) := by
  intro c w hM hv hw hm
  unfold afterDelete
  repeat' first
    | wpSimplify
    | mfDone
    | gmfUse (gmf_mergeUp B _ _ _ _ _)
    | gmfUse (gmf_collapseRoot B _ _ _)
    | wpSplit
    | split
    | contradiction

set_option maxHeartbeats 1600000 in
theorem gmf_deleteUpward (B : NodeId) (leaf : NodeId) (depth cv : Nat) (key : Key) :
    KeepsGMF B (deleteUpward leaf depth cv key) := by
  intro c w hM hv hw hm
  unfold deleteUpward
  repeat' first
    | wpSimplify
    | mfDone
    | exact writerWP_throw _ _ _ _
    | gmfUse (gmf_afterDelete B _ _ _)
    | gmfUse (gmf_mergeUp B _ _ _ _ _)
    | gmfUse (gmf_collapseRoot B _ _ _)
    | gmfUse (gmf_appendDeleteKlong B _ _ _)
    | gmfUse (gmf_emptyKeyNext B _ _)
    | gmfFoldWith fail
    | gmfForWith fail
    | mfStep
    | wpSplit
    | split
    | contradiction

theorem gmf_setValue (B : NodeId) (segRoot : NodeId) (cv : Nat) (key : Key) (value : Option Nat) :
    KeepsGMF B (setValue segRoot cv key value) := by
  intro c w hM hv hw hm
  have hpos := hv.pos
  unfold setValue
  repeat' first
    | wpSimplify
    | mfDone
    | exact writerWP_throw _ _ _ _
    | gmfApp
    | gmfUse (gmf_deleteUpward B _ _ _ _)
    | mfStep
    | wpSplit
    | split
    | contradiction

theorem gmf_putSegs (B : NodeId) (key : Key) (value : Option Nat) (segs : List Nat)
    (segRoot : NodeId) : KeepsGMF B (putSegs key value segs segRoot) := by
  induction segs generalizing segRoot with
  | nil => exact gmf_throw B _
  | cons cv rest ih =>
    cases rest with
    | nil => exact gmf_setValue B _ _ _ _
    | cons cv2 rest =>
      intro c w hM hv hw hm
      unfold putSegs
      repeat' first
        | wpSimplify
        | mfDone
        | exact writerWP_throw _ _ _ _
        | gmfUse (gmf_setNode B _ _ _)
        | gmfUse (ih _)
        | mfStep
        | wpSplit
        | split
        | contradiction

theorem gmf_putKv (B : NodeId) (op : Op) : KeepsGMF B (putKv op) := by
  cases op <;> (intro c w hM hv hw hm; unfold putKv)
  all_goals
    repeat' first
      | wpSimplify
      | mfDone
      | exact writerWP_throw _ _ _ _
      | gmfUse (gmf_putSegs B _ _ _ _)
      | mfStep
      | wpSplit
      | split
      | contradiction

theorem gmf_ops (B : NodeId) (ops : List Op) : KeepsGMF B (ops.mapM putKv) := by
  induction ops with
  | nil => intro c w _ _ hw hm; simpa only [List.mapM_nil, writerWP_pure] using ⟨hw, hm⟩
  | cons op ops ih =>
    intro c w hM hv hw hm
    rw [List.mapM_cons, writerWP_bind]
    refine writerWP_mono (gmf_putKv B op c w hM hv hw hm) ?_
    intro noop v hh
    have hi := ih c v hM hv hh.1 hh.2
    simpa only [writerWP_bind, writerWP_pure] using hi

end SIS.Tree
