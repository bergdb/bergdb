/-
The made-for ids name nodes of the view (bergdb 024-12, `hchk`'s `checkOld3`):
putinv2's walk of MadeForOld.lean with the made-for pair's old id also a node of
the view. `setMadeFor` passes `replacedBy x`, a recorded old id, or `some x` for a
node x that the transaction did not make: below B (`lt_of_good`), and so, by its
`Good` origin, a key node of the view (`mfv_site`). `stateOK_madeForView` is the
statement at every state between operations.
-/
import SIS.Tree.WriterTakenOps
import SIS.Tree.MergeRootHeight

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- Every made-for pair names an old node below B. -/
def MFV (B : NodeId) (c : Ctx) (w : W) : Prop := ∀ q ∈ w.madeFor, q.2 < B ∧ (c.view q.2).isSome = true

theorem mfv_lookup (B : NodeId) (c : Ctx) (w : W) (h : MFV B c w) :
    ∀ x o, w.madeFor.lookup x = some o → o < B ∧ (c.view o).isSome = true := by
  intro x o hl
  obtain ⟨pre, post, he, _⟩ := List.lookup_eq_some_iff.mp hl
  exact h (x, o) (by rw [he]; simp)

/-- f keeps `MFB`, with no premise (it records no made-for pair). -/
def KeepsMFV (B : NodeId) {α : Type} (f : M α) : Prop :=
  ∀ c w, MFV B c w → WriterWP f c w (fun _ v => MFV B c v)

theorem writerWP_of_mfV {α : Type} {B : NodeId} {f : M α} (hf : KeepsMFV B f)
    (c : Ctx) (w : W) (post : α → W → Prop) (hw : MFV B c w)
    (hp : ∀ r v, MFV B c v → post r v) : WriterWP f c w post :=
  writerWP_mono (hf c w hw) hp

macro "mfPrimV" : tactic => `(tactic| (
  intro c w hw
  repeat' first
    | simp only [writerWP_bind, writerWP_pure, writerWP_read, writerWP_get, writerWP_set,
        writerWP_modify]
    | exact writerWP_throw _ _ _ _
    | split
    | exact hw))

theorem mf_getNodeV (B : NodeId) (x : NodeId) : KeepsMFV B (getNode x) := by
  unfold getNode; mfPrimV
theorem mf_putNodeV (B : NodeId) (x : NodeId) (n : KNode) : KeepsMFV B (putNode x n) := by
  unfold putNode; mfPrimV
theorem mf_freshV (B : NodeId) : KeepsMFV B fresh := by
  unfold fresh; mfPrimV
theorem mf_newKeyV (B : NodeId) (g h : Nat) (leaf : Bool) (ks : List Klong) :
    KeepsMFV B (newKey g h leaf ks) := by
  unfold newKey fresh; mfPrimV
theorem mf_newValueV (B : NodeId) (h : Nat) : KeepsMFV B (newValue h) := by
  unfold newValue fresh; mfPrimV
theorem mf_noteV (B : NodeId) (s : String) : KeepsMFV B (note s) := by
  unfold note; mfPrimV
theorem mf_replacedByV (B : NodeId) (x : NodeId) : KeepsMFV B (replacedBy x) := by
  unfold replacedBy; mfPrimV
theorem mf_pathClearV (B : NodeId) : KeepsMFV B pathClear := by
  unfold pathClear; mfPrimV
theorem mf_pathAddV (B : NodeId) (cv : Option Nat) (x : NodeId) : KeepsMFV B (pathAdd cv x) := by
  unfold pathAdd; mfPrimV
theorem mf_pathSizeV (B : NodeId) : KeepsMFV B pathSize := by
  unfold pathSize; mfPrimV
theorem mf_pathNodeV (B : NodeId) (d : Nat) : KeepsMFV B (pathNode d) := by
  unfold pathNode; mfPrimV
theorem mf_klongAtV (B : NodeId) (d : Nat) : KeepsMFV B (klongAt d) := by
  unfold klongAt; mfPrimV
theorem mf_parentAtV (B : NodeId) (d : Nat) : KeepsMFV B (parentAt d) := by
  unfold parentAt pathNode; mfPrimV
theorem mf_newSuperRootV (B : NodeId) (x : NodeId) : KeepsMFV B (newSuperRoot x) := by
  unfold newSuperRoot note fresh; mfPrimV
theorem mf_findRootV (B : NodeId) : KeepsMFV B findRoot := by
  unfold findRoot pathAdd; mfPrimV
theorem mf_takenBackV (B : NodeId) (x : NodeId) : KeepsMFV B (takenBack x) := by
  unfold takenBack; mfPrimV
theorem mf_throwV (B : NodeId) {α : Type} (e : String) : KeepsMFV B (throw e : M α) := by
  intro c w _
  exact writerWP_throw _ _ _ _

/-- `replacedBy x` gives a recorded old id. -/
theorem writerWP_replacedBy_mfV (B : NodeId) (x : NodeId) (c : Ctx) (w : W) (hw : MFV B c w) :
    WriterWP (replacedBy x) c w (fun r v => v = w ∧ ∀ o, r = some o → o < B ∧ (c.view o).isSome = true) := by
  unfold replacedBy
  simp only [writerWP_bind, writerWP_get, writerWP_pure]
  exact ⟨trivial, fun o h => mfv_lookup B c w hw x o h⟩

theorem writerWP_setMadeFor_mfV (B : NodeId) (x : NodeId) (old : Option NodeId) (c : Ctx) (w : W)
    (hw : MFV B c w) (ho : ∀ o, old = some o → o < B ∧ (c.view o).isSome = true) :
    WriterWP (setMadeFor x old) c w (fun _ v => MFV B c v) := by
  unfold setMadeFor
  cases old with
  | none => simp only [writerWP_pure]; exact hw
  | some o =>
    simp only [writerWP_modify]
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact ho o rfl
    · exact hw q hq

macro "mfUseV " h:term : tactic => `(tactic| (
  (with_unfolding_none refine' writerWP_of_mfV $h _ _ _ ?mfState ?mfPost)
  case mfState => assumption
  intro _ _ _))

macro "mfCoreV" : tactic => `(tactic| first
  | exact writerWP_throw _ _ _ _
  | mfUseV (mf_getNodeV _ _)
  | mfUseV (mf_newKeyV _ _ _ _ _)
  | mfUseV (mf_noteV _ _)
  | mfUseV (mf_freshV _)
  | mfUseV (mf_putNodeV _ _ _)
  | mfUseV (mf_newValueV _ _)
  | mfUseV (mf_replacedByV _ _)
  | mfUseV (mf_pathClearV _)
  | mfUseV (mf_pathAddV _ _ _)
  | mfUseV (mf_pathSizeV _)
  | mfUseV (mf_pathNodeV _ _)
  | mfUseV (mf_klongAtV _ _)
  | mfUseV (mf_parentAtV _ _)
  | mfUseV (mf_newSuperRootV _ _)
  | mfUseV (mf_findRootV _)
  | mfUseV (mf_takenBackV _ _)
  | assumption)

theorem mf_ghOfV (B : NodeId) (x : NodeId) : KeepsMFV B (ghOf x) := by
  intro c w hw
  unfold ghOf
  repeat' first | tkSimplify | mfCoreV | split

theorem mf_addKeysV (B : NodeId) (x : NodeId) (ins : List (Nat × NodeId)) :
    KeepsMFV B (addKeys x ins) := by
  intro c w hw
  unfold addKeys
  repeat' first | tkSimplify | mfCoreV | split

theorem mf_foldlMV (B : NodeId) {α β : Type} (xs : List α) (f : β → α → M β) (init : β)
    (hf : ∀ b a, KeepsMFV B (f b a)) : KeepsMFV B (xs.foldlM f init) := by
  induction xs generalizing init with
  | nil => intro c w hw; simpa only [List.foldlM_nil, writerWP_pure] using hw
  | cons a xs ih =>
    intro c w hw
    rw [List.foldlM_cons, writerWP_bind]
    exact writerWP_mono (hf init a c w hw) (fun b v hv => ih b c v hv)

macro "mfFoldWithV " extra:tactic : tactic => `(tactic| (
  (with_unfolding_none refine' writerWP_of_mfV (mf_foldlMV _ _ _ _ ?mfBody) _ _ _ ?mfState ?mfPost)
  case mfBody =>
    intro b a c w hw
    repeat' first
      | tkSimplify
      | mfCoreV
      | ($extra:tactic)
      | wpSplit
      | split
      | contradiction
  case mfState => assumption
  intro _ _ _))

theorem mf_replaceOrAddV (B : NodeId) (last : KNode) (ins : List (Nat × NodeId)) :
    KeepsMFV B (replaceOrAdd last ins) := by
  intro c w hw
  unfold replaceOrAdd
  repeat' first | tkSimplify | mfCoreV | mfFoldWithV fail | wpSplit | split | contradiction

theorem mf_descendLteV (B : NodeId) (cv fuel : Nat) (x : NodeId) :
    KeepsMFV B (descendLte cv fuel x) := by
  induction fuel generalizing x with
  | zero => exact mf_throwV _ _
  | succ fuel ih =>
    intro c w hw
    unfold descendLte
    repeat' first | tkSimplify | mfCoreV | mfUseV (ih _) | wpSplit | split | contradiction

theorem mf_descendToSegmentRootV (B : NodeId) (key : Key) (segment : Nat) :
    KeepsMFV B (descendToSegmentRoot key segment) := by
  intro c w hw
  unfold descendToSegmentRoot
  repeat' first
    | tkSimplify
    | mfCoreV
    | mfFoldWithV (mfUseV (mf_descendLteV _ _ _ _))
    | wpSplit
    | split
    | contradiction

theorem mf_unlinkV (B : NodeId) (x : NodeId) : KeepsMFV B (unlink x) := by
  intro c w hw
  unfold unlink
  repeat' first | tkSimplify | mfCoreV | wpSplit | split | contradiction

theorem mf_retargetV (B : NodeId) (q src dst : NodeId) : KeepsMFV B (retarget q src dst) := by
  intro c w hw
  unfold retarget
  repeat' first | tkSimplify | mfCoreV | wpSplit | split | contradiction

theorem mf_canTakeBackV (B : NodeId) (x parent : NodeId) (cv : Nat) :
    KeepsMFV B (canTakeBack x parent cv) := by
  intro c w hw
  unfold canTakeBack
  repeat' first | tkSimplify | mfCoreV | wpSplit | split | contradiction

theorem mf_takeBackV (B : NodeId) (x parent : NodeId) (cv : Nat) : KeepsMFV B (takeBack x parent cv) := by
  intro c w hw
  unfold takeBack
  repeat' first | tkSimplify | mfCoreV | mfUseV (mf_retargetV _ _ _ _) | wpSplit | split | contradiction

theorem mf_takeBackRootV (B : NodeId) (x : NodeId) (depth only : Nat) :
    KeepsMFV B (takeBackRoot x depth only) := by
  intro c w hw
  unfold takeBackRoot
  repeat' first | tkSimplify | mfCoreV | mfUseV (mf_retargetV _ _ _ _) | wpSplit | split | contradiction

theorem mf_descendHeightV (B : NodeId) (cv h fuel : Nat) (x : NodeId) :
    KeepsMFV B (descendHeight cv h fuel x) := by
  induction fuel generalizing x with
  | zero => exact mf_throwV _ _
  | succ fuel ih =>
    intro c w hw
    unfold descendHeight
    repeat' first
      | tkSimplify | mfCoreV | mfUseV (mf_ghOfV _ _) | mfUseV (ih _) | wpSplit | split | contradiction

theorem mf_descendToHeightV (B : NodeId) (key : Key) (g h : Nat) : KeepsMFV B (descendToHeight key g h) := by
  intro c w hw
  unfold descendToHeight
  repeat' first
    | tkSimplify
    | mfCoreV
    | mfUseV (mf_descendToSegmentRootV _ _ _)
    | mfUseV (mf_descendHeightV _ _ _ _ _)
    | wpSplit
    | split
    | contradiction

theorem mf_siblingV (B : NodeId) (q : NodeId) (pn : KNode) (i : Nat) (inner : Bool) :
    KeepsMFV B (sibling q pn i inner) := by
  intro c w hw
  unfold sibling
  repeat' first | tkSimplify | mfCoreV | wpSplit | split | contradiction

theorem mf_climbV (B : NodeId) (depth : Nat) : KeepsMFV B (climb depth) := by
  induction depth with
  | zero =>
    intro c w hw
    unfold climb
    repeat' first | tkSimplify | mfCoreV | wpSplit | split | contradiction
  | succ depth ih =>
    intro c w hw
    unfold climb
    repeat' first
      | tkSimplify | mfCoreV | mfUseV (mf_canTakeBackV _ _ _ _) | mfUseV ih | wpSplit | split | contradiction

/-! ## The sites: a node not of the transaction is below B -/

/-- A `Good` node with a klong whose first time is not the transaction's is a
node of before it, below B. -/
theorem lt_of_goodV (B : NodeId) (c : Ctx) (x : NodeId) (n : KNode) (hv : ViewGood B c)
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
def XOKV (B : NodeId) (w : W) (x : NodeId) : Prop :=
  ∀ n, w.nodes.lookup x = some n → n.ks = [] → x < B

/-- `getNode x` gives a node with a klong, or x is below B. -/
theorem writerWP_getNode_xokV (B : NodeId) (x : NodeId) (c : Ctx) (w : W) (hv : ViewGood B c)
    (hx : XOKV B w x) :
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

theorem mf_site_ltV (B : NodeId) (c : Ctx) (x : NodeId) (n : KNode) (hv : ViewGood B c)
    (h : Good B c x n) (hne : n.ks ≠ [] ∨ x < B) (hf : ¬ (n.firstTime == some c.i) = true) : x < B := by
  rcases hne with hne | hlt
  · exact lt_of_goodV B c x n hv h hne (by simpa using hf)
  · exact hlt

/-- At a made-for site of a node not of the transaction: below B, and a key node
of the view by its origin. -/
theorem mf_site_vV (B : NodeId) (c : Ctx) (x : NodeId) (n : KNode) (hv : ViewGood B c)
    (h : Good B c x n) (hne : n.ks ≠ [] ∨ x < B) (hf : ¬ (n.firstTime == some c.i) = true) :
    x < B ∧ (c.view x).isSome = true := by
  have hlt := mf_site_ltV B c x n hv h hne hf
  refine ⟨hlt, ?_⟩
  rcases h.origin with ⟨nd, hnd, _, _⟩ | hB
  · rw [hnd]; rfl
  · omega

theorem ks_ne_of_live_lV (n m : KNode) (h : ¬ (n.live.isEmpty || m.live.isEmpty) = true) : n.ks ≠ [] := by
  intro hk
  obtain ⟨leaf, ks⟩ := n
  simp only at hk; subst hk
  apply h
  simp [KNode.live, KNode.lastVersion, KNode.lastVersionGivenDel]

theorem ks_ne_of_live_rV (n m : KNode) (h : ¬ (n.live.isEmpty || m.live.isEmpty) = true) : m.ks ≠ [] := by
  intro hk
  obtain ⟨leaf, ks⟩ := m
  simp only at hk; subst hk
  apply h
  simp [KNode.live, KNode.lastVersion, KNode.lastVersionGivenDel]

/-! ## The walk with the overlay's books -/

/-- f keeps `CacheGood` and `MFB`, with node size at least 4. -/
def KeepsGMFV (B : NodeId) {α : Type} (f : M α) : Prop :=
  ∀ c w, 4 ≤ c.p.M → ViewGood B c → CacheGood B c w → MFV B c w →
    WriterWP f c w (fun _ v => CacheGood B c v ∧ MFV B c v)

theorem keepsGMF_ofV {α : Type} {B : NodeId} {f : M α} (hg : KeepsGood B f) (hm : KeepsMFV B f) :
    KeepsGMFV B f :=
  fun c w _ hv hw hmw => writerWP_and (hg c w hv hw) (hm c w hmw)

theorem writerWP_of_gmfV {α : Type} {B : NodeId} {f : M α} (hf : KeepsGMFV B f)
    (c : Ctx) (w : W) (post : α → W → Prop) (hM : 4 ≤ c.p.M) (hv : ViewGood B c)
    (hw : CacheGood B c w) (hm : MFV B c w) (hp : ∀ r v, CacheGood B c v → MFV B c v → post r v) :
    WriterWP f c w post :=
  writerWP_mono (hf c w hM hv hw hm) (fun r v h => hp r v h.1 h.2)

theorem writerWP_mf_frameV {α : Type} {B : NodeId} {f : M α} {c : Ctx} {w : W}
    {post : α → W → Prop} (hw : MFV B c w) (hf : KeepsMFV B f)
    (h : WriterWP f c w (fun r v => MFV B c v → post r v)) : WriterWP f c w post :=
  fun r v he => h r v he (hf c w hw r v he)

macro "mfFrV " pat:term " => " h:term : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP $pat _ _ _)
  refine' writerWP_mf_frameV ‹MFV _ _ _› $h ?_))

macro "mfFrameV" : tactic => `(tactic| first
  | mfFrV (getNode _) => (mf_getNodeV _ _)
  | mfFrV (putNode _ _) => (mf_putNodeV _ _ _)
  | mfFrV (newKey _ _ _ _) => (mf_newKeyV _ _ _ _ _)
  | mfFrV (newValue _) => (mf_newValueV _ _)
  | mfFrV fresh => (mf_freshV _)
  | mfFrV (note _) => (mf_noteV _ _)
  | mfFrV pathClear => (mf_pathClearV _)
  | mfFrV (pathAdd _ _) => (mf_pathAddV _ _ _)
  | mfFrV pathSize => (mf_pathSizeV _)
  | mfFrV (pathNode _) => (mf_pathNodeV _ _)
  | mfFrV (klongAt _) => (mf_klongAtV _ _)
  | mfFrV (parentAt _) => (mf_parentAtV _ _)
  | mfFrV (newSuperRoot _) => (mf_newSuperRootV _ _)
  | mfFrV findRoot => (mf_findRootV _)
  | mfFrV (ghOf _) => (mf_ghOfV _ _)
  | mfFrV (addKeys _ _) => (mf_addKeysV _ _ _)
  | mfFrV (replaceOrAdd _ _) => (mf_replaceOrAddV _ _ _)
  | mfFrV (descendLte _ _ _) => (mf_descendLteV _ _ _ _)
  | mfFrV (descendToSegmentRoot _ _) => (mf_descendToSegmentRootV _ _ _)
  | mfFrV (unlink _) => (mf_unlinkV _ _)
  | mfFrV (retarget _ _ _) => (mf_retargetV _ _ _ _)
  | mfFrV (canTakeBack _ _ _) => (mf_canTakeBackV _ _ _ _)
  | mfFrV (takeBack _ _ _) => (mf_takeBackV _ _ _ _)
  | mfFrV (takeBackRoot _ _ _) => (mf_takeBackRootV _ _ _ _)
  | mfFrV (descendHeight _ _ _ _) => (mf_descendHeightV _ _ _ _ _)
  | mfFrV (descendToHeight _ _ _) => (mf_descendToHeightV _ _ _ _)
  | mfFrV (sibling _ _ _ _) => (mf_siblingV _ _ _ _ _)
  | mfFrV (climb _) => (mf_climbV _ _)
  | mfFrV (takenBack _) => (mf_takenBackV _ _))

/-- A made-for pair of a node not of the transaction. -/
macro "mfSiteV" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (setMadeFor _ (some _)) _ _ _)
  (refine writerWP_mono (writerWP_and (good_setMadeFor _ _ _ _ _ (by assumption) (by assumption))
    (writerWP_setMadeFor_mfV _ _ _ _ _ (by assumption) ?mfO)) ?mfPost)
  case mfO =>
    intro o ho
    simp only [Option.some.injEq] at ho
    subst ho
    first
      | exact mf_site_vV _ _ _ _ (by assumption) (by assumption) (by assumption) (by assumption)
      | exact mf_site_vV _ _ _ _ (by assumption) (by assumption)
          (Or.inl (ks_ne_of_live_lV _ _ (by assumption))) (by assumption)
      | exact mf_site_vV _ _ _ _ (by assumption) (by assumption)
          (Or.inl (ks_ne_of_live_rV _ _ (by assumption))) (by assumption)
  rintro _ _ ⟨_, _⟩))

/-- A made-for pair of a recorded old id. -/
macro "mfSiteOldV" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (setMadeFor _ _) _ _ _)
  (refine writerWP_mono (writerWP_and (good_setMadeFor _ _ _ _ _ (by assumption) (by assumption))
    (writerWP_setMadeFor_mfV _ _ _ _ _ (by assumption) (by assumption))) ?mfPost)
  rintro _ _ ⟨_, _⟩))

macro "mfReplV" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (replacedBy _) _ _ _)
  (refine writerWP_mono (writerWP_and (good_replacedBy _ _ _ _ (by assumption) (by assumption))
    (writerWP_replacedBy_mfV _ _ _ _ (by assumption))) ?mfPost)
  rintro _ _ ⟨_, hmfEq, _⟩
  subst hmfEq))

macro "gmfUpV " h:term : tactic => `(tactic| (
  (with_unfolding_none refine writerWP_of_gmfV ($h _ _ ?gmfL) _ _ _ ?gmfM ?gmfV ?gmfS ?gmfF ?gmfPost)
  case gmfL => simp
  case gmfM => assumption
  case gmfV => assumption
  case gmfS => assumption
  case gmfF => assumption
  intro _ _ _ _))

macro "mfGoodV" : tactic => `(tactic| first
  | gdLink
  | gdReplace
  | tkGood
  | gdUse (good_takeBack _ _ _ _))

macro "mfStepV" : tactic => `(tactic| (mfFrameV; mfGoodV; intro _))

macro "mfDoneV" : tactic => `(tactic| (
  (with_unfolding_none guard_target = (CacheGood _ _ _ ∧ MFV _ _ _))
  exact ⟨by assumption, by assumption⟩))

macro "gmfUseV " h:term : tactic => `(tactic| (
  (with_unfolding_none refine writerWP_of_gmfV $h _ _ _ ?gmfM ?gmfV ?gmfS ?gmfF ?gmfPost)
  case gmfM => assumption
  case gmfV => assumption
  case gmfS => assumption
  case gmfF => assumption
  intro _ _ _ _))

set_option maxHeartbeats 3200000 in
/-- Every route of a full node's replacement keeps `CacheGood` and `MFB`, for a
last version at the transaction's time and a node x with a klong or below B. -/
theorem gmf_handleFullWithV (B : NodeId) (up : NodeId → List (Nat × NodeId) → M Unit)
    (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) (last : KNode) (compact : Bool)
    (c : Ctx) (w : W) (hM : 4 ≤ c.p.M) (hv : ViewGood B c) (hw : CacheGood B c w) (hm : MFV B c w)
    (hlast : FlatAt c.i last.ks) (hx : XOKV B w x)
    (hup : ∀ q more, more.length ≤ 2 → KeepsGMFV B (up q more)) :
    WriterWP (handleFullWith up depth x ins last compact) c w
      (fun _ v => CacheGood B c v ∧ MFV B c v) := by
  have hpos := hv.pos
  unfold handleFullWith
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (writerWP_and (writerWP_and (good_getNode B x c w hv hw) (mf_getNodeV B x c w hm))
    (writerWP_getNode_xokV B x c w hv hx)) ?_
  rintro n v ⟨⟨⟨hv1, hgx⟩, hm1⟩, hne⟩
  repeat' first
    | wpSimplify
    | mfDoneV
    | mfSiteV
    | mfReplV
    | mfSiteOldV
    | exact writerWP_throw _ _ _ _
    | mfStepV
    | gmfUpV hup
    | wpSplit
    | split
    | contradiction

/-- A node with no klong takes at most two key klongs without passing theta. -/
theorem deadOver_fold_nilV (p : Params) (t : Time) (leaf : Bool) (ins : List (Nat × NodeId))
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

theorem gmf_throwV (B : NodeId) {α : Type} (e : String) : KeepsGMFV B (throw e : M α) :=
  fun _ _ _ _ _ _ => writerWP_throw _ _ _ _

/-- The klongs `ins` (at most two) into node x, full or not. -/
theorem gmf_appendKlongsV (B : NodeId) (depth : Nat) :
    ∀ (x : NodeId) (ins : List (Nat × NodeId)), ins.length ≤ 2 → KeepsGMFV B (appendKlongs depth x ins) := by
  induction depth with
  | zero =>
    intro x ins hl c w hM hv hw hm
    rw [appendKlongs_step_dead]
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_mono (writerWP_and (writerWP_and (good_getNode B x c w hv hw) (mf_getNodeV B x c w hm))
      (writerWP_getNode_cache x c w)) ?_
    rintro n v ⟨⟨⟨hv1, hgx⟩, hm1⟩, hlk, _, _⟩
    have hxok : (n.ks = [] → False) → XOKV B v x := fun h n' hn' hk => by
      rw [hlk] at hn'; cases hn'; exact (h hk).elim
    refine writerWP_if _ _ _ _ _ _ (fun hs => ?_) (fun hs => writerWP_if _ _ _ _ _ _ (fun hd => ?_) (fun _ => ?_))
    · refine gmf_handleFullWithV B _ 0 x ins _ false c v hM hv hv1 hm1 (KNode.lastVersion_flatAt _ _)
        (hxok (fun hk => ?_)) (fun _ _ _ => gmf_throwV B _)
      simp only [KNode.size, hk, List.length_nil] at hs; omega
    · refine gmf_handleFullWithV B _ 0 x ins _ true c v hM hv hv1 hm1 (KNode.lastVersion_flatAt _ _)
        (hxok (fun hk => ?_)) (fun _ _ _ => gmf_throwV B _)
      obtain ⟨leaf, ks⟩ := n
      simp only at hk; subst hk
      rw [deadOver_fold_nilV _ _ _ _ hl] at hd; cases hd
    · exact keepsGMF_ofV (good_addKeys B x ins) (mf_addKeysV B x ins) c v hM hv hv1 hm1
  | succ depth ih =>
    intro x ins hl c w hM hv hw hm
    rw [appendKlongs_step_dead]
    simp only [writerWP_bind, writerWP_read]
    refine writerWP_mono (writerWP_and (writerWP_and (good_getNode B x c w hv hw) (mf_getNodeV B x c w hm))
      (writerWP_getNode_cache x c w)) ?_
    rintro n v ⟨⟨⟨hv1, hgx⟩, hm1⟩, hlk, _, _⟩
    have hxok : (n.ks = [] → False) → XOKV B v x := fun h n' hn' hk => by
      rw [hlk] at hn'; cases hn'; exact (h hk).elim
    refine writerWP_if _ _ _ _ _ _ (fun hs => ?_) (fun hs => writerWP_if _ _ _ _ _ _ (fun hd => ?_) (fun _ => ?_))
    · refine gmf_handleFullWithV B _ (depth + 1) x ins _ false c v hM hv hv1 hm1 (KNode.lastVersion_flatAt _ _)
        (hxok (fun hk => ?_)) (fun q more hq => ih q more hq)
      simp only [KNode.size, hk, List.length_nil] at hs; omega
    · refine gmf_handleFullWithV B _ (depth + 1) x ins _ true c v hM hv hv1 hm1 (KNode.lastVersion_flatAt _ _)
        (hxok (fun hk => ?_)) (fun q more hq => ih q more hq)
      obtain ⟨leaf, ks⟩ := n
      simp only at hk; subst hk
      rw [deadOver_fold_nilV _ _ _ _ hl] at hd; cases hd
    · exact keepsGMF_ofV (good_addKeys B x ins) (mf_addKeysV B x ins) c v hM hv hv1 hm1

theorem gmf_handleFullV (B : NodeId) (depth : Nat) (x : NodeId) (last : KNode) (compact : Bool)
    (c : Ctx) (w : W) (hM : 4 ≤ c.p.M) (hv : ViewGood B c) (hw : CacheGood B c w) (hm : MFV B c w)
    (hlast : FlatAt c.i last.ks) (hx : XOKV B w x) :
    WriterWP (handleFull depth x last compact) c w (fun _ v => CacheGood B c v ∧ MFV B c v) := by
  unfold handleFull
  refine gmf_handleFullWithV B _ depth x [] last compact c w hM hv hw hm hlast hx ?_
  intro q more hq
  cases depth with
  | zero => exact gmf_throwV B _
  | succ d => exact gmf_appendKlongsV B d q more hq

theorem xok_of_lookupV (B : NodeId) (w : W) (x : NodeId) (n : KNode) (hlk : w.nodes.lookup x = some n)
    (h : n.ks ≠ []) : XOKV B w x := fun n' hn' hk => by
  rw [hlk] at hn'; cases hn'; exact (h hk).elim

theorem ks_ne_of_unionV (n : KNode) (cv : Nat)
    (h : (!(bitsUnion n.lastBitmap (n.bitsOf cv) == n.lastBitmap)) = true) : n.ks ≠ [] := by
  intro hk
  obtain ⟨leaf, ks⟩ := n
  simp only at hk; subst hk
  simp [KNode.lastBitmap, lastBitmapOf, KNode.bitsOf, bitsUnion] at h

theorem ks_ne_of_bitsV (n : KNode) (cv e : Nat) (h : (n.bitsOf cv).getLast? = some e) : n.ks ≠ [] := by
  intro hk
  obtain ⟨leaf, ks⟩ := n
  simp only at hk; subst hk
  simp [KNode.bitsOf] at h

theorem ks_ne_of_replaceV (n : KNode) (t t' : Time) (d : List Nat) (cv : Nat) (y : NodeId)
    (ks : List Klong) (h : replaceKlong (n.lastVersionGivenDel t d).ks t' cv y = .ok (some ks)) :
    n.ks ≠ [] := by
  intro hk
  obtain ⟨leaf, ks0⟩ := n
  simp only at hk; subst hk
  simp [KNode.lastVersionGivenDel, replaceKlong, replaceKlong.go] at h

macro "gmfHandleV" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (handleFull _ _ _ _) _ _ _)
  (with_unfolding_none refine writerWP_mono (gmf_handleFullV ?ghB _ _ _ _ _ _ ?ghM ?ghV ?ghS ?ghF ?ghL ?ghX) ?ghPost)
  case ghV => assumption
  case ghM => assumption
  case ghS => assumption
  case ghF => assumption
  case ghL => first
    | gdFlat
    | (refine flatAt_rename_after_head _ _ _ _ _ _ _ (by assumption) ?_; gdFlat)
  case ghX => first
    | (refine xok_of_lookupV _ _ _ _ (by assumption) ?_
       first
        | exact ks_ne_of_unionV _ _ (by assumption)
        | exact ks_ne_of_bitsV _ _ _ (by assumption)
        | exact ks_ne_of_replaceV _ _ _ _ _ _ _ (by assumption)
        | assumption)
    | skip
  rintro _ _ ⟨_, _⟩))

theorem gmf_appendDeleteKlongV (B : NodeId) (x : NodeId) (depth cv : Nat) :
    KeepsGMFV B (appendDeleteKlong x depth cv) := by
  intro c w hM hv hw hm
  have hpos := hv.pos
  unfold appendDeleteKlong
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (writerWP_and (writerWP_and (good_getNode B x c w hv hw) (mf_getNodeV B x c w hm))
    (writerWP_getNode_cache x c w)) ?_
  rintro n v ⟨⟨⟨hv1, hgx⟩, hm1⟩, hlk, _, _⟩
  simp only [note]
  repeat' first
    | wpSimplify
    | mfDoneV
    | exact writerWP_throw _ _ _ _
    | gmfHandleV
    | mfStepV
    | wpSplit
    | split
    | contradiction

macro "gmfAppV" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (appendKlongs _ _ _) _ _ _)
  (with_unfolding_none refine writerWP_of_gmfV (gmf_appendKlongsV ?gaB _ _ _ ?gaL) _ _ _ ?gaM ?gaV ?gaS ?gaF ?gaPost)
  case gaV => assumption
  case gaL => simp
  case gaM => assumption
  case gaS => assumption
  case gaF => assumption
  intro _ _ _ _))

theorem gmf_emptyKeyNextV (B : NodeId) (x : NodeId) (depth : Nat) : KeepsGMFV B (emptyKeyNext x depth) := by
  intro c w hM hv hw hm
  have hpos := hv.pos
  unfold emptyKeyNext
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (writerWP_and (writerWP_and (good_getNode B x c w hv hw) (mf_getNodeV B x c w hm))
    (writerWP_getNode_cache x c w)) ?_
  rintro n v ⟨⟨⟨hv1, hgx⟩, hm1⟩, hlk, _, _⟩
  simp only [note]
  repeat' first
    | wpSimplify
    | mfDoneV
    | exact writerWP_throw _ _ _ _
    | gmfHandleV
    | mfStepV
    | wpSplit
    | split
    | contradiction

set_option maxHeartbeats 1600000 in
theorem gmf_mergeParentV (B : NodeId) (q : NodeId) (depth il cL : Nat) (m1 : NodeId) (ir cR : Nat)
    (m2 : Option (NodeId × Nat)) : KeepsGMFV B (mergeParent q depth il cL m1 ir cR m2) := by
  intro c w hM hv hw hm
  have hpos := hv.pos
  unfold mergeParent
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (writerWP_and (writerWP_and (good_getNode B q c w hv hw) (mf_getNodeV B q c w hm))
    (writerWP_getNode_cache q c w)) ?_
  rintro n v ⟨⟨⟨hv1, hgx⟩, hm1⟩, hlk, _, _⟩
  simp only [note]
  repeat' first
    | wpSimplify
    | mfDoneV
    | exact writerWP_throw _ _ _ _
    | gmfHandleV
    | mfStepV
    | wpSplit
    | split
    | contradiction

theorem gmf_replaceRootV (B : NodeId) (x : NodeId) (depth only : Nat) : KeepsGMFV B (replaceRoot x depth only) := by
  intro c w hM hv hw hm
  unfold replaceRoot
  repeat' first
    | wpSimplify
    | mfDoneV
    | exact writerWP_throw _ _ _ _
    | gmfAppV
    | mfStepV
    | wpSplit
    | split
    | contradiction

/-- `sibling` gives a `Good` node. -/
theorem good_sibling_resV (B : NodeId) (q : NodeId) (pn : KNode) (i : Nat) (inner : Bool) (c : Ctx) (w : W)
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

macro "gmfSibV" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (sibling _ _ _ _) _ _ _)
  refine' writerWP_mf_frameV ‹MFV _ _ _› (mf_siblingV _ _ _ _ _) ?_
  (refine writerWP_mono (good_sibling_resV _ _ _ _ _ _ _ (by assumption) (by assumption)) ?gsPost)
  rintro ⟨_, _⟩ _ ⟨_, _⟩ _))

set_option maxHeartbeats 3200000 in
theorem gmf_mergeV (B : NodeId) (x : NodeId) (d : Nat) : KeepsGMFV B (merge x d) := by
  intro c w hM hv hw hm
  have hpos := hv.pos
  unfold merge
  repeat' first
    | wpSimplify
    | simp only [List.forIn_cons, List.forIn_nil]
    | mfDoneV
    | exact writerWP_throw _ _ _ _
    | mfSiteV
    | mfReplV
    | mfSiteOldV
    | gmfSibV
    | gmfUseV (gmf_mergeParentV B _ _ _ _ _ _ _ _)
    | mfStepV
    | wpSplit
    | split
    | contradiction


theorem gmf_foldlMV (B : NodeId) {α β : Type} (xs : List α) (f : β → α → M β) (init : β)
    (hf : ∀ b a, KeepsGMFV B (f b a)) : KeepsGMFV B (xs.foldlM f init) := by
  induction xs generalizing init with
  | nil => intro c w _ _ hw hm; simpa only [List.foldlM_nil, writerWP_pure] using ⟨hw, hm⟩
  | cons a xs ih =>
    intro c w hM hv hw hm
    rw [List.foldlM_cons, writerWP_bind]
    exact writerWP_mono (hf init a c w hM hv hw hm) (fun b v hh => ih b c v hM hv hh.1 hh.2)

theorem gmf_forInV (B : NodeId) {α β : Type} (xs : List α) (init : β)
    (f : α → β → M (ForInStep β)) (c : Ctx) (hM : 4 ≤ c.p.M) (hv : ViewGood B c)
    (hf : ∀ a b w, CacheGood B c w → MFV B c w →
      WriterWP (f a b) c w (fun _ v => CacheGood B c v ∧ MFV B c v))
    (w : W) (hw : CacheGood B c w) (hm : MFV B c w) :
    WriterWP (forIn xs init f) c w (fun _ v => CacheGood B c v ∧ MFV B c v) := by
  induction xs generalizing init w with
  | nil => simpa only [List.forIn_nil, writerWP_pure] using ⟨hw, hm⟩
  | cons a xs ih =>
    rw [List.forIn_cons, writerWP_bind]
    refine writerWP_mono (hf a init w hw hm) ?_
    intro step v hh
    cases step with
    | done b => simpa only [writerWP_pure] using hh
    | yield b => exact ih b v hh.1 hh.2

macro "gmfFoldWithV " extra:tactic : tactic => `(tactic| (
  (with_unfolding_none refine' writerWP_of_gmfV (gmf_foldlMV _ _ _ _ ?gfBody) _ _ _ ?gfM ?gfV ?gfS ?gfF ?gfPost)
  case gfBody =>
    intro b a c w hM hv hw hm
    repeat' first
      | wpSimplify
      | exact writerWP_throw _ _ _ _
      | ($extra:tactic)
      | mfStepV
      | wpSplit
      | split
      | contradiction
      | mfDoneV
  case gfM => assumption
  case gfV => assumption
  case gfS => assumption
  case gfF => assumption
  intro _ _ _ _))

macro "gmfForWithV " extra:tactic : tactic => `(tactic| (
  (with_unfolding_none refine writerWP_mono (gmf_forInV ?gfB _ _ _ _ ?gfM ?gfV ?gfBody _ ?gfS ?gfF) ?gfPost)
  case gfV => assumption
  case gfM => assumption
  case gfBody =>
    intro a b w hw hm
    repeat' first
      | wpSimplify
      | exact writerWP_throw _ _ _ _
      | ($extra:tactic)
      | mfStepV
      | wpSplit
      | split
      | contradiction
      | mfDoneV
  case gfS => assumption
  case gfF => assumption
  rintro _ _ ⟨_, _⟩))

theorem gmf_setNodeV (B : NodeId) (segRoot : NodeId) (cv : Nat) (create : Bool) :
    KeepsGMFV B (setNode segRoot cv create) := by
  intro c w hM hv hw hm
  have hpos := hv.pos
  unfold setNode
  repeat' first
    | wpSimplify
    | mfDoneV
    | exact writerWP_throw _ _ _ _
    | gmfAppV
    | mfStepV
    | wpSplit
    | split
    | contradiction


theorem gmf_mergeUpV (B : NodeId) (key : Key) (g : Nat) :
    ∀ fuel h merged, KeepsGMFV B (mergeUp key g fuel h merged) := by
  intro fuel
  induction fuel with
  | zero => intro h merged; exact gmf_throwV B _
  | succ fuel ih =>
    intro h merged c w hM hv hw hm
    unfold mergeUp
    repeat' first
      | wpSimplify
      | mfDoneV
      | exact writerWP_throw _ _ _ _
      | gmfUseV (gmf_mergeV B _ _)
      | gmfUseV (ih _ _)
      | mfStepV
      | wpSplit
      | split
      | contradiction

theorem gmf_collapseRootV (B : NodeId) (key : Key) (segment : Nat) :
    ∀ fuel, KeepsGMFV B (collapseRoot key segment fuel) := by
  intro fuel
  induction fuel with
  | zero => exact gmf_throwV B _
  | succ fuel ih =>
    intro c w hM hv hw hm
    unfold collapseRoot
    repeat' first
      | wpSimplify
      | mfDoneV
      | exact writerWP_throw _ _ _ _
      | mfReplV
      | (mfFrV (takeBackRoot _ _ _) => (mf_takeBackRootV _ _ _ _)
         refine writerWP_mono (good_takeBackRoot B _ _ _ _ _ hv (by assumption)
           (Blank.ge B _ _ hv (blank_of_firstTime B _ _ _ hv.pos (by assumption) (by assumption)))) ?_
         intro _ _ _ _)
      | gmfUseV (gmf_replaceRootV B _ _ _)
      | gmfUseV ih
      | mfStepV
      | wpSplit
      | split
      | contradiction

theorem gmf_afterDeleteV (B : NodeId) (key : Key) (g h : Nat) : KeepsGMFV B (afterDelete key g h) := by
  intro c w hM hv hw hm
  unfold afterDelete
  repeat' first
    | wpSimplify
    | mfDoneV
    | gmfUseV (gmf_mergeUpV B _ _ _ _ _)
    | gmfUseV (gmf_collapseRootV B _ _ _)
    | wpSplit
    | split
    | contradiction

set_option maxHeartbeats 1600000 in
theorem gmf_deleteUpwardV (B : NodeId) (leaf : NodeId) (depth cv : Nat) (key : Key) :
    KeepsGMFV B (deleteUpward leaf depth cv key) := by
  intro c w hM hv hw hm
  unfold deleteUpward
  repeat' first
    | wpSimplify
    | mfDoneV
    | exact writerWP_throw _ _ _ _
    | gmfUseV (gmf_afterDeleteV B _ _ _)
    | gmfUseV (gmf_mergeUpV B _ _ _ _ _)
    | gmfUseV (gmf_collapseRootV B _ _ _)
    | gmfUseV (gmf_appendDeleteKlongV B _ _ _)
    | gmfUseV (gmf_emptyKeyNextV B _ _)
    | gmfFoldWithV fail
    | gmfForWithV fail
    | mfStepV
    | wpSplit
    | split
    | contradiction

theorem gmf_setValueV (B : NodeId) (segRoot : NodeId) (cv : Nat) (key : Key) (value : Option Nat) :
    KeepsGMFV B (setValue segRoot cv key value) := by
  intro c w hM hv hw hm
  have hpos := hv.pos
  unfold setValue
  repeat' first
    | wpSimplify
    | mfDoneV
    | exact writerWP_throw _ _ _ _
    | gmfAppV
    | gmfUseV (gmf_deleteUpwardV B _ _ _ _)
    | mfStepV
    | wpSplit
    | split
    | contradiction

theorem gmf_putSegsV (B : NodeId) (key : Key) (value : Option Nat) (segs : List Nat)
    (segRoot : NodeId) : KeepsGMFV B (putSegs key value segs segRoot) := by
  induction segs generalizing segRoot with
  | nil => exact gmf_throwV B _
  | cons cv rest ih =>
    cases rest with
    | nil => exact gmf_setValueV B _ _ _ _
    | cons cv2 rest =>
      intro c w hM hv hw hm
      unfold putSegs
      repeat' first
        | wpSimplify
        | mfDoneV
        | exact writerWP_throw _ _ _ _
        | gmfUseV (gmf_setNodeV B _ _ _)
        | gmfUseV (ih _)
        | mfStepV
        | wpSplit
        | split
        | contradiction

theorem gmf_putKvV (B : NodeId) (op : Op) : KeepsGMFV B (putKv op) := by
  cases op <;> (intro c w hM hv hw hm; unfold putKv)
  all_goals
    repeat' first
      | wpSimplify
      | mfDoneV
      | exact writerWP_throw _ _ _ _
      | gmfUseV (gmf_putSegsV B _ _ _ _)
      | mfStepV
      | wpSplit
      | split
      | contradiction

theorem gmf_opsV (B : NodeId) (ops : List Op) : KeepsGMFV B (ops.mapM putKv) := by
  induction ops with
  | nil => intro c w _ _ hw hm; simpa only [List.mapM_nil, writerWP_pure] using ⟨hw, hm⟩
  | cons op ops ih =>
    intro c w hM hv hw hm
    rw [List.mapM_cons, writerWP_bind]
    refine writerWP_mono (gmf_putKvV B op c w hM hv hw hm) ?_
    intro noop v hh
    have hi := ih c v hM hv hh.1 hh.2
    simpa only [writerWP_bind, writerWP_pure] using hi

end SIS.Tree
