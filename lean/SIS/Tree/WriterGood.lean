/-
The tree model (bergdb 024-12, TP7): the writer keeps the klongs of earlier
times. Through every rule of the writer, each node of the overlay stays `Good`
(SIS/Tree/CacheGood.lean): its klongs before the transaction's time are those
of P@(i-1). This file: the writer's primitive steps, the splits and
`appendKlongs`.
-/
import SIS.Tree.CacheGood
import SIS.Tree.WriterSteps
import SIS.Tree.WriterCache

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- Every node of the overlay is `Good`, and the next id is one of the
transaction's. -/
def CacheGood (B : NodeId) (c : Ctx) (w : W) : Prop :=
  B ≤ w.next ∧ ∀ q ∈ w.nodes, Good B c q.1 q.2

def KeepsGood (B : NodeId) {α : Type} (f : M α) : Prop :=
  ∀ c w, ViewGood B c → CacheGood B c w → WriterWP f c w (fun _ v => CacheGood B c v)

theorem cacheGood_lookup (B : NodeId) (c : Ctx) (w : W) (hw : CacheGood B c w) (x : NodeId)
    (n : KNode) (hn : w.nodes.lookup x = some n) : Good B c x n := by
  obtain ⟨pre, post, he, _⟩ := List.lookup_eq_some_iff.mp hn
  apply hw.2 (x, n)
  rw [he]
  simp

theorem good_getNode (B : NodeId) (x : NodeId) (c : Ctx) (w : W)
    (hv : ViewGood B c) (hw : CacheGood B c w) :
    WriterWP (getNode x) c w (fun n v => CacheGood B c v ∧ Good B c x n) := by
  unfold getNode
  simp only [writerWP_bind, writerWP_get]
  split
  · rename_i n hn
    simp only [writerWP_pure]
    exact ⟨hw, cacheGood_lookup B c w hw x n hn⟩
  · simp only [writerWP_bind, writerWP_read]
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
        have hg := good_load B c hv x nd (c.p.heightOf nd.level == 0) hn hd hl
        simp only [writerWP_bind, writerWP_set, writerWP_pure]
        refine ⟨⟨hw.1, ?_⟩, hg⟩
        intro q hq
        rcases List.mem_append.mp hq with hq | hq
        · exact hw.2 q hq
        · have heq := List.mem_singleton.mp hq
          subst q
          exact hg
    · exact writerWP_throw _ _ _ _

theorem good_putNode (B : NodeId) (x : NodeId) (n : KNode) (c : Ctx) (w : W)
    (post : Unit → W → Prop) (hw : CacheGood B c w) (hn : Good B c x n)
    (hp : ∀ r v, CacheGood B c v → post r v) : WriterWP (putNode x n) c w post := by
  simp only [putNode, writerWP_modify]
  apply hp
  refine ⟨hw.1, ?_⟩
  intro q hq
  unfold upsert at hq
  split at hq
  · obtain ⟨a, ha, he⟩ := List.mem_map.mp hq
    split at he
    · cases he; exact hn
    · cases he; exact hw.2 _ ha
  · rcases List.mem_append.mp hq with hq | hq
    · exact hw.2 q hq
    · have he := List.mem_singleton.mp hq
      subst q; exact hn

/-- A new key node, without klongs or with a last version at the
transaction's time: its id is blank. -/
theorem good_newKey (B : NodeId) (g h : Nat) (leaf : Bool) (ks : List Klong) (c : Ctx) (w : W)
    (post : NodeId → W → Prop) (hv : ViewGood B c) (hw : CacheGood B c w)
    (hks : ks = [] ∨ FlatAt c.i ks)
    (hp : ∀ x v, CacheGood B c v ∧ Blank B c x → post x v) :
    WriterWP (newKey g h leaf ks) c w post := by
  have hb := blank_fresh B c hv w.next hw.1
  have hg : Good B c w.next ⟨leaf, ks⟩ := Good.ofBlank B c w.next ⟨leaf, ks⟩ hv.pos hb hks
  unfold newKey fresh
  wpSimplify
  split <;> wpSimplify
  all_goals
    apply hp
    refine ⟨⟨by show B ≤ w.next + 2; have := hw.1; omega, ?_⟩, hb⟩
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hw.2 q hq
    · have he := List.mem_singleton.mp hq
      subst q; exact hg

theorem good_fresh (B : NodeId) : KeepsGood B fresh := by
  intro c w _ hw
  unfold fresh
  wpSimplify
  exact ⟨by show B ≤ w.next + 2; have := hw.1; omega, hw.2⟩

theorem good_note (B : NodeId) (s : String) : KeepsGood B (note s) := by
  intro c w _ hw
  simp only [note, writerWP_modify]
  exact hw

theorem good_takenBack (B : NodeId) (x : NodeId) : KeepsGood B (takenBack x) := by
  intro c w _ hw
  simp only [takenBack, writerWP_modify]
  exact hw

theorem good_pathClear (B : NodeId) : KeepsGood B pathClear := by
  intro c w _ hw
  simp only [pathClear, writerWP_modify]
  exact hw

theorem good_pathAdd (B : NodeId) (cv : Option Nat) (x : NodeId) : KeepsGood B (pathAdd cv x) := by
  intro c w _ hw
  simp only [pathAdd, writerWP_modify]
  exact hw

theorem good_setMadeFor (B : NodeId) (x : NodeId) (old : Option NodeId) :
    KeepsGood B (setMadeFor x old) := by
  intro c w _ hw
  unfold setMadeFor
  split
  · simp only [writerWP_modify]; exact hw
  · simpa only [writerWP_pure] using hw

theorem good_newValue (B : NodeId) (h : Nat) : KeepsGood B (newValue h) := by
  intro c w _ hw
  unfold newValue fresh
  wpSimplify
  exact ⟨by show B ≤ w.next + 2; have := hw.1; omega, hw.2⟩

theorem good_newSuperRoot (B : NodeId) (x : NodeId) : KeepsGood B (newSuperRoot x) := by
  intro c w _ hw
  unfold newSuperRoot note fresh
  wpSimplify
  split <;> wpSimplify
  · exact hw
  · exact ⟨by show B ≤ w.next + 2; have := hw.1; omega, hw.2⟩

theorem writerWP_of_good {α : Type} {B : NodeId} {f : M α} (hf : KeepsGood B f)
    (c : Ctx) (w : W) (post : α → W → Prop) (hv : ViewGood B c)
    (hw : CacheGood B c w) (hp : ∀ r v, CacheGood B c v → post r v) :
    WriterWP f c w post := writerWP_mono (hf c w hv hw) hp

macro "gdUse " h:term : tactic => `(tactic| (
  (with_unfolding_none refine' writerWP_of_good $h _ _ _ ?gdView ?gdState ?gdPost)
  case gdView => assumption
  case gdState => assumption
  intro _ _ _))

macro "gdNode" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (getNode _) _ _ _)
  (refine writerWP_mono (good_getNode ?gdB _ _ _ ?gdView ?gdState) ?gdPost)
  case gdView => assumption
  case gdState => assumption
  rintro _ _ ⟨_, _⟩))

macro "gdNeutral" : tactic => `(tactic| (
  intro c w hv hw
  repeat' first
    | wpSimplify
    | gdNode
    | exact writerWP_throw _ _ _ _
    | split
    | assumption
    | contradiction))

theorem good_ghOf (B : NodeId) (x : NodeId) : KeepsGood B (ghOf x) := by unfold ghOf; gdNeutral
theorem good_replacedBy (B : NodeId) (x : NodeId) : KeepsGood B (replacedBy x) := by
  unfold replacedBy; gdNeutral
theorem good_pathSize (B : NodeId) : KeepsGood B pathSize := by unfold pathSize; gdNeutral
theorem good_pathNode (B : NodeId) (d : Nat) : KeepsGood B (pathNode d) := by
  unfold pathNode; gdNeutral
theorem good_klongAt (B : NodeId) (d : Nat) : KeepsGood B (klongAt d) := by
  unfold klongAt; gdNeutral

theorem good_parentAt (B : NodeId) (d : Nat) : KeepsGood B (parentAt d) := by
  cases d with
  | zero => intro c w hv hw; simpa only [parentAt, writerWP_pure] using hw
  | succ d =>
    intro c w hv hw
    unfold parentAt
    simp only [writerWP_bind]
    gdUse (good_pathNode _ _)
    simpa only [writerWP_pure] using ‹CacheGood B _ _›

theorem good_findRoot (B : NodeId) : KeepsGood B findRoot := by
  intro c w hv hw
  unfold findRoot
  wpSimplify
  exact good_pathAdd B none _ c w hv hw

theorem good_throw (B : NodeId) {α : Type} (e : String) : KeepsGood B (throw e : M α) := by
  intro c w hv hw
  exact writerWP_throw _ _ _ _

syntax "gdFlat" : tactic
macro_rules
  | `(tactic| gdFlat) => `(tactic| first
    | assumption
    | exact flatAt_newKlongs _ _
    | exact flatAt_newKlongs _ [(_, _), (_, _)]
    | exact KNode.lastVersion_flatAt _ _
    | exact KNode.lastVersionGivenDel_flatAt _ _ _
    | exact (halves_flatAt _ _ _ _ (FlatAt.flat _ _ (by assumption))).1
    | exact (halves_flatAt _ _ _ _ (FlatAt.flat _ _ (by assumption))).2
    | (refine flatAt_replaceKlong _ _ _ _ _ _ ?_ (by assumption); gdFlat)
    | (apply flatAt_insertSorted; gdFlat))

macro "gdBlank" : tactic => `(tactic| first
  | assumption
  | exact blank_of_firstTime _ _ _ _ (by assumption) (by assumption) (by assumption))

syntax "gdKs" : tactic
macro_rules
  | `(tactic| gdKs) => `(tactic| first
    | assumption
    | ((with_unfolding_none guard_target = Good _ _ _ (KNode.add _ _ (.key _ _)))
       apply Good.add_key _ _ _ _ _ _ (by assumption); gdKs)
    | ((with_unfolding_none guard_target = Good _ _ _ (KNode.add _ _ (.del _)))
       apply Good.add_del _ _ _ _ _ (by assumption); gdKs)
    | ((with_unfolding_none guard_target = Good _ _ _ (KNode.toPrev _ _))
       apply Good.toPrev; gdKs)
    | (apply Good.fold_add _ _ _ _ (by assumption); gdKs)
    | exact Good.ofBlank _ _ _ _ (by assumption) (by gdBlank) (Or.inr (by gdFlat)))

macro "gdStore" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (putNode _ _) _ _ _)
  (with_unfolding_none refine good_putNode ?gdB _ _ _ _ _ ?gdState ?gdInput ?gdPost)
  case gdState => assumption
  case gdInput => gdKs
  intro _ _ _))

macro "gdCreate" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (newKey _ _ _ _) _ _ _)
  (with_unfolding_none refine good_newKey ?gdB _ _ _ _ _ _ _ ?gdView ?gdState ?gdInput ?gdPost)
  case gdView => assumption
  case gdState => assumption
  case gdInput => first
    | exact Or.inl rfl
    | exact Or.inr (by gdFlat)
  rintro _ _ ⟨_, _⟩))

macro "gdCore" : tactic => `(tactic| first
  | gdNode
  | gdStore
  | gdCreate
  | gdUse (good_pathAdd _ _ _)
  | gdUse (good_ghOf _ _)
  | gdUse (good_replacedBy _ _)
  | gdUse (good_pathSize _)
  | gdUse (good_pathNode _ _)
  | gdUse (good_klongAt _ _)
  | gdUse (good_parentAt _ _)
  | gdUse (good_findRoot _)
  | gdUse (good_note _ _)
  | gdUse (good_fresh _)
  | gdUse (good_newValue _ _)
  | gdUse (good_newSuperRoot _ _)
  | gdUse (good_setMadeFor _ _ _)
  | gdUse (good_takenBack _ _)
  | gdUse (good_pathClear _)
  | assumption
  | exact writerWP_throw _ _ _ _)

theorem good_addKeys (B : NodeId) (x : NodeId) (ins : List (Nat × NodeId)) :
    KeepsGood B (addKeys x ins) := by
  intro c w hv hw
  have hpos := hv.pos
  unfold addKeys
  wpSimplify
  gdNode
  exact good_putNode B _ _ _ _ _ (by assumption)
    (Good.fold_add B c x ins hpos _ (by assumption)) (fun _ _ h => h)

/-- The loop of a time split gives a last version at the transaction's
time, and changes no state. -/
theorem writerWP_replaceOrAdd_flat (last : KNode) (ins : List (Nat × NodeId))
    (c : Ctx) (w : W) (hlast : FlatAt c.i last.ks) :
    WriterWP (replaceOrAdd last ins) c w (fun out v => FlatAt c.i out.ks ∧ v = w) := by
  unfold replaceOrAdd
  simp only [writerWP_bind, writerWP_read]
  induction ins generalizing last with
  | nil => simp only [List.foldlM_nil, writerWP_pure]; exact ⟨hlast, trivial⟩
  | cons q ins ih =>
    rw [List.foldlM_cons, writerWP_bind]
    cases hr : replaceKlong last.ks c.i q.1 q.2 with
    | error e => exact writerWP_throw _ _ _ _
    | ok result =>
      cases result with
      | none =>
        simp only [writerWP_pure]
        exact ih _ (FlatAt.add_key _ last _ _ hlast)
      | some ks =>
        simp only [writerWP_pure]
        exact ih {last with ks := ks} (flatAt_replaceKlong _ _ _ _ _ _ hlast hr)

macro "gdReplace" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (replaceOrAdd _ _) _ _ _)
  refine writerWP_mono (writerWP_replaceOrAdd_flat _ _ _ _ ?gdLast) ?gdPost
  case gdLast => gdFlat
  rintro out v ⟨hout, heq⟩
  subst v))

/-- The klong of the transaction that links a node of the transaction,
pointed in place (a segment root made and split, or taken back). -/
macro "gdLink" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (putNode _ (KNode.repoint _ _ _)) _ _ _)
  (with_unfolding_none refine good_putNode ?gdB _ _ _ _ _ ?gdState ?gdInput ?gdPost)
  case gdState => assumption
  case gdInput =>
    exact Good.repointLink _ _ _ _ _ _ _ _ ‹ViewGood _ _› (by assumption) (by assumption)
      (Blank.ge _ _ _ ‹ViewGood _ _› (by gdBlank))
  intro _ _ _))

set_option maxHeartbeats 1600000 in
/-- Every route of a full node's replacement keeps the overlay's nodes
`Good`, for a last version at the transaction's time. -/
theorem good_handleFullWith (B : NodeId) (up : NodeId → List (Nat × NodeId) → M Unit)
    (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) (last : KNode) (compact : Bool)
    (c : Ctx) (w : W) (hv : ViewGood B c) (hw : CacheGood B c w)
    (hlast : FlatAt c.i last.ks) (hup : ∀ q more, KeepsGood B (up q more)) :
    WriterWP (handleFullWith up depth x ins last compact) c w (fun _ v => CacheGood B c v) := by
  have hpos := hv.pos
  unfold handleFullWith
  repeat' first
    | wpSimplify
    | gdLink
    | gdCore
    | gdReplace
    | gdUse (hup _ _)
    | wpSplit
    | split
    | contradiction

end SIS.Tree
