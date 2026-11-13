/-
The tree model (bergdb 024-12, TP7): every key node of the writer's overlay has
a klong, but the pending ones. A key node without a klong at a transaction's
end would be exported without a history. The writer makes such nodes on the
way (a split's new nodes, filled before the split returns; `setNode`'s new
segment leaf, filled by the next step of the put), so the invariant `NEx E`
has a list E of the ids that may be empty. It is walked together with `Good`
(SIS/Tree/WriterGood.lean). This file: the rules for the writer's primitive
steps, the splits.
-/
import SIS.Tree.WriterGoodOps

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- Every node of the overlay has a klong, but those of E. -/
def NEx (E : List NodeId) (w : W) : Prop := ∀ q ∈ w.nodes, q.2.ks = [] → q.1 ∈ E

def KeepsNE (B : NodeId) {α : Type} (f : M α) : Prop :=
  ∀ (E : List NodeId) c w, ViewGood B c → CacheGood B c w → NEx E w →
    WriterWP f c w (fun _ v => CacheGood B c v ∧ NEx E v)

theorem NEx.mono {E E' : List NodeId} {w : W} (hs : ∀ y ∈ E, y ∈ E') (h : NEx E w) :
    NEx E' w := fun q hq he => hs _ (h q hq he)

/-- `NEx.mono` with the invariant first. -/
theorem NEx.of {E E' : List NodeId} {w : W} (h : NEx E w) (hs : ∀ y ∈ E, y ∈ E') :
    NEx E' w := NEx.mono hs h

/-! ## Nodes with a klong -/

theorem nex_flat_ne (i : Time) (ks : List Klong) (h : FlatAt i ks) : ks ≠ [] := by
  obtain ⟨r, rfl, _⟩ := h
  exact List.cons_ne_nil _ _

theorem nex_add_ne (n : KNode) (t : Time) (k : Klong) : (n.add t k).ks ≠ [] := by
  rcases n.add_ks t k with he | he <;> rw [he] <;> simp

theorem nex_fold_nil (n : KNode) (i : Time) (ins : List (Nat × NodeId))
    (h : (ins.foldl (fun n (q : Nat × NodeId) => n.add i (.key q.1 q.2)) n).ks = []) :
    n.ks = [] := by
  induction ins generalizing n with
  | nil => exact h
  | cons q ins ih => exact absurd (ih _ h) (nex_add_ne _ _ _)

theorem nex_setAt_nil (n : KNode) (j : Nat) (k : Klong) (h : (n.setAt j k).ks = []) :
    n.ks = [] := by
  unfold KNode.setAt at h
  simpa using h

theorem nex_repoint_nil (n : KNode) (j : Nat) (y : NodeId) (h : (n.repoint j y).ks = []) :
    n.ks = [] := by
  unfold KNode.repoint at h
  split at h
  · exact nex_setAt_nil _ _ _ h
  · exact h

theorem nex_zipIdx_nil (n : KNode) (F : Klong × Nat → Klong)
    (h : ({ n with ks := n.ks.zipIdx.map F } : KNode).ks = []) : n.ks = [] := by
  simpa using h

/-- A node that the writer read before the transaction made it has klongs
of P@(i-1) once it has a klong at all: its first klong is a time klong of an
earlier time. -/
theorem nex_base (B : NodeId) (c : Ctx) (x : NodeId) (n : KNode) (h : Good B c x n)
    (hpos : 0 < c.i) (hne : n.ks ≠ []) (hf : ¬ (n.firstTime == some c.i) = true) :
    baseKlongs c.view x ≠ [] := by
  intro hb
  have hp := h.old
  rw [hb] at hp
  obtain ⟨leaf, ks⟩ := n
  cases ks with
  | nil => exact hne rfl
  | cons k r =>
    cases k with
    | time t =>
      have ht := h.times t List.mem_cons_self
      by_cases hle : t ≤ c.i - 1
      · simp [prefixAt, hle] at hp
      · have htt : t = c.i := by omega
        subst htt
        simp [KNode.firstTime] at hf
    | key cv y => simp [prefixAt] at hp
    | del b => simp [prefixAt] at hp

theorem nex_base_of_false (B : NodeId) (c : Ctx) (x : NodeId) (n : KNode) (h : Good B c x n)
    (hpos : 0 < c.i) (hne : n.ks ≠ []) (hf : (n.firstTime == some c.i) = false) :
    baseKlongs c.view x ≠ [] :=
  nex_base B c x n h hpos hne (by rw [hf]; simp)

theorem nex_base_or (B : NodeId) (c : Ctx) (E : List NodeId) (x : NodeId) (n : KNode)
    (h : Good B c x n) (hpos : 0 < c.i) (hr : n.ks = [] → x ∈ E)
    (hf : ¬ (n.firstTime == some c.i) = true) : baseKlongs c.view x ≠ [] ∨ x ∈ E := by
  by_cases hk : n.ks = []
  · exact Or.inr (hr hk)
  · exact Or.inl (nex_base B c x n h hpos hk hf)

/-! ## The primitive steps -/

theorem nex_lookup (E : List NodeId) (w : W) (hn : NEx E w) (x : NodeId) (n : KNode)
    (h : w.nodes.lookup x = some n) : n.ks = [] → x ∈ E := by
  obtain ⟨pre, post, he, _⟩ := List.lookup_eq_some_iff.mp h
  apply hn (x, n)
  rw [he]
  simp

theorem nex_getNode_only (B : NodeId) (E : List NodeId) (x : NodeId) (c : Ctx) (w : W)
    (hv : ViewGood B c) (hn : NEx E w) :
    WriterWP (getNode x) c w (fun n v => NEx E v ∧ (n.ks = [] → x ∈ E)) := by
  unfold getNode
  simp only [writerWP_bind, writerWP_get]
  split
  · rename_i n hn'
    simp only [writerWP_pure]
    exact ⟨hn, nex_lookup E w hn x n hn'⟩
  · simp only [writerWP_bind, writerWP_read]
    split
    · rename_i nd hnd
      split
      · exact writerWP_throw _ _ _ _
      · rename_i hkind
        have hd : nd.isData = false := by cases hd : nd.isData <;> simp_all
        have hl : nd.level ≤ c.p.keyMax := by
          have hh : ¬ c.p.keyMax < nd.level := by
            intro h; simp [h] at hkind
          omega
        have hne := hv.nonempty x nd hnd hd hl
        simp only [writerWP_bind, writerWP_set, writerWP_pure]
        refine ⟨?_, fun h => absurd h hne⟩
        intro q hq hk
        rcases List.mem_append.mp hq with hq | hq
        · exact hn q hq hk
        · have heq := List.mem_singleton.mp hq
          subst q
          exact absurd hk hne
    · exact writerWP_throw _ _ _ _

/-- A node read: `Good`, with a klong unless it is pending, and with klongs of
P@(i-1) unless the transaction made it or it is pending. -/
theorem nex_getNode (B : NodeId) (E : List NodeId) (x : NodeId) (c : Ctx) (w : W)
    (hv : ViewGood B c) (hw : CacheGood B c w) (hn : NEx E w) :
    WriterWP (getNode x) c w (fun n v => CacheGood B c v ∧ NEx E v ∧ Good B c x n ∧
      (n.ks = [] → x ∈ E) ∧
      (¬ (n.firstTime == some c.i) = true → baseKlongs c.view x ≠ [] ∨ x ∈ E)) := by
  refine writerWP_mono (writerWP_and (good_getNode B x c w hv hw)
    (nex_getNode_only B E x c w hv hn)) ?_
  rintro n v ⟨⟨hc, hg⟩, hn', hr⟩
  exact ⟨hc, hn', hg, hr, nex_base_or B c E x n hg hv.pos hr⟩

theorem nex_upsert (E : List NodeId) (ns : List (NodeId × KNode)) (x : NodeId) (n : KNode)
    (hn : ∀ q ∈ ns, q.2.ks = [] → q.1 ∈ E) (hx : n.ks = [] → x ∈ E) :
    ∀ q ∈ upsert ns x n, q.2.ks = [] → q.1 ∈ E := by
  intro q hq
  unfold upsert at hq
  split at hq
  · obtain ⟨a, ha, he⟩ := List.mem_map.mp hq
    split at he
    · cases he; exact hx
    · cases he; exact hn _ ha
  · rcases List.mem_append.mp hq with hq | hq
    · exact hn q hq
    · have he := List.mem_singleton.mp hq
      subst q; exact hx

/-- A store of a node with a klong, or of a pending one. -/
theorem nex_putNode (B : NodeId) (E : List NodeId) (x : NodeId) (n : KNode) (c : Ctx) (w : W)
    (post : Unit → W → Prop) (hw : CacheGood B c w) (hn : NEx E w) (hg : Good B c x n)
    (hx : n.ks = [] → x ∈ E) (hp : ∀ r v, CacheGood B c v → NEx E v → post r v) :
    WriterWP (putNode x n) c w post := by
  have hc := good_putNode B x n c w (fun _ v => CacheGood B c v) hw hg (fun _ _ h => h)
  simp only [putNode, writerWP_modify] at hc ⊢
  exact hp () _ hc (nex_upsert E w.nodes x n hn hx)

/-- A store of a node with a klong: x is no longer pending. -/
theorem nex_putNode_fill (B : NodeId) (E : List NodeId) (x : NodeId) (n : KNode) (c : Ctx)
    (w : W) (post : Unit → W → Prop) (hw : CacheGood B c w) (hn : NEx E w)
    (hg : Good B c x n) (hne : n.ks ≠ [])
    (hp : ∀ r v, CacheGood B c v → NEx (E.filter (fun y => y != x)) v → post r v) :
    WriterWP (putNode x n) c w post := by
  have hc := good_putNode B x n c w (fun _ v => CacheGood B c v) hw hg (fun _ _ h => h)
  simp only [putNode, writerWP_modify] at hc ⊢
  apply hp () _ hc
  intro q hq hk
  unfold upsert at hq
  split at hq
  · obtain ⟨a, ha, he⟩ := List.mem_map.mp hq
    split at he
    · cases he; exact absurd hk hne
    · rename_i hax
      cases he
      refine List.mem_filter.mpr ⟨hn _ ha hk, ?_⟩
      simpa using hax
  · rename_i hany
    rcases List.mem_append.mp hq with hq | hq
    · refine List.mem_filter.mpr ⟨hn q hq hk, ?_⟩
      have : q.1 ≠ x := by
        intro hq1
        apply hany
        exact List.any_eq_true.mpr ⟨q, hq, by simp [hq1]⟩
      simpa using this
    · have he := List.mem_singleton.mp hq
      subst q; exact absurd hk hne

/-- A store of the node's klongs before the transaction: they are those of
P@(i-1). -/
theorem nex_putNode_toPrev (B : NodeId) (E : List NodeId) (x : NodeId) (n : KNode) (c : Ctx)
    (w : W) (post : Unit → W → Prop) (hw : CacheGood B c w) (hn : NEx E w)
    (hg : Good B c x n) (hx : baseKlongs c.view x ≠ [] ∨ x ∈ E)
    (hp : ∀ r v, CacheGood B c v → NEx E v → post r v) :
    WriterWP (putNode x (n.toPrev (c.i - 1))) c w post := by
  refine nex_putNode B E x _ c w post hw hn (Good.toPrev B c x n hg) ?_ hp
  intro hk
  rcases hx with hb | hb
  · have ho := hg.old
    exact absurd (by rw [← ho]; exact hk) hb
  · exact hb

/-- A new key node with a last version keeps the invariant. -/
theorem nex_newKey (B : NodeId) (E : List NodeId) (g h : Nat) (leaf : Bool) (ks : List Klong)
    (c : Ctx) (w : W) (post : NodeId → W → Prop) (hv : ViewGood B c) (hw : CacheGood B c w)
    (hn : NEx E w) (hks : FlatAt c.i ks)
    (hp : ∀ x v, CacheGood B c v → Blank B c x → NEx E v → post x v) :
    WriterWP (newKey g h leaf ks) c w post := by
  refine writerWP_mono (writerWP_and (good_newKey B g h leaf ks c w _ hv hw (Or.inr hks)
    (fun x v hh => hh)) (?_ : WriterWP (newKey g h leaf ks) c w (fun _ v => NEx E v))) ?_
  · unfold newKey fresh
    wpSimplify
    split <;> wpSimplify
    all_goals
      intro q hq hk
      rcases List.mem_append.mp hq with hq | hq
      · exact hn q hq hk
      · have he := List.mem_singleton.mp hq
        subst q
        exact absurd hk (nex_flat_ne _ _ hks)
  · rintro x v ⟨⟨hc, hb⟩, hn'⟩
    exact hp x v hc hb hn'

/-- A new key node without klongs: it is pending. -/
theorem nex_newKey_empty (B : NodeId) (E : List NodeId) (g h : Nat) (leaf : Bool)
    (c : Ctx) (w : W) (post : NodeId → W → Prop) (hv : ViewGood B c) (hw : CacheGood B c w)
    (hn : NEx E w) (hp : ∀ x v, CacheGood B c v → Blank B c x → NEx (x :: E) v → post x v) :
    WriterWP (newKey g h leaf []) c w post := by
  refine writerWP_mono (writerWP_and (good_newKey B g h leaf [] c w _ hv hw (Or.inl rfl)
    (fun x v hh => hh)) (?_ : WriterWP (newKey g h leaf []) c w (fun x v => NEx (x :: E) v))) ?_
  · unfold newKey fresh
    wpSimplify
    split <;> wpSimplify
    all_goals
      intro q hq hk
      rcases List.mem_append.mp hq with hq | hq
      · exact List.mem_cons_of_mem _ (hn q hq hk)
      · have he := List.mem_singleton.mp hq
        subst q
        exact List.mem_cons_self
  · rintro x v ⟨⟨hc, hb⟩, hn'⟩
    exact hp x v hc hb hn'

theorem writerWP_of_ne {α : Type} {B : NodeId} {f : M α} (hf : KeepsNE B f)
    (E : List NodeId) (c : Ctx) (w : W) (post : α → W → Prop) (hv : ViewGood B c)
    (hw : CacheGood B c w) (hn : NEx E w) (hp : ∀ r v, CacheGood B c v → NEx E v → post r v) :
    WriterWP f c w post := writerWP_mono (hf E c w hv hw hn) (fun r v h => hp r v h.1 h.2)

/-- A step that keeps `Good` and changes no node keeps the invariant. -/
theorem keepsNE_of_nodes {α : Type} {B : NodeId} {f : M α} (hg : KeepsGood B f)
    (hs : ∀ c w, WriterWP f c w (fun _ v => v.nodes = w.nodes)) : KeepsNE B f := by
  intro E c w hv hw hn
  refine writerWP_mono (writerWP_and (hg c w hv hw) (hs c w)) ?_
  rintro r v ⟨hc, he⟩
  refine ⟨hc, ?_⟩
  intro q hq
  rw [he] at hq
  exact hn q hq

macro "neSame" : tactic => `(tactic| (
  intro c w
  repeat' first
    | wpSimplify
    | rfl
    | exact writerWP_throw _ _ _ _
    | split))

theorem nex_fresh (B : NodeId) : KeepsNE B fresh :=
  keepsNE_of_nodes (good_fresh B) (by unfold fresh; neSame)
theorem nex_note (B : NodeId) (s : String) : KeepsNE B (note s) :=
  keepsNE_of_nodes (good_note B s) (by unfold note; neSame)
theorem nex_takenBack (B : NodeId) (x : NodeId) : KeepsNE B (takenBack x) :=
  keepsNE_of_nodes (good_takenBack B x) (by unfold takenBack; neSame)
theorem nex_pathClear (B : NodeId) : KeepsNE B pathClear :=
  keepsNE_of_nodes (good_pathClear B) (by unfold pathClear; neSame)
theorem nex_pathAdd (B : NodeId) (cv : Option Nat) (x : NodeId) : KeepsNE B (pathAdd cv x) :=
  keepsNE_of_nodes (good_pathAdd B cv x) (by unfold pathAdd; neSame)
theorem nex_setMadeFor (B : NodeId) (x : NodeId) (old : Option NodeId) :
    KeepsNE B (setMadeFor x old) :=
  keepsNE_of_nodes (good_setMadeFor B x old) (by unfold setMadeFor; neSame)
theorem nex_newValue (B : NodeId) (h : Nat) : KeepsNE B (newValue h) :=
  keepsNE_of_nodes (good_newValue B h) (by unfold newValue fresh; neSame)
theorem nex_newSuperRoot (B : NodeId) (x : NodeId) : KeepsNE B (newSuperRoot x) :=
  keepsNE_of_nodes (good_newSuperRoot B x) (by unfold newSuperRoot note fresh; neSame)
theorem nex_replacedBy (B : NodeId) (x : NodeId) : KeepsNE B (replacedBy x) :=
  keepsNE_of_nodes (good_replacedBy B x) (by unfold replacedBy; neSame)
theorem nex_pathSize (B : NodeId) : KeepsNE B pathSize :=
  keepsNE_of_nodes (good_pathSize B) (by unfold pathSize; neSame)
theorem nex_pathNode (B : NodeId) (d : Nat) : KeepsNE B (pathNode d) :=
  keepsNE_of_nodes (good_pathNode B d) (by unfold pathNode; neSame)
theorem nex_klongAt (B : NodeId) (d : Nat) : KeepsNE B (klongAt d) :=
  keepsNE_of_nodes (good_klongAt B d) (by unfold klongAt; neSame)
theorem nex_parentAt (B : NodeId) (d : Nat) : KeepsNE B (parentAt d) :=
  keepsNE_of_nodes (good_parentAt B d) (by unfold parentAt pathNode; neSame)
theorem nex_findRoot (B : NodeId) : KeepsNE B findRoot :=
  keepsNE_of_nodes (good_findRoot B) (by unfold findRoot pathAdd; neSame)
theorem nex_throw (B : NodeId) {α : Type} (e : String) : KeepsNE B (throw e : M α) := by
  intro E c w hv hw hn
  exact writerWP_throw _ _ _ _

macro "neUse " h:term : tactic => `(tactic| (
  (with_unfolding_none refine' writerWP_of_ne $h ?neE _ _ _ ?gdView ?gdState ?neState ?gdPost)
  case neState => assumption
  case gdView => assumption
  case gdState => assumption
  intro _ _ _ _))

macro "neNode" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (getNode _) _ _ _)
  (refine writerWP_mono (nex_getNode ?gdB ?neE _ _ _ ?gdView ?gdState ?neState) ?gdPost)
  case gdView => assumption
  case gdState => assumption
  case neState => assumption
  rintro _ _ ⟨_, _, _, _, _⟩))

/-- Closes a postcondition. -/
macro "neDone" : tactic => `(tactic| exact ⟨by assumption, by assumption⟩)

theorem nex_ghOf (B : NodeId) (x : NodeId) : KeepsNE B (ghOf x) := by
  intro E c w hv hw hn
  unfold ghOf
  repeat' first
    | wpSimplify
    | neNode
    | exact writerWP_throw _ _ _ _
    | split
    | neDone

/-! ## The klongs stored -/

theorem nex_imp_add (n : KNode) (t : Time) (k : Klong) (P : Prop) : (n.add t k).ks = [] → P :=
  fun h => absurd h (nex_add_ne n t k)

theorem nex_imp_flat (i : Time) (n : KNode) (P : Prop) (hf : FlatAt i n.ks) : n.ks = [] → P :=
  fun h => absurd h (nex_flat_ne i n.ks hf)

theorem nex_imp_cons (leaf : Bool) (k : Klong) (r : List Klong) (P : Prop) :
    (⟨leaf, k :: r⟩ : KNode).ks = [] → P := fun h => by cases h

theorem nex_imp_fold (n : KNode) (i : Time) (ins : List (Nat × NodeId)) (P : Prop)
    (h : n.ks = [] → P) :
    (ins.foldl (fun n (q : Nat × NodeId) => n.add i (.key q.1 q.2)) n).ks = [] → P :=
  fun he => h (nex_fold_nil n i ins he)

theorem nex_imp_setAt (n : KNode) (j : Nat) (k : Klong) (P : Prop) (h : n.ks = [] → P) :
    (n.setAt j k).ks = [] → P := fun he => h (nex_setAt_nil n j k he)

theorem nex_imp_repoint (n : KNode) (j : Nat) (y : NodeId) (P : Prop) (h : n.ks = [] → P) :
    (n.repoint j y).ks = [] → P := fun he => h (nex_repoint_nil n j y he)

theorem nex_imp_zipIdx (n : KNode) (F : Klong × Nat → Klong) (P : Prop) (h : n.ks = [] → P) :
    ({ n with ks := n.ks.zipIdx.map F } : KNode).ks = [] → P := fun he => h (nex_zipIdx_nil n F he)

theorem nex_imp_ite (b : Prop) [Decidable b] (n m : KNode) (P : Prop) (h1 : n.ks = [] → P)
    (h2 : m.ks = [] → P) : (if b then n else m).ks = [] → P := by
  by_cases hb : b
  · simpa [hb] using h1
  · simpa [hb] using h2

/-- The node stored has a klong, or is the node read, which has one unless
it is pending. -/
syntax "neKs" : tactic
macro_rules
  | `(tactic| neKs) => `(tactic| first
    | assumption
    | exact nex_imp_add _ _ _ _
    | exact nex_imp_cons _ _ _ _
    | exact nex_imp_flat _ _ _ (by gdFlat)
    | (refine nex_imp_fold _ _ _ _ ?_; neKs)
    | (refine nex_imp_setAt _ _ _ _ ?_; neKs)
    | (refine nex_imp_repoint _ _ _ _ ?_; neKs)
    | (refine nex_imp_zipIdx _ _ _ ?_; neKs)
    | (refine nex_imp_ite _ _ _ _ ?_ ?_ <;> neKs)
    | (split <;> neKs))

/-- The `Good` input of a store, as the Good walk proves it. -/
macro "neGood" : tactic => `(tactic| first
  | gdKs
  | (apply Good.setLastDel' _ _ _ _ _ (by assumption) (by assumption); assumption)
  | (refine Good.lebWrite _ _ _ _ _ _ _ _ _ (by assumption) (by assumption) rfl rfl)
  | (refine Good.mergeWrite _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by assumption) (by assumption) rfl rfl ?_
     first
      | exact and3_right _ _ _
      | exact fun h => h)
  | exact Good.repointLink _ _ _ _ _ _ _ _ ‹ViewGood _ _› (by assumption) (by assumption)
      (Blank.ge _ _ _ ‹ViewGood _ _› (by gdBlank))
  | exact Good.repointLink _ _ _ _ _ _ _ _ ‹ViewGood _ _› (by assumption) (by assumption)
      (by assumption)
  | exact Good.retarget _ _ _ _ _ _ (by assumption) (by assumption) (by assumption))

macro "neStore" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (putNode _ _) _ _ _)
  (with_unfolding_none refine nex_putNode ?gdB ?neE _ _ _ _ _ ?gdState ?neState ?gdInput ?neInput ?gdPost)
  case gdState => assumption
  case neState => assumption
  case gdInput => neGood
  case neInput => neKs
  intro _ _ _ _))

/-- A store that fills a node: it is no longer pending. -/
macro "neFill" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (putNode _ _) _ _ _)
  (with_unfolding_none refine nex_putNode_fill ?gdB ?neE _ _ _ _ _ ?gdState ?neState ?gdInput ?neInput ?gdPost)
  case gdState => assumption
  case neState => assumption
  case neInput => first
    | exact nex_flat_ne _ _ (by gdFlat)
    | exact List.cons_ne_nil _ _
  case gdInput => neGood
  intro _ _ _ _))

macro "neCreate" : tactic => `(tactic| first
  | ((with_unfolding_none refine nex_newKey_empty ?gdB ?neE _ _ _ _ _ _ ?gdView ?gdState ?neState ?gdPost)
     case gdView => assumption
     case gdState => assumption
     case neState => assumption
     intro _ _ _ _ _)
  | ((with_unfolding_none guard_target = WriterWP (newKey _ _ _ _) _ _ _)
     (with_unfolding_none refine nex_newKey ?gdB ?neE _ _ _ _ _ _ _ ?gdView ?gdState ?neState ?gdInput ?gdPost)
     case gdView => assumption
     case gdState => assumption
     case neState => assumption
     case gdInput => gdFlat
     intro _ _ _ _ _))

macro "neCore" : tactic => `(tactic| first
  | neNode
  | neStore
  | neCreate
  | neUse (nex_pathAdd _ _ _)
  | neUse (nex_ghOf _ _)
  | neUse (nex_replacedBy _ _)
  | neUse (nex_pathSize _)
  | neUse (nex_pathNode _ _)
  | neUse (nex_klongAt _ _)
  | neUse (nex_parentAt _ _)
  | neUse (nex_findRoot _)
  | neUse (nex_note _ _)
  | neUse (nex_fresh _)
  | neUse (nex_newValue _ _)
  | neUse (nex_newSuperRoot _ _)
  | neUse (nex_setMadeFor _ _ _)
  | neUse (nex_takenBack _ _)
  | neUse (nex_pathClear _)
  | neDone
  | exact writerWP_throw _ _ _ _)

theorem nex_addKeys (B : NodeId) (x : NodeId) (ins : List (Nat × NodeId)) :
    KeepsNE B (addKeys x ins) := by
  intro E c w hv hw hn
  have hpos := hv.pos
  unfold addKeys
  repeat' first
    | wpSimplify
    | neCore
    | split

/-- The loop of a time split changes no state. -/
theorem nex_replaceOrAdd_same (last : KNode) (ins : List (Nat × NodeId)) (c : Ctx) (w : W) :
    WriterWP (replaceOrAdd last ins) c w (fun _ v => v = w) := by
  unfold replaceOrAdd
  simp only [writerWP_bind, writerWP_read]
  induction ins generalizing last with
  | nil => simp only [List.foldlM_nil, writerWP_pure]
  | cons q ins ih =>
    rw [List.foldlM_cons, writerWP_bind]
    split
    · exact writerWP_throw _ _ _ _
    · simp only [writerWP_pure]; exact ih _
    · simp only [writerWP_pure]; exact ih _

theorem nex_replaceOrAdd (B : NodeId) (last : KNode) (ins : List (Nat × NodeId)) :
    KeepsNE B (replaceOrAdd last ins) := by
  intro E c w hv hw hn
  refine writerWP_mono (nex_replaceOrAdd_same last ins c w) ?_
  rintro r v rfl
  exact ⟨hw, hn⟩

/-- What is left pending is pending before. -/
macro "neMem" : tactic => `(tactic| (
  intro y hy
  (try simp only [List.mem_filter, List.mem_cons, bne_iff_ne, ne_eq] at hy)
  grind))

/-- Closes a postcondition, the list of pending nodes back to the caller's. -/
macro "neClose" : tactic => `(tactic| exact ⟨by assumption, NEx.of (by assumption) (by neMem)⟩)

set_option maxHeartbeats 1600000 in
/-- Every route of a full node's replacement keeps the invariant: the new
nodes are filled before it returns, and a node that existed before the
transaction gets its klongs of P@(i-1). -/
theorem nex_handleFullWith (B : NodeId) (up : NodeId → List (Nat × NodeId) → M Unit)
    (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) (last : KNode) (compact : Bool)
    (E : List NodeId) (c : Ctx) (w : W) (hv : ViewGood B c) (hw : CacheGood B c w)
    (hn : NEx E w) (hlast : FlatAt c.i last.ks) (hup : ∀ q more, KeepsNE B (up q more)) :
    WriterWP (handleFullWith up depth x ins last compact) c w
      (fun _ v => CacheGood B c v ∧ NEx E v) := by
  have hpos := hv.pos
  unfold handleFullWith
  wpSimplify
  refine writerWP_mono (nex_getNode B E x c w hv hw hn) ?_
  rintro n0 w0 ⟨hc0, hn0, hg0, hr0, hb0⟩
  have hb1 : (!(n0.firstTime == some c.i)) = true → baseKlongs c.view x ≠ [] ∨ x ∈ E :=
    fun h => hb0 (by simpa using h)
  repeat' first
    | wpSimplify
    | (refine nex_putNode_toPrev B E x _ c _ _ (by assumption) (NEx.of (by assumption) (by neMem)) (by assumption) (hb1 (by assumption)) ?_
       intro _ _ _ _)
    | neFill
    | gdReplace
    | neCore
    | neUse (hup _ _)
    | wpSplit
    | split
    | contradiction
    | neClose

end SIS.Tree
