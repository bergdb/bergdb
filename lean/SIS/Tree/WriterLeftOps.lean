/-
The tree model (bergdb 024-12, TP7): the empty key in every inner node of the
writer's overlay (`LeftCache`), walked together with `CacheGood`
(SIS/Tree/WriterGood*.lean) and `Book` (SIS/Tree/WriterBook*.lean). A split
makes new inner nodes without klongs and fills them before it returns; the
invariant `LeftCacheE E` has a list E of the ids that may be such nodes. This
file: the writer's primitive steps.
-/
import SIS.Tree.WriterLeft

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- An inner node read as node x: without a klong only if x is pending, else
with the empty key live. -/
def LeftRead (E : List NodeId) (x : NodeId) (n : KNode) : Prop :=
  n.leaf = false → (n.ks = [] → x ∈ E) ∧ (n.ks ≠ [] → Live0 n)

/-- Every inner node of the overlay has the empty key live, but the pending
ones, which have no klong. -/
def LeftCacheE (E : List NodeId) (w : W) : Prop := ∀ q ∈ w.nodes, LeftRead E q.1 q.2

theorem LeftRead.node {x : NodeId} {n : KNode} (h : LeftRead [] x n) : LeftNode n := by
  intro hl
  obtain ⟨h1, h2⟩ := h hl
  have hne : n.ks ≠ [] := fun he => by cases h1 he
  exact ⟨hne, h2 hne⟩

theorem LeftRead.of_node {E : List NodeId} {x : NodeId} {n : KNode} (h : LeftNode n) :
    LeftRead E x n := by
  intro hl
  obtain ⟨h1, h2⟩ := h hl
  exact ⟨fun he => absurd he h1, fun _ => h2⟩

theorem LeftRead.not_mem {E : List NodeId} {x : NodeId} {n : KNode} (h : LeftRead E x n)
    (hx : x ∉ E) : LeftNode n := by
  intro hl
  obtain ⟨h1, h2⟩ := h hl
  have hne : n.ks ≠ [] := fun he => hx (h1 he)
  exact ⟨hne, h2 hne⟩

theorem leftCache_of_nil {w : W} (h : LeftCacheE [] w) : LeftCache w :=
  fun q hq => (h q hq).node

theorem LeftCacheE.mono {E E' : List NodeId} {w : W} (hs : ∀ y ∈ E, y ∈ E') (h : LeftCacheE E w) :
    LeftCacheE E' w := by
  intro q hq hl
  obtain ⟨h1, h2⟩ := h q hq hl
  exact ⟨fun he => hs _ (h1 he), h2⟩

theorem LeftCacheE.of {E E' : List NodeId} {w : W} (h : LeftCacheE E w) (hs : ∀ y ∈ E, y ∈ E') :
    LeftCacheE E' w := LeftCacheE.mono hs h

/-! ## The empty key's live klong in a node of the view -/

/-- A node of the overlay with klongs in the view: its klongs there, with its
leaf flag, have the empty key live (the books give the view's level). -/
theorem left_base (B : NodeId) (c : Ctx) (w : W) (hv : ViewGood B c)
    (hl : ViewLeftOK c.p c.view) (hb : Book B c w) (x : NodeId) (n0 : KNode)
    (hx : w.nodes.lookup x = some n0) (hbase : baseKlongs c.view x ≠ []) :
    LeftNode ⟨n0.leaf, baseKlongs c.view x⟩ := by
  cases hvx : c.view x with
  | none => simp [baseKlongs, hvx] at hbase
  | some nd =>
    have hmem := bk_mem_of_lookup _ _ _ hx
    have hid : x ∈ w.gh.map (·.1) := by
      have := bk_mem_ids_of_mem _ _ _ hmem
      rw [hb.ids] at this
      exact List.mem_reverse.mp this
    obtain ⟨⟨x', g, h⟩, hq, hqe⟩ := List.mem_map.mp hid
    simp only at hqe
    subst hqe
    have hleaf := hb.leaf x' n0 g h hmem hq
    rcases hb.tag x' g h hq with ⟨nd', hnd', hd, hlev, _, hh⟩ | ⟨hB, _, _⟩
    · rw [hvx] at hnd'
      cases hnd'
      have := hl x' nd hvx hd hlev
      rw [hleaf, hh]
      simpa [baseKlongs, hvx] using this
    · have := hv.ids x' nd hvx
      omega

/-! ## The primitive steps -/

theorem left_getNode_only (E : List NodeId) (x : NodeId) (c : Ctx) (w : W)
    (hl : ViewLeftOK c.p c.view) (hn : LeftCacheE E w) :
    WriterWP (getNode x) c w (fun n v => LeftCacheE E v ∧ LeftRead E x n) := by
  unfold getNode
  simp only [writerWP_bind, writerWP_get]
  split
  · rename_i n hn'
    simp only [writerWP_pure]
    refine ⟨hn, ?_⟩
    obtain ⟨pre, post, he, _⟩ := List.lookup_eq_some_iff.mp hn'
    exact hn (x, n) (by rw [he]; simp)
  · simp only [writerWP_bind, writerWP_read]
    split
    · rename_i nd hnd
      split
      · exact writerWP_throw _ _ _ _
      · rename_i hkind
        have hd : nd.isData = false := by cases hd : nd.isData <;> simp_all
        have hlv : nd.level ≤ c.p.keyMax := by
          have hh : ¬ c.p.keyMax < nd.level := by
            intro h; simp [h] at hkind
          omega
        have hnode : LeftRead E x ⟨c.p.heightOf nd.level == 0, klongsOf nd.hist⟩ :=
          LeftRead.of_node (hl x nd hnd hd hlv)
        simp only [writerWP_bind, writerWP_set, writerWP_pure]
        refine ⟨?_, hnode⟩
        intro q hq
        rcases List.mem_append.mp hq with hq | hq
        · exact hn q hq
        · have heq := List.mem_singleton.mp hq
          subst q
          exact hnode
    · exact writerWP_throw _ _ _ _

/-- A node read: `Good`, in the overlay, and with the empty key live if it is
inner and not pending. -/
theorem left_getNode (B : NodeId) (E : List NodeId) (x : NodeId) (c : Ctx) (w : W)
    (hv : ViewGood B c) (hl : ViewLeftOK c.p c.view) (hw : CacheGood B c w) (hb : Book B c w)
    (hn : LeftCacheE E w) :
    WriterWP (getNode x) c w (fun n v => CacheGood B c v ∧ Book B c v ∧ Kept w v ∧
      LeftCacheE E v ∧ Good B c x n ∧ v.nodes.lookup x = some n ∧ LeftRead E x n) := by
  refine writerWP_mono (writerWP_and (writerWP_and (good_getNode B x c w hv hw)
    (book_getNode B x c w hv.ids hb)) (left_getNode_only E x c w hl hn)) ?_
  rintro n v ⟨⟨⟨hc, hg⟩, hb', hk, hlk⟩, hn', hr⟩
  exact ⟨hc, hb', hk, hn', hg, hlk, hr⟩

theorem left_upsert_fill (E : List NodeId) (ns : List (NodeId × KNode)) (x : NodeId) (n : KNode)
    (hn : ∀ q ∈ ns, LeftRead E q.1 q.2) (hx : LeftNode n) :
    ∀ q ∈ upsert ns x n, LeftRead (E.filter (fun y => y != x)) q.1 q.2 := by
  intro q hq
  unfold upsert at hq
  split at hq
  · obtain ⟨a, ha, he⟩ := List.mem_map.mp hq
    split at he
    · cases he; exact LeftRead.of_node hx
    · rename_i hax
      cases he
      intro hl
      obtain ⟨h1, h2⟩ := hn _ ha hl
      refine ⟨fun hk => List.mem_filter.mpr ⟨h1 hk, ?_⟩, h2⟩
      simpa using hax
  · rename_i hany
    rcases List.mem_append.mp hq with hq | hq
    · intro hl
      obtain ⟨h1, h2⟩ := hn q hq hl
      refine ⟨fun hk => List.mem_filter.mpr ⟨h1 hk, ?_⟩, h2⟩
      have : q.1 ≠ x := by
        intro hq1
        apply hany
        exact List.any_eq_true.mpr ⟨q, hq, by simp [hq1]⟩
      simpa using this
    · have he := List.mem_singleton.mp hq
      subst q; exact LeftRead.of_node hx

/-- A store of a node with the empty key live (or a leaf): x is no longer
pending. -/
theorem left_putNode (B : NodeId) (E : List NodeId) (x : NodeId) (n' : KNode) (c : Ctx)
    (vr w : W) (n0 : KNode) (post : Unit → W → Prop) (hw : CacheGood B c w) (hb : Book B c w)
    (hn : LeftCacheE E w) (hg : Good B c x n') (hleaf : n'.leaf = n0.leaf)
    (hl : vr.nodes.lookup x = some n0) (hk : Kept vr w) (hx : LeftNode n')
    (hp : ∀ r v, CacheGood B c v → Book B c v → Kept w v →
      LeftCacheE (E.filter (fun y => y != x)) v → post r v) :
    WriterWP (putNode x n') c w post := by
  refine writerWP_mono (writerWP_and (writerWP_and
    (good_putNode B x n' c w (fun _ v => CacheGood B c v) hw hg (fun _ _ h => h))
    (book_putNode_of B x n' c vr w n0 hb hleaf hl hk))
    (?_ : WriterWP (putNode x n') c w (fun _ v => LeftCacheE (E.filter (fun y => y != x)) v))) ?_
  · simp only [putNode, writerWP_modify]
    exact left_upsert_fill E w.nodes x n' hn hx
  · rintro r v ⟨⟨hc, hb', hk'⟩, hn'⟩
    exact hp r v hc hb' hk' hn'

theorem left_newKey_only (E : List NodeId) (g h : Nat) (leaf : Bool) (ks : List Klong)
    (c : Ctx) (w : W) (hn : LeftCacheE E w) (hx : LeftNode ⟨leaf, ks⟩) :
    WriterWP (newKey g h leaf ks) c w (fun _ v => LeftCacheE E v) := by
  unfold newKey fresh
  wpSimplify
  split <;> wpSimplify
  all_goals
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hn q hq
    · have he := List.mem_singleton.mp hq
      subst q
      exact LeftRead.of_node hx

theorem left_newKey_empty_only (E : List NodeId) (g h : Nat) (leaf : Bool)
    (c : Ctx) (w : W) (hn : LeftCacheE E w) :
    WriterWP (newKey g h leaf []) c w (fun x v => LeftCacheE (x :: E) v) := by
  unfold newKey fresh
  wpSimplify
  split <;> wpSimplify
  all_goals
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · intro hl
      obtain ⟨h1, h2⟩ := hn q hq hl
      exact ⟨fun hk => List.mem_cons_of_mem _ (h1 hk), h2⟩
    · have he := List.mem_singleton.mp hq
      subst q
      intro _
      exact ⟨fun _ => List.mem_cons_self, fun hk => absurd rfl hk⟩

/-- A new key node with a last version with the empty key live (or a leaf). -/
theorem left_newKey (B : NodeId) (E : List NodeId) (g h : Nat) (leaf : Bool) (ks : List Klong)
    (c : Ctx) (w : W) (post : NodeId → W → Prop) (hv : ViewGood B c) (hw : CacheGood B c w)
    (hb : Book B c w) (hn : LeftCacheE E w) (hks : FlatAt c.i ks) (hh : leaf = (h == 0))
    (hx : LeftNode ⟨leaf, ks⟩)
    (hp : ∀ x v, CacheGood B c v → Blank B c x → Book B c v → Kept w v →
      v.nodes.lookup x = some ⟨leaf, ks⟩ → LeftCacheE E v → post x v) :
    WriterWP (newKey g h leaf ks) c w post := by
  refine writerWP_mono (writerWP_and (writerWP_and
    (good_newKey B g h leaf ks c w _ hv hw (Or.inr hks) (fun x v hh => hh))
    (book_newKey B g h leaf ks c w hb hh)) (left_newKey_only E g h leaf ks c w hn hx)) ?_
  rintro x v ⟨⟨⟨hc, hbl⟩, hb', hk, hlk⟩, hn'⟩
  exact hp x v hc hbl hb' hk hlk hn'

/-- A new key node without klongs: it is pending. -/
theorem left_newKey_empty (B : NodeId) (E : List NodeId) (g h : Nat) (leaf : Bool)
    (c : Ctx) (w : W) (post : NodeId → W → Prop) (hv : ViewGood B c) (hw : CacheGood B c w)
    (hb : Book B c w) (hn : LeftCacheE E w) (hh : leaf = (h == 0))
    (hp : ∀ x v, CacheGood B c v → Blank B c x → Book B c v → Kept w v →
      v.nodes.lookup x = some ⟨leaf, []⟩ → LeftCacheE (x :: E) v → post x v) :
    WriterWP (newKey g h leaf []) c w post := by
  refine writerWP_mono (writerWP_and (writerWP_and
    (good_newKey B g h leaf [] c w _ hv hw (Or.inl rfl) (fun x v hh => hh))
    (book_newKey B g h leaf [] c w hb hh)) (left_newKey_empty_only E g h leaf c w hn)) ?_
  rintro x v ⟨⟨⟨hc, hbl⟩, hb', hk, hlk⟩, hn'⟩
  exact hp x v hc hbl hb' hk hlk hn'

/-! ## Steps that store nothing -/

def KeepsLeft (B : NodeId) {α : Type} (f : M α) : Prop :=
  ∀ (E : List NodeId) c w, ViewGood B c → MergeParamsOK c.p → ViewLeftOK c.p c.view →
    CacheGood B c w → Book B c w → LeftCacheE E w →
    WriterWP f c w (fun _ v => CacheGood B c v ∧ Book B c v ∧ Kept w v ∧ LeftCacheE E v)

/-- The same for the steps that need no pending node. -/
def KeepsLeft0 (B : NodeId) {α : Type} (f : M α) : Prop :=
  ∀ c w, ViewGood B c → MergeParamsOK c.p → ViewLeftOK c.p c.view →
    CacheGood B c w → Book B c w → LeftCacheE [] w →
    WriterWP f c w (fun _ v => CacheGood B c v ∧ Book B c v ∧ Kept w v ∧ LeftCacheE [] v)

theorem KeepsLeft.zero {B : NodeId} {α : Type} {f : M α} (h : KeepsLeft B f) : KeepsLeft0 B f :=
  fun c w => h [] c w

theorem writerWP_of_left {α : Type} {B : NodeId} {f : M α} (hf : KeepsLeft B f)
    (E : List NodeId) (c : Ctx) (w : W) (post : α → W → Prop) (hv : ViewGood B c)
    (hp : MergeParamsOK c.p) (hl : ViewLeftOK c.p c.view) (hw : CacheGood B c w)
    (hb : Book B c w) (hn : LeftCacheE E w)
    (hq : ∀ r v, CacheGood B c v → Book B c v → Kept w v → LeftCacheE E v → post r v) :
    WriterWP f c w post :=
  writerWP_mono (hf E c w hv hp hl hw hb hn) (fun r v h => hq r v h.1 h.2.1 h.2.2.1 h.2.2.2)

theorem writerWP_of_left0 {α : Type} {B : NodeId} {f : M α} (hf : KeepsLeft0 B f)
    (c : Ctx) (w : W) (post : α → W → Prop) (hv : ViewGood B c)
    (hp : MergeParamsOK c.p) (hl : ViewLeftOK c.p c.view) (hw : CacheGood B c w)
    (hb : Book B c w) (hn : LeftCacheE [] w)
    (hq : ∀ r v, CacheGood B c v → Book B c v → Kept w v → LeftCacheE [] v → post r v) :
    WriterWP f c w post :=
  writerWP_mono (hf c w hv hp hl hw hb hn) (fun r v h => hq r v h.1 h.2.1 h.2.2.1 h.2.2.2)

/-- A step that keeps `Good` and the books and changes no node. -/
theorem keepsLeft_of_nodes {α : Type} {B : NodeId} {f : M α} (hg : KeepsGood B f)
    (hbk : KeepsBook B f) (hs : ∀ c w, WriterWP f c w (fun _ v => v.nodes = w.nodes)) :
    KeepsLeft B f := by
  intro E c w hv _ _ hw hb hn
  refine writerWP_mono (writerWP_and (writerWP_and (hg c w hv hw) (hbk c w hv.ids hb)) (hs c w)) ?_
  rintro r v ⟨⟨hc, hb', hk⟩, he⟩
  refine ⟨hc, hb', hk, ?_⟩
  intro q hq
  rw [he] at hq
  exact hn q hq

theorem left_throw (B : NodeId) {α : Type} (e : String) : KeepsLeft B (throw e : M α) := by
  intro E c w _ _ _ _ _ _
  exact writerWP_throw _ _ _ _

theorem left_fresh (B : NodeId) : KeepsLeft B fresh :=
  keepsLeft_of_nodes (good_fresh B) (book_fresh B) (by unfold fresh; neSame)
theorem left_note (B : NodeId) (s : String) : KeepsLeft B (note s) :=
  keepsLeft_of_nodes (good_note B s) (book_note B s) (by unfold note; neSame)
theorem left_pathClear (B : NodeId) : KeepsLeft B pathClear :=
  keepsLeft_of_nodes (good_pathClear B) (book_pathClear B) (by unfold pathClear; neSame)
theorem left_pathAdd (B : NodeId) (cv : Option Nat) (x : NodeId) : KeepsLeft B (pathAdd cv x) :=
  keepsLeft_of_nodes (good_pathAdd B cv x) (book_pathAdd B cv x) (by unfold pathAdd; neSame)
theorem left_setMadeFor (B : NodeId) (x : NodeId) (old : Option NodeId) :
    KeepsLeft B (setMadeFor x old) :=
  keepsLeft_of_nodes (good_setMadeFor B x old) (book_setMadeFor B x old)
    (by unfold setMadeFor; neSame)
theorem left_newValue (B : NodeId) (h : Nat) : KeepsLeft B (newValue h) :=
  keepsLeft_of_nodes (good_newValue B h) (book_newValue B h) (by unfold newValue fresh; neSame)
theorem left_newSuperRoot (B : NodeId) (x : NodeId) : KeepsLeft B (newSuperRoot x) :=
  keepsLeft_of_nodes (good_newSuperRoot B x) (book_newSuperRoot B x)
    (by unfold newSuperRoot note fresh; neSame)
theorem left_replacedBy (B : NodeId) (x : NodeId) : KeepsLeft B (replacedBy x) :=
  keepsLeft_of_nodes (good_replacedBy B x) (book_replacedBy B x) (by unfold replacedBy; neSame)
theorem left_pathSize (B : NodeId) : KeepsLeft B pathSize :=
  keepsLeft_of_nodes (good_pathSize B) (book_pathSize B) (by unfold pathSize; neSame)
theorem left_pathNode (B : NodeId) (d : Nat) : KeepsLeft B (pathNode d) :=
  keepsLeft_of_nodes (good_pathNode B d) (book_pathNode B d) (by unfold pathNode; neSame)
theorem left_klongAt (B : NodeId) (d : Nat) : KeepsLeft B (klongAt d) :=
  keepsLeft_of_nodes (good_klongAt B d) (book_klongAt B d) (by unfold klongAt; neSame)
theorem left_parentAt (B : NodeId) (d : Nat) : KeepsLeft B (parentAt d) :=
  keepsLeft_of_nodes (good_parentAt B d) (book_parentAt B d) (by unfold parentAt pathNode; neSame)
theorem left_findRoot (B : NodeId) : KeepsLeft B findRoot :=
  keepsLeft_of_nodes (good_findRoot B) (book_findRoot B) (by unfold findRoot pathAdd; neSame)

/-! ## The tactics of the walk -/

/-- What is left pending is pending before. -/
macro "lfMem" : tactic => `(tactic| (
  intro y hy
  (try simp only [List.mem_filter, List.mem_cons, bne_iff_ne, ne_eq, List.not_mem_nil,
    List.filter_nil] at hy)
  grind))

macro "lfState" : tactic => `(tactic| first
  | assumption
  | exact LeftCacheE.of (by assumption) (by lfMem))

macro "lfUse " h:term : tactic => `(tactic| (
  (with_unfolding_none refine' writerWP_of_left $h ?lfE _ _ _ ?gdView ?lfP ?lfView ?gdState ?bkState ?lfState ?gdPost)
  case gdView => assumption
  case lfP => assumption
  case lfView => assumption
  case gdState => assumption
  case bkState => bkState
  case lfState => lfState
  intro _ _ _ _ _ _))

macro "lfUse0 " h:term : tactic => `(tactic| (
  (with_unfolding_none refine' writerWP_of_left0 $h _ _ _ ?gdView ?lfP ?lfView ?gdState ?bkState ?lfState ?gdPost)
  case gdView => assumption
  case lfP => assumption
  case lfView => assumption
  case gdState => assumption
  case bkState => bkState
  case lfState => lfState
  intro _ _ _ _ _ _))

macro "lfNode" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (getNode _) _ _ _)
  (refine writerWP_mono (left_getNode ?gdB ?lfE _ _ _ ?gdView ?lfView ?gdState ?bkState ?lfState) ?gdPost)
  case gdView => assumption
  case lfView => assumption
  case gdState => assumption
  case bkState => bkState
  case lfState => assumption
  rintro _ _ ⟨_, _, _, _, _, _, _⟩))

/-- Closes a postcondition. -/
macro "lfDone" : tactic => `(tactic| (
  (with_unfolding_none guard_target = CacheGood _ _ _ ∧ Book _ _ _ ∧ Kept _ _ ∧ LeftCacheE _ _)
  exact ⟨by assumption, by bkState, by bkChain, by assumption⟩))

theorem left_ghOf (B : NodeId) (x : NodeId) : KeepsLeft B (ghOf x) := by
  intro E c w hv hp hl hw hb hn
  unfold ghOf
  repeat' first
    | wpSimplify
    | lfNode
    | exact writerWP_throw _ _ _ _
    | split
    | lfDone

/-! ## The nodes the splits store -/

theorem left_node_of (leaf : Bool) (i : Time) (ks : List Klong) (hf : FlatAt i ks)
    (hH : leaf = false → Head0 ks) : LeftNode ⟨leaf, ks⟩ := by
  cases leaf with
  | true => exact left_leaf _ rfl
  | false => exact left_of_head0_flat false i ks hf (hH rfl)

theorem left_root3 (leaf : Bool) (t : Time) (a : NodeId) (sc : Nat) (b : NodeId) :
    LeftNode ⟨leaf, [.time t, .key 0 a, .key sc b]⟩ :=
  left_of_head0_nodel leaf _ ⟨t, a, _, rfl⟩ (by intro bits hm; simp at hm)

theorem left_size_of {b : Bool} {s : Nat} {p : Params}
    (h : (b && decide (s > p.splitAbove)) = true) (hp : MergeParamsOK p) : 3 ≤ s := by
  obtain ⟨h1, -, h3, -⟩ := hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  omega

theorem left_flat_drop (i : Time) (ks : List Klong) (hf : FlatAt i ks) :
    ∀ k ∈ ks.drop 1, ∃ cv y, k = Klong.key cv y := by
  obtain ⟨r, hr, hk⟩ := hf
  rw [hr]
  exact hk

theorem left_halves1 (leaf : Bool) (t i : Time) (last : KNode) (ins : List (Nat × NodeId))
    (hf : FlatAt i last.ks) (hH : leaf = false → Head0 last.ks) (hs : 3 ≤ last.size) :
    LeftNode (halves leaf t last ins).1 := by
  cases leaf with
  | true => exact left_leaf _ (bk_halves_fst_leaf _ _ _ _)
  | false =>
    intro _
    exact left_of_head0_flat false t _
      (halves_flatAt false t last ins (FlatAt.flat _ _ hf)).1
      (left_halves t last ins (hH rfl) hs (left_flat_drop i _ hf)).1 rfl

theorem left_halves2 (leaf : Bool) (t i : Time) (last : KNode) (ins : List (Nat × NodeId))
    (hf : FlatAt i last.ks) (hH : leaf = false → Head0 last.ks) (hs : 3 ≤ last.size) :
    LeftNode (halves leaf t last ins).2.1 := by
  cases leaf with
  | true => exact left_leaf _ (bk_halves_snd_leaf _ _ _ _)
  | false =>
    intro _
    exact left_of_head0_flat false t _
      (halves_flatAt false t last ins (FlatAt.flat _ _ hf)).2
      (left_halves t last ins (hH rfl) hs (left_flat_drop i _ hf)).2 rfl

theorem left_node_of2 (leaf : Bool) (i : Time) (ks last : List Klong) (hf : FlatAt i ks)
    (h1 : leaf = false → Head0 last) (h2 : Head0 last → Head0 ks) : LeftNode ⟨leaf, ks⟩ :=
  left_node_of leaf i ks hf (fun h => h2 (h1 h))

theorem left_base_of_kept {P : Prop} {a b : W} {x : NodeId} {n n' : KNode}
    (h : n.leaf = false → P) (ha : a.nodes.lookup x = some n) (hb : b.nodes.lookup x = some n')
    (hk : Kept a b) : n'.leaf = false → P := by
  intro hl
  apply h
  rw [← nex_run_kept_leaf hk ha hb]
  exact hl

/-- The klongs of a node of the view, stored back with its leaf flag. -/
theorem left_toPrev (B : NodeId) (c : Ctx) (w : W) (x : NodeId) (n : KNode) (hv : ViewGood B c)
    (hl : ViewLeftOK c.p c.view) (hb : Book B c w) (hlk : w.nodes.lookup x = some n)
    (hg : Good B c x n) (hbase : n.leaf = false → baseKlongs c.view x ≠ []) :
    LeftNode (n.toPrev (c.i - 1)) := by
  cases hn : n.leaf with
  | true => exact left_leaf _ hn
  | false =>
    have h := left_base B c w hv hl hb x n hlk (hbase hn)
    have he : n.toPrev (c.i - 1) = ⟨n.leaf, baseKlongs c.view x⟩ := by
      show (⟨n.leaf, prefixAt n.ks (c.i - 1)⟩ : KNode) = _
      rw [hg.old]
    rw [he]
    exact h

/-- The store of a node's klongs of P@(i-1). -/
theorem left_putNode_toPrev (B : NodeId) (E : List NodeId) (x : NodeId) (n : KNode) (c : Ctx)
    (w : W) (post : Unit → W → Prop) (hv : ViewGood B c) (hl : ViewLeftOK c.p c.view)
    (hw : CacheGood B c w) (hb : Book B c w) (hn : LeftCacheE E w) (hg : Good B c x n)
    (hlk : w.nodes.lookup x = some n) (hbase : n.leaf = false → baseKlongs c.view x ≠ [])
    (hp : ∀ r v, CacheGood B c v → Book B c v → Kept w v →
      LeftCacheE (E.filter (fun y => y != x)) v → post r v) :
    WriterWP (putNode x (n.toPrev (c.i - 1))) c w post :=
  left_putNode B E x _ c w w n post hw hb hn (Good.toPrev B c x n hg) rfl hlk (Kept.refl w)
    (left_toPrev B c w x n hv hl hb hlk hg hbase) hp

/-- The loop of a time split: a last version at the transaction's time, with the
empty key first if `last` has it first; no state changes. -/
theorem left_replaceOrAdd_both (last : KNode) (ins : List (Nat × NodeId)) (c : Ctx) (w : W)
    (hlast : FlatAt c.i last.ks) :
    WriterWP (replaceOrAdd last ins) c w
      (fun out v => FlatAt c.i out.ks ∧ v = w ∧ (Head0 last.ks → Head0 out.ks)) := by
  refine writerWP_mono (writerWP_and (writerWP_replaceOrAdd_flat last ins c w hlast)
    (left_replaceOrAdd last ins c w)) ?_
  rintro out v ⟨⟨h1, h2⟩, _, h3⟩
  exact ⟨h1, h2, h3⟩

/-! ## The tactics of the stores -/

/-- An inner node read, and not pending. -/
macro "lfRead" : tactic => `(tactic| first
  | exact LeftRead.node (by assumption)
  | exact LeftRead.not_mem (by assumption) (by simp_all)
  | assumption)

syntax "lfKs" : tactic
macro_rules
  | `(tactic| lfKs) => `(tactic| first
    | assumption
    | exact left_root3 _ _ _ _ _
    | exact LeftNode.add_key (by lfRead) _ _ _
    | exact LeftNode.fold_add (by lfRead) _ _
    | exact LeftNode.repoint (by lfRead) _ _
    | exact left_leaf _ (by assumption)
    | exact left_halves1 _ _ _ _ _ (by gdFlat) (by assumption)
        (left_size_of (by assumption) (by assumption))
    | exact left_halves2 _ _ _ _ _ (by gdFlat) (by assumption)
        (left_size_of (by assumption) (by assumption))
    | exact left_node_of _ _ _ (by gdFlat) (by assumption)
    | exact left_node_of2 _ _ _ _ (by gdFlat) (by assumption) (by assumption)
    | (split <;> lfKs))

syntax "lfLeaf" : tactic
macro_rules
  | `(tactic| lfLeaf) => `(tactic| first
    | bkLeaf
    | (split <;> lfLeaf))

macro "lfStore" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (putNode _ _) _ _ _)
  (refine left_putNode ?gdB ?lfE _ _ _ ?bkVr _ ?bkN _ ?gdState ?bkState ?lfState ?gdInput ?bkLeaf ?bkLook ?bkKept ?lfInput ?gdPost)
  case gdState => assumption
  case bkState => bkState
  case lfState => assumption
  case bkLook => assumption
  case bkLeaf => lfLeaf
  case bkKept => bkChain
  case gdInput => neGood
  case lfInput => lfKs
  intro _ _ _ _ _ _))

macro "lfCreate" : tactic => `(tactic| first
  | ((with_unfolding_none refine left_newKey_empty ?gdB ?lfE _ _ _ _ _ _ ?gdView ?gdState ?bkState ?lfState ?bkH ?gdPost)
     case gdView => assumption
     case gdState => assumption
     case bkState => bkState
     case lfState => assumption
     case bkH => bkHeight
     intro _ _ _ _ _ _ _ _)
  | ((with_unfolding_none guard_target = WriterWP (newKey _ _ _ _) _ _ _)
     (with_unfolding_none refine left_newKey ?gdB ?lfE _ _ _ _ _ _ _ ?gdView ?gdState ?bkState ?lfState ?gdInput ?bkH ?lfInput ?gdPost)
     case gdView => assumption
     case gdState => assumption
     case bkState => bkState
     case lfState => assumption
     case gdInput => gdFlat
     case bkH => bkHeight
     case lfInput => lfKs
     intro _ _ _ _ _ _ _ _))

/-- The segment and the height of a node read before: no change. -/
macro "lfGh" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (ghOf _) _ _ _)
  first
    | (refine writerWP_mono (book_ghOf_leaf ?bkB _ _ ?bkVr _ ?bkN ?bkLook ?bkKept ?bkState) ?bkPost
       case bkLook => assumption
       case bkKept => bkChain
       case bkState => bkState
       rintro ⟨_, _⟩ _ ⟨hbkEq, _⟩
       subst hbkEq)
    | lfUse (left_ghOf _ _)))

macro "lfClose" : tactic => `(tactic| (
  (with_unfolding_none guard_target = CacheGood _ _ _ ∧ Book _ _ _ ∧ Kept _ _ ∧ LeftCacheE _ _)
  exact ⟨by assumption, by bkState, by bkChain, by lfState⟩))

macro "lfCore" : tactic => `(tactic| first
  | lfClose
  | lfNode
  | lfStore
  | lfCreate
  | lfGh
  | lfUse (left_pathAdd _ _ _)
  | lfUse (left_replacedBy _ _)
  | lfUse (left_pathSize _)
  | lfUse (left_pathNode _ _)
  | lfUse (left_klongAt _ _)
  | lfUse (left_parentAt _ _)
  | lfUse (left_findRoot _)
  | lfUse (left_note _ _)
  | lfUse (left_fresh _)
  | lfUse (left_newValue _ _)
  | lfUse (left_newSuperRoot _ _)
  | lfUse (left_setMadeFor _ _ _)
  | lfUse (left_pathClear _)
  | exact writerWP_throw _ _ _ _)

theorem left_addKeys (B : NodeId) (x : NodeId) (ins : List (Nat × NodeId)) :
    KeepsLeft0 B (addKeys x ins) := by
  intro c w hv hp hl hw hb hn
  have hpos := hv.pos
  unfold addKeys
  repeat' first
    | wpSimplify
    | lfCore
    | split

macro "lfReplace" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (replaceOrAdd _ _) _ _ _)
  refine writerWP_mono (left_replaceOrAdd_both _ _ _ _ ?gdLast) ?gdPost
  case gdLast => gdFlat
  rintro out v ⟨hout, heq, hhead⟩
  subst v))

end SIS.Tree
