/-
The tree model (bergdb 024-12, TP7): every key node of the writer's overlay has
a klong at a transaction's end (`execW_nonempty`). The walk of
SIS/Tree/WriterNonempty*.lean covers every writer function but the put's loop
over the key's segments: `setNode` makes a new segment leaf without a klong,
and the next step of the put fills it. That step starts from the new leaf:
its descent stops there at once (the node is a leaf), and its store adds a
klong to it. This file walks that hand-over with `CacheGood`, `Book`
(SIS/Tree/WriterBook*.lean) and `NEx` together.
-/
import SIS.Tree.WriterNonemptyMerge
import SIS.Tree.WriterBookMerge

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The state at the hand-over from one segment to the next, for the node r
that the next step starts from: only r may be without a klong, and then it is
a segment leaf. -/
def nexRunPend (w : W) (r : NodeId) : Prop :=
  NEx [r] w ∧ ∀ n, w.nodes.lookup r = some n → n.ks = [] → n.leaf = true

theorem nex_run_pend_of_nil (w : W) (r : NodeId) (h : NEx [] w) : nexRunPend w r := by
  refine ⟨NEx.mono (fun y hy => by cases hy) h, ?_⟩
  intro n hl hk
  exact absurd (nex_lookup [] w h r n hl hk) (fun hm => by cases hm)

/-! ## The overlay's ids are distinct -/

theorem nex_run_lookup_of_mem (ns : List (NodeId × KNode)) (x : NodeId) (m : KNode)
    (hd : (ns.map (·.1)).Nodup) (hm : (x, m) ∈ ns) : ns.lookup x = some m := by
  induction ns with
  | nil => cases hm
  | cons q ns ih =>
    obtain ⟨a, b⟩ := q
    simp only [List.map_cons, List.nodup_cons] at hd
    rcases List.mem_cons.mp hm with he | hm'
    · cases he
      simp [List.lookup]
    · have hxa : x ≠ a := by
        intro he
        subst he
        exact hd.1 (bk_mem_ids_of_mem _ _ _ hm')
      have hb : (x == a) = false := by simpa using hxa
      simp only [List.lookup, hb]
      exact ih hd.2 hm'

theorem nex_run_nodup (B : NodeId) (c : Ctx) (w : W) (hb : Book B c w) :
    (w.nodes.map (·.1)).Nodup := by
  rw [hb.ids]
  exact (List.reverse_perm _).nodup_iff.mpr hb.nodup

/-- A node of the overlay with a klong is no longer pending. -/
theorem nex_run_drop (B : NodeId) (c : Ctx) (E : List NodeId) (w : W) (r : NodeId) (n : KNode)
    (hb : Book B c w) (hl : w.nodes.lookup r = some n) (hne : n.ks ≠ []) (h : NEx (r :: E) w) :
    NEx E w := by
  intro q hq hk
  rcases List.mem_cons.mp (h q hq hk) with he | he
  · obtain ⟨x, m⟩ := q
    simp only at he hk
    subst he
    have := nex_run_lookup_of_mem _ _ _ (nex_run_nodup B c w hb) hq
    rw [hl] at this
    cases this
    exact absurd hk hne
  · exact he

/-! ## An empty node -/

theorem nex_run_searchEq_nil (n : KNode) (t : Time) (cv : Nat) (h : n.ks = []) :
    n.searchEq t cv = none := by
  unfold KNode.searchEq
  rw [h]
  simp [prefixAt]

theorem nex_run_deadOver_nil (p : Params) (n : KNode) (t : Time) (cv : Nat) (y : NodeId)
    (h : n.ks = []) : deadOver p (n.add t (.key cv y)) = false := by
  obtain ⟨leaf, ks⟩ := n
  simp only at h
  subst h
  simp [deadOver, KNode.add, KNode.lastTime, KNode.deadCount, KNode.lastBitmap, lastBitmapOf,
    List.zipIdx]

theorem nex_run_size_nil (n : KNode) (h : n.ks = []) : n.size = 0 := by
  simp [KNode.size, h]

/-! ## The three invariants together -/

theorem nex_run_step {α : Type} {B : NodeId} {f : M α} (hne : KeepsNE B f) (hbk : KeepsBook B f)
    (E : List NodeId) (c : Ctx) (w : W) (post : α → W → Prop) (hv : ViewGood B c)
    (hw : CacheGood B c w) (hb : Book B c w) (hn : NEx E w)
    (hp : ∀ r v, CacheGood B c v → Book B c v → Kept w v → NEx E v → post r v) :
    WriterWP f c w post :=
  writerWP_mono (writerWP_and (hne E c w hv hw hn) (hbk c w hv.ids hb))
    (fun r v h => hp r v h.1.1 h.2.1 h.2.2 h.1.2)

theorem nex_run_getNode (B : NodeId) (E : List NodeId) (x : NodeId) (c : Ctx) (w : W)
    (post : KNode → W → Prop) (hv : ViewGood B c) (hw : CacheGood B c w) (hb : Book B c w)
    (hn : NEx E w)
    (hp : ∀ n v, CacheGood B c v → Book B c v → Kept w v → NEx E v → Good B c x n →
      v.nodes.lookup x = some n → (n.ks = [] → x ∈ E) → post n v) :
    WriterWP (getNode x) c w post :=
  writerWP_mono (writerWP_and (nex_getNode B E x c w hv hw hn) (book_getNode B x c w hv.ids hb))
    (fun n v h => hp n v h.1.1 h.2.1 h.2.2.1 h.1.2.1 h.1.2.2.1 h.2.2.2 h.1.2.2.2.1)

theorem nex_run_newKey (B : NodeId) (E : List NodeId) (g : Nat) (c : Ctx) (w : W)
    (post : NodeId → W → Prop) (hv : ViewGood B c) (hw : CacheGood B c w) (hb : Book B c w)
    (hn : NEx E w)
    (hp : ∀ x v, CacheGood B c v → Book B c v → Kept w v → NEx (x :: E) v →
      v.nodes.lookup x = some ⟨true, []⟩ → post x v) :
    WriterWP (newKey g 0 true []) c w post :=
  writerWP_mono (writerWP_and
    (nex_newKey_empty B E g 0 true c w (fun x v => CacheGood B c v ∧ NEx (x :: E) v) hv hw hn
      (fun _ _ h1 _ h2 => ⟨h1, h2⟩))
    (book_newKey B g 0 true [] c w hb rfl))
    (fun x v h => hp x v h.1.1 h.2.1 h.2.2.1 h.1.2 h.2.2.2)

theorem nex_run_fill (B : NodeId) (E : List NodeId) (x : NodeId) (n0 n : KNode) (c : Ctx)
    (vr w : W) (post : Unit → W → Prop) (hw : CacheGood B c w) (hb : Book B c w)
    (hn : NEx E w) (hg : Good B c x n) (hne : n.ks ≠ []) (hleaf : n.leaf = n0.leaf)
    (hl : vr.nodes.lookup x = some n0) (hk : Kept vr w)
    (hp : ∀ r v, CacheGood B c v → Book B c v → Kept w v →
      NEx (E.filter (fun y => y != x)) v → post r v) :
    WriterWP (putNode x n) c w post :=
  writerWP_mono (writerWP_and
    (nex_putNode_fill B E x n c w (fun _ v => CacheGood B c v ∧
      NEx (E.filter (fun y => y != x)) v) hw hn hg hne (fun _ _ h1 h2 => ⟨h1, h2⟩))
    (book_putNode_of B x n c vr w n0 hb hleaf hl hk))
    (fun r v h => hp r v h.1.1 h.2.1 h.2.2 h.1.2)

/-- Kept nodes keep their lookup's leaf flag. -/
theorem nex_run_kept_leaf {a b : W} (h : Kept a b) {x : NodeId} {n n' : KNode}
    (ha : a.nodes.lookup x = some n) (hb : b.nodes.lookup x = some n') : n'.leaf = n.leaf := by
  obtain ⟨m, hm, hml⟩ := h.lookup ha
  rw [hb] at hm
  cases hm
  exact hml

/-! ## The descent from the hand-over node -/

theorem nex_run_descend_nil (B : NodeId) (cv fuel : Nat) (r : NodeId) (c : Ctx) (w : W)
    (hv : ViewGood B c) (hw : CacheGood B c w) (hb : Book B c w) (hn : NEx [] w) :
    WriterWP (descendLte cv fuel r) c w (fun cur v => CacheGood B c v ∧ Book B c v ∧
      Kept w v ∧ nexRunPend v cur ∧ (NEx [] w → NEx [] v)) :=
  nex_run_step (nex_descendLte B cv fuel r) (book_descendLte B cv fuel r) [] c w _ hv hw hb hn
    (fun cur v hc hb' hk hn' => ⟨hc, hb', hk, nex_run_pend_of_nil v cur hn', fun _ => hn'⟩)

/-- The descent from the hand-over node: a pending node is a segment leaf, and
the descent stops there at once with the state unchanged. -/
theorem nex_run_descend (B : NodeId) (cv : Nat) (r : NodeId) (c : Ctx) (w : W)
    (hv : ViewGood B c) (hw : CacheGood B c w) (hb : Book B c w) (hp : nexRunPend w r) :
    WriterWP (descendLte cv c.p.fuel r) c w (fun cur v => CacheGood B c v ∧ Book B c v ∧
      Kept w v ∧ nexRunPend v cur ∧ (NEx [] w → NEx [] v)) := by
  cases hl : w.nodes.lookup r with
  | some n =>
    by_cases hk : n.ks = []
    · have hleaf := hp.2 n hl hk
      have hf : c.p.fuel = (c.p.fuel - 1) + 1 := by unfold Params.fuel; omega
      rw [hf]
      unfold descendLte getNode
      simp only [writerWP_bind, writerWP_read, writerWP_get, hl, writerWP_pure, hleaf,
        ↓reduceIte]
      exact ⟨hw, hb, Kept.refl w, hp, fun h => h⟩
    · exact nex_run_descend_nil B cv _ r c w hv hw hb (nex_run_drop B c [] w r n hb hl hk hp.1)
  | none =>
    refine nex_run_descend_nil B cv _ r c w hv hw hb ?_
    intro q hq hk
    have he := List.mem_singleton.mp (hp.1 q hq hk)
    obtain ⟨x, m⟩ := q
    simp only at he
    subst he
    exact absurd (bk_mem_ids_of_mem _ _ _ hq) (bk_not_mem_ids_of_lookup _ _ hl)

/-! ## The last segment: `setValue` -/

/-- A put's last segment from the hand-over node fills it: its store adds the
value's klong to the leaf the descent stops at; an empty leaf has room for it. -/
theorem nex_run_setValue (B : NodeId) (r : NodeId) (cv : Nat) (key : Key) (h : Nat) (c : Ctx)
    (w : W) (hv : ViewGood B c) (hM : 2 ≤ c.p.M) (hw : CacheGood B c w) (hb : Book B c w)
    (hp : nexRunPend w r) :
    WriterWP (setValue r cv key (some h)) c w
      (fun _ v => CacheGood B c v ∧ Book B c v ∧ NEx [] v) := by
  unfold setValue
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (nex_run_descend B cv r c w hv hw hb hp) ?_
  rintro cur w1 ⟨hc1, hb1, -, hp1, -⟩
  refine nex_run_step (nex_newValue B h) (book_newValue B h) [cur] c w1 _ hv hc1 hb1 hp1.1 ?_
  intro val w2 hc2 hb2 _ hn2
  refine nex_run_getNode B [cur] cur c w2 _ hv hc2 hb2 hn2 ?_
  intro n w3 hc3 hb3 _ hn3 hg3 hl3 _
  refine writerWP_if _ _ _ _ _ _ ?_ ?_
  · intro _
    simp only [writerWP_bind, writerWP_pure]
    refine nex_run_fill B [cur] cur n _ c w3 w3 _ hc3 hb3 hn3
      (Good.add_key B c cur n cv val hv.pos hg3) (nex_add_ne _ _ _) (KNode.add_leaf _ _ _) hl3
      (Kept.refl _) ?_
    intro _ v hc hb hk hn
    refine ⟨hc, hb, NEx.mono ?_ hn⟩
    intro y hy
    simp at hy
  · intro hcond
    have hne : n.ks ≠ [] := by
      intro hk
      apply hcond
      simp [nex_run_size_nil n hk, nex_run_deadOver_nil _ n _ _ _ hk]
      omega
    have hn0 := nex_run_drop B c [] w3 cur n hb3 hl3 hne hn3
    simp only [writerWP_bind, writerWP_pure]
    refine nex_run_step (nex_pathSize B) (book_pathSize B) [] c w3 _ hv hc3 hb3 hn0 ?_
    intro s w4 hc4 hb4 _ hn4
    refine nex_run_step (nex_appendKlongs B _ _ _) (book_appendKlongs B _ _ _) [] c w4 _ hv
      hc4 hb4 hn4 ?_
    intro _ v hc hb _ hn
    exact ⟨hc, hb, hn⟩

/-! ## A segment above the last: `setNode` -/

/-- `setNode` from the hand-over node: what it returns is the next hand-over
node; a new segment leaf is the one node without a klong, and a leaf. Without
`create` no node is pending before or after. -/
theorem nex_run_setNode (B : NodeId) (r : NodeId) (cv : Nat) (create : Bool) (c : Ctx) (w : W)
    (hv : ViewGood B c) (hM : 2 ≤ c.p.M) (hw : CacheGood B c w) (hb : Book B c w)
    (hp : nexRunPend w r) (hcr : create = false → NEx [] w) :
    WriterWP (setNode r cv create) c w (fun res v => CacheGood B c v ∧ Book B c v ∧
      (res = none → NEx [] v) ∧ (∀ next, res = some next → nexRunPend v next) ∧
      (create = false → NEx [] v)) := by
  unfold setNode
  simp only [writerWP_bind, writerWP_read]
  refine writerWP_mono (nex_run_descend B cv r c w hv hw hb hp) ?_
  rintro cur w1 ⟨hc1, hb1, -, hp1, hz1⟩
  cases create with
  | false =>
    have hn1 := hz1 (hcr rfl)
    refine nex_run_getNode B [] cur c w1 _ hv hc1 hb1 hn1 ?_
    intro n w2 hc2 hb2 _ hn2 _ _ _
    split
    · rw [writerWP_bind]
      refine nex_run_step (nex_pathAdd B _ _) (book_pathAdd B _ _) [] c w2 _ hv hc2 hb2 hn2 ?_
      intro _ v hc hb' _ hn
      rw [writerWP_pure]
      exact ⟨hc, hb', fun _ => hn, fun next _ => nex_run_pend_of_nil v next hn, fun _ => hn⟩
    · refine writerWP_if _ _ _ _ _ _ (fun _ => (writerWP_pure _ _ _ _).mpr ?_)
        (fun h => absurd rfl h)
      exact ⟨hc2, hb2, fun _ => hn2, (fun _ h => by cases h), fun _ => hn2⟩
  | true =>
    refine nex_run_getNode B [cur] cur c w1 _ hv hc1 hb1 hp1.1 ?_
    intro n w2 hc2 hb2 hk2 hn2 hg2 hl2 _
    split
    · rename_i fd hfd
      have hne : n.ks ≠ [] := fun hk => by rw [nex_run_searchEq_nil n _ _ hk] at hfd; cases hfd
      have hn0 := nex_run_drop B c [] w2 cur n hb2 hl2 hne hn2
      rw [writerWP_bind]
      refine nex_run_step (nex_pathAdd B _ _) (book_pathAdd B _ _) [] c w2 _ hv hc2 hb2 hn0 ?_
      intro _ v hc hb' _ hn
      rw [writerWP_pure]
      exact ⟨hc, hb', fun _ => hn, fun next _ => nex_run_pend_of_nil v next hn, (fun h => by cases h)⟩
    · refine writerWP_if _ _ _ _ _ _ (fun h => absurd h (by decide)) ?_
      intro _
      by_cases hk : n.ks = []
      · rw [writerWP_bind]
        refine nex_run_step (nex_ghOf B cur) (book_ghOf B cur) [cur] c w2 _ hv hc2 hb2 hn2 ?_
        intro gh w3 hc3 hb3 hk3 hn3
        rw [writerWP_bind]
        refine nex_run_step (nex_note B _) (book_note B _) [cur] c w3 _ hv hc3 hb3 hn3 ?_
        intro _ w4 hc4 hb4 hk4 hn4
        rw [writerWP_bind]
        refine nex_run_newKey B [cur] _ c w4 _ hv hc4 hb4 hn4 ?_
        intro child w5 hc5 hb5 hk5 hn5 hl5
        refine writerWP_if _ _ _ _ _ _ ?_ ?_
        · intro _
          rw [writerWP_bind]
          refine nex_run_fill B [child, cur] cur n _ c w2 w5 _ hc5 hb5 hn5
            (Good.add_key B c cur n cv child hv.pos hg2) (nex_add_ne _ _ _)
            (KNode.add_leaf _ _ _) hl2 (hk3.trans (hk4.trans hk5)) ?_
          intro _ v hc hb' hk' hn
          rw [writerWP_pure]
          refine ⟨hc, hb', (fun h => by cases h), ?_, (fun h => by cases h)⟩
          intro next hnext
          cases hnext
          refine ⟨NEx.mono ?_ hn, ?_⟩
          · intro y hy
            obtain ⟨hm, hy'⟩ := List.mem_filter.mp hy
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
            rcases hm with rfl | rfl
            · exact List.mem_singleton.mpr rfl
            · simp at hy'
          · intro m hm _
            rw [nex_run_kept_leaf hk' hl5 hm]
        · intro hcond
          exact absurd (by rw [nex_run_size_nil n hk]; omega) hcond
      · have hn0 := nex_run_drop B c [] w2 cur n hb2 hl2 hk hn2
        rw [writerWP_bind]
        refine nex_run_step (nex_ghOf B cur) (book_ghOf B cur) [] c w2 _ hv hc2 hb2 hn0 ?_
        intro gh w3 hc3 hb3 hk3 hn3
        rw [writerWP_bind]
        refine nex_run_step (nex_note B _) (book_note B _) [] c w3 _ hv hc3 hb3 hn3 ?_
        intro _ w4 hc4 hb4 hk4 hn4
        rw [writerWP_bind]
        refine nex_run_newKey B [] _ c w4 _ hv hc4 hb4 hn4 ?_
        intro child w5 hc5 hb5 hk5 hn5 hl5
        refine writerWP_if _ _ _ _ _ _ ?_ ?_
        · intro _
          rw [writerWP_bind]
          refine nex_run_fill B [child] cur n _ c w2 w5 _ hc5 hb5 hn5
            (Good.add_key B c cur n cv child hv.pos hg2) (nex_add_ne _ _ _)
            (KNode.add_leaf _ _ _) hl2 (hk3.trans (hk4.trans hk5)) ?_
          intro _ v hc hb' hk' hn
          rw [writerWP_pure]
          refine ⟨hc, hb', (fun h => by cases h), ?_, (fun h => by cases h)⟩
          intro next hnext
          cases hnext
          refine ⟨NEx.mono (fun y hy => (List.mem_filter.mp hy).1) hn, ?_⟩
          intro m hm _
          rw [nex_run_kept_leaf hk' hl5 hm]
        · intro _
          rw [writerWP_bind]
          refine nex_run_step (nex_pathSize B) (book_pathSize B) [child] c w5 _ hv hc5 hb5 hn5 ?_
          intro s w6 hc6 hb6 hk6 hn6
          rw [writerWP_bind]
          refine nex_run_step (nex_appendKlongs B _ _ _) (book_appendKlongs B _ _ _) [child] c w6
            _ hv hc6 hb6 hn6 ?_
          intro _ v hc hb' hk' hn
          rw [writerWP_pure]
          refine ⟨hc, hb', (fun h => by cases h), ?_, (fun h => by cases h)⟩
          intro next hnext
          cases hnext
          refine ⟨hn, ?_⟩
          intro m hm _
          rw [nex_run_kept_leaf (hk6.trans hk') hl5 hm]

/-! ## The put's loop, an operation, a transaction -/

/-- The loop over the key's segments from the hand-over node: a pending node is
filled by the next step; a delete has no pending node. -/
theorem nex_run_putSegs (B : NodeId) (key : Key) (value : Option Nat) (segs : List Nat) :
    ∀ (r : NodeId) (c : Ctx) (w : W), ViewGood B c → 2 ≤ c.p.M → CacheGood B c w →
      Book B c w → nexRunPend w r → (value.isSome = true ∨ NEx [] w) →
      WriterWP (putSegs key value segs r) c w
        (fun _ v => CacheGood B c v ∧ Book B c v ∧ NEx [] v) := by
  induction segs with
  | nil =>
    intro r c w _ _ _ _ _ _
    unfold putSegs
    exact writerWP_throw _ _ _ _
  | cons cv rest ih =>
    intro r c w hv hM hw hb hp hval
    cases rest with
    | nil =>
      unfold putSegs
      cases value with
      | some h => exact nex_run_setValue B r cv key h c w hv hM hw hb hp
      | none =>
        have hn : NEx [] w := hval.resolve_left (by simp)
        exact nex_run_step (nex_setValue B r cv key none) (book_setValue B r cv key none) [] c w
          _ hv hw hb hn (fun _ v hc hb' _ hn' => ⟨hc, hb', hn'⟩)
    | cons cv2 rest =>
      unfold putSegs
      rw [writerWP_bind]
      refine writerWP_mono (nex_run_setNode B r cv value.isSome c w hv hM hw hb hp ?_) ?_
      · intro hf
        exact hval.resolve_left (by rw [hf]; simp)
      rintro res v ⟨hc, hb', hnone, hsome, hfalse⟩
      cases res with
      | none =>
        rw [writerWP_pure]
        exact ⟨hc, hb', hnone rfl⟩
      | some next =>
        refine ih next c v hv hM hc hb' (hsome next rfl) ?_
        cases hs : value.isSome
        · exact Or.inr (hfalse hs)
        · exact Or.inl rfl

theorem nex_run_putKv (B : NodeId) (op : Op) (c : Ctx) (w : W) (hv : ViewGood B c)
    (hM : 2 ≤ c.p.M) (hw : CacheGood B c w) (hb : Book B c w) (hn : NEx [] w) :
    WriterWP (putKv op) c w (fun _ v => CacheGood B c v ∧ Book B c v ∧ NEx [] v) := by
  unfold putKv
  rw [writerWP_bind]
  refine nex_run_step (nex_pathClear B) (book_pathClear B) [] c w _ hv hw hb hn ?_
  intro _ w1 hc1 hb1 _ hn1
  rw [writerWP_bind]
  refine nex_run_step (nex_findRoot B) (book_findRoot B) [] c w1 _ hv hc1 hb1 hn1 ?_
  intro root w2 hc2 hb2 _ hn2
  cases op with
  | put key h =>
    exact nex_run_putSegs B key (some h) key root c w2 hv hM hc2 hb2
      (nex_run_pend_of_nil _ _ hn2) (Or.inl rfl)
  | del key =>
    exact nex_run_putSegs B key none key root c w2 hv hM hc2 hb2
      (nex_run_pend_of_nil _ _ hn2) (Or.inr hn2)

theorem nex_run_ops (B : NodeId) (ops : List Op) (c : Ctx) (w : W) (hv : ViewGood B c)
    (hM : 2 ≤ c.p.M) (hw : CacheGood B c w) (hb : Book B c w) (hn : NEx [] w) :
    WriterWP (ops.mapM putKv) c w (fun _ v => CacheGood B c v ∧ Book B c v ∧ NEx [] v) := by
  induction ops generalizing w with
  | nil => simpa only [List.mapM_nil, writerWP_pure] using ⟨hw, hb, hn⟩
  | cons op ops ih =>
    rw [List.mapM_cons, writerWP_bind]
    refine writerWP_mono (nex_run_putKv B op c w hv hM hw hb hn) ?_
    rintro noop v ⟨hc, hb', hn'⟩
    have hi := ih v hc hb' hn'
    simpa only [writerWP_bind, writerWP_pure] using hi

/-- Every key node of the writer's overlay has a klong at the end of a
successful transaction (with M at least 2): a node read from P@(i-1) has its
klongs, every node the transaction makes is filled before the step that made
it returns, and a new segment leaf by the next step of the put. -/
theorem execW_nonempty (p : Params) (tx : Tx) (i : Time) (v : View BVal) (bs : List Bool) (w : W)
    (hM : 2 ≤ p.M) (hv : ViewGood tx.base { p := p, i := i, view := rootless v })
    (he : execW p tx i v = .ok (bs, w)) : ∀ q ∈ w.nodes, q.2.ks ≠ [] := by
  unfold execW runOps runOpsFrom at he
  cases hz : lastTop v with
  | none => simp [hz] at he
  | some z =>
    simp only [hz] at he
    cases ht : topOf p (rootless v) z with
    | error e => simp [ht] at he
    | ok top =>
      simp only [ht] at he
      have hr := boundsOK_ok p _ bs w he
      have hn := (nex_run_ops tx.base tx.ops { p := p, i := i, view := rootless v }
        { next := tx.base, top := top } hv hM ⟨Nat.le_refl _, by intro q hq; cases hq⟩
        (book_start _ _ top) (by intro q hq; cases hq) bs w hr).2.2
      intro q hq hk
      exact absurd (hn q hq hk) (fun hm => by cases hm)

end SIS.Tree
