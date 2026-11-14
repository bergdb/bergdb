/-
The heights walked through the writer (bergdb 024-22, step 4; TP7's (b)),
continued: the nodes a store makes meet `NodeHt`, the tactics of the walk, a
full node's replacement (`handleFullWith`), `addKeys` and `appendKlongs`.
-/
import SIS.Tree.WriterHeightsSteps
import SIS.Tree.WriterKindsSplit

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

variable {H : NodeId → Nat → Prop}

/-! ## A klong of the right height -/

/-- Klong (cv, y) of a node of height h names a node not taken back, and for an
inner node a key node one height below. -/
def HtP (_c : Ctx) (H : NodeId → Nat → Prop) (w : W) (h : Nat) : Nat → NodeId → Prop :=
  fun _ y => w.taken.contains y = false ∧ (h ≠ 0 → HasHt H w y (h - 1))

/-- A state and a later one: the books' relation, and the same nodes taken back. -/
def HtLe (w v : W) : Prop := Kept w v ∧ v.taken = w.taken

theorem HtLe.refl (w : W) : HtLe w w := ⟨Kept.refl w, rfl⟩

theorem HtLe.trans {a b d : W} (h1 : HtLe a b) (h2 : HtLe b d) : HtLe a d :=
  ⟨h1.1.trans h2.1, h2.2.trans h1.2⟩

theorem HtLe.gh' {w v : W} {e : NodeId × Nat × Nat} (h : e ∈ w.gh) (hk : HtLe w v) : e ∈ v.gh :=
  hk.1.2 e h

theorem HtP.mono {c : Ctx} {w v : W} {h cv : Nat} {y : NodeId} (hp : HtP c H w h cv y)
    (hk : HtLe w v) : HtP c H v h cv y :=
  ⟨by rw [hk.2]; exact hp.1, fun h0 => (hp.2 h0).mono (fun q hq => hk.1.2 q hq)⟩

theorem htKs_mono {c : Ctx} {w v : W} {h : Nat} {ks : List Klong} (hk : kdKs (HtP c H w h) ks)
    (hle : HtLe w v) : kdKs (HtP c H v h) ks := fun cv y hm => (hk cv y hm).mono hle

theorem htPairs_mono {c : Ctx} {w v : W} {h : Nat} {l : List (Nat × NodeId)}
    (hk : kdPairs (HtP c H w h) l) (hle : HtLe w v) : kdPairs (HtP c H v h) l :=
  fun q hq => (hk q hq).mono hle

theorem NodeHt.htMono {c : Ctx} {w v : W} {h : Nat} {n : KNode} (hn : NodeHt c H w h n)
    (hle : HtLe w v) : NodeHt c H v h n :=
  hn.mono (fun q hq => hle.1.2 q hq) (fun y hy => by rw [hle.2]; exact hy)

theorem ht_free (c : Ctx) (w : W) (h : Nat) : kdFree (HtP c H w h) := fun _ _ _ hp => hp

/-! ## Nodes of the right heights -/

theorem ht_live_nil {leaf : Bool} {cv : Nat} {y : NodeId} :
    (cv, y) ∉ (⟨leaf, []⟩ : KNode).live := by
  intro h
  have := ht_live_mem h
  cases this

theorem nodeHt_nil (c : Ctx) (w : W) (h : Nat) (leaf : Bool) : NodeHt c H w h ⟨leaf, []⟩ := by
  refine ⟨fun cv y hy => absurd hy ht_live_nil, fun cv y hy => ?_, fun t ht => by cases ht⟩
  simp only [KNode.toPrev, prefixAt, List.takeWhile_nil] at hy
  exact absurd hy ht_live_nil

/-- A node of the transaction's time whose klongs are of the right height. -/
theorem nodeHt_of_ks {c : Ctx} {w : W} {h : Nat} {leaf : Bool} {ks : List Klong}
    (hpos : 0 < c.i) (hks : ∃ r, ks = .time c.i :: r) (hk : kdKs (HtP c H w h) ks)
    (htm : ∀ t, Klong.time t ∈ ks → t ≤ c.i) :
    NodeHt c H w h ⟨leaf, ks⟩ := by
  refine ⟨fun cv y hy => hk cv y (ht_live_mem hy), fun cv y hy => ?_, htm⟩
  obtain ⟨r, rfl⟩ := hks
  simp only [KNode.toPrev] at hy
  rw [ht_prefixAt_time_cons (c.i - 1) c.i (by omega) r] at hy
  exact absurd hy ht_live_nil

theorem ht_halves_time (leaf : Bool) (t : Time) (last : KNode) (ins : List (Nat × NodeId)) :
    (∃ r, (halves leaf t last ins).1.ks = .time t :: r) ∧
    (∃ r, (halves leaf t last ins).2.1.ks = .time t :: r) := by
  unfold halves
  dsimp only
  repeat' split
  all_goals first
    | exact ⟨⟨_, rfl⟩, ⟨_, List.cons_append⟩⟩
    | exact ⟨⟨_, List.cons_append⟩, ⟨_, rfl⟩⟩

theorem ht_flat_times {i : Time} {ks : List Klong} (hf : FlatAt i ks) :
    ∀ t, Klong.time t ∈ ks → t ≤ i := by
  obtain ⟨r, rfl, hr⟩ := hf
  intro t ht
  rcases List.mem_cons.mp ht with ht | ht
  · cases ht; exact Nat.le_refl _
  · obtain ⟨cv, y, he⟩ := hr _ ht
    cases he

theorem nodeHt_halves {c : Ctx} {w : W} {h : Nat} (hpos : 0 < c.i) (leaf : Bool) (last : KNode)
    (ins : List (Nat × NodeId)) (hl : kdKs (HtP c H w h) last.ks) (hi : kdPairs (HtP c H w h) ins)
    (hfl : FlatAt c.i last.ks) :
    NodeHt c H w h (halves leaf c.i last ins).1 ∧ NodeHt c H w h (halves leaf c.i last ins).2.1 := by
  have hk := kdKs_halves leaf c.i (fun _ => ht_free c w h) hl hi
  have ht := ht_halves_time leaf c.i last ins
  have hf := halves_flatAt leaf c.i last ins (FlatAt.flat c.i last.ks hfl)
  have e1 : (halves leaf c.i last ins).1 =
      ⟨(halves leaf c.i last ins).1.leaf, (halves leaf c.i last ins).1.ks⟩ := rfl
  have e2 : (halves leaf c.i last ins).2.1 =
      ⟨(halves leaf c.i last ins).2.1.leaf, (halves leaf c.i last ins).2.1.ks⟩ := rfl
  rw [e1, e2]
  exact ⟨nodeHt_of_ks hpos ht.1 hk.1 (ht_flat_times hf.1),
    nodeHt_of_ks hpos ht.2 hk.2 (ht_flat_times hf.2)⟩

/-- A new root above x and y, nodes of height h not taken back. -/
theorem nodeHt_root {c : Ctx} {w : W} {x y : NodeId} {h : Nat} (hpos : 0 < c.i) (sc : Nat)
    (hx : HtP c H w (h + 1) 0 x) (hy : HtP c H w (h + 1) sc y) :
    NodeHt c H w (h + 1) ⟨false, [.time c.i, .key 0 x, .key sc y]⟩ :=
  nodeHt_of_ks hpos ⟨_, rfl⟩ (kdKs_cons_time _ (kdKs_cons_key hx (kdKs_cons_key hy (kdKs_nil _))))
    (fun t ht => by simp at ht; omega)

/-- The version before the transaction keeps its heights. -/
theorem nodeHt_toPrev {c : Ctx} {w : W} {h : Nat} {n : KNode} (hn : NodeHt c H w h n) :
    NodeHt c H w h (n.toPrev (c.i - 1)) := by
  refine ⟨hn.2, ?_, fun t ht => hn.3 t ((prefixAt_prefix _ _).subset ht)⟩
  rw [ht_toPrev_toPrev]
  exact hn.2

theorem ht_prefixAt_addFold (t : Time) (i : Time) (hi : t < i) :
    ∀ (ins : List (Nat × NodeId)) (n : KNode),
      prefixAt (ins.foldl (fun n (q : Nat × NodeId) => n.add i (.key q.1 q.2)) n).ks t =
        prefixAt n.ks t
  | [], n => rfl
  | q :: ins, n => by
    rw [List.foldl_cons, ht_prefixAt_addFold t i hi ins _, KNode.add_prefixAt_past n i t hi]

theorem ht_add_times {n : KNode} {i : Time} {k : Klong} (hn : ∀ t, Klong.time t ∈ n.ks → t ≤ i)
    (hk : ∀ t, k ≠ .time t) : ∀ t, Klong.time t ∈ (n.add i k).ks → t ≤ i := by
  intro t ht
  unfold KNode.add at ht
  split at ht
  · split at ht
    · simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at ht
      rcases ht with ht | ht | ht
      · exact hn t ht
      · cases ht; exact Nat.le_refl _
      · exact absurd ht.symm (hk t)
    · simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at ht
      rcases ht with ht | ht
      · exact hn t ht
      · exact absurd ht.symm (hk t)
  · simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at ht
    rcases ht with ht | ht | ht
    · exact hn t ht
    · cases ht; exact Nat.le_refl _
    · exact absurd ht.symm (hk t)

theorem ht_addFold_times (i : Time) :
    ∀ (ins : List (Nat × NodeId)) (n : KNode), (∀ t, Klong.time t ∈ n.ks → t ≤ i) →
      ∀ t, Klong.time t ∈ (ins.foldl (fun n (q : Nat × NodeId) => n.add i (.key q.1 q.2)) n).ks →
        t ≤ i
  | [], n, hn => hn
  | q :: ins, n, hn => by
    rw [List.foldl_cons]
    exact ht_addFold_times i ins _ (ht_add_times hn (fun t h => by cases h))

/-- Key klongs added at the transaction's time, of the right height. -/
theorem nodeHt_addFold {c : Ctx} {w : W} {h : Nat} {n : KNode} (hpos : 0 < c.i)
    (hn : NodeHt c H w h n) (ins : List (Nat × NodeId)) (hi : kdPairs (HtP c H w h) ins) :
    NodeHt c H w h (ins.foldl (fun n (q : Nat × NodeId) => n.add c.i (.key q.1 q.2)) n) := by
  refine ⟨fun cv y hy => ?_, fun cv y hy => ?_, ?_⟩
  · rcases ht_live_addFold c.i ins n cv y hy with h1 | h1
    · exact hn.1 cv y h1
    · exact hi _ h1
  · have he : ((ins.foldl (fun n (q : Nat × NodeId) => n.add c.i (.key q.1 q.2)) n).toPrev (c.i - 1)) =
        n.toPrev (c.i - 1) := by
      unfold KNode.toPrev
      rw [ht_prefixAt_addFold (c.i - 1) c.i (by omega) ins n]
      congr 1
      clear hy hi hn
      induction ins generalizing n with
      | nil => rfl
      | cons q ins ih =>
        rw [List.foldl_cons, ih]
        unfold KNode.add
        split
        · split <;> rfl
        · rfl
    rw [he] at hy
    exact hn.2 cv y hy
  · exact ht_addFold_times c.i ins n hn.3

theorem ht_swapL_prefixAt {S : NodeId → Prop} (t : Time) :
    ∀ {ks ks' : List Klong}, PtrSwapL S ks ks' → PtrSwapL S (prefixAt ks t) (prefixAt ks' t)
  | [], [], _ => trivial
  | [], _ :: _, hf => by simp [PtrSwapL] at hf
  | _ :: _, [], hf => by simp [PtrSwapL] at hf
  | a :: as, b :: bs, hf => by
    obtain ⟨hab, hrest⟩ := hf
    unfold prefixAt
    simp only [List.takeWhile_cons]
    rcases hab with hab | ⟨a', y, y', rfl, rfl, hs⟩
    · subst hab
      cases b with
      | time x =>
        by_cases hx : x ≤ t
        · simp only [hx, decide_true, ↓reduceIte]
          exact ⟨Or.inl rfl, ht_swapL_prefixAt t hrest⟩
        · simp only [hx, decide_false, Bool.false_eq_true, ↓reduceIte]
          trivial
      | key a y =>
        simp only [↓reduceIte]
        exact ⟨Or.inl rfl, ht_swapL_prefixAt t hrest⟩
      | del d =>
        simp only [↓reduceIte]
        exact ⟨Or.inl rfl, ht_swapL_prefixAt t hrest⟩
    · simp only [↓reduceIte]
      exact ⟨Or.inr ⟨a', y, y', rfl, rfl, hs⟩, ht_swapL_prefixAt t hrest⟩

/-- A klong pointed to y, a node of the right height. -/
theorem nodeHt_repoint {c : Ctx} {w : W} {h : Nat} {n : KNode} (hn : NodeHt c H w h n) (j : Nat)
    (y : NodeId) (hy : ∀ cv, HtP c H w h cv y) : NodeHt c H w h (n.repoint j y) := by
  unfold KNode.repoint
  split
  · rename_i a y0 hj
    have hf : PtrSwapL (fun z => z = y) n.ks (n.setAt j (.key a y)).ks :=
      ht_swapL_set n.ks j a y0 y hj rfl
    refine ⟨fun cv z hz => ?_, fun cv z hz => ?_, fun t ht => ?_⟩
    · rcases ht_live_swap hf hz with h1 | rfl
      · exact hn.1 cv z h1
      · exact hy cv
    · have hf' : PtrSwapL (fun z => z = y) (n.toPrev (c.i - 1)).ks
          ((n.setAt j (.key a y)).toPrev (c.i - 1)).ks := ht_swapL_prefixAt _ hf
      rcases ht_live_swap hf' hz with h1 | rfl
      · exact hn.2 cv z h1
      · exact hy cv
    · rcases List.mem_or_eq_of_mem_set ht with ht | ht
      · exact hn.3 t ht
      · cases ht
  · exact hn

/-- A time split's node: klongs of the right height at the transaction's time. -/
theorem nodeHt_flat {c : Ctx} {w : W} {h : Nat} {leaf : Bool} {ks : List Klong} (hpos : 0 < c.i)
    (hf : FlatAt c.i ks) (hk : kdKs (HtP c H w h) ks) : NodeHt c H w h ⟨leaf, ks⟩ := by
  have htm := ht_flat_times hf
  obtain ⟨r, hr, _⟩ := hf
  exact nodeHt_of_ks hpos ⟨r, hr⟩ hk htm

/-- The loop of a time split: no state changes; its klongs are those of `last`
and `ins`, at the transaction's time. -/
theorem ht_replaceOrAdd (P : Nat → NodeId → Prop) (last : KNode) (ins : List (Nat × NodeId))
    (c : Ctx) (w : W) (hl : kdKs P last.ks) (hi : kdPairs P ins) (hf : FlatAt c.i last.ks) :
    WriterWP (replaceOrAdd last ins) c w (fun l v => v = w ∧ kdKs P l.ks ∧ FlatAt c.i l.ks) := by
  refine writerWP_mono (writerWP_and (kd_replaceOrAdd P last ins c w hl hi)
    (writerWP_replaceOrAdd_flat last ins c w hf)) ?_
  rintro l v ⟨⟨he, hk⟩, hfl, _⟩
  exact ⟨he, hk, hfl⟩

/-- The heights a store of an overlay node needs, from its entry in `gh`. -/
theorem ht_putNode_of (B x : NodeId) (n' : KNode) (c : Ctx) (vr vt w : W)
    (n0 : KNode) (hb : Book B c w) (hi : HtInv H B c w) (hl : vr.nodes.lookup x = some n0)
    (hkr : HtLe vr w) (hleaf : n'.leaf = n0.leaf) (g h : Nat) (hm : (x, g, h) ∈ vt.gh)
    (hkt : HtLe vt w) (hks : NodeHt c H w h n') :
    WriterWP (putNode x n') c w (fun _ v => Book B c v ∧ HtInv H B c v ∧ HtLe w v ∧
      v.path = w.path ∧ v.nodes.lookup x = some n') := by
  obtain ⟨n1, hn1, hl1⟩ := hkr.1.1 x n0 hl
  refine writerWP_mono (ht_putNode B x n' c w hb hi n1 hn1 (hleaf.trans hl1.symm) ?_) ?_
  · intro g' h' hg' _
    obtain ⟨rfl, rfl⟩ := kd_tag_eq hb (HtLe.gh' hm hkt) hg'
    exact hks
  · rintro _ v ⟨hb', hi', hk', hp, ht, hlk⟩
    exact ⟨hb', hi', ⟨hk', ht⟩, hp, hlk⟩

end SIS.Tree
