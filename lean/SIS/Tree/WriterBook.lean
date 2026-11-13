/-
The tree model (bergdb 024-12, TP7): the writer keeps its books (`Book`,
SIS/Tree/OverlayBook.lean). This file: the lists of the overlay, the relation
`Kept` between a state and a later one (every node of the overlay stays, with
its leaf flag; every entry of `gh` stays), and the writer's primitive steps.
-/
import SIS.Tree.OverlayBook
import SIS.Tree.KlongShape

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! ## The lists of the overlay -/

theorem bk_mem_of_lookup {β : Type} (ns : List (NodeId × β)) (x : NodeId) (n : β)
    (h : ns.lookup x = some n) : (x, n) ∈ ns := by
  obtain ⟨pre, post, he, _⟩ := List.lookup_eq_some_iff.mp h
  rw [he]
  simp

theorem bk_mem_ids_of_mem {β : Type} (ns : List (NodeId × β)) (x : NodeId) (n : β)
    (h : (x, n) ∈ ns) : x ∈ ns.map (·.1) :=
  List.mem_map.mpr ⟨(x, n), h, rfl⟩

theorem bk_mem_ids_of_lookup {β : Type} (ns : List (NodeId × β)) (x : NodeId) (n : β)
    (h : ns.lookup x = some n) : x ∈ ns.map (·.1) :=
  List.mem_map.mpr ⟨(x, n), bk_mem_of_lookup ns x n h, rfl⟩

theorem bk_not_mem_ids_of_lookup {β : Type} (ns : List (NodeId × β)) (x : NodeId)
    (h : ns.lookup x = none) : x ∉ ns.map (·.1) := by
  intro hm
  obtain ⟨q, hq, he⟩ := List.mem_map.mp hm
  have := List.lookup_eq_none_iff.mp h q hq
  subst he
  simp at this

theorem bk_lookup_of_mem_ids {β : Type} (ns : List (NodeId × β)) (x : NodeId)
    (h : x ∈ ns.map (·.1)) : ∃ n, ns.lookup x = some n := by
  cases hl : ns.lookup x with
  | some n => exact ⟨n, rfl⟩
  | none => exact absurd h (bk_not_mem_ids_of_lookup ns x hl)

theorem bk_lookup_append_left {β : Type} (ns ms : List (NodeId × β)) (x : NodeId) (n : β)
    (h : ns.lookup x = some n) : (ns ++ ms).lookup x = some n := by
  rw [List.lookup_append, h]
  rfl

theorem bk_lookup_append_new {β : Type} (ns : List (NodeId × β)) (x : NodeId) (n : β)
    (h : ns.lookup x = none) : (ns ++ [(x, n)]).lookup x = some n := by
  rw [List.lookup_append, h]
  simp

theorem bk_lookup_map_replace (ns : List (NodeId × KNode)) (x y : NodeId) (n : KNode) :
    (ns.map (fun q => if q.1 == x then (x, n) else q)).lookup y =
      if y = x then (if ns.any (fun q => q.1 == x) then some n else none) else ns.lookup y := by
  induction ns with
  | nil => by_cases hy : y = x <;> simp [hy]
  | cons q ns ih =>
    obtain ⟨a, m⟩ := q
    by_cases ha : a = x
    · subst ha
      by_cases hy : y = a
      · subst hy; simp
      · have hya : (y == a) = false := by simpa using hy
        simp [List.lookup, hya, hy] at ih ⊢
        exact ih
    · have hax : (a == x) = false := by simpa using ha
      simp only [List.map_cons, hax, Bool.false_eq_true, ↓reduceIte, List.lookup, List.any_cons,
        Bool.false_or]
      by_cases hy : y = a
      · subst hy
        simp [ha]
      · have hya : (y == a) = false := by simpa using hy
        simp only [hya]
        exact ih

theorem bk_any_of_lookup (ns : List (NodeId × KNode)) (x : NodeId) (n : KNode)
    (h : ns.lookup x = some n) : ns.any (fun q => q.1 == x) = true := by
  rw [List.any_eq_true]
  exact ⟨(x, n), bk_mem_of_lookup ns x n h, by simp⟩

theorem bk_lookup_upsert (ns : List (NodeId × KNode)) (x y : NodeId) (n n0 : KNode)
    (h : ns.lookup x = some n0) :
    (upsert ns x n).lookup y = if y = x then some n else ns.lookup y := by
  have ha := bk_any_of_lookup ns x n0 h
  unfold upsert
  simp only [ha, ↓reduceIte]
  rw [bk_lookup_map_replace, ha]
  rfl

theorem bk_ids_upsert (ns : List (NodeId × KNode)) (x : NodeId) (n n0 : KNode)
    (h : ns.lookup x = some n0) : (upsert ns x n).map (·.1) = ns.map (·.1) := by
  have ha := bk_any_of_lookup ns x n0 h
  unfold upsert
  simp only [ha, ↓reduceIte]
  rw [List.map_map]
  apply List.map_congr_left
  intro q _
  simp only [Function.comp_apply]
  split
  · rename_i hq; simp at hq; exact hq.symm
  · rfl

theorem bk_mem_upsert (ns : List (NodeId × KNode)) (x : NodeId) (n n0 : KNode)
    (h : ns.lookup x = some n0) (y : NodeId) (m : KNode) (hm : (y, m) ∈ upsert ns x n) :
    (y = x ∧ m = n) ∨ (y, m) ∈ ns := by
  have ha := bk_any_of_lookup ns x n0 h
  unfold upsert at hm
  simp only [ha, ↓reduceIte] at hm
  obtain ⟨q, hq, he⟩ := List.mem_map.mp hm
  split at he
  · cases he; exact Or.inl ⟨rfl, rfl⟩
  · rw [← he]; exact Or.inr hq

/-! ## A state and a later one -/

/-- Every node of the overlay of w is in the overlay of v, with its leaf flag;
every entry of `gh` of w is in `gh` of v. -/
def Kept (w v : W) : Prop :=
  (∀ x n, w.nodes.lookup x = some n → ∃ n', v.nodes.lookup x = some n' ∧ n'.leaf = n.leaf) ∧
  (∀ e ∈ w.gh, e ∈ v.gh)

theorem Kept.refl (w : W) : Kept w w :=
  ⟨fun _ n h => ⟨n, h, rfl⟩, fun _ h => h⟩

theorem Kept.trans {a b d : W} (h1 : Kept a b) (h2 : Kept b d) : Kept a d := by
  refine ⟨?_, fun e he => h2.2 e (h1.2 e he)⟩
  intro x n hn
  obtain ⟨n1, h1n, h1l⟩ := h1.1 x n hn
  obtain ⟨n2, h2n, h2l⟩ := h2.1 x n1 h1n
  exact ⟨n2, h2n, h2l.trans h1l⟩

/-- A node read at an earlier state is in the overlay now, with its leaf flag. -/
theorem Kept.lookup {a b : W} (h : Kept a b) {x : NodeId} {n : KNode}
    (hn : a.nodes.lookup x = some n) : ∃ n', b.nodes.lookup x = some n' ∧ n'.leaf = n.leaf :=
  h.1 x n hn

/-- A node of the overlay at an earlier state is in the overlay now. -/
theorem Kept.has {a b : W} (h : Kept a b) {x : NodeId} {n : KNode}
    (hn : a.nodes.lookup x = some n) : ∃ n', b.nodes.lookup x = some n' :=
  (h.1 x n hn).imp fun _ h => h.1

/-- The same overlay and books. -/
theorem Kept.same {w v : W} (hn : v.nodes = w.nodes) (hg : v.gh = w.gh) : Kept w v := by
  refine ⟨?_, ?_⟩
  · intro x n h; rw [hn]; exact ⟨n, h, rfl⟩
  · intro e h; rw [hg]; exact h

/-- Overlay nodes appended, entries of `gh` added in front. -/
theorem Kept.grow {w v : W} (ns : List (NodeId × KNode)) (es : List (NodeId × Nat × Nat))
    (hn : v.nodes = w.nodes ++ ns) (hg : v.gh = es ++ w.gh) : Kept w v := by
  refine ⟨?_, ?_⟩
  · intro x n h; rw [hn]; exact ⟨n, bk_lookup_append_left _ _ x n h, rfl⟩
  · intro e h; rw [hg]; exact List.mem_append_right _ h

def KeepsBook (B : NodeId) {α : Type} (f : M α) : Prop :=
  ∀ c w, ViewIdsBelow B c.view → Book B c w → WriterWP f c w (fun _ v => Book B c v ∧ Kept w v)

theorem book_writerWP {α : Type} {B : NodeId} {f : M α} (hf : KeepsBook B f)
    (c : Ctx) (w : W) (post : α → W → Prop) (hv : ViewIdsBelow B c.view)
    (hw : Book B c w) (hp : ∀ r v, Book B c v → Kept w v → post r v) :
    WriterWP f c w post := writerWP_mono (hf c w hv hw) (fun r v h => hp r v h.1 h.2)

theorem book_throw (B : NodeId) {α : Type} (e : String) : KeepsBook B (throw e : M α) := by
  intro c w _ _
  exact writerWP_throw _ _ _ _

/-! ## The primitive steps -/

/-- A read of key node x: a hit changes nothing; a load adds the node at the
end of the overlay and its segment and height in front of `gh`. -/
theorem book_getNode (B x : NodeId) (c : Ctx) (w : W) (hv : ViewIdsBelow B c.view)
    (hb : Book B c w) :
    WriterWP (getNode x) c w (fun n v => Book B c v ∧ Kept w v ∧ v.nodes.lookup x = some n) := by
  unfold getNode
  simp only [writerWP_bind, writerWP_get]
  split
  · rename_i n hn
    simp only [writerWP_pure]
    exact ⟨hb, Kept.refl w, hn⟩
  · rename_i hn
    simp only [writerWP_bind, writerWP_read]
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
        have hxB : x < B := hv x nd hnd
        have hxn : x ∉ w.nodes.map (·.1) := bk_not_mem_ids_of_lookup _ x hn
        have hxg : x ∉ w.gh.map (·.1) := by
          intro h; apply hxn; rw [hb.ids]; exact List.mem_reverse.mpr h
        simp only [writerWP_bind, writerWP_set, writerWP_pure]
        refine ⟨?_, Kept.grow _ [(x, c.p.segOf nd.level, c.p.heightOf nd.level)] rfl rfl,
          bk_lookup_append_new _ x _ hn⟩
        refine ⟨hb.next, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [hb.ids]
        · intro q hq
          simp only [List.mem_cons] at hq
          rcases hq with rfl | hq
          · show x < w.next; have := hb.next; omega
          · exact hb.bound q hq
        · simp only [List.map_cons, List.nodup_cons]
          exact ⟨hxg, hb.nodup⟩
        · intro y m g h hm hg
          simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at hm
          simp only [List.mem_cons, Prod.mk.injEq] at hg
          rcases hm with hm | ⟨rfl, rfl⟩
          · rcases hg with ⟨rfl, rfl, rfl⟩ | hg
            · exact absurd (bk_mem_ids_of_mem _ _ _ hm) hxn
            · exact hb.leaf y m g h hm hg
          · rcases hg with ⟨_, _, rfl⟩ | hg
            · rfl
            · exact absurd (bk_mem_ids_of_mem _ _ _ hg) hxg
        · intro y g h hg
          simp only [List.mem_cons] at hg
          rcases hg with hg | hg
          · cases hg
            exact Or.inl ⟨nd, hnd, hd, hl, rfl, rfl⟩
          · exact hb.tag y g h hg
        · intro y hy
          exact List.mem_cons_of_mem _ (hb.taken y hy)
        · intro ht
          obtain ⟨h1, h2, h3⟩ := hb.top ht
          refine ⟨h1, h2, ?_⟩
          simp only [List.map_cons, List.mem_cons, not_or]
          refine ⟨?_, h3⟩
          intro he
          omega
    · exact writerWP_throw _ _ _ _

/-- A store of key node x, a node of the overlay, with its leaf flag. -/
theorem book_putNode (B x : NodeId) (n : KNode) (c : Ctx) (w : W) (hb : Book B c w)
    (hx : ∃ n0, w.nodes.lookup x = some n0 ∧ n.leaf = n0.leaf) :
    WriterWP (putNode x n) c w (fun _ v => Book B c v ∧ Kept w v) := by
  obtain ⟨n0, hn0, hleaf⟩ := hx
  simp only [putNode, writerWP_modify]
  refine ⟨⟨hb.next, ?_, hb.bound, hb.nodup, ?_, hb.tag, hb.taken, hb.top⟩, ?_, ?_⟩
  · show (upsert w.nodes x n).map (·.1) = _
    rw [bk_ids_upsert _ x n n0 hn0]
    exact hb.ids
  · intro y m g h hm hg
    rcases bk_mem_upsert w.nodes x n n0 hn0 y m hm with ⟨rfl, rfl⟩ | hm
    · rw [hleaf]
      exact hb.leaf y n0 g h (bk_mem_of_lookup _ _ _ hn0) hg
    · exact hb.leaf y m g h hm hg
  · intro y m hm
    show ∃ n', (upsert w.nodes x n).lookup y = some n' ∧ _
    rw [bk_lookup_upsert _ x y n n0 hn0]
    by_cases hy : y = x
    · subst hy
      rw [hn0] at hm
      cases hm
      exact ⟨n, by simp, hleaf⟩
    · simp only [hy, ↓reduceIte]
      exact ⟨m, hm, rfl⟩
  · intro e he; exact he

/-- A new key node, its leaf flag that of its height. -/
theorem book_newKey (B : NodeId) (g h : Nat) (leaf : Bool) (ks : List Klong) (c : Ctx) (w : W)
    (hb : Book B c w) (hleaf : leaf = (h == 0)) :
    WriterWP (newKey g h leaf ks) c w (fun x v =>
      Book B c v ∧ Kept w v ∧ v.nodes.lookup x = some ⟨leaf, ks⟩) := by
  have hxg : w.next ∉ w.gh.map (·.1) := by
    intro hm
    obtain ⟨q, hq, he⟩ := List.mem_map.mp hm
    have := hb.bound q hq
    rw [he] at this
    exact Nat.lt_irrefl _ this
  have hxn : w.next ∉ w.nodes.map (·.1) := by
    rw [hb.ids]; intro h; exact hxg (List.mem_reverse.mp h)
  have hnone : w.nodes.lookup w.next = none := by
    cases hl : w.nodes.lookup w.next with
    | none => rfl
    | some m => exact absurd (bk_mem_ids_of_lookup _ _ _ hl) hxn
  unfold newKey fresh
  simp only [writerWP_bind, writerWP_read, writerWP_get, writerWP_set, writerWP_pure]
  have hfin : ∀ (o : List (NodeId × Nat × Nat)),
      (∀ e ∈ w.outside, e ∈ o) →
      ((c.p.G < g ∨ c.p.H < h) → (w.next, g, h) ∈ o) →
      Book B c
        { w with next := w.next + 2, nodes := w.nodes ++ [(w.next, ⟨leaf, ks⟩)],
                 gh := (w.next, g, h) :: w.gh,
                 made := w.made ++ [⟨w.next, c.p.keyLevel g h, false⟩], outside := o } := by
    intro o hout hnew
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show B ≤ w.next + 2; have := hb.next; omega
    · show (w.nodes ++ _).map _ = _; simp [hb.ids]
    · intro q hq
      simp only [List.mem_cons] at hq
      show q.1 < w.next + 2
      rcases hq with rfl | hq
      · omega
      · have := hb.bound q hq; omega
    · show List.Nodup (((w.next, g, h) :: w.gh).map (·.1))
      simp only [List.map_cons, List.nodup_cons]
      exact ⟨hxg, hb.nodup⟩
    · intro y m g' h' hm hg
      simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at hm
      simp only [List.mem_cons, Prod.mk.injEq] at hg
      rcases hm with hm | ⟨rfl, rfl⟩
      · rcases hg with ⟨rfl, rfl, rfl⟩ | hg
        · exact absurd (bk_mem_ids_of_mem _ _ _ hm) hxn
        · exact hb.leaf y m g' h' hm hg
      · rcases hg with ⟨_, _, rfl⟩ | hg
        · exact hleaf
        · exact absurd (bk_mem_ids_of_mem _ _ _ hg) hxg
    · intro y g' h' hg
      simp only [List.mem_cons] at hg
      rcases hg with hg | hg
      · cases hg
        refine Or.inr ⟨hb.next, by simp, hnew⟩
      · rcases hb.tag y g' h' hg with ht | ⟨h1, h2, h3⟩
        · exact Or.inl ht
        · exact Or.inr ⟨h1, List.mem_append_left _ h2, fun hh => hout _ (h3 hh)⟩
    · intro y hy
      exact List.mem_cons_of_mem _ (hb.taken y hy)
    · intro ht
      obtain ⟨h1, h2, h3⟩ := hb.top ht
      refine ⟨h1, ?_, ?_⟩
      · show w.top.id < w.next + 2; omega
      · simp only [List.map_cons, List.mem_cons, not_or]
        refine ⟨?_, h3⟩
        intro he
        omega
  split
  · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
    refine ⟨hfin _ (fun e he => List.mem_cons_of_mem _ he) (fun _ => List.mem_cons_self),
      Kept.grow _ [(w.next, g, h)] rfl rfl, bk_lookup_append_new _ _ _ hnone⟩
  · rename_i hno
    simp only [writerWP_bind, writerWP_pure, writerWP_modify]
    refine ⟨hfin _ (fun e he => he) ?_, Kept.grow _ [(w.next, g, h)] rfl rfl,
      bk_lookup_append_new _ _ _ hnone⟩
    intro hh
    exfalso; apply hno
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact hh

/-- The books with more made nodes, more noted nodes, a larger next id, and the
same top node id. -/
theorem Book.grow {B : NodeId} {c : Ctx} {w : W} (hb : Book B c w) (v : W)
    (hn : v.nodes = w.nodes) (hg : v.gh = w.gh) (ht : v.taken = w.taken)
    (hm : ∀ e ∈ w.made, e ∈ v.made) (ho : ∀ e ∈ w.outside, e ∈ v.outside)
    (hx : w.next ≤ v.next) (htop : v.top.id = w.top.id) (hnt : v.newTop = w.newTop) :
    Book B c v := by
  refine ⟨Nat.le_trans hb.next hx, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hn, hg]; exact hb.ids
  · intro q hq; rw [hg] at hq; exact Nat.lt_of_lt_of_le (hb.bound q hq) hx
  · rw [hg]; exact hb.nodup
  · intro y m g h hm hq; rw [hn] at hm; rw [hg] at hq; exact hb.leaf y m g h hm hq
  · intro y g h hq
    rw [hg] at hq
    rcases hb.tag y g h hq with h1 | ⟨h1, h2, h3⟩
    · exact Or.inl h1
    · exact Or.inr ⟨h1, hm _ h2, fun hh => ho _ (h3 hh)⟩
  · intro y hy; rw [ht] at hy; rw [hg]; exact hb.taken y hy
  · intro hh
    rw [hnt] at hh
    obtain ⟨h1, h2, h3⟩ := hb.top hh
    rw [htop, hg]
    exact ⟨h1, Nat.lt_of_lt_of_le h2 hx, h3⟩

/-- The books do not change with what they do not hold. -/
theorem Book.congr {B : NodeId} {c : Ctx} {w : W} (hb : Book B c w) (v : W)
    (hn : v.nodes = w.nodes) (hg : v.gh = w.gh) (hm : v.made = w.made)
    (ho : v.outside = w.outside) (ht : v.taken = w.taken) (hx : v.next = w.next)
    (htop : v.top.id = w.top.id) (hnt : v.newTop = w.newTop) : Book B c v :=
  hb.grow v hn hg ht (fun _ he => hm ▸ he) (fun _ he => ho ▸ he) (Nat.le_of_eq hx.symm) htop hnt

theorem book_merges {B : NodeId} {c : Ctx} {w : W} (hb : Book B c w) (m : Nat) :
    Book B c { w with merges := m } := hb.congr _ rfl rfl rfl rfl rfl rfl rfl rfl

theorem book_spaceSplits {B : NodeId} {c : Ctx} {w : W} (hb : Book B c w) (m : Nat) :
    Book B c { w with spaceSplits := m } := hb.congr _ rfl rfl rfl rfl rfl rfl rfl rfl

/-- The books of a state with other fields changed: the record update of a
state that the walks meet. -/
theorem Book.upd {B : NodeId} {c : Ctx} {w : W} (hb : Book B c w) (vals : List (NodeId × Nat))
    (madeFor : List (NodeId × NodeId)) (path : List (Option Nat × NodeId)) (top : Top)
    (trail : List String) (merges spaceSplits : Nat) (htop : top.id = w.top.id) :
    Book B c ⟨w.nodes, w.gh, w.made, vals, w.taken, madeFor, w.next, path, top, w.newTop, trail,
      merges, spaceSplits, w.outside⟩ :=
  hb.congr _ rfl rfl rfl rfl rfl rfl htop rfl

theorem book_note (B : NodeId) (s : String) : KeepsBook B (note s) := by
  intro c w _ hb; simp only [note, writerWP_modify]; exact ⟨hb.congr _ rfl rfl rfl rfl rfl rfl rfl rfl, Kept.same rfl rfl⟩

theorem book_pathClear (B : NodeId) : KeepsBook B pathClear := by
  intro c w _ hb; simp only [pathClear, writerWP_modify]; exact ⟨hb.congr _ rfl rfl rfl rfl rfl rfl rfl rfl, Kept.same rfl rfl⟩

theorem book_pathAdd (B : NodeId) (cv : Option Nat) (x : NodeId) : KeepsBook B (pathAdd cv x) := by
  intro c w _ hb; simp only [pathAdd, writerWP_modify]; exact ⟨hb.congr _ rfl rfl rfl rfl rfl rfl rfl rfl, Kept.same rfl rfl⟩

theorem book_setMadeFor (B : NodeId) (x : NodeId) (old : Option NodeId) :
    KeepsBook B (setMadeFor x old) := by
  intro c w _ hb
  unfold setMadeFor
  split
  · simp only [writerWP_modify]; exact ⟨hb.congr _ rfl rfl rfl rfl rfl rfl rfl rfl, Kept.same rfl rfl⟩
  · simp only [writerWP_pure]; exact ⟨hb, Kept.refl w⟩

theorem book_fresh (B : NodeId) : KeepsBook B fresh := by
  intro c w _ hb
  simp only [fresh, writerWP_bind, writerWP_get, writerWP_set, writerWP_pure]
  exact ⟨hb.grow _ rfl rfl rfl (fun _ h => h) (fun _ h => h) (Nat.le_add_right _ 2) rfl rfl,
    Kept.same rfl rfl⟩

theorem book_newValue (B : NodeId) (h : Nat) : KeepsBook B (newValue h) := by
  intro c w _ hb
  simp only [newValue, fresh, writerWP_bind, writerWP_get, writerWP_set, writerWP_pure,
    writerWP_modify]
  exact ⟨hb.grow _ rfl rfl rfl (fun _ h => List.mem_append_left _ h) (fun _ h => h)
    (Nat.le_add_right _ 2) rfl rfl, Kept.same rfl rfl⟩

theorem book_newSuperRoot (B : NodeId) (y : NodeId) : KeepsBook B (newSuperRoot y) := by
  intro c w _ hb
  unfold newSuperRoot
  simp only [note, fresh, writerWP_bind, writerWP_get, writerWP_read]
  split
  · simp only [writerWP_bind, writerWP_set, writerWP_modify]
    exact ⟨hb.congr _ rfl rfl rfl rfl rfl rfl rfl rfl, Kept.same rfl rfl⟩
  · simp only [writerWP_bind, writerWP_modify, writerWP_get, writerWP_set, writerWP_pure]
    refine ⟨⟨?_, hb.ids, ?_, hb.nodup, hb.leaf, ?_, hb.taken, ?_⟩, Kept.same rfl rfl⟩
    · show B ≤ w.next + 2; have := hb.next; omega
    · intro q hq; show q.1 < w.next + 2; have := hb.bound q hq; omega
    · intro x g h hq
      rcases hb.tag x g h hq with h1 | ⟨h1, h2, h3⟩
      · exact Or.inl h1
      · exact Or.inr ⟨h1, List.mem_append_left _ h2, h3⟩
    · intro _
      refine ⟨hb.next, ?_, ?_⟩
      · show w.next < w.next + 2; omega
      · intro hm
        obtain ⟨q, hq, he⟩ := List.mem_map.mp hm
        have := hb.bound q hq
        rw [he] at this
        exact Nat.lt_irrefl _ this

/-- Taking back a node of the overlay, read at an earlier state. -/
theorem book_takenBack (B x : NodeId) (c : Ctx) (vr w : W) (n : KNode)
    (hl : vr.nodes.lookup x = some n) (hk : Kept vr w) (hb : Book B c w) :
    WriterWP (takenBack x) c w (fun _ v => Book B c v ∧ Kept w v) := by
  obtain ⟨n', hn', _⟩ := hk.lookup hl
  have hx : x ∈ w.gh.map (·.1) := by
    have := bk_mem_ids_of_lookup _ _ _ hn'
    rw [hb.ids] at this
    exact List.mem_reverse.mp this
  simp only [takenBack, writerWP_modify]
  refine ⟨⟨hb.next, hb.ids, hb.bound, hb.nodup, hb.leaf, hb.tag, ?_, hb.top⟩, Kept.same rfl rfl⟩
  intro y hy
  simp only [List.mem_cons] at hy
  rcases hy with rfl | hy
  · exact hx
  · exact hb.taken y hy

macro "bkNeutral" : tactic => `(tactic| (
  intro c w hv hb
  simp only [writerWP_bind, writerWP_get, writerWP_pure]
  repeat' first
    | split
    | exact writerWP_throw _ _ _ _
    | exact ⟨hb, Kept.refl _⟩
    | simp only [writerWP_bind, writerWP_get, writerWP_pure]))

theorem book_replacedBy (B : NodeId) (x : NodeId) : KeepsBook B (replacedBy x) := by
  unfold replacedBy; bkNeutral
theorem book_pathSize (B : NodeId) : KeepsBook B pathSize := by unfold pathSize; bkNeutral
theorem book_pathNode (B : NodeId) (d : Nat) : KeepsBook B (pathNode d) := by
  unfold pathNode; bkNeutral
theorem book_klongAt (B : NodeId) (d : Nat) : KeepsBook B (klongAt d) := by
  unfold klongAt; bkNeutral

theorem book_parentAt (B : NodeId) (d : Nat) : KeepsBook B (parentAt d) := by
  cases d with
  | zero => intro c w _ hb; simpa only [parentAt, writerWP_pure] using ⟨hb, Kept.refl w⟩
  | succ d =>
    intro c w hv hb
    unfold parentAt
    simp only [writerWP_bind]
    refine writerWP_mono (book_pathNode B d c w hv hb) ?_
    intro _ _ h
    simpa only [writerWP_pure] using h

theorem book_findRoot (B : NodeId) : KeepsBook B findRoot := by
  intro c w hv hb
  unfold findRoot
  simp only [writerWP_bind, writerWP_get, writerWP_pure]
  exact book_pathAdd B none _ c w hv hb

/-- The segment and the height of key node x: no change but a read. -/
theorem book_ghOf (B : NodeId) (x : NodeId) : KeepsBook B (ghOf x) := by
  intro c w hv hb
  unfold ghOf
  simp only [writerWP_bind]
  refine writerWP_mono (book_getNode B x c w hv hb) ?_
  rintro _ v ⟨hbv, hk, _⟩
  simp only [writerWP_get]
  split
  · simp only [writerWP_pure]; exact ⟨hbv, hk⟩
  · exact writerWP_throw _ _ _ _

/-- The segment and the height of key node x of the overlay, read at an
earlier state: no change, and the height is that of the leaf flag. -/
theorem book_ghOf_leaf (B x : NodeId) (c : Ctx) (vr w : W) (n : KNode)
    (hl : vr.nodes.lookup x = some n) (hk : Kept vr w) (hb : Book B c w) :
    WriterWP (ghOf x) c w (fun r v => v = w ∧ n.leaf = (r.2 == 0)) := by
  obtain ⟨n', hn', hleaf⟩ := hk.lookup hl
  unfold ghOf getNode
  simp only [writerWP_bind, writerWP_get, hn', writerWP_pure]
  split
  · rename_i gh hgh
    simp only [writerWP_pure]
    refine ⟨by first | rfl | trivial, ?_⟩
    rw [← hleaf]
    exact hb.leaf x n' gh.1 gh.2 (bk_mem_of_lookup _ _ _ hn') (bk_mem_of_lookup _ _ _ hgh)
  · exact writerWP_throw _ _ _ _

/-! ## Leaf flags of the nodes the writer stores -/

theorem bk_setAt_leaf (n : KNode) (i : Nat) (k : Klong) : (n.setAt i k).leaf = n.leaf := rfl

theorem bk_toPrev_leaf (n : KNode) (t : Time) : (n.toPrev t).leaf = n.leaf := rfl

theorem bk_repoint_leaf (n : KNode) (i : Nat) (y : NodeId) : (n.repoint i y).leaf = n.leaf := by
  unfold KNode.repoint
  split <;> rfl

theorem bk_halves_fst_leaf (leaf : Bool) (t : Time) (last : KNode) (ins : List (Nat × NodeId)) :
    (halves leaf t last ins).1.leaf = leaf := by
  simp only [halves]
  repeat' split
  all_goals rfl

theorem bk_halves_snd_leaf (leaf : Bool) (t : Time) (last : KNode) (ins : List (Nat × NodeId)) :
    (halves leaf t last ins).2.1.leaf = leaf := by
  simp only [halves]
  repeat' split
  all_goals rfl

theorem bk_foldl_add_leaf (i : Time) (ins : List (Nat × NodeId)) (n : KNode) :
    (ins.foldl (fun n q => n.add i (.key q.1 q.2)) n).leaf = n.leaf := by
  induction ins generalizing n with
  | nil => rfl
  | cons q ins ih =>
    rw [List.foldl_cons, ih]
    exact KNode.add_leaf _ _ _

/-- A store of a node of the overlay, read at an earlier state, with its leaf
flag. -/
theorem book_putNode_of (B x : NodeId) (n' : KNode) (c : Ctx) (vr w : W) (n : KNode)
    (hb : Book B c w) (hleaf : n'.leaf = n.leaf) (hl : vr.nodes.lookup x = some n)
    (hk : Kept vr w) :
    WriterWP (putNode x n') c w (fun _ v => Book B c v ∧ Kept w v) := by
  obtain ⟨n0, hn0, h0⟩ := hk.lookup hl
  exact book_putNode B x n' c w hb ⟨n0, hn0, hleaf.trans h0.symm⟩

/-! ## The tactics of the walks -/

macro "bkState" : tactic => `(tactic| first
  | assumption
  | exact Book.upd (by assumption) _ _ _ _ _ _ _ rfl)

/-- `Kept a b` along the chain of the steps' hypotheses `Kept v1 v2`. -/
syntax "bkChain" : tactic
macro_rules
  | `(tactic| bkChain) => `(tactic| first
    | exact Kept.refl _
    | assumption
    | (refine Kept.trans ?bkL (by assumption); bkChain))

macro "bkDone" : tactic => `(tactic| (
  (with_unfolding_none guard_target = Book _ _ _ ∧ Kept _ _)
  refine ⟨?bkS, ?bkK⟩
  case bkS => bkState
  case bkK => bkChain))

macro "bkUse " h:term : tactic => `(tactic| (
  (with_unfolding_none refine' book_writerWP $h _ _ _ ?bkView ?bkState ?bkPost)
  case bkView => assumption
  case bkState => bkState
  intro _ _ _ _))

macro "bkNode" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (getNode _) _ _ _)
  (refine writerWP_mono (book_getNode ?bkB _ _ _ ?bkView ?bkState) ?bkPost)
  case bkView => assumption
  case bkState => bkState
  rintro _ _ ⟨_, _, _⟩))

macro "bkLeaf" : tactic => `(tactic| (
  (try simp only [KNode.add_leaf, bk_setAt_leaf, bk_toPrev_leaf, bk_repoint_leaf,
    bk_halves_fst_leaf, bk_halves_snd_leaf, bk_foldl_add_leaf, apply_ite KNode.leaf, ite_self,
    Bool.not_not])
  all_goals first
    | rfl
    | assumption))

macro "bkStore" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (putNode _ _) _ _ _)
  first
    | (refine writerWP_mono (book_putNode_of ?bkB _ _ _ ?bkVr _ ?bkN ?bkState ?bkLeaf ?bkLook ?bkKept) ?bkPost
       case bkState => bkState
       case bkLeaf => bkLeaf
       case bkLook => assumption
       case bkKept => bkChain
       rintro _ _ ⟨_, _⟩)
    | (refine writerWP_mono (book_putNode_of ?bkB _ _ _ ?bkVr _ ?bkN ?bkState ?bkLeaf ?bkLook ?bkKept) ?bkPost
       case bkState => bkState
       case bkLook => assumption
       case bkLeaf => bkLeaf
       case bkKept => bkChain
       rintro _ _ ⟨_, _⟩)))

/-- The leaf flag of a new node is that of its height. -/
macro "bkHeight" : tactic => `(tactic| first
  | assumption
  | rfl
  | (simp only [Bool.not_not]; assumption)
  | (simp only [Bool.not_not] at *; assumption)
  | simp)

macro "bkCreate" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (newKey _ _ _ _) _ _ _)
  (refine writerWP_mono (book_newKey ?bkB _ _ _ _ _ _ ?bkState ?bkH) ?bkPost)
  case bkState => bkState
  case bkH => bkHeight
  rintro _ _ ⟨_, _, _⟩))

macro "bkTake" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (takenBack _) _ _ _)
  (refine writerWP_mono (book_takenBack ?bkB _ _ ?bkVr _ ?bkN ?bkLook ?bkKept ?bkState) ?bkPost)
  case bkLook => assumption
  case bkKept => bkChain
  case bkState => bkState
  rintro _ _ ⟨_, _⟩))

macro "bkGh" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (ghOf _) _ _ _)
  first
    | (refine writerWP_mono (book_ghOf_leaf ?bkB _ _ ?bkVr _ ?bkN ?bkLook ?bkKept ?bkState) ?bkPost
       case bkLook => assumption
       case bkKept => bkChain
       case bkState => bkState
       rintro ⟨_, _⟩ _ ⟨hbkEq, _⟩
       subst hbkEq)
    | bkUse (book_ghOf _ _)))

macro "bkCore" : tactic => `(tactic| first
  | bkDone
  | bkNode
  | bkStore
  | bkCreate
  | bkTake
  | bkGh
  | bkUse (book_pathAdd _ _ _)
  | bkUse (book_replacedBy _ _)
  | bkUse (book_pathSize _)
  | bkUse (book_pathNode _ _)
  | bkUse (book_klongAt _ _)
  | bkUse (book_parentAt _ _)
  | bkUse (book_findRoot _)
  | bkUse (book_note _ _)
  | bkUse (book_fresh _)
  | bkUse (book_newValue _ _)
  | bkUse (book_newSuperRoot _ _)
  | bkUse (book_setMadeFor _ _ _)
  | bkUse (book_pathClear _)
  | exact writerWP_throw _ _ _ _)

/-! ## The splits -/

theorem book_addKeys (B : NodeId) (x : NodeId) (ins : List (Nat × NodeId)) :
    KeepsBook B (addKeys x ins) := by
  intro c w hv hb
  unfold addKeys
  repeat' first | wpSimplify | bkCore

/-- The loop of a time split changes no state. -/
theorem bk_replaceOrAdd_same (last : KNode) (ins : List (Nat × NodeId)) (c : Ctx) (w : W) :
    WriterWP (replaceOrAdd last ins) c w (fun _ v => v = w) := by
  unfold replaceOrAdd
  simp only [writerWP_bind, writerWP_read]
  induction ins generalizing last with
  | nil => simp only [List.foldlM_nil, writerWP_pure]
  | cons q ins ih =>
    rw [List.foldlM_cons, writerWP_bind]
    cases hr : replaceKlong last.ks c.i q.1 q.2 with
    | error e => exact writerWP_throw _ _ _ _
    | ok result =>
      cases result with
      | none => simp only [writerWP_pure]; exact ih _
      | some ks => simp only [writerWP_pure]; exact ih _

macro "bkReplace" : tactic => `(tactic| (
  (with_unfolding_none guard_target = WriterWP (replaceOrAdd _ _) _ _ _)
  refine writerWP_mono (bk_replaceOrAdd_same _ _ _ _) ?bkPost
  rintro _ _ hbkEq
  subst hbkEq))

set_option maxHeartbeats 1600000 in
/-- Every route of a full node's replacement keeps the books. -/
theorem book_handleFullWith (B : NodeId) (up : NodeId → List (Nat × NodeId) → M Unit)
    (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) (last : KNode) (compact : Bool)
    (hup : ∀ q more, KeepsBook B (up q more)) :
    KeepsBook B (handleFullWith up depth x ins last compact) := by
  intro c w hv hb
  unfold handleFullWith
  repeat' first
    | wpSimplify
    | bkCore
    | bkReplace
    | bkUse (hup _ _)
    | wpSplit
    | split
    | contradiction

end SIS.Tree
