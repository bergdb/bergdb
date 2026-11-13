/-
The heights of the writer's key nodes (bergdb 024-22, step 4 of case (4);
024-12, TP7's open (b), the live heights of children). A key node's height is
its entry in `W.gh`, or for a key node of P the height of its level
(`heightOf`). `HtCache`: every inner node of the overlay that the transaction
did not take back has its live children one height below it. With the books
(`Book`) and the same of P's key nodes (`ViewHeights`), every key node x of
height h has its segment tree balanced and of depth h (`SegDepthEq h x`,
`segDepthEq_of_hasHt`), so the fuel premise of a state follows from the heights
of the nodes it reaches (`segFits_of_heights`).
-/
import SIS.Tree.SegBalance
import SIS.Tree.WriterKindsRules

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- y is a key node of height h: by its entry in the writer's list, or a key
node of the view whose level has height h. -/
def HasHt (c : Ctx) (w : W) (y : NodeId) (h : Nat) : Prop :=
  (∃ g, (y, g, h) ∈ w.gh) ∨
  (∃ nd, c.view y = some nd ∧ nd.isData = false ∧ nd.level ≤ c.p.keyMax ∧ c.p.heightOf nd.level = h)

/-- The live klongs of node n of height h, and of its version before the
transaction, name nodes not taken back, and for an inner node key nodes one
height below it; n has no time after the transaction's. -/
structure NodeHt (c : Ctx) (w : W) (h : Nat) (n : KNode) : Prop where
  live : ∀ cv y, (cv, y) ∈ n.live → w.taken.contains y = false ∧ (h ≠ 0 → HasHt c w y (h - 1))
  prev : ∀ cv y, (cv, y) ∈ (n.toPrev (c.i - 1)).live →
    w.taken.contains y = false ∧ (h ≠ 0 → HasHt c w y (h - 1))
  times : ∀ t, Klong.time t ∈ n.ks → t ≤ c.i

/-- Every node of the overlay that is not taken back meets `NodeHt` for its
height: its live children are not taken back, and an inner node's are one height
below it, now and before the transaction. -/
def HtCache (c : Ctx) (w : W) : Prop :=
  ∀ x n g h, (x, n) ∈ w.nodes → (x, g, h) ∈ w.gh → w.taken.contains x = false →
    NodeHt c w h n

/-- A view's key node of the given height. -/
def ViewHt (c : Ctx) (y : NodeId) (h : Nat) : Prop :=
  ∃ ny, c.view y = some ny ∧ ny.isData = false ∧ ny.level ≤ c.p.keyMax ∧ c.p.heightOf ny.level = h

/-- The same for the view's key nodes: an inner key node's live children are
key nodes of the view one height below it, now and before the transaction. -/
def ViewHeights (c : Ctx) : Prop :=
  ∀ x nd, c.view x = some nd → nd.isData = false → nd.level ≤ c.p.keyMax →
    c.p.heightOf nd.level ≠ 0 →
    (∀ cv y, (cv, y) ∈ (nodeK c.p nd).live → ViewHt c y (c.p.heightOf nd.level - 1)) ∧
    (∀ cv y, (cv, y) ∈ ((nodeK c.p nd).toPrev (c.i - 1)).live →
      ViewHt c y (c.p.heightOf nd.level - 1))

/-- TP7's open (b) (tp7's state note of 2026-11-13, section 2): in P at time t,
an inner key node reached from the root has its live children, that are nodes
of P, one height below it. -/
def HeightLiveOK (p : Params) (P : Struct BVal) (t : Time) : Prop :=
  ∀ x ∈ keyNodesAt p P t, ∀ nd, P.get? x = some nd → p.heightOf nd.level ≠ 0 →
    ∀ c y, (c, y) ∈ (nodeK p nd).liveAt t → ∀ ny, P.get? y = some ny →
      p.heightOf ny.level + 1 = p.heightOf nd.level

theorem HasHt.mono {c : Ctx} {w v : W} {y : NodeId} {h : Nat} (hy : HasHt c w y h)
    (hg : ∀ q ∈ w.gh, q ∈ v.gh) : HasHt c v y h := by
  rcases hy with ⟨g, hm⟩ | hy
  · exact Or.inl ⟨g, hg _ hm⟩
  · exact Or.inr hy

theorem NodeHt.mono {c : Ctx} {w v : W} {h : Nat} {n : KNode} (hn : NodeHt c w h n)
    (hg : ∀ q ∈ w.gh, q ∈ v.gh) (ht : ∀ y, w.taken.contains y = false → v.taken.contains y = false) :
    NodeHt c v h n :=
  ⟨fun cv y hy => ⟨ht y (hn.1 cv y hy).1, fun h0 => ((hn.1 cv y hy).2 h0).mono hg⟩,
   fun cv y hy => ⟨ht y (hn.2 cv y hy).1, fun h0 => ((hn.2 cv y hy).2 h0).mono hg⟩, hn.3⟩

section Facts

variable {B : NodeId} {c : Ctx} {w : W}

/-- A key node has one height. -/
theorem hasHt_tag (hb : Book B c w) (hv : ViewIdsBelow B c.view) {x : NodeId} {g h h' : Nat}
    (hm : (x, g, h) ∈ w.gh) (hx : HasHt c w x h') : h = h' := by
  rcases hx with ⟨g', hm'⟩ | ⟨nd, hnd, _, _, hh⟩
  · exact (kd_tag_eq hb hm hm').2
  · rcases hb.tag x g h hm with ⟨nd', hnd', _, _, _, hh'⟩ | ⟨hB, _, _⟩
    · rw [hnd] at hnd'
      cases hnd'
      rw [hh', hh]
    · exact absurd (hv x nd hnd) (by omega)

theorem ht_wNode_cases {p : Params} {base : View BVal} {w : W} {x : NodeId} {n : KNode}
    (hx : wNode p base w x = some n) :
    w.taken.contains x = false ∧ (w.nodes.lookup x = some n ∨
      (w.nodes.lookup x = none ∧ knodeOf p base x = some n)) := by
  unfold wNode at hx
  cases ht : w.taken.contains x with
  | true =>
    simp only [ht, ↓reduceIte] at hx
    cases hx
  | false =>
    simp only [ht, Bool.false_eq_true, ↓reduceIte] at hx
    refine ⟨rfl, ?_⟩
    cases hl : w.nodes.lookup x with
    | some n' => rw [hl] at hx; cases hx; exact Or.inl rfl
    | none => rw [hl] at hx; exact Or.inr ⟨rfl, hx⟩

theorem ht_knodeOf_some {p : Params} {v : View BVal} {x : NodeId} {n : KNode}
    (hk : knodeOf p v x = some n) :
    ∃ nd, v x = some nd ∧ nd.isData = false ∧ nd.level ≤ p.keyMax ∧
      n = { leaf := p.heightOf nd.level == 0, ks := klongsOf nd.hist } := by
  unfold knodeOf at hk
  split at hk
  · rename_i nd hnd
    split at hk
    · cases hk
    · rename_i hkind
      cases hk
      have hd : nd.isData = false := by cases hd : nd.isData <;> simp_all
      have hlv : nd.level ≤ p.keyMax := by
        have hh : ¬ p.keyMax < nd.level := by
          intro h; simp [h] at hkind
        omega
      exact ⟨nd, hnd, hd, hlv, rfl⟩
  · cases hk

/-- A node of the writer's state has a height, and it is a segment leaf exactly
when that height is 0. -/
theorem hasHt_of_wNode (hb : Book B c w) (base : View BVal)
    (hkb : ∀ x n, knodeOf c.p base x = some n → knodeOf c.p c.view x = some n)
    {x : NodeId} {n : KNode} (hx : wNode c.p base w x = some n) :
    ∃ h, HasHt c w x h ∧ n.leaf = (h == 0) := by
  obtain ⟨_, hl | ⟨_, hk⟩⟩ := ht_wNode_cases hx
  · obtain ⟨g, h, hm⟩ := kd_tag_of_lookup hb hl
    exact ⟨h, Or.inl ⟨g, hm⟩, kd_leaf hb hl hm⟩
  · obtain ⟨nd, hnd, hd, hlv, rfl⟩ := ht_knodeOf_some (hkb x n hk)
    exact ⟨c.p.heightOf nd.level, Or.inr ⟨nd, hnd, hd, hlv, rfl⟩, rfl⟩

/-- Every key node of height h has its segment tree balanced, of depth h. -/
theorem segDepthEq_of_hasHt (hb : Book B c w) (hv : ViewIdsBelow B c.view) (hc : HtCache c w)
    (hvh : ViewHeights c) (base : View BVal)
    (hkb : ∀ x n, knodeOf c.p base x = some n → knodeOf c.p c.view x = some n)
    (htw : ∀ x n, w.nodes.lookup x = some n → ∀ t, Klong.time t ∈ n.ks → t ≤ c.i)
    (htv : ∀ x n, knodeOf c.p c.view x = some n → ∀ t, Klong.time t ∈ n.ks → t ≤ c.i) :
    ∀ h x, HasHt c w x h → SegDepthEq (wNode c.p base w) c.i h x := by
  intro h
  induction h with
  | zero =>
    intro x hx n hn
    obtain ⟨_, hl | ⟨hnone, hk⟩⟩ := ht_wNode_cases hn
    · obtain ⟨g, h1, hm⟩ := kd_tag_of_lookup hb hl
      have e1 := hasHt_tag hb hv hm hx
      rw [kd_leaf hb hl hm, e1]
      rfl
    · obtain ⟨nd, hnd, _, _, rfl⟩ := ht_knodeOf_some (hkb x n hk)
      rcases hx with ⟨g, hm⟩ | ⟨nd', hnd', _, _, hh⟩
      · obtain ⟨n', hl'⟩ := kd_lookup_of_tag hb hm
        rw [hnone] at hl'
        cases hl'
      · rw [hnd] at hnd'
        cases hnd'
        simp [hh]
  | succ k ih =>
    intro x hx n hn
    obtain ⟨htk, hl | ⟨hnone, hk⟩⟩ := ht_wNode_cases hn
    · obtain ⟨g, h1, hm⟩ := kd_tag_of_lookup hb hl
      have e1 := hasHt_tag hb hv hm hx
      subst e1
      refine ⟨?_, ?_⟩
      · rw [kd_leaf hb hl hm]
        simp
      · intro cv y hy
        rw [KNode.liveAt_of_times n c.i (htw x n hl)] at hy
        exact ih y (((hc x n g (k + 1) (bk_mem_of_lookup _ _ _ hl) hm htk).1 cv y hy).2 (by omega))
    · obtain ⟨nd, hnd, hd, hlv, rfl⟩ := ht_knodeOf_some (hkb x n hk)
      rcases hx with ⟨g, hm⟩ | ⟨nd', hnd', _, _, hh⟩
      · obtain ⟨n', hl'⟩ := kd_lookup_of_tag hb hm
        rw [hnone] at hl'
        cases hl'
      · rw [hnd] at hnd'
        cases hnd'
        refine ⟨by simp [hh], ?_⟩
        intro cv y hy
        rw [KNode.liveAt_of_times _ c.i (htv x _ (hkb x _ hk))] at hy
        obtain ⟨ny, hny, hnyd, hnyl, hnyh⟩ :=
          (hvh x nd hnd hd hlv (by omega)).1 cv y hy
        exact ih y (Or.inr ⟨ny, hny, hnyd, hnyl, by omega⟩)

/-- The fuel premise from the heights: when every node reached from r has a
height at most `bound`, every segment tree reached fits in `bound`. -/
theorem segFits_of_heights (hb : Book B c w) (hv : ViewIdsBelow B c.view) (hc : HtCache c w)
    (hvh : ViewHeights c) (base : View BVal)
    (hkb : ∀ x n, knodeOf c.p base x = some n → knodeOf c.p c.view x = some n)
    (htw : ∀ x n, w.nodes.lookup x = some n → ∀ t, Klong.time t ∈ n.ks → t ≤ c.i)
    (htv : ∀ x n, knodeOf c.p c.view x = some n → ∀ t, Klong.time t ∈ n.ks → t ≤ c.i)
    (bound : Nat) (r : NodeId)
    (hr : ∀ x, ReachS (wNode c.p base w) c.i r x → ∀ h, HasHt c w x h → h ≤ bound) :
    SegFits (wNode c.p base w) c.i bound r := by
  intro x hx
  cases hn : wNode c.p base w x with
  | none =>
    cases bound with
    | zero => intro n h; rw [hn] at h; cases h
    | succ b => intro n h; rw [hn] at h; cases h
  | some n =>
    obtain ⟨h, hh, _⟩ := hasHt_of_wNode hb base hkb hn
    have he := segDepthEq_of_hasHt hb hv hc hvh base hkb htw htv h x hh
    exact SegDepthLe.mono _ _ h x (he.le h x) bound (hr x hx h hh)

/-- Balance: every segment tree reached from r is balanced, of depth its root's
height, when every reached node has a height at most `bound`. -/
theorem segBal_of_heights (hb : Book B c w) (hv : ViewIdsBelow B c.view) (hc : HtCache c w)
    (hvh : ViewHeights c) (base : View BVal)
    (hkb : ∀ x n, knodeOf c.p base x = some n → knodeOf c.p c.view x = some n)
    (htw : ∀ x n, w.nodes.lookup x = some n → ∀ t, Klong.time t ∈ n.ks → t ≤ c.i)
    (htv : ∀ x n, knodeOf c.p c.view x = some n → ∀ t, Klong.time t ∈ n.ks → t ≤ c.i)
    (bound : Nat) (r : NodeId)
    (hr : ∀ x, ReachS (wNode c.p base w) c.i r x → ∃ h, h ≤ bound ∧ HasHt c w x h) :
    SegBal (wNode c.p base w) c.i bound r := by
  intro x hx
  obtain ⟨h, hh, hx'⟩ := hr x hx
  exact ⟨h, hh, segDepthEq_of_hasHt hb hv hc hvh base hkb htw htv h x hx'⟩

end Facts

end SIS.Tree
