/-
The heights of the writer's key nodes (bergdb 024-22, step 4 of case (4);
024-12, TP7's open (b), the live heights of children). A key node's height is
its entry in `W.gh`, or for a key node of P the height of its level
(`heightOf`). `HtCache`: every inner node of the overlay that the transaction
did not take back has its live children one height below it. The heights of
P's key nodes come from an oracle H (`ViewHeights`, `BaseHeights`), as the
kinds' walk has them. With the books (`Book`), every key node x of
height h has its segment tree balanced and of depth h (`SegDepthEq h x`,
`segDepthEq_of_hasHt`), so the fuel premise of a state follows from the heights
of the nodes it reaches (`segFits_of_heights`).
-/
import SIS.Tree.SegBalance
import SIS.Tree.WriterKindsRules

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- y is a key node of height h: by its entry in the writer's list, or by what
the oracle H says of P's key nodes. -/
def HasHt (H : NodeId → Nat → Prop) (w : W) (y : NodeId) (h : Nat) : Prop :=
  (∃ g, (y, g, h) ∈ w.gh) ∨ H y h

/-- The live klongs of node n of height h, and of its version before the
transaction, name nodes not taken back, and for an inner node key nodes one
height below it; n has no time after the transaction's. -/
structure NodeHt (c : Ctx) (H : NodeId → Nat → Prop) (w : W) (h : Nat) (n : KNode) : Prop where
  live : ∀ cv y, (cv, y) ∈ n.live → w.taken.contains y = false ∧ (h ≠ 0 → HasHt H w y (h - 1))
  prev : ∀ cv y, (cv, y) ∈ (n.toPrev (c.i - 1)).live →
    w.taken.contains y = false ∧ (h ≠ 0 → HasHt H w y (h - 1))
  times : ∀ t, Klong.time t ∈ n.ks → t ≤ c.i

/-- Every node of the overlay that is not taken back meets `NodeHt` for its
height: its live children are not taken back, and an inner node's are one height
below it, now and before the transaction. -/
def HtCache (c : Ctx) (H : NodeId → Nat → Prop) (w : W) : Prop :=
  ∀ x n g h, (x, n) ∈ w.nodes → (x, g, h) ∈ w.gh → w.taken.contains x = false →
    NodeHt c H w h n

/-- What the oracle H must meet for the writer's view, with B the transaction's
first id: it knows only ids below B, one height a node; a key node of the view
has its level's height; and an inner key node of the view has its live
children, now and before the transaction, one height below it. -/
structure ViewHeights (H : NodeId → Nat → Prop) (B : NodeId) (c : Ctx) : Prop where
  old : ∀ y h, H y h → y < B
  uniq : ∀ y h h', H y h → H y h' → h = h'
  node : ∀ x nd, c.view x = some nd → nd.isData = false → nd.level ≤ c.p.keyMax →
    H x (c.p.heightOf nd.level)
  live : ∀ x nd, c.view x = some nd → nd.isData = false → nd.level ≤ c.p.keyMax →
    c.p.heightOf nd.level ≠ 0 →
    ∀ cv y, (cv, y) ∈ (nodeK c.p nd).live → H y (c.p.heightOf nd.level - 1)
  prev : ∀ x nd, c.view x = some nd → nd.isData = false → nd.level ≤ c.p.keyMax →
    c.p.heightOf nd.level ≠ 0 →
    ∀ cv y, (cv, y) ∈ ((nodeK c.p nd).toPrev (c.i - 1)).live → H y (c.p.heightOf nd.level - 1)

/-- The same of the key nodes of a base that the reading sees: each has a height
of the oracle, is a segment leaf exactly at 0, and an inner one has its live
children one height below it. -/
def BaseHeights (c : Ctx) (H : NodeId → Nat → Prop) (base : View BVal) : Prop :=
  ∀ x n, knodeOf c.p base x = some n → ∃ h, H x h ∧ n.leaf = (h == 0) ∧
    (∀ t, Klong.time t ∈ n.ks → t ≤ c.i) ∧
    (h ≠ 0 → ∀ cv y, (cv, y) ∈ n.live → H y (h - 1))

/-- TP7's open (b) (tp7's state note of 2026-11-13, section 2): in P at time t,
an inner key node reached from the root has its live children, that are nodes
of P, one height below it. -/
def HeightLiveOK (p : Params) (P : Struct BVal) (t : Time) : Prop :=
  ∀ x ∈ keyNodesAt p P t, ∀ nd, P.get? x = some nd → p.heightOf nd.level ≠ 0 →
    ∀ c y, (c, y) ∈ (nodeK p nd).liveAt t → ∀ ny, P.get? y = some ny →
      p.heightOf ny.level + 1 = p.heightOf nd.level

theorem HasHt.mono {H : NodeId → Nat → Prop} {w v : W} {y : NodeId} {h : Nat}
    (hy : HasHt H w y h) (hg : ∀ q ∈ w.gh, q ∈ v.gh) : HasHt H v y h := by
  rcases hy with ⟨g, hm⟩ | hy
  · exact Or.inl ⟨g, hg _ hm⟩
  · exact Or.inr hy

theorem NodeHt.mono {c : Ctx} {H : NodeId → Nat → Prop} {w v : W} {h : Nat} {n : KNode}
    (hn : NodeHt c H w h n)
    (hg : ∀ q ∈ w.gh, q ∈ v.gh) (ht : ∀ y, w.taken.contains y = false → v.taken.contains y = false) :
    NodeHt c H v h n :=
  ⟨fun cv y hy => ⟨ht y (hn.1 cv y hy).1, fun h0 => ((hn.1 cv y hy).2 h0).mono hg⟩,
   fun cv y hy => ⟨ht y (hn.2 cv y hy).1, fun h0 => ((hn.2 cv y hy).2 h0).mono hg⟩, hn.3⟩

section Facts

variable {B : NodeId} {c : Ctx} {H : NodeId → Nat → Prop} {w : W}

/-- A key node has one height. -/
theorem hasHt_tag (hb : Book B c w) (hv : ViewHeights H B c) {x : NodeId} {g h h' : Nat}
    (hm : (x, g, h) ∈ w.gh) (hx : HasHt H w x h') : h = h' := by
  rcases hx with ⟨g', hm'⟩ | hx
  · exact (kd_tag_eq hb hm hm').2
  · rcases hb.tag x g h hm with ⟨nd', hnd', hd, hlv, _, hh'⟩ | ⟨hB, _, _⟩
    · rw [hh']
      exact hv.uniq x _ _ (hv.node x nd' hnd' hd hlv) hx
    · exact absurd (hv.old x h' hx) (by omega)

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
theorem hasHt_of_wNode (hb : Book B c w) (base : View BVal) (hbase : BaseHeights c H base)
    {x : NodeId} {n : KNode} (hx : wNode c.p base w x = some n) :
    ∃ h, HasHt H w x h ∧ n.leaf = (h == 0) := by
  obtain ⟨_, hl | ⟨_, hk⟩⟩ := ht_wNode_cases hx
  · obtain ⟨g, h, hm⟩ := kd_tag_of_lookup hb hl
    exact ⟨h, Or.inl ⟨g, hm⟩, kd_leaf hb hl hm⟩
  · obtain ⟨h, hH, hleaf, _, _⟩ := hbase x n hk
    exact ⟨h, Or.inr hH, hleaf⟩

/-- Every key node of height h has its segment tree balanced, of depth h. -/
theorem segDepthEq_of_hasHt (hb : Book B c w) (hc : HtCache c H w)
    (hvh : ViewHeights H B c) (base : View BVal) (hbase : BaseHeights c H base) :
    ∀ h x, HasHt H w x h → SegDepthEq (wNode c.p base w) c.i h x := by
  intro h
  induction h with
  | zero =>
    intro x hx n hn
    obtain ⟨_, hl | ⟨hnone, hk⟩⟩ := ht_wNode_cases hn
    · obtain ⟨g, h1, hm⟩ := kd_tag_of_lookup hb hl
      have e1 := hasHt_tag hb hvh hm hx
      rw [kd_leaf hb hl hm, e1]
      rfl
    · obtain ⟨h', hH, hleaf, _, _⟩ := hbase x n hk
      rcases hx with ⟨g, hm⟩ | hx
      · obtain ⟨n', hl'⟩ := kd_lookup_of_tag hb hm
        rw [hnone] at hl'
        cases hl'
      · have := hvh.uniq x _ _ hx hH
        subst this
        rw [hleaf]
        rfl
  | succ k ih =>
    intro x hx n hn
    obtain ⟨htk, hl | ⟨hnone, hk⟩⟩ := ht_wNode_cases hn
    · obtain ⟨g, h1, hm⟩ := kd_tag_of_lookup hb hl
      have hN := hc x n g h1 (bk_mem_of_lookup _ _ _ hl) hm htk
      have e1 := hasHt_tag hb hvh hm hx
      subst e1
      refine ⟨?_, ?_⟩
      · rw [kd_leaf hb hl hm]
        simp
      · intro cv y hy
        rw [KNode.liveAt_of_times n c.i hN.3] at hy
        exact ih y ((hN.1 cv y hy).2 (by omega))
    · obtain ⟨h', hH, hleaf, htm, hch⟩ := hbase x n hk
      rcases hx with ⟨g, hm⟩ | hx
      · obtain ⟨n', hl'⟩ := kd_lookup_of_tag hb hm
        rw [hnone] at hl'
        cases hl'
      · have := hvh.uniq x _ _ hx hH
        subst this
        refine ⟨by rw [hleaf]; simp, ?_⟩
        intro cv y hy
        rw [KNode.liveAt_of_times n c.i htm] at hy
        exact ih y (Or.inr (hch (by omega) cv y hy))

/-- The fuel premise from the heights: when every node reached from r has a
height at most `bound`, every segment tree reached fits in `bound`. -/
theorem segFits_of_heights (hb : Book B c w) (hc : HtCache c H w)
    (hvh : ViewHeights H B c) (base : View BVal) (hbase : BaseHeights c H base)
    (bound : Nat) (r : NodeId)
    (hr : ∀ x, ReachS (wNode c.p base w) c.i r x → ∀ h, HasHt H w x h → h ≤ bound) :
    SegFits (wNode c.p base w) c.i bound r := by
  intro x hx
  cases hn : wNode c.p base w x with
  | none =>
    cases bound with
    | zero => intro n h; rw [hn] at h; cases h
    | succ b => intro n h; rw [hn] at h; cases h
  | some n =>
    obtain ⟨h, hh, _⟩ := hasHt_of_wNode hb base hbase hn
    have he := segDepthEq_of_hasHt hb hc hvh base hbase h x hh
    exact SegDepthLe.mono _ _ h x (he.le h x) bound (hr x hx h hh)

/-- Balance: every segment tree reached from r is balanced, of depth its root's
height, when every reached node has a height at most `bound`. -/
theorem segBal_of_heights (hb : Book B c w) (hc : HtCache c H w)
    (hvh : ViewHeights H B c) (base : View BVal) (hbase : BaseHeights c H base)
    (bound : Nat) (r : NodeId)
    (hr : ∀ x, ReachS (wNode c.p base w) c.i r x → ∃ h, h ≤ bound ∧ HasHt H w x h) :
    SegBal (wNode c.p base w) c.i bound r := by
  intro x hx
  obtain ⟨h, hh, hx'⟩ := hr x hx
  exact ⟨h, hh, segDepthEq_of_hasHt hb hc hvh base hbase h x hx'⟩

end Facts

end SIS.Tree
