/-
The contract package (bergdb 030-16): `handleFull` of a delete when it does a
space split (Java's `Dag.spaceSplit` and `spaceSplitInPlace` with nothing to
insert): x's last version `last`, of more than h klongs, is cut in two halves;
at the space root a new space root names both, below it the parent gets one
klong or two (`appendKlongs`); a node that the transaction made keeps the
first half in place.

The put's form of the same rule is WriterSpaceSplit.lean (`handleFull_space`,
from `CasPre`); this file is its form from `CasPreD` (WriterDelDefs.lean): the
node x would be V, and `last` is V's last version.
-/
import Contract.Proof.WriterDelDefs

namespace Contract

open SIS (View)
open SIS.Check (BVal)
open SIS.Tree (Ctx)

/-! ## 1. The state before the step -/

/-- The state before the step keeps what the steps keep (`CasPreD` gives its
frame, top and BalancedOK), and its map is that of the state with x set to V,
but at x. -/
theorem wds_start {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top} {depth : Nat}
    {x : NodeId} {w : MW} {n V last : MNode} {C : List (Key × Nat)}
    (h : CasPreD p i base s tp w depth x n V last C) (htx : w.taken.contains x = false) :
    SsOk p i base s tp (fun _ => False) w ∧
      (treeOf i s (w.withNode x V)).obj x = some (.key ⟨wLevel s w x, n.leaf, ksOf V⟩) ∧
      ∀ z, z ≠ x → (treeOf i s (w.withNode x V)).obj z = (treeOf i s w).obj z := by
  have hA : treeOf i s (w.withNode x V) = (treeOf i s w).set x
      (.key ⟨wLevel s w x, n.leaf, ksOf V⟩) := by
    rw [treeOf_withNode i s _ htx, h.vleaf]
  refine ⟨⟨h.wframe, h.wbal, h.books.toE, h.wtop, ?_⟩, by rw [hA]; simp [Tree.set],
    fun z hz => by rw [hA]; simp [Tree.set, hz]⟩
  intro y m hy hty he
  obtain ⟨t, rest, hr⟩ := h.books.timeFirst y m hy hty
  rw [hr] at he
  cases he

/-- A fresh id names nothing in the map of the state with x set to V. -/
theorem wds_fresh {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top} {depth : Nat}
    {x : NodeId} {w : MW} {n V last : MNode} {C : List (Key × Nat)}
    (hb : Books i base s tp) (h : CasPreD p i base s tp w depth x n V last C)
    (htx : w.taken.contains x = false) {z : NodeId} (hz : w.next ≤ z) :
    (treeOf i s (w.withNode x V)).obj z = none := by
  obtain ⟨-, -, hAz⟩ := wds_start h htx
  have hxz : z ≠ x := fun e => by
    have := h.books.ids.1 x n h.look
    omega
  rw [hAz z hxz]
  exact (treeOf_fresh hb h.books hz).1

/-- V starts with a time klong, and has M + 3 klongs at most if x is reached
in the map of the state with x set to V. -/
theorem wds_vfacts {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top} {depth : Nat}
    {x : NodeId} {w : MW} {n V last : MNode} {C : List (Key × Nat)}
    (h : CasPreD p i base s tp w depth x n V last C) (htx : w.taken.contains x = false)
    (hx : x ∈ reachAt (treeOf i s (w.withNode x V))
      ((treeOf i s (w.withNode x V)).fuel w.top.rootKey) w.top.rootKey) :
    (∃ t rest, V.ks = .time t :: rest) ∧ V.size ≤ p.M + 3 := by
  obtain ⟨-, hAx, -⟩ := wds_start h htx
  refine ⟨h.vfirst, ?_⟩
  have h1 := h.vsound.nodes x hx _ hAx
  simp only [nodeOk, Bool.and_eq_true, decide_eq_true_eq, ite_true] at h1
  rw [← ksOf_length]
  exact h1.1.1

/-- x cut back to before the transaction: its klongs of s. -/
theorem wds_toPrev {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top} {depth : Nat}
    {x : NodeId} {w : MW} {n V last : MNode} {C : List (Key × Nat)}
    (hb : Books i base s tp) (h : CasPreD p i base s tp w depth x n V last C)
    (htx : w.taken.contains x = false) {n0 : KNode} (hs : s.obj x = some (.key n0)) :
    ksOf (n.toPrev (i - 1)) = n0.ks :=
  toPrev_ext (prim_timesBefore (hb.times x n0 hs)) (hb.first x n0 hs)
    (frame_overlay_ext h.wframe h.look htx hs).2.2

/-! ## 2. The halves -/

/-- The halves of `last`, V's last version, as the contract sees them. -/
theorem wds_halves {p : MParams} {i : Time} {leaf : Bool} {V last : MNode}
    (hp : ParamsOK p) (hVf : ∃ t rest, V.ks = .time t :: rest) (hVs : V.size ≤ p.M + 3)
    (hl : ksOf last = Klong.time i :: (live (ksOf V)).map (fun cy => Klong.key cy.1 cy.2))
    (hcase : p.splitAbove < last.size)
    {f s2 : MNode} {sc : Nat} (hH : SIS.Tree.halves leaf i last [] = (f, s2, sc)) :
    ∃ L1 y0 rest, live (ksOf V) = L1 ++ (sc, y0) :: rest ∧ L1 ≠ [] ∧
      f.leaf = leaf ∧ s2.leaf = leaf ∧
      live (ksOf f) = L1 ∧ live (ksOf s2) = (if leaf then sc else 0, y0) :: rest ∧
      klongsWf (ksOf f) = true ∧ klongsWf (ksOf s2) = true ∧
      (∃ rest1, f.ks = .time i :: rest1) ∧ (∃ rest2, s2.ks = .time i :: rest2) ∧
      (∀ t, SIS.Tree.Klong.time t ∈ f.ks → t ≤ i) ∧
      (∀ t, SIS.Tree.Klong.time t ∈ s2.ks → t ≤ i) ∧
      f.size ≤ p.M ∧ s2.size ≤ p.M ∧
      (∀ c y, SIS.Tree.Klong.key c y ∈ f.ks → ∃ c', Klong.key c' y ∈ ksOf V) ∧
      (∀ c y, SIS.Tree.Klong.key c y ∈ s2.ks → ∃ c', Klong.key c' y ∈ ksOf V) := by
  have hs := live_sorted (ksOf V)
  have hlen' : (live (ksOf V)).length + 1 = last.size := by
    rw [← ksOf_length, hl, List.length_cons, List.length_map]
  have hle : (live (ksOf V)).length + 1 ≤ V.size := by
    rw [← ksOf_length]
    obtain ⟨t, rest, hr⟩ := hVf
    exact live_length_le ⟨t, rest.map kOf, by simp [ksOf, hr, kOf]⟩
  have h2 : 2 ≤ (live (ksOf V)).length := by
    have := hp.splitLo
    omega
  obtain ⟨⟨sc0, yy⟩, hget⟩ : ∃ e, (live (ksOf V))[(live (ksOf V)).length / 2]? = some e :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨hc, hfl, hsl, L1, y0, rest, hfold, hL1, -, -, hlf, hls, hwff, hwfs, hf1, hs1, htf, hts,
    hszf, hszs, hkf, hks⟩ := halves_spec leaf i hs hl h2 ⟨yy, hget⟩ [] (Or.inl (by simp)) hH
  subst hc
  have hm : ∀ y, y ∈ (live (ksOf V)).map (·.2) ∨ y ∈ ([] : List (Nat × NodeId)).map (·.2) →
      ∃ c', Klong.key c' y ∈ ksOf V := by
    intro y hy
    rcases hy with hy | hy
    · obtain ⟨⟨c', y'⟩, hm, e⟩ := List.mem_map.mp hy
      simp only at e
      subst e
      exact ⟨c', ss_live_mem hm⟩
    · simp at hy
  refine ⟨L1, y0, rest, hfold, hL1, hfl, hsl, hlf, hls, hwff, hwfs, hf1, hs1,
    fun t ht => Nat.le_of_eq (htf t (ss_time_ksOf ht)),
    fun t ht => Nat.le_of_eq (hts t (ss_time_ksOf ht)), ?_, ?_,
    fun c y hy => hm y (hkf c y (ss_key_ksOf hy)), fun c y hy => hm y (hks c y (ss_key_ksOf hy))⟩
  · have := hp.size
    simp only [List.length_nil] at hszf
    omega
  · have := hp.size
    simp only [List.length_nil] at hszs
    omega

/-! ## 3. The key access path above x -/

/-- Above x the path is in the map of w a chain of inner nodes from the space
root, each one level above the next; so x is not on it above its depth, and
its parent q and x are reached in the map A of the state with x set to V, q
with a live klong (k1, x). -/
theorem wds_path {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top} {d : Nat}
    {x : NodeId} {w : MW} {n V last : MNode} {C : List (Key × Nat)}
    (h : CasPreD p i base s tp w (d + 1) x n V last C)
    {c0 : Option Nat} (hon : w.path[d + 1]? = some (c0, x)) (htx : w.taken.contains x = false) :
    ∃ k1 cq q nq, w.path[d]? = some (cq, q) ∧ w.path[d + 1]? = some (some k1, x) ∧
      w.nodes.lookup q = some nq ∧ w.taken.contains q = false ∧ q ≠ x ∧ nq.leaf = false ∧
      (k1, x) ∈ live (ksOf nq) ∧
      q ∈ reachAt (treeOf i s (w.withNode x V))
        ((treeOf i s (w.withNode x V)).fuel w.top.rootKey) w.top.rootKey ∧
      wLevel s w x + 1 = wLevel s w q ∧
      (∀ e c u, e ≤ d → w.path[e]? = some (c, u) → u ≠ x) ∧
      x ∈ reachAt (treeOf i s (w.withNode x V))
        ((treeOf i s (w.withNode x V)).fuel w.top.rootKey) w.top.rootKey := by
  obtain ⟨-, -, hAz⟩ := wds_start h htx
  have hTx : (treeOf i s w).obj x = some (.key ⟨wLevel s w x, n.leaf, ksOf n⟩) :=
    treeOf_obj_overlay i s h.look htx
  -- the levels along the path, in the map of w
  have hlev : ∀ k, k ≤ d + 1 → ∀ c u, w.path[d + 1 - k]? = some (c, u) →
      ∃ m, (treeOf i s w).obj u = some (.key m) ∧ m.level = wLevel s w x + k := by
    intro k
    induction k with
    | zero =>
      intro _ c u hu
      rw [Nat.sub_zero, hon] at hu
      cases hu
      exact ⟨_, hTx, rfl⟩
    | succ k ih =>
      intro hk c u hu
      obtain ⟨c0', u', c', y, nu, h1, h2, h3, h4⟩ := h.path.links (d - k) (by omega)
      rw [show d + 1 - (k + 1) = d - k by omega, h1] at hu
      cases hu
      obtain ⟨my, hmy1, hmy2⟩ := ih (by omega) _ _
        (by rw [show d + 1 - k = d - k + 1 by omega]; exact h2)
      obtain ⟨_, u2, nu', h5, h6, h7⟩ := h.path.nodes (d - k) (by omega)
      rw [h1] at h5
      cases h5
      have hinner := h.inner (d - k) c u nu' (by omega) h1 h6
      rw [treeOf_obj_overlay i s h6 h7] at h3
      cases h3
      refine ⟨_, treeOf_obj_overlay i s h6 h7, ?_⟩
      obtain ⟨-, -, hb3⟩ := h.wbal u _ (treeOf_obj_overlay i s h6 h7)
      obtain ⟨m', hm1, hm2⟩ := hb3 hinner c' y (ss_live_mem h4)
      rw [hmy1] at hm1
      cases hm1
      simp only at hm2 ⊢
      omega
  have hnx : ∀ e c u, e ≤ d → w.path[e]? = some (c, u) → u ≠ x := by
    intro e c u he hu hux
    subst hux
    obtain ⟨m, hm1, hm2⟩ := hlev (d + 1 - e) (by omega) c u
      (by rw [show d + 1 - (d + 1 - e) = e by omega]; exact hu)
    rw [hTx] at hm1
    cases hm1
    simp only at hm2
    omega
  -- the nodes on the path are reached in A
  have hreach : ∀ e, e ≤ d + 1 → ∀ c u, w.path[e]? = some (c, u) →
      u ∈ reachAt (treeOf i s (w.withNode x V))
        ((treeOf i s (w.withNode x V)).fuel w.top.rootKey) w.top.rootKey := by
    intro e
    induction e with
    | zero =>
      intro _ c u hu
      rw [h.path.root] at hu
      cases hu
      exact tc_self _ _ _
    | succ e ih =>
      intro he c u hu
      obtain ⟨c0', u', c', y, nu, h1, h2, h3, h4⟩ := h.path.links e (by omega)
      rw [h2] at hu
      cases hu
      have hq := ih (by omega) _ _ h1
      have hux := hnx e c0' u' (by omega) h1
      rw [← hAz u' hux] at h3
      have hz := tc_kid h3 h4 (tc_self _ nu.level u)
      exact h.vsound.good.tr_closed hq (g := nu.level + 1) hz
  obtain ⟨c0', q, k1, y, nq', h1, h2, h3, h4⟩ := h.path.links d (by omega)
  rw [hon] at h2
  cases h2
  obtain ⟨_, u2, nq, h5, h6, h7⟩ := h.path.nodes d (by omega)
  rw [h1] at h5
  cases h5
  rw [treeOf_obj_overlay i s h6 h7] at h3
  cases h3
  have hqx := hnx d c0' q le_rfl h1
  have hinner := h.inner d c0' q nq (by omega) h1 h6
  refine ⟨k1, c0', q, nq, h1, hon, h6, h7, hqx, hinner, h4, hreach d (by omega) _ _ h1, ?_, hnx,
    hreach (d + 1) le_rfl _ _ hon⟩
  obtain ⟨-, -, hb3⟩ := h.wbal q _ (treeOf_obj_overlay i s h6 h7)
  obtain ⟨m', hm1, hm2⟩ := hb3 hinner k1 x (ss_live_mem h4)
  rw [hTx] at hm1
  cases hm1
  exact hm2

/-! ## 4. The nodes that the halves name -/

/-- A node that a key klong of V names, x an inner node: a key node one level
below x, not x, and of the state before. -/
theorem wds_named {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top} {depth : Nat}
    {x : NodeId} {w : MW} {n V last : MNode} {C : List (Key × Nat)}
    (hb : Books i base s tp) (h : CasPreD p i base s tp w depth x n V last C)
    (htx : w.taken.contains x = false) (hl : n.leaf = false) {y : NodeId}
    (hy : ∃ c', Klong.key c' y ∈ ksOf V) :
    ∃ m', (treeOf i s w).obj y = some (.key m') ∧ m'.level + 1 = wLevel s w x ∧ y ≠ x ∧
      y < w.next := by
  obtain ⟨-, hAx, hAz⟩ := wds_start h htx
  obtain ⟨c', hc'⟩ := hy
  obtain ⟨-, -, hb3⟩ := h.vbal x _ hAx
  obtain ⟨m', hm1, hm2⟩ := hb3 hl c' y hc'
  have hyx : y ≠ x := by
    intro e
    subst e
    rw [hAx] at hm1
    cases hm1
    simp only at hm2
    omega
  rw [hAz y hyx] at hm1
  refine ⟨m', hm1, hm2, hyx, ?_⟩
  rcases Nat.lt_or_ge y w.next with hlt | hge
  · exact hlt
  · rw [(treeOf_fresh hb h.books hge).1] at hm1
    cases hm1

/-- A node that a key klong of V names exists in the map of the state with x
set to V, if x is reached there. -/
theorem wds_named_some {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {depth : Nat} {x : NodeId} {w : MW} {n V last : MNode}
    {C : List (Key × Nat)} (h : CasPreD p i base s tp w depth x n V last C)
    (htx : w.taken.contains x = false)
    (hx : x ∈ reachAt (treeOf i s (w.withNode x V))
      ((treeOf i s (w.withNode x V)).fuel w.top.rootKey) w.top.rootKey)
    {y : NodeId} (hy : ∃ c', Klong.key c' y ∈ ksOf V) :
    ((treeOf i s (w.withNode x V)).obj y).isSome = true := by
  obtain ⟨-, hAx, -⟩ := wds_start h htx
  obtain ⟨c', hc'⟩ := hy
  exact ss_nodeOk_names (h.vsound.nodes x hx _ hAx) hc'

/-! ## 5. At the space root, x made by the transaction -/

/-- x keeps the first half in place, a new node the second, and a new space
root names both. -/
theorem wds_root_inPlace_post {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {x : NodeId} {w : MW} {n V last : MNode} {C : List (Key × Nat)}
    (hp : ParamsOK p) (hb : Books i base s tp) (h : CasPreD p i base s tp w 0 x n V last C)
    (hcase : p.splitAbove < last.size) (hin : n.firstTime = some i)
    {g hh : Nat} (hgh : w.gh.lookup x = some (g, hh))
    {f s2 : MNode} {sc : Nat} (hH : SIS.Tree.halves n.leaf i last [] = (f, s2, sc))
    {w1 w2 w3 w4 w5 w6 : MW}
    (e1 : w1 = (ssSp w).afterNewKey p g hh n.leaf [])
    (e2 : w2 = ssMF w1 w.next (w1.madeFor.lookup x))
    (e3 : w3 = w2.withNode x f) (e4 : w4 = w3.withNode w.next s2)
    (e5 : w5 = (ssNote w4 "split.space3.inplace").afterNewKey p g (hh + 1) false
      [.time i, .key 0 x, .key sc w.next])
    (e6 : w6 = ssMF w5 (w.next + 2) (w5.madeFor.lookup x)) :
    CasPostD p i base s tp w 0 x V C () (MW.afterSuperRoot w6 p i (w.next + 2)) := by
  intro hout
  obtain ⟨c0, hon⟩ := h.on
  have hlook := h.look
  have htx : w.taken.contains x = false := (h.path.lookup le_rfl hon).choose_spec.2
  obtain ⟨g', hh', hgh', hgG, hhH, hlev, hleafh⟩ := h.books.levels x n hlook htx
  rw [hgh] at hgh'
  cases hgh'
  have hxr : x = w.top.rootKey := by
    have := h.path.root
    rw [hon] at this
    cases this
    rfl
  obtain ⟨hO, hAx, hAz⟩ := wds_start h htx
  have hxreach : x ∈ reachAt (treeOf i s (w.withNode x V))
      ((treeOf i s (w.withNode x V)).fuel w.top.rootKey) w.top.rootKey := by
    rw [← hxr]; exact tc_self _ _ _
  obtain ⟨hVf, hVs⟩ := wds_vfacts h htx hxreach
  obtain ⟨L1, y0, rest, hsplit, hL1, hfl, hsl, hlf, hls, hwff, hwfs, ⟨rf, hf1⟩, ⟨rs, hs1⟩, htf,
    hts, hszf, hszs, hkf, hks⟩ :=
    wds_halves hp hVf hVs h.lastKs hcase hH
  have hsx : s.obj x = none := by
    have := h.books.first x n hlook htx
    rw [hin] at this
    cases e : s.obj x with
    | none => rfl
    | some o => rw [e] at this; exact absurd rfl (this.mp rfl)
  obtain ⟨-, hs0, hn0, -, ht0, hm0⟩ := treeOf_fresh hb h.books (Nat.le_refl w.next)
  have hA0 := wds_fresh hb h htx (Nat.le_refl w.next)
  have hA2 := wds_fresh hb h htx (Nat.le_add_right w.next 2)
  have hxlt : x < w.next := h.books.ids.1 x n hlook
  -- the bound of the new root
  have hout6 : w6.outside = [] := by
    rw [← hout]
    exact ((afterSuperRoot_fields w6 p i (w.next + 2)).2.2.2.2.2.2.2.2).symm
  have hH1 : hh + 1 ≤ p.H := by
    rcases Nat.lt_or_ge p.H (hh + 1) with hc | hc
    · rw [e6, e5] at hout6
      simp [ssMF, MW.afterNewKey, hc] at hout6
    · exact hc
  -- the states
  have hn1 : w1.next = w.next + 2 := by rw [e1]; rfl
  have hlk1 : ∀ y, y ≠ w.next → w1.nodes.lookup y = w.nodes.lookup y := by
    intro y hy
    rw [e1]
    exact prim_lookup_append_ne _ _ hy
  have hlk1n : w1.nodes.lookup w.next = some ⟨n.leaf, []⟩ := by
    rw [e1]
    exact prim_lookup_append_self _ _ hn0
  have hwl1 : ∀ y, y ≠ w.next → wLevel s w1 y = wLevel s w y := by
    intro y hy
    rw [e1]
    exact prim_wLevel_afterNewKey hy
  have hwl1n : wLevel s w1 w.next = p.keyLevel g hh := by
    rw [e1]
    exact ss_wLevel_newKey p g hh n.leaf [] hs0 hm0
  have hO1 : SsOk p i base s tp (fun z => z = w.next) w1 ∧
      ∀ z, (treeOf i s w1).obj z = if z = w.next then some (.key ⟨p.keyLevel g hh, n.leaf, []⟩)
        else (treeOf i s w).obj z := by
    rw [e1]
    exact ssOk_newKey hb (hO.congr (w' := ssSp w) rfl rfl rfl rfl rfl rfl rfl rfl rfl) hgG hhH
      hleafh (Or.inl rfl)
      (by simp) (by simp) (by
        intro z hz
        rcases hz with ⟨hz, -⟩ | hz
        · exact hz
        · exact hz.elim)
  have hO2 : SsOk p i base s tp (fun z => z = w.next) w2 := by
    rw [e2]
    exact hO1.1.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hT2 : treeOf i s w2 = treeOf i s w1 := by rw [e2]; rfl
  have hk2 : w2.taken = w.taken := by rw [e2, e1]; rfl
  have hN2 : w2.nodes = w1.nodes := by rw [e2]; rfl
  have hM2 : w2.made = w1.made := by rw [e2]; rfl
  have hwl2 : wLevel s w2 = wLevel s w1 := by unfold wLevel; rw [hM2]
  have hfst : f.ks.head? = n.ks.head? := by
    obtain ⟨t, r, hr⟩ := h.books.timeFirst x n hlook htx
    have := prim_firstTime_of hr
    rw [hin] at this
    cases this
    rw [hf1, hr]
    rfl
  have hold : ∀ y, y ≠ x → y < w.next → (treeOf i s w2).obj y = (treeOf i s w).obj y := by
    intro y hyx hy
    rw [hT2, hO1.2 y, ss_ite_neg (Nat.ne_of_lt hy)]
  have hO3 : SsOk p i base s tp (fun z => z = w.next) w3 ∧
      ∀ z, (treeOf i s w3).obj z = if z = x then some (.key ⟨wLevel s w x, f.leaf, ksOf f⟩)
        else (treeOf i s w2).obj z := by
    have hwx : wLevel s w2 x = wLevel s w x := by rw [hwl2, hwl1 x (Nat.ne_of_lt hxlt)]
    rw [e3, ← hwx]
    refine ssOk_withNode hO2 (by rw [hN2, hlk1 x (Nat.ne_of_lt hxlt)]; exact hlook)
      (by rw [hk2]; exact htx) hfl
      (Or.inl hfst) htf (fun n0 hn0 => by rw [hsx] at hn0; cases hn0) ?_
      (by rw [hf1]; simp) (fun z _ hz => hz)
    intro hl c y hy
    obtain ⟨m', hm1, hm2, hyx, hylt⟩ := wds_named hb h htx (by rw [← hfl]; exact hl) (hkf c y hy)
    exact ⟨m', by rw [hold y hyx hylt]; exact hm1, by rw [hwx]; exact hm2⟩
  have hN3 : ∀ y, y ≠ x → w3.nodes.lookup y = w2.nodes.lookup y := by
    intro y hy
    rw [e3]
    exact lookup_upsert_ne _ _ hy
  have hwl3 : wLevel s w3 = wLevel s w1 := by rw [e3, ← hwl2]; rfl
  have hO4 : SsOk p i base s tp (fun _ => False) w4 ∧
      ∀ z, (treeOf i s w4).obj z = if z = w.next then
        some (.key ⟨p.keyLevel g hh, s2.leaf, ksOf s2⟩) else (treeOf i s w3).obj z := by
    have hwn : wLevel s w3 w.next = p.keyLevel g hh := by rw [hwl3, hwl1n]
    rw [e4, ← hwn]
    refine ssOk_withNode hO3.1 (m := ⟨n.leaf, []⟩)
      (by rw [hN3 _ (Nat.ne_of_gt hxlt), hN2]; exact hlk1n)
      (by rw [show w3.taken = w2.taken by rw [e3]; rfl, hk2]; exact ht0) hsl
      (Or.inr ⟨rfl, rs, hs1⟩) hts
      (fun n0 hn0 => by rw [hs0] at hn0; cases hn0) ?_ (by rw [hs1]; simp)
      (fun z hz hz' => hz hz')
    intro hl c y hy
    obtain ⟨m', hm1, hm2, hyx, hylt⟩ := wds_named hb h htx (by rw [← hsl]; exact hl) (hks c y hy)
    refine ⟨m', ?_, by rw [hwn, ← hlev]; exact hm2⟩
    rw [hO3.2 y, ss_ite_neg hyx, hold y hyx hylt]
    exact hm1
  have hn4 : w4.next = w.next + 2 := by rw [e4, e3, e2]; exact hn1
  have hO5 : SsOk p i base s tp (fun _ => False) w5 ∧
      ∀ z, (treeOf i s w5).obj z = if z = w.next + 2 then
        some (.key ⟨p.keyLevel g (hh + 1), false,
          ([.time i, .key 0 x, .key sc w.next] : List MKlong).map kOf⟩)
        else (treeOf i s w4).obj z := by
    rw [e5, ← hn4]
    refine ssOk_newKey hb (hO4.1.congr (w' := ssNote w4 "split.space3.inplace") rfl rfl rfl rfl
      rfl rfl rfl rfl rfl) hgG hH1 (by simp)
      (Or.inr ⟨_, rfl⟩) (by simp) ?_ (by simp)
    intro _ c y hy
    simp only [List.mem_cons, SIS.Tree.Klong.key.injEq, List.not_mem_nil, or_false,
      reduceCtorEq, false_or] at hy
    rcases hy with ⟨-, e⟩ | ⟨-, e⟩
    · rw [e]
      refine ⟨⟨wLevel s w x, f.leaf, ksOf f⟩, ?_, ?_⟩
      · show (treeOf i s w4).obj x = _
        rw [hO4.2 x, ss_ite_neg (Nat.ne_of_lt hxlt), hO3.2 x, ss_ite_pos rfl]
      · simp only
        rw [keyLevel_succ, hlev]
    · rw [e]
      refine ⟨⟨p.keyLevel g hh, s2.leaf, ksOf s2⟩, ?_, ?_⟩
      · show (treeOf i s w4).obj w.next = _
        rw [hO4.2 w.next, ss_ite_pos rfl]
      · simp only
        rw [keyLevel_succ]
  have hO6 : SsOk p i base s tp (fun _ => False) w6 := by
    rw [e6]
    exact hO5.1.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hT6 : treeOf i s w6 = treeOf i s w5 := by rw [e6]; rfl
  -- the map after the step
  have hobjF := (treeOf_afterSuperRoot i s p (w.next + 2) hO6.books.ids.1).1
  have hBr : (treeOf i s (MW.afterSuperRoot w6 p i (w.next + 2))).obj (w.next + 2) =
      some (.key ⟨p.keyLevel g (hh + 1), false,
        ([.time i, .key 0 x, .key sc w.next] : List MKlong).map kOf⟩) := by
    rw [hobjF, hT6, hO5.2, ss_ite_pos rfl]
  have hBs : (treeOf i s (MW.afterSuperRoot w6 p i (w.next + 2))).obj w.next =
      some (.key ⟨p.keyLevel g hh, s2.leaf, ksOf s2⟩) := by
    rw [hobjF, hT6, hO5.2, ss_ite_neg (ss_ne_add (by decide)), hO4.2, ss_ite_pos rfl]
  have hBx : (treeOf i s (MW.afterSuperRoot w6 p i (w.next + 2))).obj x =
      some (.key ⟨wLevel s w x, f.leaf, ksOf f⟩) := by
    rw [hobjF, hT6, hO5.2, ss_ite_neg (ss_ne_of_lt_add hxlt), hO4.2, ss_ite_neg (Nat.ne_of_lt hxlt),
      hO3.2,
      ss_ite_pos rfl]
  have hBo : ∀ z, z ≠ w.next + 2 → z ≠ w.next → z ≠ x →
      (treeOf i s (MW.afterSuperRoot w6 p i (w.next + 2))).obj z = (treeOf i s w).obj z := by
    intro z h1 h2 h3
    rw [hobjF, hT6, hO5.2, ss_ite_neg h1, hO4.2, ss_ite_neg h2, hO3.2, ss_ite_neg h3, hT2, hO1.2,
      ss_ite_neg h2]
  have hBA : ∀ z, ((treeOf i s (w.withNode x V)).obj z).isSome = true →
      ((treeOf i s (MW.afterSuperRoot w6 p i (w.next + 2))).obj z).isSome = true := by
    intro z hz
    by_cases h1 : z = w.next + 2
    · rw [h1, hBr]; rfl
    by_cases h2 : z = w.next
    · rw [h2, hBs]; rfl
    by_cases h3 : z = x
    · rw [h3, hBx]; rfl
    rw [hBo z h1 h2 h3, ← hAz z h3]
    exact hz
  have hS : Sound p.M (some x) (treeOf i s (w.withNode x V)) w.top.rootKey C :=
    h.vsound
  rw [← hxr] at hS
  have hsc0 : 0 < sc := Good.tr_split_lo hS.good hAx hsplit hL1
  have hnames : ∀ (m : MNode), (∀ c y, SIS.Tree.Klong.key c y ∈ m.ks →
      ∃ c', Klong.key c' y ∈ ksOf V) → ∀ c y, SIS.Tree.Klong.key c y ∈ m.ks →
      ((treeOf i s (MW.afterSuperRoot w6 p i (w.next + 2))).obj y).isSome = true :=
    fun m hm c y hy => hBA y (wds_named_some h htx hxreach (hm c y hy))
  have hNf : NodeIs (treeOf i s (MW.afterSuperRoot w6 p i (w.next + 2))) x (wLevel s w x) n.leaf
      L1 p.M := by
    rw [← hfl]
    exact ss_nodeIs hBx hlf hwff hszf (hnames f hkf)
  have hNs : NodeIs (treeOf i s (MW.afterSuperRoot w6 p i (w.next + 2))) w.next (wLevel s w x)
      n.leaf (if n.leaf then (sc, y0) :: rest else (0, y0) :: rest) p.M := by
    rw [← hsl, hlev]
    refine ss_nodeIs hBs ?_ hwfs hszs (hnames s2 hks)
    rw [hls, hsl]
    cases n.leaf <;> rfl
  have hNr : NodeIs (treeOf i s (MW.afterSuperRoot w6 p i (w.next + 2))) (w.next + 2)
      (wLevel s w x + 1) false [(0, x), (sc, w.next)] p.M := by
    rw [hlev, ← keyLevel_succ]
    exact ss_nodeIs_root hsc0 (by have := hp.size; omega) hBr (by rw [hBx]; rfl)
      (by rw [hBs]; rfl)
  obtain ⟨hSB, -, hRB⟩ := Sound.spaceSplitRoot hS hAx hsplit hL1 (Or.inl rfl) hA0
    (Nat.ne_of_lt hxlt) hA2 ⟨(ss_ne_of_lt_add hxlt).symm, (ss_ne_add (by decide)).symm⟩ hNf hNs
    hNr (by rw [hBx]; rfl)
    (fun z h1 _ h3 h4 => by rw [hBo z h4 h3 h1, hAz z h1])
  obtain ⟨hPI, -, hrkF⟩ := ss_pinv_superRoot hb hO6 (fun _ h => h) (w.next + 2) hSB
  refine ⟨hPI, ⟨?_, ?_, ?_, ?_⟩⟩
  · rw [(afterSuperRoot_fields w6 p i (w.next + 2)).2.2.2.2.2.2.2.1, e6, e5, e4, e3, e2, e1]
    rfl
  · intro y ny hy hnot
    have hyx : y ≠ x := fun e => hnot 0 c0 le_rfl (by rw [e]; exact hon)
    have hylt : y < w.next := h.books.ids.1 y ny hy
    rw [(afterSuperRoot_fields w6 p i (w.next + 2)).2.2.1,
      show w6.nodes = w5.nodes by rw [e6]; rfl]
    have e5n : w5.nodes = w4.nodes ++ [(w4.next, ⟨false, [.time i, .key 0 x, .key sc w.next]⟩)] :=
      by rw [e5]; rfl
    rw [e5n, prim_lookup_append_ne _ _ (by rw [hn4]; exact ss_ne_of_lt_add hylt), e4, MW.withNode,
      lookup_upsert_ne _ _ (Nat.ne_of_lt hylt), hN3 y hyx, hN2, hlk1 y (Nat.ne_of_lt hylt)]
    exact hy
  · have h6 : w6.next = w.next + 4 := by rw [e6, e5]; show w4.next + 2 = _; rw [hn4]
    exact Nat.le_trans (ss_le_add h6) (ss_afterSuperRoot_next w6 p i (w.next + 2))
  · intro z hz
    unfold reachOf at hz ⊢
    rw [hrkF] at hz
    have hW0r : (w.withNode x V).top.rootKey = x := hxr.symm
    rw [hW0r]
    rcases hRB z hz with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · rw [h1]
      exact Or.inl (tc_self _ _ _)
    · rw [h1]
      exact Or.inr (Nat.le_refl _)
    · rw [h1]
      exact Or.inr (Nat.le_add_right _ _)

theorem wds_root_inPlace {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {x : NodeId} {w : MW} {n V last : MNode}
    {C : List (Key × Nat)} {up : NodeId → List (Nat × NodeId) → SIS.Tree.M Unit}
    (hp : ParamsOK p) (hb : Books i base s tp) (h : CasPreD p i base s tp w 0 x n V last C)
    (hcase : p.splitAbove < last.size) (hin : n.firstTime = some i) :
    WP (SIS.Tree.handleFullWith up 0 x [] last false)
      { p := p, i := i, view := v } w (CasPostD p i base s tp w 0 x V C) := by
  obtain ⟨c0, hon⟩ := h.on
  have htx : w.taken.contains x = false := (h.path.lookup le_rfl hon).choose_spec.2
  obtain ⟨g, hh, hgh, -⟩ := h.books.levels x n h.look htx
  have hc' : (!false && decide (last.size > p.splitAbove)) = true := by
    simpa using hcase
  unfold SIS.Tree.handleFullWith
  refine ss_wp_step (ss_read _ w) ?_
  refine ss_wp_step (getNode_hit _ h.look) ?_
  refine ss_wp_step (ghOf_hit _ h.look hgh) ?_
  refine ss_wp_step (parentAt_zero _ _) ?_
  dsimp only
  refine ss_wp_step (ss_pure _ _ _) ?_
  simp only [Bool.false_eq_true, ↓reduceIte, hc', hin, beq_self_eq_true]
  refine ss_wp_step (ss_modify _ _) ?_
  refine ss_wp_step (newKey_eq _ _ _ _ _ _) ?_
  refine ss_wp_step (replacedBy_eq _ _ _) ?_
  refine ss_wp_step (ss_setMadeFor _ _ _ _) ?_
  generalize hH : SIS.Tree.halves n.leaf i last [] = H
  obtain ⟨f, s2, sc⟩ := H
  dsimp only
  refine ss_wp_step (putNode_eq _ _ _ _) ?_
  refine ss_wp_step (putNode_eq _ _ _ _) ?_
  refine ss_wp_step (ss_note _ _ _) ?_
  refine ss_wp_step (newKey_eq _ _ _ _ _ _) ?_
  refine ss_wp_step (replacedBy_eq _ _ _) ?_
  refine ss_wp_step (ss_setMadeFor _ _ _ _) ?_
  refine ss_wp_step (newSuperRoot_eq v _ h.wtop) ?_
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  refine (wp_pure _ _ _ _).mpr ?_
  exact wds_root_inPlace_post hp hb h hcase hin hgh hH rfl rfl rfl rfl rfl rfl

/-! ## 6. At the space root, x from before the transaction -/

/-- Two new nodes hold the halves, a new space root names both, and x is cut
back to before the transaction. -/
theorem wds_root_new_post {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {x : NodeId} {w : MW} {n V last : MNode}
    {C : List (Key × Nat)} (hp : ParamsOK p) (hb : Books i base s tp)
    (h : CasPreD p i base s tp w 0 x n V last C)
    (hcase : p.splitAbove < last.size) (hin : ¬ n.firstTime = some i)
    {g hh : Nat} (hgh : w.gh.lookup x = some (g, hh))
    {f s2 : MNode} {sc : Nat} (hH : SIS.Tree.halves n.leaf i last [] = (f, s2, sc))
    {w1 w2 w3 w4 w5 w6 w7 w8 : MW}
    (e1 : w1 = (ssSp w).afterNewKey p g hh n.leaf [])
    (e2 : w2 = w1.afterNewKey p g hh n.leaf [])
    (e3 : w3 = ssMF (ssMF w2 w.next (some x)) (w.next + 2) (some x))
    (e4 : w4 = (ssNote w3 "split.space3").afterNewKey p g (hh + 1) false [])
    (e5 : w5 = ssMF w4 (w.next + 4) (some x))
    (e6 : w6 = w5.withNode w.next f) (e7 : w7 = w6.withNode (w.next + 2) s2)
    (e8 : w8 = w7.withNode (w.next + 4) ⟨false, [.time i, .key 0 w.next, .key sc (w.next + 2)]⟩) :
    WP (SIS.Tree.getNode x >>= fun n' => SIS.Tree.putNode x (n'.toPrev (i - 1)))
      { p := p, i := i, view := v } (MW.afterSuperRoot w8 p i (w.next + 4))
      (CasPostD p i base s tp w 0 x V C) := by
  obtain ⟨c0, hon⟩ := h.on
  have hlook := h.look
  have htx : w.taken.contains x = false := (h.path.lookup le_rfl hon).choose_spec.2
  have hxlt : x < w.next := h.books.ids.1 x n hlook
  have hn1 : w1.next = w.next + 2 := by rw [e1]; rfl
  have hn2 : w2.next = w.next + 4 := by rw [e2]; show w1.next + 2 = _; rw [hn1]
  have hn3 : w3.next = w.next + 4 := by rw [e3]; exact hn2
  -- the node lookups through the steps
  have hlk : ∀ y, y ≠ w.next → y ≠ w.next + 2 → y ≠ w.next + 4 →
      w8.nodes.lookup y = w.nodes.lookup y := by
    intro y h1 h2 h4
    rw [e8, ss_lookup_withNode h4, e7, ss_lookup_withNode h2, e6, ss_lookup_withNode h1,
      show w5.nodes = w4.nodes by rw [e5]; rfl, e4,
      ss_lookup_newKey (w := ssNote w3 "split.space3") (by show y ≠ w3.next; rw [hn3]; exact h4),
      show (ssNote w3 "split.space3").nodes = w2.nodes by rw [e3]; rfl, e2,
      ss_lookup_newKey (w := w1) (by rw [hn1]; exact h2), e1,
      ss_lookup_newKey (w := ssSp w) h1]
    rfl
  have hlk9 : (MW.afterSuperRoot w8 p i (w.next + 4)).nodes.lookup x = some n := by
    rw [(afterSuperRoot_fields w8 p i _).2.2.1, hlk x (Nat.ne_of_lt hxlt)
      (ss_ne_of_lt_add hxlt) (ss_ne_of_lt_add hxlt)]
    exact hlook
  refine ss_wp_step (getNode_hit _ hlk9) ?_
  refine ss_wp_putNode ?_
  intro hout
  obtain ⟨g', hh', hgh', hgG, hhH, hlev, hleafh⟩ := h.books.levels x n hlook htx
  rw [hgh] at hgh'
  cases hgh'
  have hxr : x = w.top.rootKey := by
    have := h.path.root
    rw [hon] at this
    cases this
    rfl
  obtain ⟨hO, hAx, hAz⟩ := wds_start h htx
  have hxreach : x ∈ reachAt (treeOf i s (w.withNode x V))
      ((treeOf i s (w.withNode x V)).fuel w.top.rootKey) w.top.rootKey := by
    rw [← hxr]; exact tc_self _ _ _
  obtain ⟨hVf, hVs⟩ := wds_vfacts h htx hxreach
  obtain ⟨L1, y0, rest, hsplit, hL1, hfl, hsl, hlf, hls, hwff, hwfs, ⟨rf, hf1⟩, ⟨rs, hs1⟩, htf,
    hts, hszf, hszs, hkf, hks⟩ :=
    wds_halves hp hVf hVs h.lastKs hcase hH
  obtain ⟨t0, r0, hr0⟩ := h.books.timeFirst x n hlook htx
  have ht0i : t0 ≤ i - 1 := by
    have h1 : @LE.le Nat _ t0 i :=
      h.books.times x n hlook t0 (by rw [hr0]; exact List.mem_cons_self)
    have h2 : t0 ≠ i := fun e => hin (by rw [prim_firstTime_of hr0, e])
    have h3 : @Ne Nat t0 i := h2
    omega
  obtain ⟨-, hs0, hn0, -, ht0, hm0⟩ := treeOf_fresh hb h.books (Nat.le_refl w.next)
  have hA0 := wds_fresh hb h htx (Nat.le_refl w.next)
  have hA2 := wds_fresh hb h htx (Nat.le_add_right w.next 2)
  have hA4 := wds_fresh hb h htx (Nat.le_add_right w.next 4)
  -- the bound of the new root
  have hout4 : w4.outside = [] := by
    rw [← hout]
    show w4.outside = (MW.afterSuperRoot w8 p i (w.next + 4)).outside
    rw [(afterSuperRoot_fields w8 p i (w.next + 4)).2.2.2.2.2.2.2.2, e8, e7, e6, e5]
    rfl
  have hH1 : hh + 1 ≤ p.H := by
    rcases Nat.lt_or_ge p.H (hh + 1) with hc | hc
    · rw [e4] at hout4
      simp [MW.afterNewKey, hc] at hout4
    · exact hc
  -- the steps
  have hO1 : SsOk p i base s tp (fun z => z = w.next) w1 ∧
      ∀ z, (treeOf i s w1).obj z = if z = w.next then some (.key ⟨p.keyLevel g hh, n.leaf, []⟩)
        else (treeOf i s w).obj z := by
    rw [e1]
    exact ssOk_newKey hb (hO.congr (w' := ssSp w) rfl rfl rfl rfl rfl rfl rfl rfl rfl) hgG hhH
      hleafh (Or.inl rfl) (by simp) (by simp) (by
        intro z hz
        rcases hz with ⟨hz, -⟩ | hz
        · exact hz
        · exact hz.elim)
  have hfr1 := treeOf_freshE hb hO1.1.books (Nat.le_refl w1.next)
  rw [hn1] at hfr1
  obtain ⟨-, hs2, hn2', -, ht2, hm2⟩ := hfr1
  have hO2 : SsOk p i base s tp (fun z => z = w.next + 2 ∨ z = w.next) w2 ∧
      ∀ z, (treeOf i s w2).obj z = if z = w.next + 2 then
        some (.key ⟨p.keyLevel g hh, n.leaf, []⟩) else (treeOf i s w1).obj z := by
    rw [e2, ← hn1]
    exact ssOk_newKey hb hO1.1 hgG hhH hleafh (Or.inl rfl) (by simp) (by simp) (by
        intro z hz
        rcases hz with ⟨hz, -⟩ | hz
        · exact Or.inl hz
        · exact Or.inr hz)
  have hO3 : SsOk p i base s tp (fun z => z = w.next + 2 ∨ z = w.next) w3 := by
    rw [e3]
    exact hO2.1.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hT3 : treeOf i s w3 = treeOf i s w2 := by rw [e3]; rfl
  have hfr3 := treeOf_freshE hb hO3.books (Nat.le_refl w3.next)
  rw [hn3] at hfr3
  obtain ⟨-, hs4, hn4', -, ht4, hm4⟩ := hfr3
  have hO4 : SsOk p i base s tp (fun z => z = w.next + 4 ∨ z = w.next + 2 ∨ z = w.next) w4 ∧
      ∀ z, (treeOf i s w4).obj z = if z = w.next + 4 then
        some (.key ⟨p.keyLevel g (hh + 1), false, []⟩) else (treeOf i s w3).obj z := by
    rw [e4, ← hn3]
    exact ssOk_newKey hb (hO3.congr (w' := ssNote w3 "split.space3") rfl rfl rfl rfl rfl rfl rfl rfl
      rfl) hgG hH1 (by simp) (Or.inl rfl) (by simp) (by simp) (by
        intro z hz
        rcases hz with ⟨hz, -⟩ | hz
        · exact Or.inl hz
        · exact Or.inr hz)
  have hO5 : SsOk p i base s tp (fun z => z = w.next + 4 ∨ z = w.next + 2 ∨ z = w.next) w5 := by
    rw [e5]
    exact hO4.1.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hT5 : treeOf i s w5 = treeOf i s w4 := by rw [e5]; rfl
  have hk5 : w5.taken = w.taken := by rw [e5, e4, e3, e2, e1]; rfl
  have hM5 : wLevel s w5 = wLevel s w4 := by rw [e5]; rfl
  have hw4n : ∀ y, y ≠ w.next + 4 → wLevel s w5 y = wLevel s w2 y := by
    intro y hy
    rw [hM5, e4, prim_wLevel_afterNewKey (w := ssNote w3 "split.space3")
      (by show y ≠ w3.next; rw [hn3]; exact hy)]
    rw [e3]
    rfl
  have hwl0 : wLevel s w5 w.next = p.keyLevel g hh := by
    rw [hw4n _ (ss_ne_add (by decide)), e2,
      prim_wLevel_afterNewKey (w := w1) (by rw [hn1]; exact ss_ne_add (by decide)), e1]
    exact ss_wLevel_newKey p g hh n.leaf [] hs0 hm0
  have hwl2 : wLevel s w5 (w.next + 2) = p.keyLevel g hh := by
    rw [hw4n _ (by
      have := ss_ne_add (a := w.next + 2) (b := 2) (by decide)
      rw [Nat.add_assoc] at this
      exact this), e2, ← hn1]
    exact ss_wLevel_newKey p g hh n.leaf [] (by rw [hn1]; exact hs2) (by rw [hn1]; exact hm2)
  have hwl4 : wLevel s w5 (w.next + 4) = p.keyLevel g (hh + 1) := by
    rw [hM5, e4, ← hn3]
    exact ss_wLevel_newKey (w := ssNote w3 "split.space3") p g (hh + 1) false []
      (by show s.obj w3.next = none; rw [hn3]; exact hs4)
      (by show ∀ m ∈ w3.made, m.id ≠ w3.next; rw [hn3]; exact hm4)
  have hN5 : ∀ y, y ≠ w.next + 4 → y ≠ w.next + 2 → w5.nodes.lookup y = w1.nodes.lookup y := by
    intro y h4 h2
    rw [show w5.nodes = w4.nodes by rw [e5]; rfl, e4,
      ss_lookup_newKey (w := ssNote w3 "split.space3") (by show y ≠ w3.next; rw [hn3]; exact h4),
      show (ssNote w3 "split.space3").nodes = w2.nodes by rw [e3]; rfl, e2,
      ss_lookup_newKey (w := w1) (by rw [hn1]; exact h2)]
  have hlk1n : w1.nodes.lookup w.next = some ⟨n.leaf, []⟩ := by
    rw [e1]
    exact prim_lookup_append_self _ _ hn0
  have hold5 : ∀ y, y < w.next → (treeOf i s w5).obj y = (treeOf i s w).obj y := by
    intro y hy
    rw [hT5, hO4.2, ss_ite_neg (ss_ne_of_lt_add hy), hT3, hO2.2, ss_ite_neg (ss_ne_of_lt_add hy),
      hO1.2, ss_ite_neg (Nat.ne_of_lt hy)]
  have hO6 : SsOk p i base s tp (fun z => z = w.next + 4 ∨ z = w.next + 2) w6 ∧
      ∀ z, (treeOf i s w6).obj z = if z = w.next then
        some (.key ⟨p.keyLevel g hh, f.leaf, ksOf f⟩) else (treeOf i s w5).obj z := by
    rw [e6, ← hwl0]
    refine ssOk_withNode hO5 (m := ⟨n.leaf, []⟩)
      (by rw [hN5 _ (ss_ne_add (by decide)) (ss_ne_add (by decide)), hlk1n])
      (by rw [hk5]; exact ht0) hfl (Or.inr ⟨rfl, rf, hf1⟩) htf
      (fun n0 hn0' => by rw [hs0] at hn0'; cases hn0') ?_ (by rw [hf1]; simp) ?_
    · intro hl c y hy
      obtain ⟨m', hm1, hm2, hyx, hylt⟩ := wds_named hb h htx (by rw [← hfl]; exact hl)
        (hkf c y hy)
      exact ⟨m', by rw [hold5 y hylt]; exact hm1, by rw [hwl0, ← hlev]; exact hm2⟩
    · intro z hz hz'
      rcases hz' with hz' | hz' | hz'
      · exact Or.inl hz'
      · exact Or.inr hz'
      · exact absurd hz' hz
  have hne20 : w.next + 2 ≠ w.next := (ss_ne_add (by decide)).symm
  have hne40 : w.next + 4 ≠ w.next := (ss_ne_add (by decide)).symm
  have hne42 : w.next + 4 ≠ w.next + 2 := by
    have := ss_ne_add (a := w.next + 2) (b := 2) (by decide)
    rw [Nat.add_assoc] at this
    exact this.symm
  have hlk1 : w1.nodes.lookup (w.next + 2) = none := by rw [← hn1]; rw [hn1]; exact hn2'
  have hO7 : SsOk p i base s tp (fun z => z = w.next + 4) w7 ∧
      ∀ z, (treeOf i s w7).obj z = if z = w.next + 2 then
        some (.key ⟨p.keyLevel g hh, s2.leaf, ksOf s2⟩) else (treeOf i s w6).obj z := by
    have hwl6 : wLevel s w6 (w.next + 2) = p.keyLevel g hh := by rw [e6]; exact hwl2
    rw [e7, ← hwl6]
    refine ssOk_withNode hO6.1 (m := ⟨n.leaf, []⟩) ?_
      (by
        rw [e6]; show w5.taken.contains _ = false
        rw [hk5, show w.taken = w1.taken by rw [e1]; rfl]; exact ht2) hsl
      (Or.inr ⟨rfl, rs, hs1⟩) hts (fun n0 hn0' => by rw [hs2] at hn0'; cases hn0') ?_
      (by rw [hs1]; simp) ?_
    · rw [e6, ss_lookup_withNode hne20, show w5.nodes = w4.nodes by rw [e5]; rfl, e4,
        ss_lookup_newKey (w := ssNote w3 "split.space3")
          (by show _ ≠ w3.next; rw [hn3]; exact hne42.symm),
        show (ssNote w3 "split.space3").nodes = w2.nodes by rw [e3]; rfl, e2, ← hn1]
      exact prim_lookup_append_self _ _ (by rw [hn1]; exact hlk1)
    · intro hl c y hy
      obtain ⟨m', hm1, hm2, hyx, hylt⟩ := wds_named hb h htx (by rw [← hsl]; exact hl)
        (hks c y hy)
      refine ⟨m', ?_, by rw [hwl6, ← hlev]; exact hm2⟩
      rw [hO6.2, ss_ite_neg (Nat.ne_of_lt hylt), hold5 y hylt]
      exact hm1
    · intro z hz hz'
      rcases hz' with hz' | hz'
      · exact hz'
      · exact absurd hz' hz
  have hO8 : SsOk p i base s tp (fun _ => False) w8 ∧
      ∀ z, (treeOf i s w8).obj z = if z = w.next + 4 then
        some (.key ⟨p.keyLevel g (hh + 1), false,
          ([.time i, .key 0 w.next, .key sc (w.next + 2)] : List MKlong).map kOf⟩)
        else (treeOf i s w7).obj z := by
    have hwl7 : wLevel s w7 (w.next + 4) = p.keyLevel g (hh + 1) := by rw [e7, e6]; exact hwl4
    rw [e8, ← hwl7]
    refine ssOk_withNode hO7.1 (m := ⟨false, []⟩) ?_
      (by
        rw [e7, e6]; show w5.taken.contains _ = false
        rw [hk5, show w.taken = w3.taken by rw [e3, e2, e1]; rfl]; exact ht4) rfl
      (Or.inr ⟨rfl, _, rfl⟩) (by simp) (fun n0 hn0' => by rw [hs4] at hn0'; cases hn0') ?_
      (by simp) (fun _ hz h => hz h)
    · rw [e7, ss_lookup_withNode hne42, e6, ss_lookup_withNode hne40,
        show w5.nodes = w4.nodes by rw [e5]; rfl, e4, ← hn3]
      exact prim_lookup_append_self (l := (ssNote w3 "split.space3").nodes) _
        (by show w3.nodes.lookup w3.next = none; rw [hn3]; exact hn4')
    · intro _ c y hy
      simp only [List.mem_cons, SIS.Tree.Klong.key.injEq, List.not_mem_nil, or_false,
        reduceCtorEq, false_or] at hy
      rcases hy with ⟨-, e⟩ | ⟨-, e⟩
      · rw [e]
        refine ⟨⟨p.keyLevel g hh, f.leaf, ksOf f⟩, ?_, by rw [hwl7, keyLevel_succ]⟩
        rw [hO7.2, ss_ite_neg hne20.symm, hO6.2, ss_ite_pos rfl]
      · rw [e]
        refine ⟨⟨p.keyLevel g hh, s2.leaf, ksOf s2⟩, ?_, by rw [hwl7, keyLevel_succ]⟩
        rw [hO7.2, ss_ite_pos rfl]
  obtain ⟨hO9, hobj9, hroot9, hrk9⟩ := ssOk_superRoot hb hO8.1 (w.next + 4)
  have htx9 : (MW.afterSuperRoot w8 p i (w.next + 4)).taken.contains x = false := by
    rw [(afterSuperRoot_fields w8 p i (w.next + 4)).2.2.2.2.1, e8, e7, e6]
    show w5.taken.contains x = false
    rw [hk5]; exact htx
  have hO10 := ssOk_withNode (E' := fun _ => False) hO9 hlk9 htx9 rfl (m' := n.toPrev (i - 1))
    (Or.inl (by
      obtain ⟨rest', hr'⟩ := ss_toPrev_head hr0 ht0i
      rw [hr', hr0]; rfl))
    (fun t ht => h.books.times x n hlook t (ss_mem_toPrev ht))
    (fun n0 hn0' => Or.inl (wds_toPrev hb h htx hn0'))
    (fun hl c y hy => by
      obtain ⟨-, -, hb3⟩ := hO9.bal x _ (treeOf_obj_overlay i s hlk9 htx9)
      exact hb3 hl c y (ss_key_ksOf (ss_mem_toPrev hy)))
    (by obtain ⟨rest', hr'⟩ := ss_toPrev_head hr0 ht0i; rw [hr']; simp) (fun _ _ h => h)
  -- the map after the step
  have hxn : x ≠ w.next := Nat.ne_of_lt hxlt
  have hxn2 : x ≠ w.next + 2 := ss_ne_of_lt_add hxlt
  have hxn4 : x ≠ w.next + 4 := ss_ne_of_lt_add hxlt
  have hB : ∀ z, z ≠ x → (treeOf i s ((MW.afterSuperRoot w8 p i (w.next + 4)).withNode x
      (n.toPrev (i - 1)))).obj z = (treeOf i s w8).obj z := by
    intro z hz
    rw [hO10.2, ss_ite_neg hz, hobj9]
  have hBr : (treeOf i s ((MW.afterSuperRoot w8 p i (w.next + 4)).withNode x
      (n.toPrev (i - 1)))).obj (w.next + 4) = some (.key ⟨p.keyLevel g (hh + 1), false,
        ([.time i, .key 0 w.next, .key sc (w.next + 2)] : List MKlong).map kOf⟩) := by
    rw [hB _ hxn4.symm, hO8.2, ss_ite_pos rfl]
  have hBs : (treeOf i s ((MW.afterSuperRoot w8 p i (w.next + 4)).withNode x
      (n.toPrev (i - 1)))).obj (w.next + 2) = some (.key ⟨p.keyLevel g hh, s2.leaf, ksOf s2⟩) := by
    rw [hB _ hxn2.symm, hO8.2, ss_ite_neg hne42.symm, hO7.2, ss_ite_pos rfl]
  have hBf : (treeOf i s ((MW.afterSuperRoot w8 p i (w.next + 4)).withNode x
      (n.toPrev (i - 1)))).obj w.next = some (.key ⟨p.keyLevel g hh, f.leaf, ksOf f⟩) := by
    rw [hB _ hxn.symm, hO8.2, ss_ite_neg hne40.symm, hO7.2, ss_ite_neg hne20.symm, hO6.2,
      ss_ite_pos rfl]
  have hBx : ((treeOf i s ((MW.afterSuperRoot w8 p i (w.next + 4)).withNode x
      (n.toPrev (i - 1)))).obj x).isSome = true := by
    rw [hO10.2, ss_ite_pos rfl]; rfl
  have hBo : ∀ z, z ≠ x → z ≠ w.next → z ≠ w.next + 2 → z ≠ w.next + 4 →
      (treeOf i s ((MW.afterSuperRoot w8 p i (w.next + 4)).withNode x
        (n.toPrev (i - 1)))).obj z = (treeOf i s w).obj z := by
    intro z h0 h1 h2 h4
    rw [hB z h0, hO8.2, ss_ite_neg h4, hO7.2, ss_ite_neg h2, hO6.2, ss_ite_neg h1, hT5, hO4.2,
      ss_ite_neg h4, hT3, hO2.2, ss_ite_neg h2, hO1.2, ss_ite_neg h1]
  have hBA : ∀ z, ((treeOf i s (w.withNode x V)).obj z).isSome = true →
      ((treeOf i s ((MW.afterSuperRoot w8 p i (w.next + 4)).withNode x
        (n.toPrev (i - 1)))).obj z).isSome = true := by
    intro z hz
    by_cases h0 : z = x
    · rw [h0]; exact hBx
    by_cases h1 : z = w.next
    · rw [h1, hBf]; rfl
    by_cases h2 : z = w.next + 2
    · rw [h2, hBs]; rfl
    by_cases h4 : z = w.next + 4
    · rw [h4, hBr]; rfl
    rw [hBo z h0 h1 h2 h4, ← hAz z h0]
    exact hz
  have hS : Sound p.M (some x) (treeOf i s (w.withNode x V)) w.top.rootKey C :=
    h.vsound
  rw [← hxr] at hS
  have hsc0 : 0 < sc := Good.tr_split_lo hS.good hAx hsplit hL1
  have hnames : ∀ (m : MNode), (∀ c y, SIS.Tree.Klong.key c y ∈ m.ks →
      ∃ c', Klong.key c' y ∈ ksOf V) → ∀ c y, SIS.Tree.Klong.key c y ∈ m.ks →
      ((treeOf i s ((MW.afterSuperRoot w8 p i (w.next + 4)).withNode x
        (n.toPrev (i - 1)))).obj y).isSome = true :=
    fun m hm c y hy => hBA y (wds_named_some h htx hxreach (hm c y hy))
  have hNf : NodeIs (treeOf i s ((MW.afterSuperRoot w8 p i (w.next + 4)).withNode x
      (n.toPrev (i - 1)))) w.next (wLevel s w x) n.leaf L1 p.M := by
    rw [← hfl, hlev]
    exact ss_nodeIs hBf hlf hwff hszf (hnames f hkf)
  have hNs : NodeIs (treeOf i s ((MW.afterSuperRoot w8 p i (w.next + 4)).withNode x
      (n.toPrev (i - 1)))) (w.next + 2) (wLevel s w x) n.leaf
      (if n.leaf then (sc, y0) :: rest else (0, y0) :: rest) p.M := by
    rw [← hsl, hlev]
    refine ss_nodeIs hBs ?_ hwfs hszs (hnames s2 hks)
    rw [hls, hsl]
    cases n.leaf <;> rfl
  have hNr : NodeIs (treeOf i s ((MW.afterSuperRoot w8 p i (w.next + 4)).withNode x
      (n.toPrev (i - 1)))) (w.next + 4) (wLevel s w x + 1) false
      [(0, w.next), (sc, w.next + 2)] p.M := by
    rw [hlev, ← keyLevel_succ]
    exact ss_nodeIs_root hsc0 (by have := hp.size; omega) hBr (by rw [hBf]; rfl)
      (by rw [hBs]; rfl)
  obtain ⟨hSB, -, hRB⟩ := Sound.spaceSplitRoot hS hAx hsplit hL1 (Or.inr hA0) hA2 hne20.symm hA4
    ⟨hne40, hne42⟩ hNf hNs hNr hBx
    (fun z h0 h1 h2 h4 => by rw [hBo z h0 h1 h2 h4, hAz z h0])
  have hrk10 : ((MW.afterSuperRoot w8 p i (w.next + 4)).withNode x
      (n.toPrev (i - 1))).top.rootKey = w.next + 4 := hrk9
  have hroot10 : (treeOf i s ((MW.afterSuperRoot w8 p i (w.next + 4)).withNode x
      (n.toPrev (i - 1)))).root = some (w.next + 4) := by
    rw [treeOf_withNode i s _ htx9]
    exact hroot9
  refine ⟨ss_pinv hO10.1 (by rw [hrk10]; exact hroot10) (by rw [hrk10]; exact hSB),
    ⟨?_, ?_, ?_, ?_⟩⟩
  · show (MW.afterSuperRoot w8 p i (w.next + 4)).path = w.path
    rw [(afterSuperRoot_fields w8 p i (w.next + 4)).2.2.2.2.2.2.2.1, e8, e7, e6, e5, e4, e3, e2, e1]
    rfl
  · intro y ny hy hnot
    have hyx : y ≠ x := fun e => hnot 0 c0 le_rfl (by rw [e]; exact hon)
    have hylt : y < w.next := h.books.ids.1 y ny hy
    rw [ss_lookup_withNode hyx, (afterSuperRoot_fields w8 p i (w.next + 4)).2.2.1,
      hlk y (Nat.ne_of_lt hylt) (ss_ne_of_lt_add hylt) (ss_ne_of_lt_add hylt)]
    exact hy
  · have h8 : w8.next = w.next + 6 := by
      rw [e8, e7, e6, e5, e4]
      show w3.next + 2 = _
      rw [hn3]
    exact Nat.le_trans (ss_le_add h8) (ss_afterSuperRoot_next w8 p i (w.next + 4))
  · intro z hz
    unfold reachOf at hz ⊢
    rw [hrk10] at hz
    have hW0r : (w.withNode x V).top.rootKey = x := hxr.symm
    rw [hW0r]
    rcases hRB z hz with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · rw [h1]; exact Or.inr (Nat.le_refl _)
    · rw [h1]; exact Or.inr (Nat.le_add_right _ _)
    · rw [h1]; exact Or.inr (Nat.le_add_right _ _)

theorem wds_root_new {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {x : NodeId} {w : MW} {n V last : MNode}
    {C : List (Key × Nat)} {up : NodeId → List (Nat × NodeId) → SIS.Tree.M Unit}
    (hp : ParamsOK p) (hb : Books i base s tp) (h : CasPreD p i base s tp w 0 x n V last C)
    (hcase : p.splitAbove < last.size) (hin : ¬ n.firstTime = some i) :
    WP (SIS.Tree.handleFullWith up 0 x [] last false)
      { p := p, i := i, view := v } w (CasPostD p i base s tp w 0 x V C) := by
  obtain ⟨c0, hon⟩ := h.on
  have htx : w.taken.contains x = false := (h.path.lookup le_rfl hon).choose_spec.2
  obtain ⟨g, hh, hgh, -⟩ := h.books.levels x n h.look htx
  have hc' : (!false && decide (last.size > p.splitAbove)) = true := by
    simpa using hcase
  have hin' : (n.firstTime == some i) = false := by simpa using hin
  unfold SIS.Tree.handleFullWith
  refine ss_wp_step (ss_read _ w) ?_
  refine ss_wp_step (getNode_hit _ h.look) ?_
  refine ss_wp_step (ghOf_hit _ h.look hgh) ?_
  refine ss_wp_step (parentAt_zero _ _) ?_
  dsimp only
  refine ss_wp_step (ss_pure _ _ _) ?_
  simp only [Bool.false_eq_true, ↓reduceIte, hc', hin']
  refine ss_wp_step (ss_modify _ _) ?_
  refine ss_wp_step (newKey_eq _ _ _ _ _ _) ?_
  refine ss_wp_step (newKey_eq _ _ _ _ _ _) ?_
  refine ss_wp_step (ss_setMadeFor _ _ _ _) ?_
  refine ss_wp_step (ss_setMadeFor _ _ _ _) ?_
  refine ss_wp_step (ss_note _ _ _) ?_
  refine ss_wp_step (newKey_eq _ _ _ _ _ _) ?_
  refine ss_wp_step (ss_setMadeFor _ _ _ _) ?_
  generalize hH : SIS.Tree.halves n.leaf i last [] = H
  obtain ⟨f, s2, sc⟩ := H
  dsimp only
  refine ss_wp_step (putNode_eq _ _ _ _) ?_
  refine ss_wp_step (putNode_eq _ _ _ _) ?_
  refine ss_wp_step (putNode_eq _ _ _ _) ?_
  refine ss_wp_step (newSuperRoot_eq v _ h.wtop) ?_
  simp only [Bool.not_false, ↓reduceIte]
  exact wds_root_new_post hp hb h hcase hin hgh hH rfl rfl rfl rfl rfl rfl rfl rfl

/-! ## 7. Under an inner parent: the parent's step -/

/-- The state before the parent's step `up`: if it holds the halves (first and
second) and is otherwise the state before x's step, it meets the parent's
`CasPre`, and the parent's "if" state reaches what A (the map of the state
with x set to V) reaches and the halves, and not x if x was replaced. -/
theorem wds_parent_pre {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top} {d : Nat}
    {x : NodeId} {w : MW} {n V last : MNode} {C : List (Key × Nat)}
    (hb : Books i base s tp) (h : CasPreD p i base s tp w (d + 1) x n V last C)
    (htx : w.taken.contains x = false)
    {k1 : Nat} {cq : Option Nat} {q : NodeId} {nq : MNode}
    (hq1 : w.path[d]? = some (cq, q)) (hq3 : w.nodes.lookup q = some nq)
    (hq4 : w.taken.contains q = false) (hqx : q ≠ x) (hql : nq.leaf = false)
    (hk1 : (k1, x) ∈ live (ksOf nq))
    (hqr : q ∈ reachAt (treeOf i s (w.withNode x V))
      ((treeOf i s (w.withNode x V)).fuel w.top.rootKey) w.top.rootKey)
    (hlq : wLevel s w x + 1 = wLevel s w q)
    (hnx : ∀ e c u, e ≤ d → w.path[e]? = some (c, u) → u ≠ x)
    {f s2 : MNode} {sc : Nat} {L1 rest : List (Nat × NodeId)} {y0 : NodeId}
    (hsplit : live (ksOf V) = L1 ++ (sc, y0) :: rest) (hL1 : L1 ≠ [])
    (hfl : f.leaf = n.leaf) (hsl : s2.leaf = n.leaf) (hlf : live (ksOf f) = L1)
    (hls : live (ksOf s2) = (if n.leaf then sc else 0, y0) :: rest)
    (hwff : klongsWf (ksOf f) = true) (hwfs : klongsWf (ksOf s2) = true)
    (hszf : f.size ≤ p.M) (hszs : s2.size ≤ p.M)
    (hkf : ∀ c y, SIS.Tree.Klong.key c y ∈ f.ks → ∃ c', Klong.key c' y ∈ ksOf V)
    (hks : ∀ c y, SIS.Tree.Klong.key c y ∈ s2.ks → ∃ c', Klong.key c' y ∈ ksOf V)
    {first second : NodeId} {insU : List (Nat × NodeId)} {wU : MW}
    (hOU : SsOk p i base s tp (fun _ => False) wU)
    (hpU : wU.path = w.path) (htopU : wU.top = w.top) (hntU : wU.newTop = w.newTop)
    (hkU : wU.taken = w.taken)
    (hlkU : ∀ y, y ≠ x → y < w.next → wU.nodes.lookup y = w.nodes.lookup y)
    (hwlU : ∀ y, y < w.next → wLevel s wU y = wLevel s w y)
    (hobjU : ∀ z, z ≠ first → z ≠ second → (treeOf i s wU).obj z = (treeOf i s w).obj z)
    (hfU : (treeOf i s wU).obj first = some (.key ⟨wLevel s w x, f.leaf, ksOf f⟩))
    (hsU : (treeOf i s wU).obj second = some (.key ⟨wLevel s w x, s2.leaf, ksOf s2⟩))
    (hfirst : first = x ∨ w.next ≤ first) (hsecond : w.next ≤ second) (hfs : first ≠ second)
    (hins : (insU = [(sc, second)] ∧ first = x) ∨ insU = [(k1, first), (sc, second)]) :
    CasPre p i base s tp wU d q nq insU C ∧
      (first ≠ x → x ∉ reachOf i s (wU.withNode q (addAll i nq insU))) ∧
      (∀ z ∈ reachOf i s (wU.withNode q (addAll i nq insU)),
        z ∈ reachOf i s (w.withNode x V) ∨ z = first ∨ z = second) ∧
      x ∈ reachOf i s (w.withNode x V) := by
  obtain ⟨-, hAx, hAz⟩ := wds_start h htx
  have hlook := h.look
  have hxlt : x < w.next := h.books.ids.1 x n hlook
  have hqlt : q < w.next := h.books.ids.1 q nq hq3
  have hAq : (treeOf i s (w.withNode x V)).obj q =
      some (.key ⟨wLevel s w q, nq.leaf, ksOf nq⟩) := by
    rw [hAz q hqx, treeOf_obj_overlay i s hq3 hq4]
  -- q's node: well formed, of size M at most
  have hnq := h.vsound.nodes q hqr _ hAq
  simp only [ss_ite_neg (show ¬ some x = some q from fun e => hqx (Option.some.inj e).symm)]
    at hnq
  have hnq' := hnq
  simp only [nodeOk, Bool.and_eq_true, decide_eq_true_eq] at hnq'
  obtain ⟨⟨hnqs, hnqwf⟩, -⟩ := hnq'
  rw [ksOf_length] at hnqs
  -- x is reached in A, and a kid of q there
  obtain ⟨loq, hiq, hgq⟩ := h.vsound.good.tr_reach_good _ q hqr _ hAq
  obtain ⟨pre, post, he⟩ := List.append_of_mem hk1
  obtain ⟨hpre, -, hpp⟩ := live_split he
  have hkx := (hgq.tr_kids hAq _ (bounds_mem hiq he)).2.2.2 (by simp [hql])
  obtain ⟨mx, hmx, -, -, hgx⟩ := hkx
  simp only [hql, Bool.false_eq_true, ite_false] at hgx
  have hxreach : x ∈ reachAt (treeOf i s (w.withNode x V))
      ((treeOf i s (w.withNode x V)).fuel w.top.rootKey) w.top.rootKey :=
    h.vsound.good.tr_closed hqr (g := wLevel s w q + 1) (tc_kid hAq hk1 (tc_self _ _ x))
  have hsc1 : max loq k1 < sc := Good.tr_split_lo hgx hAx hsplit hL1
  have hscpost : ∀ b ∈ post, sc < b.1 :=
    tr_lt_post hpp (Good.tr_hi hgx hAx (y := y0) (by rw [hsplit]; simp))
  -- the klongs for the parent
  have hlenU : insU.length = 1 ∨ insU.length = 2 := by
    rcases hins with ⟨rfl, -⟩ | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hmemU : ∀ c y, (c, y) ∈ insU → y = first ∨ y = second := by
    intro c y hm
    rcases hins with ⟨rfl, -⟩ | rfl
    · simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
      exact Or.inr hm.2
    · simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
      rcases hm with hm | hm
      · exact Or.inl hm.2
      · exact Or.inr hm.2
  have hliveU : insU.foldl (fun m cy => insertCv cy.1 cy.2 m) (live (ksOf nq)) =
      insertCv sc second (insertCv k1 first (live (ksOf nq))) := by
    rcases hins with ⟨rfl, rfl⟩ | rfl
    · simp only [List.foldl_cons, List.foldl_nil]
      rw [ss_insertCv_mem (live_sorted _) hk1]
    · rfl
  -- the state at q
  have hkq : wU.taken.contains q = false := by rw [hkU]; exact hq4
  have hlkq : wU.nodes.lookup q = some nq := by rw [hlkU q hqx hqlt]; exact hq3
  have hwq : wLevel s wU q = wLevel s w q := hwlU q hqlt
  have hqf : q ≠ first := by
    rcases hfirst with e | e
    · rw [e]; exact hqx
    · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hqlt e)
  have hqs : q ≠ second := Nat.ne_of_lt (Nat.lt_of_lt_of_le hqlt hsecond)
  obtain ⟨tq, rq, hrq⟩ := (hOU.toBooks (fun _ h => h)).timeFirst q nq hlkq hkq
  obtain ⟨rq', hrq'⟩ := addAll_first (i := i) hrq insU
  have hOq := ssOk_withNode (E' := fun _ => False) hOU hlkq hkq (addAll_leaf i nq insU)
    (Or.inl (by rw [hrq', hrq]; rfl))
    (fun t ht => addAll_timesLe (ss_timesLe (hOU.books.times q nq hlkq)) insU t (ss_time_ksOf ht))
    (fun n0 hs0 => addAll_ext (prim_timesBefore (hb.times q n0 hs0))
      (frame_overlay_ext hOU.frame hlkq hkq hs0).2.2 insU)
    (by
      intro hl c y hy
      rcases (addAll_key_mem insU nq).mp (ss_key_ksOf hy) with h1 | h1
      · obtain ⟨-, -, hb3⟩ := hOU.bal q _ (treeOf_obj_overlay i s hlkq hkq)
        exact hb3 (by rw [addAll_leaf] at hl; exact hl) c y h1
      · rcases hmemU c y h1 with e | e
        · rw [e]
          exact ⟨_, hfU, by rw [hwq]; exact hlq⟩
        · rw [e]
          exact ⟨_, hsU, by rw [hwq]; exact hlq⟩)
    (by rw [hrq']; simp) (fun _ _ h => h)
  -- the parent's "if" state's map B
  have hBq : (treeOf i s (wU.withNode q (addAll i nq insU))).obj q =
      some (.key ⟨wLevel s w q, nq.leaf, ksOf (addAll i nq insU)⟩) := by
    rw [hOq.2, ss_ite_pos rfl, addAll_leaf, hwq]
  have hBo : ∀ z, z ≠ q →
      (treeOf i s (wU.withNode q (addAll i nq insU))).obj z = (treeOf i s wU).obj z := by
    intro z hz
    rw [hOq.2, ss_ite_neg hz]
  have hBx : ((treeOf i s (wU.withNode q (addAll i nq insU))).obj x).isSome = true := by
    rw [hBo x hqx.symm]
    by_cases hxf : x = first
    · rw [hxf, hfU]; rfl
    · have hxs : x ≠ second := Nat.ne_of_lt (Nat.lt_of_lt_of_le hxlt hsecond)
      rw [hobjU x hxf hxs, treeOf_obj_overlay i s hlook htx]; rfl
  have hsame : ∀ z, z ≠ x → z ≠ first → z ≠ second → z ≠ q →
      (treeOf i s (wU.withNode q (addAll i nq insU))).obj z =
        (treeOf i s (w.withNode x V)).obj z := by
    intro z h0 h1 h2 h3
    rw [hBo z h3, hobjU z h1 h2, hAz z h0]
  have hBA : ∀ z, ((treeOf i s (w.withNode x V)).obj z).isSome = true →
      ((treeOf i s (wU.withNode q (addAll i nq insU))).obj z).isSome = true := by
    intro z hz
    by_cases h3 : z = q
    · rw [h3, hBq]; rfl
    by_cases h1 : z = first
    · rw [h1, hBo _ hqf.symm, hfU]; rfl
    by_cases h2 : z = second
    · rw [h2, hBo _ hqs.symm, hsU]; rfl
    by_cases h0 : z = x
    · rw [h0]; exact hBx
    rw [hsame z h0 h1 h2 h3]
    exact hz
  have hnames : ∀ (m : MNode), (∀ c y, SIS.Tree.Klong.key c y ∈ m.ks →
      ∃ c', Klong.key c' y ∈ ksOf V) → ∀ c y, SIS.Tree.Klong.key c y ∈ m.ks →
      ((treeOf i s (wU.withNode q (addAll i nq insU))).obj y).isSome = true :=
    fun m hm c y hy => hBA y (wds_named_some h htx hxreach (hm c y hy))
  have hNf : NodeIs (treeOf i s (wU.withNode q (addAll i nq insU))) first (wLevel s w x) n.leaf
      L1 p.M := by
    rw [← hfl]
    exact ss_nodeIs (by rw [hBo _ hqf.symm]; exact hfU) hlf hwff hszf (hnames f hkf)
  have hNs : NodeIs (treeOf i s (wU.withNode q (addAll i nq insU))) second (wLevel s w x) n.leaf
      (if n.leaf then (sc, y0) :: rest else (0, y0) :: rest) p.M := by
    rw [← hsl]
    refine ss_nodeIs (by rw [hBo _ hqs.symm]; exact hsU) ?_ hwfs hszs (hnames s2 hks)
    rw [hls, hsl]
    cases n.leaf <;> rfl
  have hNq : NodeIs (treeOf i s (wU.withNode q (addAll i nq insU))) q (wLevel s w q) false
      (insertCv sc second (insertCv k1 first (live (ksOf nq)))) (bnd p.M (some q) q) := by
    rw [← hql, ← addAll_leaf i nq insU, ← hliveU, ← addAll_live hnqwf]
    refine ss_nodeIs (by rw [hBq, addAll_leaf]) rfl (addAll_wf hnqwf insU) ?_ ?_
    · simp only [bnd, ite_true]
      have := addAll_size i nq insU
      rcases hlenU with e | e <;> rw [e] at this <;> omega
    · intro c y hy
      rcases (addAll_key_mem insU nq).mp (ss_key_ksOf hy) with h1 | h1
      · exact hBA y (ss_nodeOk_names hnq h1)
      · rcases hmemU c y h1 with e | e
        · rw [e, hBo _ hqf.symm, hfU]; rfl
        · rw [e, hBo _ hqs.symm, hsU]; rfl
  have hfirstA : first = x ∨ (treeOf i s (w.withNode x V)).obj first = none := by
    rcases hfirst with e | e
    · exact Or.inl e
    · exact Or.inr (wds_fresh hb h htx e)
  obtain ⟨hSB, hxB, hRB⟩ := Sound.spaceSplit (ex' := some q) h.vsound hqr hAq hql hk1 hAx hsplit
    hL1 hfirstA (wds_fresh hb h htx hsecond) hfs hNf hNs hNq hBx hsame
  have hrkq : (wU.withNode q (addAll i nq insU)).top.rootKey = w.top.rootKey := by
    show wU.top.rootKey = _
    rw [htopU]
  refine ⟨⟨hlkq, ⟨cq, by rw [hpU]; exact hq1⟩, ?_, ?_, hOU.toBooks (fun _ h => h), hnqwf, hnqs,
    hlenU, ?_, ?_⟩, ?_, ?_, ?_⟩
  · -- the path
    refine ⟨by rw [hpU, htopU]; exact h.path.root, fun e he => ?_, fun e he => ?_⟩
    · obtain ⟨c, u, n', h1, h2, h3⟩ := h.path.nodes e (by omega)
      have hux := hnx e c u he h1
      have hult : u < w.next := h.books.ids.1 u n' h2
      exact ⟨c, u, n', by rw [hpU]; exact h1, by rw [hlkU u hux hult]; exact h2,
        by rw [hkU]; exact h3⟩
    · obtain ⟨c0, u, c, y, nu, h1, h2, h3, h4⟩ := h.path.links e (by omega)
      have hux := hnx e c0 u (by omega) h1
      obtain ⟨n', hn', -⟩ := h.path.lookup (Nat.le_of_lt (by omega : e < d + 1)) h1
      have hult : u < w.next := h.books.ids.1 u n' hn'
      have huf : u ≠ first := by
        rcases hfirst with e' | e'
        · rw [e']; exact hux
        · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hult e')
      have hus : u ≠ second := Nat.ne_of_lt (Nat.lt_of_lt_of_le hult hsecond)
      exact ⟨c0, u, c, y, nu, by rw [hpU]; exact h1, by rw [hpU]; exact h2,
        by rw [hobjU u huf hus]; exact h3, h4⟩
  · -- the path is inner
    intro e c u nu he h1 h2
    rw [hpU] at h1
    obtain ⟨n', hn', ht'⟩ := h.path.lookup (Nat.le_of_lt (by omega : e < d + 1)) h1
    have hux := hnx e c u (by omega) h1
    have hult : u < w.next := h.books.ids.1 u n' hn'
    rw [hlkU u hux hult, hn'] at h2
    rw [← Option.some.inj h2]
    exact h.inner e c u n' (by omega) h1 hn'
  · -- two klongs: the halves of x
    intro a y1 b y2 heq
    rcases hins with ⟨rfl, -⟩ | rfl
    · simp at heq
    · simp only [List.cons.injEq, Prod.mk.injEq, and_true] at heq
      obtain ⟨⟨rfl, -⟩, rfl, -⟩ := heq
      refine ⟨by omega, ⟨x, hk1⟩, fun c' y' hm hlt => ?_⟩
      rw [he] at hm
      rcases List.mem_append.mp hm with hm | hm
      · have := hpre _ hm
        simp only at this
        omega
      · rcases List.mem_cons.mp hm with hm | hm
        · cases hm
          omega
        · exact hscpost _ hm
  · -- the parent's "if" state
    refine ⟨?_, by rw [hrkq]; exact hSB, hOq.1.frame, hOq.1.top, hOq.1.bal,
      hOq.1.toBooks (fun _ h => h)⟩
    rw [hrkq, treeOf_withNode i s _ hkq]
    have e1 : (treeOf i s wU).root = (treeOf i s w).root := by
      simp only [Tree.root, treeOf, hntU, htopU]
    exact e1.trans h.wroot
  · intro hfx
    unfold reachOf
    rw [hrkq]
    exact hxB hfx
  · intro z hz
    unfold reachOf at hz ⊢
    rw [hrkq] at hz
    exact hRB z hz
  · exact hxreach

/-! ## 8. Under an inner parent: x made by the transaction -/

/-- x keeps the first half in place, a new node the second, and the parent
gets the second half's klong. -/
theorem wds_parent_inPlace_post {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {d : Nat} {x : NodeId} {w : MW} {n V last : MNode}
    {C : List (Key × Nat)} {up : NodeId → List (Nat × NodeId) → SIS.Tree.M Unit}
    (hp : ParamsOK p) (hb : Books i base s tp) (h : CasPreD p i base s tp w (d + 1) x n V last C)
    (hup : UpOk p i base s tp v up d)
    (hcase : p.splitAbove < last.size) (hin : n.firstTime = some i)
    {g hh : Nat} (hgh : w.gh.lookup x = some (g, hh)) {cq : Option Nat} {q : NodeId}
    {nq : MNode} (hq1 : w.path[d]? = some (cq, q)) (hq3 : w.nodes.lookup q = some nq)
    {f s2 : MNode} {sc : Nat} (hH : SIS.Tree.halves n.leaf i last [] = (f, s2, sc))
    {w1 w2 w3 w4 w5 : MW}
    (e1 : w1 = (ssSp w).afterNewKey p g hh n.leaf [])
    (e2 : w2 = ssMF w1 w.next (w1.madeFor.lookup x))
    (e3 : w3 = w2.withNode x f) (e4 : w4 = w3.withNode w.next s2)
    (e5 : w5 = ssNote w4 "split.space1.inplace") :
    WP (up q [(sc, w.next)] >>= fun _ => pure ()) { p := p, i := i, view := v } w5
      (CasPostD p i base s tp w (d + 1) x V C) := by
  obtain ⟨c0, hon⟩ := h.on
  have hlook := h.look
  have htx : w.taken.contains x = false := (h.path.lookup le_rfl hon).choose_spec.2
  obtain ⟨g', hh', hgh', hgG, hhH, hlev, hleafh⟩ := h.books.levels x n hlook htx
  rw [hgh] at hgh'
  cases hgh'
  obtain ⟨k1, cq', q', nq', hq1', hon', hq3', hq4, hqx, hql, hk1, hqr, hlq, hnx, hxA⟩ :=
    wds_path h hon htx
  rw [hq1] at hq1'
  cases hq1'
  rw [hq3] at hq3'
  cases hq3'
  obtain ⟨hO, hAx, hAz⟩ := wds_start h htx
  obtain ⟨hVf, hVs⟩ := wds_vfacts h htx hxA
  obtain ⟨L1, y0, rest, hsplit, hL1, hfl, hsl, hlf, hls, hwff, hwfs, ⟨rf, hf1⟩, ⟨rs, hs1⟩, htf,
    hts, hszf, hszs, hkf, hks⟩ :=
    wds_halves hp hVf hVs h.lastKs hcase hH
  have hsx : s.obj x = none := by
    have := h.books.first x n hlook htx
    rw [hin] at this
    cases e : s.obj x with
    | none => rfl
    | some o => rw [e] at this; exact absurd rfl (this.mp rfl)
  obtain ⟨-, hs0, hn0, -, ht0, hm0⟩ := treeOf_fresh hb h.books (Nat.le_refl w.next)
  have hxlt : x < w.next := h.books.ids.1 x n hlook
  -- the states
  have hlk1 : ∀ y, y ≠ w.next → w1.nodes.lookup y = w.nodes.lookup y := by
    intro y hy
    rw [e1]
    exact prim_lookup_append_ne _ _ hy
  have hlk1n : w1.nodes.lookup w.next = some ⟨n.leaf, []⟩ := by
    rw [e1]
    exact prim_lookup_append_self _ _ hn0
  have hwl1 : ∀ y, y ≠ w.next → wLevel s w1 y = wLevel s w y := by
    intro y hy
    rw [e1]
    exact prim_wLevel_afterNewKey hy
  have hwl1n : wLevel s w1 w.next = p.keyLevel g hh := by
    rw [e1]
    exact ss_wLevel_newKey p g hh n.leaf [] hs0 hm0
  have hO1 : SsOk p i base s tp (fun z => z = w.next) w1 ∧
      ∀ z, (treeOf i s w1).obj z = if z = w.next then some (.key ⟨p.keyLevel g hh, n.leaf, []⟩)
        else (treeOf i s w).obj z := by
    rw [e1]
    exact ssOk_newKey hb (hO.congr (w' := ssSp w) rfl rfl rfl rfl rfl rfl rfl rfl rfl) hgG hhH
      hleafh (Or.inl rfl) (by simp) (by simp) (by
        intro z hz
        rcases hz with ⟨hz, -⟩ | hz
        · exact hz
        · exact hz.elim)
  have hO2 : SsOk p i base s tp (fun z => z = w.next) w2 := by
    rw [e2]
    exact hO1.1.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hT2 : treeOf i s w2 = treeOf i s w1 := by rw [e2]; rfl
  have hk2 : w2.taken = w.taken := by rw [e2, e1]; rfl
  have hN2 : w2.nodes = w1.nodes := by rw [e2]; rfl
  have hM2 : w2.made = w1.made := by rw [e2]; rfl
  have hwl2 : wLevel s w2 = wLevel s w1 := by unfold wLevel; rw [hM2]
  have hfst : f.ks.head? = n.ks.head? := by
    obtain ⟨t, r, hr⟩ := h.books.timeFirst x n hlook htx
    have := prim_firstTime_of hr
    rw [hin] at this
    cases this
    rw [hf1, hr]
    rfl
  have hold : ∀ y, y ≠ x → y < w.next → (treeOf i s w2).obj y = (treeOf i s w).obj y := by
    intro y hyx hy
    rw [hT2, hO1.2 y, ss_ite_neg (Nat.ne_of_lt hy)]
  have hwx : wLevel s w2 x = wLevel s w x := by rw [hwl2, hwl1 x (Nat.ne_of_lt hxlt)]
  have hO3 : SsOk p i base s tp (fun z => z = w.next) w3 ∧
      ∀ z, (treeOf i s w3).obj z = if z = x then some (.key ⟨wLevel s w x, f.leaf, ksOf f⟩)
        else (treeOf i s w2).obj z := by
    rw [e3, ← hwx]
    refine ssOk_withNode hO2 (by rw [hN2, hlk1 x (Nat.ne_of_lt hxlt)]; exact hlook)
      (by rw [hk2]; exact htx) hfl
      (Or.inl hfst) htf (fun n0 hn0 => by rw [hsx] at hn0; cases hn0) ?_
      (by rw [hf1]; simp) (fun z _ hz => hz)
    intro hl c y hy
    obtain ⟨m', hm1, hm2, hyx, hylt⟩ := wds_named hb h htx (by rw [← hfl]; exact hl) (hkf c y hy)
    exact ⟨m', by rw [hold y hyx hylt]; exact hm1, by rw [hwx]; exact hm2⟩
  have hN3 : ∀ y, y ≠ x → w3.nodes.lookup y = w2.nodes.lookup y := by
    intro y hy
    rw [e3]
    exact lookup_upsert_ne _ _ hy
  have hwl3 : wLevel s w3 = wLevel s w1 := by rw [e3, ← hwl2]; rfl
  have hO4 : SsOk p i base s tp (fun _ => False) w4 ∧
      ∀ z, (treeOf i s w4).obj z = if z = w.next then
        some (.key ⟨p.keyLevel g hh, s2.leaf, ksOf s2⟩) else (treeOf i s w3).obj z := by
    have hwn : wLevel s w3 w.next = p.keyLevel g hh := by rw [hwl3, hwl1n]
    rw [e4, ← hwn]
    refine ssOk_withNode hO3.1 (m := ⟨n.leaf, []⟩)
      (by rw [hN3 _ (Nat.ne_of_gt hxlt), hN2]; exact hlk1n)
      (by rw [show w3.taken = w2.taken by rw [e3]; rfl, hk2]; exact ht0) hsl
      (Or.inr ⟨rfl, rs, hs1⟩) hts
      (fun n0 hn0 => by rw [hs0] at hn0; cases hn0) ?_ (by rw [hs1]; simp)
      (fun z hz hz' => hz hz')
    intro hl c y hy
    obtain ⟨m', hm1, hm2, hyx, hylt⟩ := wds_named hb h htx (by rw [← hsl]; exact hl) (hks c y hy)
    refine ⟨m', ?_, by rw [hwn, ← hlev]; exact hm2⟩
    rw [hO3.2 y, ss_ite_neg hyx, hold y hyx hylt]
    exact hm1
  have hO5 : SsOk p i base s tp (fun _ => False) w5 := by
    rw [e5]
    exact hO4.1.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hT5 : treeOf i s w5 = treeOf i s w4 := by rw [e5]; rfl
  have hn5 : w5.next = w.next + 2 := by rw [e5, e4, e3, e2, e1]; rfl
  obtain ⟨hpre, -, hreach, hxr⟩ := wds_parent_pre hb h htx hq1 hq3 hq4 hqx hql hk1 hqr hlq hnx
    hsplit hL1 hfl hsl hlf hls hwff hwfs hszf hszs hkf hks (first := x) (second := w.next)
    (insU := [(sc, w.next)]) hO5
    (by rw [e5, e4, e3, e2, e1]; rfl) (by rw [e5, e4, e3, e2, e1]; rfl)
    (by rw [e5, e4, e3, e2, e1]; rfl) (by rw [e5, e4, e3, e2, e1]; rfl)
    (by
      intro y hyx hy
      rw [e5, e4]
      show (w3.withNode w.next s2).nodes.lookup y = _
      rw [ss_lookup_withNode (Nat.ne_of_lt hy), hN3 y hyx, hN2, hlk1 y (Nat.ne_of_lt hy)])
    (by
      intro y hy
      rw [show wLevel s w5 = wLevel s w1 by rw [e5, e4, ← hwl3]; rfl]
      exact hwl1 y (Nat.ne_of_lt hy))
    (by
      intro z h1 h2
      rw [hT5, hO4.2, ss_ite_neg h2, hO3.2, ss_ite_neg h1, hT2, hO1.2, ss_ite_neg h2])
    (by rw [hT5, hO4.2, ss_ite_neg (Nat.ne_of_lt hxlt), hO3.2, ss_ite_pos rfl])
    (by rw [hT5, hO4.2, ss_ite_pos rfl, hlev])
    (Or.inl rfl) (Nat.le_refl _) (Nat.ne_of_lt hxlt) (Or.inl ⟨rfl, rfl⟩)
  rw [wp_bind]
  refine WP.mono (hup q _ w5 nq C hpre) (fun _ w' hpost => (wp_pure _ _ _ _).mpr ?_)
  intro hout
  obtain ⟨hPI, hCP⟩ := hpost hout
  have hpU : w5.path = w.path := by rw [e5, e4, e3, e2, e1]; rfl
  refine ⟨hPI, hCP.path.trans hpU, ?_, ?_, ?_⟩
  · intro y ny hy hnot
    have hyx : y ≠ x := fun e => hnot (d + 1) c0 le_rfl (by rw [e]; exact hon)
    have hylt : y < w.next := h.books.ids.1 y ny hy
    refine hCP.off y ny ?_ (fun d' c hd' => by rw [hpU]; exact hnot d' c (by omega))
    rw [e5, e4]
    show (w3.withNode w.next s2).nodes.lookup y = _
    rw [ss_lookup_withNode (Nat.ne_of_lt hylt), hN3 y hyx, hN2, hlk1 y (Nat.ne_of_lt hylt)]
    exact hy
  · exact Nat.le_trans (ss_le_add hn5) hCP.next
  · intro z hz
    rcases hCP.reach z hz with h1 | h1
    · rcases hreach z h1 with h2 | h2 | h2
      · exact Or.inl h2
      · rw [h2]; exact Or.inl hxr
      · rw [h2]; exact Or.inr (Nat.le_refl _)
    · exact Or.inr (Nat.le_trans (ss_le_add hn5) h1)

theorem wds_parent_inPlace {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {d : Nat} {x : NodeId} {w : MW} {n V last : MNode}
    {C : List (Key × Nat)} {up : NodeId → List (Nat × NodeId) → SIS.Tree.M Unit}
    (hp : ParamsOK p) (hb : Books i base s tp) (h : CasPreD p i base s tp w (d + 1) x n V last C)
    (hup : UpOk p i base s tp v up d)
    (hcase : p.splitAbove < last.size) (hin : n.firstTime = some i) :
    WP (SIS.Tree.handleFullWith up (d + 1) x [] last false)
      { p := p, i := i, view := v } w (CasPostD p i base s tp w (d + 1) x V C) := by
  obtain ⟨c0, hon⟩ := h.on
  have htx : w.taken.contains x = false := (h.path.lookup le_rfl hon).choose_spec.2
  obtain ⟨g, hh, hgh, -⟩ := h.books.levels x n h.look htx
  obtain ⟨k1, cq, q, nq, hq1, -, hq3, -, -, hql, -⟩ := wds_path h hon htx
  have hc' : (!false && decide (last.size > p.splitAbove)) = true := by
    simpa using hcase
  unfold SIS.Tree.handleFullWith
  refine ss_wp_step (ss_read _ w) ?_
  refine ss_wp_step (getNode_hit _ h.look) ?_
  refine ss_wp_step (ghOf_hit _ h.look hgh) ?_
  refine ss_wp_step (parentAt_succ _ hq1) ?_
  dsimp only
  refine ss_wp_step (getNode_hit _ hq3) ?_
  refine ss_wp_step (ss_pure _ _ _) ?_
  simp only [Bool.false_eq_true, ↓reduceIte, hc', hin, beq_self_eq_true, hql]
  refine ss_wp_step (ss_modify _ _) ?_
  refine ss_wp_step (newKey_eq _ _ _ _ _ _) ?_
  refine ss_wp_step (replacedBy_eq _ _ _) ?_
  refine ss_wp_step (ss_setMadeFor _ _ _ _) ?_
  generalize hH : SIS.Tree.halves n.leaf i last [] = H
  obtain ⟨f, s2, sc⟩ := H
  dsimp only
  refine ss_wp_step (putNode_eq _ _ _ _) ?_
  refine ss_wp_step (putNode_eq _ _ _ _) ?_
  refine ss_wp_step (ss_note _ _ _) ?_
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  exact wds_parent_inPlace_post hp hb h hup hcase hin hgh hq1 hq3 hH rfl rfl rfl rfl rfl

/-! ## 9. Under an inner parent: x from before the transaction -/

/-- Two new nodes hold the halves, the parent gets a klong for each, and x is
cut back to before the transaction. -/
theorem wds_parent_new_post {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {d : Nat} {x : NodeId} {w : MW} {n V last : MNode}
    {C : List (Key × Nat)} {up : NodeId → List (Nat × NodeId) → SIS.Tree.M Unit}
    (hp : ParamsOK p) (hb : Books i base s tp) (h : CasPreD p i base s tp w (d + 1) x n V last C)
    (hup : UpOk p i base s tp v up d)
    (hcase : p.splitAbove < last.size) (hin : ¬ n.firstTime = some i)
    {g hh : Nat} (hgh : w.gh.lookup x = some (g, hh)) {cq : Option Nat} {q : NodeId}
    {nq : MNode} {k1 : Nat} (hq1 : w.path[d]? = some (cq, q)) (hq3 : w.nodes.lookup q = some nq)
    (hon' : w.path[d + 1]? = some (some k1, x))
    {f s2 : MNode} {sc : Nat} (hH : SIS.Tree.halves n.leaf i last [] = (f, s2, sc))
    {w1 w2 w3 w4 w5 w6 : MW}
    (e1 : w1 = (ssSp w).afterNewKey p g hh n.leaf [])
    (e2 : w2 = w1.afterNewKey p g hh n.leaf [])
    (e3 : w3 = ssMF (ssMF w2 w.next (some x)) (w.next + 2) (some x))
    (e4 : w4 = ssNote w3 "split.space1")
    (e5 : w5 = w4.withNode w.next f) (e6 : w6 = w5.withNode (w.next + 2) s2) :
    WP (up q [(k1, w.next), (sc, w.next + 2)] >>= fun _ =>
        SIS.Tree.getNode x >>= fun n' => SIS.Tree.putNode x (n'.toPrev (i - 1)))
      { p := p, i := i, view := v } w6 (CasPostD p i base s tp w (d + 1) x V C) := by
  have hlook := h.look
  have htx : w.taken.contains x = false := (h.path.lookup le_rfl hon').choose_spec.2
  obtain ⟨g', hh', hgh', hgG, hhH, hlev, hleafh⟩ := h.books.levels x n hlook htx
  rw [hgh] at hgh'
  cases hgh'
  obtain ⟨k1', cq', q', nq', hq1', hon'', hq3', hq4, hqx, hql, hk1, hqr, hlq, hnx, hxA⟩ :=
    wds_path h hon' htx
  rw [hq1] at hq1'
  cases hq1'
  rw [hq3] at hq3'
  cases hq3'
  rw [hon'] at hon''
  cases hon''
  obtain ⟨hO, hAx, hAz⟩ := wds_start h htx
  obtain ⟨hVf, hVs⟩ := wds_vfacts h htx hxA
  obtain ⟨L1, y0, rest, hsplit, hL1, hfl, hsl, hlf, hls, hwff, hwfs, ⟨rf, hf1⟩, ⟨rs, hs1⟩, htf,
    hts, hszf, hszs, hkf, hks⟩ :=
    wds_halves hp hVf hVs h.lastKs hcase hH
  obtain ⟨t0, r0, hr0⟩ := h.books.timeFirst x n hlook htx
  have ht0i : t0 ≤ i - 1 := by
    have h1 : @LE.le Nat _ t0 i :=
      h.books.times x n hlook t0 (by rw [hr0]; exact List.mem_cons_self)
    have h2 : t0 ≠ i := fun e => hin (by rw [prim_firstTime_of hr0, e])
    have h3 : @Ne Nat t0 i := h2
    omega
  obtain ⟨-, hs0, hn0, -, ht0, hm0⟩ := treeOf_fresh hb h.books (Nat.le_refl w.next)
  have hxlt : x < w.next := h.books.ids.1 x n hlook
  have hn1 : w1.next = w.next + 2 := by rw [e1]; rfl
  have hne20 : w.next + 2 ≠ w.next := (ss_ne_add (by decide)).symm
  -- the steps
  have hO1 : SsOk p i base s tp (fun z => z = w.next) w1 ∧
      ∀ z, (treeOf i s w1).obj z = if z = w.next then some (.key ⟨p.keyLevel g hh, n.leaf, []⟩)
        else (treeOf i s w).obj z := by
    rw [e1]
    exact ssOk_newKey hb (hO.congr (w' := ssSp w) rfl rfl rfl rfl rfl rfl rfl rfl rfl) hgG hhH
      hleafh (Or.inl rfl) (by simp) (by simp) (by
        intro z hz
        rcases hz with ⟨hz, -⟩ | hz
        · exact hz
        · exact hz.elim)
  have hfr1 := treeOf_freshE hb hO1.1.books (Nat.le_refl w1.next)
  rw [hn1] at hfr1
  obtain ⟨-, hs2, hn2', -, ht2, hm2⟩ := hfr1
  have hO2 : SsOk p i base s tp (fun z => z = w.next + 2 ∨ z = w.next) w2 ∧
      ∀ z, (treeOf i s w2).obj z = if z = w.next + 2 then
        some (.key ⟨p.keyLevel g hh, n.leaf, []⟩) else (treeOf i s w1).obj z := by
    rw [e2, ← hn1]
    exact ssOk_newKey hb hO1.1 hgG hhH hleafh (Or.inl rfl) (by simp) (by simp) (by
        intro z hz
        rcases hz with ⟨hz, -⟩ | hz
        · exact Or.inl hz
        · exact Or.inr hz)
  have hO4 : SsOk p i base s tp (fun z => z = w.next + 2 ∨ z = w.next) w4 := by
    rw [e4, e3]
    exact hO2.1.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hT4 : treeOf i s w4 = treeOf i s w2 := by rw [e4, e3]; rfl
  have hk4 : w4.taken = w.taken := by rw [e4, e3, e2, e1]; rfl
  have hN4 : w4.nodes = w2.nodes := by rw [e4, e3]; rfl
  have hM4 : w4.made = w2.made := by rw [e4, e3]; rfl
  have hwl4 : wLevel s w4 = wLevel s w2 := by unfold wLevel; rw [hM4]
  have hwl0 : wLevel s w4 w.next = p.keyLevel g hh := by
    rw [hwl4, e2, prim_wLevel_afterNewKey (w := w1) (by rw [hn1]; exact hne20.symm), e1]
    exact ss_wLevel_newKey p g hh n.leaf [] hs0 hm0
  have hwl2 : wLevel s w4 (w.next + 2) = p.keyLevel g hh := by
    rw [hwl4, e2, ← hn1]
    exact ss_wLevel_newKey p g hh n.leaf [] (by rw [hn1]; exact hs2) (by rw [hn1]; exact hm2)
  have hwlo : ∀ y, y < w.next → wLevel s w4 y = wLevel s w y := by
    intro y hy
    rw [hwl4, e2, prim_wLevel_afterNewKey (w := w1) (by rw [hn1]; exact ss_ne_of_lt_add hy), e1]
    exact prim_wLevel_afterNewKey (Nat.ne_of_lt hy)
  have hlk4 : ∀ y, y ≠ w.next → y ≠ w.next + 2 → w4.nodes.lookup y = w.nodes.lookup y := by
    intro y h1 h2
    rw [hN4, e2, ss_lookup_newKey (w := w1) (by rw [hn1]; exact h2), e1,
      ss_lookup_newKey (w := ssSp w) h1]
    rfl
  have hold4 : ∀ y, y < w.next → (treeOf i s w4).obj y = (treeOf i s w).obj y := by
    intro y hy
    rw [hT4, hO2.2, ss_ite_neg (ss_ne_of_lt_add hy), hO1.2, ss_ite_neg (Nat.ne_of_lt hy)]
  have hO5 : SsOk p i base s tp (fun z => z = w.next + 2) w5 ∧
      ∀ z, (treeOf i s w5).obj z = if z = w.next then
        some (.key ⟨p.keyLevel g hh, f.leaf, ksOf f⟩) else (treeOf i s w4).obj z := by
    rw [e5, ← hwl0]
    refine ssOk_withNode hO4 (m := ⟨n.leaf, []⟩)
      (by rw [hN4, e2, ss_lookup_newKey (w := w1) (by rw [hn1]; exact hne20.symm), e1]
          exact prim_lookup_append_self _ _ hn0)
      (by rw [hk4]; exact ht0) hfl (Or.inr ⟨rfl, rf, hf1⟩) htf
      (fun n0 hn0' => by rw [hs0] at hn0'; cases hn0') ?_ (by rw [hf1]; simp) ?_
    · intro hl c y hy
      obtain ⟨m', hm1, hm2, hyx, hylt⟩ := wds_named hb h htx (by rw [← hfl]; exact hl)
        (hkf c y hy)
      exact ⟨m', by rw [hold4 y hylt]; exact hm1, by rw [hwl0, ← hlev]; exact hm2⟩
    · intro z hz hz'
      rcases hz' with hz' | hz'
      · exact hz'
      · exact absurd hz' hz
  have hO6 : SsOk p i base s tp (fun _ => False) w6 ∧
      ∀ z, (treeOf i s w6).obj z = if z = w.next + 2 then
        some (.key ⟨p.keyLevel g hh, s2.leaf, ksOf s2⟩) else (treeOf i s w5).obj z := by
    have hwl5 : wLevel s w5 (w.next + 2) = p.keyLevel g hh := by rw [e5]; exact hwl2
    rw [e6, ← hwl5]
    refine ssOk_withNode hO5.1 (m := ⟨n.leaf, []⟩) ?_
      (by
        rw [e5]; show w4.taken.contains _ = false
        rw [hk4, show w.taken = w1.taken by rw [e1]; rfl]; exact ht2) hsl
      (Or.inr ⟨rfl, rs, hs1⟩) hts (fun n0 hn0' => by rw [hs2] at hn0'; cases hn0') ?_
      (by rw [hs1]; simp) (fun _ hz h => hz h)
    · rw [e5, ss_lookup_withNode hne20, hN4, e2, ← hn1]
      exact prim_lookup_append_self _ _ (by rw [hn1]; exact hn2')
    · intro hl c y hy
      obtain ⟨m', hm1, hm2, hyx, hylt⟩ := wds_named hb h htx (by rw [← hsl]; exact hl)
        (hks c y hy)
      refine ⟨m', ?_, by rw [hwl5, ← hlev]; exact hm2⟩
      rw [hO5.2, ss_ite_neg (Nat.ne_of_lt hylt), hold4 y hylt]
      exact hm1
  have hpU : w6.path = w.path := by rw [e6, e5, e4, e3, e2, e1]; rfl
  have hn6 : w6.next = w.next + 4 := by rw [e6, e5, e4, e3, e2]; show w1.next + 2 = _; rw [hn1]
  have hlk6 : ∀ y, y ≠ x → y < w.next → w6.nodes.lookup y = w.nodes.lookup y := by
    intro y _ hy
    rw [e6, ss_lookup_withNode (ss_ne_of_lt_add hy), e5, ss_lookup_withNode (Nat.ne_of_lt hy),
      hlk4 y (Nat.ne_of_lt hy) (ss_ne_of_lt_add hy)]
  obtain ⟨hpre, hxnot, hreach, -⟩ := wds_parent_pre hb h htx hq1 hq3 hq4 hqx hql hk1 hqr hlq hnx
    hsplit hL1 hfl hsl hlf hls hwff hwfs hszf hszs hkf hks (first := w.next)
    (second := w.next + 2) (insU := [(k1, w.next), (sc, w.next + 2)]) hO6.1 hpU
    (by rw [e6, e5, e4, e3, e2, e1]; rfl) (by rw [e6, e5, e4, e3, e2, e1]; rfl)
    (by rw [e6, e5, e4, e3, e2, e1]; rfl) hlk6
    (by
      intro y hy
      rw [show wLevel s w6 = wLevel s w4 by rw [e6, e5]; rfl]
      exact hwlo y hy)
    (by
      intro z h1 h2
      rw [hO6.2, ss_ite_neg h2, hO5.2, ss_ite_neg h1, hT4, hO2.2, ss_ite_neg h2, hO1.2,
        ss_ite_neg h1])
    (by rw [hO6.2, ss_ite_neg hne20.symm, hO5.2, ss_ite_pos rfl, hlev])
    (by rw [hO6.2, ss_ite_pos rfl, hlev])
    (Or.inr (Nat.le_refl _)) (Nat.le_add_right _ _) hne20.symm (Or.inr rfl)
  rw [wp_bind]
  refine WP.mono (hup q _ w6 nq C hpre) (fun _ (w' : MW) hpost => ?_)
  refine ss_wp_getPut (n := n) (fun hout => ?_)
  obtain ⟨hPI, hCP⟩ := hpost hout
  have hlk6x : w6.nodes.lookup x = some n := by
    rw [e6, ss_lookup_withNode (ss_ne_of_lt_add hxlt), e5, ss_lookup_withNode (Nat.ne_of_lt hxlt),
      hlk4 x (Nat.ne_of_lt hxlt) (ss_ne_of_lt_add hxlt)]
    exact hlook
  have hlkx : w'.nodes.lookup x = some n := by
    refine hCP.off x n hlk6x ?_
    intro d' c hd' e
    rw [hpU] at e
    exact hnx d' c x hd' e rfl
  have hsx : (s.obj x).isSome = true := (h.books.first x n hlook htx).mpr hin
  have htx' : w'.taken.contains x = false := by
    cases e : w'.taken.contains x with
    | false => rfl
    | true =>
      obtain ⟨m, hm, hmx⟩ := List.mem_map.mp (hPI.books.taken x e)
      have := (hPI.books.ids.2.2.1 m hm).2
      rw [hmx] at this
      rw [(hb.ids x this).1] at hsx
      cases hsx
  have hxnr : x ∉ reachOf i s w' := by
    intro hx
    rcases hCP.reach x hx with h1 | h1
    · exact hxnot hxlt.ne' h1
    · rw [hn6] at h1
      exact absurd (Nat.lt_of_lt_of_le hxlt (Nat.le_trans (Nat.le_add_right _ 4) h1))
        (Nat.lt_irrefl _)
  have hO' : SsOk p i base s tp (fun _ => False) w' :=
    ⟨hPI.frame, hPI.balanced, hPI.books.toE, hPI.top, fun y m hy ht he => by
      obtain ⟨t, r, hr⟩ := hPI.books.timeFirst y m hy ht
      rw [hr] at he
      cases he⟩
  have hO'' := ssOk_withNode (E' := fun _ => False) hO' hlkx htx' rfl (m' := n.toPrev (i - 1))
    (Or.inl (by
      obtain ⟨rest', hr'⟩ := ss_toPrev_head hr0 ht0i
      rw [hr', hr0]; rfl))
    (fun t ht => h.books.times x n hlook t (ss_mem_toPrev ht))
    (fun n0 hn0' => Or.inl (wds_toPrev hb h htx hn0'))
    (fun hl c y hy => by
      obtain ⟨-, -, hb3⟩ := hO'.bal x _ (treeOf_obj_overlay i s hlkx htx')
      exact hb3 hl c y (ss_key_ksOf (ss_mem_toPrev hy)))
    (by obtain ⟨rest', hr'⟩ := ss_toPrev_head hr0 ht0i; rw [hr']; simp) (fun _ _ h => h)
  have ha : ∀ z ∈ reachOf i s w', (treeOf i s (w'.withNode x (n.toPrev (i - 1)))).obj z =
      (treeOf i s w').obj z := by
    intro z hz
    have hzx : z ≠ x := fun e => hxnr (e ▸ hz)
    rw [hO''.2, ss_ite_neg hzx]
  have hrx : w'.top.rootKey ≠ x := fun e => hxnr (by unfold reachOf; rw [e]; exact tc_self _ _ _)
  have hfuel : (treeOf i s (w'.withNode x (n.toPrev (i - 1)))).fuel w'.top.rootKey =
      (treeOf i s w').fuel w'.top.rootKey := by
    simp only [Tree.fuel, hO''.2, ss_ite_neg hrx]
  have hreach' : reachOf i s (w'.withNode x (n.toPrev (i - 1))) = reachOf i s w' := by
    unfold reachOf
    show reachAt _ ((treeOf i s (w'.withNode x (n.toPrev (i - 1)))).fuel w'.top.rootKey)
      w'.top.rootKey = _
    rw [hfuel]
    exact reachAt_agree _ _ ha
  have hSB : Sound p.M none (treeOf i s (w'.withNode x (n.toPrev (i - 1))))
      (w'.withNode x (n.toPrev (i - 1))).top.rootKey C := by
    refine Sound.agree hPI.sound ha (fun z hz => ?_)
    by_cases hzx : z = x
    · rw [hzx, hO''.2, ss_ite_pos rfl]; rfl
    · rw [hO''.2, ss_ite_neg hzx]; exact hz
  have hroot : (treeOf i s (w'.withNode x (n.toPrev (i - 1)))).root =
      some (w'.withNode x (n.toPrev (i - 1))).top.rootKey := by
    rw [treeOf_withNode i s _ htx']
    exact hPI.root
  refine ⟨hlkx, ss_pinv hO''.1 hroot hSB, ⟨hCP.path.trans hpU, ?_, ?_, ?_⟩⟩
  · intro y ny hy hnot
    have hyx : y ≠ x := fun e => hnot (d + 1) (some k1) le_rfl (by rw [e]; exact hon')
    have hylt : y < w.next := h.books.ids.1 y ny hy
    rw [ss_lookup_withNode hyx]
    refine hCP.off y ny (by rw [hlk6 y hyx hylt]; exact hy) ?_
    intro d' c hd'
    rw [hpU]
    exact hnot d' c (by omega)
  · exact Nat.le_trans (ss_le_add hn6) hCP.next
  · intro z hz
    rw [hreach'] at hz
    rcases hCP.reach z hz with h1 | h1
    · rcases hreach z h1 with h2 | h2 | h2
      · exact Or.inl h2
      · rw [h2]; exact Or.inr (Nat.le_refl _)
      · rw [h2]; exact Or.inr (Nat.le_add_right _ _)
    · exact Or.inr (Nat.le_trans (ss_le_add hn6) h1)


theorem wds_parent_new {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {d : Nat} {x : NodeId} {w : MW} {n V last : MNode}
    {C : List (Key × Nat)} {up : NodeId → List (Nat × NodeId) → SIS.Tree.M Unit}
    (hp : ParamsOK p) (hb : Books i base s tp) (h : CasPreD p i base s tp w (d + 1) x n V last C)
    (hup : UpOk p i base s tp v up d)
    (hcase : p.splitAbove < last.size) (hin : ¬ n.firstTime = some i) :
    WP (SIS.Tree.handleFullWith up (d + 1) x [] last false)
      { p := p, i := i, view := v } w (CasPostD p i base s tp w (d + 1) x V C) := by
  obtain ⟨c0, hon⟩ := h.on
  have htx : w.taken.contains x = false := (h.path.lookup le_rfl hon).choose_spec.2
  obtain ⟨g, hh, hgh, -⟩ := h.books.levels x n h.look htx
  obtain ⟨k1, cq, q, nq, hq1, hon', hq3, -, -, hql, -⟩ := wds_path h hon htx
  have hc' : (!false && decide (last.size > p.splitAbove)) = true := by
    simpa using hcase
  have hin' : (n.firstTime == some i) = false := by simpa using hin
  unfold SIS.Tree.handleFullWith
  refine ss_wp_step (ss_read _ w) ?_
  refine ss_wp_step (getNode_hit _ h.look) ?_
  refine ss_wp_step (ghOf_hit _ h.look hgh) ?_
  refine ss_wp_step (parentAt_succ _ hq1) ?_
  dsimp only
  refine ss_wp_step (getNode_hit _ hq3) ?_
  refine ss_wp_step (ss_pure _ _ _) ?_
  simp only [Bool.false_eq_true, ↓reduceIte, hc', hin', hql]
  refine ss_wp_step (ss_modify _ _) ?_
  refine ss_wp_step (newKey_eq _ _ _ _ _ _) ?_
  refine ss_wp_step (newKey_eq _ _ _ _ _ _) ?_
  refine ss_wp_step (ss_setMadeFor _ _ _ _) ?_
  refine ss_wp_step (ss_setMadeFor _ _ _ _) ?_
  refine ss_wp_step (ss_note _ _ _) ?_
  generalize hH : SIS.Tree.halves n.leaf i last [] = H
  obtain ⟨f, s2, sc⟩ := H
  dsimp only
  refine ss_wp_step (putNode_eq _ _ _ _) ?_
  refine ss_wp_step (putNode_eq _ _ _ _) ?_
  refine ss_wp_step (ss_klongAt rfl hon') ?_
  simp only [Bool.not_false, ↓reduceIte]
  exact wds_parent_new_post hp hb h hup hcase hin hgh hq1 hq3 hon' hH rfl rfl rfl rfl rfl rfl

/-! ## 10. The step

`handleFull` with a space split: at the space root or under an inner parent,
x made by the transaction or not; the parent's step is `appendKlongs`
(`appendKlongs_spec`). -/

theorem handleFullD_space {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} (hp : ParamsOK p) (hb : Books i base s tp) {depth : Nat} {x : NodeId}
    {w : MW} {n V last : MNode} {C : List (Key × Nat)}
    (h : CasPreD p i base s tp w depth x n V last C)
    (hcase : p.splitAbove < last.size) :
    WP (SIS.Tree.handleFull depth x last false) { p := p, i := i, view := v } w
      (CasPostD p i base s tp w depth x V C) := by
  cases depth with
  | zero =>
    by_cases hin : n.firstTime = some i
    · exact wds_root_inPlace hp hb h hcase hin
    · exact wds_root_new hp hb h hcase hin
  | succ d =>
    have hup := appendKlongs_spec (v := v) hp hb d
    by_cases hin : n.firstTime = some i
    · exact wds_parent_inPlace hp hb h hup hcase hin
    · exact wds_parent_new hp hb h hup hcase hin

end Contract
