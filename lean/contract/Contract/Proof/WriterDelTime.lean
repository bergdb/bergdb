/-
The contract package (bergdb 030-16): `handleFull` of a delete when it does a
time split (Java's `Dag.timeSplit` and `timeSplitInPlace` with nothing to
insert): x is replaced by its last version `last`, a new node y that the
parent's klong then names, or that becomes the space root; a node that the
transaction made becomes `last` in place. Also a node full by its dead
klongs only (`compact`).

The put's form of the same rule is WriterTimeSplit.lean (`handleFull_time`,
from `CasPre`); this file is its form from `CasPreD` (WriterDelDefs.lean): the
node x would be V, and `last` is V's last version.

The proof follows the put's, section by section, with V for the node with
the klongs added and `last` for its last version; the helpers of
WriterTimeSplit.lean that do not mention `CasPre` are used as they are. The
state w's own frame, top and BalancedOK are given in `CasPreD`. With nothing
to insert, `replaceOrAdd last []` gives `last` (`replaceOrAdd_spec`); the
parent's step is the put's `appendKlongs` (`appendKlongs_spec`), from `CasPre`
for the parent with the one klong of the new node, by `Sound.timeSplit`.
-/
import Contract.Proof.WriterDelDefs

namespace Contract

open SIS (View)
open SIS.Check (BVal)
open SIS.Tree (Ctx)

/-! ## 1. The state w -/

/-- x is not taken: it is on the path. -/
theorem wdt_taken {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top} {w : MW}
    {depth : Nat} {x : NodeId} {n V last : MNode} {C : List (Key × Nat)}
    (h : CasPreD p i base s tp w depth x n V last C) : w.taken.contains x = false := by
  obtain ⟨c0, hon⟩ := h.on
  obtain ⟨m, -, ht⟩ := h.path.lookup (le_refl _) hon
  exact ht

/-- The map of the "if" state: x set to V, of x's kind. -/
theorem wdt_treeA {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top} {w : MW}
    {depth : Nat} {x : NodeId} {n V last : MNode} {C : List (Key × Nat)}
    (h : CasPreD p i base s tp w depth x n V last C) :
    treeOf i s (w.withNode x V) = (treeOf i s w).set x (.key ⟨wLevel s w x, n.leaf, ksOf V⟩) := by
  rw [treeOf_withNode i s _ (wdt_taken h), h.vleaf]

/-! ## 2. A node that the transaction made: in place -/

/-- The state after the time split in place: x is the node r, with x's
kind, whose live klongs are those of V. -/
theorem wdt_inPlace {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {depth : Nat} {x : NodeId} {w : MW} {n V last : MNode} {C : List (Key × Nat)}
    (h : CasPreD p i base s tp w depth x n V last C)
    (hnt : n.firstTime = some i) {r : MNode}
    (hrl : live (ksOf r) = live (ksOf V)) (hrwf : klongsWf (ksOf r) = true)
    (hrs : r.size ≤ p.M)
    (hrk : ∀ c y, Klong.key c y ∈ ksOf r → Klong.key c y ∈ ksOf V)
    (hrf : ∃ rest, r.ks = .time i :: rest) (hrt : TimesLe r i)
    (hxr : x ∈ reachAt (treeOf i s (w.withNode x V))
      ((treeOf i s (w.withNode x V)).fuel w.top.rootKey) w.top.rootKey)
    (T : List String) :
    CasPostD p i base s tp w depth x V C ()
      (MW.withNode { w with trail := T } x ⟨n.leaf, r.ks⟩) := by
  intro _
  have htx := wdt_taken h
  have hx := h.look
  have hA := wdt_treeA h
  have hBt : treeOf i s (MW.withNode { w with trail := T } x ⟨n.leaf, r.ks⟩) =
      (treeOf i s w).set x (.key ⟨wLevel s w x, n.leaf, ksOf r⟩) := by
    rw [treeOf_withNode i s (w := { w with trail := T }) _ htx]
    rfl
  have hAx : (treeOf i s (w.withNode x V)).obj x =
      some (.key ⟨wLevel s w x, n.leaf, ksOf V⟩) := by
    rw [hA]; simp [Tree.set]
  have hBx : (treeOf i s (MW.withNode { w with trail := T } x ⟨n.leaf, r.ks⟩)).obj x =
      some (.key ⟨wLevel s w x, n.leaf, ksOf r⟩) := by
    rw [hBt]; simp [Tree.set]
  have hsame : ∀ z, z ≠ x →
      (treeOf i s (MW.withNode { w with trail := T } x ⟨n.leaf, r.ks⟩)).obj z =
        (treeOf i s (w.withNode x V)).obj z := by
    intro z hz
    rw [hA, hBt]
    simp [Tree.set, hz]
  have hxok := h.vsound.nodes x hxr _ hAx
  simp only [ite_true] at hxok
  obtain ⟨-, -, hxp⟩ := ts_nodeOk_iff.mp hxok
  have hNode : NodeIs (treeOf i s (MW.withNode { w with trail := T } x ⟨n.leaf, r.ks⟩)) x
      (wLevel s w x) n.leaf (live (ksOf V)) p.M := by
    refine ⟨_, hBx, rfl, rfl, hrl, ts_nodeOk_iff.mpr ⟨?_, hrwf, fun c y hk => ?_⟩⟩
    · show (ksOf r).length ≤ p.M
      rw [ksOf_length]; exact hrs
    · have := hxp c y (hrk c y hk)
      by_cases hy : y = x
      · rw [hy, hBx]; rfl
      · rw [hsame y hy]; exact this
  have hS := Sound.inPlace h.vsound hAx hNode hsame
  have hfirst := h.books.first x n hx htx
  refine ⟨⟨?_, hS, ?_, h.wtop, ?_, ?_⟩, ⟨rfl, ?_, le_refl _, ?_⟩⟩
  · rw [hBt]; exact h.wroot
  · refine frame_withNode (w := { w with trail := T }) h.wframe hx htx rfl (fun n0 hs0 => ?_)
    exact absurd hnt (hfirst.mp (by rw [hs0]; rfl))
  · refine balancedAll_withNode (w := { w with trail := T }) h.wbal hx htx rfl
      (fun hl c y hy => ?_)
    exact ts_kids hA h.vbal hl (hrk c y (ts_key_mem_ksOf hy))
  · refine putBooks_withNode (w := { w with trail := T })
      (putBooks_congr h.books rfl rfl rfl rfl rfl rfl rfl rfl rfl) hx htx rfl ?_ ?_
    · obtain ⟨rest, hr⟩ := hrf
      obtain ⟨t0, rest0, hn⟩ := h.books.timeFirst x n hx htx
      rw [prim_firstTime_of hn] at hnt
      cases hnt
      show r.ks.head? = n.ks.head?
      rw [hr, hn]
      rfl
    · intro t ht
      exact hrt t (ts_time_mem_ksOf ht)
  · intro y m hy hny
    have hyx : y ≠ x := by
      intro e
      obtain ⟨c0, hon⟩ := h.on
      exact hny depth c0 (le_refl _) (e ▸ hon)
    show (SIS.Tree.upsert w.nodes x _).lookup y = some m
    rw [lookup_upsert_ne _ _ hyx]
    exact hy
  · intro z hz
    left
    unfold reachOf at hz ⊢
    rw [ts_reach_live hAx hBx hrl rfl hsame] at hz
    exact hz

/-! ## 3. A node from before the transaction at the space root -/

/-- The time split at the space root of a node from before the transaction: a
new node y, with the live klongs of V, becomes the space root; then x is cut
back to its node of before. -/
theorem wdt_root {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    (hb : Books i base s tp) {x : NodeId} {w : MW} {n V last : MNode} {C : List (Key × Nat)}
    (h : CasPreD p i base s tp w 0 x n V last C)
    (hnt : n.firstTime ≠ some i) {g hh : Nat} (hg : w.gh.lookup x = some (g, hh)) {r : MNode}
    (hrl : live (ksOf r) = live (ksOf V)) (hrwf : klongsWf (ksOf r) = true)
    (hrs : r.size ≤ p.M)
    (hrk : ∀ c y, Klong.key c y ∈ ksOf r → Klong.key c y ∈ ksOf V)
    (hrf : ∃ rest, r.ks = .time i :: rest) (hrt : TimesLe r i)
    (M' : List (NodeId × NodeId)) (T' : List String) :
    CasPostD p i base s tp w 0 x V C ()
      (MW.withNode (MW.afterSuperRoot
        { w.afterNewKey p g hh n.leaf r.ks with madeFor := M', trail := T' } p i w.next)
        x (n.toPrev (i - 1))) := by
  intro _
  have htx := wdt_taken h
  have hF := h.wframe
  have hT := h.wtop
  have hB := h.wbal
  have hx := h.look
  have hxr : x = w.top.rootKey := by
    obtain ⟨c0, hon⟩ := h.on
    rw [h.path.root] at hon
    cases hon
    rfl
  obtain ⟨g', hh', hgh, hG, hH, hlev, hleaf⟩ := h.books.levels x n hx htx
  rw [hg] at hgh
  cases hgh
  obtain ⟨hf0, hs0, hn0, -, ht0, hm0⟩ := treeOf_fresh hb h.books (Nat.le_refl w.next)
  have hxne : x ≠ w.next := Nat.ne_of_lt (h.books.ids.1 x n hx)
  have hA := wdt_treeA h
  have hAx : (treeOf i s (w.withNode x V)).obj x =
      some (.key ⟨wLevel s w x, n.leaf, ksOf V⟩) := by
    rw [hA]; simp [Tree.set]
  -- the states
  let W1 : MW := { w.afterNewKey p g hh n.leaf r.ks with madeFor := M', trail := T' }
  let W2 : MW := MW.afterSuperRoot W1 p i w.next
  have hT1 : treeOf i s W1 = (treeOf i s w).set w.next (.key ⟨p.keyLevel g hh, n.leaf, ksOf r⟩) :=
    treeOf_afterNewKey i s p g hh n.leaf r.ks hs0 hn0 ht0 hm0
  have hK1 : PutBooks p i base s W1 :=
    putBooks_congr (putBooks_afterNewKey hb h.books hG hH hleaf hrf
      (fun t ht => hrt t (ts_time_mem_ksOf ht))) rfl rfl rfl rfl rfl rfl rfl rfl rfl
  obtain ⟨f1, -, f3, -, f5, -, -, f8, -⟩ := afterSuperRoot_fields W1 p i w.next
  obtain ⟨hobj2, hroot2, -⟩ := treeOf_afterSuperRoot i s p w.next hK1.ids.1
  have hx2 : W2.nodes.lookup x = some n := by
    rw [f3]; exact prim_lookup_append_some _ hx
  have ht2 : W2.taken.contains x = false := by rw [f5]; exact htx
  have hT3 : treeOf i s (W2.withNode x (n.toPrev (i - 1))) =
      (treeOf i s W2).set x (.key ⟨wLevel s W2 x, n.leaf, ksOf (n.toPrev (i - 1))⟩) :=
    treeOf_withNode i s _ ht2
  have hBobj : ∀ z, (treeOf i s (W2.withNode x (n.toPrev (i - 1)))).obj z =
      if z = x then some (.key ⟨wLevel s W2 x, n.leaf, ksOf (n.toPrev (i - 1))⟩) else
        if z = w.next then some (.key ⟨p.keyLevel g hh, n.leaf, ksOf r⟩) else
          (treeOf i s w).obj z := by
    intro z
    rw [hT3]
    simp only [Tree.set]
    rw [hobj2, hT1]
    rfl
  -- the rule
  have hxok := h.vsound.nodes x
    (by rw [← hxr]
        exact tc_self _ _ _) _ hAx
  simp only [ite_true] at hxok
  obtain ⟨-, -, hxp⟩ := ts_nodeOk_iff.mp hxok
  have hsome : ∀ z, ((treeOf i s (w.withNode x V)).obj z).isSome = true →
      ((treeOf i s (W2.withNode x (n.toPrev (i - 1)))).obj z).isSome = true := by
    intro z hz
    rw [hBobj]
    by_cases e1 : z = x
    · simp [e1]
    · by_cases e2 : z = w.next
      · subst e2
        simp [Ne.symm hxne]
      · simp only [e1, e2, ↓reduceIte]
        rw [hA] at hz
        simpa [Tree.set, e1] using hz
  have hBy : NodeIs (treeOf i s (W2.withNode x (n.toPrev (i - 1)))) w.next (wLevel s w x) n.leaf
      (live (ksOf V)) p.M := by
    refine ⟨⟨p.keyLevel g hh, n.leaf, ksOf r⟩, by rw [hBobj]; simp [Ne.symm hxne], hlev.symm,
      rfl, hrl,
      ts_nodeOk_iff.mpr ⟨?_, hrwf, fun c y hk => hsome y (hxp c y (hrk c y hk))⟩⟩
    show (ksOf r).length ≤ p.M
    rw [ksOf_length]; exact hrs
  have hS0 : Sound p.M (some x) (treeOf i s (w.withNode x V)) x C := by
    have := h.vsound
    rw [← hxr] at this
    exact this
  obtain ⟨hSB, -, hreach⟩ := Sound.timeSplitRoot hS0 hAx
    (show (treeOf i s (w.withNode x V)).obj w.next = none from
      by rw [hA]; simpa [Tree.set, Ne.symm hxne] using hf0) hBy (by rw [hBobj]; simp)
    (fun z e1 e2 => by rw [hBobj, hA]; simp [Tree.set, e1, e2])
  -- the frame, BalancedOK, the books
  have hF1 : Frame i s (dirtyOf W1) (treeOf i s W1) :=
    frame_afterNewKey p g hh n.leaf r.ks hF hs0 hn0 ht0 hm0
  have hF3 := frame_withNode (ts_frame_superRoot p w.next hF1 hK1.ids.1) hx2 ht2
    (rfl : (n.toPrev (i - 1)).leaf = n.leaf) (ts_toPrev_ext hb hF hx htx)
  have hB1 : BalancedAll p (treeOf i s W1) :=
    balancedAll_afterNewKey g hh n.leaf r.ks hB hs0 hn0 ht0 hm0 hH hleaf (fun hl c y hy => by
      rw [← hlev]
      exact ts_kids hA h.vbal hl (hrk c y (ts_key_mem_ksOf hy)))
  have hB2 : BalancedAll p (treeOf i s W2) := by
    unfold BalancedAll; rw [hobj2]; exact hB1
  have hB3 := balancedAll_withNode hB2 hx2 ht2 (rfl : (n.toPrev (i - 1)).leaf = n.leaf)
    (fun hl c y hy => by
      obtain ⟨-, -, hk⟩ := hB2 x _ (treeOf_obj_overlay i s hx2 ht2)
      exact hk hl c y (ts_key_mem_ksOf (ts_mem_toPrev hy)))
  obtain ⟨hfst, htimes⟩ := ts_old h.books hx htx hnt
  have hK3 := putBooks_withNode (n' := n.toPrev (i - 1)) (putBooks_afterSuperRoot w.next hK1) hx2
    ht2 rfl hfst htimes
  have hT2 : WTopInv i s tp W2.top W2.newTop :=
    topInv_afterSuperRoot w.next hT hb (by have := hK1.ids.2.2.2.1; exact this)
  refine ⟨⟨?_, ?_, hF3, hT2, hB3, hK3⟩, ⟨f8, ?_, ?_, ?_⟩⟩
  · rw [hT3]
    show (treeOf i s W2).root = some W2.top.rootKey
    rw [hroot2, f1]
  · show Sound p.M none (treeOf i s (W2.withNode x (n.toPrev (i - 1)))) W2.top.rootKey C
    rw [f1]
    exact hSB
  · intro y m hy hny
    have hyx : y ≠ x := by
      intro e
      obtain ⟨c0, hon⟩ := h.on
      exact hny 0 c0 (le_refl _) (e ▸ hon)
    show (SIS.Tree.upsert W2.nodes x _).lookup y = some m
    rw [lookup_upsert_ne _ _ hyx, f3]
    exact prim_lookup_append_some _ hy
  · show w.next ≤ W2.next
    cases hnt1 : W1.newTop
    · rw [(afterSuperRoot_new hnt1 p i w.next).2.1]
      show w.next ≤ w.next + 2 + 2
      omega
    · rw [(afterSuperRoot_inPlace hnt1 p i w.next).2.1]
      show w.next ≤ w.next + 2
      omega
  · intro z hz
    unfold reachOf at hz ⊢
    have hz' : z ∈ reachAt (treeOf i s (W2.withNode x (n.toPrev (i - 1))))
        ((treeOf i s (W2.withNode x (n.toPrev (i - 1)))).fuel w.next) w.next := by
      rw [← f1]; exact hz
    rcases hreach z hz' with e | e
    · left
      show z ∈ reachAt (treeOf i s (w.withNode x V))
        ((treeOf i s (w.withNode x V)).fuel w.top.rootKey) w.top.rootKey
      rw [← hxr]
      exact e
    · right
      rw [e]

/-! ## 4. A node from before the transaction below the space root -/

/-- The time split below the space root of a node from before the
transaction, up to the parent's step: the state after the new node y is made
meets `CasPre` for the parent q with y's klong, from the rule `Sound.timeSplit`;
and the nodes that the parent's "if" state reaches. -/
theorem wdt_parentPre {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    (hb : Books i base s tp) {d : Nat} {x : NodeId} {w : MW} {n V last : MNode}
    {C : List (Key × Nat)} (h : CasPreD p i base s tp w (d + 1) x n V last C)
    {g hh : Nat} (hg : w.gh.lookup x = some (g, hh)) {r : MNode}
    (hrl : live (ksOf r) = live (ksOf V)) (hrwf : klongsWf (ksOf r) = true)
    (hrs : r.size ≤ p.M)
    (hrk : ∀ c y, Klong.key c y ∈ ksOf r → Klong.key c y ∈ ksOf V)
    (hrf : ∃ rest, r.ks = .time i :: rest) (hrt : TimesLe r i)
    {q : NodeId} {nq : MNode} {c0 : Option Nat} {k1 : Nat} (hq : w.path[d]? = some (c0, q))
    (hqn : w.nodes.lookup q = some nq) (hk1 : w.path[d + 1]? = some (some k1, x))
    (M' : List (NodeId × NodeId)) (T' : List String) :
    CasPre p i base s tp { w.afterNewKey p g hh n.leaf r.ks with madeFor := M', trail := T' } d q
        nq [(k1, w.next)] C ∧
      x ∉ reachOf i s (MW.withNode
        { w.afterNewKey p g hh n.leaf r.ks with madeFor := M', trail := T' } q
        (addAll i nq [(k1, w.next)])) ∧
      ∀ z ∈ reachOf i s (MW.withNode
        { w.afterNewKey p g hh n.leaf r.ks with madeFor := M', trail := T' } q
        (addAll i nq [(k1, w.next)])),
        z ∈ reachOf i s (w.withNode x V) ∨ z = w.next := by
  have htx := wdt_taken h
  have hF := h.wframe
  have hT := h.wtop
  have hB := h.wbal
  have hx := h.look
  obtain ⟨g', hh', hgh, hG, hH, hlev, hleaf⟩ := h.books.levels x n hx htx
  rw [hg] at hgh
  cases hgh
  obtain ⟨hf0, hs0, hn0, -, ht0, hm0⟩ := treeOf_fresh hb h.books (Nat.le_refl w.next)
  have hxne : x ≠ w.next := Nat.ne_of_lt (h.books.ids.1 x n hx)
  -- the parent
  obtain ⟨-, -, htq⟩ := h.path.lookup (Nat.le_succ d) hq
  have hqne : q ≠ w.next := Nat.ne_of_lt (h.books.ids.1 q nq hqn)
  have hqx : q ≠ x := ts_path_ne hB h.path h.inner hk1 (Nat.lt_succ_self d) hq
  have hlq : wLevel s w x + 1 = wLevel s w q := ts_path_step hB h.path h.inner
    (Nat.lt_succ_self d) hq hk1
  have hk1l : (k1, x) ∈ live (ksOf nq) := by
    obtain ⟨c0', u, c, y, nu, e1, e2, e3, e4⟩ := h.path.links d (Nat.lt_succ_self d)
    rw [hq] at e1
    cases e1
    rw [hk1] at e2
    cases e2
    rw [treeOf_obj_overlay i s hqn htq] at e3
    cases e3
    exact e4
  -- the tree A of the "if" state
  have hA := wdt_treeA h
  have hAo : ∀ z, z ≠ x → (treeOf i s (w.withNode x V)).obj z = (treeOf i s w).obj z := by
    intro z hz; rw [hA]; simp [Tree.set, hz]
  have hAx : (treeOf i s (w.withNode x V)).obj x =
      some (.key ⟨wLevel s w x, n.leaf, ksOf V⟩) := by
    rw [hA]; simp [Tree.set]
  have hAq : (treeOf i s (w.withNode x V)).obj q =
      some (.key ⟨wLevel s w q, nq.leaf, ksOf nq⟩) := by
    rw [hAo q hqx]; exact treeOf_obj_overlay i s hqn htq
  have hreachP := ts_path_reach (w := w) h.vsound.good hB h.path h.inner hk1 hAo
  have hqr := hreachP d (Nat.le_succ d) c0 q hq
  have hxr := hreachP (d + 1) (Nat.le_refl _) (some k1) x hk1
  have hxok := h.vsound.nodes x hxr _ hAx
  simp only [ite_true] at hxok
  obtain ⟨-, -, hxp⟩ := ts_nodeOk_iff.mp hxok
  have hqok := h.vsound.nodes q hqr _ hAq
  simp only [Option.some.injEq, Ne.symm hqx, ite_false] at hqok
  obtain ⟨hqlen, hqwf, hqp⟩ := ts_nodeOk_iff.mp hqok
  -- the states
  let W1 : MW := { w.afterNewKey p g hh n.leaf r.ks with madeFor := M', trail := T' }
  have hT1 : treeOf i s W1 = (treeOf i s w).set w.next (.key ⟨p.keyLevel g hh, n.leaf, ksOf r⟩) :=
    treeOf_afterNewKey i s p g hh n.leaf r.ks hs0 hn0 ht0 hm0
  have hK1 : PutBooks p i base s W1 :=
    putBooks_congr (putBooks_afterNewKey hb h.books hG hH hleaf hrf
      (fun t ht => hrt t (ts_time_mem_ksOf ht))) rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hqn1 : W1.nodes.lookup q = some nq := prim_lookup_append_some _ hqn
  have hwq : wLevel s W1 q = wLevel s w q :=
    prim_wLevel_afterNewKey (p := p) (g := g) (h := hh) (leaf := n.leaf) (ks := r.ks) hqne
  have hTq : treeOf i s (W1.withNode q (addAll i nq [(k1, w.next)])) =
      (treeOf i s W1).set q (.key ⟨wLevel s w q, nq.leaf, ksOf (addAll i nq [(k1, w.next)])⟩) := by
    rw [treeOf_withNode i s (w := W1) _ htq, hwq, addAll_leaf]
  have hBobj : ∀ z, (treeOf i s (W1.withNode q (addAll i nq [(k1, w.next)]))).obj z =
      if z = q then some (.key ⟨wLevel s w q, nq.leaf, ksOf (addAll i nq [(k1, w.next)])⟩) else
        if z = w.next then some (.key ⟨p.keyLevel g hh, n.leaf, ksOf r⟩) else
          (treeOf i s w).obj z := by
    intro z
    rw [hTq]
    simp only [Tree.set]
    rw [hT1]
    rfl
  have hsome : ∀ z, ((treeOf i s (w.withNode x V)).obj z).isSome = true →
      ((treeOf i s (W1.withNode q (addAll i nq [(k1, w.next)]))).obj z).isSome = true := by
    intro z hz
    rw [hBobj]
    by_cases e1 : z = q
    · simp [e1]
    · by_cases e2 : z = w.next
      · subst e2
        simp [hqne.symm]
      · simp only [e1, e2, ↓reduceIte]
        by_cases e3 : z = x
        · subst e3
          rw [treeOf_obj_overlay i s hx htx]
          rfl
        · rw [hAo z e3] at hz
          exact hz
  -- the rule
  have hBy : NodeIs (treeOf i s (W1.withNode q (addAll i nq [(k1, w.next)]))) w.next
      (wLevel s w x) n.leaf (live (ksOf V)) p.M := by
    refine ⟨⟨p.keyLevel g hh, n.leaf, ksOf r⟩, by rw [hBobj]; simp [hqne.symm], hlev.symm,
      rfl, hrl, ts_nodeOk_iff.mpr ⟨?_, hrwf, fun c y hk => hsome y (hxp c y (hrk c y hk))⟩⟩
    show (ksOf r).length ≤ p.M
    rw [ksOf_length]; exact hrs
  have hBq : NodeIs (treeOf i s (W1.withNode q (addAll i nq [(k1, w.next)]))) q
      (wLevel s w q) nq.leaf (insertCv k1 w.next (live (ksOf nq))) (bnd p.M (some q) q) := by
    refine ⟨⟨wLevel s w q, nq.leaf, ksOf (addAll i nq [(k1, w.next)])⟩, by rw [hBobj]; simp,
      rfl, rfl, by rw [addAll_live hqwf]; rfl, ts_nodeOk_iff.mpr ⟨?_, addAll_wf hqwf _, ?_⟩⟩
    · show (ksOf (addAll i nq [(k1, w.next)])).length ≤ bnd p.M (some q) q
      rw [ksOf_length]
      have := addAll_size i nq [(k1, w.next)]
      have hql : (ksOf nq).length ≤ p.M := hqlen
      rw [ksOf_length] at hql
      simp only [bnd, ite_true, List.length_singleton] at this ⊢
      omega
    · intro c y hk
      rcases (addAll_key_mem _ nq).mp hk with hk | hk
      · exact hsome y (hqp c y hk)
      · simp only [List.mem_singleton, Prod.mk.injEq] at hk
        rw [hk.2, hBobj]
        simp [hqne.symm]
  have hBx : ((treeOf i s (W1.withNode q (addAll i nq [(k1, w.next)]))).obj x).isSome = true := by
    rw [hBobj]
    simp only [Ne.symm hqx, hxne, ↓reduceIte]
    rw [treeOf_obj_overlay i s hx htx]
    rfl
  obtain ⟨hSB, hxnot, hreach⟩ := Sound.timeSplit h.vsound hqr hAq hk1l hAx
    (show (treeOf i s (w.withNode x V)).obj w.next = none from
      by rw [hA]; simpa [Tree.set, Ne.symm hxne] using hf0) hBy hBq hBx
    (fun z e1 e2 e3 => by rw [hBobj, hAo z e1]; simp [e2, e3])
  -- the frame, BalancedOK, the books
  have hF1 : Frame i s (dirtyOf W1) (treeOf i s W1) :=
    frame_afterNewKey p g hh n.leaf r.ks hF hs0 hn0 ht0 hm0
  have hB1 : BalancedAll p (treeOf i s W1) :=
    balancedAll_afterNewKey g hh n.leaf r.ks hB hs0 hn0 ht0 hm0 hH hleaf (fun hl c y hy => by
      rw [← hlev]
      exact ts_kids hA h.vbal hl (hrk c y (ts_key_mem_ksOf hy)))
  obtain ⟨tq, restq, hnq⟩ := h.books.timeFirst q nq hqn htq
  refine ⟨⟨hqn1, ⟨c0, hq⟩, ?_, ?_, hK1, hqwf, ?_, Or.inl rfl, ?_, ⟨?_, hSB, ?_, hT, ?_, ?_⟩⟩,
    hxnot, hreach⟩
  · exact PathOk.congr (pathOk_afterNewKey p g hh n.leaf r.ks (h.path.mono (Nat.le_succ d)) hs0
      hn0 ht0 hm0) rfl rfl rfl rfl rfl
  · intro d' c u m hd' hu hm
    obtain ⟨m', hm', -⟩ := h.path.lookup (by omega : d' ≤ d + 1) hu
    have : W1.nodes.lookup u = some m' := prim_lookup_append_some _ hm'
    rw [hm] at this
    cases this
    exact h.inner d' c u m (by omega) hu hm'
  · have hql : (ksOf nq).length ≤ p.M := hqlen
    rw [ksOf_length] at hql
    exact hql
  · intro a y1 b y2 he
    simp at he
  · exact h.wroot
  · refine frame_withNode hF1 hqn1 htq (addAll_leaf i nq _) (fun n0 hs => ?_)
    obtain ⟨-, -, he⟩ := frame_overlay_ext hF1 hqn1 htq hs
    exact addAll_ext (prim_timesBefore (hb.times q n0 hs)) he _
  · refine balancedAll_withNode hB1 hqn1 htq (addAll_leaf i nq _) (fun hl c y hy => ?_)
    rw [addAll_leaf] at hl
    rcases (addAll_key_mem _ nq).mp (ts_key_mem_ksOf hy) with hk | hk
    · obtain ⟨-, -, hkk⟩ := hB1 q _ (treeOf_obj_overlay i s hqn1 htq)
      exact hkk hl c y hk
    · simp only [List.mem_singleton, Prod.mk.injEq] at hk
      rw [hk.2, hT1, hwq]
      refine ⟨⟨p.keyLevel g hh, n.leaf, ksOf r⟩, by simp [Tree.set], ?_⟩
      show p.keyLevel g hh + 1 = wLevel s w q
      rw [← hlev, hlq]
  · refine putBooks_withNode hK1 hqn1 htq (addAll_leaf i nq _) ?_ ?_
    · obtain ⟨rest', hr'⟩ := addAll_first (i := i) hnq [(k1, w.next)]
      rw [hr', hnq]
      rfl
    · intro t ht
      exact addAll_timesLe (ts_timesLe_of (h.books.times q nq hqn)) _ t (ts_time_mem_ksOf ht)

/-- After the parent's step: x, which that step leaves as it was and does not
reach, is cut back to its node of before (`toPrev`): the frame holds again. -/
theorem wdt_parentPost {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    (hb : Books i base s tp) {d : Nat} {x : NodeId} {w : MW} {n V last : MNode}
    {C : List (Key × Nat)} (h : CasPreD p i base s tp w (d + 1) x n V last C)
    (hnt : n.firstTime ≠ some i) {W1 W1q W3 : MW}
    (hI3 : PInv p i base s tp none C W3) (hcp : CascadePost i s W1 W1q W3 d)
    (hW1n : ∀ y m, w.nodes.lookup y = some m → W1.nodes.lookup y = some m)
    (hW1p : W1.path = w.path) (hW1next : w.next + 2 ≤ W1.next)
    (hxnot : x ∉ reachOf i s W1q)
    (hreach : ∀ z ∈ reachOf i s W1q, z ∈ reachOf i s (w.withNode x V) ∨ z = w.next) :
    W3.nodes.lookup x = some n ∧
      CasPostD p i base s tp w (d + 1) x V C () (W3.withNode x (n.toPrev (i - 1))) := by
  have htx := wdt_taken h
  have hB := h.wbal
  have hx := h.look
  obtain ⟨c0, hon⟩ := h.on
  have hxnext : x < w.next := h.books.ids.1 x n hx
  have hx3 : W3.nodes.lookup x = some n := hcp.off x n (hW1n x n hx) (fun d' c hd' he => by
    rw [hW1p] at he
    exact ts_path_ne hB h.path h.inner hon (Nat.lt_succ_of_le hd') he rfl)
  have hxs := (h.books.first x n hx htx).mpr hnt
  have htx3 : W3.taken.contains x = false := by
    cases e : W3.taken.contains x with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨m, hm, hmx⟩ := List.mem_map.mp (hI3.books.taken x e)
      have hbm := (hI3.books.ids.2.2.1 m hm).2
      rw [hmx] at hbm
      rw [(hb.ids x hbm).1] at hxs
      cases hxs
  refine ⟨hx3, fun _ => ?_⟩
  have hT4 : treeOf i s (W3.withNode x (n.toPrev (i - 1))) =
      (treeOf i s W3).set x (.key ⟨wLevel s W3 x, n.leaf, ksOf (n.toPrev (i - 1))⟩) :=
    treeOf_withNode i s _ htx3
  have hx3r : x ∉ reachAt (treeOf i s W3) ((treeOf i s W3).fuel W3.top.rootKey) W3.top.rootKey := by
    intro hm
    rcases hcp.reach x hm with e | e
    · exact hxnot e
    · exact absurd (Nat.lt_of_lt_of_le hxnext (Nat.le_trans (Nat.le_add_right _ 2)
        (Nat.le_trans hW1next e))) (Nat.lt_irrefl x)
  have hsame4 : ∀ z, z ≠ x → (treeOf i s (W3.withNode x (n.toPrev (i - 1)))).obj z =
      (treeOf i s W3).obj z := by
    intro z hz; rw [hT4]; simp [Tree.set, hz]
  have ha : ∀ z ∈ reachAt (treeOf i s W3) ((treeOf i s W3).fuel W3.top.rootKey) W3.top.rootKey,
      (treeOf i s (W3.withNode x (n.toPrev (i - 1)))).obj z = (treeOf i s W3).obj z :=
    fun z hz => hsame4 z (fun e => hx3r (e ▸ hz))
  have hs4 : ∀ z, ((treeOf i s W3).obj z).isSome = true →
      ((treeOf i s (W3.withNode x (n.toPrev (i - 1)))).obj z).isSome = true := by
    intro z hz
    by_cases e : z = x
    · rw [e, hT4]; simp [Tree.set]
    · rw [hsame4 z e]; exact hz
  have hr3 : W3.top.rootKey ≠ x := fun e => hx3r (e ▸ tc_self _ _ _)
  have hR : reachAt (treeOf i s (W3.withNode x (n.toPrev (i - 1))))
      ((treeOf i s (W3.withNode x (n.toPrev (i - 1)))).fuel W3.top.rootKey) W3.top.rootKey =
      reachAt (treeOf i s W3) ((treeOf i s W3).fuel W3.top.rootKey) W3.top.rootKey := by
    rw [show (treeOf i s (W3.withNode x (n.toPrev (i - 1)))).fuel W3.top.rootKey =
      (treeOf i s W3).fuel W3.top.rootKey by simp only [Tree.fuel, hsame4 _ hr3]]
    exact reachAt_agree _ _ ha
  obtain ⟨hfst, htimes⟩ := ts_old hI3.books hx3 htx3 hnt
  refine ⟨⟨?_, hI3.sound.agree ha hs4, frame_withNode hI3.frame hx3 htx3 rfl
      (ts_toPrev_ext hb hI3.frame hx3 htx3), hI3.top, ?_,
      putBooks_withNode (n' := n.toPrev (i - 1)) hI3.books hx3 htx3 rfl hfst htimes⟩,
    ⟨hcp.path.trans hW1p, ?_, Nat.le_trans (Nat.le_trans (Nat.le_add_right _ 2) hW1next) hcp.next,
      ?_⟩⟩
  · rw [hT4]; exact hI3.root
  · refine balancedAll_withNode hI3.balanced hx3 htx3 (rfl : (n.toPrev (i - 1)).leaf = n.leaf)
      (fun hl c y hy => ?_)
    obtain ⟨-, -, hk⟩ := hI3.balanced x _ (treeOf_obj_overlay i s hx3 htx3)
    exact hk hl c y (ts_key_mem_ksOf (ts_mem_toPrev hy))
  · intro y m hy hny
    have hyx : y ≠ x := fun e => hny (d + 1) c0 (Nat.le_refl _) (e ▸ hon)
    have := hcp.off y m (hW1n y m hy) (fun d' c hd' he => hny d' c (Nat.le_succ_of_le hd')
      (hW1p ▸ he))
    show (SIS.Tree.upsert W3.nodes x _).lookup y = some m
    rw [lookup_upsert_ne _ _ hyx]
    exact this
  · intro z hz
    have hz3 : z ∈ reachOf i s W3 := by
      unfold reachOf at hz ⊢
      rw [← hR]
      exact hz
    rcases hcp.reach z hz3 with e | e
    · rcases hreach z e with e' | e'
      · exact Or.inl e'
      · exact Or.inr (Nat.le_of_eq e'.symm)
    · exact Or.inr (Nat.le_trans (Nat.le_trans (Nat.le_add_right _ 2) hW1next) e)

/-! ## 5. The steps of `handleFullWith` -/

/-- `replaceOrAdd` on `last` with nothing to insert: no error, the same state,
and a node r with the live klongs of V, well formed, within the node size,
that starts with a time klong of i and has no time after i; its key klongs are
V's. -/
theorem wdt_wp_replace {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} (hp : ParamsOK p) {depth : Nat} {x : NodeId} {w : MW} {n V last : MNode}
    {C : List (Key × Nat)} {compact : Bool} (h : CasPreD p i base s tp w depth x n V last C)
    (hcase : (compact = true ∧ (live (ksOf V)).length + 1 ≤ p.M) ∨
      (compact = false ∧ last.size ≤ p.splitAbove))
    {w0 : MW} {k : MNode → SIS.Tree.M Unit} {post : Unit → MW → Prop}
    (hk : ∀ r : MNode, live (ksOf r) = live (ksOf V) →
      klongsWf (ksOf r) = true → r.size ≤ p.M →
      (∀ c y, Klong.key c y ∈ ksOf r → Klong.key c y ∈ ksOf V) →
      (∃ rest, r.ks = .time i :: rest) → TimesLe r i →
      WP (k r) { p := p, i := i, view := v } w0 post) :
    WP (SIS.Tree.replaceOrAdd last [] >>= k) { p := p, i := i, view := v } w0 post := by
  obtain ⟨r, hrun, -, hrwf, hrlive, hrf, hrt, -, hrsize, hrkeys⟩ :=
    replaceOrAdd_spec ({ p := p, i := i, view := v } : Ctx) w0 (live_sorted _) h.lastKs []
  rw [ts_wp_bind_ok hrun]
  refine hk r hrlive hrwf ?_ ?_ hrf hrt
  · have hlen : last.size = (live (ksOf V)).length + 1 := by
      rw [← ksOf_length, h.lastKs]
      simp
    simp only [List.length_nil, Nat.add_zero] at hrsize
    rcases hcase with ⟨-, hc⟩ | ⟨-, hc⟩
    · omega
    · have := hp.splitHi
      omega
  · intro c y hk
    rcases hrkeys c y hk with e | e
    · exact ts_live_mem_key e
    · simp at e

/-! ## 6. The statement -/

/-- `handleFullWith` with nothing to insert and a time split, for any step
`up` of the parent that meets the put's statement. -/
theorem wdt_handleFullWith {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} (hp : ParamsOK p) (hb : Books i base s tp) {depth : Nat} {x : NodeId}
    {w : MW} {n V last : MNode} {C : List (Key × Nat)}
    {up : NodeId → List (Nat × NodeId) → SIS.Tree.M Unit} {compact : Bool}
    (h : CasPreD p i base s tp w depth x n V last C)
    (hup : ∀ d, depth = d + 1 → UpOk p i base s tp v up d)
    (hcase : (compact = true ∧ (live (ksOf V)).length + 1 ≤ p.M) ∨
      (compact = false ∧ last.size ≤ p.splitAbove)) :
    WP (SIS.Tree.handleFullWith up depth x [] last compact)
      { p := p, i := i, view := v } w (CasPostD p i base s tp w depth x V C) := by
  have hx := h.look
  have htx := wdt_taken h
  have hT := h.wtop
  have hB := h.wbal
  obtain ⟨g, hh, hg, -⟩ := h.books.levels x n hx htx
  obtain ⟨c0, hon⟩ := h.on
  have hspl : (!compact && decide (last.size > p.splitAbove)) = false := by
    rcases hcase with ⟨rfl, -⟩ | ⟨rfl, hle⟩
    · rfl
    · simp only [Bool.not_false, Bool.true_and, decide_eq_false_iff_not]
      omega
  unfold SIS.Tree.handleFullWith
  rw [ts_wp_bind_ok (a := ({ p := p, i := i, view := v } : Ctx)) rfl]
  rw [ts_wp_bind_ok (getNode_hit _ hx)]
  rw [ts_wp_bind_ok (ghOf_hit _ hx hg)]
  cases hnt : (n.firstTime == some i)
  · have hnt' : n.firstTime ≠ some i := by simpa using hnt
    cases depth with
    | zero =>
      rw [ts_wp_bind_ok (parentAt_zero _ _)]
      simp only [hspl, Bool.false_eq_true, ↓reduceIte, Bool.not_false]
      rw [ts_wp_bind_ok rfl]
      refine ts_wp_ite_note (fun T => ?_)
      refine wdt_wp_replace hp h hcase (fun r hrl hrwf hrs hrk hrf hrt => ?_)
      refine ts_wp_ite_note (fun T' => ?_)
      rw [ts_wp_bind_ok (newKey_eq _ _ _ _ _ _), ts_wp_bind_ok (setMadeFor_some _ _ _ _),
        ts_wp_bind_ok (note_eq _ _ _)]
      refine (ts_wp_bind_ok (newSuperRoot_eq (s := s) (tp := tp) v _ ?_)).mpr ?_
      · exact hT
      refine (ts_wp_bind_ok (getNode_hit (n := n) _ ?_)).mpr ?_
      · rw [(afterSuperRoot_fields _ _ _ _).2.2.1]
        exact prim_lookup_append_some _ hx
      rw [ts_wp_ok (putNode_eq _ _ _ _)]
      exact wdt_root hb h hnt' hg hrl hrwf hrs hrk hrf hrt _ _
    | succ d =>
      obtain ⟨c0', u0, k1, x', nu, e1, e2, -⟩ := h.path.links d (Nat.lt_succ_self d)
      rw [hon] at e2
      cases e2
      obtain ⟨nq, hqn, -⟩ := h.path.lookup (Nat.le_succ d) e1
      rw [ts_wp_bind_ok (parentAt_succ _ e1)]
      rw [ts_wp_bind_ok (getNode_hit _ hqn)]
      rw [ts_wp_bind_ok rfl]
      simp only [hspl, Bool.false_eq_true, ↓reduceIte, Bool.not_false]
      refine ts_wp_ite_note (fun T => ?_)
      refine wdt_wp_replace hp h hcase (fun r hrl hrwf hrs hrk hrf hrt => ?_)
      refine ts_wp_ite_note (fun T' => ?_)
      rw [ts_wp_bind_ok (newKey_eq _ _ _ _ _ _), ts_wp_bind_ok (setMadeFor_some _ _ _ _),
        ts_wp_bind_ok (note_eq _ _ _)]
      refine (ts_wp_bind_ok (klongAt_eq (k := k1) (x := x) _ ?_)).mpr ?_
      · exact hon
      rw [wp_bind]
      obtain ⟨hpre, hxnot, hreach⟩ := wdt_parentPre hb h hg hrl hrwf hrs hrk hrf hrt e1 hqn hon
        ((w.next, x) :: w.madeFor) ("split.time1" :: T')
      refine WP.mono (hup d rfl u0 [(k1, w.next)] _ nq C hpre) (fun _ W3 hpost => ?_)
      by_cases hout : W3.outside = []
      · obtain ⟨hI3, hcp⟩ := hpost hout
        obtain ⟨hx3, hfin⟩ := wdt_parentPost hb h hnt' hI3 hcp
          (fun y m hy => prim_lookup_append_some _ hy) rfl (Nat.le_refl _) hxnot hreach
        rw [ts_wp_bind_ok (getNode_hit _ hx3), ts_wp_ok (putNode_eq _ _ _ _)]
        exact hfin
      · intro _ W4 hrun hout4
        exact absurd ((ts_getNode_put_outside hrun).symm.trans hout4) hout
  · have hnt' : n.firstTime = some i := by simpa using hnt
    have hAo : ∀ z, z ≠ x → (treeOf i s (w.withNode x V)).obj z = (treeOf i s w).obj z := by
      intro z hz
      rw [wdt_treeA h]
      simp [Tree.set, hz]
    have hxr := ts_path_reach (w := w) h.vsound.good hB h.path h.inner hon hAo depth
      (Nat.le_refl _) c0 x hon
    cases depth with
    | zero =>
      rw [ts_wp_bind_ok (parentAt_zero _ _), ts_wp_bind_ok rfl]
      simp only [hspl, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
      refine ts_wp_ite_note (fun T => ?_)
      rw [ts_wp_bind_ok (note_eq _ _ _)]
      refine wdt_wp_replace hp h hcase (fun r hrl hrwf hrs hrk hrf hrt => ?_)
      refine ts_wp_ite_note (fun T' => ?_)
      rw [ts_wp_bind_ok (putNode_eq _ _ _ _), wp_pure]
      exact wdt_inPlace h hnt' hrl hrwf hrs hrk hrf hrt hxr _
    | succ d =>
      obtain ⟨c0', u0, -, -, -, e1, -⟩ := h.path.links d (Nat.lt_succ_self d)
      obtain ⟨nq, hqn, -⟩ := h.path.lookup (Nat.le_succ d) e1
      rw [ts_wp_bind_ok (parentAt_succ _ e1), ts_wp_bind_ok (getNode_hit _ hqn),
        ts_wp_bind_ok rfl]
      simp only [hspl, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
      refine ts_wp_ite_note (fun T => ?_)
      rw [ts_wp_bind_ok (note_eq _ _ _)]
      refine wdt_wp_replace hp h hcase (fun r hrl hrwf hrs hrk hrf hrt => ?_)
      refine ts_wp_ite_note (fun T' => ?_)
      rw [ts_wp_bind_ok (putNode_eq _ _ _ _), wp_pure]
      exact wdt_inPlace h hnt' hrl hrwf hrs hrk hrf hrt hxr _

theorem handleFullD_time {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} (hp : ParamsOK p) (hb : Books i base s tp) {depth : Nat} {x : NodeId}
    {w : MW} {n V last : MNode} {C : List (Key × Nat)} {compact : Bool}
    (h : CasPreD p i base s tp w depth x n V last C)
    (hcase : (compact = true ∧ (live (ksOf V)).length + 1 ≤ p.M) ∨
      (compact = false ∧ last.size ≤ p.splitAbove)) :
    WP (SIS.Tree.handleFull depth x last compact) { p := p, i := i, view := v } w
      (CasPostD p i base s tp w depth x V C) := by
  unfold SIS.Tree.handleFull
  refine wdt_handleFullWith hp hb h (fun d hd => ?_) hcase
  subst hd
  exact appendKlongs_spec hp hb d

end Contract
