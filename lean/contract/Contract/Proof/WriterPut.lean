/-
The contract package (bergdb 030-10): a put of a key of one segment. The
recursion up the path (`appendKlongs_spec`, from the two forms of
`handleFullWith`); the descent to the segment leaf (`descendLte`), which
gives the key access path and the key's route; and the operation: `putKv` of
a put of a one-segment key keeps `MidP` (`putKv_put1`). Then: a transaction
of such puts meets the writer's contract (`writerMeets_put1`), and a run of
such transactions is a history that meets `MeetsTop` (`runs_meetsTop_put1`).
-/
import Contract.Proof.WriterTimeSplit
import Contract.Proof.WriterSpaceSplit
import Contract.Proof.WriterRun

namespace Contract

open SIS (View)
open SIS.Tree (Ctx)
open SIS.Check (BVal)

/-! ## 1. Helpers: steps with a known result; a node that fits -/

theorem wput_ok {α β : Type} {f : SIS.Tree.M α} {g : α → SIS.Tree.M β} {c : Ctx} {w w' : MW}
    {a : α} {post : β → MW → Prop} (h : f c w = .ok (a, w')) (hg : WP (g a) c w' post) :
    WP (f >>= g) c w post := by
  rw [wp_bind]
  intro r u hr
  rw [h] at hr
  simp only [Except.ok.injEq, Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  exact hg

theorem wput_read {β : Type} {g : Ctx → SIS.Tree.M β} {c : Ctx} {w : MW}
    {post : β → MW → Prop} (hg : WP (g c) c w post) : WP (read >>= g) c w post :=
  wput_ok (f := read) (a := c) (w' := w) rfl hg

theorem wput_nodeOk_le {M M' : Nat} {T : Tree} {m : KNode} (h : nodeOk ⟨M'⟩ T m = true)
    (hl : m.ks.length ≤ M) : nodeOk ⟨M⟩ T m = true := by
  simp only [nodeOk, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  exact ⟨⟨hl, h.1.2⟩, h.2⟩

/-- A tree sound with x over its size is sound with no node over it, if x
fits the size. -/
theorem wput_sound_fit {M : Nat} {x : NodeId} {T : Tree} {r : NodeId} {C : List (Key × Nat)}
    (h : Sound M (some x) T r C) (hx : ∀ m, T.obj x = some (.key m) → m.ks.length ≤ M) :
    Sound M none T r C := by
  refine ⟨h.key, h.good, fun z hz m hm => ?_, h.holds, h.tree⟩
  have := h.nodes z hz m hm
  by_cases e : z = x
  · subst e
    simp only [ite_true] at this
    simpa using wput_nodeOk_le this (hx m hm)
  · have e' : ¬ (some x = some z) := fun h' => e (Option.some.inj h').symm
    simpa [e'] using this

theorem wput_taken {i : Time} {s : Tree} {w : MW} {x : NodeId} {o : Obj}
    (h : (treeOf i s w).obj x = some o) : w.taken.contains x = false := by
  cases e : w.taken.contains x
  · rfl
  · simp only [treeOf, e, ↓reduceIte] at h
    cases h

/-- `PInv` with x over its size is `PInv` with no node over it, if x fits. -/
theorem wput_pinv_fit {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {C : List (Key × Nat)} {w : MW} {x : NodeId} {n : MNode}
    (hI : PInv p i base s tp (some x) C w) (hx : w.nodes.lookup x = some n)
    (hsz : n.size ≤ p.M) : PInv p i base s tp none C w := by
  refine ⟨hI.root, wput_sound_fit hI.sound (fun m hm => ?_), hI.frame, hI.top, hI.balanced,
    hI.books⟩
  rw [treeOf_obj_overlay i s hx (wput_taken hm)] at hm
  cases hm
  show (ksOf n).length ≤ p.M
  rw [ksOf_length]
  exact hsz

/-! ## 2. The recursion up the path -/

/-- `CascadePost` of a step that only sets its own node, not the path's
others. -/
theorem wput_cascade_self {i : Time} {s : Tree} {w : MW} {x : NodeId} {m : MNode} {depth : Nat}
    (hon : ∃ c0, w.path[depth]? = some (c0, x)) :
    CascadePost i s w (w.withNode x m) (w.withNode x m) depth := by
  refine ⟨rfl, fun y n hy hoff => ?_, Nat.le_refl _, fun z hz => Or.inl hz⟩
  obtain ⟨c0, hc0⟩ := hon
  have hyx : y ≠ x := fun e => hoff depth c0 (Nat.le_refl _) (e ▸ hc0)
  rw [MW.withNode, lookup_upsert_ne _ _ hyx]
  exact hy

open SIS.Tree in
/-- `appendKlongs`, one step unfolded (the old proofs' `appendKlongs_step_dead`). -/
theorem wput_appendKlongs_eq (depth : Nat) (x : NodeId) (ins : List (Nat × NodeId)) :
    appendKlongs depth x ins = (do
      let c ← read
      let n ← getNode x
      let up : NodeId → List (Nat × NodeId) → M Unit := match depth with
        | 0 => fun _ _ => throw "corrupt: a split's parent above depth 0"
        | d + 1 => fun q more => appendKlongs d q more
      if n.size + ins.length + 1 > c.p.M then
        handleFullWith up depth x ins (n.lastVersion c.i)
      else if deadOver c.p (ins.foldl (fun n (cv, y) => n.add c.i (.key cv y)) n) then
        handleFullWith up depth x ins (n.lastVersion c.i) true
      else addKeys x ins) := by
  cases depth <;> rfl

/-- One level of `appendKlongs`, given the levels above it. -/
theorem wput_append_step {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} (hp : ParamsOK p) (hb : Books i base s tp) (depth : Nat)
    (hup : ∀ d, depth = d + 1 →
      UpOk p i base s tp v (fun q ins => SIS.Tree.appendKlongs d q ins) d) :
    UpOk p i base s tp v (fun q ins => SIS.Tree.appendKlongs depth q ins) depth := by
  intro x ins w n C h
  simp only []
  rw [wput_appendKlongs_eq]
  refine wput_read (wput_ok (getNode_hit _ h.look) ?_)
  dsimp only
  split
  · by_cases h2 : (n.lastVersion i).size ≤ p.splitAbove
    · refine handleFull_time hp hb h ?_ (Or.inr ⟨rfl, h2⟩)
      intro d hd; subst hd; exact hup d rfl
    · refine handleFull_space hp hb h ?_ (by omega)
      intro d hd; subst hd; exact hup d rfl
  · next h1 =>
    split
    · refine handleFull_time hp hb h ?_ (Or.inl ⟨rfl, by omega⟩)
      intro d hd; subst hd; exact hup d rfl
    · unfold SIS.Tree.addKeys
      refine wput_read (wput_ok (getNode_hit _ h.look) ?_)
      intro r w' hr
      rw [putNode_eq] at hr
      simp only [Except.ok.injEq, Prod.mk.injEq] at hr
      obtain ⟨-, rfl⟩ := hr
      show CasPost p i base s tp w depth x n ins C () (w.withNode x (addAll i n ins))
      intro _
      have hsz : (addAll i n ins).size ≤ p.M := by
        have := addAll_size i n ins
        omega
      exact ⟨wput_pinv_fit h.hyp (lookup_upsert_self _ _ _) hsz, wput_cascade_self h.on⟩

/-- `appendKlongs` meets the statement at every depth. -/
theorem appendKlongs_spec {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} (hp : ParamsOK p) (hb : Books i base s tp) :
    ∀ d, UpOk p i base s tp v (fun q ins => SIS.Tree.appendKlongs d q ins) d := by
  intro d
  induction d with
  | zero => exact wput_append_step hp hb 0 (fun d h => absurd h (by omega))
  | succ d ih =>
    exact wput_append_step hp hb (d + 1) (fun d' h => by
      obtain rfl : d = d' := by omega
      exact ih)

/-! ## 3. The descent to the segment leaf -/

open SIS.Tree in
theorem wput_descend_zero (cv : Nat) (x : NodeId) :
    descendLte cv 0 x =
      throw s!"bounds: a descent from key node {x} went below the height bound" := rfl

open SIS.Tree in
theorem wput_descend_succ (cv f : Nat) (x : NodeId) :
    descendLte cv (f + 1) x = (do
      let c ← read
      let n ← getNode x
      if n.leaf then pure x else
        match n.searchLte c.i cv with
        | none => throw s!"corrupt: key node {x}, not a segment leaf, has no klong at or \
            below the key at {c.i}"
        | some fd =>
          pathAdd (some fd.c) fd.y
          descendLte cv f fd.y) := rfl

theorem wput_good_obj {T : Tree} {x : NodeId} {lo : Nat} {hi : Option Nat} (h : Good T x lo hi) :
    ∃ m, T.obj x = some (.key m) := by
  cases h with
  | mk x lo hi n hobj => exact ⟨n, hobj⟩

/-- Before `descendLte` from node x at `depth` of the key access path, x not
read yet: `PInv` with no node over its size; the path ends with x and starts
at the space root; each node above x is an inner node of the overlay whose
live klong names the next node; and a route of the key [cv] from x is one
from the space root. -/
structure DescInv (p : MParams) (i : Time) (base : NodeId) (s : Tree) (tp : Top)
    (C : List (Key × Nat)) (cv : Nat) (w : MW) (depth : Nat) (x : NodeId) : Prop where
  inv : PInv p i base s tp none C w
  len : w.path.length = depth + 1
  last : ∃ c0, w.path[depth]? = some (c0, x)
  root : w.path[0]? = some (none, w.top.rootKey)
  nodes : ∀ d, d < depth → ∃ c u n, w.path[d]? = some (c, u) ∧ w.nodes.lookup u = some n ∧
    w.taken.contains u = false ∧ n.leaf = false
  links : ∀ d, d < depth → ∃ c0 u c y nu, w.path[d]? = some (c0, u) ∧
    w.path[d + 1]? = some (some c, y) ∧ (treeOf i s w).obj u = some (.key nu) ∧
    (c, y) ∈ live nu.ks
  route : ∀ q, Route (treeOf i s w) x [cv] q [cv] →
    Route (treeOf i s w) w.top.rootKey [cv] q [cv]

/-- After the descent from the state w: the map and the super root as in w;
`PInv`; the node returned is a segment leaf of the overlay, the last of the
path; the path is a path of the tree, of inner nodes above the leaf; and the
key [cv] is routed to the leaf from the space root. -/
def DescPost (p : MParams) (i : Time) (base : NodeId) (s : Tree) (tp : Top)
    (C : List (Key × Nat)) (cv : Nat) (w : MW) : NodeId → MW → Prop :=
  fun leaf w' => treeOf i s w' = treeOf i s w ∧ w'.top = w.top ∧
    PInv p i base s tp none C w' ∧ (∃ nl, w'.nodes.lookup leaf = some nl ∧ nl.leaf = true) ∧
    (∃ c0, w'.path[w'.path.length - 1]? = some (c0, leaf)) ∧
    PathOk i s w' (w'.path.length - 1) ∧ PathInner w' (w'.path.length - 1) ∧
    Route (treeOf i s w') w'.top.rootKey [cv] leaf [cv]

theorem wput_timesLe {p : MParams} {i : Time} {base : NodeId} {s : Tree} {w : MW} {x : NodeId}
    {n : MNode} (hk : PutBooks p i base s w) (hx : w.nodes.lookup x = some n) : TimesLe n i :=
  fun t' h' => hk.times x n hx t' (mem_map_kOf_time.mp h')

/-- The descent: from a state with `DescInv`, every result of `descendLte`
meets `DescPost`; the fuel runs out only with an error. -/
theorem wput_descend {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} {C : List (Key × Nat)} {cv : Nat} (hs : Shows p v z s tp)
    (hb : Books i base s tp) :
    ∀ (f : Nat) (w : MW) (depth : Nat) (x : NodeId), DescInv p i base s tp C cv w depth x →
      WP (SIS.Tree.descendLte cv f x) { p := p, i := i, view := v } w
        (DescPost p i base s tp C cv w) := by
  intro f
  induction f with
  | zero =>
    intro w depth x _
    rw [wput_descend_zero]
    exact wp_throw _ _ _ _
  | succ f ih =>
    intro w depth x hD
    rw [wput_descend_succ]
    refine wput_read ?_
    have hrx := hD.route x (Route.here x [cv])
    obtain ⟨⟨lo, hi, hGx⟩, hxr0⟩ := hrx.tc_target hD.inv.sound.good
    obtain ⟨m, hxm⟩ := wput_good_obj hGx
    have hxr : x ∈ reach (treeOf i s w) := by
      rw [reach_of_root hD.inv.root]
      exact hxr0
    obtain ⟨n, w1, hget, hks, hleaf, hlk1, hT1, hI1, hw1, -⟩ :=
      getNode_spec hs hb hD.inv hxm hxr
    refine wput_ok hget ?_
    have hfield : w1.path = w.path ∧ w1.top = w.top ∧ w1.taken = w.taken ∧
        ∀ u n0, w.nodes.lookup u = some n0 → w1.nodes.lookup u = some n0 := by
      rcases hw1 with rfl | ⟨-, gh, rfl⟩
      · exact ⟨rfl, rfl, rfl, fun _ _ h => h⟩
      · exact ⟨rfl, rfl, rfl, fun _ _ h => prim_lookup_append_some _ h⟩
    obtain ⟨hp1, htop1, htk1, hext1⟩ := hfield
    have htx : w1.taken.contains x = false := by rw [htk1]; exact wput_taken hxm
    obtain ⟨c0, hc0⟩ := hD.last
    have hnodes1 : ∀ d, d < depth → ∃ c u n, w1.path[d]? = some (c, u) ∧
        w1.nodes.lookup u = some n ∧ w1.taken.contains u = false ∧ n.leaf = false := by
      intro d hd
      obtain ⟨c, u, n0, h1, h2, h3, h4⟩ := hD.nodes d hd
      exact ⟨c, u, n0, by rw [hp1]; exact h1, hext1 u n0 h2, by rw [htk1]; exact h3, h4⟩
    have hlinks1 : ∀ d, d < depth → ∃ c0 u c y nu, w1.path[d]? = some (c0, u) ∧
        w1.path[d + 1]? = some (some c, y) ∧ (treeOf i s w1).obj u = some (.key nu) ∧
        (c, y) ∈ live nu.ks := by
      intro d hd
      rw [hp1, hT1]
      exact hD.links d hd
    split
    · next hl =>
      rw [wp_pure]
      have hlen : w1.path.length - 1 = depth := by rw [hp1, hD.len]; omega
      refine ⟨hT1, htop1, hI1, ⟨n, hlk1, hl⟩, ⟨c0, by rw [hlen, hp1]; exact hc0⟩, ?_, ?_, ?_⟩
      · rw [hlen]
        refine ⟨by rw [hp1, htop1]; exact hD.root, fun d hd => ?_, fun d hd => hlinks1 d hd⟩
        rcases Nat.lt_or_eq_of_le hd with hd | rfl
        · obtain ⟨c, u, n0, h1, h2, h3, -⟩ := hnodes1 d hd
          exact ⟨c, u, n0, h1, h2, h3⟩
        · exact ⟨c0, x, n, by rw [hp1]; exact hc0, hlk1, htx⟩
      · rw [hlen]
        intro d c u n' hd hu hn'
        obtain ⟨c', u', n0, h1, h2, -, h4⟩ := hnodes1 d hd
        rw [hu] at h1
        cases h1
        rw [h2] at hn'
        cases hn'
        exact h4
      · rw [hT1, htop1]
        exact hrx
    · next hl =>
      split
      · exact wp_throw _ _ _ _
      · next fd hfd =>
        obtain ⟨hm, hle, hmax⟩ := searchLte_some (wput_timesLe hI1.books hlk1) hfd
        rw [hks] at hm hmax
        refine wput_ok (pathAdd_eq _ _ _ _) ?_
        let w2 : MW := { w1 with path := w1.path ++ [(some fd.c, fd.y)] }
        have hT2 : treeOf i s w2 = treeOf i s w := hT1
        have hlen1 : w1.path.length = depth + 1 := by rw [hp1]; exact hD.len
        have hpa : ∀ d, d < depth + 1 → w2.path[d]? = w1.path[d]? := by
          intro d hd
          exact List.getElem?_append_left (by omega)
        have hpb : w2.path[depth + 1]? = some (some fd.c, fd.y) := by
          show (w1.path ++ [(some fd.c, fd.y)])[depth + 1]? = _
          rw [List.getElem?_append_right (by omega), hlen1]
          simp
        have hD2 : DescInv p i base s tp C cv w2 (depth + 1) fd.y := by
          refine ⟨hI1.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl, ?_, ⟨_, hpb⟩, ?_, ?_, ?_, ?_⟩
          · show (w1.path ++ [(some fd.c, fd.y)]).length = depth + 1 + 1
            rw [List.length_append, hlen1]
            rfl
          · rw [hpa 0 (by omega), hp1]
            exact htop1 ▸ hD.root
          · intro d hd
            rw [hpa d hd]
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hd) with hd | rfl
            · exact hnodes1 d hd
            · exact ⟨c0, x, n, by rw [hp1]; exact hc0, hlk1, htx, by
                cases e : n.leaf
                · rfl
                · exact absurd e hl⟩
          · intro d hd
            rw [hpa d hd]
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hd) with hd | rfl
            · rw [hpa (d + 1) (by omega)]
              exact hlinks1 d hd
            · exact ⟨c0, x, fd.c, fd.y, m, by rw [hp1]; exact hc0, hpb, by rw [hT2]; exact hxm,
                hm⟩
          · intro q hq
            rw [hT2] at hq ⊢
            show Route (treeOf i s w) w1.top.rootKey [cv] q [cv]
            rw [htop1]
            refine hD.route q (Route.inner x m fd.c fd.y cv [] q [cv] hxm ?_ hm hle hmax hq)
            rw [← hleaf]
            cases e : n.leaf
            · rfl
            · exact absurd e hl
        refine (ih w2 (depth + 1) fd.y hD2).mono ?_
        rintro leaf w' ⟨h1, h2, h3⟩
        exact ⟨h1.trans hT2, h2.trans htop1, h3⟩

/-- The descent from the space root, as `setValue` starts it: from a state
with `PInv` whose key access path is the space root alone. -/
theorem wput_descend_root {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} {C : List (Key × Nat)} {cv : Nat} (hs : Shows p v z s tp)
    (hb : Books i base s tp) {w : MW} (hI : PInv p i base s tp none C w)
    (hpath : w.path = [(none, w.top.rootKey)]) (f : Nat) :
    WP (SIS.Tree.descendLte cv f w.top.rootKey) { p := p, i := i, view := v } w
      (DescPost p i base s tp C cv w) :=
  wput_descend hs hb f w 0 _ ⟨hI, by rw [hpath]; rfl, ⟨none, by rw [hpath]; rfl⟩,
    by rw [hpath]; rfl, fun d hd => absurd hd (Nat.not_lt_zero d),
    fun d hd => absurd hd (Nat.not_lt_zero d), fun _ hq => hq⟩

/-! ## 4. The put -/

theorem wput_set_isSome {T : Tree} {a : NodeId} {o : Obj} {y : NodeId}
    (h : (T.obj y).isSome = true) : ((T.set a o).obj y).isSome = true := by
  simp only [Tree.set]
  split
  · rfl
  · exact h

/-- The state after the new value, with the value's klong added to the
segment leaf, meets `PInv` with the leaf over its size and holds the keys
with the put applied (`Sound.put`); and the leaf, of a sound tree, is well
formed and fits a node. -/
theorem wput_put_fact {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {C : List (Key × Nat)} (hb : Books i base s tp) {w : MW} {leaf : NodeId} {nl : MNode}
    {cv h : Nat} (hI : PInv p i base s tp none C w) (hlk : w.nodes.lookup leaf = some nl)
    (ht : w.taken.contains leaf = false) (hl : nl.leaf = true)
    (hr : Route (treeOf i s w) w.top.rootKey [cv] leaf [cv]) (hcv : isLong cv = false) :
    PInv p i base s tp (some leaf) (mapPut [cv] h C)
      ((w.afterNewValue h).withNode leaf (nl.add i (.key cv w.next))) ∧
      klongsWf (ksOf nl) = true ∧ nl.size ≤ p.M := by
  obtain ⟨hTv, hsv, hnv, hvv, htv, -⟩ := treeOf_fresh hb hI.books (Nat.le_refl w.next)
  have hlv : leaf ≠ w.next := Nat.ne_of_lt (hI.books.ids.1 leaf nl hlk)
  have hAx := treeOf_obj_overlay i s hlk ht
  have hreach := (hr.tc_target hI.sound.good).2
  have hok := hI.sound.nodes leaf hreach _ hAx
  simp only [reduceCtorEq, ite_false] at hok
  have hok' := hok
  simp only [nodeOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hok'
  obtain ⟨⟨hlen, hwf⟩, hptr⟩ := hok'
  have hsz : nl.size ≤ p.M := by rw [← ksOf_length]; exact hlen
  refine ⟨?_, hwf, hsz⟩
  -- the states and their maps
  have ht4 : (w.afterNewValue h).taken.contains leaf = false := ht
  have hlk4 : (w.afterNewValue h).nodes.lookup leaf = some nl := hlk
  have hT4 : treeOf i s (w.afterNewValue h) = (treeOf i s w).set w.next (.val h) :=
    treeOf_afterNewValue i s h hnv hvv htv
  have hTW : treeOf i s ((w.afterNewValue h).withNode leaf (nl.add i (.key cv w.next))) =
      (treeOf i s (w.afterNewValue h)).set leaf (.key ⟨wLevel s (w.afterNewValue h) leaf,
        (nl.add i (.key cv w.next)).leaf, ksOf (nl.add i (.key cv w.next))⟩) :=
    treeOf_withNode i s (nl.add i (.key cv w.next)) ht4
  have hwl : wLevel s (w.afterNewValue h) leaf = wLevel s w leaf :=
    prim_wLevel_afterNewValue hlv
  have hleaf' : (nl.add i (.key cv w.next)).leaf = nl.leaf := add_leaf nl i _
  have hF4 := frame_afterNewValue h hI.frame hsv hnv hvv htv
  have hk4 := putBooks_afterNewValue hI.books h
  have hBv : (treeOf i s ((w.afterNewValue h).withNode leaf (nl.add i (.key cv w.next)))).obj
      w.next = some (.val h) := by
    rw [hTW, hT4]
    simp [Tree.set, Ne.symm hlv]
  have hBx : NodeIs (treeOf i s ((w.afterNewValue h).withNode leaf (nl.add i (.key cv w.next))))
      leaf (wLevel s w leaf) true (insertCv cv w.next (live (ksOf nl))) (p.M + 3) := by
    refine ⟨⟨wLevel s (w.afterNewValue h) leaf, (nl.add i (.key cv w.next)).leaf,
      ksOf (nl.add i (.key cv w.next))⟩, ?_, hwl, by rw [hleaf']; exact hl,
      add_key_live hwf cv w.next, ?_⟩
    · rw [hTW]; simp [Tree.set]
    · simp only [nodeOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
      refine ⟨⟨?_, add_key_wf hwf cv w.next⟩, ?_⟩
      · rw [ksOf_length]
        have := add_size nl i (.key cv w.next)
        omega
      · intro k hk
        cases k with
        | key c y =>
          rcases add_key_mem.mp hk with hk | ⟨rfl, rfl⟩
          · rw [hTW, hT4]
            exact wput_set_isSome (wput_set_isSome (hptr _ hk))
          · rw [hTW, hT4]
            simp [Tree.set, Ne.symm hlv]
        | time t => rfl
        | del b => rfl
  have hsame : ∀ z, z ≠ leaf → z ≠ w.next →
      (treeOf i s ((w.afterNewValue h).withNode leaf (nl.add i (.key cv w.next)))).obj z =
        (treeOf i s w).obj z := by
    intro z hz1 hz2
    rw [hTW, hT4]
    simp [Tree.set, hz1, hz2]
  obtain ⟨hSnd, hRch⟩ := Sound.put hI.sound hr hAx hl hcv hTv hBv hBx hsame
  have hrootW : (treeOf i s ((w.afterNewValue h).withNode leaf (nl.add i (.key cv w.next)))).root =
      some w.top.rootKey := hI.root
  refine ⟨hI.root, hSnd, ?_, hI.top, ?_, ?_⟩
  · -- the frame
    refine frame_withNode hF4 hlk4 ht4 hleaf' (fun n0 hs0 => ?_)
    obtain ⟨-, -, he⟩ := frame_overlay_ext hF4 hlk4 ht4 hs0
    exact add_ext (prim_timesBefore (hb.times leaf n0 hs0)) he _
  · -- BalancedOK, by the nodes reached
    refine Balanced.of_reach (N := [leaf, w.next]) hI.balanced (fun z hz => ?_)
      (fun z _ hz => ?_) (levels_kept_trans (levels_kept_afterNewValue i s h hsv hnv hvv htv)
        (levels_kept_withNode i s (nl.add i (.key cv w.next)) hlk4 ht4)) (fun z hz _ m hm => ?_)
    · rw [reach_of_root hrootW] at hz
      rcases hRch z hz with h1 | h1
      · left
        rw [reach_of_root hI.root]
        exact h1
      · right
        simp [h1]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
      exact hsame z hz.1 hz.2
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl
      · rw [hTW] at hm
        simp only [Tree.set, ite_true, Option.some.injEq, Obj.key.injEq] at hm
        subst hm
        have hLr : z ∈ reach (treeOf i s w) := by
          rw [reach_of_root hI.root]
          exact hreach
        obtain ⟨h1, h2, -⟩ := hI.balanced z hLr _ hAx
        refine ⟨by rw [hwl]; exact h1, by rw [hwl, hleaf']; exact h2, fun hl' => ?_⟩
        rw [hleaf', hl] at hl'
        cases hl'
      · rw [hBv] at hm
        cases hm
  · -- the books
    obtain ⟨t, rest, hr0⟩ := hI.books.timeFirst leaf nl hlk ht
    obtain ⟨rest', hr1⟩ := add_first (t := i) (.key cv w.next) hr0
    refine putBooks_withNode hk4 hlk4 ht4 hleaf' (by rw [hr1, hr0]; rfl) ?_
    exact timesLe_model (add_timesLe (wput_timesLe hI.books hlk) _ (fun t' e => by cases e))

/-- On a path of inner nodes of a sound map from the space root the levels
fall: no node is twice on it (`CasPre.nodup`). -/
theorem wput_nodup {M : Nat} {ex : Option NodeId} {C : List (Key × Nat)} {i : Time} {s : Tree}
    {w : MW} {D : Nat} (hP : PathOk i s w D) (hin : PathInner w D)
    (hS : Sound M ex (treeOf i s w) w.top.rootKey C) :
    ∀ e e' c c' u, e < e' → e' ≤ D → w.path[e]? = some (c, u) →
      w.path[e']? = some (c', u) → False := by
  have hG : ∀ d, d ≤ D → ∀ c u, w.path[d]? = some (c, u) →
      ∃ m lo hi, (treeOf i s w).obj u = some (.key m) ∧ Good (treeOf i s w) u lo hi := by
    intro d
    induction d with
    | zero =>
      intro _ c u hu
      rw [hP.root] at hu
      cases hu
      obtain ⟨m, hm⟩ := wput_good_obj hS.good
      exact ⟨m, 0, none, hm, hS.good⟩
    | succ d ih =>
      intro hd c u hu
      obtain ⟨c0, u0, c1, y, nu, h1, h2, h3, h4⟩ := hP.links d (by omega)
      rw [hu] at h2
      cases h2
      obtain ⟨m0, lo, hi, hm0, hG0⟩ := ih (by omega) c0 u0 h1
      rw [hm0] at h3
      simp only [Option.some.injEq, Obj.key.injEq] at h3
      subst h3
      obtain ⟨n0, hn0, ht0⟩ := hP.lookup (by omega) h1
      have hl0 := hin d c0 u0 n0 (by omega) h1 hn0
      have hm0l : m0.leaf = false := by
        have hm0' := hm0
        rw [treeOf_obj_overlay i s hn0 ht0] at hm0'
        simp only [Option.some.injEq, Obj.key.injEq] at hm0'
        rw [← hm0']
        exact hl0
      obtain ⟨m', lo', hi', hm', -, -, hG'⟩ := hG0.child hm0 h4 (fun h => by
        rw [hm0l] at h; cases h)
      exact ⟨m', lo', hi', hm', hG'⟩
  have hdrop : ∀ d, d < D → ∀ c u c' u' m m', w.path[d]? = some (c, u) →
      w.path[d + 1]? = some (c', u') → (treeOf i s w).obj u = some (.key m) →
      (treeOf i s w).obj u' = some (.key m') → m'.level < m.level := by
    intro d hd c u c' u' m m' h1 h2 h3 h4
    obtain ⟨c0, u0, c1, y, nu, g1, g2, g3, g4⟩ := hP.links d hd
    rw [h1] at g1
    simp only [Option.some.injEq, Prod.mk.injEq] at g1
    obtain ⟨-, rfl⟩ := g1
    rw [h2] at g2
    simp only [Option.some.injEq, Prod.mk.injEq] at g2
    obtain ⟨-, rfl⟩ := g2
    rw [h3] at g3
    simp only [Option.some.injEq, Obj.key.injEq] at g3
    subst g3
    obtain ⟨m0, lo, hi, hm0, hG0⟩ := hG d (by omega) _ _ h1
    obtain ⟨n0, hn0, ht0⟩ := hP.lookup (by omega) h1
    have hl0 := hin d _ u n0 hd h1 hn0
    have hml : m.leaf = false := by
      have h3' := h3
      rw [treeOf_obj_overlay i s hn0 ht0] at h3'
      simp only [Option.some.injEq, Obj.key.injEq] at h3'
      rw [← h3']
      exact hl0
    have hG1 : Good (treeOf i s w) u lo hi := hG0
    obtain ⟨m'', -, -, hm'', hlt, -, -⟩ := hG1.child h3 g4 (fun h => by
      rw [hml] at h; cases h)
    rw [h4] at hm''
    simp only [Option.some.injEq, Obj.key.injEq] at hm''
    subst hm''
    exact hlt
  have hdec : ∀ k e c u m, e + k + 1 ≤ D → w.path[e]? = some (c, u) →
      (treeOf i s w).obj u = some (.key m) → ∀ c' u' m', w.path[e + k + 1]? = some (c', u') →
      (treeOf i s w).obj u' = some (.key m') → m'.level < m.level := by
    intro k
    induction k with
    | zero =>
      intro e c u m he h1 h2 c' u' m' h3 h4
      exact hdrop e (by omega) c u c' u' m m' h1 h3 h2 h4
    | succ k ih =>
      intro e c u m he h1 h2 c' u' m' h3 h4
      obtain ⟨c2, u2, n2, h5, -, -⟩ := hP.nodes (e + k + 1) (by omega)
      obtain ⟨m2, -, -, h6, -⟩ := hG (e + k + 1) (by omega) c2 u2 h5
      have a := ih e c u m (by omega) h1 h2 c2 u2 m2 h5 h6
      have b := hdrop (e + k + 1) (by omega) c2 u2 c' u' m2 m' h5
        (by rw [show e + k + 1 + 1 = e + (k + 1) + 1 by omega]; exact h3) h6 h4
      omega
  intro e e' c c' u hlt hle h1 h2
  obtain ⟨m, -, -, h4, -⟩ := hG e (by omega) c u h1
  obtain ⟨k, rfl⟩ : ∃ k, e' = e + k + 1 := ⟨e' - e - 1, by omega⟩
  have := hdec k e c u m hle h1 h4 c' u m h2 h4
  omega

/-- A put of a key of one segment keeps `MidP`. -/
theorem putKv_put1 {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} (hp : ParamsOK p) (hs : Shows p v z s tp)
    (hb : Books i base s tp) {done : List Op} {w w' : MW} {b : Bool} {cv h : Nat}
    (hm : MidP p i base s tp done w) (hcv : isLong cv = false)
    (hrun : SIS.Tree.putKv (.put [cv] h) { p := p, i := i, view := v } w = .ok (b, w'))
    (hout : w'.outside = []) : MidP p i base s tp (done ++ [Op.put [cv] h]) w' := by
  suffices hW : WP (SIS.Tree.putKv (.put [cv] h)) { p := p, i := i, view := v } w
      (fun _ w' => w'.outside = [] → MidP p i base s tp (done ++ [Op.put [cv] h]) w') from
    hW b w' hrun hout
  have hC : applyOps (done ++ [Op.put [cv] h]) (contents s) =
      mapPut [cv] h (applyOps done (contents s)) := by
    rw [applyOps, List.foldl_append]
    rfl
  simp only [MidP, hC]
  unfold SIS.Tree.putKv
  refine wput_ok (pathClear_eq _ _) ?_
  refine wput_ok (w' := { w with path := [(none, w.top.rootKey)] }) rfl ?_
  dsimp only
  rw [SIS.Tree.putSegs.eq_2]
  unfold SIS.Tree.setValue
  refine wput_read ?_
  rw [wp_bind]
  refine (wput_descend_root (cv := cv) hs hb (w := { w with path := [(none, w.top.rootKey)] })
    (hm.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl) rfl _).mono ?_
  rintro leaf (w3 : MW) ⟨-, -, hI3, ⟨nl, hlk3, hl3⟩, ⟨c0, hc0⟩, hP3, hin3, hr3⟩
  dsimp only
  obtain ⟨-, -, ht3⟩ := hP3.lookup (Nat.le_refl _) hc0
  obtain ⟨-, -, hnv, hvv, htv, -⟩ := treeOf_fresh hb hI3.books (Nat.le_refl w3.next)
  obtain ⟨hfact, hwf, hsz⟩ := wput_put_fact (h := h) hb hI3 hlk3 ht3 hl3 hr3 hcv
  refine wput_ok (newValue_eq _ _ _) ?_
  refine wput_ok (getNode_hit _ (w := w3.afterNewValue h) hlk3) ?_
  split
  · next hc =>
    refine wput_ok (putNode_eq _ _ _ _) ?_
    rw [wp_pure]
    intro _
    have hc' : nl.size + 1 < p.M := by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact hc.1
    have := add_size nl i (.key cv w3.next)
    exact wput_pinv_fit hfact (lookup_upsert_self _ _ _) (by omega)
  · refine wput_ok (pathSize_eq _ _) ?_
    rw [wp_bind]
    refine (appendKlongs_spec hp hb _ leaf [(cv, w3.next)] (w3.afterNewValue h) nl _
      ⟨hlk3, ⟨c0, hc0⟩, pathOk_afterNewValue h hP3 hnv hvv htv,
        wput_nodup (w := w3) hP3 hin3 hI3.sound, hin3,
        putBooks_afterNewValue hI3.books h, hwf, hsz, Or.inl rfl,
        fun a y1 b y2 he => by simp at he, hfact⟩).mono ?_
    intro r W hW
    rw [wp_pure]
    intro hout
    exact (hW hout).1

/-! ## 5. A transaction, a run -/

/-- `MidP` holds at the start of a transaction. -/
theorem wput_midP_start {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} {t : SIS.Tree.Top} (hs : Shows p v z s tp)
    (ht : SIS.Tree.topOf p v z = .ok t) (hb : Before p i base s tp) :
    MidP p i base s tp [] { next := base, top := t } := by
  have h0 := treeOf_start i s base t
  obtain ⟨t', zn, h1, h2, h3, h4, h5, h6, h7⟩ := hs.top
  rw [ht] at h1
  obtain rfl : t = t' := by injection h1
  have hroot : s.root = some t.rootKey := by
    simp only [Tree.root, hb.books.roots, rootsOf, List.getLast?_map, h2, Option.map_some, h5]
  obtain ⟨r, hr, hS⟩ := (sound_iff (M := p.M)).mp ⟨hb.inv, rfl, hb.tree⟩
  rw [hroot] at hr
  cases hr
  have htop : WTopInv i s tp t false := by
    refine ⟨hb.books.roots, fun _ => ⟨?_, zn, by rw [h3]; exact h2, h6, h7,
      hb.books.skips z zn h2⟩, fun h => by cases h⟩
    rw [h4]
    apply hb.books.rootTimes (zn.time, zn.root)
    rw [hb.books.roots]
    exact List.mem_map.mpr ⟨(z, zn), List.mem_of_getLast? h2, rfl⟩
  refine ⟨by rw [h0]; exact hroot, by rw [h0]; exact hS, ?_, htop, by rw [h0]; exact hb.balanced,
    ?_⟩
  · rw [h0]
    refine ⟨fun x o hx => ⟨o, hx, Ext.refl i o, fun _ => rfl⟩, ?_, [], by simp, by simp⟩
    intro x n hx hn
    rw [hn] at hx
    cases hx
  · constructor <;> simp

/-- A key of one segment, as `Keys.toSegments` makes it, is no long one. -/
theorem wput_isLong {cv : Nat} (h : keyWf [cv] = true) : isLong cv = false := by
  simpa [keyWf] using h

/-- The accepted puts of one-segment keys keep `MidP`. -/
theorem wput_midP_run {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} (hp : ParamsOK p) (hs : Shows p v z s tp)
    (hb : Books i base s tp) :
    ∀ (ops : List MOp) (w w' : MW), OpsRun { p := p, i := i, view := v } w ops w' →
      (∀ op ∈ ops, ∃ cv h, op = SIS.Tree.Op.put [cv] h) → ∀ done, MidP p i base s tp done w →
      MidP p i base s tp (done ++ ops.map opOf) w' := by
  intro ops w w' hrun
  induction hrun with
  | nil w => intro _ done hm; simpa using hm
  | cons w w1 w' op ops b hk h1 h2 _ ih =>
    intro hop done hm
    obtain ⟨cv, h, rfl⟩ := hop _ List.mem_cons_self
    have hm1 := putKv_put1 hp hs hb hm (wput_isLong hk) h1 h2
    have := ih (fun o ho => hop o (List.mem_cons_of_mem _ ho)) _ hm1
    simpa [opOf] using this

theorem wput_times {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {ex : Option NodeId} {C : List (Key × Nat)} {w : MW} (hm : PInv p i base s tp ex C w)
    (hb : Books i base s tp) :
    ∀ x n, (treeOf i s w).obj x = some (.key n) → ∀ t, Klong.time t ∈ n.ks → t ≤ i := by
  intro x n hx t ht
  simp only [treeOf] at hx
  split at hx
  · cases hx
  · split at hx
    · next m hl =>
      simp only [Option.some.injEq, Obj.key.injEq] at hx
      subst hx
      exact hm.books.times x m hl t (mem_map_kOf_time.mp ht)
    · split at hx
      · cases hx
      · exact Nat.le_of_lt (timesBefore_iff.mp (hb.times x n hx) t ht)

theorem wput_first {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {ex : Option NodeId} {C : List (Key × Nat)} {w : MW} (hm : PInv p i base s tp ex C w)
    (hb : Books i base s tp) :
    ∀ x n, (treeOf i s w).obj x = some (.key n) → ∃ t rest, n.ks = Klong.time t :: rest := by
  intro x n hx
  simp only [treeOf] at hx
  split at hx
  · cases hx
  · next htk =>
    split at hx
    · next m hl =>
      simp only [Option.some.injEq, Obj.key.injEq] at hx
      subst hx
      obtain ⟨t, rest, he⟩ := hm.books.timeFirst x m hl (by simpa using htk)
      exact ⟨t, rest.map kOf, by simp [he, kOf]⟩
    · split at hx
      · cases hx
      · exact hb.first x n hx

theorem wput_rootTimes {i : Time} {base : NodeId} {s : Tree} {tp : Top} {w : MW}
    (hb : Books i base s tp) : ∀ r ∈ (treeOf i s w).roots, r.1 ≤ i := by
  intro r hr
  simp only [treeOf] at hr
  split at hr
  · rcases List.mem_append.mp hr with h | h
    · exact Nat.le_of_lt (hb.rootTimes r h)
    · simp only [List.mem_singleton] at h
      subst h
      exact Nat.le_refl _
  · exact Nat.le_of_lt (hb.rootTimes r hr)

theorem wput_ids {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {ex : Option NodeId} {C : List (Key × Nat)} {w : MW} (hm : PInv p i base s tp ex C w)
    (hb : Books i base s tp) :
    ∀ x, w.next ≤ x → (treeOf i s w).obj x = none ∧ (topOf i tp w).node x = none := by
  intro x hx
  obtain ⟨h1, h2, _, h4, h5⟩ := hm.books.ids
  have hbx : base ≤ x := Nat.le_trans h4 hx
  constructor
  · simp only [treeOf]
    split
    · rfl
    · split
      · next m hl => exact absurd (h1 x m hl) (Nat.not_lt.mpr hx)
      · split
        · next v hl => exact absurd (h2 x v hl) (Nat.not_lt.mpr hx)
        · exact (hb.ids x hbx).1
  · simp only [topOf]
    split
    · next hn =>
      have hne : (x == w.top.id) = false := by
        have := h5 hn
        simp only [beq_eq_false_iff_ne, ne_eq]
        omega
      simp only [Top.node, List.lookup_append, List.lookup_cons, List.lookup_nil, hne]
      have := (hb.ids x hbx).2
      simp only [Top.node] at this
      rw [this]
      rfl
    · exact (hb.ids x hbx).2

/-- A transaction of puts of one-segment keys: the model's writer meets the
writer's contract. -/
theorem writerMeets_put1 {p : MParams} (hp : ParamsOK p) (ops : List MOp)
    (hops : ∀ op ∈ ops, ∃ cv h, op = SIS.Tree.Op.put [cv] h) : WriterMeets p ops := by
  intro i base s tp v z t w hbf hs ht hrun
  have hb := hbf.books
  have hm : MidP p i base s tp (ops.map opOf) w := by
    have := wput_midP_run hp hs hb ops _ w hrun hops [] (wput_midP_start hs ht hbf)
    simpa using this
  obtain ⟨hinv, hcont, htree⟩ := (sound_iff (M := p.M)).mpr ⟨_, hm.root, hm.sound⟩
  have hinv' : invOk (cpOf p) (treeOf i s w) = true := hinv
  have hat : (treeOf i s w).at i = treeOf i s w :=
    Tree.at_eq_self (wput_times hm hb) (wput_rootTimes hb)
  have hat0 : s.at (i - 1) = s := by
    apply Tree.at_eq_self
    · intro x n hx t' ht'
      exact Nat.le_sub_one_of_lt (timesBefore_iff.mp (hb.times x n hx) t' ht')
    · intro r hr
      exact Nat.le_sub_one_of_lt (hb.rootTimes r hr)
  refine ⟨⟨?_, hm.frame⟩, by rw [hat]; exact htree, hm.top.step, hm.top.roots, hinv', htree,
    hm.balanced, wput_first hm hb, ?_, ?_, wput_ids hm hb, hm.top.skips hb.skips⟩
  · simp only [contractOk, hat, hat0, hinv', hcont, Bool.true_and, beq_self_eq_true]
  · intro x n hx
    rw [timesBefore_iff]
    intro t' ht'
    exact Nat.lt_succ_of_le (wput_times hm hb x n hx t' ht')
  · intro r hr
    exact Nat.lt_succ_of_le (wput_rootTimes hb r hr)

/-- A run of the model's writer whose operations are puts of one-segment keys
is a history that meets the writer's contract, TREE and the top's clauses. -/
theorem runs_meetsTop_put1 {p : MParams} (hp : ParamsOK p) {txs : List (List Op)} {s : Tree}
    {tp : Top} (h : Runs p txs s tp)
    (hops : ∀ tx ∈ txs, ∀ op ∈ tx, ∃ cv h, op = Op.put [cv] h) : MeetsTop (cpOf p) txs s tp := by
  have key : ∀ {txs : List (List Op)} {s : Tree} {tp : Top}, Runs p txs s tp →
      (∀ tx ∈ txs, ∀ op ∈ tx, ∃ cv h, op = Op.put [cv] h) →
      MeetsTop (cpOf p) txs s tp ∧ RunInv p txs s tp := by
    intro txs s tp h
    induction h with
    | start s tp base hb hc ht =>
      intro _
      have hat : s.at 0 = s := by
        apply Tree.at_eq_self
        · intro x n hx t' ht'
          exact Nat.le_of_lt_succ (timesBefore_iff.mp (hb.books.times x n hx) t' ht')
        · intro r hr
          exact Nat.le_of_lt_succ (hb.books.rootTimes r hr)
      refine ⟨MeetsTop.start s tp ⟨by rw [hat]; exact hb.inv, by rw [hat]; exact hc⟩
        (by rw [hat]; exact hb.tree) ht hb.books.roots, ?_⟩
      exact ⟨hb.inv, hb.tree, hb.balanced, hb.books.first, hb.books.times, hb.books.rootTimes,
        hb.books.roots, hb.books.skips⟩
    | step txs s tp ops base v z t w _ hs ht hids hrun ih =>
      intro hall
      obtain ⟨hmeets, hinv⟩ := ih (fun tx htx => hall tx (List.mem_append_left _ htx))
      have hbf : Before p (txs.length + 1) base s tp :=
        ⟨hinv.inv, hinv.tree, hinv.balanced,
          ⟨hinv.first, hinv.times, hinv.rootTimes, hids, hinv.roots, hinv.skips⟩⟩
      have hops' : ∀ op ∈ ops, ∃ cv h, op = SIS.Tree.Op.put [cv] h := by
        intro op hop
        obtain ⟨cv, h, he⟩ := hall (ops.map opOf) (by simp) (opOf op) (List.mem_map_of_mem hop)
        cases op with
        | put k h' =>
          simp only [opOf, Op.put.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          exact ⟨cv, _, rfl⟩
        | del k => simp [opOf] at he
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, hf, h8, h9, _, h11⟩ :=
        writerMeets_put1 hp ops hops' (txs.length + 1) base s tp v z t w hbf hs ht hrun
      refine ⟨MeetsTop.step txs s tp (ops.map opOf) (dirtyOf w) _ _ hmeets h1 h2 h3 h4, ?_⟩
      refine ⟨h5, h6, h7, hf, ?_, ?_, h4, h11⟩
      · simpa using h8
      · simpa using h9
  exact (key h hops).1

end Contract
