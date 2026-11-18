/-
The contract package (bergdb 030-10): a put that makes new segment leaves,
where the segment leaf that gets the first new klong has room for it. The key
is routed to a segment leaf with two segments or more left, and the leaf has
no live klong of the first of them: `setNode` makes a new segment leaf for
the next segment's tree (`segment.new`), links it by a klong in the leaf
(which has room: no split), and each further segment gets a new segment leaf
in turn; the last one gets the value's klong.

(Without room the leaf is split while the new segment leaf has no klong yet;
that case is not here.)
-/
import Contract.Proof.WriterPutG
import Contract.Proof.TreeRulesChain

namespace Contract

open SIS (View)
open SIS.Check (BVal)

/-! ## 1. The descent along a route that ends with segments left

WriterPutG.lean's descent, for a route to the segment leaf `leaf` with any
key `kend` left (there: [cv]). -/

/-- A route from an inner node: its first step is by the last live klong at
or below the key's first segment. -/
theorem wputs_route_inner {T : Tree} {x leaf : NodeId} {c : Nat} {rest kend : Key}
    {m nl : KNode}
    (hr : Route T x (c :: rest) leaf kend) (hx : T.obj x = some (.key m)) (hml : m.leaf = false)
    (hleaf : T.obj leaf = some (.key nl)) (hnl : nl.leaf = true) :
    ∃ c' y, (c', y) ∈ live m.ks ∧ c' ≤ c ∧
      (∀ c'' y'', (c'', y'') ∈ live m.ks → c'' ≤ c → c'' ≤ c') ∧
      Route T y (c :: rest) leaf kend := by
  cases hr with
  | here =>
    rw [hx] at hleaf
    cases hleaf
    rw [hml] at hnl
    cases hnl
  | inner u n c' y cv' rest' q k' hobj hl hm hle hmax hr =>
    rw [hx] at hobj
    cases hobj
    exact ⟨c', y, hm, hle, hmax, hr⟩
  | leaf u n c' y rest' q k' hobj hl =>
    rw [hx] at hobj
    cases hobj
    rw [hml] at hl
    cases hl

/-- A route from a segment leaf: it ends there, or goes on by the live long
klong of the key's first segment. -/
theorem wputs_route_leaf {T : Tree} {x leaf : NodeId} {c : Nat} {rest kend : Key} {m : KNode}
    (hr : Route T x (c :: rest) leaf kend) (hx : T.obj x = some (.key m)) (hml : m.leaf = true) :
    (x = leaf ∧ c :: rest = kend) ∨
      ∃ y, (c, y) ∈ live m.ks ∧ isLong c = true ∧ Route T y rest leaf kend := by
  cases hr with
  | here => exact Or.inl ⟨rfl, rfl⟩
  | inner u n c' y cv' rest' q k' hobj hl =>
    rw [hx] at hobj
    cases hobj
    rw [hml] at hl
    cases hl
  | leaf u n c' y rest' q k' hobj hl hm hlong hr =>
    rw [hx] at hobj
    cases hobj
    exact Or.inr ⟨y, hm, hlong, hr⟩

/-- Before `descendLte` with the segment c from node x at `depth` of the key
access path, x not read yet: `PInv` with no node over its size; the path
ends with x and starts at the space root; each node above x is in the
overlay, and its live klong names the next node; x is sound; the key is
routed from the space root to the segment leaf `leaf` with `kend` left, and
from x with c :: rest left. -/
structure DescInvS (p : MParams) (i : Time) (base : NodeId) (s : Tree) (tp : Top)
    (C : List (Key × Nat)) (key : Key) (leaf : NodeId) (kend : Key) (c : Nat) (rest : Key)
    (w : MW) (depth : Nat) (x : NodeId) : Prop where
  inv : PInv p i base s tp none C w
  len : w.path.length = depth + 1
  last : ∃ c0, w.path[depth]? = some (c0, x)
  root : w.path[0]? = some (none, w.top.rootKey)
  nodes : ∀ d, d < depth → ∃ c u n, w.path[d]? = some (c, u) ∧ w.nodes.lookup u = some n ∧
    w.taken.contains u = false
  links : ∀ d, d < depth → ∃ c0 u c y nu, w.path[d]? = some (c0, u) ∧
    w.path[d + 1]? = some (some c, y) ∧ (treeOf i s w).obj u = some (.key nu) ∧
    (c, y) ∈ live nu.ks
  good : ∃ lo hi, Good (treeOf i s w) x lo hi
  target : ∃ nl, (treeOf i s w).obj leaf = some (.key nl) ∧ nl.leaf = true
  full : Route (treeOf i s w) w.top.rootKey key leaf kend
  route : Route (treeOf i s w) x (c :: rest) leaf kend
  lev : LevDown i s w depth
  reached : x ∈ reach (treeOf i s w)
  old : OldReach i s w

/-- After the descent with the segment c from the state w: the map and the
super root as in w; `PInv`; the node returned is a segment leaf of the
overlay, the last of the path, sound, and the key is routed from it with
c :: rest left; the path is a path of the tree. -/
def DescPostS (p : MParams) (i : Time) (base : NodeId) (s : Tree) (tp : Top)
    (C : List (Key × Nat)) (leaf : NodeId) (kend : Key) (c : Nat) (rest : Key) (w : MW) :
    NodeId → MW → Prop :=
  fun L w' => treeOf i s w' = treeOf i s w ∧ w'.top = w.top ∧
    PInv p i base s tp none C w' ∧ (∃ nl, w'.nodes.lookup L = some nl ∧ nl.leaf = true) ∧
    (∃ c0, w'.path[w'.path.length - 1]? = some (c0, L)) ∧
    PathOk i s w' (w'.path.length - 1) ∧ (∃ lo hi, Good (treeOf i s w') L lo hi) ∧
    Route (treeOf i s w') L (c :: rest) leaf kend ∧ LevDown i s w' (w'.path.length - 1) ∧
    L ∈ reach (treeOf i s w')

/-- The descent in a segment tree along the key's route: from a state with
`DescInvS`, every result of `descendLte` meets `DescPostS`. -/
theorem wputs_descend {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} {C : List (Key × Nat)} {key : Key} {leaf : NodeId}
    {kend : Key} {c : Nat} {rest : Key} (hs : Shows p v z s tp) (hb : Books i base s tp) :
    ∀ (f : Nat) (w : MW) (depth : Nat) (x : NodeId),
      DescInvS p i base s tp C key leaf kend c rest w depth x →
      WP (SIS.Tree.descendLte c f x) { p := p, i := i, view := v } w
        (DescPostS p i base s tp C leaf kend c rest w) := by
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
    obtain ⟨lo, hi, hGx⟩ := hD.good
    obtain ⟨m, hxm⟩ := wput_good_obj hGx
    obtain ⟨n, w1, hget, hks, hleaf, hlk1, hT1, hI1, hw1, -⟩ :=
      getNode_spec hs hb hD.inv hxm hD.reached hD.old
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
        w1.nodes.lookup u = some n ∧ w1.taken.contains u = false := by
      intro d hd
      obtain ⟨c, u, n0, h1, h2, h3⟩ := hD.nodes d hd
      exact ⟨c, u, n0, by rw [hp1]; exact h1, hext1 u n0 h2, by rw [htk1]; exact h3⟩
    have hlinks1 : ∀ d, d < depth → ∃ c0 u c y nu, w1.path[d]? = some (c0, u) ∧
        w1.path[d + 1]? = some (some c, y) ∧ (treeOf i s w1).obj u = some (.key nu) ∧
        (c, y) ∈ live nu.ks := by
      intro d hd
      rw [hp1, hT1]
      exact hD.links d hd
    have hlev1 : LevDown i s w1 depth := by
      unfold LevDown
      rw [hp1, hT1]
      exact hD.lev
    split
    · next hl =>
      rw [wp_pure]
      have hlen : w1.path.length - 1 = depth := by rw [hp1, hD.len]; omega
      refine ⟨hT1, htop1, hI1, ⟨n, hlk1, hl⟩, ⟨c0, by rw [hlen, hp1]; exact hc0⟩, ?_,
        ⟨lo, hi, by rw [hT1]; exact hGx⟩, by rw [hT1]; exact hD.route, by rw [hlen]; exact hlev1,
        by rw [hT1]; exact hD.reached⟩
      rw [hlen]
      refine ⟨by rw [hp1, htop1]; exact hD.root, fun d hd => ?_, fun d hd => hlinks1 d hd⟩
      rcases Nat.lt_or_eq_of_le hd with hd | rfl
      · exact hnodes1 d hd
      · exact ⟨c0, x, n, by rw [hp1]; exact hc0, hlk1, htx⟩
    · next hl =>
      split
      · exact wp_throw _ _ _ _
      · next fd hfd =>
        obtain ⟨hm, hle, hmax⟩ := searchLte_some (wput_timesLe hI1.books hlk1) hfd
        rw [hks] at hm hmax
        have hml : m.leaf = false := by
          rw [← hleaf]
          cases e : n.leaf
          · rfl
          · exact absurd e hl
        obtain ⟨nl, hnl, hnll⟩ := hD.target
        obtain ⟨c', y, hm', hle', hmax', hr'⟩ := wputs_route_inner hD.route hxm hml hnl hnll
        have hc' : c' = fd.c := Nat.le_antisymm (hmax c' y hm' hle') (hmax' fd.c fd.y hm hle)
        subst hc'
        obtain rfl : y = fd.y := live_unique hm' hm
        obtain ⟨m', lo', hi', hym', hlt', -, hG'⟩ := hGx.child hxm hm' (fun h => by
          rw [hml] at h; cases h)
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
        have hD2 : DescInvS p i base s tp C key leaf kend c rest w2 (depth + 1) fd.y := by
          refine ⟨hI1.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl, ?_, ⟨_, hpb⟩, ?_, ?_, ?_,
            ⟨lo', hi', by rw [hT2]; exact hG'⟩, ⟨nl, by rw [hT2]; exact hnl, hnll⟩, ?_,
            by rw [hT2]; exact hr', ?_, ?_, wput_old_congr hD.old hT2⟩
          · show (w1.path ++ [(some fd.c, fd.y)]).length = depth + 1 + 1
            rw [List.length_append, hlen1]
            rfl
          · rw [hpa 0 (by omega), hp1]
            exact htop1 ▸ hD.root
          · intro d hd
            rw [hpa d hd]
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hd) with hd | rfl
            · exact hnodes1 d hd
            · exact ⟨c0, x, n, by rw [hp1]; exact hc0, hlk1, htx⟩
          · intro d hd
            rw [hpa d hd]
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hd) with hd | rfl
            · rw [hpa (d + 1) (by omega)]
              exact hlinks1 d hd
            · exact ⟨c0, x, fd.c, fd.y, m, by rw [hp1]; exact hc0, hpb, by rw [hT2]; exact hxm,
                hm'⟩
          · rw [hT2]
            show Route (treeOf i s w) w1.top.rootKey key leaf kend
            rw [htop1]
            exact hD.full
          · intro d hd c1 u c1' u' m1 m2 h1 h2 h3 h4
            rw [hT2] at h3 h4
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hd) with hd | rfl
            · rw [hpa d (by omega), hp1] at h1
              rw [hpa (d + 1) (by omega), hp1] at h2
              exact hD.lev d hd c1 u c1' u' m1 m2 h1 h2 h3 h4
            · rw [hpa d (by omega), hp1, hc0] at h1
              rw [hpb] at h2
              cases h1
              cases h2
              rw [hxm] at h3
              rw [hym'] at h4
              cases h3
              cases h4
              exact hlt'
          · rw [hT2]
            exact wputg_reach_kid hD.inv.sound.good hD.inv.root hD.reached hxm hm'
        refine (ih w2 (depth + 1) fd.y hD2).mono ?_
        rintro L w' ⟨h1, h2, h3⟩
        exact ⟨h1.trans hT2, h2.trans htop1, h3⟩

/-- `setNode` for a segment of the key whose tree exists, not the route's end: the descent to the
segment leaf, whose live long klong of the segment names the root of the next
segment's tree (the route's leaf step: `searchEq` finds it); the path goes on
to that root. -/
theorem wputs_setNode {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} {C : List (Key × Nat)} {key : Key} {leaf : NodeId}
    {kend : Key} {c c2 : Nat} {rest : Key} (hs : Shows p v z s tp) (hb : Books i base s tp) {w : MW}
    {depth : Nat} {x : NodeId}
    (hD : DescInvS p i base s tp C key leaf kend c (c2 :: rest) w depth x)
    (hne : c :: c2 :: rest ≠ kend) :
    WP (SIS.Tree.setNode x c true) { p := p, i := i, view := v } w
      (fun r w' => ∃ y depth', r = some y ∧ treeOf i s w' = treeOf i s w ∧
        DescInvS p i base s tp C key leaf kend c2 rest w' depth' y) := by
  unfold SIS.Tree.setNode
  refine wput_read ?_
  rw [wp_bind]
  refine (wputs_descend hs hb _ w depth x hD).mono ?_
  rintro L (w3 : MW) ⟨hT3, htop3, hI3, ⟨nl, hlk3, hl3⟩, ⟨c0, hc0⟩, hP3, ⟨lo, hi, hGL⟩, hr3, hlev3,
    hrc3⟩
  obtain ⟨-, -, ht3⟩ := hP3.lookup (Nat.le_refl _) hc0
  refine wput_ok (getNode_hit _ hlk3) ?_
  have hLm := treeOf_obj_overlay i s hlk3 ht3
  have hwf : klongsWf (ksOf nl) = true := wputg_good_wf hGL hLm
  rcases wputs_route_leaf hr3 hLm hl3 with ⟨-, hk⟩ | ⟨y, hmy, hlong, hry⟩
  · exact absurd hk hne
  split
  · next fd hfd =>
    obtain ⟨hfc, hfm⟩ := searchEq_some hwf (wput_timesLe hI3.books hlk3) hfd
    obtain rfl : y = fd.y := live_unique hmy hfm
    refine wput_ok (pathAdd_eq _ _ _ _) ?_
    rw [wp_pure, hfc]
    obtain ⟨D, hD3⟩ : ∃ D, w3.path.length = D + 1 := by
      cases e : w3.path.length with
      | zero =>
        rw [List.eq_nil_of_length_eq_zero e] at hc0
        simp at hc0
      | succ D => exact ⟨D, rfl⟩
    rw [hD3, Nat.add_sub_cancel] at hc0 hlev3
    rw [hD3, Nat.add_sub_cancel] at hP3
    obtain ⟨m', lo', hi', hym', hlt', -, hG'⟩ := hGL.child hLm hmy (fun _ => hlong)
    let w4 : MW := { w3 with path := w3.path ++ [(some c, fd.y)] }
    have hT4 : treeOf i s w4 = treeOf i s w3 := rfl
    have hpa : ∀ d, d < D + 1 → w4.path[d]? = w3.path[d]? := by
      intro d hd
      exact List.getElem?_append_left (by omega)
    have hpb : w4.path[D + 1]? = some (some c, fd.y) := by
      show (w3.path ++ [(some c, fd.y)])[D + 1]? = _
      rw [List.getElem?_append_right (by omega), hD3]
      simp
    refine ⟨fd.y, D + 1, rfl, hT3, hI3.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl, ?_, ⟨_, hpb⟩,
      ?_, ?_, ?_, ⟨lo', hi', hG'⟩, ?_, ?_, hry, ?_, ?_, wput_old_congr hD.old hT3⟩
    · show (w3.path ++ [(some c, fd.y)]).length = D + 1 + 1
      rw [List.length_append, hD3]
      rfl
    · rw [hpa 0 (by omega)]
      exact hP3.root
    · intro d hd
      rw [hpa d hd]
      exact hP3.nodes d (by omega)
    · intro d hd
      rw [hpa d hd]
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hd) with hd | rfl
      · rw [hpa (d + 1) (by omega)]
        exact hP3.links d hd
      · exact ⟨c0, L, c, fd.y, _, hc0, hpb, hLm, hmy⟩
    · obtain ⟨nl', h1, h2⟩ := hD.target
      exact ⟨nl', by rw [hT4, hT3]; exact h1, h2⟩
    · show Route (treeOf i s w3) w3.top.rootKey key leaf kend
      rw [hT3, htop3]
      exact hD.full
    · intro d hd c1 u c1' u' m1 m2 h1 h2 h3 h4
      change (treeOf i s w3).obj u = some (.key m1) at h3
      change (treeOf i s w3).obj u' = some (.key m2) at h4
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hd) with hd | rfl
      · rw [hpa d (by omega)] at h1
        rw [hpa (d + 1) (by omega)] at h2
        exact hlev3 d hd c1 u c1' u' m1 m2 h1 h2 h3 h4
      · rw [hpa d (by omega), hc0] at h1
        rw [hpb] at h2
        cases h1
        cases h2
        rw [hLm] at h3
        rw [hym'] at h4
        cases h3
        cases h4
        exact hlt'
    · exact wputg_reach_kid hI3.sound.good hI3.root hrc3 hLm hmy
  · next hfd =>
    exact (searchEq_none hwf (wput_timesLe hI3.books hlk3) hfd y hmy).elim

/-! ## 2. The steps on a new segment leaf -/

/-- `descendLte` from a segment leaf of the overlay returns it at once. -/
theorem wputs_descend_leaf (c : SIS.Tree.Ctx) {w : MW} {y : NodeId} {n : MNode}
    (hy : w.nodes.lookup y = some n) (hl : n.leaf = true) (cv f : Nat) :
    WP (SIS.Tree.descendLte cv (f + 1) y) c w (fun r w' => r = y ∧ w' = w) := by
  rw [wput_descend_succ]
  refine wput_read (wput_ok (getNode_hit _ hy) ?_)
  simp [hl, wp_pure]

theorem wputs_fuel (p : MParams) : p.fuel = ((p.G + 1) * (p.H + 2) + 1) + 1 := rfl

/-- The empty segment leaf with one key klong added: a time klong of i and
the klong; no dead klong. -/
theorem wputs_add_empty (i c y : Nat) :
    (⟨true, []⟩ : MNode).add i (.key c y) = ⟨true, [.time i, .key c y]⟩ := rfl

theorem wputs_deadOver (p : MParams) (i c y : Nat) :
    SIS.Tree.deadOver p ((⟨true, []⟩ : MNode).add i (.key c y)) = false := by
  simp [SIS.Tree.deadOver, SIS.Tree.KNode.deadCount, SIS.Tree.KNode.add,
    SIS.Tree.KNode.lastTime, SIS.Tree.KNode.lastBitmap, SIS.Tree.lastBitmapOf]

/-- `setValue` on a new segment leaf y of the overlay with no klongs: the new
value, and its klong in y (room; no dead klong). -/
theorem wputs_setValue_new {p : MParams} {i : Time} {v : View BVal} (hp : ParamsOK p)
    {w : MW} {y : NodeId} (hy : w.nodes.lookup y = some ⟨true, []⟩) (c : Nat) (key : Key)
    (h : Nat) :
    WP (SIS.Tree.setValue y c key (some h)) { p := p, i := i, view := v } w
      (fun _ w' => w' = (w.afterNewValue h).withNode y ((⟨true, []⟩ : MNode).add i
        (.key c w.next))) := by
  unfold SIS.Tree.setValue
  refine wput_read ?_
  rw [wp_bind]
  dsimp only
  rw [wputs_fuel]
  refine (wputs_descend_leaf _ hy rfl c _).mono ?_
  rintro r w1 ⟨rfl, hw1⟩
  subst w1
  refine wput_ok (newValue_eq _ _ _) ?_
  refine wput_ok (getNode_hit _ (w := w.afterNewValue h) hy) ?_
  split
  · refine wput_ok (putNode_eq _ _ _ _) ?_
    rw [wp_pure]
  · next hc =>
    exfalso
    apply hc
    have := hp.size
    simp only [wputs_deadOver, Bool.not_false, Bool.and_true, decide_eq_true_eq]
    show 0 + 1 < p.M
    omega

/-- `setNode` with `create` on a new segment leaf y of the overlay with no
klongs (segment g, height 0): no klong of c, so a new segment leaf for the
next segment, at segment g + 1, linked by c in y. -/
theorem wputs_setNode_new {p : MParams} {i : Time} {v : View BVal} (hp : ParamsOK p)
    {w : MW} {y : NodeId} {g : Nat} (hy : w.nodes.lookup y = some ⟨true, []⟩)
    (hg : w.gh.lookup y = some (g, 0)) (c : Nat) :
    WP (SIS.Tree.setNode y c true) { p := p, i := i, view := v } w
      (fun r w' => r = some w.next ∧
        w' = (MW.afterNewKey { w with trail := "segment.new" :: w.trail } p (g + 1) 0 true
          []).withNode y ((⟨true, []⟩ : MNode).add i (.key c w.next))) := by
  unfold SIS.Tree.setNode
  refine wput_read ?_
  rw [wp_bind]
  dsimp only
  rw [wputs_fuel]
  refine (wputs_descend_leaf _ hy rfl c _).mono ?_
  rintro r w1 ⟨rfl, hw1⟩
  subst w1
  refine wput_ok (getNode_hit _ hy) ?_
  have hse : (⟨true, []⟩ : MNode).searchEq i c = none := rfl
  rw [hse]
  dsimp only
  refine wput_ok (ghOf_hit _ hy hg) ?_
  dsimp only
  refine wput_ok (note_eq _ _ _) ?_
  refine wput_ok (newKey_eq _ _ _ _ _ _) ?_
  split
  · refine wput_ok (putNode_eq _ _ _ _) ?_
    rw [wp_pure]
    exact ⟨rfl, rfl⟩
  · next hc =>
    exfalso
    have := hp.size
    apply hc
    show 0 + 1 < p.M
    omega

/-! ## 3. The chain of new segment leaves -/

/-- The writer's state but for `Sound` and BalancedOK (which is shown for the
put's last state, by the nodes reached): the map's root, the frame, the top,
and the books with nodes that have no klongs yet (`PutBooksE`). -/
structure WInvE (p : MParams) (i : Time) (base : NodeId) (s : Tree) (tp : Top) (w : MW) :
    Prop where
  root : (treeOf i s w).root = some w.top.rootKey
  frame : Frame i s (dirtyOf w) (treeOf i s w)
  top : WTopInv i s tp w.top w.newTop
  books : PutBooksE p i base s w

theorem WInvE.trail {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top} {w : MW}
    (h : WInvE p i base s tp w) (t : List String) : WInvE p i base s tp { w with trail := t } :=
  ⟨h.root, h.frame, h.top, ⟨h.books.first, h.books.times, h.books.levels,
    h.books.ids, h.books.taken, h.books.overlay, h.books.within, h.books.timeFirst,
    h.books.empty⟩⟩

/-- Before `putSegs` on the segments left from y, the last new segment leaf,
with no klongs yet, of segment g at height 0; A the map before the put. The
steps' facts hold always; the books if no node is outside G and H. -/
structure ChainPre (p : MParams) (i : Time) (base : NodeId) (s : Tree) (tp : Top) (A : Tree)
    (w : MW) (y : NodeId) (g : Nat) : Prop where
  look : w.nodes.lookup y = some ⟨true, []⟩
  gh : w.gh.lookup y = some (g, 0)
  ids : ∀ x n, w.nodes.lookup x = some n → x < w.next
  fresh : ∀ z, (z = y ∨ w.next ≤ z) → A.obj z = none
  cond : w.outside = [] → WInvE p i base s tp w ∧ w.taken.contains y = false ∧
    (∀ x n, w.nodes.lookup x = some n → w.taken.contains x = false → n.ks = [] → x = y) ∧
    g ≤ p.G

/-- After `putSegs` on the segments `rest` from y: if no node is outside G and
H, the books of the state, with no node without klongs; y heads a chain of
new segment leaves that holds the key's rest with the value h (`NewChain`),
of ids at or above the next id, but y, each a segment leaf at height 0; the
other nodes below the next id are as they were. -/
def ChainPost (p : MParams) (i : Time) (base : NodeId) (s : Tree) (tp : Top) (A : Tree)
    (h : Nat) (w : MW) (y : NodeId) (g : Nat) (rest : Key) : Bool → MW → Prop :=
  fun _ w' => w'.outside = [] →
    w.outside = [] ∧ WInvE p i base s tp w' ∧
    (∀ x n, w'.nodes.lookup x = some n → w'.taken.contains x = false → n.ks ≠ []) ∧
    g ≤ p.G ∧
    (∃ ids, NewChain p.M A (treeOf i s w') h y (p.keyLevel g 0) rest ids ∧
      (∀ z ∈ ids, z = y ∨ w.next ≤ z) ∧
      (∀ z, w.next ≤ z → z ∉ ids → (treeOf i s w').obj z = none) ∧
      ∀ z ∈ ids, ∀ m, (treeOf i s w').obj z = some (.key m) →
        0 < m.level ∧ m.leaf = true ∧ p.heightOf m.level = 0) ∧
    (∀ z, z < w.next → z ≠ y → (treeOf i s w').obj z = (treeOf i s w).obj z) ∧
    w'.top = w.top ∧ w'.newTop = w.newTop

theorem wputs_chain_head {M : Nat} {A B : Tree} {hval : Nat} {y : NodeId} {lv : Nat} {key : Key}
    {ids : List NodeId} (h : NewChain M A B hval y lv key ids) : y ∈ ids := by
  cases h with
  | last => exact List.mem_cons_self
  | step => exact List.mem_cons_self

theorem wputs_keyLevel_lt (p : MParams) {g : Nat} (hg : g + 1 ≤ p.G) :
    p.keyLevel (g + 1) 0 < p.keyLevel g 0 := by
  unfold SIS.Tree.Params.keyLevel
  have : p.G - g = (p.G - (g + 1)) + 1 := by omega
  rw [this, Nat.succ_mul]
  omega

theorem wputs_live_one (i c y : Nat) : live (ksOf ⟨true, [.time i, .key c y]⟩) = [(c, y)] := by
  rw [← wputs_add_empty, add_key_live (by decide)]
  rfl

theorem wputs_wf_one (i c y : Nat) : klongsWf (ksOf ⟨true, [.time i, .key c y]⟩) = true := by
  rw [← wputs_add_empty]
  exact add_key_wf (by decide) c y

/-- A new segment leaf with one klong, of c to y, is a node of the map B on
its level within the node size, if B has y. -/
theorem wputs_nodeIs_one {p : MParams} (hp : ParamsOK p) {B : Tree} {x : NodeId} {lv i c y : Nat}
    (hx : B.obj x = some (.key ⟨lv, true, ksOf ⟨true, [.time i, .key c y]⟩⟩))
    (hy : (B.obj y).isSome = true) : NodeIs B x lv true [(c, y)] p.M := by
  refine ⟨_, hx, rfl, rfl, wputs_live_one i c y, ?_⟩
  have := hp.size
  simp only [nodeOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨⟨by simp only [ksOf, List.map, List.length]; omega, wputs_wf_one i c y⟩, ?_⟩
  intro k hk
  simp only [ksOf, List.map, kOf, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl
  · rfl
  · exact hy

/-- `putSegs` on the segments left from a new segment leaf with no klongs: a
new segment leaf for each further segment, the value's klong in the last. -/
theorem wputs_chain {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} (hp : ParamsOK p) (hb : Books i base s tp) {A : Tree} {key : Key}
    {h : Nat} :
    ∀ (rest : Key) (w : MW) (y : NodeId) (g : Nat), rest ≠ [] → keyWf rest = true →
      ChainPre p i base s tp A w y g →
      WP (SIS.Tree.putSegs key (some h) rest y) { p := p, i := i, view := v } w
        (ChainPost p i base s tp A h w y g rest) := by
  intro rest
  induction rest with
  | nil => intro w y g hne; exact absurd rfl hne
  | cons c rest' ih =>
    intro w y g _ hk hpre
    have hyn : y < w.next := hpre.ids y _ hpre.look
    have hyv : y ≠ w.next := Nat.ne_of_lt hyn
    have hnv' : w.nodes.lookup w.next = none := by
      cases e : w.nodes.lookup w.next with
      | none => rfl
      | some n => exact absurd (hpre.ids _ n e) (Nat.lt_irrefl _)
    cases rest' with
    | nil =>
      rw [SIS.Tree.putSegs.eq_2]
      refine (wputs_setValue_new hp hpre.look c key h).mono ?_
      rintro r wf rfl ho
      rw [wputs_add_empty] at ho ⊢
      obtain ⟨hW, hty, hemp, hg⟩ := hpre.cond ho
      obtain ⟨hTv, hsv, hnv, hvv, htv, -⟩ := treeOf_freshE hb hW.books (Nat.le_refl w.next)
      have hsy : s.obj y = none := hW.books.empty y _ hpre.look hty rfl
      have hlvl : wLevel s w y = p.keyLevel g 0 := by
        obtain ⟨g', h', h1, -, -, h4, -⟩ := hW.books.levels y _ hpre.look hty
        rw [hpre.gh] at h1
        cases h1
        exact h4
      have hT4 : treeOf i s (w.afterNewValue h) = (treeOf i s w).set w.next (.val h) :=
        treeOf_afterNewValue i s h hnv hvv htv
      have hTW := treeOf_withNode i s (w := w.afterNewValue h)
        (⟨true, [.time i, .key c w.next]⟩ : MNode) hty
      have hwl : wLevel s (w.afterNewValue h) y = wLevel s w y := prim_wLevel_afterNewValue hyv
      refine ⟨ho, ⟨hW.root, ?_, hW.top, ?_⟩, ?_, hg, ⟨[y, w.next], ?_, ?_, ?_, ?_⟩, ?_, rfl,
        rfl⟩
      · exact frame_withNode (frame_afterNewValue h hW.frame hsv hnv hvv htv) hpre.look hty rfl
          (fun n0 hs0 => by rw [hsy] at hs0; cases hs0)
      · refine putBooksE_withNode (putBooksE_afterNewValue hW.books h) hpre.look hty rfl
          (Or.inr ⟨rfl, _, rfl⟩) (fun t ht => ?_)
        simp only [List.mem_cons, SIS.Tree.Klong.time.injEq, List.not_mem_nil, or_false,
          reduceCtorEq] at ht
        omega
      · intro x n hx htx
        rcases prim_lookup_withNode hx with ⟨rfl, rfl⟩ | ⟨hxy, hx'⟩
        · simp
        · exact fun he => hxy (hemp x n hx' htx he)
      · refine NewChain.last y w.next _ c (hpre.fresh y (Or.inl rfl))
          (hpre.fresh w.next (Or.inr (Nat.le_refl _))) hyv ?_ (wput_isLong hk) ?_
        · refine wputs_nodeIs_one (i := i) hp ?_ ?_
          · rw [hTW]
            simp [Tree.set, hwl, hlvl]
          · rw [hTW, hT4]
            simp [Tree.set, Ne.symm hyv]
        · rw [hTW, hT4]
          simp [Tree.set, Ne.symm hyv]
      · intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr (Nat.le_refl _)
      · intro z hz hzi
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hzi
        rw [hTW, hT4]
        simp only [Tree.set, hzi.1, hzi.2, ite_false]
        exact (treeOf_freshE hb hW.books hz).1
      · intro z hz m hm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with hz | hz
        · rw [hz, hTW] at hm
          simp [Tree.set, hwl, hlvl] at hm
          subst hm
          exact ⟨keyLevel_pos p g 0, rfl, heightOf_keyLevel p (Nat.zero_le _)⟩
        · rw [hz, hTW, hT4] at hm
          simp [Tree.set, Ne.symm hyv] at hm
      · intro z hz hzy
        rw [hTW, hT4]
        simp [Tree.set, hzy, Nat.ne_of_lt hz]
    | cons c2 rest2 =>
      have hk2 : isLong c = true ∧ keyWf (c2 :: rest2) = true := by
        simp only [keyWf, Bool.and_eq_true] at hk
        exact hk
      rw [SIS.Tree.putSegs.eq_3 _ _ _ _ _ (by simp), wp_bind]
      refine (wputs_setNode_new hp hpre.look hpre.gh c).mono ?_
      rintro r w3 ⟨rfl, hw3⟩
      subst w3
      dsimp only
      rw [wputs_add_empty]
      set wN : MW := { w with trail := "segment.new" :: w.trail } with hwN
      set wA : MW := MW.afterNewKey wN p (g + 1) 0 true [] with hwA
      set n1 : MNode := ⟨true, [.time i, .key c w.next]⟩ with hn1
      have hNn : wN.next = w.next := rfl
      have hlkA : wA.nodes.lookup y = some ⟨true, []⟩ := prim_lookup_append_some _ hpre.look
      have hlkA' : wA.nodes.lookup w.next = some ⟨true, []⟩ := prim_lookup_append_self _ _ hnv'
      have hn3 : (wA.withNode y n1).next = w.next + 2 := rfl
      have hout3 : (wA.withNode y n1).outside = if (decide (p.G < g + 1) || decide (p.H < 0))
          then (w.next, g + 1, 0) :: w.outside else w.outside := rfl
      have hcond : (wA.withNode y n1).outside = [] → w.outside = [] ∧ g + 1 ≤ p.G := by
        intro ho3
        rw [hout3] at ho3
        split at ho3
        · cases ho3
        · next hcnd =>
          simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_lt] at hcnd
          exact ⟨ho3, hcnd.1⟩
      have htimes : ∀ t, SIS.Tree.Klong.time t ∈ n1.ks → t ≤ i := by
        intro t ht
        simp only [hn1, List.mem_cons, SIS.Tree.Klong.time.injEq, List.not_mem_nil, or_false,
          reduceCtorEq] at ht
        omega
      have hpre3 : ChainPre p i base s tp A (wA.withNode y n1) w.next (g + 1) := by
        refine ⟨?_, prim_gh_cons_self _ _ _ _, ?_, ?_, ?_⟩
        · rw [MW.withNode, lookup_upsert_ne _ _ (Ne.symm hyv)]
          exact hlkA'
        · intro x n hx
          rw [hn3]
          rcases prim_lookup_withNode hx with ⟨rfl, -⟩ | ⟨-, hx'⟩
          · omega
          · rcases prim_lookup_afterNewKey (w := wN) hnv' hx' with ⟨rfl, -⟩ | ⟨-, hx''⟩
            · omega
            · have := hpre.ids x n hx''
              omega
        · intro z hz
          apply hpre.fresh z (Or.inr ?_)
          rcases hz with rfl | hz
          · exact Nat.le_refl _
          · omega
        · intro ho3
          obtain ⟨ho, hg1⟩ := hcond ho3
          obtain ⟨hW, hty, hemp, -⟩ := hpre.cond ho
          obtain ⟨-, hsv, hnv, -, htv, hmv⟩ := treeOf_freshE hb hW.books (Nat.le_refl w.next)
          have hsy : s.obj y = none := hW.books.empty y _ hpre.look hty rfl
          have hWN := hW.trail ("segment.new" :: w.trail)
          have hkA := putBooksE_afterNewKey (w := wN) hb hWN.books hg1 (Nat.zero_le _) rfl
            (Or.inl rfl) (by simp)
          have hFA := frame_afterNewKey (w := wN) p (g + 1) 0 true [] hWN.frame hsv hnv htv hmv
          refine ⟨⟨hW.root, frame_withNode hFA hlkA hty rfl (fun n0 hs0 => by
            rw [hsy] at hs0; cases hs0), hW.top, putBooksE_withNode hkA hlkA hty rfl
            (Or.inr ⟨rfl, _, rfl⟩) htimes⟩, htv, ?_, hg1⟩
          intro x n hx htx he
          rcases prim_lookup_withNode hx with ⟨rfl, rfl⟩ | ⟨hxy, hx'⟩
          · cases he
          · rcases prim_lookup_afterNewKey (w := wN) hnv hx' with ⟨rfl, -⟩ | ⟨-, hx''⟩
            · rfl
            · exact absurd (hemp x n hx'' htx he) hxy
      refine (ih (wA.withNode y n1) w.next (g + 1) (by simp) hk2.2 hpre3).mono ?_
      intro r wf hpost ho
      obtain ⟨ho3, hWf, hnoe, hg1, ⟨ids, hch, hids, hnone, hlvi⟩, hsame, htopf, hnewf⟩ := hpost ho
      obtain ⟨ho', -⟩ := hcond ho3
      obtain ⟨hW, hty, -, -⟩ := hpre.cond ho'
      obtain ⟨-, hsv, hnv, -, htv, hmv⟩ := treeOf_freshE hb hW.books (Nat.le_refl w.next)
      have hTA : treeOf i s wA = (treeOf i s w).set w.next (.key ⟨p.keyLevel (g + 1) 0, true,
          []⟩) := treeOf_afterNewKey (w := wN) i s p (g + 1) 0 true [] hsv hnv htv hmv
      have hT3 : treeOf i s (wA.withNode y n1) =
          (treeOf i s wA).set y (.key ⟨wLevel s wA y, true, ksOf n1⟩) := treeOf_withNode i s n1 hty
      have hwlA : wLevel s wA y = wLevel s w y := prim_wLevel_afterNewKey (w := wN) hyv
      have hlvl : wLevel s w y = p.keyLevel g 0 := by
        obtain ⟨g', h', h1, -, -, h4, -⟩ := hW.books.levels y _ hpre.look hty
        rw [hpre.gh] at h1
        cases h1
        exact h4
      have hhead := wputs_chain_head hch
      refine ⟨ho', hWf, hnoe, by omega, ⟨y :: ids, ?_, ?_, ?_, ?_⟩, ?_, htopf, hnewf⟩
      · refine NewChain.step y w.next _ _ c (c2 :: rest2) ids (hpre.fresh y (Or.inl rfl)) ?_ ?_
          hk2.1 (wputs_keyLevel_lt p hg1) hch
        · intro hyi
          rcases hids y hyi with h1 | h1
          · exact hyv h1
          · omega
        · refine wputs_nodeIs_one (i := i) hp ?_ ?_
          · rw [hsame y (by omega) hyv, hT3]
            simp [Tree.set, hwlA, hlvl, hn1]
          · obtain ⟨⟨m, hm, -⟩, -⟩ := hch.tr_props
            rw [hm]
            rfl
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact Or.inl rfl
        · rcases hids z hz with rfl | h1
          · exact Or.inr (Nat.le_refl _)
          · exact Or.inr (by omega)
      · intro z hz hzi
        have hzy : z ≠ y := fun e => hzi (e ▸ List.mem_cons_self)
        have hzi' : z ∉ ids := fun e => hzi (List.mem_cons_of_mem _ e)
        by_cases hz3 : (wA.withNode y n1).next ≤ z
        · exact hnone z hz3 hzi'
        · have hzn : z ≠ w.next := fun e => hzi' (e ▸ hhead)
          rw [hsame z (by omega) hzn, hT3, hTA]
          simp only [Tree.set, hzy, hzn, ite_false]
          exact (treeOf_freshE hb hW.books hz).1
      · intro z hz m hm
        rcases List.mem_cons.mp hz with hz | hz
        · rw [hz, hsame y (by omega) hyv, hT3] at hm
          simp [Tree.set, hwlA, hlvl, hn1] at hm
          subst hm
          exact ⟨keyLevel_pos p g 0, rfl, heightOf_keyLevel p (Nat.zero_le _)⟩
        · exact hlvi z hz m hm
      · intro z hz hzy
        have hzn : z ≠ w.next := Nat.ne_of_lt hz
        rw [hsame z (by omega) hzn, hT3, hTA]
        simp [Tree.set, hzy, hzn]

/-! ## 4. The put -/

theorem wputs_route_suffix {T : Tree} {u q : NodeId} {k k' : Key} (hr : Route T u k q k') :
    ∃ pre, k = pre ++ k' := by
  induction hr with
  | here q k => exact ⟨[], rfl⟩
  | inner u n c y cv rest q k' _ _ _ _ _ _ ih => exact ih
  | leaf u n c y rest q k' _ _ _ _ _ ih =>
    obtain ⟨pre, he⟩ := ih
    exact ⟨c :: pre, by rw [he]; rfl⟩

/-- `putSegs` from the root x of the tree of the segment cv, which has no
live klong of cv in the segment leaf the key is routed to, with room in it: a
new segment leaf for the next segment's tree, linked from the leaf, then the
chain of new segment leaves (`wputs_chain`), and `Sound.putSeg`. -/
theorem wputs_newseg {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} {C : List (Key × Nat)} {key : Key} {leaf : NodeId}
    {cv : Nat} {rest : Key} {h : Nat} {T : Tree} {nl : KNode} (hp : ParamsOK p)
    (hs : Shows p v z s tp) (hb : Books i base s tp) (hrne : rest ≠ [])
    (hk : keyWf (cv :: rest) = true) (hleafT : T.obj leaf = some (.key nl))
    (hno : ∀ y, (cv, y) ∉ live nl.ks) (hsize : nl.ks.length + 2 ≤ p.M) {w : MW} {depth : Nat}
    {x : NodeId} (hT : treeOf i s w = T)
    (hD : DescInvS p i base s tp C key leaf (cv :: rest) cv rest w depth x) :
    WP (SIS.Tree.putSegs key (some h) (cv :: rest) x) { p := p, i := i, view := v } w
      (fun _ w' => w'.outside = [] → PInv p i base s tp none (mapPut key h C) w' ∧
        OldReach i s w') := by
  have hk2 : isLong cv = true ∧ keyWf rest = true := by
    cases rest with
    | nil => exact absurd rfl hrne
    | cons c2 r =>
      simp only [keyWf, Bool.and_eq_true] at hk
      exact hk
  rw [SIS.Tree.putSegs.eq_3 _ _ _ _ _ hrne, wp_bind]
  unfold SIS.Tree.setNode
  refine wput_read ?_
  rw [wp_bind]
  refine (wputs_descend hs hb _ w depth x hD).mono ?_
  rintro L (w3 : MW) ⟨hT3, htop3, hI3, ⟨n, hlk3, hl3⟩, ⟨c0, hc0⟩, hP3, ⟨lo, hi, hGL⟩, hr3, -,
    hrc3⟩
  obtain ⟨-, -, ht3⟩ := hP3.lookup (Nat.le_refl _) hc0
  have hLm := treeOf_obj_overlay i s hlk3 ht3
  rcases wputs_route_leaf hr3 hLm hl3 with ⟨hL, -⟩ | ⟨y, -, -, hry⟩
  swap
  · exfalso
    obtain ⟨pre, he⟩ := wputs_route_suffix hry
    have := congrArg List.length he
    simp only [List.length_append, List.length_cons] at this
    omega
  subst hL
  have hnx : nl = ⟨wLevel s w3 L, n.leaf, ksOf n⟩ := by
    have := hLm
    rw [hT3, hT, hleafT] at this
    cases this
    rfl
  subst hnx
  have hwf : klongsWf (ksOf n) = true := wputg_good_wf hGL hLm
  have hsz : n.size + 2 ≤ p.M := by
    rw [← ksOf_length]
    exact hsize
  have hrT3 : Route (treeOf i s w3) w3.top.rootKey key L (cv :: rest) := by
    rw [hT3, htop3]
    exact hD.full
  refine wput_ok (getNode_hit _ hlk3) ?_
  split
  · next fd hfd =>
    exfalso
    obtain ⟨-, hfm⟩ := searchEq_some hwf (wput_timesLe hI3.books hlk3) hfd
    exact hno fd.y hfm
  · dsimp only
    obtain ⟨g, hh, hgh, -, -, hlv, hlf⟩ := hI3.books.levels L n hlk3 ht3
    have hh0 : hh = 0 := by
      rw [hl3] at hlf
      cases hh with
      | zero => rfl
      | succ k => simp at hlf
    subst hh0
    refine wput_ok (ghOf_hit _ hlk3 hgh) ?_
    dsimp only
    refine wput_ok (note_eq _ _ _) ?_
    refine wput_ok (newKey_eq _ _ _ _ _ _) ?_
    split
    · refine wput_ok (putNode_eq _ _ _ _) ?_
      rw [wp_pure]
      dsimp only
      set wN : MW := { w3 with trail := "segment.new" :: w3.trail } with hwN
      set wA : MW := MW.afterNewKey wN p (g + 1) 0 true [] with hwA
      set n' : MNode := n.add i (.key cv w3.next) with hn'
      have hNn : wN.next = w3.next := rfl
      have hn6 : (wA.withNode L n').next = w3.next + 2 := rfl
      obtain ⟨-, hsv, hnv, -, htv, hmv⟩ := treeOf_fresh hb hI3.books (Nat.le_refl w3.next)
      have hLn : L < w3.next := hI3.books.ids.1 L n hlk3
      have hLv : L ≠ w3.next := Nat.ne_of_lt hLn
      have hlkA : wA.nodes.lookup L = some n := prim_lookup_append_some _ hlk3
      have hlkA' : wA.nodes.lookup w3.next = some ⟨true, []⟩ := prim_lookup_append_self _ _ hnv
      have hleaf' : n'.leaf = n.leaf := add_leaf n i _
      obtain ⟨t0, rest0, hr0⟩ := hI3.books.timeFirst L n hlk3 ht3
      obtain ⟨rest1, hr1⟩ := add_first (t := i) (.key cv w3.next) hr0
      have hout6 : (wA.withNode L n').outside = if (decide (p.G < g + 1) || decide (p.H < 0))
          then (w3.next, g + 1, 0) :: w3.outside else w3.outside := rfl
      have hcond : (wA.withNode L n').outside = [] → g + 1 ≤ p.G := by
        intro ho6
        rw [hout6] at ho6
        split at ho6
        · cases ho6
        · next hcnd =>
          simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_lt] at hcnd
          exact hcnd.1
      have hpre6 : ChainPre p i base s tp (treeOf i s w3) (wA.withNode L n') w3.next (g + 1) := by
        refine ⟨?_, prim_gh_cons_self _ _ _ _, ?_, ?_, ?_⟩
        · rw [MW.withNode, lookup_upsert_ne _ _ (Ne.symm hLv)]
          exact hlkA'
        · intro x n0 hx
          rw [hn6]
          rcases prim_lookup_withNode hx with ⟨rfl, -⟩ | ⟨-, hx'⟩
          · omega
          · rcases prim_lookup_afterNewKey (w := wN) hnv hx' with ⟨rfl, -⟩ | ⟨-, hx''⟩
            · omega
            · have := hI3.books.ids.1 x n0 hx''
              omega
        · intro z hz
          refine (treeOf_fresh hb hI3.books (x := z) ?_).1
          rcases hz with rfl | hz
          · exact Nat.le_refl _
          · omega
        · intro ho6
          have hg1 := hcond ho6
          have hW3 : WInvE p i base s tp w3 :=
            ⟨hI3.root, hI3.frame, hI3.top, hI3.books.toE⟩
          have hWN := hW3.trail ("segment.new" :: w3.trail)
          have hkA := putBooksE_afterNewKey (w := wN) hb hWN.books hg1 (Nat.zero_le _) rfl
            (Or.inl rfl) (by simp)
          have hFA := frame_afterNewKey (w := wN) p (g + 1) 0 true [] hWN.frame hsv hnv htv hmv
          refine ⟨⟨hI3.root, ?_, hI3.top, ?_⟩, htv, ?_, hg1⟩
          · refine frame_withNode hFA hlkA ht3 hleaf' (fun n0 hs0 => ?_)
            obtain ⟨-, -, he⟩ := frame_overlay_ext hI3.frame hlk3 ht3 hs0
            exact add_ext (prim_timesBefore (hb.times L n0 hs0)) he _
          · exact putBooksE_withNode hkA hlkA ht3 hleaf' (Or.inl (by rw [hr1, hr0]; rfl))
              (timesLe_model (add_timesLe (wput_timesLe hI3.books hlk3) _
                (fun t' e => by cases e)))
          · intro x n0 hx htx he
            rcases prim_lookup_withNode hx with ⟨rfl, rfl⟩ | ⟨hxy, hx'⟩
            · rw [hr1] at he
              cases he
            · rcases prim_lookup_afterNewKey (w := wN) hnv hx' with ⟨rfl, -⟩ | ⟨-, hx''⟩
              · rfl
              · obtain ⟨t1, r1, hr⟩ := hI3.books.timeFirst x n0 hx'' htx
                rw [hr] at he
                cases he
      refine (wputs_chain hp hb rest (wA.withNode L n') w3.next (g + 1) hrne hk2.2 hpre6).mono ?_
      intro r wf hpost ho
      obtain ⟨-, hWf, hnoe, hg1, ⟨ids, hch, hids, hnone, hlvi⟩, hsame, htopf, -⟩ := hpost ho
      have hTA : treeOf i s wA = (treeOf i s w3).set w3.next (.key ⟨p.keyLevel (g + 1) 0, true,
          []⟩) := treeOf_afterNewKey (w := wN) i s p (g + 1) 0 true [] hsv hnv htv hmv
      have hT6 : treeOf i s (wA.withNode L n') =
          (treeOf i s wA).set L (.key ⟨wLevel s wA L, n'.leaf, ksOf n'⟩) :=
        treeOf_withNode i s n' ht3
      have hwlA : wLevel s wA L = wLevel s w3 L := prim_wLevel_afterNewKey (w := wN) hLv
      have hhead := wputs_chain_head hch
      have hT6z : ∀ z, z ≠ L → z ≠ w3.next →
          (treeOf i s (wA.withNode L n')).obj z = (treeOf i s w3).obj z := by
        intro z h1 h2
        rw [hT6, hTA]
        simp [Tree.set, h1, h2]
      have hBsome : ∀ y, ((treeOf i s w3).obj y).isSome = true →
          ((treeOf i s wf).obj y).isSome = true := by
        intro y hy
        have hy3 : y < w3.next := by
          by_contra hc
          rw [(treeOf_fresh hb hI3.books (Nat.le_of_not_lt hc)).1] at hy
          cases hy
        by_cases hyL : y = L
        · subst hyL
          rw [hsame _ (by omega) hLv, hT6]
          simp [Tree.set]
        · rw [hsame y (by rw [hn6]; exact Nat.lt_of_lt_of_le hy3 (Nat.le_add_right _ _))
            (Nat.ne_of_lt hy3), hT6z y hyL (Nat.ne_of_lt hy3)]
          exact hy
      have hreach := (hrT3.tc_target hI3.sound.good).2
      have hok := hI3.sound.nodes L hreach _ hLm
      simp only [reduceCtorEq, ite_false] at hok
      simp only [nodeOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hok
      obtain ⟨-, hptr⟩ := hok
      have hsameF : ∀ z, z ≠ L → z ∉ ids → (treeOf i s wf).obj z = (treeOf i s w3).obj z := by
        intro z hzL hzi
        by_cases hz6 : (wA.withNode L n').next ≤ z
        · rw [hnone z hz6 hzi]
          exact ((treeOf_fresh hb hI3.books (by omega)).1).symm
        · have hzn : z ≠ w3.next := fun e => hzi (e ▸ hhead)
          rw [hsame z (by omega) hzn, hT6z z hzL hzn]
      have hBL : (treeOf i s wf).obj L = some (.key ⟨wLevel s wA L, n'.leaf, ksOf n'⟩) := by
        rw [hsame L (by omega) hLv, hT6]
        simp [Tree.set]
      have hSP := Sound.putSeg (ex' := none) hI3.sound hrT3 hLm hl3 hk2.1 hno hch ?_ ?_ hsameF
      · obtain ⟨hS, hRch⟩ := hSP
        have hrootF : (treeOf i s wf).root = some w3.top.rootKey := by
          rw [hWf.root, htopf]
          rfl
        refine ⟨⟨hWf.root, ?_, hWf.frame, hWf.top, ?_, hWf.books.toBooks hnoe⟩, ?_⟩
        · rw [htopf]
          exact hS
        · -- BalancedOK, by the nodes reached
          refine Balanced.of_reach (N := L :: ids) hI3.balanced (fun z hz => ?_)
            (fun z _ hz => ?_) (fun y m hm => ?_) (fun z hz _ m hm => ?_)
          · rw [reach_of_root hrootF] at hz
            rcases hRch z hz with h1 | h1
            · left
              rw [reach_of_root hI3.root]
              exact h1
            · exact Or.inr (List.mem_cons_of_mem _ h1)
          · simp only [List.mem_cons, not_or] at hz
            exact hsameF z hz.1 hz.2
          · by_cases hyi : y ∈ ids
            · have hy3 : w3.next ≤ y := by
                rcases hids y hyi with h1 | h1
                · exact Nat.le_of_eq h1.symm
                · rw [hn6] at h1
                  omega
              rw [(treeOf_fresh hb hI3.books hy3).1] at hm
              cases hm
            · by_cases hyL : y = L
              · rw [hyL, hLm] at hm
                cases hm
                exact ⟨_, by rw [hyL]; exact hBL, hwlA⟩
              · exact ⟨m, by rw [hsameF y hyL hyi]; exact hm, rfl⟩
          · rcases List.mem_cons.mp hz with hz | hz
            · rw [hz, hBL] at hm
              cases hm
              obtain ⟨h1, h2, -⟩ := hI3.balanced L hrc3 _ hLm
              refine ⟨by rw [hwlA]; exact h1, by rw [hwlA, hleaf']; exact h2, fun hl' => ?_⟩
              rw [hleaf', hl3] at hl'
              cases hl'
            · obtain ⟨h1, h2, h3⟩ := hlvi z hz m hm
              refine ⟨h1, by simp [h2, h3], fun hl' => ?_⟩
              rw [h2] at hl'
              cases hl'
        · -- OldReach: a node reached was reached before, or is new
          refine wput_old_step hb (wput_old_congr hD.old hT3) (fun z hz => ?_)
          rw [reach_of_root hrootF] at hz
          rcases hRch z hz with h1 | h1
          · left
            rw [reach_of_root hI3.root]
            exact h1
          · right
            have h2 := hI3.books.ids.2.2.2.1
            rcases hids z h1 with h3 | h3
            · rw [h3]
              exact h2
            · rw [hn6] at h3
              exact Nat.le_trans h2 (Nat.le_trans (Nat.le_add_right _ 2) h3)
      · show p.keyLevel (g + 1) 0 < wLevel s w3 L
        rw [hlv]
        exact wputs_keyLevel_lt p hg1
      · refine ⟨⟨wLevel s wA L, n'.leaf, ksOf n'⟩, ?_, hwlA, by rw [hleaf']; exact hl3,
          add_key_live hwf cv w3.next, ?_⟩
        · rw [hsame L (by omega) hLv, hT6]
          simp [Tree.set]
        · simp only [bnd, reduceCtorEq, ite_false, nodeOk, Bool.and_eq_true, decide_eq_true_eq,
            List.all_eq_true]
          refine ⟨⟨?_, add_key_wf hwf cv w3.next⟩, ?_⟩
          · rw [ksOf_length]
            have : n'.size ≤ n.size + 2 := add_size n i _
            omega
          · intro k hk
            cases k with
            | key c y =>
              rcases add_key_mem.mp hk with hk | ⟨rfl, rfl⟩
              · exact hBsome y (hptr _ hk)
              · obtain ⟨⟨m, hm, -⟩, -⟩ := hch.tr_props
                show ((treeOf i s wf).obj w3.next).isSome = true
                rw [hm]
                rfl
            | time t => rfl
            | del b => rfl
    · next hc =>
      exfalso
      apply hc
      omega

/-- `putSegs` along the key's route to the segment leaf `leaf` with cv :: rest
left, from the root x of the tree of the segment c. -/
theorem wputs_putSegs {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} {C : List (Key × Nat)} {key : Key} {leaf : NodeId}
    {cv : Nat} {rest : Key} {h : Nat} {T : Tree} {nl : KNode} (hp : ParamsOK p)
    (hs : Shows p v z s tp) (hb : Books i base s tp) (hrne : rest ≠ [])
    (hleafT : T.obj leaf = some (.key nl)) (hno : ∀ y, (cv, y) ∉ live nl.ks)
    (hsize : nl.ks.length + 2 ≤ p.M) :
    ∀ (tail : Key) (c : Nat) (w : MW) (depth : Nat) (x : NodeId), treeOf i s w = T →
      keyWf (c :: tail) = true → DescInvS p i base s tp C key leaf (cv :: rest) c tail w depth x →
      WP (SIS.Tree.putSegs key (some h) (c :: tail) x) { p := p, i := i, view := v } w
        (fun _ w' => w'.outside = [] → PInv p i base s tp none (mapPut key h C) w' ∧
          OldReach i s w') := by
  intro tail
  induction tail with
  | nil =>
    intro c w depth x _ _ hD
    exfalso
    obtain ⟨pre, he⟩ := wputs_route_suffix hD.route
    have := congrArg List.length he
    have hr1 : 0 < rest.length := List.length_pos_iff.mpr hrne
    simp only [List.length_append, List.length_cons, List.length_nil] at this
    omega
  | cons c2 tail2 ih =>
    intro c w depth x hT hk hD
    obtain ⟨pre, he⟩ := wputs_route_suffix hD.route
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact wputs_newseg hp hs hb hrne hk hleafT hno hsize hT hD
    | cons a pre' =>
      have hne : c :: c2 :: tail2 ≠ cv :: rest := by
        intro e
        rw [e] at he
        have := congrArg List.length he
        simp only [List.length_append, List.length_cons] at this
        omega
      have hk2 : keyWf (c2 :: tail2) = true := by
        simp only [keyWf, Bool.and_eq_true] at hk
        exact hk.2
      rw [SIS.Tree.putSegs.eq_3 _ _ _ _ _ (by simp), wp_bind]
      refine (wputs_setNode hs hb hD hne).mono ?_
      rintro r w' ⟨y, depth', rfl, hT', hD'⟩
      exact ih c2 w' depth' y (hT'.trans hT) hk2 hD'

theorem putKv_put_newseg {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} (hp : ParamsOK p) (hs : Shows p v z s tp)
    (hb : Books i base s tp) {done : List Op} {w w' : MW} {b : Bool} {key : Key} {h : Nat}
    (hm : MidP p i base s tp done w) (ho : OldReach i s w) (hkey : keyWf key = true)
    (hroute : ∃ leaf cv rest nl, rest ≠ [] ∧
      Route (treeOf i s w) w.top.rootKey key leaf (cv :: rest) ∧
      (treeOf i s w).obj leaf = some (.key nl) ∧ nl.leaf = true ∧
      (∀ y, (cv, y) ∉ live nl.ks) ∧ nl.ks.length + 2 ≤ p.M)
    (hrun : SIS.Tree.putKv (.put key h) { p := p, i := i, view := v } w = .ok (b, w'))
    (hout : w'.outside = []) :
    MidP p i base s tp (done ++ [Op.put key h]) w' ∧ OldReach i s w' := by
  suffices hW : WP (SIS.Tree.putKv (.put key h)) { p := p, i := i, view := v } w
      (fun _ w' => w'.outside = [] →
        MidP p i base s tp (done ++ [Op.put key h]) w' ∧ OldReach i s w') from
    hW b w' hrun hout
  have hC : applyOps (done ++ [Op.put key h]) (contents s) =
      mapPut key h (applyOps done (contents s)) := by
    rw [applyOps, List.foldl_append]
    rfl
  simp only [MidP, hC]
  obtain ⟨leaf, cv, rest, nl, hrne, hr, hleafo, hnl, hno, hsize⟩ := hroute
  unfold SIS.Tree.putKv
  refine wput_ok (pathClear_eq _ _) ?_
  refine wput_ok (w' := { w with path := [(none, w.top.rootKey)] }) rfl ?_
  dsimp only
  cases key with
  | nil => simp [keyWf] at hkey
  | cons c tail =>
    exact wputs_putSegs hp hs hb hrne hleafo hno hsize tail c _ 0 _ rfl hkey
      ⟨hm.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl, rfl, ⟨none, rfl⟩, rfl,
        fun d hd => absurd hd (Nat.not_lt_zero d), fun d hd => absurd hd (Nat.not_lt_zero d),
        ⟨0, none, hm.sound.good⟩, ⟨nl, hleafo, hnl⟩, hr, hr,
        fun d hd => absurd hd (Nat.not_lt_zero d), by
          show w.top.rootKey ∈ reach (treeOf i s w)
          rw [reach_of_root hm.root]
          exact tc_self _ _ _, wput_old_congr ho rfl⟩

/-! ## 5. A transaction of puts of both kinds -/

/-- The premise of `putKv_put_routed`: the key is routed to a segment leaf
with its last segment left. -/
def RoutedPre (i : Time) (s : Tree) (w : MW) (key : Key) : Prop :=
  ∃ leaf cv nl, Route (treeOf i s w) w.top.rootKey key leaf [cv] ∧
    (treeOf i s w).obj leaf = some (.key nl) ∧ nl.leaf = true

/-- The premise of `putKv_put_newseg`: the key is routed to a segment leaf
with two segments or more left, the leaf has no live klong of the first, and
room for one more. -/
def NewSegPre (p : MParams) (i : Time) (s : Tree) (w : MW) (key : Key) : Prop :=
  ∃ leaf cv rest nl, rest ≠ [] ∧ Route (treeOf i s w) w.top.rootKey key leaf (cv :: rest) ∧
    (treeOf i s w).obj leaf = some (.key nl) ∧ nl.leaf = true ∧
    (∀ y, (cv, y) ∉ live nl.ks) ∧ nl.ks.length + 2 ≤ p.M

/-- The writer accepts the operations one by one, each a put of a key as
`Keys.toSegments` makes it that, in the state it runs from, is routed to a
segment leaf with its last segment left (`RoutedPre`), or with more segments
left whose trees do not exist and room in the leaf (`NewSegPre`), with no key
node outside G and H after any of them. -/
inductive OpsRunPuts (c : SIS.Tree.Ctx) (s : Tree) : MW → List MOp → MW → Prop where
  | nil (w : MW) : OpsRunPuts c s w [] w
  | cons (w w1 w' : MW) (key : Key) (h : Nat) (ops : List MOp) (b : Bool) :
      keyWf key = true → (RoutedPre c.i s w key ∨ NewSegPre c.p c.i s w key) →
      SIS.Tree.putKv (.put key h) c w = .ok (b, w1) → w1.outside = [] →
      OpsRunPuts c s w1 ops w' →
      OpsRunPuts c s w (.put key h :: ops) w'

/-- Such a run is a run (`OpsRun`). -/
theorem OpsRunPuts.opsRun {c : SIS.Tree.Ctx} {s : Tree} {w w' : MW} {ops : List MOp}
    (h : OpsRunPuts c s w ops w') : OpsRun c w ops w' := by
  induction h with
  | nil w => exact OpsRun.nil w
  | cons w w1 w' key h ops b hk _ h1 h2 _ ih => exact OpsRun.cons w w1 w' _ ops b hk h1 h2 ih

/-- A routed run (WriterPutG.lean) is such a run. -/
theorem OpsRunRouted.opsRunPuts {c : SIS.Tree.Ctx} {s : Tree} {w w' : MW} {ops : List MOp}
    (h : OpsRunRouted c s w ops w') : OpsRunPuts c s w ops w' := by
  induction h with
  | nil w => exact OpsRunPuts.nil w
  | cons w w1 w' key h ops b hk hr h1 h2 _ ih =>
    exact OpsRunPuts.cons w w1 w' key h ops b hk (Or.inl hr) h1 h2 ih

/-- One transaction of puts of both kinds: the model's writer meets the
writer's contract (`WriterMeets`' conclusion), from a tree whose key klongs
name its nodes (`SNamed`). -/
def WriterMeetsPuts (p : MParams) (ops : List MOp) : Prop :=
  ∀ (i : Time) (base : NodeId) (s : Tree) (tp : Top) (v : View BVal) (z : NodeId) (t : SIS.Tree.Top)
    (w : MW),
    SNamed s → Before p i base s tp → Shows p v z s tp → SIS.Tree.topOf p v z = .ok t →
    OpsRunPuts { p := p, i := i, view := v } s { next := base, top := t } ops w →
    Contract (cpOf p) i s (ops.map opOf) (dirtyOf w) (treeOf i s w) ∧
      TreeOk ((treeOf i s w).at i) ∧ TopStep i tp (topOf i tp w) ∧
      (treeOf i s w).roots = rootsOf (topOf i tp w) ∧
      invOk (cpOf p) (treeOf i s w) = true ∧ TreeOk (treeOf i s w) ∧
      Balanced p (treeOf i s w) ∧
      (∀ x n, (treeOf i s w).obj x = some (.key n) → ∃ t rest, n.ks = Klong.time t :: rest) ∧
      (∀ x n, (treeOf i s w).obj x = some (.key n) → timesBefore (i + 1) n.ks = true) ∧
      (∀ r ∈ (treeOf i s w).roots, r.1 < i + 1) ∧
      (∀ x, w.next ≤ x → (treeOf i s w).obj x = none ∧ (topOf i tp w).node x = none) ∧
      (∀ z zn, (topOf i tp w).getLast? = some (z, zn) → ∀ q ∈ zn.skips,
        ((topOf i tp w).node q.2.1).map (·.time) = some q.2.2)

/-- The accepted puts of both kinds keep `MidP` and `OldReach`. -/
theorem wputs_midP_run {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} (hp : ParamsOK p) (hs : Shows p v z s tp)
    (hb : Books i base s tp) (hn : SNamed s) :
    ∀ (ops : List MOp) (w w' : MW), OpsRunPuts { p := p, i := i, view := v } s w ops w' →
      ∀ done, MidP p i base s tp done w → OldReach i s w →
        MidP p i base s tp (done ++ ops.map opOf) w' ∧ OldReach i s w' := by
  intro ops w w' hrun
  induction hrun with
  | nil w => intro done hm ho; exact ⟨by simpa using hm, ho⟩
  | cons w w1 w' key h ops b hk hr h1 h2 _ ih =>
    intro done hm ho
    have hm1 : MidP p i base s tp (done ++ [Op.put key h]) w1 ∧ OldReach i s w1 := by
      rcases hr with hr | hr
      · exact putKv_put_routed hp hs hb hn hm ho hk hr h1 h2
      · exact putKv_put_newseg hp hs hb hm ho hk hr h1 h2
    obtain ⟨this, ho'⟩ := ih _ hm1.1 hm1.2
    exact ⟨by simpa [opOf] using this, ho'⟩

/-- A transaction of puts of both kinds meets the writer's contract. -/
theorem writerMeets_puts {p : MParams} (hp : ParamsOK p) (ops : List MOp) :
    WriterMeetsPuts p ops := by
  intro i base s tp v z t w hn hbf hs ht hrun
  have hb := hbf.books
  have hm : MidP p i base s tp (ops.map opOf) w := by
    have := (wputs_midP_run hp hs hb hn ops _ w hrun [] (wput_midP_start hs ht hbf)
      (wput_old_start i s base t)).1
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

end Contract
