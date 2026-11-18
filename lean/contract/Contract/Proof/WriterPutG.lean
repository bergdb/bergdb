/-
The contract package (bergdb 030-10): a put of a key of any number of
segments whose segment trees exist: the key is routed from the space root,
through the segment leaves' long klongs, to the segment leaf of its last
segment. (A put that makes a new segment leaf is not here.)
-/
import Contract.Proof.WriterPut
import Contract.Proof.WriterTimeSplitG
import Contract.Proof.WriterSpaceSplitG

namespace Contract

open SIS (View)
open SIS.Check (BVal)

/-! ## 1. The recursion up the path -/

/-- `getNode` leaves `outside` as it is. -/
theorem wputg_getNode_outside (c : SIS.Tree.Ctx) (w : MW) (x : NodeId) :
    WP (SIS.Tree.getNode x) c w (fun _ w' => w'.outside = w.outside) := by
  unfold SIS.Tree.getNode
  simp only [wp_bind, wp_get]
  split
  · rw [wp_pure]
  · simp only [wp_bind, wp_read]
    split
    · split
      · exact wp_throw _ _ _ _
      · simp only [wp_bind, wp_set, wp_pure]
    · exact wp_throw _ _ _ _

/-- One level of `appendKlongs` removes no node from `outside`, if the levels
above it remove none. -/
theorem wputg_append_outside_step (c : SIS.Tree.Ctx) (depth : Nat)
    (hup : ∀ d, depth = d + 1 → ∀ q ins (w : MW),
      WP (SIS.Tree.appendKlongs d q ins) c w (fun _ w' => w'.outside = [] → w.outside = [])) :
    ∀ x ins (w : MW),
      WP (SIS.Tree.appendKlongs depth x ins) c w
        (fun _ w' => w'.outside = [] → w.outside = []) := by
  intro x ins w
  rw [wput_appendKlongs_eq]
  refine wput_read ?_
  rw [wp_bind]
  refine (wputg_getNode_outside c w x).mono ?_
  intro n w1 h1
  dsimp only
  have hup' : ∀ q ins (w : MW), WP ((match depth with
      | 0 => fun _ _ => throw "corrupt: a split's parent above depth 0"
      | d + 1 => fun q more => SIS.Tree.appendKlongs d q more :
        NodeId → List (Nat × NodeId) → SIS.Tree.M Unit) q ins) c w
        (fun _ w' => w'.outside = [] → w.outside = []) := by
    cases depth with
    | zero => intro q ins w; exact wp_throw _ _ _ _
    | succ d => exact hup d rfl
  split
  · exact (handleFullWith_outside hup' _ _ _ _ _ w1).mono (fun _ w' h ho => h1 ▸ h ho)
  · split
    · exact (handleFullWith_outside hup' _ _ _ _ _ w1).mono (fun _ w' h ho => h1 ▸ h ho)
    · unfold SIS.Tree.addKeys
      refine wput_read ?_
      rw [wp_bind]
      refine (wputg_getNode_outside c w1 x).mono ?_
      intro n2 w2 h2 r w' hr
      rw [putNode_eq] at hr
      simp only [Except.ok.injEq, Prod.mk.injEq] at hr
      obtain ⟨-, rfl⟩ := hr
      intro ho
      rw [← h1, ← h2]
      exact ho

/-- `appendKlongs` removes no node from `outside`. -/
theorem wputg_append_outside (c : SIS.Tree.Ctx) (d : Nat) :
    ∀ q ins (w : MW),
      WP (SIS.Tree.appendKlongs d q ins) c w (fun _ w' => w'.outside = [] → w.outside = []) := by
  induction d with
  | zero => exact wputg_append_outside_step c 0 (fun d h => absurd h (by omega))
  | succ d ih =>
    exact wputg_append_outside_step c (d + 1) (fun d' h => by
      obtain rfl : d = d' := by omega
      exact ih)

/-- One level of `appendKlongs`, given the levels above it, a parent a
segment leaf or not (`wput_append_step` with `CasPreG`). -/
theorem wputg_append_step {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} (hp : ParamsOK p) (hb : Books i base s tp) (hn : SNamed s) (depth : Nat)
    (hup : ∀ d, depth = d + 1 →
      UpOkG p i base s tp v (fun q ins => SIS.Tree.appendKlongs d q ins) d) :
    UpOkG p i base s tp v (fun q ins => SIS.Tree.appendKlongs depth q ins) depth := by
  intro x ins w n C h
  simp only []
  rw [wput_appendKlongs_eq]
  refine wput_read (wput_ok (getNode_hit _ h.look) ?_)
  dsimp only
  split
  · by_cases h2 : (n.lastVersion i).size ≤ p.splitAbove
    · refine handleFull_time_g hp hb h ?_ (Or.inr ⟨rfl, h2⟩)
      intro d hd; subst hd; exact hup d rfl
    · refine handleFull_space_g hp hb hn h ?_ ?_ (by omega)
      · intro d hd; subst hd; exact hup d rfl
      · intro d hd; subst hd; exact wputg_append_outside _ d
  · next h1 =>
    split
    · refine handleFull_time_g hp hb h ?_ (Or.inl ⟨rfl, by omega⟩)
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

/-- `appendKlongs` meets the statement at every depth, a parent a segment leaf
or not. -/
theorem appendKlongs_spec_g {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} (hp : ParamsOK p) (hb : Books i base s tp) (hn : SNamed s) :
    ∀ d, UpOkG p i base s tp v (fun q ins => SIS.Tree.appendKlongs d q ins) d := by
  intro d
  induction d with
  | zero => exact wputg_append_step hp hb hn 0 (fun d h => absurd h (by omega))
  | succ d ih =>
    exact wputg_append_step hp hb hn (d + 1) (fun d' h => by
      obtain rfl : d = d' := by omega
      exact ih)

/-! ## 2. The descent along the key's route -/

/-- A route from an inner node: its first step is by the last live klong at
or below the key's first segment. -/
theorem wputg_route_inner {T : Tree} {x leaf : NodeId} {c cv : Nat} {rest : Key} {m nl : KNode}
    (hr : Route T x (c :: rest) leaf [cv]) (hx : T.obj x = some (.key m)) (hml : m.leaf = false)
    (hleaf : T.obj leaf = some (.key nl)) (hnl : nl.leaf = true) :
    ∃ c' y, (c', y) ∈ live m.ks ∧ c' ≤ c ∧
      (∀ c'' y'', (c'', y'') ∈ live m.ks → c'' ≤ c → c'' ≤ c') ∧
      Route T y (c :: rest) leaf [cv] := by
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
theorem wputg_route_leaf {T : Tree} {x leaf : NodeId} {c cv : Nat} {rest : Key} {m : KNode}
    (hr : Route T x (c :: rest) leaf [cv]) (hx : T.obj x = some (.key m)) (hml : m.leaf = true) :
    (x = leaf ∧ c = cv ∧ rest = []) ∨
      ∃ y, (c, y) ∈ live m.ks ∧ isLong c = true ∧ Route T y rest leaf [cv] := by
  cases hr with
  | here => exact Or.inl ⟨rfl, rfl, rfl⟩
  | inner u n c' y cv' rest' q k' hobj hl =>
    rw [hx] at hobj
    cases hobj
    rw [hml] at hl
    cases hl
  | leaf u n c' y rest' q k' hobj hl hm hlong hr =>
    rw [hx] at hobj
    cases hobj
    exact Or.inr ⟨y, hm, hlong, hr⟩

theorem wputg_good_wf {T : Tree} {x : NodeId} {lo : Nat} {hi : Option Nat} {m : KNode}
    (h : Good T x lo hi) (hx : T.obj x = some (.key m)) : klongsWf m.ks = true := by
  cases h with
  | mk x lo hi n hobj hwf =>
    rw [hx] at hobj
    cases hobj
    exact hwf

/-- Along the key access path up to D, the levels of the map fall: each node
is on a lower level than the node before it. -/
def LevDown (i : Time) (s : Tree) (w : MW) (D : Nat) : Prop :=
  ∀ d, d < D → ∀ c u c' u' m m', w.path[d]? = some (c, u) → w.path[d + 1]? = some (c', u') →
    (treeOf i s w).obj u = some (.key m) → (treeOf i s w).obj u' = some (.key m') →
    m'.level < m.level

/-- A path of the tree whose levels fall has no node twice. -/
theorem wputg_nodup {i : Time} {s : Tree} {w : MW} {D : Nat} (hP : PathOk i s w D)
    (hL : LevDown i s w D) :
    ∀ e e' c c' u, e < e' → e' ≤ D → w.path[e]? = some (c, u) →
      w.path[e']? = some (c', u) → False := by
  have hobj : ∀ d, d ≤ D → ∃ c u m, w.path[d]? = some (c, u) ∧
      (treeOf i s w).obj u = some (.key m) := by
    intro d hd
    obtain ⟨c, u, n, h1, h2, h3⟩ := hP.nodes d hd
    exact ⟨c, u, _, h1, treeOf_obj_overlay i s h2 h3⟩
  have hdec : ∀ k e c u m, e + k + 1 ≤ D → w.path[e]? = some (c, u) →
      (treeOf i s w).obj u = some (.key m) → ∀ c' u' m', w.path[e + k + 1]? = some (c', u') →
      (treeOf i s w).obj u' = some (.key m') → m'.level < m.level := by
    intro k
    induction k with
    | zero =>
      intro e c u m he h1 h2 c' u' m' h3 h4
      exact hL e (by omega) c u c' u' m m' h1 h3 h2 h4
    | succ k ih =>
      intro e c u m he h1 h2 c' u' m' h3 h4
      obtain ⟨c2, u2, m2, h5, h6⟩ := hobj (e + k + 1) (by omega)
      have a := ih e c u m (by omega) h1 h2 c2 u2 m2 h5 h6
      have b := hL (e + k + 1) (by omega) c2 u2 c' u' m2 m' h5
        (by rw [show e + k + 1 + 1 = e + (k + 1) + 1 by omega]; exact h3) h6 h4
      omega
  intro e e' c c' u hlt hle h1 h2
  obtain ⟨c3, u3, m, h3, h4⟩ := hobj e (by omega)
  rw [h1] at h3
  cases h3
  obtain ⟨k, rfl⟩ : ∃ k, e' = e + k + 1 := ⟨e' - e - 1, by omega⟩
  have := hdec k e c u m hle h1 h4 c' u m h2 h4
  omega

/-- The child of a live klong of a node reached is reached. -/
theorem wputg_reach_kid {T : Tree} {r x y : NodeId} {n : KNode} {c : Nat} {lo : Nat}
    {hi : Option Nat} (hG : Good T r lo hi) (hroot : T.root = some r) (hx : x ∈ reach T)
    (hxn : T.obj x = some (.key n)) (hm : (c, y) ∈ live n.ks) : y ∈ reach T := by
  rw [reach_of_root hroot] at hx ⊢
  have h1 : y ∈ reachAt T (T.fuel x) x := by
    rw [show T.fuel x = n.level + 1 by simp [Tree.fuel, hxn]]
    exact tc_kid hxn hm (tc_self _ _ _)
  exact hG.tr_closed hx h1

/-- Before `descendLte` with the segment c from node x at `depth` of the key
access path, x not read yet: `PInv` with no node over its size; the path
ends with x and starts at the space root; each node above x is in the
overlay, and its live klong names the next node; x is sound; the key is
routed from the space root to the segment leaf `leaf` with [cv] left, and
from x with c :: rest left. -/
structure DescInvG (p : MParams) (i : Time) (base : NodeId) (s : Tree) (tp : Top)
    (C : List (Key × Nat)) (key : Key) (leaf : NodeId) (cv : Nat) (c : Nat) (rest : Key)
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
  full : Route (treeOf i s w) w.top.rootKey key leaf [cv]
  route : Route (treeOf i s w) x (c :: rest) leaf [cv]
  lev : LevDown i s w depth
  reached : x ∈ reach (treeOf i s w)
  old : OldReach i s w

/-- After the descent with the segment c from the state w: the map and the
super root as in w; `PInv`; the node returned is a segment leaf of the
overlay, the last of the path, sound, and the key is routed from it with
c :: rest left; the path is a path of the tree. -/
def DescPostG (p : MParams) (i : Time) (base : NodeId) (s : Tree) (tp : Top)
    (C : List (Key × Nat)) (leaf : NodeId) (cv : Nat) (c : Nat) (rest : Key) (w : MW) :
    NodeId → MW → Prop :=
  fun L w' => treeOf i s w' = treeOf i s w ∧ w'.top = w.top ∧
    PInv p i base s tp none C w' ∧ (∃ nl, w'.nodes.lookup L = some nl ∧ nl.leaf = true) ∧
    (∃ c0, w'.path[w'.path.length - 1]? = some (c0, L)) ∧
    PathOk i s w' (w'.path.length - 1) ∧ (∃ lo hi, Good (treeOf i s w') L lo hi) ∧
    Route (treeOf i s w') L (c :: rest) leaf [cv] ∧ LevDown i s w' (w'.path.length - 1) ∧
    L ∈ reach (treeOf i s w')

/-- The descent in a segment tree along the key's route: from a state with
`DescInvG`, every result of `descendLte` meets `DescPostG`. -/
theorem wputg_descend {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} {C : List (Key × Nat)} {key : Key} {leaf : NodeId}
    {cv c : Nat} {rest : Key} (hs : Shows p v z s tp) (hb : Books i base s tp) :
    ∀ (f : Nat) (w : MW) (depth : Nat) (x : NodeId),
      DescInvG p i base s tp C key leaf cv c rest w depth x →
      WP (SIS.Tree.descendLte c f x) { p := p, i := i, view := v } w
        (DescPostG p i base s tp C leaf cv c rest w) := by
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
        obtain ⟨c', y, hm', hle', hmax', hr'⟩ := wputg_route_inner hD.route hxm hml hnl hnll
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
        have hD2 : DescInvG p i base s tp C key leaf cv c rest w2 (depth + 1) fd.y := by
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
            show Route (treeOf i s w) w1.top.rootKey key leaf [cv]
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

/-! ## 3. The put -/

/-- The state after the new value, with the value's klong added to the
segment leaf, meets `PInv` with the leaf over its size and holds the keys
with the put applied (`Sound.put`); and the leaf, of a sound tree, is well
formed and fits a node; `OldReach` is kept. `wput_put_fact` for a key of any
number of segments. -/
theorem wputg_put_fact {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {C : List (Key × Nat)} (hb : Books i base s tp) {w : MW} {leaf : NodeId} {nl : MNode}
    {key : Key} {cv h : Nat} (hI : PInv p i base s tp none C w) (ho : OldReach i s w)
    (hlk : w.nodes.lookup leaf = some nl)
    (ht : w.taken.contains leaf = false) (hl : nl.leaf = true)
    (hr : Route (treeOf i s w) w.top.rootKey key leaf [cv]) (hcv : isLong cv = false) :
    (PInv p i base s tp (some leaf) (mapPut key h C)
      ((w.afterNewValue h).withNode leaf (nl.add i (.key cv w.next))) ∧
      OldReach i s ((w.afterNewValue h).withNode leaf (nl.add i (.key cv w.next)))) ∧
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
  refine ⟨⟨hI.root, hSnd, ?_, hI.top, ?_, ?_⟩, ?_⟩
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
  · -- OldReach: a node reached was reached before, or is the new value
    refine wput_old_step hb ho (fun z hz => ?_)
    rw [reach_of_root hrootW] at hz
    rcases hRch z hz with h1 | h1
    · left
      rw [reach_of_root hI.root]
      exact h1
    · right
      rw [h1]
      exact hI.books.ids.2.2.2.1

/-- `setNode` for a segment of the key but the last: the descent to the
segment leaf, whose live long klong of the segment names the root of the next
segment's tree (the route's leaf step: `searchEq` finds it); the path goes on
to that root. -/
theorem wputg_setNode {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} {C : List (Key × Nat)} {key : Key} {leaf : NodeId}
    {cv c c2 : Nat} {rest : Key} (hs : Shows p v z s tp) (hb : Books i base s tp) {w : MW}
    {depth : Nat} {x : NodeId}
    (hD : DescInvG p i base s tp C key leaf cv c (c2 :: rest) w depth x) :
    WP (SIS.Tree.setNode x c true) { p := p, i := i, view := v } w
      (fun r w' => ∃ y depth', r = some y ∧
        DescInvG p i base s tp C key leaf cv c2 rest w' depth' y) := by
  unfold SIS.Tree.setNode
  refine wput_read ?_
  rw [wp_bind]
  refine (wputg_descend hs hb _ w depth x hD).mono ?_
  rintro L (w3 : MW) ⟨hT3, htop3, hI3, ⟨nl, hlk3, hl3⟩, ⟨c0, hc0⟩, hP3, ⟨lo, hi, hGL⟩, hr3, hlev3,
    hrc3⟩
  obtain ⟨-, -, ht3⟩ := hP3.lookup (Nat.le_refl _) hc0
  refine wput_ok (getNode_hit _ hlk3) ?_
  have hLm := treeOf_obj_overlay i s hlk3 ht3
  have hwf : klongsWf (ksOf nl) = true := wputg_good_wf hGL hLm
  rcases wputg_route_leaf hr3 hLm hl3 with ⟨-, -, hnil⟩ | ⟨y, hmy, hlong, hry⟩
  · cases hnil
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
    refine ⟨fd.y, D + 1, rfl, hI3.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl, ?_, ⟨_, hpb⟩, ?_, ?_,
      ?_, ⟨lo', hi', hG'⟩, ?_, ?_, hry, ?_, ?_, wput_old_congr hD.old hT3⟩
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
    · show Route (treeOf i s w3) w3.top.rootKey key leaf [cv]
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

/-- `setValue` for the key's last segment c: the descent to the segment leaf
that the key is routed to, then the value's klong added to it, or the leaf
full and `appendKlongs` up the path. -/
theorem wputg_setValue {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} {C : List (Key × Nat)} {key : Key} {leaf : NodeId}
    {cv c h : Nat} (hp : ParamsOK p) (hs : Shows p v z s tp) (hb : Books i base s tp)
    (hn : SNamed s) {w : MW} {depth : Nat} {x : NodeId} (hk : keyWf [c] = true)
    (hD : DescInvG p i base s tp C key leaf cv c [] w depth x) :
    WP (SIS.Tree.setValue x c key (some h)) { p := p, i := i, view := v } w
      (fun _ w' => w'.outside = [] → PInv p i base s tp none (mapPut key h C) w' ∧
        OldReach i s w') := by
  unfold SIS.Tree.setValue
  refine wput_read ?_
  rw [wp_bind]
  refine (wputg_descend hs hb _ w depth x hD).mono ?_
  rintro L (w3 : MW) ⟨hT3, htop3, hI3, ⟨nl, hlk3, hl3⟩, ⟨c0, hc0⟩, hP3, -, hr3, hlev3⟩
  dsimp only
  obtain ⟨-, -, ht3⟩ := hP3.lookup (Nat.le_refl _) hc0
  have hLm := treeOf_obj_overlay i s hlk3 ht3
  have hcv : isLong c = false := wput_isLong hk
  rcases wputg_route_leaf hr3 hLm hl3 with ⟨rfl, rfl, -⟩ | ⟨y, -, hlong, -⟩
  swap
  · rw [hcv] at hlong
    cases hlong
  have hfull : Route (treeOf i s w3) w3.top.rootKey key L [c] := by
    rw [hT3, htop3]
    exact hD.full
  obtain ⟨-, -, hnv, hvv, htv, -⟩ := treeOf_fresh hb hI3.books (Nat.le_refl w3.next)
  obtain ⟨⟨hfact, hold⟩, hwf, hsz⟩ := wputg_put_fact (h := h) hb hI3
    (wput_old_congr hD.old hT3) hlk3 ht3 hl3 hfull hcv
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
    have := add_size nl i (.key c w3.next)
    exact ⟨wput_pinv_fit hfact (lookup_upsert_self _ _ _) (by omega), hold⟩
  · refine wput_ok (pathSize_eq _ _) ?_
    rw [wp_bind]
    refine (appendKlongs_spec_g hp hb hn _ L [(c, w3.next)] (w3.afterNewValue h) nl _
      ⟨hlk3, ⟨c0, hc0⟩, pathOk_afterNewValue h hP3 hnv hvv htv,
        wputg_nodup (w := w3) hP3 hlev3.1,
        putBooks_afterNewValue hI3.books h, hwf, hsz, Or.inl rfl,
        fun a y1 b y2 he => by simp at he, hfact⟩).mono ?_
    intro r W hW
    rw [wp_pure]
    intro hout
    obtain ⟨hPW, hCW⟩ := hW hout
    refine ⟨hPW, wput_old_step hb hold (fun z hz => ?_)⟩
    rw [reach_of_root hPW.root] at hz
    rcases hCW.reach z hz with h1 | h1
    · left
      rw [reach_of_root hfact.root]
      exact h1
    · right
      have h2 : (w3.afterNewValue h).next = w3.next + 2 := rfl
      have h3 := hI3.books.ids.2.2.2.1
      omega

/-- `putSegs` over the segments c :: rest of the key that are left, from
their segment tree's root x. -/
theorem wputg_putSegs {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} {C : List (Key × Nat)} {key : Key} {leaf : NodeId}
    {cv h : Nat} (hp : ParamsOK p) (hs : Shows p v z s tp) (hb : Books i base s tp)
    (hn : SNamed s) :
    ∀ (rest : Key) (c : Nat) (w : MW) (depth : Nat) (x : NodeId), keyWf (c :: rest) = true →
      DescInvG p i base s tp C key leaf cv c rest w depth x →
      WP (SIS.Tree.putSegs key (some h) (c :: rest) x) { p := p, i := i, view := v } w
        (fun _ w' => w'.outside = [] → PInv p i base s tp none (mapPut key h C) w' ∧
          OldReach i s w') := by
  intro rest
  induction rest with
  | nil =>
    intro c w depth x hk hD
    rw [SIS.Tree.putSegs.eq_2]
    exact wputg_setValue hp hs hb hn hk hD
  | cons c2 rest ih =>
    intro c w depth x hk hD
    rw [SIS.Tree.putSegs.eq_3 _ _ _ _ _ (by simp), wp_bind]
    refine (wputg_setNode hs hb hD).mono ?_
    rintro r w' ⟨y, depth', rfl, hD'⟩
    have hk' : keyWf (c2 :: rest) = true := by
      simp only [keyWf, Bool.and_eq_true] at hk
      exact hk.2
    exact ih c2 w' depth' y hk' hD'

/-- A put of a key whose segment trees exist keeps `MidP` and `OldReach`. -/
theorem putKv_put_routed {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} (hp : ParamsOK p) (hs : Shows p v z s tp)
    (hb : Books i base s tp) (hn : SNamed s) {done : List Op} {w w' : MW} {b : Bool} {key : Key}
    {h : Nat} (hm : MidP p i base s tp done w) (ho : OldReach i s w) (hkey : keyWf key = true)
    (hroute : ∃ leaf cv nl, Route (treeOf i s w) w.top.rootKey key leaf [cv] ∧
      (treeOf i s w).obj leaf = some (.key nl) ∧ nl.leaf = true)
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
  obtain ⟨leaf, cv, nl, hr, hleafo, hnl⟩ := hroute
  unfold SIS.Tree.putKv
  refine wput_ok (pathClear_eq _ _) ?_
  refine wput_ok (w' := { w with path := [(none, w.top.rootKey)] }) rfl ?_
  dsimp only
  cases key with
  | nil => simp [keyWf] at hkey
  | cons c rest =>
    exact wputg_putSegs hp hs hb hn rest c _ 0 _ hkey
      ⟨hm.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl, rfl, ⟨none, rfl⟩, rfl,
        fun d hd => absurd hd (Nat.not_lt_zero d), fun d hd => absurd hd (Nat.not_lt_zero d),
        ⟨0, none, hm.sound.good⟩, ⟨nl, hleafo, hnl⟩, hr, hr,
        fun d hd => absurd hd (Nat.not_lt_zero d), by
          show w.top.rootKey ∈ reach (treeOf i s w)
          rw [reach_of_root hm.root]
          exact tc_self _ _ _, wput_old_congr ho rfl⟩

/-! ## 4. A transaction of such puts -/

/-- The writer accepts the operations one by one, each a put of a key as
`Keys.toSegments` makes it that is routed, in the state it runs from, from
the space root to a segment leaf (the key's segment trees exist), with no key
node outside G and H after any of them. -/
inductive OpsRunRouted (c : SIS.Tree.Ctx) (s : Tree) : MW → List MOp → MW → Prop where
  | nil (w : MW) : OpsRunRouted c s w [] w
  | cons (w w1 w' : MW) (key : Key) (h : Nat) (ops : List MOp) (b : Bool) :
      keyWf key = true →
      (∃ leaf cv nl, Route (treeOf c.i s w) w.top.rootKey key leaf [cv] ∧
        (treeOf c.i s w).obj leaf = some (.key nl) ∧ nl.leaf = true) →
      SIS.Tree.putKv (.put key h) c w = .ok (b, w1) → w1.outside = [] →
      OpsRunRouted c s w1 ops w' →
      OpsRunRouted c s w (.put key h :: ops) w'

/-- A routed run is a run (`OpsRun`). -/
theorem OpsRunRouted.opsRun {c : SIS.Tree.Ctx} {s : Tree} {w w' : MW} {ops : List MOp}
    (h : OpsRunRouted c s w ops w') : OpsRun c w ops w' := by
  induction h with
  | nil w => exact OpsRun.nil w
  | cons w w1 w' key h ops b hk _ h1 h2 _ ih => exact OpsRun.cons w w1 w' _ ops b hk h1 h2 ih

/-- One transaction of routed puts: the model's writer meets the writer's
contract (`WriterMeets`' conclusion), from a tree whose key klongs name its
nodes (`SNamed`). -/
def WriterMeetsRouted (p : MParams) (ops : List MOp) : Prop :=
  ∀ (i : Time) (base : NodeId) (s : Tree) (tp : Top) (v : View BVal) (z : NodeId) (t : SIS.Tree.Top)
    (w : MW),
    SNamed s → Before p i base s tp → Shows p v z s tp → SIS.Tree.topOf p v z = .ok t →
    OpsRunRouted { p := p, i := i, view := v } s { next := base, top := t } ops w →
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

/-- The accepted routed puts keep `MidP` and `OldReach`. -/
theorem wputg_midP_run {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} (hp : ParamsOK p) (hs : Shows p v z s tp)
    (hb : Books i base s tp) (hn : SNamed s) :
    ∀ (ops : List MOp) (w w' : MW), OpsRunRouted { p := p, i := i, view := v } s w ops w' →
      ∀ done, MidP p i base s tp done w → OldReach i s w →
        MidP p i base s tp (done ++ ops.map opOf) w' ∧ OldReach i s w' := by
  intro ops w w' hrun
  induction hrun with
  | nil w => intro done hm ho; exact ⟨by simpa using hm, ho⟩
  | cons w w1 w' key h ops b hk hr h1 h2 _ ih =>
    intro done hm ho
    obtain ⟨hm1, ho1⟩ := putKv_put_routed hp hs hb hn hm ho hk hr h1 h2
    obtain ⟨this, ho'⟩ := ih _ hm1 ho1
    exact ⟨by simpa [opOf] using this, ho'⟩

/-- A transaction of routed puts meets the writer's contract. -/
theorem writerMeets_routed {p : MParams} (hp : ParamsOK p) (ops : List MOp) :
    WriterMeetsRouted p ops := by
  intro i base s tp v z t w hn hbf hs ht hrun
  have hb := hbf.books
  have hm : MidP p i base s tp (ops.map opOf) w := by
    have := (wputg_midP_run hp hs hb hn ops _ w hrun [] (wput_midP_start hs ht hbf)
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
