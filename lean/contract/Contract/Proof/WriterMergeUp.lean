/-
The contract package (bergdb 030-16): the merges after a delete, for a key of
one segment: `Dag.mergeAfterDelete` (the model's `mergeUp`: from the node at
height h on the key's path, while it is not the root and holds fewer than m
live klongs, it is merged, and after a merge into one node its parent is
checked), then root collapse after a merge (`afterDelete`). Each round descends
again from the space root (`descendToHeight`). The merges keep the keys,
`PInv` and the link book (`afterOkW_on`); with the link book this is the
premise `AfterOk` of `putKv_del1_keep` (WriterDelKeep.lean) with the merges on.

The merge itself is a premise, `MergeOk`, the statement of `merge_spec`
(WriterMerge.lean), so that this file does not depend on its proof; with it the
merges need `WmgFresh` (the klongs name ids below the next) before, and keep it.
-/
import Contract.Proof.WriterMerge
import Contract.Proof.WriterDelKeep

namespace Contract

open SIS (View)
open SIS.Check (BVal)
open SIS.Tree (Ctx)

/-- `AfterOk` with the link book: the merges after a delete changed the node of
segment g at height 0 on the key [cv]'s path keep `PInv`, the keys and
`WcrLink`, from a state whose klongs name ids below the next (`WmgFresh`, a premise
of the merge). Not `WmgFresh` after: root collapse after a merge does not give it
(`collapseRoot_spec` keeps `PInv` and `WcrLink` only). -/
def AfterOkW (p : MParams) (i : Time) (base : NodeId) (s : Tree) (tp : Top) (v : View BVal)
    (cv : Nat) : Prop :=
  ∀ (g : Nat) (w : MW) (C : List (Key × Nat)), PInv p i base s tp none C w → WcrLink i s w →
    WmgFresh i s w →
    WP (SIS.Tree.afterDelete [cv] g 0) { p := p, i := i, view := v } w
      (fun _ w' => w'.outside = [] → PInv p i base s tp none C w' ∧ WcrLink i s w')

/-- The statement of `merge_spec` (WriterMerge.lean, prover C), as a premise, so that the
merges' loop does not wait for its proof: the merge of node x at depth d of the key access
path, not the root, keeps `PInv`, the link book and the fresh ids. -/
def MergeOk (p : MParams) (i : Time) (base : NodeId) (s : Tree) (tp : Top)
    (v : View BVal) : Prop :=
  ∀ (d : Nat) (x : NodeId) (w : MW) (C : List (Key × Nat)),
    PInv p i base s tp none C w → WcrLink i s w → WmgFresh i s w →
    PathOk i s w d → PathInner w d → (∃ c0, w.path[d]? = some (c0, x)) → d ≠ 0 →
    WP (SIS.Tree.merge x d) { p := p, i := i, view := v } w
      (fun _ w' => w'.outside = [] →
        PInv p i base s tp none C w' ∧ WcrLink i s w' ∧ WmgFresh i s w')

/-! ## 1. The merges' descent to a height -/

/-- Before `descendHeight cv h f x` from node x at `depth` of the key access path: `PInv`;
the path ends with x and starts at the space root; each node above x is an inner node of
the overlay whose live klong names the next node; x is a sound node of the map. -/
structure WmuInv (p : MParams) (i : Time) (base : NodeId) (s : Tree) (tp : Top)
    (C : List (Key × Nat)) (w : MW) (depth : Nat) (x : NodeId) : Prop where
  inv : PInv p i base s tp none C w
  len : w.path.length = depth + 1
  last : ∃ c0, w.path[depth]? = some (c0, x)
  root : w.path[0]? = some (none, w.top.rootKey)
  nodes : ∀ d, d < depth → ∃ c u n, w.path[d]? = some (c, u) ∧ w.nodes.lookup u = some n ∧
    w.taken.contains u = false ∧ n.leaf = false
  links : ∀ d, d < depth → ∃ c0 u c y nu, w.path[d]? = some (c0, u) ∧
    w.path[d + 1]? = some (some c, y) ∧ (treeOf i s w).obj u = some (.key nu) ∧
    (c, y) ∈ live nu.ks
  good : ∃ lo hi, Good (treeOf i s w) x lo hi

/-- After the descent from the state w: the map, the super root and the next id as in w;
`PInv`; the path is a path of the tree, of inner nodes above its last node. -/
def WmuPost (p : MParams) (i : Time) (base : NodeId) (s : Tree) (tp : Top)
    (C : List (Key × Nat)) (w : MW) : Unit → MW → Prop :=
  fun _ w' => treeOf i s w' = treeOf i s w ∧ w'.top = w.top ∧ w'.next = w.next ∧
    PInv p i base s tp none C w' ∧ PathOk i s w' (w'.path.length - 1) ∧
    PathInner w' (w'.path.length - 1)

/-- `ghOf` of a key node of the map (as `wdel_ghOf`), and the next id kept. -/
theorem wmu_ghOf {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} {C : List (Key × Nat)} {w : MW}
    (hs : Shows p v z s tp) (hb : Books i base s tp) (hI : PInv p i base s tp none C w)
    {x : NodeId} {m : KNode} (hx : (treeOf i s w).obj x = some (.key m)) :
    ∃ n w1 g h, SIS.Tree.ghOf x { p := p, i := i, view := v } w = .ok ((g, h), w1) ∧
      w1.nodes.lookup x = some n ∧ ksOf n = m.ks ∧ n.leaf = m.leaf ∧
      treeOf i s w1 = treeOf i s w ∧ PInv p i base s tp none C w1 ∧ w1.path = w.path ∧
      w1.top = w.top ∧ w1.next = w.next ∧
      ∀ y n0, w.nodes.lookup y = some n0 → w1.nodes.lookup y = some n0 := by
  obtain ⟨n, w1, hget, hks, hleaf, hlk1, hT1, hI1, hw1, -⟩ := getNode_spec hs hb hI hx
  have htx : w1.taken.contains x = false := wput_taken (o := .key m) (by rw [hT1]; exact hx)
  obtain ⟨g, h, hgh, -, -, -, -⟩ := hI1.books.levels x n hlk1 htx
  have hfield : w1.path = w.path ∧ w1.top = w.top ∧ w1.next = w.next ∧
      ∀ y n0, w.nodes.lookup y = some n0 → w1.nodes.lookup y = some n0 := by
    rcases hw1 with rfl | ⟨-, gh, rfl⟩
    · exact ⟨rfl, rfl, rfl, fun _ _ h => h⟩
    · exact ⟨rfl, rfl, rfl, fun _ _ h => prim_lookup_append_some _ h⟩
  refine ⟨n, w1, g, h, ?_, hlk1, hks, hleaf, hT1, hI1, hfield⟩
  unfold SIS.Tree.ghOf
  show (SIS.Tree.getNode x _ w).bind _ = _
  rw [hget]
  show (match w1.gh.lookup x with
    | some v => pure v
    | none => _ : SIS.Tree.M (Nat × Nat)) _ w1 = _
  rw [hgh]
  rfl

/-- The descent of the merges (`descendHeight` to height h): from a state with `WmuInv`,
every result meets `WmuPost`. -/
theorem wmu_descend {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} {C : List (Key × Nat)} {cv h : Nat} (hs : Shows p v z s tp)
    (hb : Books i base s tp) :
    ∀ (f : Nat) (w : MW) (depth : Nat) (x : NodeId), WmuInv p i base s tp C w depth x →
      WP (SIS.Tree.descendHeight cv h f x) { p := p, i := i, view := v } w
        (WmuPost p i base s tp C w) := by
  intro f
  induction f with
  | zero =>
    intro w depth x _
    exact wp_throw _ _ _ _
  | succ f ih =>
    intro w depth x hD
    rw [wdel_dh_succ]
    refine wput_read ?_
    obtain ⟨lo, hi, hGx⟩ := hD.good
    obtain ⟨m, hxm⟩ := wput_good_obj hGx
    obtain ⟨n, w1, g, hh, hgh, hlk1, hks, hl1, hT1, hI1, hp1, htop1, hnx1, hext1⟩ :=
      wmu_ghOf hs hb hD.inv hxm
    refine wput_ok hgh ?_
    have htx : w1.taken.contains x = false := wput_taken (o := .key m) (by rw [hT1]; exact hxm)
    have htk : ∀ u n0, w.nodes.lookup u = some n0 → w.taken.contains u = false →
        w1.taken.contains u = false := by
      intro u n0 hu htu
      have := treeOf_obj_overlay i s hu htu
      rw [← hT1] at this
      exact wput_taken this
    obtain ⟨c0, hc0⟩ := hD.last
    have hnodes1 : ∀ d, d < depth → ∃ c u n, w1.path[d]? = some (c, u) ∧
        w1.nodes.lookup u = some n ∧ w1.taken.contains u = false ∧ n.leaf = false := by
      intro d hd
      obtain ⟨c, u, n0, h1, h2, h3, h4⟩ := hD.nodes d hd
      exact ⟨c, u, n0, by rw [hp1]; exact h1, hext1 u n0 h2, htk u n0 h2 h3, h4⟩
    have hlinks1 : ∀ d, d < depth → ∃ c0 u c y nu, w1.path[d]? = some (c0, u) ∧
        w1.path[d + 1]? = some (some c, y) ∧ (treeOf i s w1).obj u = some (.key nu) ∧
        (c, y) ∈ live nu.ks := by
      intro d hd
      rw [hp1, hT1]
      exact hD.links d hd
    refine wp_ite _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_)
    · rw [wp_pure]
      have hlen : w1.path.length - 1 = depth := by rw [hp1, hD.len]; omega
      refine ⟨hT1, htop1, hnx1, hI1, ?_, ?_⟩
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
    · refine wput_ok (getNode_hit _ hlk1) ?_
      refine wp_ite _ _ _ _ _ _ (fun _ => wp_throw _ _ _ _) (fun hl => ?_)
      have hnl : n.leaf = false := by
        cases e : n.leaf
        · rfl
        · simp [e] at hl
      split
      · exact wp_throw _ _ _ _
      · next fd hfd =>
        obtain ⟨hm, -, -⟩ := searchLte_some (wput_timesLe hI1.books hlk1) hfd
        rw [hks] at hm
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
        have hGy : ∃ lo hi, Good (treeOf i s w2) fd.y lo hi := by
          rcases hGx.kind hxm hm with ⟨hl', -, -⟩ | ⟨-, m', lo', hi', -, -, -, hg'⟩
          · rw [← hl1, hnl] at hl'
            cases hl'
          · exact ⟨lo', hi', by rw [hT2]; exact hg'⟩
        have hD2 : WmuInv p i base s tp C w2 (depth + 1) fd.y := by
          refine ⟨hI1.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl, ?_, ⟨_, hpb⟩, ?_, ?_, ?_, hGy⟩
          · show (w1.path ++ [(some fd.c, fd.y)]).length = depth + 1 + 1
            rw [List.length_append, hlen1]
            rfl
          · rw [hpa 0 (by omega), hp1]
            exact htop1 ▸ hD.root
          · intro d hd
            rw [hpa d hd]
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hd) with hd | rfl
            · exact hnodes1 d hd
            · exact ⟨c0, x, n, by rw [hp1]; exact hc0, hlk1, htx, hnl⟩
          · intro d hd
            rw [hpa d hd]
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hd) with hd | rfl
            · rw [hpa (d + 1) (by omega)]
              exact hlinks1 d hd
            · exact ⟨c0, x, fd.c, fd.y, m, by rw [hp1]; exact hc0, hpb, by rw [hT2]; exact hxm,
                hm⟩
        refine (ih w2 (depth + 1) fd.y hD2).mono ?_
        rintro _ w' ⟨h1, h2, h3, h4⟩
        exact ⟨h1.trans hT2, h2.trans htop1, h3.trans hnx1, h4⟩

/-- `descendToHeight [cv] 0 h`: from the space root, along the key [cv], to height h; the
depth it gives is that of the path's last node. -/
theorem wmu_descendToHeight {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} {C : List (Key × Nat)} (hs : Shows p v z s tp)
    (hb : Books i base s tp) (cv h : Nat) {w : MW} (hI : PInv p i base s tp none C w) :
    WP (SIS.Tree.descendToHeight [cv] 0 h) { p := p, i := i, view := v } w
      (fun d w' => treeOf i s w' = treeOf i s w ∧ w'.top = w.top ∧ w'.next = w.next ∧
        PInv p i base s tp none C w' ∧ PathOk i s w' d ∧ PathInner w' d) := by
  unfold SIS.Tree.descendToHeight
  refine wput_read ?_
  refine wput_ok (wcr_descend_eq _ w cv) ?_
  simp only [List.getElem?_cons_zero]
  rw [wp_bind]
  have hD : WmuInv p i base s tp C { w with path := [(none, w.top.rootKey)] } 0 w.top.rootKey :=
    ⟨hI.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl, rfl, ⟨none, rfl⟩, rfl,
      fun d hd => absurd hd (Nat.not_lt_zero d), fun d hd => absurd hd (Nat.not_lt_zero d),
      ⟨0, none, hI.sound.good⟩⟩
  refine (wmu_descend (h := h) hs hb _ _ 0 _ hD).mono ?_
  rintro _ w' ⟨hT, htop, hnx, hI', hP, hin⟩
  refine wput_ok (pathSize_eq _ _) ?_
  rw [wp_pure]
  exact ⟨hT, htop, hnx, hI', hP, hin⟩

/-- For a segment g other than 0 the key [cv] has none: `descendToHeight` gives an error. -/
theorem wmu_dth_err {c : Ctx} {w : MW} {cv g h : Nat} (hg : g ≠ 0) (post : Nat → MW → Prop) :
    WP (SIS.Tree.descendToHeight [cv] g h) c w post := by
  unfold SIS.Tree.descendToHeight
  refine wput_read ?_
  rw [wp_bind]
  intro r u _
  have hn : [cv][g]? = none := by simp; omega
  split
  · exact wp_throw _ _ _ _
  · next hsome =>
    rw [hn] at hsome
    cases hsome

/-! ## 2. The loop -/

/-- The merges' loop keeps `PInv`, the link book and the fresh ids, given the merge
(`MergeOk`, `merge_spec`'s statement). (Restated by prover H, wave 4: `MergeOk` in place of
`ParamsOK`, the bound on c and `SNamed`, which only the merge needed; `WmgFresh` before and
after.) -/
theorem mergeUp_spec {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} (hs : Shows p v z s tp) (hb : Books i base s tp)
    (hmerge : MergeOk p i base s tp v) (cv : Nat) :
    ∀ (f h : Nat) (merged : Bool) (w : MW) (C : List (Key × Nat)),
      PInv p i base s tp none C w → WcrLink i s w → WmgFresh i s w →
      WP (SIS.Tree.mergeUp [cv] 0 f h merged) { p := p, i := i, view := v } w
        (fun _ w' => w'.outside = [] →
          PInv p i base s tp none C w' ∧ WcrLink i s w' ∧ WmgFresh i s w') := by
  intro f
  induction f with
  | zero =>
    intro h merged w C _ _ _
    rw [SIS.Tree.mergeUp.eq_1]
    exact wp_throw _ _ _ _
  | succ f ih =>
    intro h merged w C hI hK hF
    rw [SIS.Tree.mergeUp.eq_2]
    refine wput_read ?_
    rw [wp_bind]
    refine (wmu_descendToHeight hs hb cv h hI).mono ?_
    rintro d w1 ⟨hT1, htop1, hnx1, hI1, hP1, hin1⟩
    have hK1 : WcrLink i s w1 := wcr_books_congr hT1 (by rw [htop1]) hK
    have hF1 : WmgFresh i s w1 := by
      intro u nu c y hu hk
      rw [hnx1]
      rw [hT1] at hu
      exact hF u nu c y hu hk
    refine wp_ite _ _ _ _ _ _ (fun _ => ?_) (fun hd0 => ?_)
    · rw [wp_pure]
      exact fun _ => ⟨hI1, hK1, hF1⟩
    · have hd : d ≠ 0 := by simpa using hd0
      obtain ⟨c0, x, nx, hx1, hlkx, -⟩ := hP1.nodes d (Nat.le_refl d)
      obtain ⟨c1, q, nq, hq1, hlkq, -⟩ := hP1.nodes (d - 1) (by omega)
      refine wput_ok (pathNode_eq _ hx1) ?_
      refine wput_ok (pathNode_eq _ hq1) ?_
      refine wput_ok (getNode_hit _ hlkq) ?_
      refine wp_ite _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_)
      · rw [wp_pure]
        exact fun _ => ⟨hI1, hK1, hF1⟩
      refine wput_ok (getNode_hit _ hlkx) ?_
      refine wp_ite _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_)
      · rw [wp_pure]
        exact fun _ => ⟨hI1, hK1, hF1⟩
      rw [wp_bind]
      refine (hmerge d x w1 C hI1 hK1 hF1 hP1 hin1 ⟨c0, hx1⟩ hd).mono ?_
      intro r w2 h2
      refine wp_ite _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_)
      · rw [wp_pure]
        exact h2
      · by_cases ho : w2.outside = []
        · obtain ⟨hI2, hK2, hF2⟩ := h2 ho
          exact ih (h + 1) true w2 C hI2 hK2 hF2
        · exact ((wdk_grow_mergeUp [cv] 0 f (h + 1) true).out _ w2).mono
            (fun _ _ h3 h3o => absurd (h3 h3o) ho)

/-! ## 3. After a delete -/

/-- The merges after a delete, then root collapse after a merge, keep `PInv` and the link
book, given the merge (`MergeOk`). (Restated by prover H, wave 4: `MergeOk` in place of
`ParamsOK` and the bound on c; `SNamed` stays, for root collapse.) -/
theorem afterOkW_on {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} (hs : Shows p v z s tp) (hb : Books i base s tp)
    (hsn : SNamed s) (hmerge : MergeOk p i base s tp v) (cv : Nat) :
    AfterOkW p i base s tp v cv := by
  intro g w C hI hK hF
  unfold SIS.Tree.afterDelete
  refine wput_read ?_
  by_cases hmg : p.merges = true
  · simp only [hmg, ↓reduceIte]
    rw [wp_bind]
    by_cases hg : g = 0
    · subst hg
      refine (mergeUp_spec hs hb hmerge cv p.fuel 0 false w C hI hK hF).mono ?_
      intro b w1 h1
      refine wp_ite _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_)
      · by_cases ho : w1.outside = []
        · obtain ⟨hI1, hK1, -⟩ := h1 ho
          exact collapseRoot_spec hs hb hsn cv p.fuel w1 C hI1 hK1
        · exact ((wdk_grow_collapseRoot [cv] 0 p.fuel).out _ w1).mono
            (fun _ _ h3 h3o => absurd (h3 h3o) ho)
      · rw [wp_pure]
        exact fun ho => ⟨(h1 ho).1, (h1 ho).2.1⟩
    · rw [show p.fuel = ((p.G + 1) * (p.H + 2) + 1) + 1 from rfl, SIS.Tree.mergeUp.eq_2]
      refine wput_read ?_
      rw [wp_bind]
      exact wmu_dth_err hg _
  · simp only [hmg, Bool.false_eq_true, ↓reduceIte]
    rw [wp_pure]
    exact fun _ => ⟨hI, hK⟩

end Contract
