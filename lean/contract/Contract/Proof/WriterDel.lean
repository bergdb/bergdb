/-
The contract package (bergdb 030-10): the first delete. A delete of a key of
one segment, by the writer with the merges and option 2 off (the parameters
of release 2026.4), whose segment leaf has room for a bitmap and keeps a
live klong: the leaf gets the bitmap (`Dag.appendDeleteKlong`: a new bitmap
klong, or the bits in the transaction's own bitmap), nothing else changes.
Also the delete of a key that the tree does not hold, a noop. The delete
keeps `MidP` (`putKv_del1_leaf`). With the merges on, the same delete of a key
whose leaf is the space root or keeps at least m live klongs: the merges'
descent finds the leaf and makes no merge (`putKv_del1_leaf_merges`).
-/
import Contract.Proof.WriterPut
import Contract.Proof.NodeAlg3
import Contract.Proof.TreeRulesDel

namespace Contract

open SIS (View)
open SIS.Tree (Ctx)
open SIS.Check (BVal)

/-! ## 1. Helpers -/

/-- `fresh` keeps the books: only the next id grows. -/
theorem wdel_books_next {p : MParams} {i : Time} {base : NodeId} {s : Tree} {w : MW}
    (hk : PutBooks p i base s w) : PutBooks p i base s { w with next := w.next + 2 } := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hk.ids
  refine ⟨hk.first, hk.times, hk.levels, ⟨fun x n hx => ?_, fun x h hx => ?_, fun m hm => ?_,
    ?_, fun ht => ?_⟩, hk.taken, hk.overlay, hk.within, hk.timeFirst⟩
  · have := h1 x n hx
    show x < w.next + 2
    omega
  · have := h2 x h hx
    show x < w.next + 2
    omega
  · have := h3 m hm
    exact ⟨by show m.id < w.next + 2; omega, this.2⟩
  · show base ≤ w.next + 2
    omega
  · have := h5 ht
    show w.top.id < w.next + 2
    omega

/-- `fresh` keeps `PInv`. -/
theorem wdel_pinv_next {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {ex : Option NodeId} {C : List (Key × Nat)} {w : MW} (hI : PInv p i base s tp ex C w) :
    PInv p i base s tp ex C { w with next := w.next + 2 } :=
  hI.of_map rfl (fun _ hy => hy) rfl rfl (wdel_books_next hI.books)

/-- The state with the segment leaf set to n', a node with the leaf's live
klongs but those of cv, well formed, of the leaf's kind and first klong, with
no other key klongs and no time after i, that fits a node and extends the
leaf's klongs of s: it meets `PInv` and holds the keys with the delete
(`Sound.del`). -/
theorem wdel_fact {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {C : List (Key × Nat)} {w : MW} {leaf : NodeId} {nl n' : MNode} {cv : Nat}
    (hI : PInv p i base s tp none C w) (hlk : w.nodes.lookup leaf = some nl)
    (ht : w.taken.contains leaf = false) (hl : nl.leaf = true)
    (hr : Route (treeOf i s w) w.top.rootKey [cv] leaf [cv]) (hcv : isLong cv = false)
    (hkeep : dropCv cv (live (ksOf nl)) ≠ [])
    (hlive : live (ksOf n') = dropCv cv (live (ksOf nl)))
    (hwf : klongsWf (ksOf n') = true)
    (hkey : ∀ c y, Klong.key c y ∈ ksOf n' → Klong.key c y ∈ ksOf nl)
    (hsz : n'.size ≤ p.M) (hleaf : n'.leaf = nl.leaf) (hfst : n'.ks.head? = nl.ks.head?)
    (htimes : TimesLe n' i)
    (hext : ∀ n0, s.obj leaf = some (.key n0) →
      ksOf n' = n0.ks ∨ ∃ more, ksOf n' = n0.ks ++ Klong.time i :: more) :
    PInv p i base s tp none (mapDel [cv] C) (w.withNode leaf n') := by
  have hAx := treeOf_obj_overlay i s hlk ht
  have hreach := (hr.tc_target hI.sound.good).2
  have hok := hI.sound.nodes leaf hreach _ hAx
  simp only [reduceCtorEq, ite_false, nodeOk, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true] at hok
  obtain ⟨-, hptr⟩ := hok
  have hTW : treeOf i s (w.withNode leaf n') =
      (treeOf i s w).set leaf (.key ⟨wLevel s w leaf, n'.leaf, ksOf n'⟩) :=
    treeOf_withNode i s n' ht
  have hBx : NodeIs (treeOf i s (w.withNode leaf n')) leaf (wLevel s w leaf) true
      (dropCv cv (live (ksOf nl))) (bnd p.M none leaf) := by
    refine ⟨⟨wLevel s w leaf, n'.leaf, ksOf n'⟩, ?_, rfl, by rw [hleaf]; exact hl, hlive,
      ?_⟩
    · rw [hTW]
      simp [Tree.set]
    · simp only [bnd, reduceCtorEq, ite_false, nodeOk, Bool.and_eq_true, decide_eq_true_eq,
        List.all_eq_true]
      refine ⟨⟨by rw [ksOf_length]; exact hsz, hwf⟩, fun k hk => ?_⟩
      cases k with
      | key c y =>
        rw [hTW]
        exact wput_set_isSome (hptr _ (hkey c y hk))
      | time t => rfl
      | del b => rfl
  have hsame : ∀ z, z ≠ leaf →
      (treeOf i s (w.withNode leaf n')).obj z = (treeOf i s w).obj z := by
    intro z hz
    rw [hTW]
    simp [Tree.set, hz]
  obtain ⟨hSnd, hRch⟩ := Sound.del (ex' := none) hI.sound hr hAx hl hcv (Or.inl hkeep) hBx hsame
  have hrootW : (treeOf i s (w.withNode leaf n')).root = some w.top.rootKey := hI.root
  refine ⟨hI.root, hSnd, frame_withNode hI.frame hlk ht hleaf hext, hI.top, ?_,
    putBooks_withNode hI.books hlk ht hleaf hfst (timesLe_model htimes)⟩
  -- BalancedOK, by the nodes reached: they are among those reached before
  refine Balanced.of_reach (N := [leaf]) hI.balanced (fun z hz => ?_) (fun z _ hz => ?_)
    (levels_kept_withNode i s n' hlk ht) (fun z hz _ m hm => ?_)
  · rw [reach_of_root hrootW] at hz
    left
    rw [reach_of_root hI.root]
    exact hRch z hz
  · exact hsame z (by simpa using hz)
  · simp only [List.mem_singleton] at hz
    subst hz
    rw [hTW] at hm
    simp only [Tree.set, ite_true, Option.some.injEq, Obj.key.injEq] at hm
    subst hm
    have hLr : z ∈ reach (treeOf i s w) := by
      rw [reach_of_root hI.root]
      exact hreach
    obtain ⟨h1, h2, -⟩ := hI.balanced z hLr _ hAx
    refine ⟨h1, by rw [hleaf]; exact h2, fun hl' => ?_⟩
    rw [hleaf, hl] at hl'
    cases hl'

/-! ## 2. The delete's steps -/

/-- A route of the key [cv] to a segment leaf x is a route in a tree that
differs from the first only at x. -/
theorem wdel_route {A B : Tree} {x : NodeId} {nx : KNode} {cv : Nat} (hcv : isLong cv = false)
    (hAx : A.obj x = some (.key nx)) (hl : nx.leaf = true)
    (hsame : ∀ z, z ≠ x → B.obj z = A.obj z) {u : NodeId} (hr : Route A u [cv] x [cv]) :
    Route B u [cv] x [cv] := by
  suffices h : ∀ u k q k', Route A u k q k' → k = [cv] → q = x → Route B u k q k' from
    h u _ _ _ hr rfl rfl
  intro u k q k' hr
  induction hr with
  | here q k => intro _ _; exact Route.here _ _
  | inner u n c y cv' rest q k' hu hn hc hle hmax _ ih =>
    intro hk hq
    have hux : u ≠ x := by
      intro e
      rw [e, hAx] at hu
      cases hu
      rw [hl] at hn
      cases hn
    exact Route.inner u n c y cv' rest q k' (by rw [hsame u hux]; exact hu) hn hc hle hmax
      (ih hk hq)
  | leaf u n c y rest q k' _ _ _ hlong _ _ =>
    intro hk _
    simp only [List.cons.injEq] at hk
    rw [hk.1, hcv] at hlong
    cases hlong

/-- `deleteUpward` of the segment leaf that the key [cv] is routed to, which
keeps a live klong and has room for a bitmap, with option 2 off: a noop, or
the bitmap in the leaf and then `afterDelete`; given that `afterDelete` keeps
`PInv` from the state with the bitmap, the delete keeps it. -/
theorem wdel_core {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} (hb : Books i base s tp) {C : List (Key × Nat)} {cv : Nat}
    (hcv : isLong cv = false) (hth : p.theta = 0) {w3 : MW} {leaf : NodeId} {nl : MNode}
    (hI3 : PInv p i base s tp none C w3) (hlk3 : w3.nodes.lookup leaf = some nl)
    (ht3 : w3.taken.contains leaf = false) (hl3 : nl.leaf = true)
    (hr3 : Route (treeOf i s w3) w3.top.rootKey [cv] leaf [cv])
    (hroom : nl.size + 2 ≤ p.M) (hkeep : dropCv cv (live (ksOf nl)) ≠ []) (d : Nat)
    (had : ∀ g h (w4 : MW) (n' : MNode), w3.gh.lookup leaf = some (g, h) →
      PInv p i base s tp none (mapDel [cv] C) w4 → w4.top = w3.top → w4.gh = w3.gh →
      w4.nodes.lookup leaf = some n' → w4.taken.contains leaf = false →
      live (ksOf n') = dropCv cv (live (ksOf nl)) → n'.leaf = nl.leaf →
      Route (treeOf i s w4) w4.top.rootKey [cv] leaf [cv] →
      WP (SIS.Tree.afterDelete [cv] g h) { p := p, i := i, view := v } w4
        (fun _ w5 => PInv p i base s tp none (mapDel [cv] C) w5)) :
    WP (SIS.Tree.deleteUpward leaf d cv [cv]) { p := p, i := i, view := v } w3
      (fun _ w4 => PInv p i base s tp none (mapDel [cv] C) w4) := by
  have hAx := treeOf_obj_overlay i s hlk3 ht3
  unfold SIS.Tree.deleteUpward
  refine wput_read ?_
  refine wput_ok (getNode_hit _ hlk3) ?_
  have hreach := (hr3.tc_target hI3.sound.good).2
  have hok := hI3.sound.nodes leaf hreach _ hAx
  have hok' := hok
  simp only [reduceCtorEq, ite_false, nodeOk, Bool.and_eq_true, decide_eq_true_eq] at hok'
  have hwf0 : klongsWf (ksOf nl) = true := hok'.1.2
  dsimp only
  split
  · next hno =>
    rw [wp_pure]
    have hsame := delUnion_noop hwf0 hno
    exact ⟨hI3.root, (Sound.del hI3.sound hr3 hAx hl3 hcv (Or.inl hkeep)
      ⟨_, hAx, rfl, hl3, hsame.symm, hok⟩ (fun _ _ => rfl)).1, hI3.frame, hI3.top,
      hI3.balanced, hI3.books⟩
  · next hnn =>
    split
    · obtain ⟨g, h, hgh, -, -, -, -⟩ := hI3.books.levels leaf nl hlk3 ht3
      refine wput_ok (ghOf_hit _ hlk3 hgh) ?_
      rw [wp_bind]
      dsimp only
      -- the state with the bitmap, and what `afterDelete` needs of it
      have hnext : ∀ (n' : MNode) (t : String),
          PInv p i base s tp none (mapDel [cv] C) (w3.withNode leaf n') →
          live (ksOf n') = dropCv cv (live (ksOf nl)) → n'.leaf = nl.leaf →
          WP (SIS.Tree.afterDelete [cv] g h) { p := p, i := i, view := v }
            (MW.withNode { w3 with trail := t :: w3.trail } leaf n')
            (fun _ w5 => PInv p i base s tp none (mapDel [cv] C) w5) := by
        intro n' t hI4 hlive hleaf'
        have hTW := treeOf_withNode i s n' ht3
        refine had g h _ n' hgh (hI4.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl) rfl rfl
          (lookup_upsert_self _ _ _) ht3 hlive hleaf' ?_
        show Route (treeOf i s (w3.withNode leaf n')) w3.top.rootKey [cv] leaf [cv]
        rw [hTW]
        exact wdel_route hcv hAx hl3 (fun z hz => by simp [Tree.set, hz]) hr3
      unfold SIS.Tree.appendDeleteKlong
      refine wput_read ?_
      refine wput_ok (getNode_hit _ hlk3) ?_
      dsimp only
      split
      · rw [wp_bind]
        exact wp_throw _ _ _ _
      · have hdu : SIS.Tree.bitsUnion nl.lastBitmap (nl.bitsOf cv) = delUnion nl cv := rfl
        simp only [hdu] at hnn ⊢
        refine wp_ite _ _ _ _ _ _ (fun _ => ?_) (fun h0 => absurd (by simpa using hnn) h0)
        obtain ⟨t0, rest, hr0⟩ := hI3.books.timeFirst leaf nl hlk3 ht3
        have hT0 := wput_timesLe hI3.books hlk3
        refine wp_ite _ _ _ _ _ _ (fun htd => ?_) (fun _ => ?_)
        · have htd' : hasTransDel nl i = true := htd
          refine wp_ite _ _ _ _ _ _ (fun hd => absurd hd (by simp [SIS.Tree.deadOver, hth]))
            (fun _ => ?_)
          refine wput_ok (note_eq _ _ _) ?_
          refine wput_ok (putNode_eq _ _ _ _) ?_
          rw [wp_pure, wp_bind]
          refine WP.mono (hnext _ _ ?_ (setDel_live hwf0 htd' cv) (setDel_leaf _ _)) ?_
          · obtain ⟨rest', hr1⟩ := setDel_first htd' hr0 (delUnion nl cv)
            refine wdel_fact hI3 hlk3 ht3 hl3 hr3 hcv hkeep (setDel_live hwf0 htd' cv)
              (setDel_wf hwf0 htd' cv) (fun c y h => (setDel_key_mem htd').mp h)
              (by rw [setDel_size]; omega) (setDel_leaf _ _) (by rw [hr1, hr0]; rfl)
              (setDel_timesLe hT0 _) (fun n0 hs0 => ?_)
            obtain ⟨-, -, he⟩ := frame_overlay_ext hI3.frame hlk3 ht3 hs0
            exact Or.inr (setDel_ext (prim_timesBefore (hb.times leaf n0 hs0)) htd' he _)
          · intro _ w5 h5
            rw [wp_pure]
            exact h5
        · refine wp_ite _ _ _ _ _ _ (fun _ => ?_) (fun hfull => absurd (by omega) hfull)
          refine wp_ite _ _ _ _ _ _ (fun hd => absurd hd (by simp [SIS.Tree.deadOver, hth]))
            (fun _ => ?_)
          refine wput_ok (note_eq _ _ _) ?_
          refine wput_ok (putNode_eq _ _ _ _) ?_
          rw [wp_pure, wp_bind]
          refine WP.mono (hnext _ _ ?_ (addDel_live hwf0 cv) (add_leaf _ _ _)) ?_
          · obtain ⟨rest', hr1⟩ := add_first (t := i) (.del (delUnion nl cv)) hr0
            have := add_size nl i (.del (delUnion nl cv))
            refine wdel_fact hI3 hlk3 ht3 hl3 hr3 hcv hkeep (addDel_live hwf0 cv)
              (addDel_wf hwf0 cv) (fun c y h => addDel_key_mem.mp h)
              (by omega) (add_leaf _ _ _) (by rw [hr1, hr0]; rfl)
              (add_timesLe hT0 _ (fun t' e => by cases e)) (fun n0 hs0 => ?_)
            obtain ⟨-, -, he⟩ := frame_overlay_ext hI3.frame hlk3 ht3 hs0
            exact add_ext (prim_timesBefore (hb.times leaf n0 hs0)) he _
          · intro _ w5 h5
            rw [wp_pure]
            exact h5
    · next hall =>
      exfalso
      exact hkeep ((allKeysIn_iff hwf0 cv).mp (by simpa [delUnion] using hall))

/-- `putKv` of a delete of the key [cv]: the descent, then `deleteUpward`, then
`fresh` if it was no noop; given what the leaf meets in the state after the
descent and that `deleteUpward` keeps `PInv` from there, the delete keeps
`MidP`. -/
theorem wdel_putKv {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} (hs : Shows p v z s tp) (hb : Books i base s tp)
    {done : List Op} {w : MW} {cv : Nat} (hm : MidP p i base s tp done w)
    (hdel : ∀ (leaf : NodeId) (w3 : MW) (nl : MNode),
      PInv p i base s tp none (applyOps done (contents s)) w3 →
      w3.nodes.lookup leaf = some nl → w3.taken.contains leaf = false → nl.leaf = true →
      Route (treeOf i s w3) w3.top.rootKey [cv] leaf [cv] →
      treeOf i s w3 = treeOf i s w → w3.top = w.top →
      WP (SIS.Tree.deleteUpward leaf (w3.path.length - 1) cv [cv])
        { p := p, i := i, view := v } w3
        (fun _ w4 => PInv p i base s tp none (mapDel [cv] (applyOps done (contents s))) w4)) :
    WP (SIS.Tree.putKv (.del [cv])) { p := p, i := i, view := v } w
      (fun _ w' => MidP p i base s tp (done ++ [Op.del [cv]]) w') := by
  have hC : applyOps (done ++ [Op.del [cv]]) (contents s) =
      mapDel [cv] (applyOps done (contents s)) := by
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
  rintro leaf (w3 : MW) ⟨hT3, htop3, hI3, ⟨nl, hlk3, hl3⟩, ⟨c0, hc0⟩, hP3, -, hr3⟩
  dsimp only
  obtain ⟨-, -, ht3⟩ := hP3.lookup (Nat.le_refl _) hc0
  refine wput_ok (pathSize_eq _ _) ?_
  rw [wp_bind]
  refine (hdel leaf w3 nl hI3 hlk3 ht3 hl3 hr3 hT3 htop3).mono ?_
  intro noop w4 h4
  split
  · refine wput_ok (f := SIS.Tree.fresh) (a := w4.next) (w' := { w4 with next := w4.next + 2 })
      rfl ?_
    rw [wp_pure]
    exact wdel_pinv_next h4
  · rw [wp_pure]
    exact h4

/-! ## 3. The delete with the merges off -/

/-- A delete of a key of one segment whose segment leaf has room for a bitmap
and keeps a live klong, with the merges and option 2 off, keeps `MidP`. -/
theorem putKv_del1_leaf {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} (hs : Shows p v z s tp) (hb : Books i base s tp)
    {done : List Op} {w w' : MW} {b : Bool} {cv : Nat}
    (hm : MidP p i base s tp done w) (hcv : isLong cv = false) (hth : p.theta = 0)
    (hmg : p.merges = false)
    (hleaf : ∀ leaf nl, Route (treeOf i s w) w.top.rootKey [cv] leaf [cv] →
      (treeOf i s w).obj leaf = some (.key nl) → nl.leaf = true →
      nl.ks.length + 2 ≤ p.M ∧ (live nl.ks).filter (fun a => a.1 != cv) ≠ [])
    (hrun : SIS.Tree.putKv (.del [cv]) { p := p, i := i, view := v } w = .ok (b, w')) :
    MidP p i base s tp (done ++ [Op.del [cv]]) w' := by
  refine wdel_putKv hs hb hm (fun leaf w3 nl hI3 hlk3 ht3 hl3 hr3 hT3 htop3 => ?_) b w' hrun
  have hAx := treeOf_obj_overlay i s hlk3 ht3
  obtain ⟨hroom, hkeep⟩ := hleaf leaf _ (by rw [← hT3, ← htop3]; exact hr3)
    (by rw [← hT3]; exact hAx) hl3
  refine wdel_core hb hcv hth hI3 hlk3 ht3 hl3 hr3 (by rw [← ksOf_length]; exact hroom) hkeep _
    (fun g h w4 n' _ hI4 _ _ _ _ _ _ _ => ?_)
  unfold SIS.Tree.afterDelete
  refine wput_read ?_
  dsimp only
  simp only [hmg, Bool.false_eq_true, ↓reduceIte]
  rw [wp_pure]
  exact hI4

/-! ## 4. The delete with the merges on: no merge -/

/-- `ghOf` of a key node of the map: it reads the node into the overlay (as
`getNode_spec`) and gives its segment and height, height 0 exactly for a
segment leaf. -/
theorem wdel_ghOf {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} {C : List (Key × Nat)} {w : MW}
    (hs : Shows p v z s tp) (hb : Books i base s tp) (hI : PInv p i base s tp none C w)
    {x : NodeId} {m : KNode} (hx : (treeOf i s w).obj x = some (.key m))
    (hxr : x ∈ reach (treeOf i s w)) :
    ∃ n w1 g h, SIS.Tree.ghOf x { p := p, i := i, view := v } w = .ok ((g, h), w1) ∧
      w1.nodes.lookup x = some n ∧ ksOf n = m.ks ∧ n.leaf = m.leaf ∧ n.leaf = (h == 0) ∧
      treeOf i s w1 = treeOf i s w ∧ PInv p i base s tp none C w1 ∧ w1.path = w.path ∧
      w1.top = w.top ∧ ∀ y n0, w.nodes.lookup y = some n0 → w1.nodes.lookup y = some n0 := by
  obtain ⟨n, w1, hget, hks, hleaf, hlk1, hT1, hI1, hw1, -⟩ := getNode_spec hs hb hI hx hxr
  have htx : w1.taken.contains x = false := wput_taken (o := .key m) (by rw [hT1]; exact hx)
  obtain ⟨g, h, hgh, -, -, -, hlh⟩ := hI1.books.levels x n hlk1 htx
  have hfield : w1.path = w.path ∧ w1.top = w.top ∧
      ∀ y n0, w.nodes.lookup y = some n0 → w1.nodes.lookup y = some n0 := by
    rcases hw1 with rfl | ⟨-, gh, rfl⟩
    · exact ⟨rfl, rfl, fun _ _ h => h⟩
    · exact ⟨rfl, rfl, fun _ _ h => prim_lookup_append_some _ h⟩
  refine ⟨n, w1, g, h, ?_, hlk1, hks, hleaf, hlh, hT1, hI1, hfield⟩
  unfold SIS.Tree.ghOf
  show (SIS.Tree.getNode x _ w).bind _ = _
  rw [hget]
  show (match w1.gh.lookup x with
    | some v => pure v
    | none => _ : SIS.Tree.M (Nat × Nat)) _ w1 = _
  rw [hgh]
  rfl

open SIS.Tree in
/-- `descendHeight`, one step unfolded. -/
theorem wdel_dh_succ (cv h f : Nat) (x : NodeId) :
    descendHeight cv h (f + 1) x = (do
      let c ← read
      let (_, hx) ← ghOf x
      if hx == h then return
      let n ← getNode x
      if n.leaf || hx < h then
        throw s!"Bug: merge descent at {c.i}: key node {x} at height {hx} is above no node \
          at height {h}"
      match n.searchLte c.i cv with
      | none => throw s!"corrupt: key node {x}, not a segment leaf, has no klong at or below \
          the key at {c.i}"
      | some fd =>
        pathAdd (some fd.c) fd.y
        descendHeight cv h f fd.y) := rfl

/-- Two routes, one after the other. -/
theorem wdel_route_trans {A : Tree} {u q q' : NodeId} {k k' k'' : Key}
    (h1 : Route A u k q k') (h2 : Route A q k' q' k'') : Route A u k q' k'' := by
  revert h2
  induction h1 with
  | here => exact id
  | inner u n c y cv rest q k' hobj hl hm hle hmax _ ih =>
    exact fun h2 => Route.inner u n c y cv rest _ _ hobj hl hm hle hmax (ih h2)
  | leaf u n c y rest q k' hobj hl hm hlong _ ih =>
    exact fun h2 => Route.leaf u n c y rest _ _ hobj hl hm hlong (ih h2)

/-- The descent of the merges (`descendHeight` to height 0) from node x, the
last of the key access path, along the route of the key [cv] to the segment
leaf `leaf`: it keeps the map and `PInv`, and extends the path to end at the
leaf, with an inner node of the overlay before it if it extended the path at
all, which it does if x is not the leaf. -/
theorem wdel_descendHeight {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} {C : List (Key × Nat)} {cv : Nat} {leaf : NodeId}
    {ml : KNode} (hs : Shows p v z s tp) (hb : Books i base s tp) (hcv : isLong cv = false)
    (hml : ml.leaf = true) :
    ∀ (f : Nat) (u : MW) (x : NodeId), PInv p i base s tp none C u →
      (treeOf i s u).obj leaf = some (.key ml) →
      Route (treeOf i s u) x [cv] leaf [cv] →
      Route (treeOf i s u) u.top.rootKey [cv] x [cv] →
      (∃ c0, u.path[u.path.length - 1]? = some (c0, x)) →
      WP (SIS.Tree.descendHeight cv 0 f x) { p := p, i := i, view := v } u
        (fun _ u' => PInv p i base s tp none C u' ∧ treeOf i s u' = treeOf i s u ∧
          u'.top = u.top ∧
          (∃ pre, u'.path = u.path ++ pre ∧ (x = leaf → pre = []) ∧
            (∃ c0, u'.path[u'.path.length - 1]? = some (c0, leaf)) ∧
            (pre ≠ [] → ∃ c0 q nq, u'.path[u'.path.length - 2]? = some (c0, q) ∧
              u'.nodes.lookup q = some nq ∧ nq.leaf = false)) ∧
          ∀ y n0, u.nodes.lookup y = some n0 → u'.nodes.lookup y = some n0) := by
  intro f
  induction f with
  | zero =>
    intro u x _ _ _ _ _
    exact wp_throw _ _ _ _
  | succ f ih =>
    intro u x hI hlo hr hrx hlast
    rw [wdel_dh_succ]
    refine wput_read ?_
    have hxr : x ∈ reach (treeOf i s u) := by
      rw [reach_of_root hI.root]
      exact (hrx.tc_target hI.sound.good).2
    cases hr with
    | here =>
      obtain ⟨n, u1, g, h, hgh, -, -, hl1, hlh, hT1, hI1, hp1, htop1, hext1⟩ :=
        wdel_ghOf hs hb hI hlo hxr
      refine wput_ok hgh ?_
      have h0 : h = 0 := by
        rw [hl1, hml] at hlh
        simpa using hlh.symm
      subst h0
      refine wp_ite _ _ _ _ _ _ (fun _ => ?_) (fun hne => absurd rfl hne)
      rw [wp_pure]
      exact ⟨hI1, hT1, htop1, ⟨[], by rw [hp1, List.append_nil], fun _ => rfl,
        by rw [hp1]; exact hlast, fun h => absurd rfl h⟩, hext1⟩
    | inner _ n c y _ _ _ _ hobj hnl hc hle hmax hry =>
      obtain ⟨nx, u1, g, h, hgh, hlk1, hks, hl1, hlh, hT1, hI1, hp1, htop1, hext1⟩ :=
        wdel_ghOf hs hb hI hobj hxr
      refine wput_ok hgh ?_
      have hh : h ≠ 0 := by
        intro e
        rw [e, hl1, hnl] at hlh
        simp at hlh
      refine wp_ite _ _ _ _ _ _ (fun he => absurd (by simpa using he) hh) (fun _ => ?_)
      refine wput_ok (getNode_hit _ hlk1) ?_
      refine wp_ite _ _ _ _ _ _ (fun hbad => absurd hbad (by simp [hl1, hnl])) (fun _ => ?_)
      split
      · exact wp_throw _ _ _ _
      · next fd hfd =>
        obtain ⟨hm, hle', hmax'⟩ := searchLte_some (wput_timesLe hI1.books hlk1) hfd
        rw [hks] at hm hmax'
        have hcc : fd.c = c := Nat.le_antisymm (hmax fd.c fd.y hm hle') (hmax' c y hc hle)
        have hyy : fd.y = y := (Prod.mk.inj (sorted_unique (live_sorted _) hm hc hcc)).2
        refine wput_ok (pathAdd_eq _ _ _ _) ?_
        have hT2 : treeOf i s { u1 with path := u1.path ++ [(some fd.c, fd.y)] } =
            treeOf i s u := hT1
        refine (ih { u1 with path := u1.path ++ [(some fd.c, fd.y)] } fd.y
          (hI1.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl) (by rw [hT2]; exact hlo)
          (by rw [hT2, hyy]; exact hry) ?_ ⟨some fd.c, by simp⟩).mono ?_
        · rw [hT2]
          show Route _ u1.top.rootKey _ _ _
          rw [htop1, hyy]
          exact wdel_route_trans hrx
            (Route.inner _ n c y _ [] y [cv] hobj hnl hc hle hmax (Route.here y [cv]))
        rintro _ u' ⟨hI', hT', htop', ⟨pre, hpre, -, hlast', hsec⟩, hext'⟩
        have hpre' : u'.path = u.path ++ [(some fd.c, fd.y)] ++ pre := by
          rw [hpre, ← hp1]
        refine ⟨hI', hT'.trans hT2, htop'.trans htop1,
          ⟨(some fd.c, fd.y) :: pre, by rw [hpre']; simp, ?_, hlast', fun _ => ?_⟩,
          fun y0 n0 h0 => hext' y0 n0 (hext1 y0 n0 h0)⟩
        · intro hxl
          exfalso
          rw [hxl, hlo] at hobj
          cases hobj
          rw [hml] at hnl
          cases hnl
        · by_cases hpe : pre = []
          · subst hpe
            obtain ⟨c0, hc0⟩ := hlast
            have hlen : 0 < u.path.length := by
              have := (List.getElem?_eq_some_iff.mp hc0).1
              omega
            refine ⟨c0, _, nx, ?_, hext' _ nx hlk1, by rw [hl1, hnl]⟩
            rw [hpre', List.append_nil, List.getElem?_append_left (by simp; omega)]
            simpa [Nat.add_sub_cancel] using hc0
          · exact hsec hpe
    | leaf _ _ _ _ _ _ _ _ _ _ hlong _ =>
      rw [hcv] at hlong
      cases hlong

/-- `afterDelete` with the merges on, after the bitmap in the segment leaf
that the key [cv] is routed to (height 0): the merges' descent ends at the
leaf, which is the space root or keeps at least m live klongs, so no merge is
made and nothing changes but the path. -/
theorem wdel_afterDelete {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} {C : List (Key × Nat)} {cv : Nat} (hs : Shows p v z s tp)
    (hb : Books i base s tp) (hcv : isLong cv = false) (hmg : p.merges = true) {w4 : MW}
    {leaf : NodeId} {n' : MNode} (hI4 : PInv p i base s tp none C w4)
    (hlk4 : w4.nodes.lookup leaf = some n') (ht4 : w4.taken.contains leaf = false)
    (hl4 : n'.leaf = true) (hr4 : Route (treeOf i s w4) w4.top.rootKey [cv] leaf [cv])
    (hcnt : leaf = w4.top.rootKey ∨ p.mergeBelow ≤ (live (ksOf n')).length) (g : Nat) :
    WP (SIS.Tree.afterDelete [cv] g 0) { p := p, i := i, view := v } w4
      (fun _ w5 => PInv p i base s tp none C w5) := by
  unfold SIS.Tree.afterDelete
  refine wput_read ?_
  dsimp only
  simp only [hmg, ↓reduceIte]
  rw [wp_bind]
  refine WP.mono (post := fun r w5 => r = false ∧ PInv p i base s tp none C w5) ?_ ?_
  · rw [show p.fuel = ((p.G + 1) * (p.H + 2) + 1) + 1 from rfl, SIS.Tree.mergeUp.eq_2]
    refine wput_read ?_
    rw [wp_bind]
    refine WP.mono (post := fun d u' => PInv p i base s tp none C u' ∧
      u'.nodes.lookup leaf = some n' ∧ (∃ c0, u'.path[d]? = some (c0, leaf)) ∧
      (d ≠ 0 → ∃ c1 q nq, u'.path[d - 1]? = some (c1, q) ∧ u'.nodes.lookup q = some nq ∧
        nq.leaf = false) ∧ (d ≠ 0 → p.mergeBelow ≤ (live (ksOf n')).length)) ?_ ?_
    · -- the merges' descent
      unfold SIS.Tree.descendToHeight
      refine wput_read ?_
      rw [wp_bind]
      rcases Nat.eq_zero_or_pos g with rfl | hg
      · unfold SIS.Tree.descendToSegmentRoot
        refine wput_read ?_
        refine wput_ok (pathClear_eq _ _) ?_
        refine wput_ok (w' := { w4 with path := [(none, w4.top.rootKey)] }) rfl ?_
        simp only [List.take_zero, List.foldlM_nil]
        rw [wp_pure]
        simp only [List.getElem?_cons_zero]
        rw [wp_bind]
        have hAx := treeOf_obj_overlay i s hlk4 ht4
        refine (wdel_descendHeight hs hb hcv hl4 _ { w4 with path := [(none, w4.top.rootKey)] }
          w4.top.rootKey (hI4.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl) hAx hr4
          (Route.here _ _) ⟨none, rfl⟩).mono ?_
        rintro _ u' ⟨hI', -, -, ⟨pre, hpre, hx, ⟨c0, hlast⟩, hsec⟩, hext'⟩
        refine wput_ok (pathSize_eq _ _) ?_
        rw [wp_pure]
        have hlen : u'.path.length = pre.length + 1 := by
          rw [hpre]
          simp only [List.length_append, List.length_singleton]
          omega
        refine ⟨hI', hext' leaf n' hlk4, ⟨c0, hlast⟩, fun hd => ?_, fun hd => ?_⟩
        · have hpe : pre ≠ [] := by
            intro e
            rw [e] at hlen
            simp only [List.length_nil] at hlen
            omega
          obtain ⟨c1, q, nq, h1, h2, h3⟩ := hsec hpe
          refine ⟨c1, q, nq, ?_, h2, h3⟩
          rw [show u'.path.length - 1 - 1 = u'.path.length - 2 by omega]
          exact h1
        · rcases hcnt with hc | hc
          · exfalso
            have := hx hc.symm
            rw [this] at hlen
            simp only [List.length_nil] at hlen
            omega
          · exact hc
      · intro r u5 _
        have hn : [cv][g]? = none := by simp; omega
        split
        · exact wp_throw _ _ _ _
        · next hsome =>
          rw [hn] at hsome
          cases hsome
    · rintro d u' ⟨hI', hlk', ⟨c0, hd⟩, hq, hcnt'⟩
      refine wp_ite _ _ _ _ _ _ (fun _ => ?_) (fun hd0 => ?_)
      · rw [wp_pure]
        exact ⟨rfl, hI'⟩
      · have hd0' : d ≠ 0 := by simpa using hd0
        obtain ⟨c1, q, nq, hq1, hq2, hq3⟩ := hq hd0'
        refine wput_ok (pathNode_eq _ hd) ?_
        refine wput_ok (pathNode_eq _ hq1) ?_
        refine wput_ok (getNode_hit _ hq2) ?_
        refine wp_ite _ _ _ _ _ _ (fun h => absurd h (by simp [hq3])) (fun _ => ?_)
        refine wput_ok (getNode_hit _ hlk') ?_
        refine wp_ite _ _ _ _ _ _ (fun _ => ?_) (fun h => absurd ?_ h)
        · rw [wp_pure]
          exact ⟨rfl, hI'⟩
        · show p.mergeBelow ≤ n'.cnt
          rw [SIS.Tree.KNode.cnt, mlive_eq]
          exact hcnt' hd0'
  · rintro r w5 ⟨rfl, h5⟩
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [wp_pure]
    exact h5

/-- With the merges on: the delete of `putKv_del1_leaf`, of a key whose
segment leaf is the space root or keeps at least m live klongs after it, makes
no merge and keeps `MidP`. -/
theorem putKv_del1_leaf_merges {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} (hs : Shows p v z s tp) (hb : Books i base s tp)
    {done : List Op} {w w' : MW} {b : Bool} {cv : Nat}
    (hm : MidP p i base s tp done w) (hcv : isLong cv = false) (hth : p.theta = 0)
    (hmg : p.merges = true)
    (hleaf : ∀ leaf nl, Route (treeOf i s w) w.top.rootKey [cv] leaf [cv] →
      (treeOf i s w).obj leaf = some (.key nl) → nl.leaf = true →
      nl.ks.length + 2 ≤ p.M ∧ (live nl.ks).filter (fun a => a.1 != cv) ≠ [] ∧
      (leaf = w.top.rootKey ∨
        p.mergeBelow ≤ ((live nl.ks).filter (fun a => a.1 != cv)).length))
    (hrun : SIS.Tree.putKv (.del [cv]) { p := p, i := i, view := v } w = .ok (b, w')) :
    MidP p i base s tp (done ++ [Op.del [cv]]) w' := by
  refine wdel_putKv hs hb hm (fun leaf w3 nl hI3 hlk3 ht3 hl3 hr3 hT3 htop3 => ?_) b w' hrun
  have hAx := treeOf_obj_overlay i s hlk3 ht3
  obtain ⟨hroom, hkeep, hcnt⟩ := hleaf leaf _ (by rw [← hT3, ← htop3]; exact hr3)
    (by rw [← hT3]; exact hAx) hl3
  refine wdel_core hb hcv hth hI3 hlk3 ht3 hl3 hr3 (by rw [← ksOf_length]; exact hroom) hkeep _
    (fun g h w4 n' hgh hI4 htop4 _ hlk4 ht4 hlive hl4 hr4 => ?_)
  obtain ⟨g', h', hgh', -, -, -, hlh⟩ := hI3.books.levels leaf nl hlk3 ht3
  rw [hgh] at hgh'
  cases hgh'
  have h0 : h = 0 := by
    rw [hl3] at hlh
    simpa using hlh.symm
  subst h0
  refine wdel_afterDelete hs hb hcv hmg hI4 hlk4 ht4 (by rw [hl4]; exact hl3) hr4 ?_ g
  rcases hcnt with hc | hc
  · left
    rw [htop4, htop3]
    exact hc
  · right
    rw [hlive]
    exact hc

end Contract
