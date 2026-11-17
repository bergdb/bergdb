/-
The contract package (bergdb 030-16): root collapse for a key of one segment,
`Dag.collapseRoot` at the space root (segment 0): while the space root is an
inner node with one live klong, the empty key's, and not a node that the
transaction made otherwise than by a split, its child takes its place: a root
of before is cut back (`unlink`) and the top's root pointer names the child
(`replaceRoot`); a root that a split of the transaction made is taken back
(`takeBackRoot`). The tree rule: `Sound.collapse` (TreeRulesUp.lean).

A root taken back is no node of the map: no node reached from the child names
it, since a key klong of an inner node names a node one level below
(BalancedOK) and every node reached from the child is below the root.

The statement first given (`PInv` and `LinkLive` before, the same after) is
false; `collapseRoot_spec` has two premises more (030-16, prover H, 17
November), and gives `WcrLink` after the step in place of `LinkLive`:

* `WcrLink`, a link book: a key node reached that is no node of s is named,
  by key klongs of other key nodes of the map, by one node at most, and by
  none if it is the space root. Without it: a node u of s, not reached, one
  level above the made root x, in the overlay with its klongs of s, a time
  klong of i and a key klong that names x, meets the frame, BalancedOK (x is
  one level below u) and `LinkLive` (which asks nothing of a node not
  reached, nor of a segment leaf); `takeBackRoot` makes x no node, and u's
  klong names none: BalancedOK fails after the step. (Likewise a dead klong
  to x in a segment leaf reached breaks PointersOK.)
* `SNamed s` (030-10's premise of the tree before): a root of before, cut
  back to its klongs of before, must not name its child if the transaction
  made it, else the next round's take-back of the child leaves a klong to no
  node. With it the klongs of before name nodes of s only.

`ParamsOK` was a premise and is not needed: removed. `LinkLive` (an
earlier link book on the nodes reached only, retired) is not needed either
(wave 3): no proof step reads it, as `WcrLink` says all that a take-back of
the root asks; it was a premise and a conclusion only, and is dropped from
both.
-/
import Contract.Proof.WriterDelDefs
import Contract.Proof.TreeRulesUp
import Contract.Proof.WriterCascadeDefsG

namespace Contract

open SIS (View)
open SIS.Check (BVal)
open SIS.Tree (Ctx)

/-- The link book that root collapse needs: a key node reached that is no node of s is
named, by key klongs of other key nodes of the map, by one node at most, and by none if it is
the space root. -/
def WcrLink (i : Time) (s : Tree) (w : MW) : Prop :=
  ∀ m ∈ reachOf i s w, ∀ mn, (treeOf i s w).obj m = some (.key mn) → s.obj m = none →
    ∀ u nu c, (treeOf i s w).obj u = some (.key nu) → Klong.key c m ∈ nu.ks → u ≠ m →
      m ≠ w.top.rootKey ∧ ∀ u' nu' c', (treeOf i s w).obj u' = some (.key nu') →
        Klong.key c' m ∈ nu'.ks → u' ≠ m → u' = u

/-! ## 1. The node: its one live klong -/

/-- The step of `KNode.onlyLiveKlong`'s loop. -/
def wcrOnlyStep (del : List Nat) (acc : Option (Option (Nat × Nat))) (ki : MKlong × Nat) :
    Option (Option (Nat × Nat)) :=
  match acc with
  | none => none
  | some cur =>
    match ki.1 with
    | .key c _ =>
      if del.contains ki.2 then acc else
        match cur with
        | some (_, cv) => if c != cv then none else some (some (ki.2, c))
        | none => some (some (ki.2, c))
    | _ => acc

/-- The step of `liveWith`'s loop. -/
def wcrLiveStep (del : List Nat) (m : List (Nat × NodeId)) (ki : Klong × Nat) :
    List (Nat × NodeId) :=
  match ki.1 with
  | .key c y => if del.contains ki.2 then m else insertCv c y m
  | _ => m

theorem wcr_onlyLive_eq (n : MNode) :
    n.onlyLiveKlong = (match n.ks.zipIdx.foldl (wcrOnlyStep n.lastBitmap) (some none) with
      | some (some (i, _)) => some i
      | _ => none) := rfl

theorem wcr_live_eq (n : MNode) :
    live (ksOf n) = n.ks.zipIdx.foldl
      (fun m ki => wcrLiveStep (SIS.Tree.lastBitmapOf n.ks) m (kOf ki.1, ki.2)) [] := by
  unfold live liveWith
  rw [lastBitmap_ksOf, ksOf, List.zipIdx_map, List.foldl_map]
  rfl

theorem wcr_only_none (del : List Nat) :
    ∀ L : List (MKlong × Nat), L.foldl (wcrOnlyStep del) none = none
  | [] => rfl
  | _ :: L => wcr_only_none del L

theorem wcr_only_fold (ks : List MKlong) (del : List Nat) :
    ∀ (L : List (MKlong × Nat)) (acc : Option (Option (Nat × Nat))) (m : List (Nat × NodeId)),
      (∀ ki ∈ L, ks[ki.2]? = some ki.1) → (acc = some none → m = []) →
      (∀ j c, acc = some (some (j, c)) → ∃ y, ks[j]? = some (.key c y) ∧ m = [(c, y)]) →
      ∀ j c, L.foldl (wcrOnlyStep del) acc = some (some (j, c)) →
        ∃ y, ks[j]? = some (.key c y) ∧
          L.foldl (fun m ki => wcrLiveStep del m (kOf ki.1, ki.2)) m = [(c, y)]
  | [], acc, m, _, _, h2, j, c, h => h2 j c h
  | (k, idx) :: L, acc, m, hL, h1, h2, j, c, h => by
    have hk : ks[idx]? = some k := hL (k, idx) List.mem_cons_self
    have hL' : ∀ ki ∈ L, ks[ki.2]? = some ki.1 := fun ki hki => hL ki (List.mem_cons_of_mem _ hki)
    rw [List.foldl_cons] at h ⊢
    cases acc with
    | none =>
      rw [show wcrOnlyStep del none (k, idx) = none from rfl, wcr_only_none] at h
      cases h
    | some cur =>
      cases k with
      | time t => exact wcr_only_fold ks del L _ _ hL' h1 h2 j c h
      | del b => exact wcr_only_fold ks del L _ _ hL' h1 h2 j c h
      | key c0 y0 =>
        by_cases hd : idx ∈ del
        · have e1 : wcrOnlyStep del (some cur) (.key c0 y0, idx) = some cur := by
            simp [wcrOnlyStep, hd]
          have e2 : wcrLiveStep del m (kOf (.key c0 y0), idx) = m := by
            simp [wcrLiveStep, kOf, hd]
          rw [e1] at h
          rw [e2]
          exact wcr_only_fold ks del L _ _ hL' h1 h2 j c h
        · have e2 : wcrLiveStep del m (kOf (.key c0 y0), idx) = insertCv c0 y0 m := by
            simp [wcrLiveStep, kOf, hd]
          rw [e2]
          cases cur with
          | none =>
            have e1 : wcrOnlyStep del (some none) (.key c0 y0, idx) = some (some (idx, c0)) := by
              simp [wcrOnlyStep, hd]
            rw [e1] at h
            have hm : m = [] := h1 rfl
            subst hm
            refine wcr_only_fold ks del L _ _ hL' (fun h' => by cases h') ?_ j c h
            intro j' c' h'
            simp only [Option.some.injEq, Prod.mk.injEq] at h'
            obtain ⟨rfl, rfl⟩ := h'
            exact ⟨y0, hk, rfl⟩
          | some jc =>
            obtain ⟨j0, cv⟩ := jc
            by_cases hc : c0 = cv
            · subst hc
              have e1 : wcrOnlyStep del (some (some (j0, c0))) (.key c0 y0, idx) =
                  some (some (idx, c0)) := by
                simp [wcrOnlyStep, hd]
              rw [e1] at h
              obtain ⟨y1, -, hm⟩ := h2 j0 c0 rfl
              subst hm
              have e3 : insertCv c0 y0 [(c0, y1)] = [(c0, y0)] := by simp [insertCv]
              rw [e3]
              refine wcr_only_fold ks del L _ _ hL' (fun h' => by cases h') ?_ j c h
              intro j' c' h'
              simp only [Option.some.injEq, Prod.mk.injEq] at h'
              obtain ⟨rfl, rfl⟩ := h'
              exact ⟨y0, hk, rfl⟩
            · have e1 : wcrOnlyStep del (some (some (j0, cv))) (.key c0 y0, idx) = none := by
                simp [wcrOnlyStep, hd, hc]
              rw [e1, wcr_only_none] at h
              cases h

/-- `KNode.onlyLiveKlong`: the node's one live klong, of its last key klong of the
compare value, is klong `only`. -/
theorem wcr_onlyLive {n : MNode} {only : Nat} (h : n.onlyLiveKlong = some only) :
    ∃ c y, n.ks[only]? = some (.key c y) ∧ live (ksOf n) = [(c, y)] := by
  rw [wcr_onlyLive_eq] at h
  split at h
  · next j c0 hf =>
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨y, h1, h2⟩ := wcr_only_fold n.ks n.lastBitmap n.ks.zipIdx (some none) [] (by
      rintro ⟨k, i⟩ hki
      obtain ⟨hlt, heq⟩ := List.mem_zipIdx' hki
      simp only at hlt heq ⊢
      rw [List.getElem?_eq_getElem hlt, heq]) (fun _ => rfl) (fun _ _ h => by cases h) j c0 hf
    refine ⟨c0, y, h1, ?_⟩
    rw [wcr_live_eq]
    exact h2
  · cases h


/-! ## 2. A node of before: its klongs of before -/

theorem wcr_tfold_false : ∀ (l : List Klong) (o : Option Time), (l.foldl tStep (false, o)).1 = false
  | [], _ => rfl
  | k :: l, o => by
    rw [List.foldl_cons]
    cases k with
    | time t => exact wcr_tfold_false l _
    | key c y => exact wcr_tfold_false l _
    | del b => exact wcr_tfold_false l _

theorem wcr_tfold_last : ∀ (l : List Klong) (b : Bool) (t0 : Time),
    (∀ t, Klong.time t ∈ l → t ≤ t0) → (l.foldl tStep (b, some t0)).1 = true →
      (l.foldl tStep (b, some t0)).2 = some t0
  | [], _, _, _, _ => rfl
  | k :: l, b, t0, hle, h => by
    rw [List.foldl_cons] at h ⊢
    have hle' : ∀ t, Klong.time t ∈ l → t ≤ t0 := fun t ht => hle t (List.mem_cons_of_mem _ ht)
    cases k with
    | key c y => exact wcr_tfold_last l b t0 hle' h
    | del bs => exact wcr_tfold_last l b t0 hle' h
    | time t =>
      have ht := hle t List.mem_cons_self
      exfalso
      have e : tStep (b, some t0) (.time t) = (false, some t) := by
        simp only [tStep, Bool.and_eq_false_iff, decide_eq_false_iff_not, Prod.mk.injEq, and_true]
        exact Or.inr (Nat.not_lt.mpr ht)
      rw [e, wcr_tfold_false] at h
      cases h

/-- A node of before with a time klong of i: if its times increase and none is after i,
the last time klong is of i. -/
theorem wcr_lastT_ext {ks0 more : List Klong} {i : Time}
    (hw : timesOk (ks0 ++ Klong.time i :: more) = true)
    (hle : ∀ t, Klong.time t ∈ more → t ≤ i) : lastT (ks0 ++ Klong.time i :: more) = some i := by
  rw [timesOk_eq, Bool.and_eq_true] at hw
  unfold lastT
  have h2 := hw.2
  rw [List.foldl_append, List.foldl_cons] at h2
  have e := tfold_snd (ks0 ++ Klong.time i :: more) (true, none)
  simp only at e
  rw [← e, List.foldl_append, List.foldl_cons]
  exact wcr_tfold_last more _ i hle h2

/-- A node of the overlay of before the transaction with no time klong of i last has the
klongs of before. -/
theorem wcr_ks_old {n : MNode} {i : Time} {ks0 : List Klong} (hwf : timesOk (ksOf n) = true)
    (ht : TimesLe n i) (h : ksOf n = ks0 ∨ ∃ more, ksOf n = ks0 ++ Klong.time i :: more)
    (hl : n.lastTime ≠ some i) : ksOf n = ks0 := by
  rcases h with h | ⟨more, h⟩
  · exact h
  · exfalso
    apply hl
    rw [← lastT_ksOf, h]
    rw [h] at hwf
    refine wcr_lastT_ext hwf (fun t htm => ht t ?_)
    rw [h]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ htm)

/-! ## 3. The map after a collapse -/

/-- The nodes reached from the space root x, an inner node with the one live klong (c, y):
x and those reached from y. -/
theorem wcr_reach_dec {A : Tree} {x y : NodeId} {nr : KNode} {lo : Nat} {hi : Option Nat}
    (hG : Good A x lo hi) (hAx : A.obj x = some (.key nr)) {c : Nat}
    (hlive : live nr.ks = [(c, y)]) :
    ∀ z ∈ reachAt A (A.fuel x) x, z = x ∨ z ∈ reachAt A (A.fuel y) y := by
  intro z hz
  have hm : (c, y) ∈ live nr.ks := by rw [hlive]; simp
  rw [show A.fuel x = nr.level + 1 by simp [Tree.fuel, hAx], tc_key hAx, hlive] at hz
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons] at hz
  rcases hz with h | h
  · exact Or.inl h
  · exact Or.inr (hG.tc_kid_eq hAx hm ▸ h)

/-- The map of w' after the collapse of the space root x of w, an inner node with the one
live klong (0, y), whose other nodes are as in w: y is the space root of a sound tree with the
same keys, and the link books hold, if every klong of a node reached from y names a node of
the map and x, if still a key node, names only nodes of s. -/
theorem wcr_post {M : Nat} {i : Time} {s : Tree} {C : List (Key × Nat)} {w w' : MW}
    {x y : NodeId} {nr : KNode}
    (hS : Sound M none (treeOf i s w) x C) (hx : w.top.rootKey = x) (hy : w'.top.rootKey = y)
    (hAx : (treeOf i s w).obj x = some (.key nr)) (hrl : nr.leaf = false)
    (hlive : live nr.ks = [(0, y)])
    (hB : ∀ z, z ≠ x → (treeOf i s w').obj z = (treeOf i s w).obj z)
    (hBo : ∀ z ∈ reachAt (treeOf i s w) ((treeOf i s w).fuel y) y, ∀ m,
      (treeOf i s w).obj z = some (.key m) → ∀ c o, Klong.key c o ∈ m.ks →
        ((treeOf i s w').obj o).isSome = true)
    (hBx : ∀ nx, (treeOf i s w').obj x = some (.key nx) → ∀ c o, Klong.key c o ∈ nx.ks →
      (s.obj o).isSome = true)
    (hK : WcrLink i s w) :
    Sound M none (treeOf i s w') y C ∧ WcrLink i s w' ∧
      ∀ z ∈ reachOf i s w', z ≠ x ∧ z ∈ reachOf i s w := by
  obtain ⟨hSy, hxy, hsub⟩ := hS.collapse hAx hrl hlive
  have hBy : ∀ z ∈ reachAt (treeOf i s w) ((treeOf i s w).fuel y) y,
      (treeOf i s w').obj z = (treeOf i s w).obj z :=
    fun z hz => hB z (fun e => hxy (e ▸ hz))
  have hfy : (treeOf i s w').fuel y = (treeOf i s w).fuel y := by
    simp [Tree.fuel, hBy y (tc_self _ _ _)]
  have hR : reachAt (treeOf i s w') ((treeOf i s w').fuel y) y =
      reachAt (treeOf i s w) ((treeOf i s w).fuel y) y := by
    rw [hfy]; exact reachAt_agree _ _ hBy
  have hRw' : reachOf i s w' = reachAt (treeOf i s w) ((treeOf i s w).fuel y) y := by
    unfold reachOf; rw [hy]; exact hR
  have hRw : reachOf i s w = reachAt (treeOf i s w) ((treeOf i s w).fuel x) x := by
    unfold reachOf; rw [hx]
  have hxy' : Klong.key 0 y ∈ nr.ks := ss_live_mem (by rw [hlive]; simp)
  have hyx : y ≠ x := fun e => hxy (e ▸ tc_self _ _ _)
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨n, ho, hne⟩ := hSy.key
    refine ⟨⟨n, (hBy y (tc_self _ _ _)).trans ho, hne⟩, hSy.good.agree hBy, ?_, ?_, ?_⟩
    · intro z hz m hm
      rw [hR] at hz
      rw [hBy z hz] at hm
      have hok := hSy.nodes z hz m hm
      simp only [reduceCtorEq, ite_false, nodeOk, Bool.and_eq_true, decide_eq_true_eq,
        List.all_eq_true] at hok ⊢
      refine ⟨hok.1, fun k hk => ?_⟩
      cases k with
      | key c o => exact hBo z hz m hm c o hk
      | time t => rfl
      | del b => rfl
    · rw [← hSy.holds]; exact L_agree hBy
    · rw [hR]; exact hSy.tree
  · intro m hm mn hBm hsm u nu c hBu hk hum
    rw [hRw'] at hm
    rw [hBy m hm] at hBm
    have hm' : m ∈ reachOf i s w := by rw [hRw]; exact hsub m hm
    have hnot : ∀ u nu c, (treeOf i s w').obj u = some (.key nu) → Klong.key c m ∈ nu.ks →
        u ≠ x := by
      intro u nu c hBu hk e
      rw [e] at hBu
      have := hBx nu hBu c m hk
      rw [hsm] at this
      cases this
    have hux := hnot u nu c hBu hk
    rw [hB u hux] at hBu
    obtain ⟨-, hone⟩ := hK m hm' mn hBm hsm u nu c hBu hk hum
    refine ⟨?_, ?_⟩
    · rw [hy]
      intro e
      rw [e] at hone
      exact hux (hone x nr 0 hAx hxy' (Ne.symm hyx)).symm
    · intro u' nu' c' hBu' hk' hu'm
      have hu'x := hnot u' nu' c' hBu' hk'
      rw [hB u' hu'x] at hBu'
      exact hone u' nu' c' hBu' hk' hu'm
  · intro z hz
    rw [hRw'] at hz
    exact ⟨fun e => hxy (e ▸ hz), by rw [hRw]; exact hsub z hz⟩

/-- Every key klong of a node reached in a sound tree names a node. -/
theorem wcr_named {M : Nat} {ex : Option NodeId} {T : Tree} {r : NodeId} {C : List (Key × Nat)}
    (h : Sound M ex T r C) {z : NodeId} (hz : z ∈ reachAt T (T.fuel r) r) {m : KNode}
    (hm : T.obj z = some (.key m)) {c : Nat} {o : NodeId} (hk : Klong.key c o ∈ m.ks) :
    (T.obj o).isSome = true := by
  have hok := h.nodes z hz m hm
  simp only [nodeOk, Bool.and_eq_true, List.all_eq_true] at hok
  simpa using hok.2 _ hk

/-! ## 4. The take-back of a root that a split of the transaction made -/

theorem wcr_treeOf_take (i : Time) (s : Tree) (w : MW) (x z : NodeId) :
    (treeOf i s { w with taken := x :: w.taken }).obj z =
      if z = x then none else (treeOf i s w).obj z := by
  have hl : wLevel s { w with taken := x :: w.taken } = wLevel s w := rfl
  by_cases h : z = x
  · subst h; simp [treeOf]
  · simp [treeOf, h, hl]

/-- The put's books after node x, made by the transaction, is taken back. -/
theorem wcr_putBooks_take {p : MParams} {i : Time} {base : NodeId} {s : Tree} {w : MW}
    {x : NodeId} (hk : PutBooks p i base s w) (hx : x ∈ w.made.map (·.id)) :
    PutBooks p i base s { w with taken := x :: w.taken } := by
  have hc : ∀ y, (x :: w.taken).contains y = false → w.taken.contains y = false := by
    intro y hy
    simp only [List.contains_cons, Bool.or_eq_false_iff] at hy
    exact hy.2
  refine ⟨fun y n hy ht => hk.first y n hy (hc y ht), hk.times,
    fun y n hy ht => hk.levels y n hy (hc y ht), hk.ids, ?_, hk.overlay, hk.within,
    fun y n hy ht => hk.timeFirst y n hy (hc y ht)⟩
  intro y hy
  simp only [List.contains_cons, Bool.or_eq_true, beq_iff_eq] at hy
  rcases hy with rfl | hy
  · exact hx
  · exact hk.taken y hy

/-- `takeBackRoot x 0 only`: the space root x, made by a split of the transaction, an inner
node with the one live klong (0, y), klong `only`: y is the space root, and x is taken
back. -/
theorem wcr_take {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} (hb : Books i base s tp) {C : List (Key × Nat)} {w : MW} {x y : NodeId}
    {n : MNode} {only : Nat} (hI : PInv p i base s tp none C w) (hK : WcrLink i s w)
    (hx : w.top.rootKey = x) (hlk : w.nodes.lookup x = some n)
    (hleaf : n.leaf = false) (hmade : n.firstTime = some i)
    (hy : n.ks[only]? = some (.key 0 y)) (hlive : live (ksOf n) = [(0, y)]) :
    WP (SIS.Tree.takeBackRoot x 0 only) { p := p, i := i, view := v } w
      (fun _ w' => PInv p i base s tp none C w' ∧ WcrLink i s w') := by
  have hptr : n.ptr? only = some y := by simp [SIS.Tree.KNode.ptr?, hy]
  let wA : MW := { w with trail := "rc.takeback.space" :: w.trail }
  let wB : MW := MW.afterSuperRoot wA p i y
  have hTA : treeOf i s wA = treeOf i s w := treeOf_congr i s rfl rfl rfl rfl rfl rfl
  have hwT : WTopInv i s tp wA.top wA.newTop := hI.top
  unfold SIS.Tree.takeBackRoot
  refine wput_read ?_
  refine wput_ok (getNode_hit _ hlk) ?_
  simp only [hptr]
  refine wput_ok (note_eq _ _ _) ?_
  refine wput_ok (newSuperRoot_eq v y (w := wA) hwT) ?_
  unfold SIS.Tree.takenBack
  rw [wp_modify]
  -- the state before
  obtain ⟨n1, hr1, -⟩ := hI.sound.key
  have ht : w.taken.contains x = false := by rw [← hx]; exact wput_taken hr1
  have hAx := treeOf_obj_overlay i s hlk ht
  have hsx : s.obj x = none := by
    have h1 := hI.books.first x n hlk ht
    rw [hmade] at h1
    simpa using h1
  have hxm : x ∈ w.made.map (·.id) := by
    rcases hI.books.overlay x n hlk with h | h
    · rw [hsx] at h; cases h
    · exact h
  have hxR : x ∈ reachOf i s w := by unfold reachOf; rw [hx]; exact tc_self _ _ _
  have hfree : ∀ u nu c, (treeOf i s w).obj u = some (.key nu) → Klong.key c x ∈ nu.ks →
      u ≠ x → False :=
    fun u nu c hu hk hux => (hK x hxR _ hAx hsx u nu c hu hk hux).1 hx.symm
  have hS : Sound p.M none (treeOf i s w) x C := hx ▸ hI.sound
  obtain ⟨-, hxy, hsub⟩ := hS.collapse hAx hleaf hlive
  -- the map after
  obtain ⟨hobjB, hrootB, hdirtyB⟩ := treeOf_afterSuperRoot i s p y (w := wA) hI.books.ids.1
  have hrk : wB.top.rootKey = y := (afterSuperRoot_fields wA p i y).1
  have hC : ∀ z, (treeOf i s { wB with taken := x :: wB.taken }).obj z =
      if z = x then none else (treeOf i s w).obj z := by
    intro z
    rw [wcr_treeOf_take, hobjB, hTA]
  have hCne : ∀ z, z ≠ x → (treeOf i s { wB with taken := x :: wB.taken }).obj z =
      (treeOf i s w).obj z := fun z hz => by simp only [hC, hz, ↓reduceIte]
  have hCx : (treeOf i s { wB with taken := x :: wB.taken }).obj x = none := by
    simp only [hC, ↓reduceIte]
  obtain ⟨hS', hK', -⟩ := wcr_post (w' := { wB with taken := x :: wB.taken }) hS hx hrk hAx
    hleaf hlive hCne
    (by
      intro z hz m hm c o hk
      by_cases hox : o = x
      · subst hox
        exact (hfree z m c hm hk (fun e => hxy (e ▸ hz))).elim
      · rw [hCne o hox]
        exact wcr_named hS (hsub z hz) hm hk)
    (by intro nx hnx; rw [hCx] at hnx; cases hnx) hK
  refine ⟨⟨?_, by show Sound _ _ _ wB.top.rootKey _; rw [hrk]; exact hS', ?_, ?_, ?_, ?_⟩,
    hK'⟩
  · show (treeOf i s wB).root = some wB.top.rootKey
    rw [hrootB, hrk]
  · -- the frame
    obtain ⟨f1, f2, -⟩ := hI.frame
    have hD : dirtyOf { wB with taken := x :: wB.taken } = dirtyOf w := hdirtyB
    rw [hD]
    refine ⟨fun z o hz => ?_, fun z m hz hsz => ?_, ?_⟩
    · have hzx : z ≠ x := by intro e; rw [e, hsx] at hz; cases hz
      rw [hCne z hzx]
      exact f1 z o hz
    · have hzx : z ≠ x := by intro e; rw [e, hCx] at hz; cases hz
      rw [hCne z hzx] at hz
      exact f2 z m hz hsz
    · exact ⟨[(i, y)], treeOf_afterSuperRoot_roots i s p y wA, by simp⟩
  · exact topInv_afterSuperRoot y hwT hb hI.books.ids.2.2.2.1
  · -- BalancedOK
    intro u nu hu
    have hux : u ≠ x := by intro e; rw [e, hCx] at hu; cases hu
    rw [hCne u hux] at hu
    obtain ⟨h1, h2, h3⟩ := hI.balanced u nu hu
    refine ⟨h1, h2, fun hl c o hk => ?_⟩
    obtain ⟨m, hm, hlev⟩ := h3 hl c o hk
    have hox : o ≠ x := fun e => hfree u nu c hu (e ▸ hk) hux
    exact ⟨m, by rw [hCne o hox]; exact hm, hlev⟩
  · have hBk : PutBooks p i base s wB := putBooks_afterSuperRoot y
      (putBooks_congr hI.books rfl rfl rfl rfl rfl rfl rfl rfl rfl)
    refine wcr_putBooks_take hBk ?_
    cases hnt : wA.newTop
    · rw [(afterSuperRoot_new hnt p i y).1, List.map_append]
      exact List.mem_append_left _ hxm
    · rw [(afterSuperRoot_inPlace hnt p i y).1]
      exact hxm

/-! ## 5. The replacement of a root of before -/

/-- After the root x of before, an inner node with the one live klong (0, y), is cut back to
its klongs of before (the state wU), `newSuperRoot y`: y is the space root. -/
theorem wcr_replace_post {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    (hb : Books i base s tp) (hsn : SNamed s) {C : List (Key × Nat)} {w wU : MW}
    {x y : NodeId} {n : MNode} {n0 : KNode} (hI : PInv p i base s tp none C w)
    (hK : WcrLink i s w) (hx : w.top.rootKey = x)
    (hlk : w.nodes.lookup x = some n) (ht : w.taken.contains x = false)
    (hleaf : n.leaf = false) (hlive : live (ksOf n) = [(0, y)])
    (hs0 : s.obj x = some (.key n0))
    (hU1 : ∀ z, z ≠ x → (treeOf i s wU).obj z = (treeOf i s w).obj z)
    (hU2 : (treeOf i s wU).obj x = some (.key ⟨wLevel s w x, n.leaf, n0.ks⟩))
    (hUd : dirtyOf wU = dirtyOf w) (hUt : wU.top = w.top) (hUn : wU.newTop = w.newTop)
    (hUk : PutBooks p i base s wU) :
    PInv p i base s tp none C (MW.afterSuperRoot wU p i y) ∧
      WcrLink i s (MW.afterSuperRoot wU p i y) := by
  have hAx := treeOf_obj_overlay i s hlk ht
  obtain ⟨hlev0, hleaf0, hext⟩ := frame_overlay_ext hI.frame hlk ht hs0
  obtain ⟨hobjB, hrootB, hdirtyB⟩ := treeOf_afterSuperRoot i s p y (w := wU) hUk.ids.1
  have hrk : (MW.afterSuperRoot wU p i y).top.rootKey = y := (afterSuperRoot_fields wU p i y).1
  have hBne : ∀ z, z ≠ x → (treeOf i s (MW.afterSuperRoot wU p i y)).obj z =
      (treeOf i s w).obj z := fun z hz => by rw [hobjB]; exact hU1 z hz
  have hBx : (treeOf i s (MW.afterSuperRoot wU p i y)).obj x =
      some (.key ⟨wLevel s w x, n.leaf, n0.ks⟩) := by rw [hobjB]; exact hU2
  have hS : Sound p.M none (treeOf i s w) x C := hx ▸ hI.sound
  obtain ⟨-, hxy, hsub⟩ := hS.collapse hAx hleaf hlive
  have hsub0 : ∀ c o, Klong.key c o ∈ n0.ks → Klong.key c o ∈ ksOf n := by
    intro c o hk
    rcases hext with h | ⟨more, h⟩
    · rw [h]; exact hk
    · rw [h]; exact List.mem_append_left _ hk
  obtain ⟨hS', hK', -⟩ := wcr_post (w' := MW.afterSuperRoot wU p i y) hS hx hrk hAx
    hleaf hlive hBne
    (by
      intro z hz m hm c o hk
      by_cases hox : o = x
      · rw [hox, hBx]; rfl
      · rw [hBne o hox]
        exact wcr_named hS (hsub z hz) hm hk)
    (by
      intro nx hnx c o hk
      rw [hBx] at hnx
      simp only [Option.some.injEq, Obj.key.injEq] at hnx
      rw [← hnx] at hk
      exact hsn x n0 hs0 c o hk) hK
  refine ⟨⟨by rw [hrootB, hrk], by rw [hrk]; exact hS', ?_,
    topInv_afterSuperRoot y (topInv_congr hI.top hUt hUn) hb hUk.ids.2.2.2.1, ?_,
    putBooks_afterSuperRoot y hUk⟩, hK'⟩
  · -- the frame
    obtain ⟨f1, f2, -⟩ := hI.frame
    rw [hdirtyB, hUd]
    refine ⟨fun z o hz => ?_, fun z m hz hsz => ?_, ?_⟩
    · by_cases hzx : z = x
      · subst hzx
        rw [hs0] at hz
        cases hz
        refine ⟨_, hBx, ⟨hlev0, hleaf0, Or.inl rfl⟩, fun hd => ?_⟩
        exact absurd (mem_dirtyOf_of_lookup hlk) hd
      · rw [hBne z hzx]
        exact f1 z o hz
    · have hzx : z ≠ x := by intro e; rw [e, hs0] at hsz; cases hsz
      rw [hBne z hzx] at hz
      exact f2 z m hz hsz
    · exact ⟨[(i, y)], treeOf_afterSuperRoot_roots i s p y wU, by simp⟩
  · -- BalancedOK
    obtain ⟨hx1, hx2, hx3⟩ := hI.balanced x _ hAx
    intro u nu hu
    by_cases hux : u = x
    · subst hux
      rw [hBx] at hu
      simp only [Option.some.injEq, Obj.key.injEq] at hu
      subst hu
      refine ⟨hx1, hx2, fun hl c o hk => ?_⟩
      obtain ⟨m, hm, hlev⟩ := hx3 hl c o (hsub0 c o hk)
      have hox : o ≠ u := by
        intro e
        rw [e, hAx] at hm
        simp only [Option.some.injEq, Obj.key.injEq] at hm
        rw [← hm] at hlev
        simp at hlev
      exact ⟨m, by rw [hBne o hox]; exact hm, hlev⟩
    · rw [hBne u hux] at hu
      obtain ⟨h1, h2, h3⟩ := hI.balanced u nu hu
      refine ⟨h1, h2, fun hl c o hk => ?_⟩
      obtain ⟨m, hm, hlev⟩ := h3 hl c o hk
      by_cases hox : o = x
      · subst hox
        rw [hAx] at hm
        simp only [Option.some.injEq, Obj.key.injEq] at hm
        rw [← hm] at hlev
        exact ⟨_, hBx, hlev⟩
      · exact ⟨m, by rw [hBne o hox]; exact hm, hlev⟩

theorem wcr_head_takeWhile {α : Type} (q : α → Bool) :
    ∀ l : List α, l.takeWhile q ≠ [] → (l.takeWhile q).head? = l.head?
  | [], h => absurd rfl h
  | a :: l, h => by
    rw [List.takeWhile_cons] at h ⊢
    by_cases hq : q a = true
    · simp [hq]
    · simp [hq] at h

/-- `replaceRoot x 0 only`: the space root x, of before the transaction, an inner node with
the one live klong (0, y), klong `only`: x is cut back to its klongs of before, and y is the
space root. -/
theorem wcr_replace {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} (hb : Books i base s tp) (hsn : SNamed s) {C : List (Key × Nat)} {w : MW}
    {x y : NodeId} {n : MNode} {only : Nat} (hI : PInv p i base s tp none C w)
    (hK : WcrLink i s w) (hx : w.top.rootKey = x)
    (hlk : w.nodes.lookup x = some n) (hleaf : n.leaf = false) (hmade : n.firstTime ≠ some i)
    (hy : n.ks[only]? = some (.key 0 y)) (hlive : live (ksOf n) = [(0, y)]) :
    WP (SIS.Tree.replaceRoot x 0 only) { p := p, i := i, view := v } w
      (fun _ w' => PInv p i base s tp none C w' ∧ WcrLink i s w') := by
  have hptr : n.ptr? only = some y := by simp [SIS.Tree.KNode.ptr?, hy]
  obtain ⟨n1, hr1, -⟩ := hI.sound.key
  have ht : w.taken.contains x = false := by rw [← hx]; exact wput_taken hr1
  have hAx := treeOf_obj_overlay i s hlk ht
  have hsome : (s.obj x).isSome = true := (hI.books.first x n hlk ht).mpr hmade
  obtain ⟨n0, hs0⟩ : ∃ n0, s.obj x = some (.key n0) := by
    obtain ⟨o0, ho0⟩ := Option.isSome_iff_exists.mp hsome
    obtain ⟨o', ho', he, -⟩ := hI.frame.1 x o0 ho0
    rw [hAx] at ho'
    cases ho'
    cases o0 with
    | key n0 => exact ⟨n0, ho0⟩
    | val h => exact absurd he (by simp [Ext])
  obtain ⟨-, -, hext⟩ := frame_overlay_ext hI.frame hlk ht hs0
  let wA : MW := { w with trail := "rc.replace.space" :: w.trail }
  have hTA : treeOf i s wA = treeOf i s w := treeOf_congr i s rfl rfl rfl rfl rfl rfl
  have hkA : PutBooks p i base s wA := putBooks_congr hI.books rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hlkA : wA.nodes.lookup x = some n := hlk
  unfold SIS.Tree.replaceRoot
  refine wput_read ?_
  refine wput_ok (getNode_hit _ hlk) ?_
  simp only [hptr]
  refine wput_ok (note_eq _ _ _) ?_
  rw [wp_bind]
  unfold SIS.Tree.unlink
  refine wput_read ?_
  refine wput_ok (getNode_hit _ hlkA) ?_
  split
  · next hlt =>
    refine ss_wp_putNode ?_
    have hT : WTopInv i s tp (wA.withNode x (n.toPrev (i - 1))).top
        (wA.withNode x (n.toPrev (i - 1))).newTop := hI.top
    rw [wp_newSuperRoot v y hT]
    have hks : ksOf (n.toPrev (i - 1)) = n0.ks :=
      toPrev_ext (prim_timesBefore (hb.times x n0 hs0)) (hb.first x n0 hs0) hext
    have hWn := treeOf_withNode i s (w := wA) (x := x) (n.toPrev (i - 1)) ht
    refine wcr_replace_post hb hsn hI hK hx hlk ht hleaf hlive hs0 ?_ ?_
      (dirtyOf_withNode hlkA) rfl rfl ?_
    · intro z hz
      rw [hWn, ← hTA]
      simp [Tree.set, hz]
    · rw [hWn]
      simp only [Tree.set, ↓reduceIte, hks]
      rfl
    · refine putBooks_withNode hkA hlkA ht rfl ?_ ?_
      · have hne : (n.toPrev (i - 1)).ks ≠ [] := by
          intro e
          have h2 := hks
          rw [ksOf, e] at h2
          obtain ⟨t0, rest, h3⟩ := hb.first x n0 hs0
          rw [h3] at h2
          cases h2
        exact wcr_head_takeWhile _ n.ks hne
      · intro t htm
        exact hI.books.times x n hlk t (ss_mem_toPrev htm)
  · next hlt =>
    rw [wp_pure]
    refine (wp_newSuperRoot v y (w := wA) hI.top _).mpr ?_
    have hwf : timesOk (ksOf n) = true := by
      have hok := hI.sound.nodes x (by rw [hx]; exact tc_self _ _ _) _ hAx
      simp only [reduceCtorEq, ite_false, nodeOk, klongsWf, Bool.and_eq_true] at hok
      exact hok.1.2.1
    have hks : ksOf n = n0.ks := wcr_ks_old hwf (ss_timesLe (hI.books.times x n hlk)) hext
      (by simpa using hlt)
    refine wcr_replace_post hb hsn hI hK hx hlk ht hleaf hlive hs0
      (fun z _ => by rw [hTA]) ?_ rfl rfl rfl hkA
    rw [hTA, hAx, hks]

/-! ## 6. The loop -/

/-- The link books speak only of the map and the space root. -/
theorem wcr_books_congr {i : Time} {s : Tree} {w w' : MW} (hT : treeOf i s w' = treeOf i s w)
    (hr : w'.top.rootKey = w.top.rootKey) (hK : WcrLink i s w) : WcrLink i s w' := by
  have hR : reachOf i s w' = reachOf i s w := by unfold reachOf; rw [hT, hr]
  unfold WcrLink
  rw [hR, hT, hr]
  exact hK

/-- A join point of the do notation: the body with the join point's value. -/
theorem wcr_wp_have {α β : Type} {v : α} {b : α → SIS.Tree.M β} {c : Ctx} {w : MW}
    {post : β → MW → Prop} (h : WP (b v) c w post) : WP (have x := v; b x) c w post := h

theorem wcr_descend_eq (c : Ctx) (w : MW) (cv : Nat) :
    SIS.Tree.descendToSegmentRoot [cv] 0 c w =
      .ok (w.top.rootKey, { w with path := [(none, w.top.rootKey)] }) := rfl

theorem wcr_loop {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} (hs : Shows p v z s tp) (hb : Books i base s tp)
    (hsn : SNamed s) (cv : Nat) :
    ∀ (f : Nat) (w : MW) (C : List (Key × Nat)), PInv p i base s tp none C w →
      WcrLink i s w →
      WP (SIS.Tree.collapseRoot [cv] 0 f) { p := p, i := i, view := v } w
        (fun _ w' => PInv p i base s tp none C w' ∧ WcrLink i s w')
  | 0, w, C, _, _ => by
    unfold SIS.Tree.collapseRoot
    exact wp_throw _ _ _ _
  | f + 1, w, C, hI, hK => by
    unfold SIS.Tree.collapseRoot
    refine wput_read ?_
    refine wput_ok (wcr_descend_eq _ w cv) ?_
    have hI1 : PInv p i base s tp none C { w with path := [(none, w.top.rootKey)] } :=
      hI.congr rfl rfl rfl rfl rfl rfl rfl rfl rfl
    obtain ⟨n1, hr1, -⟩ := hI1.sound.key
    obtain ⟨n, w2, hget, -, -, hlk2, hT2, hI2, hw2, -⟩ := getNode_spec hs hb hI1 hr1
    refine wput_ok hget ?_
    have hfields : w2.top = w.top ∧ w2.path = [(none, w.top.rootKey)] := by
      rcases hw2 with rfl | ⟨-, gh, rfl⟩
      · exact ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩
    have hx2 : w2.top.rootKey = w.top.rootKey := by rw [hfields.1]
    have hK2 := wcr_books_congr hT2 hx2 hK
    split
    · rw [wp_pure]
      exact ⟨hI2, hK2⟩
    · next hleaf =>
      have hleaf' : n.leaf = false := by simpa using hleaf
      refine wput_ok (replacedBy_eq _ _ _) ?_
      split
      · rw [wp_pure]
        exact ⟨hI2, hK2⟩
      · split
        · rw [wp_pure]
          exact ⟨hI2, hK2⟩
        · next only honly =>
          obtain ⟨c, y, hy, hlive⟩ := wcr_onlyLive honly
          refine wcr_wp_have ?_
          split
          · rw [wp_bind]
            exact wp_throw _ _ _ _
          · next hcv =>
            have hc : c = 0 := by
              have h1 : n.cv? only = some 0 := by simpa using hcv
              simp [SIS.Tree.KNode.cv?, hy] at h1
              exact h1
            subst hc
            refine wput_ok (pathSize_eq _ _) ?_
            rw [hfields.2]
            refine wcr_wp_have ?_
            refine wcr_wp_have ?_
            split
            · next hmade =>
              rw [wp_bind]
              refine (wcr_take hb hI2 hK2 hx2 hlk2 hleaf' (by simpa using hmade) hy
                hlive).mono ?_
              rintro - w3 ⟨hI3, hK3⟩
              exact wcr_loop hs hb hsn cv f w3 C hI3 hK3
            · next hmade =>
              rw [wp_bind]
              refine (wcr_replace hb hsn hI2 hK2 hx2 hlk2 hleaf' (by simpa using hmade) hy
                hlive).mono ?_
              rintro - w3 ⟨hI3, hK3⟩
              exact wcr_loop hs hb hsn cv f w3 C hI3 hK3

/-! ## 7. The statement -/

/-- Root collapse at the space root keeps `PInv` and the link book `WcrLink`, from a tree
before whose klongs name its nodes (`SNamed`). -/
theorem collapseRoot_spec {p : MParams} {i : Time} {base : NodeId} {s : Tree} {tp : Top}
    {v : View BVal} {z : NodeId} (hs : Shows p v z s tp)
    (hb : Books i base s tp) (hsn : SNamed s) (cv : Nat) :
    ∀ (f : Nat) (w : MW) (C : List (Key × Nat)), PInv p i base s tp none C w →
      WcrLink i s w →
      WP (SIS.Tree.collapseRoot [cv] 0 f) { p := p, i := i, view := v } w
        (fun _ w' => w'.outside = [] → PInv p i base s tp none C w' ∧ WcrLink i s w') := by
  intro f w C hI hK
  exact (wcr_loop hs hb hsn cv f w C hI hK).mono (fun _ _ h _ => h)

end Contract
