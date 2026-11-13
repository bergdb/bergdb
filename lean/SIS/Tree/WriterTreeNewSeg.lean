/-
The writer's tree kept by the put of a key whose last segment is new (bergdb
024-22, `OpTreeOK`; prover latest's `writerWP_put_newSeg`): the leaf of the
segment before gets a klong to a new segment leaf, which gets the klong of the
value (`treeOK_newSeg`, `writerWP_put_newSeg_tree`, and under `PutInv`
`writerWP_put_newSeg_inv_tree`).
-/
import SIS.Tree.WriterTreeSegLeaf

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A reached node L gets a klong (c0, y) to a fresh node y whose live klongs
are at most (cl, v), v fresh: the tree is kept. -/
theorem treeOK_newSeg (N N' : NodeId → Option KNode) (t : Time) (r L y v : NodeId)
    (n ym : KNode) (c0 cl : Nat) (hT : TreeOK N t r) (hLR : TReach N t r L)
    (hLn : N L = some n) (hnwf : klongsWf n.ks = true) (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ t)
    (hN'L : N' L = some (n.add t (.key c0 y))) (hN'y : N' y = some ym)
    (hym : ∀ c z, (c, z) ∈ ym.liveAt t → c = cl ∧ z = v)
    (hother : ∀ z, z ≠ L → z ≠ y → N' z = N z)
    (hy : N y = none) (hv : N v = none) (hyv : y ≠ v)
    (hfresh : ∀ z, (z = y ∨ z = v) → ∀ u c', TReach N t r u → ¬ TLink N t u c' z) :
    TreeOK N' t r := by
  have hLy : L ≠ y := fun he => by rw [he, hy] at hLn; cases hLn
  have hLv : L ≠ v := fun he => by rw [he, hv] at hLn; cases hLn
  have hvN' : N' v = none := by rw [hother v (Ne.symm hLv) (Ne.symm hyv)]; exact hv
  have hnotR : ∀ z, (z = y ∨ z = v) → ¬ TReach N t r z := by
    intro z hz
    rcases hz with h | h <;> rw [h]
    · exact not_reach_fresh N t r y hT hy (hfresh y (Or.inl rfl))
    · exact not_reach_fresh N t r v hT hv (hfresh v (Or.inr rfl))
  have hLl : ∀ c' z, TLink N' t L c' z → (c' = c0 ∧ z = y) ∨ (c' ≠ c0 ∧ (c', z) ∈ n.liveAt t) := by
    intro c' z hl
    obtain ⟨m, hm, hc⟩ := hl
    rw [hN'L] at hm
    simp only [Option.some.injEq] at hm
    subst hm
    exact KNode.add_key_liveAt_mem n t c0 y hnwf hnt c' z hc
  have hyl : ∀ c' z, TLink N' t y c' z → c' = cl ∧ z = v := by
    intro c' z hl
    obtain ⟨m, hm, hc⟩ := hl
    rw [hN'y] at hm
    simp only [Option.some.injEq] at hm
    subst hm
    exact hym c' z hc
  have hvl : ∀ c' z, ¬ TLink N' t v c' z := by
    intro c' z hl
    obtain ⟨m, hm, _⟩ := hl
    rw [hvN'] at hm; cases hm
  have hOld : ∀ u, u ≠ L → u ≠ y → ∀ c' z, TLink N' t u c' z → TLink N t u c' z := by
    intro u huL huy c' z hl
    obtain ⟨m, hm, hc⟩ := hl
    rw [hother u huL huy] at hm
    exact ⟨m, hm, hc⟩
  apply treeOK_transfer_gone N N' t r r (fun z => z = y ∨ z = v) (fun _ => False) (fun u c' => (u, c'))
    hT hnotR
  · exact Or.inl ⟨rfl, id⟩
  · intro u c' z hu _ hl
    by_cases huL : u = L
    · rw [huL] at hl
      rcases hLl c' z hl with ⟨_, h⟩ | ⟨_, hmem⟩
      · exact Or.inl (Or.inl h)
      · exact Or.inr ⟨id, L, c', hLR, ⟨n, hLn, hmem⟩, by rw [huL]⟩
    · by_cases huy : u = y
      · rw [huy] at hl
        exact Or.inl (Or.inr (hyl c' z hl).2)
      · by_cases huv : u = v
        · rw [huv] at hl; exact absurd hl (hvl c' z)
        · have huR : TReach N t r u := by
            rcases hu with h | h
            · exact h
            · rcases h with h | h
              · exact absurd h huy
              · exact absurd h huv
          exact Or.inr ⟨id, u, c', huR, hOld u huL huy c' z hl, rfl⟩
  · intro u c' u' c'' z hu _ hu' _ hz hl1 hl2
    have hone : ∀ x d, (TReach N t r x ∨ (x = y ∨ x = v)) → TLink N' t x d z →
        (x = L ∧ d = c0 ∧ z = y) ∨ (x = y ∧ d = cl ∧ z = v) := by
      intro x d hx hl
      have hfr := hfresh z hz
      by_cases hxL : x = L
      · rw [hxL] at hl
        rcases hLl d z hl with ⟨hd, h⟩ | ⟨_, hmem⟩
        · exact Or.inl ⟨hxL, hd, h⟩
        · exact absurd ⟨n, hLn, hmem⟩ (hfr L d hLR)
      · by_cases hxy : x = y
        · rw [hxy] at hl
          obtain ⟨hd, h⟩ := hyl d z hl
          exact Or.inr ⟨hxy, hd, h⟩
        · by_cases hxv : x = v
          · rw [hxv] at hl; exact absurd hl (hvl d z)
          · have hxR : TReach N t r x := by
              rcases hx with h | h
              · exact h
              · rcases h with h | h
                · exact absurd h hxy
                · exact absurd h hxv
            exact absurd (hOld x hxL hxy d z hl) (hfr x d hxR)
    rcases hone u c' hu hl1 with ⟨a1, b1, c1⟩ | ⟨a1, b1, c1⟩ <;>
      rcases hone u' c'' hu' hl2 with ⟨a2, b2, c2⟩ | ⟨a2, b2, c2⟩
    · exact ⟨a1.trans a2.symm, b1.trans b2.symm⟩
    · exact absurd (c1.symm.trans c2) hyv
    · exact absurd (c2.symm.trans c1) hyv
    · exact ⟨a1.trans a2.symm, b1.trans b2.symm⟩
  · intro _ _ h; exact h
  · by_cases hrL : r = L
    · rw [hrL, hN'L]; exact ⟨_, rfl⟩
    · have hry : r ≠ y := by
        intro he; obtain ⟨_, hk⟩ := hT.rootKey; rw [he, hy] at hk; cases hk
      rw [hother r hrL hry]; exact hT.rootKey

/-- `writerWP_put_newSeg` keeps the writer's tree: a key whose prefix is there
and whose leaf for c0 has no klong of c0 and room gets a new segment leaf. -/
theorem writerWP_put_newSeg_tree (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (c0 cl h : Nat) (rk0 : NodeId) (w : W) (hM : 2 ≤ c.p.M)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk0)
    (ht : ∀ q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [c0, cl]) w.top.rootKey,
      w.taken.contains q.1 = false)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next))
    (hbaseF : ∀ z, w.next ≤ z → knodeOf c.p base z = none)
    (hcur : ∀ L n, (L, c0) ∈ eqVisits (wNode c.p base w) c.i c0 c.p.fuel rk0 →
      wNode c.p base w L = some n → n.leaf = true →
      klongsWf n.ks = true ∧ (∀ s, Klong.time s ∈ n.ks → s ≤ c.i) ∧ n.searchEq c.i c0 = none ∧
      n.size + 1 < c.p.M)
    (hwf : ∀ x xn, ReachS (wNode c.p base w) c.i w.top.rootKey x →
      wNode c.p base w x = some xn → klongsWf xn.ks = true)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hfreshT : ∀ z, w.next ≤ z → ∀ u c', TReach (wNode c.p base w) c.i w.top.rootKey u →
      ¬ TLink (wNode c.p base w) c.i u c' z) :
    WriterWP (putKv (.put (pre ++ [c0, cl]) h)) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey) := by
  obtain ⟨hidn, hidv, hidt⟩ := hids
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hvk : ∀ q ∈ eqVisits (wNode c.p base w) c.i c0 c.p.fuel rk0,
      q ∈ fromVisits (wNode c.p base w) c.i c.p.fuel (pre ++ [c0, cl]) w.top.rootKey :=
    fromVisits_append_gen _ _ _ c0 [cl] pre _ rk0 hrk
  have hfree : ∀ z, w.next ≤ z → wNode c.p base w z = none := by
    intro z hz
    have htz : w.taken.contains z = false := by
      cases h' : w.taken.contains z with
      | false => rfl
      | true => have := hidt z h'; omega
    have hnz : w.nodes.lookup z = none := by
      cases h' : w.nodes.lookup z with
      | none => rfl
      | some _ => have := hidn z (by rw [h']; rfl); omega
    simp only [wNode, htz, Bool.false_eq_true, ↓reduceIte, hnz, hbaseF z hz]
  unfold putKv pathClear findRoot pathAdd
  wpSimplify
  generalize hw2 : ({ ({ w with path := [] } : W) with
    path := ([] : List (Option Nat × NodeId)) ++ [(none, w.top.rootKey)] } : W) = w2
  have hr02 : ReadsAs c.p base w w2 := by subst hw2; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hw2n : w2.nodes = w.nodes := by subst hw2; rfl
  refine writerWP_putSegs_walk_src c base hvc (pre ++ [c0, cl]) (some h) [c0, cl] (by simp) _ pre
    w.top.rootKey rk0 w2 (by rw [hr02.1, hr02.2.2.1]; exact ht) (by rw [hr02.1]; exact hrk)
    (by subst hw2; simp) ?_
  intro w2' hr2' _ hsrc2'
  have hr0 := ReadsAs.trans _ _ _ _ _ hr02 hr2'
  rw [putSegs.eq_3 _ _ rk0 c0 [cl] (by simp)]
  unfold setNode
  wpSimplify
  have ht1 : ∀ q ∈ eqVisits (wNode c.p base w2') c.i c0 c.p.fuel rk0,
      w2'.taken.contains q.1 = false := by
    rw [hr0.1, hr0.2.2.1]
    exact fun q hq => ht q (hvk q hq)
  refine writerWP_mono (writerWP_and (writerWP_descendLte_reads c0 c base hvc c.p.fuel rk0 w2' ht1)
    (writerWP_descendLte_cache c0 c base hvc c.p.fuel rk0 w2' ht1)) ?_
  intro L w3 ⟨⟨hr23, n, hn, hnl, hlk3, hvisL, _⟩, ⟨_, hsrc3, _⟩⟩
  rw [hr0.1] at hn hvisL
  have hr03 := ReadsAs.trans _ _ _ _ _ hr0 hr23
  have hnext3 : w3.next = w.next := hr03.2.2.2.2
  obtain ⟨hnwf, hnt, hnone, hroom⟩ := hcur L n hvisL hn hnl
  rw [writerWP_getNode_known L n c _ hlk3]
  simp only [hnone, Option.isSome_some, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    writerWP_bind]
  have hsrcw3 : ∀ z, (w3.nodes.lookup z).isSome = true → z < w.next := by
    intro z hz
    rcases hsrc3 z hz with h1 | h1
    · rcases hsrc2' z h1 with h2 | h2
      · rw [hw2n] at h2; exact hidn z h2
      · exact hidv z h2
    · exact hidv z h1
  have hLlt : L < w.next := hsrcw3 L (by rw [hlk3]; rfl)
  have hntake : ∀ z, w.next ≤ z → w.taken.contains z = false := by
    intro z hz
    cases h' : w.taken.contains z with
    | false => rfl
    | true => have := hidt z h'; omega
  have hLt : w.taken.contains L = false := ht (L, c0) (hvk _ hvisL)
  have hrrk : ReachS (wNode c.p base w) c.i w.top.rootKey rk0 :=
    segRootR_reach _ _ _ _ hwf pre _ rk0 ReachS.root hrk
  have hLR : TReach (wNode c.p base w) c.i w.top.rootKey L :=
    reachS_tReach _ _ _ _ (eqVisits_reach _ _ _ c0 c.p.fuel rk0 L c0 hrrk hvisL)
  let e : KNode := ⟨true, []⟩
  have hrest : ∀ ws : W, ws.nodes = upsert (w3.nodes ++ [(w3.next, e)]) L (n.add c.i (.key c0 w3.next)) →
      ws.next = w3.next + 2 → ws.taken = w3.taken → ws.top = w3.top →
      WriterWP (setValue w3.next cl (pre ++ [c0, cl]) (some h)) c ws (fun _ w' =>
        TreeOK (wNode c.p base w') c.i w'.top.rootKey) := by
    intro ws h1 h2 h3 h5
    have hlkc : ws.nodes.lookup w3.next = some e := by
      rw [h1, lookup_upsert]
      simp only [show w3.next ≠ L by omega, ↓reduceIte]
      rw [List.lookup_append]
      have : w3.nodes.lookup w3.next = none := by
        cases h' : w3.nodes.lookup w3.next with
        | none => rfl
        | some _ => have := hsrcw3 _ (by rw [h']; rfl); omega
      rw [this]; simp [List.lookup]
    obtain ⟨f2, hf2⟩ : ∃ f2, c.p.fuel = f2 + 1 := ⟨c.p.fuel - 1, by omega⟩
    unfold setValue
    simp only [writerWP_bind, writerWP_read]
    rw [hf2]
    unfold descendLte
    simp only [writerWP_bind, writerWP_read]
    rw [writerWP_getNode_known _ e c ws hlkc]
    simp only [e, ↓reduceIte, writerWP_pure]
    unfold newValue fresh
    simp only [writerWP_bind, writerWP_get, writerWP_set, writerWP_modify, writerWP_pure]
    rw [writerWP_getNode_known _ e c _ (by simpa using hlkc)]
    have hcond : (decide ((e.size) + 1 < c.p.M) && !deadOver c.p (e.add c.i (.key cl ws.next))) = true := by
      simp only [e, KNode.size, List.length_nil, deadOver_empty_add]
      simp; omega
    have hfinal : ∀ wf : W, wf.nodes = upsert ws.nodes w3.next (e.add c.i (.key cl ws.next)) →
        wf.taken = ws.taken → wf.top = ws.top →
        TreeOK (wNode c.p base wf) c.i wf.top.rootKey := by
      intro wf g1 g3 g4
      rw [h2, hnext3] at g1
      rw [h1, hnext3] at g1
      rw [h3, hr03.2.2.1] at g3
      rw [h5, hr03.2.1] at g4
      have hLne : L ≠ w.next := by omega
      have hlookf : ∀ x, wf.nodes.lookup x =
          if x = w.next then some (e.add c.i (.key cl (w.next + 2)))
          else if x = L then some (n.add c.i (.key c0 w.next)) else w3.nodes.lookup x := by
        intro x
        rw [g1, lookup_upsert, lookup_upsert, List.lookup_append]
        by_cases hx1 : x = w.next
        · simp [hx1]
        · simp only [hx1, ↓reduceIte]
          by_cases hx2 : x = L
          · simp [hx2]
          · simp only [hx2, ↓reduceIte]
            cases h' : w3.nodes.lookup x with
            | some _ => rfl
            | none =>
              show (none : Option KNode).or ([(w.next, e)].lookup x) = none
              rw [lookup_cons_ne _ _ _ _ hx1]; rfl
      rw [g4]
      apply treeOK_newSeg (wNode c.p base w) (wNode c.p base wf) c.i w.top.rootKey L w.next
        (w.next + 2) n (e.add c.i (.key cl (w.next + 2))) c0 cl hT hLR hn hnwf hnt
      · simp only [wNode, g3, hLt, Bool.false_eq_true, ↓reduceIte, hlookf, hLne]
      · have : wf.taken.contains w.next = false := by rw [g3]; exact hntake _ (Nat.le_refl _)
        simp only [wNode, this, Bool.false_eq_true, ↓reduceIte, hlookf]
      · intro c' z hm
        have : e.add c.i (.key cl (w.next + 2)) = ⟨true, newKlongs c.i [(cl, w.next + 2)]⟩ := rfl
        rw [this] at hm
        have := liveAt_newKlongs_mem true c.i c.i _ c' z hm
        simpa using this
      · intro x hxL hxy
        rw [← hr03.1]
        simp only [wNode, g3, hr03.2.2.1, hlookf, hxy, hxL, ↓reduceIte]
      · exact hfree _ (Nat.le_refl _)
      · exact hfree _ (by omega)
      · omega
      · intro z hz u c' hu
        rcases hz with hz | hz <;> rw [hz] <;> exact hfreshT _ (by omega) u c' hu
    simp only [hcond, ↓reduceIte, putNode, writerWP_bind, writerWP_modify, writerWP_pure]
    exact hfinal _ rfl rfl rfl
  refine writerWP_ghOf_cached L n c w3 hlk3 _ (fun gh => ?_)
  simp only [note, newKey, fresh, putNode, hroom, ↓reduceIte, writerWP_bind, writerWP_modify,
    writerWP_get, writerWP_set, writerWP_read, writerWP_pure]
  split <;>
  · simp only [writerWP_bind, writerWP_modify, writerWP_pure]
    rw [putSegs.eq_2]
    exact hrest _ rfl rfl rfl rfl

/-- `writerWP_put_newSeg_tree` under `PutInv`. -/
theorem writerWP_put_newSeg_inv_tree (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (c0 cl h : Nat) (rk0 : NodeId) (w : W) (hI : PutInv c base w) (hM : 2 ≤ c.p.M)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk0)
    (hcur : ∀ L n, (L, c0) ∈ eqVisits (wNode c.p base w) c.i c0 c.p.fuel rk0 →
      wNode c.p base w L = some n → n.leaf = true →
      n.searchEq c.i c0 = none ∧ n.size + 1 < c.p.M) :
    WriterWP (putKv (.put (pre ++ [c0, cl]) h)) c w (fun _ w' =>
      TreeOK (wNode c.p base w') c.i w'.top.rootKey) := by
  obtain ⟨hwf, hbaseF, hfreshT, _, htk⟩ := PutInv.facts c base w hI
  obtain ⟨hidn, hidv, hidt, _, _⟩ := hI.ids
  exact writerWP_put_newSeg_tree c base hvc pre c0 cl h rk0 w hM hrk (htk _) ⟨hidn, hidv, hidt⟩
    hbaseF (fun L n hL hn hnl => ⟨hI.wf L n hn, hI.times L n hn, (hcur L n hL hn hnl).1,
      (hcur L n hL hn hnl).2⟩) hwf hI.tree hfreshT

end SIS.Tree
