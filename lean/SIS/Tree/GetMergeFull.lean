/-
The reading after the merge with a full parent (bergdb 024-22): a node's split
with a last version given as a virtual node and the cascade above it reads as
the tree with the node's content replaced by that version (latest's level
lemmas, `getFromR_timeLevel`, `getFromR_spaceLevel`, with
`writerWP_appendKlongs_chainGRQ`, composed as in `writerWP_del_accessPathR`).
-/
import SIS.Tree.WriterTreeMergeFull
import SIS.Tree.GetCascadeChainG
import SIS.Tree.GetFuel

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The live klongs of `mergeFullLast` as the merge's reading lemmas take them
(`getFromR_mergeOne`, `getFromR_mergeTwo`). -/
theorem mergeFullLast_iff (pn : KNode) (t : Time) (cL : Nat) (m1 : NodeId) (cR : Nat)
    (m2 : Option (NodeId × Nat)) (last : KNode) (h : mergeFullLast pn t cL m1 cR m2 = some last)
    (hpt : ∀ s, Klong.time s ∈ pn.ks → s ≤ t) :
    (m2 = none → ∀ cc z, (cc, z) ∈ last.liveAt t ↔
      (cc = cL ∧ z = m1) ∨ ((cc, z) ∈ pn.liveAt t ∧ cc ≠ cL ∧ cc ≠ cR)) ∧
    (∀ y g, m2 = some (y, g) → ∀ cc z, (cc, z) ∈ last.liveAt t ↔
      (cc = g ∧ z = y) ∨ (cc ≠ g ∧ cc = cL ∧ z = m1) ∨
        (cc ≠ g ∧ cc ≠ cL ∧ cc ≠ cR ∧ (cc, z) ∈ pn.liveAt t)) := by
  obtain ⟨pairs, hks⟩ := mergeFullLast_ks pn t cL m1 cR m2 last h
  have htl : ∀ s, Klong.time s ∈ last.ks → s ≤ t := by rw [hks]; exact newKlongs_times t pairs
  obtain ⟨_, hnone, hsome⟩ := mergeFullLast_lookup pn t cL m1 cR m2 last h
  have hl : ∀ cc z, (cc, z) ∈ last.liveAt t ↔ last.live.lookup cc = some z := by
    intro cc z
    rw [KNode.liveAt_of_times last t htl]
    exact ⟨lookup_of_mem_nodup _ (KNode.live_keys_nodup last) cc z, mem_of_lookup_nodup _ cc z⟩
  have hp : ∀ cc z, (cc, z) ∈ pn.liveAt t ↔ pn.live.lookup cc = some z := by
    intro cc z
    rw [KNode.liveAt_of_times pn t hpt]
    exact ⟨lookup_of_mem_nodup _ (KNode.live_keys_nodup pn) cc z, mem_of_lookup_nodup _ cc z⟩
  refine ⟨fun h0 cc z => ?_, fun y g hy cc z => ?_⟩
  · rw [hl, hnone h0 cc, hp]
    by_cases h1 : cc = cL
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
      constructor
      · intro he; exact Or.inl ⟨h1, (Option.some.inj he).symm⟩
      · rintro (⟨_, rfl⟩ | ⟨_, h2, _⟩)
        · rfl
        · exact absurd h1 h2
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
      by_cases h2 : cc = cR
      · rw [ite_eq_left_of_eq_true _ _ (eq_true h2)]
        constructor
        · intro he; cases he
        · rintro (⟨h, _⟩ | ⟨_, _, h⟩)
          · exact absurd h h1
          · exact absurd h2 h
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h2)]
        constructor
        · intro he; exact Or.inr ⟨he, h1, h2⟩
        · rintro (⟨h, _⟩ | ⟨he, _, _⟩)
          · exact absurd h h1
          · exact he
  · rw [hl, hsome y g hy cc, hp]
    by_cases h0 : cc = g
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h0)]
      constructor
      · intro he; exact Or.inl ⟨h0, (Option.some.inj he).symm⟩
      · rintro (⟨_, rfl⟩ | ⟨h, _⟩ | ⟨h, _⟩)
        · rfl
        · exact absurd h0 h
        · exact absurd h0 h
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h0)]
      by_cases h1 : cc = cL
      · rw [ite_eq_left_of_eq_true _ _ (eq_true h1)]
        constructor
        · intro he; exact Or.inr (Or.inl ⟨h0, h1, (Option.some.inj he).symm⟩)
        · rintro (⟨h, _⟩ | ⟨_, _, rfl⟩ | ⟨_, h, _⟩)
          · exact absurd h h0
          · rfl
          · exact absurd h1 h
      · rw [ite_eq_right_of_eq_false _ _ (eq_false h1)]
        by_cases h2 : cc = cR
        · rw [ite_eq_left_of_eq_true _ _ (eq_true h2)]
          constructor
          · intro he; cases he
          · rintro (⟨h, _⟩ | ⟨_, h, _⟩ | ⟨_, _, h, _⟩)
            · exact absurd h h0
            · exact absurd h h1
            · exact absurd h2 h
        · rw [ite_eq_right_of_eq_false _ _ (eq_false h2)]
          constructor
          · intro he; exact Or.inr (Or.inr ⟨h0, h1, h2, he⟩)
          · rintro (⟨h, _⟩ | ⟨_, h, _⟩ | ⟨_, _, _, he⟩)
            · exact absurd h h0
            · exact absurd h h1
            · exact he

set_option maxHeartbeats 1600000 in
/-- A time split, not in place, of the path's node x = X (D + 1) below an inner
parent X D, with any last version `last`: the writer's state after it and its
cascade (`writerWP_appendKlongs_chainGRQ`) reads as the tree with x's node
replaced by `last` (`getFromR_timeLevel`), when the state after fits the fuel or
the space root does not space split. -/
theorem writerWP_handleFull_timeV (c : Ctx) (base : View BVal)
    (path0 : List (Option Nat × NodeId)) (s D : Nat) (X : Nat → NodeId) (K : Nat → Nat)
    (Nn : Nat → KNode) (hsD : s ≤ D)
    (hX : ∀ i, s ≤ i → i ≤ D + 1 → (path0[i]?).map (·.2) = some (X i))
    (hK : ∀ i, s < i → i ≤ D + 1 → path0[i]? = some (some (K i), X i))
    (hlinkK : ∀ i, s < i → i ≤ D + 1 → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (hrange : ∀ i, s < i → i ≤ D → ¬ ChainRoom c (Nn i) → (Nn (i - 1)).leaf = false →
      ∀ c' z, (c', z) ∈ (Nn i).live → 0 < c' →
      K i ≤ c' ∧ ∀ c'' z', (c'', z') ∈ (Nn (i - 1)).live → K i < c'' → c' < c'')
    (hlen : ∀ i, s ≤ i → i ≤ D → ¬ ChainRoom c (Nn i) →
      c.p.splitAbove < ((Nn i).lastVersion c.i).size →
      2 ≤ (Nn i).live.length)
    (hwf : ∀ i, s ≤ i → i ≤ D + 1 → klongsWf (Nn i).ks = true)
    (htimes : ∀ i, s ≤ i → i ≤ D + 1 → ∀ t, Klong.time t ∈ (Nn i).ks → t ≤ c.i)
    (htop : ChainRoom c (Nn s) ∨ s = 0)
    (hdist : ∀ i i', s ≤ i → i ≤ D + 1 → s ≤ i' → i' ≤ D + 1 → X i = X i' → i = i')
    (hspace : ∀ i, s ≤ i → i ≤ D → ¬ ChainRoom c (Nn i) →
      c.p.splitAbove < ((Nn i).lastVersion c.i).size → i = 0 ∨ (s < i ∧ (Nn (i - 1)).leaf = false))
    (last : KNode) (compact : Bool) (w : W)
    (hfirst : (Nn (D + 1)).firstTime ≠ some c.i)
    (hcs : (!compact && decide (last.size > c.p.splitAbove)) = false)
    (hql : (Nn D).leaf = false)
    (hS1 : w.path = path0)
    (hS2 : ∀ i, s ≤ i → i ≤ D + 1 →
      w.nodes.lookup (X i) = some (Nn i) ∧ w.taken.contains (X i) = false)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hS4 : ∀ i, s ≤ i → i ≤ D + 1 → TReach (wNode c.p base w) c.i w.top.rootKey (X i))
    (hS5 : ∀ z, w.next ≤ z → w.nodes.lookup z = none ∧ w.taken.contains z = false ∧
      knodeOf c.p base z = none)
    (hS6 : ∀ u c' z, TLink (wNode c.p base w) c.i u c' z → z < w.next)
    (hR0 : s = 0 → ¬ ChainRoom c (Nn 0) → w.top.rootKey = X 0)
    (hW : ∀ z zn, wNode c.p base w z = some zn → klongsWf zn.ks = true)
    (hVal : ∀ z, (w.next ≤ z ∨ ∃ i, s ≤ i ∧ i ≤ D + 1 ∧ z = X i) → wValue base w z = none)
    (hVt : TreeOK (updN (wNode c.p base w) (X (D + 1)) ⟨(Nn (D + 1)).leaf, last.ks⟩) c.i w.top.rootKey)
    (hvx : ∀ c' z, (c', z) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i → z < w.next)
    (hxwf : klongsWf last.ks = true) (hxt : ∀ s, Klong.time s ∈ last.ks → s ≤ c.i) :
    WriterWP (handleFullWith (fun q more => appendKlongs D q more) (D + 1) (X (D + 1)) [] last compact)
      c w (fun _ w' => ¬ TReach (wNode c.p base w') c.i w'.top.rootKey (X (D + 1)) ∧
        (∀ z zn, TReach (wNode c.p base w') c.i w'.top.rootKey z → wNode c.p base w' z = some zn →
          klongsWf zn.ks = true) ∧
        ((SegFits (wNode c.p base w') c.i (c.p.fuel - 1) w'.top.rootKey ∨
          ¬ (s = 0 ∧ ¬ ChainRoom c (Nn 0) ∧ c.p.splitAbove < ((Nn 0).lastVersion c.i).size)) →
        ∀ key, getFromR (wNode c.p base w') (wValue base w') c.i c.p.fuel key w'.top.rootKey =
          getFromR (updN (wNode c.p base w) (X (D + 1)) ⟨(Nn (D + 1)).leaf, last.ks⟩) (wValue base w)
            c.i c.p.fuel key w.top.rootKey)) := by
  obtain ⟨hlkx, htkx⟩ := hS2 (D + 1) (by omega) (Nat.le_refl _)
  obtain ⟨hlkq, htkq⟩ := hS2 D hsD (by omega)
  have hpq : (w.path[D]?).map (·.2) = some (X D) := by rw [hS1]; exact hX D hsD (by omega)
  have hpk : w.path[D + 1]? = some (some (K (D + 1)), X (D + 1)) := by
    rw [hS1]; exact hK (D + 1) (by omega) (Nat.le_refl _)
  have hwx : wNode c.p base w (X (D + 1)) = some (Nn (D + 1)) := by
    simp only [wNode, htkx, Bool.false_eq_true, ↓reduceIte, hlkx]
  have hwq : wNode c.p base w (X D) = some (Nn D) := by
    simp only [wNode, htkq, Bool.false_eq_true, ↓reduceIte, hlkq]
  have hqx : X D ≠ X (D + 1) := by
    intro h; have := hdist D (D + 1) hsD (by omega) (by omega) (Nat.le_refl _) h; omega
  have hkl : (K (D + 1), X (D + 1)) ∈ (Nn D).liveAt c.i := by
    have := hlinkK (D + 1) (by omega) (Nat.le_refl _); simpa using this
  have hqwf := hwf D hsD (by omega)
  have hqt := htimes D hsD (by omega)
  obtain ⟨hfree0, htk0, hbase0⟩ := hS5 w.next (Nat.le_refl _)
  have hwY : wNode c.p base w w.next = none := by
    simp only [wNode, htk0, Bool.false_eq_true, ↓reduceIte, hfree0, hbase0]
  have hXlt : ∀ i, s ≤ i → i ≤ D + 1 → X i < w.next := by
    intro i h1 h2
    obtain ⟨hl, _⟩ := hS2 i h1 h2
    rcases Nat.lt_or_ge (X i) w.next with hlt | hge
    · exact hlt
    · have := (hS5 (X i) hge).1
      rw [hl] at this; cases this
  have hxY : X (D + 1) ≠ w.next := by have := hXlt (D + 1) (by omega) (Nat.le_refl _); omega
  have hqY : X D ≠ w.next := by have := hXlt D hsD (by omega); omega
  -- the virtual tree V
  generalize hxvd : (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode) = xv at hVt hvx ⊢
  have hxvwf : klongsWf xv.ks = true := by rw [← hxvd]; exact hxwf
  have hxvt : ∀ s, Klong.time s ∈ xv.ks → s ≤ c.i := by rw [← hxvd]; exact hxt
  have hVx : updN (wNode c.p base w) (X (D + 1)) xv (X (D + 1)) = some xv := updN_self _ _ _
  have hVq : updN (wNode c.p base w) (X (D + 1)) xv (X D) = some (Nn D) := by
    rw [updN_ne _ _ _ _ hqx]; exact hwq
  have hVY : updN (wNode c.p base w) (X (D + 1)) xv w.next = none := by
    rw [updN_ne _ _ _ _ (Ne.symm hxY)]; exact hwY
  have hVlinks : ∀ u c' z, TLink (updN (wNode c.p base w) (X (D + 1)) xv) c.i u c' z → z < w.next := by
    intro u c' z hl
    obtain ⟨m, hm, hc⟩ := hl
    by_cases hu : u = X (D + 1)
    · rw [hu, updN_self] at hm; cases hm; exact hvx c' z hc
    · rw [updN_ne _ _ _ _ hu] at hm; exact hS6 u c' z ⟨m, hm, hc⟩
  have hnoY : ∀ u c', TReach (updN (wNode c.p base w) (X (D + 1)) xv) c.i w.top.rootKey u →
      ¬ TLink (updN (wNode c.p base w) (X (D + 1)) xv) c.i u c' w.next := by
    intro u c' _ hl; have := hVlinks _ _ _ hl; omega
  -- q in V, by its depth above x
  obtain ⟨a, ha⟩ := (hS4 D hsD (by omega)).pathLen
  have hxa : PathLen (wNode c.p base w) c.i w.top.rootKey (X (D + 1)) (a + 1) :=
    PathLen.link ha ⟨Nn D, hwq, hkl⟩
  have hqV : TReach (updN (wNode c.p base w) (X (D + 1)) xv) c.i w.top.rootKey (X D) :=
    tReach_updN_of_short _ c.i _ _ _ a _ ha
      (fun k hk => by have := PathLen.depth_unique hT _ _ _ hk hxa; omega)
  have hrx : w.top.rootKey ≠ X (D + 1) := fun h =>
    hT.rootFree (X D) (K (D + 1)) (hS4 D hsD (by omega)) (by rw [h]; exact ⟨Nn D, hwq, hkl⟩)
  have hrY : w.top.rootKey ≠ w.next := by
    intro h
    obtain ⟨rn, hrn⟩ := hT.rootKey
    rw [h, hwY] at hrn; cases hrn
  apply writerWP_handleFullWith_time_up_last' D (X (D + 1)) (X D) (Nn (D + 1)) (Nn D) (K (D + 1))
    last compact c w hlkx hlkq hfirst hcs hpq hpk
  intro w1 h1n h1t h1top h1path h1next h1vals
  have hN1 : wNode c.p base w1 = updN (wNode c.p base w) w.next xv := by
    rw [← hxvd]; exact wNode_append_updN c.p base w w1 _ h1n h1t hfree0 htk0
  -- the tree with the parent's klong put
  obtain ⟨hTA, hRA⟩ := treeOK_timeSplit_gen (updN (wNode c.p base w) (X (D + 1)) xv)
    (updN (wNode c.p base w1) (X D) ((Nn D).add c.i (.key (K (D + 1)) w.next)))
    c.i w.top.rootKey (X D) (X (D + 1)) w.next (Nn D) xv xv ((Nn D).add c.i (.key (K (D + 1)) w.next))
    (K (D + 1)) hVt hqV hVq hkl hVx (updN_self _ _ _)
    (fun c' z h => KNode.add_key_liveAt_mem _ c.i _ _ hqwf hqt c' z h)
    (by rw [updN_ne _ _ _ _ (Ne.symm hqY), hN1]; exact updN_self _ _ _)
    (fun _ _ h => h)
    (by
      intro z hz1 hz2 hz3
      rw [updN_ne _ _ _ _ hz2, hN1, updN_ne _ _ _ _ hz3, updN_ne _ _ _ _ hz1])
    hVY hnoY
  have hlk1 : ∀ z zn, w.nodes.lookup z = some zn → w1.nodes.lookup z = some zn := by
    intro z zn hz
    rw [h1n, List.lookup_append, hz]; rfl
  have hv1 : wValue base w1 = wValue base w := by
    funext a; simp only [wValue, h1t, h1vals]
  have hchain := writerWP_appendKlongs_chainGRQ c base path0 s D X K Nn
    (fun i h1 h2 => hX i h1 (by omega)) (fun i h1 h2 => hK i h1 (by omega))
    (fun i h1 h2 => hlinkK i h1 (by omega)) hrange hlen (fun i h1 h2 => hwf i h1 (by omega))
    (fun i h1 h2 => htimes i h1 (by omega)) htop
    (fun i i' h1 h2 h3 h4 => hdist i i' h1 (by omega) h3 (by omega)) hspace (D - s) (by omega) w1
    [(K (D + 1), w.next)] (Or.inl ⟨_, _, rfl⟩)
    (by intro q hq; simp only [List.mem_singleton] at hq; rw [hq, h1next]; simp)
    (by rw [h1path, hS1])
    (by
      intro i h1 h2
      exact ⟨hlk1 _ _ (hS2 i h1 (by omega)).1, by rw [h1t]; exact (hS2 i h1 (by omega)).2⟩)
    (by
      rw [hN1, h1top]
      exact treeOK_updN_unreach _ c.i _ _ _ hT
        (not_reach_fresh _ c.i _ _ hT hwY (fun u c' _ hl => by have := hS6 _ _ _ hl; omega)))
    (by
      intro i h1 h2
      rw [hN1, h1top]
      obtain ⟨b, hb⟩ := (hS4 i h1 (by omega)).pathLen
      exact tReach_updN_of_short _ c.i _ _ _ b _ hb
        (fun k hk => absurd hk.reach
          (not_reach_fresh _ c.i _ _ hT hwY (fun u c' _ hl => by have := hS6 _ _ _ hl; omega))))
    (by
      intro z hz
      rw [h1next] at hz
      refine ⟨?_, by rw [h1t]; exact (hS5 z (by omega)).2.1, (hS5 z (by omega)).2.2⟩
      rw [h1n, List.lookup_append, (hS5 z (by omega)).1]
      have hb : (z == w.next) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; omega
      simp [List.lookup, hb])
    (by
      intro u c' z hl
      rw [hN1] at hl
      rw [h1next]
      obtain ⟨mm, hm, hc⟩ := hl
      by_cases hu : u = w.next
      · rw [hu, updN_self] at hm
        simp only [Option.some.injEq] at hm
        subst hm
        have := hvx c' z hc; omega
      · rw [updN_ne _ _ _ _ hu] at hm
        have := hS6 u c' z ⟨mm, hm, hc⟩; omega)
    (fun h0 hnr => by rw [h1top]; exact hR0 h0 hnr)
    (by
      intro z zn hz
      rw [hN1] at hz
      by_cases hzy : z = w.next
      · rw [hzy, updN_self] at hz; cases hz; exact hxvwf
      · rw [updN_ne _ _ _ _ hzy] at hz; exact hW z zn hz)
    (by
      intro z hz
      rw [hv1]
      rcases hz with hz | ⟨i, h1, h2, h3⟩
      · rw [h1next] at hz; exact hVal z (Or.inl (by omega))
      · exact hVal z (Or.inr ⟨i, h1, by omega, h3⟩))
    (by have hsD' : s + (D - s) = D := by omega
        rw [hsD', h1top]; exact hTA)
  have hsD' : s + (D - s) = D := by omega
  simp only [hsD'] at hchain
  refine writerWP_mono hchain ?_
  rintro _ w2 ⟨_, ⟨_, h2t, _, h2next, h2vals⟩, h2frame, h2reach, h2W, h2R, _⟩
  simp only [List.foldl_cons, List.foldl_nil] at h2R h2reach
  have hlkx2 : w2.nodes.lookup (X (D + 1)) = some (Nn (D + 1)) := by
    rw [h2frame _ (by rw [h1next]; have := hXlt (D + 1) (by omega) (Nat.le_refl _); omega)
      (fun i h1 h2 he => by have := hdist (D + 1) i (by omega) (Nat.le_refl _) h1 (by omega) he; omega)]
    exact hlk1 _ _ hlkx
  simp only [writerWP_bind]
  rw [writerWP_getNode_known _ _ c w2 hlkx2]
  simp only [putNode, writerWP_modify]
  have htk2 : w2.taken.contains (X (D + 1)) = false := by rw [h2t, h1t]; exact htkx
  have hN4 := wNode_upsert_updN c.p base w2
    { w2 with nodes := upsert w2.nodes (X (D + 1)) ((Nn (D + 1)).toPrev (c.i - 1)) } (X (D + 1)) _ rfl rfl htk2
  have hxR2 : ¬ TReach (wNode c.p base w2) c.i w2.top.rootKey (X (D + 1)) := by
    intro h
    rcases h2reach _ h with h' | h'
    · rw [h1top] at h'
      exact (hRA _ h').2 rfl
    · rw [h1next] at h'; have := hXlt (D + 1) (by omega) (Nat.le_refl _); omega
  have hwfV : ∀ z zn, ReachS (updN (wNode c.p base w) (X (D + 1)) xv) c.i w.top.rootKey z →
      updN (wNode c.p base w) (X (D + 1)) xv z = some zn → klongsWf zn.ks = true := by
    intro z zn _ hz
    by_cases hzx : z = X (D + 1)
    · rw [hzx, updN_self] at hz; cases hz; exact hxvwf
    · rw [updN_ne _ _ _ _ hzx] at hz; exact hW z zn hz
  have hres := getFromR_timeLevel (updN (wNode c.p base w) (X (D + 1)) xv)
    (updN (wNode c.p base w1) (X D) ((Nn D).add c.i (.key (K (D + 1)) w.next)))
    (wValue base w) c.i c.p.fuel w.top.rootKey (X D) (X (D + 1)) w.next (Nn D) xv xv (K (D + 1))
    hVt hwfV hVq (tReach_reachS _ _ _ _ hqV) hql hqwf hqt hkl hqx hVx hxvwf hxvt hVY
    (fun u c' hu hl => hnoY u c' (reachS_tReach _ _ _ _ hu) hl)
    (by rw [updN_ne _ _ _ _ (Ne.symm hqY), hN1]; exact updN_self _ _ _) rfl hxvwf hxvt (fun _ => rfl)
    (updN_self _ _ _)
    (by
      intro z hz1 hz2 hz3
      rw [updN_ne _ _ _ _ hz2, hN1, updN_ne _ _ _ _ hz3, updN_ne _ _ _ _ hz1])
    (by rw [hVal _ (Or.inr ⟨D + 1, by omega, Nat.le_refl _, rfl⟩), hVal _ (Or.inl (Nat.le_refl _))])
    hrY hrx
  refine ⟨fun h => ?_, fun z zn hz hzn => ?_, fun hq key' => ?_⟩
  · rw [hN4] at h
    exact hxR2 (tReach_updN_unreach _ c.i _ _ _ hxR2 _ h)
  · rw [hN4] at hz hzn
    have hz2 := tReach_updN_unreach _ c.i _ _ _ hxR2 _ hz
    have hzx : z ≠ X (D + 1) := fun he => hxR2 (by rw [← he]; exact hz2)
    rw [updN_ne _ _ _ _ hzx] at hzn
    exact h2W z zn hzn
  have hq2 := hq.imp (fun hf => SegFits.of_agree (wNode c.p base w2) _ c.i (c.p.fuel - 1)
    w2.top.rootKey (fun x hx => by rw [hN4]; exact updN_ne _ _ _ _ (fun he => hxR2 (he ▸ hx))) hf) id
  show getFromR (wNode c.p base { w2 with nodes := upsert w2.nodes (X (D + 1)) ((Nn (D + 1)).toPrev (c.i - 1)) })
    (wValue base { w2 with nodes := upsert w2.nodes (X (D + 1)) ((Nn (D + 1)).toPrev (c.i - 1)) }) c.i
    c.p.fuel key' w2.top.rootKey = _
  have hv4 : wValue base { w2 with nodes := upsert w2.nodes (X (D + 1)) ((Nn (D + 1)).toPrev (c.i - 1)) } =
      wValue base w2 := rfl
  rw [hN4, hv4]
  rw [getFromR_updN_unreach' (wNode c.p base w2) (wValue base w2) c.i c.p.fuel w2.top.rootKey
    (X (D + 1)) _ (fun z zn _ h => h2W z zn h) (fun h => hxR2 (reachS_tReach _ _ _ _ h)) key']
  have hv2 : wValue base w2 = wValue base w1 := by
    funext a; simp only [wValue, h2t, h2vals]
  rw [h2R hq2 key', hv1, h1top, hres key']

end SIS.Tree
