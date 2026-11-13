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

set_option maxHeartbeats 3200000 in
theorem writerWP_mergeTail_full_get (c : Ctx) (base : View BVal) (x : NodeId) (d : Nat) (p : NodeId)
    (pn xn : KNode) (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId)
    (rn : KNode) (ir : Nat) (cL cR : Nat) (N : NodeId → Option KNode) (root : NodeId) (nx : Nat)
    (w3 : W) (hT : TreeOK N c.i root) (hp : TReach N c.i root p) (hpn : N p = some pn)
    (hL : pn.ks[il]? = some (.key cL l)) (hLL : LastLive pn.ks pn.lastBitmap il cL)
    (hR : pn.ks[ir]? = some (.key cR r)) (hRL : LastLive pn.ks pn.lastBitmap ir cR)
    (hc : cL ≠ cR) (hxlr : x = l ∨ x = r) (hln : N l = some ln) (hrn : N r = some rn)
    (hpwf : klongsWf pn.ks = true) (hpt : ∀ s, Klong.time s ∈ pn.ks → s ≤ c.i)
    (hch : ∀ cc z zn, (cc, z) ∈ pn.liveAt c.i → N z = some zn →
      ∀ s, Klong.time s ∈ zn.ks → s ≤ c.i)
    (hN3 : wNode c.p base w3 = N) (h3top : w3.top.rootKey = root) (h3next : w3.next = nx)
    (h3p : w3.nodes.lookup p = some pn) (h3src : ∀ z, (w3.nodes.lookup z).isSome = true → z < nx)
    (hfree : ∀ z, nx ≤ z → N z = none ∧ w3.taken.contains z = false)
    (hfreshT : ∀ z, nx ≤ z → ∀ u c', TReach N c.i root u → ¬ TLink N c.i u c' z)
    (hpleaf : pn.leaf = false) (hclt : cL < cR) (hcap : 1 ≤ c.p.mergeMax)
    (hadj : ∀ cc z, (cc, z) ∈ pn.liveAt c.i → cc ≤ cL ∨ cR ≤ cc)
    (hll : ln.leaf = xn.leaf) (hrl : rn.leaf = xn.leaf)
    (hlrange : ∀ cc z, (cc, z) ∈ ln.liveAt c.i → cc < cR)
    (hllow : ∀ cc z, (cc, z) ∈ ln.liveAt c.i →
      ((!xn.leaf) = true → cc = 0 ∨ cL < cc) ∧ ((!xn.leaf) = false → cL ≤ cc))
    (hrrange : ∀ cc z, (cc, z) ∈ rn.liveAt c.i →
      ((!xn.leaf) = true → cc = 0 ∨ cR < cc) ∧ ((!xn.leaf) = false → cR ≤ cc))
    (hrup : ∀ k z, (k, z) ∈ pn.liveAt c.i → cR < k → ∀ cc z', (cc, z') ∈ rn.liveAt c.i → cc < k)
    (htimesN : ∀ y yn, N y = some yn → ∀ s, Klong.time s ∈ yn.ks → s ≤ c.i)
    (hwfN : ∀ y yn, N y = some yn → klongsWf yn.ks = true)
    (hnoval : ∀ y yn, N y = some yn → wValue base w3 y = none)
    (hvc : ViewCoherent c base)
    (hlinksAll : ∀ u c' z, TLink N c.i u c' z → z < nx)
    (hbaseF : ∀ z, nx ≤ z → knodeOf c.p base z = none)
    (hfreshV : ∀ z, nx ≤ z → wValue base w3 z = none)
    (s D : Nat) (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode) (hsD : s ≤ D)
    (hd : d - 1 = D + 1)
    (hX : ∀ i, s ≤ i → i ≤ D + 1 → (w3.path[i]?).map (·.2) = some (X i))
    (hK : ∀ i, s < i → i ≤ D + 1 → w3.path[i]? = some (some (K i), X i))
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
    (hXp : X (D + 1) = p) (hNp : Nn (D + 1) = pn)
    (hS2 : ∀ i, s ≤ i → i ≤ D + 1 →
      w3.nodes.lookup (X i) = some (Nn i) ∧ w3.taken.contains (X i) = false)
    (hS4 : ∀ i, s ≤ i → i ≤ D + 1 → TReach N c.i root (X i))
    (hR0 : s = 0 → root = X 0)
    (hXx : ∀ i, s ≤ i → i ≤ D + 1 → X i ≠ x)
    (hhalves : ∀ m1 m2 last, mergeFullLast pn c.i cL m1 cR m2 = some last →
      c.p.splitAbove < last.size → ∃ r0 : Nat, 0 < r0 ∧
      (halves (Nn (D + 1)).leaf c.i last []).2.2 = r0 ∧
      (∀ c' z, (c', z) ∈ (halves (Nn (D + 1)).leaf c.i last []).1.liveAt c.i → c' < r0 ∧
        (c', z) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i) ∧
      (∀ c' z, (c', z) ∈ (halves (Nn (D + 1)).leaf c.i last []).2.1.liveAt c.i → ∃ c0, r0 ≤ c0 ∧
        c' = splitLocalCv (Nn (D + 1)).leaf r0 c0 ∧
        (c0, z) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i) ∧
      ((Nn D).leaf = false →
        K (D + 1) ≤ r0 ∧ ∀ c'' z', (c'', z') ∈ (Nn D).live → K (D + 1) < c'' → r0 < c''))
    (hpfirst : pn.firstTime ≠ some c.i) (hql : (Nn D).leaf = false)
    (hnospace : ∀ m1 m2 last, mergeFullLast pn c.i cL m1 cR m2 = some last →
      last.size ≤ c.p.splitAbove) :
    WriterWP (mergeTail c x d p pn xn leftSome l ln il r rn ir) c w3
      (fun _ w' => (SegFits (wNode c.p base w') c.i (c.p.fuel - 1) w'.top.rootKey ∨
          ¬ (s = 0 ∧ ¬ ChainRoom c (Nn 0) ∧ c.p.splitAbove < ((Nn 0).lastVersion c.i).size)) →
        ∀ key, wGet c.p c.i base w' key = wGet c.p c.i base w3 key) := by
  -- the tree's facts
  have hpL : (cL, l) ∈ pn.liveAt c.i := by
    rw [KNode.liveAt_of_times pn c.i hpt]
    apply mem_of_lookup_nodup
    rw [KNode.live_lookup]
    exact keyLookup_of_last _ _ _ il l hL hLL
  have hpR : (cR, r) ∈ pn.liveAt c.i := by
    rw [KNode.liveAt_of_times pn c.i hpt]
    apply mem_of_lookup_nodup
    rw [KNode.live_lookup]
    exact keyLookup_of_last _ _ _ ir r hR hRL
  have hlink_l : TLink N c.i p cL l := ⟨pn, hpn, hpL⟩
  have hlink_r : TLink N c.i p cR r := ⟨pn, hpn, hpR⟩
  have hlR : TReach N c.i root l := TReach.link hp hlink_l
  have hrR : TReach N c.i root r := TReach.link hp hlink_r
  have hpl : p ≠ l := fun h => hT.no_self_link p cL hp (by rw [← h] at hlink_l; exact hlink_l)
  have hpr : p ≠ r := fun h => hT.no_self_link p cR hp (by rw [← h] at hlink_r; exact hlink_r)
  have hpx : p ≠ x := by rcases hxlr with h | h <;> rw [h] <;> assumption
  have hlt := hch cL l ln hpL hln
  have hrt := hch cR r rn hpR hrn
  have hcvL : pn.cv? il = some cL := by simp [KNode.cv?, hL]
  have hcvR : pn.cv? ir = some cR := by simp [KNode.cv?, hR]
  have hlt_nx : ∀ y yn, N y = some yn → y < nx := by
    intro y yn hy
    rcases Nat.lt_or_ge y nx with h | h
    · exact h
    · have := (hfree y h).1; rw [this] at hy; cases hy
  have hlnx := hlt_nx l ln hln
  have hrnx := hlt_nx r rn hrn
  have hpnx := hlt_nx p pn hpn
  unfold mergeTail
  simp only [hcvL, hcvR]
  generalize hLM : (ln.firstTime == some c.i) = lMade
  generalize hRM : (rn.firstTime == some c.i) = rMade
  simp only [note, writerWP_bind, writerWP_modify, writerWP_pure]
  generalize hmk : mergeKlongs (!xn.leaf) c.p.mergeMax cR ln.live rn.live = fs
  obtain ⟨first, second⟩ := fs
  wpSplit
  · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
  wpSplit
  · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
  rename_i hne1 hne2
  have hrhead : (!xn.leaf) = true → ∃ y0 tl, rn.live = (0, y0) :: tl := by
    intro hin
    rw [hin] at hne2
    simp only [Bool.true_and, Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not]
      at hne2
    cases hr' : rn.live with
    | nil => rw [hr'] at hne2; simp at hne2
    | cons a tl =>
      rw [hr'] at hne2
      simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hne2
      exact ⟨a.2, tl, by rw [← hne2.2]⟩
  have hsortE := mrg_mergeList_sorted ln rn c.i (!xn.leaf) cR hlt hrt hlrange hrrange hrhead
  have hndE : ((mergeList (!xn.leaf) cR ln.live rn.live).map Prod.fst).Nodup :=
    List.pairwise_map.mpr (hsortE.imp (by intro a b hab; omega))
  have hll' : ln.leaf = !(!xn.leaf) := by rw [hll]; simp
  have hrl' : rn.leaf = !(!xn.leaf) := by rw [hrl]; simp
  have hm1notR : ¬ TReach N c.i root nx := not_reach_fresh N c.i root nx hT (hfree nx (Nat.le_refl _)).1
    (hfreshT nx (Nat.le_refl _))
  obtain ⟨hparOne, hparTwo⟩ := mrg_parent_liveAt pn c.i il cL nx ir cR l r hpwf hpt hL hLL hR hRL hc
  -- the merged nodes: not taken, no value
  have hlrS : ∀ y, (y = l ∨ y = r) → w3.taken.contains y = false ∧ wValue base w3 y = none := by
    intro y hy
    obtain ⟨yn, hyn⟩ : ∃ yn, N y = some yn := by
      rcases hy with hy | hy <;> rw [hy]
      · exact ⟨ln, hln⟩
      · exact ⟨rn, hrn⟩
    refine ⟨?_, hnoval y yn hyn⟩
    have := hN3 ▸ hyn
    unfold wNode at this
    split at this
    · cases this
    · rename_i h; simpa using h
  simp only [writerWP_bind, writerWP_modify]
  refine writerWP_mono (writerWP_and (writerWP_ghOf_frame x c _) (writerWP_ghOf_reads x c _ base hvc)) ?_
  intro gh w4 ⟨⟨h4t, h4top, h4n, h4v, h4p, h4m, h4l⟩, hr4⟩
  have hcl' : ∀ (b1 b2 : Bool) y, y ≠ l → y ≠ r → ∀ q ∈ [(l, b1), (r, b2)], y ≠ (q : NodeId × Bool).1 := by
    intro b1 b2 y hyl hyr q hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with h | h <;> rw [h] <;> assumption
  have hne' : ∀ (b1 b2 : Bool), ∀ q ∈ [(l, b1), (r, b2)], (q : NodeId × Bool).1 ≠ p := by
    intro b1 b2 q hq
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
    rcases hq with h | h <;> rw [h]
    · exact Ne.symm hpl
    · exact Ne.symm hpr
  cases lMade <;> cases rMade <;>
    simp only [Bool.false_eq_true, ↓reduceIte, writerWP_bind, writerWP_modify, writerWP_pure,
      replacedBy, writerWP_get]
  all_goals
    refine writerWP_mono (writerWP_newKey_frame _ _ _ _ c _) ?_
    intro m1 w5 ⟨hm1, h5n, h5t, h5top, h5next, h5v, h5p, h5m⟩
    refine writerWP_mono (writerWP_setMadeFor_frame _ _ c _) ?_
    intro _ w6 ⟨h6n, h6t, h6top, h6next, h6v, h6p⟩
    -- the ids
    have hm1 : m1 = nx := by rw [hm1, h4n, h3next]
    subst hm1
    have hxnx : x < m1 := by rcases hxlr with h | h <;> rw [h] <;> assumption
    have hlk4 : ∀ y, y ≠ x → w4.nodes.lookup y = w3.nodes.lookup y := h4l
    have hnone3 : ∀ z, m1 ≤ z → w3.nodes.lookup z = none := by
      intro z hz
      cases h' : w3.nodes.lookup z with
      | none => rfl
      | some _ => have := h3src z (by rw [h']; rfl); omega
    have hw6p : w6.nodes.lookup p = some pn := by
      rw [h6n, h5n, lookup_append_single_ne _ _ _ _ (by omega), hlk4 p hpx, h3p]
    have hw6m1 : w6.nodes.lookup w4.next = some ⟨!!xn.leaf, newKlongs c.i first⟩ := by
      rw [h6n, h5n, lookup_append_single_self]
      rw [hlk4 _ (by rw [h4n, h3next]; omega), h4n, h3next]
      exact hnone3 m1 (Nat.le_refl _)
    have h6taken : w6.taken = w3.taken := by rw [h6t, h5t, h4t]
    have h6old : ∀ y, y ≠ x → y ≠ m1 → w6.nodes.lookup y = w3.nodes.lookup y := by
      intro y hyx hym
      rw [h6n, h5n, lookup_append_single_ne _ _ _ _ (by rw [h4n, h3next]; exact hym), hlk4 y hyx]
    have hpT : w3.taken.contains p = false := by
      have := hN3 ▸ hpn
      unfold wNode at this
      split at this
      · cases this
      · rename_i h; simpa using h
    have hm1T : w3.taken.contains m1 = false := (hfree m1 (Nat.le_refl _)).2
    have hm1N : N m1 = none := (hfree m1 (Nat.le_refl _)).1
    have hNw3 : ∀ y, wNode c.p base w3 y = N y := fun y => by rw [hN3]
    have hhtd := htd_last pn
    -- the parent after
    have hpliveAt : ∀ (m2 : Option (NodeId × Nat)),
        ∀ cc z, (cc, z) ∈ (mergeParentNode pn c.i il cL m1 ir cR m2).liveAt c.i →
        (mergeParentNode pn c.i il cL m1 ir cR m2).live.lookup cc = some z := by
      intro m2 cc z hm
      rw [KNode.liveAt_of_times _ c.i (by
        rw [mergeParentNode_eq]
        exact mpNode_times pn c.i il cL m1 ir cR m2 _ _ _ (hhtd _) hpt)] at hm
      exact lookup_of_mem_nodup _ (KNode.live_keys_nodup _) cc z hm
    have hlm1 : l ≠ m1 := by omega
    have hrm1 : r ≠ m1 := by omega
    have hpm1 : p ≠ m1 := by omega
    have hw4m1 : w4.next = m1 := by rw [h4n, h3next]
    rw [hw4m1] at hw6m1
    have hmkd : splitMerged (!xn.leaf) c.p.mergeMax (mergeList (!xn.leaf) cR ln.live rn.live) =
        (first, second) := hmk
    have h6top' : w6.top.rootKey = root := by rw [h6top, h5top, h4top, h3top]
    have hyx : ∀ y, y ≠ l → y ≠ r → y ≠ x := by
      intro y hyl hyr; rcases hxlr with h | h <;> rw [h] <;> assumption
    have hlr' : ∀ (b1 b2 : Bool) (q : NodeId × Bool), q ∈ [(l, b1), (r, b2)] → q.1 = l ∨ q.1 = r := by
      intro b1 b2 q hq
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
      rcases hq with h | h <;> rw [h]
      · exact Or.inl rfl
      · exact Or.inr rfl
    -- the parent after, into one node
    have hchar1 : ∀ cc z, (cc, z) ∈ (mergeParentNode pn c.i il cL m1 ir cR none).liveAt c.i →
        (cc = cL ∧ z = m1) ∨ ((cc, z) ∈ pn.liveAt c.i ∧ cc ≠ cL ∧ cc ≠ cR) := by
      intro cc z hm
      have hlk := hpliveAt none cc z hm
      rw [mergeParentNode_eq, mpNode_live_lookup pn c.i il cL m1 ir cR none _ _ _ l r hpwf hL hLL hR hRL
        hc ?htd (fun _ _ _ h => by cases h) cc] at hlk
      case htd =>
        intro h
        cases hg : pn.ks.getLast? with
        | none => rw [hg] at h; simp at h
        | some k =>
          cases k with
          | del old => exact ⟨old, rfl⟩
          | time t => rw [hg] at h; simp at h
          | key a y => rw [hg] at h; simp at h
      simp only at hlk
      by_cases h1 : cc = cL
      · simp only [h1, ↓reduceIte, Option.some.injEq] at hlk
        exact Or.inl ⟨h1, hlk.symm⟩
      · by_cases h2 : cc = cR
        · simp [h2, Ne.symm hc] at hlk
        · simp only [h1, h2, ↓reduceIte] at hlk
          right
          refine ⟨?_, h1, h2⟩
          rw [KNode.liveAt_of_times pn c.i hpt]
          exact mem_of_lookup_nodup _ cc z hlk
    -- the parent after, into two nodes
    have hchar2 : ∀ (m2 : NodeId) (g2 : Nat) cc z,
        (cc, z) ∈ (mergeParentNode pn c.i il cL m1 ir cR (some (m2, g2))).liveAt c.i →
        (cc = cL ∧ z = m1) ∨ (cc = g2 ∧ z = m2) ∨ ((cc, z) ∈ pn.liveAt c.i ∧ cc ≠ cL ∧ cc ≠ cR) := by
      intro m2 g2 cc z hm
      have hlk := hpliveAt (some (m2, g2)) cc z hm
      rw [mergeParentNode_eq, mpNode_live_lookup pn c.i il cL m1 ir cR (some (m2, g2)) _ _ _ l r
        hpwf hL hLL hR hRL hc ?htd ?hrip cc] at hlk
      case htd =>
        intro h
        cases hg : pn.ks.getLast? with
        | none => rw [hg] at h; simp at h
        | some k =>
          cases k with
          | del old => exact ⟨old, rfl⟩
          | time t => rw [hg] at h; simp at h
          | key a y => rw [hg] at h; simp at h
      case hrip =>
        intro h y g heq
        simp only [Option.some.injEq, Prod.mk.injEq] at heq
        obtain ⟨_, rfl⟩ := heq
        simp at h
        exact h.1.1
      simp only at hlk
      by_cases h0 : cc = g2
      · simp only [h0, ↓reduceIte, Option.some.injEq] at hlk
        exact Or.inr (Or.inl ⟨h0, hlk.symm⟩)
      · by_cases h1 : cc = cL
        · subst h1
          simp only [h0, ↓reduceIte, Option.some.injEq] at hlk
          exact Or.inl ⟨rfl, hlk.symm⟩
        · by_cases h2 : cc = cR
          · subst h2
            simp [h0, h1] at hlk
          · simp only [h0, h1, h2, ↓reduceIte] at hlk
            right; right
            refine ⟨?_, h1, h2⟩
            rw [KNode.liveAt_of_times pn c.i hpt]
            exact mem_of_lookup_nodup _ cc z hlk
    -- neither merged node is named live by the parent after
    -- the full parent's facts, from any state S with the nodes below m1 as before
    have hlnx' : l < m1 := hlnx
    have hrnx' : r < m1 := hrnx
    have hchild : ∀ z, ((∃ c0, (c0, z) ∈ ln.live) ∨ (∃ c0, (c0, z) ∈ rn.live)) → z < m1 := by
      rintro z (⟨c0, h0⟩ | ⟨c0, h0⟩)
      · exact hlinksAll l c0 z ⟨ln, hln, by rw [KNode.liveAt_of_times ln c.i hlt]; exact h0⟩
      · exact hlinksAll r c0 z ⟨rn, hrn, by rw [KNode.liveAt_of_times rn c.i hrt]; exact h0⟩
    have hsnd : ∀ z (E : List (Nat × NodeId)), (∀ q ∈ E, ∃ q' ∈ ln.live ++ rn.live, q'.2 = q.2) →
        ∀ c', (c', z) ∈ E → (∃ c0, (c0, z) ∈ ln.live) ∨ (∃ c0, (c0, z) ∈ rn.live) := by
      intro z E hE c' hm
      obtain ⟨q', hq', he⟩ := hE (c', z) hm
      rcases List.mem_append.mp hq' with h | h
      · exact Or.inl ⟨q'.1, by rw [show z = q'.2 from he.symm]; exact h⟩
      · exact Or.inr ⟨q'.1, by rw [show z = q'.2 from he.symm]; exact h⟩
    have hXlt : ∀ i, s ≤ i → i ≤ D + 1 → X i < m1 := by
      intro i h1 h2
      obtain ⟨hl3, ht3⟩ := hS2 i h1 h2
      have hNX : N (X i) = some (Nn i) := by
        rw [← hNw3]; simp only [wNode, ht3, Bool.false_eq_true, ↓reduceIte, hl3]
      rcases Nat.lt_or_ge (X i) m1 with h | h
      · exact h
      · rw [(hfree _ h).1] at hNX; cases hNX
    have hm1R : ¬ TReach N c.i root m1 := not_reach_fresh N c.i root m1 hT hm1N (hfreshT m1 (Nat.le_refl _))
    have hnoOld : ∀ z, (z = l ∨ z = r) → ∀ cc, (cc, z) ∈ pn.liveAt c.i → cc ≠ cL → cc ≠ cR → False := by
      intro z hz cc hm h1 h2
      rcases hz with hz | hz
      · rw [hz] at hm
        exact h1 (hT.oneLink p cc p cL l hp hp ⟨pn, hpn, hm⟩ hlink_l).2
      · rw [hz] at hm
        exact h2 (hT.oneLink p cc p cR r hp hp ⟨pn, hpn, hm⟩ hlink_r).2
    cases hsec : second with
    | none =>
      rw [hsec] at hmkd
      have hfirst : first = mergeList (!xn.leaf) cR ln.live rn.live := splitMerged_one _ _ _ _ hmkd
      simp only [writerWP_bind, writerWP_pure]
      refine writerWP_mergeParent_cases p pn (d - 1) il cL m1 ir cR none c w6 _ hw6p ?_ ?_
      rotate_left
      · intro last compact s7 hlast
        rw [hd]
        have hw6w4 : ∀ y, y ≠ m1 → wNode c.p base w6 y = wNode c.p base w4 y := by
          intro y hym
          unfold wNode
          rw [h6taken, ← h4t, h6n, h5n, lookup_append_single_ne _ _ _ _ (by rw [hw4m1]; exact hym)]
        have hlow6 : ∀ y, y < m1 → wNode c.p base w6 y = N y := by
          intro y hy
          rw [hw6w4 y (by omega), hr4.1, ← hN3]; rfl
        have hnew6 : ∀ y yn, m1 ≤ y → w6.nodes.lookup y = some yn → ∀ c' z, (c', z) ∈ yn.liveAt c.i →
            z < m1 := by
          intro y yn hy hyn c' z hz
          by_cases hym : y = m1
          · rw [hym, hw6m1] at hyn
            cases hyn
            have hm := liveAt_newKlongs_mem _ c.i c.i first c' z hz
            apply hchild
            apply hsnd z first _ c' hm
            intro q hq
            have : q.2 ∈ (ln.live ++ rn.live).map Prod.snd := by
              rw [List.map_append, ← mergeList_map_snd (!xn.leaf) cR, ← hfirst]
              exact List.mem_map.mpr ⟨q, hq, rfl⟩
            obtain ⟨q', hq', he⟩ := List.mem_map.mp this
            exact ⟨q', hq', he⟩
          · rw [h6old y (by omega) hym, hnone3 y hy] at hyn; cases hyn
        have hhigh6 : ∀ y, w6.next ≤ y → w6.nodes.lookup y = none := by
          intro y hy
          have h6nx : w6.next = m1 + 2 := by rw [h6next, h5next, hw4m1]
          rw [h6old y (by omega) (by omega), hnone3 y (by omega)]
        obtain ⟨h6S2, h6T, h6S4, h6S5, h6S6, h6R0⟩ := mergeState_facts c base N root m1 w3 w6 s D X Nn
          hT h3top hfree hlinksAll hbaseF hS2 hS4 hR0
          (fun i h1 h2 => h6old _ (hXx i h1 h2) (by have := hXlt i h1 h2; omega)) h6taken
          (by rw [h6top, h5top, h4top]) (by rw [h6next, h5next, hw4m1]; omega) hlow6 hnew6 hhigh6
        have hV6 : ∀ last, mergeFullLast pn c.i cL m1 cR none = some last →
            TreeOK (updN (wNode c.p base w6) p ⟨pn.leaf, last.ks⟩) c.i w6.top.rootKey ∧
            (∀ z, TReach (updN (wNode c.p base w6) p ⟨pn.leaf, last.ks⟩) c.i w6.top.rootKey z →
              z ≠ l ∧ z ≠ r) ∧
            ∀ c' z, (c', z) ∈ (⟨pn.leaf, last.ks⟩ : KNode).liveAt c.i → z < w6.next := by
          intro last hlast
          obtain ⟨_, hleafl, hnoneL, _⟩ := mergeFullLast_liveAt pn c.i cL m1 cR none last hlast hpt
          have hlasteq : (⟨pn.leaf, last.ks⟩ : KNode) = last := by
            cases last with
            | mk lf ks => simp only at hleafl; rw [hleafl]
          rw [hlasteq, h6top']
          have hVp : updN (wNode c.p base w6) p last p = some last := updN_self _ _ _
          have hVm1 : updN (wNode c.p base w6) p last m1 = some ⟨!!xn.leaf, newKlongs c.i first⟩ := by
            rw [updN_ne _ _ _ _ (Ne.symm hpm1)]
            simp only [wNode, h6taken, hm1T, Bool.false_eq_true, ↓reduceIte, hw6m1]
          have hVN : ∀ y, y ≠ p → y ≠ m1 → updN (wNode c.p base w6) p last y = N y := by
            intro y hyp hym
            rw [updN_ne _ _ _ _ hyp]
            rcases Nat.lt_or_ge y m1 with hy | hy
            · exact hlow6 y hy
            · have hyw : wNode c.p base w6 y = none := by
                simp only [wNode, h6taken, (hfree y hy).2, Bool.false_eq_true, ↓reduceIte,
                  h6old y (by omega) hym, hnone3 y hy, hbaseF y hy]
              rw [hyw, (hfree y hy).1]
          have hmn : ∀ cc z, (cc, z) ∈ ({ leaf := !!xn.leaf, ks := newKlongs c.i first } : KNode).liveAt c.i →
              (cc, z) ∈ mergeList (!xn.leaf) cR ln.live rn.live := by
            intro cc z hm
            have := liveAt_newKlongs_mem (!!xn.leaf) c.i c.i first cc z hm
            rw [hfirst] at this; exact this
          refine ⟨treeOK_mergeOneAfter N _ c.i root p l r m1 pn ln rn last ⟨!!xn.leaf, newKlongs c.i first⟩
            (!xn.leaf) cL cR hT hp hpn hpL hpR hc hln hrn hlt hrt hm1N (hfreshT m1 (Nat.le_refl _))
            hVm1 hmn hVp (hnoneL rfl) (fun y hyp _ _ hym => hVN y hyp hym), fun z hz => ?_, fun c' z hm => ?_⟩
          · have := mergeV_reach N _ c.i root p l r m1 none pn ln rn last cL cR hT hp hpn hpL hpR hln hrn hVp
              (fun cc z hm => by
                rcases hnoneL rfl cc z hm with ⟨_, h⟩ | h
                · exact Or.inl h
                · exact Or.inr (Or.inr h))
              (fun m mn hm hmn' cc z hz => by
                rcases hm with hm | hm
                · rw [hm, hVm1] at hmn'
                  cases hmn'
                  have hm2 := hmn cc z hz
                  have hsn := (mergeList_map_snd (!xn.leaf) cR ln.live rn.live)
                  have hz' : z ∈ (ln.live ++ rn.live).map Prod.snd := by
                    rw [List.map_append, ← hsn]; exact List.mem_map.mpr ⟨(cc, z), hm2, rfl⟩
                  obtain ⟨q', hq', he⟩ := List.mem_map.mp hz'
                  rcases List.mem_append.mp hq' with h | h
                  · exact Or.inl ⟨q'.1, by rw [KNode.liveAt_of_times ln c.i hlt, ← he]; exact h⟩
                  · exact Or.inr ⟨q'.1, by rw [KNode.liveAt_of_times rn c.i hrt, ← he]; exact h⟩
                · cases hm)
              (fun y hyp _ _ hym _ => hVN y hyp hym) hm1R (fun m hm => by cases hm) z hz
            exact ⟨this.2.1, this.2.2⟩
          · have h6nx : w6.next = m1 + 2 := by rw [h6next, h5next, hw4m1]
            rcases hnoneL rfl c' z hm with ⟨_, h⟩ | ⟨h, _, _⟩
            · omega
            · have := hlinksAll p c' z ⟨pn, hpn, h⟩; omega
        obtain ⟨hVt, _, hvx⟩ := hV6 last hlast
        obtain ⟨htl, hleafl, _, _⟩ := mergeFullLast_liveAt pn c.i cL m1 cR none last hlast hpt
        obtain ⟨hiffN, _⟩ := mergeFullLast_iff pn c.i cL m1 cR none last hlast hpt
        obtain ⟨pairsL, hksL⟩ := mergeFullLast_ks pn c.i cL m1 cR none last hlast
        have hlwf : klongsWf last.ks = true := by rw [hksL]; exact klongsWf_newKlongs c.i pairsL
        have hlasteq : (⟨pn.leaf, last.ks⟩ : KNode) = last := by
          cases last with
          | mk lf ks => simp only at hleafl; rw [hleafl]
        have hcs : (!compact && decide (last.size > c.p.splitAbove)) = false := by
          have := hnospace m1 none last hlast
          cases compact <;> simp <;> omega
        have h6v' : w6.vals = w3.vals := by rw [h6v, h5v, h4v]
        have hv6 : wValue base w6 = wValue base w3 := wValue_congr' base w6 w3 h6taken h6v'
        have hW6 : ∀ z zn, wNode c.p base w6 z = some zn → klongsWf zn.ks = true := by
          intro z zn hz
          rcases Nat.lt_or_ge z m1 with h | h
          · rw [hlow6 z h] at hz; exact hwfN z zn hz
          · by_cases hzm : z = m1
            · rw [hzm] at hz
              simp only [wNode, h6taken, hm1T, Bool.false_eq_true, ↓reduceIte, hw6m1] at hz
              cases hz; exact klongsWf_newKlongs c.i first
            · simp only [wNode, h6taken, (hfree z h).2, Bool.false_eq_true, ↓reduceIte,
                h6old z (by omega) hzm, hnone3 z h, hbaseF z h] at hz
              cases hz
        have hVal6 : ∀ z, (w6.next ≤ z ∨ ∃ i, s ≤ i ∧ i ≤ D + 1 ∧ z = X i) → wValue base w6 z = none := by
          intro z hz
          rw [hv6]
          rcases hz with hz | ⟨i, h1, h2, h3⟩
          · have : w6.next = m1 + 2 := by rw [h6next, h5next, hw4m1]
            exact hfreshV z (by omega)
          · rw [h3]
            obtain ⟨hl3, ht3⟩ := hS2 i h1 h2
            exact hnoval _ (Nn i) (by rw [← hNw3]; simp only [wNode, ht3, Bool.false_eq_true, ↓reduceIte, hl3])
        have htime := writerWP_handleFull_timeV c base w3.path s D X K Nn hsD hX hK hlinkK hrange hlen
          hwf htimes htop hdist hspace last compact ({ w6 with trail := s7 :: w6.trail } : W)
          (by rw [hNp]; exact hpfirst) hcs hql (by show w6.path = w3.path; rw [h6p, h5p, h4p])
          h6S2 h6T h6S4 h6S5 h6S6 (fun h0 _ => h6R0 h0) hW6 hVal6 (by rw [hXp, hNp]; exact hVt)
          (by rw [hNp]; exact hvx) hlwf htl
        rw [hXp] at htime
        have hbr := writerWP_mergeFull_branch c base w3.path s D X K Nn hsD hX hK hlinkK hrange hlen hwf
          htimes htop hdist p l r m1 none pn cL cR hXp hNp (hhalves m1 none) w6
          (by rw [h6p, h5p, h4p]) h6S2 h6T h6S4 h6S5 h6S6 h6R0 hV6
          ⟨by rw [h6next, h5next, hw4m1]; omega, by rw [h6next, h5next, hw4m1]; omega⟩
          last compact s7 hlast
        refine writerWP_mono (writerWP_and htime hbr) ?_
        rintro _ w7 ⟨⟨hxR7, hW7, hR7⟩, hT7, hl7, hr7, ht7, hv7⟩
        refine writerWP_mono (writerWP_mergeCleanup_wNode p m1 c base hvc _ w7 (hne' _ _)
          (by rw [ht7, h6taken]; exact hpT)) ?_
        rintro _ w8 ⟨h8top, _, h8v, h8tk, h8l, _, _⟩
        try simp only [writerWP_pure]
        intro hq key
        have hag : ∀ y, ReachS (wNode c.p base w7) c.i w7.top.rootKey y →
            wNode c.p base w8 y = wNode c.p base w7 y := by
          intro y hy
          have hyT := reachS_tReach _ _ _ _ hy
          have hyp : y ≠ p := fun he => hxR7 (by rw [← he]; exact hyT)
          have hyl : y ≠ l := fun he => hl7 (by rw [← he]; exact hyT)
          have hyr : y ≠ r := fun he => hr7 (by rw [← he]; exact hyT)
          exact h8l y hyp (hcl' _ _ y hyl hyr)
        have hV8 : wValue base w8 = wValue base w7 := by
          have hv7' : wValue base w7 = wValue base w3 := by
            rw [← hv6]; exact wValue_congr' base w7 w6 ht7 hv7
          rw [hv7']
          exact wValue_eq_of_taken base w3 w8 (by rw [h8v, hv7, h6v']) (fun y => y = l ∨ y = r)
            (fun y hy => by
              rw [h8tk y (hcl' _ _ y (fun h => hy (Or.inl h)) (fun h => hy (Or.inr h))), ht7, h6taken])
            hlrS
        have hq7 := hq.imp (fun hf => SegFits.of_agree (wNode c.p base w7) (wNode c.p base w8) c.i
          (c.p.fuel - 1) w7.top.rootKey (fun y hy => hag y (tReach_reachS _ _ _ _ hy))
          (by rw [← h8top]; exact hf)) id
        unfold wGet
        rw [hV8, h8top]
        rw [getFromR_avoid (wNode c.p base w7) (wNode c.p base w8) (wValue base w7) c.i c.p.fuel
          w7.top.rootKey (fun _ => False) (fun z zn hz hzn => hW7 z zn (reachS_tReach _ _ _ _ hz) hzn)
          (fun y hy _ => hag y hy) (fun _ _ _ _ _ _ _ h => h) key _ ReachS.root id]
        rw [hR7 hq7 key]
        show getFromR (updN (wNode c.p base w6) p ⟨(Nn (D + 1)).leaf, last.ks⟩) (wValue base w6) c.i
          c.p.fuel key w6.top.rootKey = _
        rw [hNp, hlasteq, hv6, h6top', hN3, h3top]
        refine getFromR_mergeOne N (updN (wNode c.p base w6) p last) (wValue base w3) c.i c.p.fuel root
          p l r m1 pn ln rn last ⟨!!xn.leaf, newKlongs c.i first⟩ (!xn.leaf) cL cR
          hT hp hpn hpleaf hpL hpR hclt hadj hln hrn hll' hrl' hlrange hrrange hrhead ?_ rfl ?_
          (updN_self _ _ _) (by rw [hleafl]; exact hpleaf) (hiffN rfl) ?_ hm1notR htimesN
          (newKlongs_times c.i first) htl hwfN (klongsWf_newKlongs c.i first) key
        · rw [updN_ne _ _ _ _ (Ne.symm hpm1)]
          simp only [wNode, h6taken, hm1T, Bool.false_eq_true, ↓reduceIte, hw6m1]
        · intro cc z
          rw [mrg_newKlongs_liveAt_iff _ c.i first (by rw [hfirst]; exact hndE) cc z, hfirst]
        · intro y hyp _ _ hym
          rw [updN_ne _ _ _ _ hyp]
          rcases Nat.lt_or_ge y m1 with hy | hy
          · exact hlow6 y hy
          · have hyw : wNode c.p base w6 y = none := by
              simp only [wNode, h6taken, (hfree y hy).2, Bool.false_eq_true, ↓reduceIte,
                h6old y (by omega) hym, hnone3 y hy, hbaseF y hy]
            rw [hyw, (hfree y hy).1]
      intro s7
      generalize hw7 : ({ ({ w6 with trail := s7 :: w6.trail } : W) with
        nodes := upsert w6.nodes p (mergeParentNode pn c.i il cL m1 ir cR none) } : W) = w7
      have h7n : w7.nodes = upsert w6.nodes p (mergeParentNode pn c.i il cL m1 ir cR none) := by rw [← hw7]
      have h7t : w7.taken = w6.taken := by rw [← hw7]
      have h7top : w7.top = w6.top := by rw [← hw7]
      have h7v : w7.vals = w6.vals := by rw [← hw7]
      have hlk7 : w7.nodes.lookup p = some (mergeParentNode pn c.i il cL m1 ir cR none) := by
        rw [h7n, lookup_upsert]; simp
      refine writerWP_mono (writerWP_mergeCleanup_frameV p m1 c.i c _ w7 _ (hne' _ _) hlk7
        (fun q hq c' hm => by
          rcases hchar1 c' q.1 hm with ⟨_, h⟩ | ⟨hold, h1, h2⟩
          · rcases hlr' _ _ q hq with h' | h' <;> rw [h'] at h
            · exact hlm1 h
            · exact hrm1 h
          · exact hnoOld q.1 (hlr' _ _ q hq) c' hold h1 h2)) ?_
      intro _ w8 ⟨h8top, _, h8v, h8t, h8l, pn8, h8p, h8leaf, h8times, h8iff⟩
      try simp only [writerWP_pure]
      have h8tc : ∀ y, y ≠ l → y ≠ r → w8.taken.contains y = w3.taken.contains y := by
        intro y hyl hyr; rw [h8t y (hcl' _ _ y hyl hyr), h7t, h6taken]
      have h8l' : ∀ y, y ≠ p → y ≠ l → y ≠ r → w8.nodes.lookup y = w6.nodes.lookup y := by
        intro y hyp hyl hyr; rw [h8l y hyp (hcl' _ _ y hyl hyr), h7n, lookup_upsert]; simp [hyp]
      have h8v' : w8.vals = w3.vals := by rw [h8v, h7v, h6v, h5v, h4v]
      have hV8 : wValue base w8 = wValue base w3 :=
        wValue_eq_of_taken base w3 w8 h8v' (fun y => y = l ∨ y = r)
          (fun y hy => h8tc y (fun h => hy (Or.inl h)) (fun h => hy (Or.inr h))) hlrS
      have hpt8 : ∀ s, Klong.time s ∈ pn8.ks → s ≤ c.i := h8times (by
        rw [mergeParentNode_eq]
        exact mpNode_times pn c.i il cL m1 ir cR none _ _ _ (hhtd _) hpt)
      intro _ key
      unfold wGet
      rw [hV8, h8top, h7top, h6top', hN3, h3top]
      refine getFromR_mergeOne N (wNode c.p base w8) (wValue base w3) c.i c.p.fuel root p l r m1 pn ln
        rn pn8 ⟨!!xn.leaf, newKlongs c.i first⟩ (!xn.leaf) cL cR
        hT hp hpn hpleaf hpL hpR hclt hadj hln hrn hll' hrl' hlrange hrrange hrhead ?_ rfl ?_ ?_
        (by rw [h8leaf, mrg_mergeParentNode_leaf]; exact hpleaf)
        (fun cc z => (h8iff cc z).trans (hparOne cc z)) ?_ hm1notR htimesN
        (newKlongs_times c.i first) hpt8 hwfN (klongsWf_newKlongs c.i first) key
      · simp only [wNode, h8tc m1 (Ne.symm hlm1) (Ne.symm hrm1), hm1T, Bool.false_eq_true, ↓reduceIte]
        rw [h8l' m1 (Ne.symm hpm1) (Ne.symm hlm1) (Ne.symm hrm1), hw6m1]
      · intro cc z
        rw [mrg_newKlongs_liveAt_iff _ c.i first (by rw [hfirst]; exact hndE) cc z, hfirst]
      · simp only [wNode, h8tc p hpl hpr, hpT, Bool.false_eq_true, ↓reduceIte, h8p]
      · intro y hyp hyl hyr hym
        rw [← hNw3 y]
        unfold wNode
        rw [h8tc y hyl hyr, h8l' y hyp hyl hyr, h6old y (hyx y hyl hyr) hym]
    | some ksg =>
      obtain ⟨ks2, g2⟩ := ksg
      rw [hsec] at hmkd
      have hE : (first ++ ks2).map Prod.snd = (ln.live ++ rn.live).map Prod.snd := by
        rw [splitMerged_map_snd _ _ _ first ks2 g2 hmkd, mergeList_map_snd, List.map_append]
      simp only [writerWP_bind, writerWP_pure, writerWP_get]
      refine writerWP_mono (writerWP_newKey_frame _ _ _ _ c w6) ?_
      intro m2 w7 ⟨hm2, h7n, h7t, h7top, h7next, h7v, h7p, _⟩
      have hm2' : m2 = m1 + 2 := by rw [hm2, h6next, h5next, hw4m1]
      subst hm2'
      try simp only [writerWP_bind, writerWP_pure, writerWP_get]
      refine writerWP_mono (writerWP_setMadeFor_frame _ _ c _) ?_
      intro _ w8 ⟨h8n, h8t, h8top, h8next, h8v, h8p⟩
      try simp only [writerWP_pure]
      have hw6m2 : w6.nodes.lookup (m1 + 2) = none := by
        rw [h6n, h5n, lookup_append_single_ne _ _ _ _ (by rw [hw4m1]; omega),
          hlk4 _ (by omega)]
        exact hnone3 _ (by omega)
      have h8l : ∀ y, w8.nodes.lookup y = (w6.nodes ++ [(m1 + 2,
          ({ leaf := !!xn.leaf, ks := newKlongs c.i ks2 } : KNode))]).lookup y := by
        intro y; rw [h8n, h7n, h6next, h5next, hw4m1]
      have hw8p : w8.nodes.lookup p = some pn := by
        rw [h8l, lookup_append_single_ne _ _ _ _ (by omega)]
        exact hw6p
      obtain ⟨yg, hE1, hgs, hE2⟩ := mrg_splitMerged_two (!xn.leaf) c.p.mergeMax hcap _ first ks2 g2 hmkd
      have hElen : c.p.mergeMax < (mergeList (!xn.leaf) cR ln.live rn.live).length := by
        rcases Nat.lt_or_ge c.p.mergeMax (mergeList (!xn.leaf) cR ln.live rn.live).length with h | h
        · exact h
        · exfalso
          unfold splitMerged at hmkd
          simp only [show (mergeList (!xn.leaf) cR ln.live rn.live).length ≤ c.p.mergeMax from h,
            ↓reduceIte, Prod.mk.injEq, reduceCtorEq, and_false] at hmkd
      have hlnL : ∀ q ∈ ln.live, q.1 < cR ∧ ((!xn.leaf) = true → q.1 = 0 ∨ cL < q.1) ∧
          ((!xn.leaf) = false → cL ≤ q.1) := by
        intro q hq
        have hq' : (q.1, q.2) ∈ ln.liveAt c.i := by rw [KNode.liveAt_of_times ln c.i hlt]; exact hq
        exact ⟨hlrange _ _ hq', hllow _ _ hq'⟩
      have hrnR : ∀ q ∈ rn.live, ((!xn.leaf) = true → q.1 = 0 ∨ cR < q.1) ∧
          ((!xn.leaf) = false → cR ≤ q.1) := by
        intro q hq
        have hq' : (q.1, q.2) ∈ rn.liveAt c.i := by rw [KNode.liveAt_of_times rn c.i hrt]; exact hq
        exact hrrange _ _ hq'
      obtain ⟨hgL, hg0, hgU0⟩ := mrg_two_g (!xn.leaf) cL cR ln.live rn.live
        (((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2) g2 yg hsortE (by omega) hgs
        hclt hlnL hrnR
      have hgU : ∀ k z, (k, z) ∈ pn.liveAt c.i → cR < k → g2 < k := by
        intro k z hk hkc
        apply hgU0 k hkc
        intro q hq
        have hq' : (q.1, q.2) ∈ rn.liveAt c.i := by rw [KNode.liveAt_of_times rn c.i hrt]; exact hq
        exact hrup k z hk hkc _ _ hq'
      have hnd1 : (first.map Prod.fst).Nodup := by
        rw [hE1]
        exact List.pairwise_map.mpr ((hsortE.sublist (List.take_sublist _ _)).imp
          (by intro a b hab; omega))
      have hsortD : CvSorted ((mergeList (!xn.leaf) cR ln.live rn.live).drop
          (((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2)) :=
        hsortE.sublist (List.drop_sublist _ _)
      have hnd2 : (ks2.map Prod.fst).Nodup := by
        rw [hE2]
        apply List.pairwise_map.mpr
        apply List.Pairwise.imp (R := fun a b : Nat × NodeId => a.1 < b.1)
          (by intro a b hab; omega)
        generalize hb : (!xn.leaf) = b at hsortD hgs ⊢
        cases b with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact hsortD
        | true =>
          simp only [↓reduceIte]
          apply renameHead_sorted 0 _ hsortD
          intro q hq
          cases hd : (mergeList true cR ln.live rn.live).drop
              (((mergeList true cR ln.live rn.live).length + 1) / 2) with
          | nil => rw [hd] at hq; simp at hq
          | cons a tl =>
            rw [hd] at hq hgs hsortD
            simp only [List.head?_cons, Option.some.injEq] at hgs
            subst hgs
            simp only [List.tail_cons] at hq
            have := (List.pairwise_cons.mp hsortD).1 q hq
            simp at this; omega
      refine writerWP_mergeParent_cases p pn (d - 1) il cL m1 ir cR (some (m1 + 2, g2)) c w8 _ hw8p ?_ ?_
      rotate_left
      · intro last compact s9 hlast
        rw [hd]
        have h8taken : w8.taken = w3.taken := by rw [h8t, h7t, h6taken]
        have h8nx : w8.next = m1 + 4 := by rw [h8next, h7next, h6next, h5next, hw4m1]
        have h8old : ∀ y, y ≠ x → y ≠ m1 → y ≠ m1 + 2 → w8.nodes.lookup y = w3.nodes.lookup y := by
          intro y hyx hym hym2
          rw [h8l, lookup_append_single_ne _ _ _ _ hym2, h6old y hyx hym]
        have hw8m1 : w8.nodes.lookup m1 = some ⟨!!xn.leaf, newKlongs c.i first⟩ := by
          rw [h8l, lookup_append_single_ne _ _ _ _ (by omega)]; exact hw6m1
        have hw8m2 : w8.nodes.lookup (m1 + 2) = some ⟨!!xn.leaf, newKlongs c.i ks2⟩ := by
          rw [h8l, lookup_append_single_self _ _ _ hw6m2]
        have hw8w4 : ∀ y, y ≠ m1 → y ≠ m1 + 2 → wNode c.p base w8 y = wNode c.p base w4 y := by
          intro y hym hym2
          unfold wNode
          rw [h8taken, ← h4t, h8l, lookup_append_single_ne _ _ _ _ hym2, h6n, h5n,
            lookup_append_single_ne _ _ _ _ (by rw [hw4m1]; exact hym)]
        have hlow8 : ∀ y, y < m1 → wNode c.p base w8 y = N y := by
          intro y hy
          rw [hw8w4 y (by omega) (by omega), hr4.1, ← hN3]; rfl
        have hE' : ∀ q ∈ first ++ ks2, ∃ q' ∈ ln.live ++ rn.live, q'.2 = q.2 := by
          intro q hq
          have : q.2 ∈ (ln.live ++ rn.live).map Prod.snd := by
            rw [← hE]; exact List.mem_map.mpr ⟨q, hq, rfl⟩
          obtain ⟨q', hq', he⟩ := List.mem_map.mp this
          exact ⟨q', hq', he⟩
        have hnew8 : ∀ y yn, m1 ≤ y → w8.nodes.lookup y = some yn → ∀ c' z, (c', z) ∈ yn.liveAt c.i →
            z < m1 := by
          intro y yn hy hyn c' z hz
          by_cases hym : y = m1
          · rw [hym, hw8m1] at hyn
            cases hyn
            have hm := liveAt_newKlongs_mem _ c.i c.i first c' z hz
            exact hchild z (hsnd z (first ++ ks2) hE' c' (List.mem_append_left _ hm))
          · by_cases hym2 : y = m1 + 2
            · rw [hym2, hw8m2] at hyn
              cases hyn
              have hm := liveAt_newKlongs_mem _ c.i c.i ks2 c' z hz
              exact hchild z (hsnd z (first ++ ks2) hE' c' (List.mem_append_right _ hm))
            · rw [h8old y (by omega) hym hym2, hnone3 y hy] at hyn; cases hyn
        have hhigh8 : ∀ y, w8.next ≤ y → w8.nodes.lookup y = none := by
          intro y hy
          rw [h8old y (by omega) (by omega) (by omega), hnone3 y (by omega)]
        obtain ⟨h8S2, h8T, h8S4, h8S5, h8S6, h8R0⟩ := mergeState_facts c base N root m1 w3 w8 s D X Nn
          hT h3top hfree hlinksAll hbaseF hS2 hS4 hR0
          (fun i h1 h2 => h8old _ (hXx i h1 h2) (by have := hXlt i h1 h2; omega)
            (by have := hXlt i h1 h2; omega)) h8taken
          (by rw [h8top, h7top, h6top, h5top, h4top]) (by omega) hlow8 hnew8 hhigh8
        have h8top' : w8.top.rootKey = root := by rw [h8top, h7top, h6top']
        have hm2N : N (m1 + 2) = none := (hfree _ (by omega)).1
        have hm2T : w3.taken.contains (m1 + 2) = false := (hfree _ (by omega)).2
        have hV8 : ∀ last, mergeFullLast pn c.i cL m1 cR (some (m1 + 2, g2)) = some last →
            TreeOK (updN (wNode c.p base w8) p ⟨pn.leaf, last.ks⟩) c.i w8.top.rootKey ∧
            (∀ z, TReach (updN (wNode c.p base w8) p ⟨pn.leaf, last.ks⟩) c.i w8.top.rootKey z →
              z ≠ l ∧ z ≠ r) ∧
            ∀ c' z, (c', z) ∈ (⟨pn.leaf, last.ks⟩ : KNode).liveAt c.i → z < w8.next := by
          intro last hlast
          obtain ⟨_, hleafl, _, hsomeL⟩ := mergeFullLast_liveAt pn c.i cL m1 cR _ last hlast hpt
          have hlasteq : (⟨pn.leaf, last.ks⟩ : KNode) = last := by
            cases last with
            | mk lf ks => simp only at hleafl; rw [hleafl]
          rw [hlasteq, h8top']
          have hVp : updN (wNode c.p base w8) p last p = some last := updN_self _ _ _
          have hVm1 : updN (wNode c.p base w8) p last m1 = some ⟨!!xn.leaf, newKlongs c.i first⟩ := by
            rw [updN_ne _ _ _ _ (Ne.symm hpm1)]
            simp only [wNode, h8taken, hm1T, Bool.false_eq_true, ↓reduceIte, hw8m1]
          have hVm2 : updN (wNode c.p base w8) p last (m1 + 2) = some ⟨!!xn.leaf, newKlongs c.i ks2⟩ := by
            rw [updN_ne _ _ _ _ (by omega)]
            simp only [wNode, h8taken, hm2T, Bool.false_eq_true, ↓reduceIte, hw8m2]
          have hVN : ∀ y, y ≠ p → y ≠ m1 → y ≠ m1 + 2 → updN (wNode c.p base w8) p last y = N y := by
            intro y hyp hym hym2
            rw [updN_ne _ _ _ _ hyp]
            rcases Nat.lt_or_ge y m1 with hy | hy
            · exact hlow8 y hy
            · have hyw : wNode c.p base w8 y = none := by
                simp only [wNode, h8taken, (hfree y hy).2, Bool.false_eq_true, ↓reduceIte,
                  h8old y (by omega) hym hym2, hnone3 y hy, hbaseF y hy]
              rw [hyw, (hfree y hy).1]
          refine ⟨treeOK_mergeTwoAfter N _ c.i root p l r m1 (m1 + 2) pn ln rn last
            ⟨!!xn.leaf, newKlongs c.i first⟩ ⟨!!xn.leaf, newKlongs c.i ks2⟩ cL cR g2 first ks2
            hT hp hpn hpL hpR hc hln hrn hlt hrt hm1N (hfreshT m1 (Nat.le_refl _))
            hm2N (hfreshT _ (by omega)) (by omega) hE hVm1
            (fun cc z hm => liveAt_newKlongs_mem (!!xn.leaf) c.i c.i first cc z hm) hVm2
            (fun cc z hm => liveAt_newKlongs_mem (!!xn.leaf) c.i c.i ks2 cc z hm) hVp
            (hsomeL (m1 + 2) g2 rfl) (fun y hyp _ _ hym hym2 => hVN y hyp hym hym2),
            fun z hz => ?_, fun c' z hm => ?_⟩
          · have := mergeV_reach N _ c.i root p l r m1 (some (m1 + 2)) pn ln rn last cL cR hT hp hpn hpL
              hpR hln hrn hVp
              (fun cc z hm => by
                rcases hsomeL (m1 + 2) g2 rfl cc z hm with ⟨_, h⟩ | ⟨_, h⟩ | h
                · exact Or.inl h
                · exact Or.inr (Or.inl (by rw [h]))
                · exact Or.inr (Or.inr h))
              (fun m mn hm hmn' cc z hz => by
                have hmem : (cc, z) ∈ first ++ ks2 := by
                  rcases hm with hm | hm
                  · rw [hm, hVm1] at hmn'
                    cases hmn'
                    exact List.mem_append_left _ (liveAt_newKlongs_mem _ c.i c.i first cc z hz)
                  · simp only [Option.some.injEq] at hm
                    rw [hm, hVm2] at hmn'
                    cases hmn'
                    exact List.mem_append_right _ (liveAt_newKlongs_mem _ c.i c.i ks2 cc z hz)
                rcases hsnd z (first ++ ks2) hE' cc hmem with ⟨c0, h0⟩ | ⟨c0, h0⟩
                · exact Or.inl ⟨c0, by rw [KNode.liveAt_of_times ln c.i hlt]; exact h0⟩
                · exact Or.inr ⟨c0, by rw [KNode.liveAt_of_times rn c.i hrt]; exact h0⟩)
              (fun y hyp _ _ hym hym2 => hVN y hyp hym (fun h => hym2 (by rw [h])))
              hm1R (fun m hm => by
                simp only [Option.some.injEq] at hm
                rw [hm]; exact not_reach_fresh N c.i root _ hT hm2N (hfreshT _ (by omega))) z hz
            exact ⟨this.2.1, this.2.2⟩
          · rcases hsomeL (m1 + 2) g2 rfl c' z hm with ⟨_, h⟩ | ⟨_, h⟩ | ⟨h, _, _⟩
            · omega
            · omega
            · have := hlinksAll p c' z ⟨pn, hpn, h⟩; omega
        obtain ⟨hVt, _, hvx⟩ := hV8 last hlast
        obtain ⟨htl, hleafl, _, _⟩ := mergeFullLast_liveAt pn c.i cL m1 cR _ last hlast hpt
        obtain ⟨_, hiffS⟩ := mergeFullLast_iff pn c.i cL m1 cR _ last hlast hpt
        obtain ⟨pairsL, hksL⟩ := mergeFullLast_ks pn c.i cL m1 cR _ last hlast
        have hlwf : klongsWf last.ks = true := by rw [hksL]; exact klongsWf_newKlongs c.i pairsL
        have hlasteq : (⟨pn.leaf, last.ks⟩ : KNode) = last := by
          cases last with
          | mk lf ks => simp only at hleafl; rw [hleafl]
        have hcs : (!compact && decide (last.size > c.p.splitAbove)) = false := by
          have := hnospace m1 _ last hlast
          cases compact <;> simp <;> omega
        have h8v' : w8.vals = w3.vals := by rw [h8v, h7v, h6v, h5v, h4v]
        have hv8 : wValue base w8 = wValue base w3 := wValue_congr' base w8 w3 h8taken h8v'
        have hW8 : ∀ z zn, wNode c.p base w8 z = some zn → klongsWf zn.ks = true := by
          intro z zn hz
          rcases Nat.lt_or_ge z m1 with h | h
          · rw [hlow8 z h] at hz; exact hwfN z zn hz
          · by_cases hzm : z = m1
            · rw [hzm] at hz
              simp only [wNode, h8taken, hm1T, Bool.false_eq_true, ↓reduceIte, hw8m1] at hz
              cases hz; exact klongsWf_newKlongs c.i first
            · by_cases hzm2 : z = m1 + 2
              · rw [hzm2] at hz
                simp only [wNode, h8taken, hm2T, Bool.false_eq_true, ↓reduceIte, hw8m2] at hz
                cases hz; exact klongsWf_newKlongs c.i ks2
              · simp only [wNode, h8taken, (hfree z h).2, Bool.false_eq_true, ↓reduceIte,
                  h8old z (by omega) hzm hzm2, hnone3 z h, hbaseF z h] at hz
                cases hz
        have hVal8 : ∀ z, (w8.next ≤ z ∨ ∃ i, s ≤ i ∧ i ≤ D + 1 ∧ z = X i) → wValue base w8 z = none := by
          intro z hz
          rw [hv8]
          rcases hz with hz | ⟨i, h1, h2, h3⟩
          · exact hfreshV z (by omega)
          · rw [h3]
            obtain ⟨hl3, ht3⟩ := hS2 i h1 h2
            exact hnoval _ (Nn i) (by rw [← hNw3]; simp only [wNode, ht3, Bool.false_eq_true, ↓reduceIte, hl3])
        have htime := writerWP_handleFull_timeV c base w3.path s D X K Nn hsD hX hK hlinkK hrange hlen
          hwf htimes htop hdist hspace last compact ({ w8 with trail := s9 :: w8.trail } : W)
          (by rw [hNp]; exact hpfirst) hcs hql (by show w8.path = w3.path; rw [h8p, h7p, h6p, h5p, h4p])
          h8S2 h8T h8S4 h8S5 h8S6 (fun h0 _ => h8R0 h0) hW8 hVal8 (by rw [hXp, hNp]; exact hVt)
          (by rw [hNp]; exact hvx) hlwf htl
        rw [hXp] at htime
        have hbr := writerWP_mergeFull_branch c base w3.path s D X K Nn hsD hX hK hlinkK hrange hlen hwf
          htimes htop hdist p l r m1 (some (m1 + 2, g2)) pn cL cR hXp hNp (hhalves m1 (some (m1 + 2, g2)))
          w8 (by rw [h8p, h7p, h6p, h5p, h4p]) h8S2 h8T h8S4 h8S5 h8S6 h8R0 hV8
          ⟨by omega, by omega⟩ last compact s9 hlast
        refine writerWP_mono (writerWP_and htime hbr) ?_
        rintro _ w11 ⟨⟨hxR11, hW11, hR11⟩, hT11, hl11, hr11, ht11, hv11⟩
        refine writerWP_mono (writerWP_mergeCleanup_wNode p m1 c base hvc _ w11 (hne' _ _)
          (by rw [ht11, h8taken]; exact hpT)) ?_
        rintro _ w12 ⟨h12top, _, h12v, h12tk, h12l, _, _⟩
        try simp only [writerWP_pure]
        intro hq key
        have hag : ∀ y, ReachS (wNode c.p base w11) c.i w11.top.rootKey y →
            wNode c.p base w12 y = wNode c.p base w11 y := by
          intro y hy
          have hyT := reachS_tReach _ _ _ _ hy
          have hyp : y ≠ p := fun he => hxR11 (by rw [← he]; exact hyT)
          have hyl : y ≠ l := fun he => hl11 (by rw [← he]; exact hyT)
          have hyr : y ≠ r := fun he => hr11 (by rw [← he]; exact hyT)
          exact h12l y hyp (hcl' _ _ y hyl hyr)
        have hV12 : wValue base w12 = wValue base w11 := by
          have hv11' : wValue base w11 = wValue base w3 := by
            rw [← hv8]; exact wValue_congr' base w11 w8 ht11 hv11
          rw [hv11']
          exact wValue_eq_of_taken base w3 w12 (by rw [h12v, hv11, h8v']) (fun y => y = l ∨ y = r)
            (fun y hy => by
              rw [h12tk y (hcl' _ _ y (fun h => hy (Or.inl h)) (fun h => hy (Or.inr h))), ht11, h8taken])
            hlrS
        have hq11 := hq.imp (fun hf => SegFits.of_agree (wNode c.p base w11) (wNode c.p base w12) c.i
          (c.p.fuel - 1) w11.top.rootKey (fun y hy => hag y (tReach_reachS _ _ _ _ hy))
          (by rw [← h12top]; exact hf)) id
        unfold wGet
        rw [hV12, h12top]
        rw [getFromR_avoid (wNode c.p base w11) (wNode c.p base w12) (wValue base w11) c.i c.p.fuel
          w11.top.rootKey (fun _ => False) (fun z zn hz hzn => hW11 z zn (reachS_tReach _ _ _ _ hz) hzn)
          (fun y hy _ => hag y hy) (fun _ _ _ _ _ _ _ h => h) key _ ReachS.root id]
        rw [hR11 hq11 key]
        show getFromR (updN (wNode c.p base w8) p ⟨(Nn (D + 1)).leaf, last.ks⟩) (wValue base w8) c.i
          c.p.fuel key w8.top.rootKey = _
        rw [hNp, hlasteq, hv8, h8top', hN3, h3top]
        refine getFromR_mergeTwo N (updN (wNode c.p base w8) p last) (wValue base w3) c.i c.p.fuel root
          p l r m1 (m1 + 2) (m1 + 2 + 2) pn ln rn last
          ⟨!!xn.leaf, newKlongs c.i first⟩ ⟨!!xn.leaf, newKlongs c.i ks2⟩ (!xn.leaf) cL cR
          (((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2) g2 yg
          hT hp hpn hpleaf hpL hpR hclt hadj hln hrn hll' hrl' hlrange hrrange hrhead hgs hgL hgU
          ?_ rfl ?_ ?_ rfl ?_ (updN_self _ _ _) (by rw [hleafl]; exact hpleaf)
          (hiffS (m1 + 2) g2 rfl) ?_ ?_ (by omega) (by omega)
          htimesN hwfN (newKlongs_times c.i first) (newKlongs_times c.i ks2) htl
          (klongsWf_newKlongs c.i first) (klongsWf_newKlongs c.i ks2) key
        · rw [updN_ne _ _ _ _ (Ne.symm hpm1)]
          simp only [wNode, h8taken, hm1T, Bool.false_eq_true, ↓reduceIte, hw8m1]
        · intro cc z
          rw [mrg_newKlongs_liveAt_iff _ c.i first hnd1 cc z, hE1]
        · rw [updN_ne _ _ _ _ (by omega)]
          simp only [wNode, h8taken, hm2T, Bool.false_eq_true, ↓reduceIte, hw8m2]
        · intro cc z
          rw [mrg_newKlongs_liveAt_iff _ c.i ks2 hnd2 cc z, hE2]
        · intro y hyp _ _ hym hym2
          rw [updN_ne _ _ _ _ hyp]
          rcases Nat.lt_or_ge y m1 with hy | hy
          · exact hlow8 y hy
          · have hyw : wNode c.p base w8 y = none := by
              simp only [wNode, h8taken, (hfree y hy).2, Bool.false_eq_true, ↓reduceIte,
                h8old y (by omega) hym hym2, hnone3 y hy, hbaseF y hy]
            rw [hyw, (hfree y hy).1]
        · intro z hz
          have hzn : m1 ≤ z := by rcases hz with hz | hz | hz <;> omega
          exact ⟨(hfree z hzn).1, hfreshT z hzn⟩
      intro s9
      generalize hw9 : ({ ({ w8 with trail := s9 :: w8.trail } : W) with
        nodes := upsert w8.nodes p (mergeParentNode pn c.i il cL m1 ir cR (some (m1 + 2, g2))) } : W) = w9
      have h9n : w9.nodes = upsert w8.nodes p (mergeParentNode pn c.i il cL m1 ir cR (some (m1 + 2, g2))) := by
        rw [← hw9]
      have h9t : w9.taken = w8.taken := by rw [← hw9]
      have h9top : w9.top = w8.top := by rw [← hw9]
      have h9v : w9.vals = w8.vals := by rw [← hw9]
      have hlk9 : w9.nodes.lookup p = some (mergeParentNode pn c.i il cL m1 ir cR (some (m1 + 2, g2))) := by
        rw [h9n, lookup_upsert]; simp
      refine writerWP_mono (writerWP_mergeCleanup_frameV p m1 c.i c _ w9 _ (hne' _ _) hlk9
        (fun q hq c' hm => by
          rcases hchar2 (m1 + 2) g2 c' q.1 hm with ⟨_, h⟩ | ⟨_, h⟩ | ⟨hold, h1, h2⟩
          · rcases hlr' _ _ q hq with h' | h' <;> rw [h'] at h
            · exact hlm1 h
            · exact hrm1 h
          · rcases hlr' _ _ q hq with h' | h' <;> rw [h'] at h <;> omega
          · exact hnoOld q.1 (hlr' _ _ q hq) c' hold h1 h2)) ?_
      intro _ w10 ⟨h10top, _, h10v, h10t, h10l, pn10, h10p, h10leaf, h10times, h10iff⟩
      try simp only [writerWP_pure]
      have h10tc : ∀ y, y ≠ l → y ≠ r → w10.taken.contains y = w3.taken.contains y := by
        intro y hyl hyr; rw [h10t y (hcl' _ _ y hyl hyr), h9t, h8t, h7t, h6taken]
      have h10l' : ∀ y, y ≠ p → y ≠ l → y ≠ r → w10.nodes.lookup y = w8.nodes.lookup y := by
        intro y hyp hyl hyr; rw [h10l y hyp (hcl' _ _ y hyl hyr), h9n, lookup_upsert]; simp [hyp]
      have hm2T : w3.taken.contains (m1 + 2) = false := (hfree _ (by omega)).2
      have h10v' : w10.vals = w3.vals := by rw [h10v, h9v, h8v, h7v, h6v, h5v, h4v]
      have hV10 : wValue base w10 = wValue base w3 :=
        wValue_eq_of_taken base w3 w10 h10v' (fun y => y = l ∨ y = r)
          (fun y hy => h10tc y (fun h => hy (Or.inl h)) (fun h => hy (Or.inr h))) hlrS
      have hpt10 : ∀ s, Klong.time s ∈ pn10.ks → s ≤ c.i := h10times (by
        rw [mergeParentNode_eq]
        exact mpNode_times pn c.i il cL m1 ir cR (some (m1 + 2, g2)) _ _ _ (hhtd _) hpt)
      intro _ key
      unfold wGet
      rw [hV10, h10top, h9top, h8top, h7top, h6top', hN3, h3top]
      refine getFromR_mergeTwo N (wNode c.p base w10) (wValue base w3) c.i c.p.fuel root p l r m1
        (m1 + 2) (m1 + 2 + 2) pn ln rn pn10
        ⟨!!xn.leaf, newKlongs c.i first⟩ ⟨!!xn.leaf, newKlongs c.i ks2⟩ (!xn.leaf) cL cR
        (((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2) g2 yg
        hT hp hpn hpleaf hpL hpR hclt hadj hln hrn hll' hrl' hlrange hrrange hrhead hgs hgL hgU
        ?_ rfl ?_ ?_ rfl ?_ ?_ (by rw [h10leaf, mrg_mergeParentNode_leaf]; exact hpleaf)
        (fun cc z => (h10iff cc z).trans (hparTwo (m1 + 2) g2 cc z)) ?_ ?_ (by omega) (by omega)
        htimesN hwfN (newKlongs_times c.i first) (newKlongs_times c.i ks2) hpt10
        (klongsWf_newKlongs c.i first) (klongsWf_newKlongs c.i ks2) key
      · simp only [wNode, h10tc m1 (Ne.symm hlm1) (Ne.symm hrm1), hm1T, Bool.false_eq_true, ↓reduceIte]
        rw [h10l' m1 (Ne.symm hpm1) (Ne.symm hlm1) (Ne.symm hrm1), h8l,
          lookup_append_single_ne _ _ _ _ (by omega), hw6m1]
      · intro cc z
        rw [mrg_newKlongs_liveAt_iff _ c.i first hnd1 cc z, hE1]
      · simp only [wNode, h10tc (m1 + 2) (by omega) (by omega), hm2T, Bool.false_eq_true, ↓reduceIte]
        rw [h10l' _ (by omega) (by omega) (by omega), h8l, lookup_append_single_self _ _ _ hw6m2]
      · intro cc z
        rw [mrg_newKlongs_liveAt_iff _ c.i ks2 hnd2 cc z, hE2]
      · simp only [wNode, h10tc p hpl hpr, hpT, Bool.false_eq_true, ↓reduceIte, h10p]
      · intro y hyp hyl hyr hym hym2
        rw [← hNw3 y]
        unfold wNode
        rw [h10tc y hyl hyr, h10l' y hyp hyl hyr, h8l, lookup_append_single_ne _ _ _ _ hym2,
          h6old y (hyx y hyl hyr) hym]
      · intro z hz
        have hzn : m1 ≤ z := by rcases hz with hz | hz | hz <;> omega
        exact ⟨(hfree z hzn).1, hfreshT z hzn⟩

/-- The writer's merge keeps the reading of every key with the parent full or
with room (`writerWP_merge_made_get` without its room premises): a full parent,
which existed before the transaction, below an inner node, its last version not
space split (`hnospace`), is split in time with the cascade above it
(`writerWP_mergeTail_full_get`); the reading holds when the state after fits the
fuel or the space root does not space split. -/
theorem writerWP_merge_full_get (x : NodeId) (d : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (w : W)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hpar : ∀ p, (w.path[d - 1]?).map (·.2) = some p →
      TReach (wNode c.p base w) c.i w.top.rootKey p ∧ ∃ pn, wNode c.p base w p = some pn ∧
        pn.leaf = false ∧ klongsWf pn.ks = true ∧ (∀ s, Klong.time s ∈ pn.ks → s ≤ c.i) ∧
        ∀ cc z zn, (cc, z) ∈ pn.liveAt c.i → wNode c.p base w z = some zn →
          ∀ s, Klong.time s ∈ zn.ks → s ≤ c.i)
    (hRt : ∀ y, TReach (wNode c.p base w) c.i w.top.rootKey y → w.taken.contains y = false)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next))
    (hbaseF : ∀ z, w.next ≤ z → knodeOf c.p base z = none)
    (hfreshT : ∀ z, w.next ≤ z → ∀ u c', TReach (wNode c.p base w) c.i w.top.rootKey u →
      ¬ TLink (wNode c.p base w) c.i u c' z)
    (hR : RangeOrder (wNode c.p base w) c.i w.top.rootKey) (hcap : 1 ≤ c.p.mergeMax)
    (htimesN : ∀ y yn, wNode c.p base w y = some yn → ∀ s, Klong.time s ∈ yn.ks → s ≤ c.i)
    (hwfN : ∀ y yn, wNode c.p base w y = some yn → klongsWf yn.ks = true)
    (hnoval : ∀ y yn, wNode c.p base w y = some yn → wValue base w y = none)
    (hlinksAll : ∀ u c' z, TLink (wNode c.p base w) c.i u c' z → z < w.next)
    (hfreshV : ∀ z, w.next ≤ z → wValue base w z = none)
    (s D : Nat) (X : Nat → NodeId) (K : Nat → Nat) (Nn : Nat → KNode) (hsD : s ≤ D)
    (hd : d - 1 = D + 1)
    (hX : ∀ i, s ≤ i → i ≤ D + 1 → (w.path[i]?).map (·.2) = some (X i))
    (hK : ∀ i, s < i → i ≤ D + 1 → w.path[i]? = some (some (K i), X i))
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
    (hS2 : ∀ i, s ≤ i → i ≤ D + 1 →
      w.nodes.lookup (X i) = some (Nn i) ∧ w.taken.contains (X i) = false)
    (hS4 : ∀ i, s ≤ i → i ≤ D + 1 → TReach (wNode c.p base w) c.i w.top.rootKey (X i))
    (hR0 : s = 0 → w.top.rootKey = X 0)
    (hXx : ∀ i, s ≤ i → i ≤ D + 1 → X i ≠ x)
    (hhalves : ∀ cL cR m1 m2 last, mergeFullLast (Nn (D + 1)) c.i cL m1 cR m2 = some last →
      c.p.splitAbove < last.size → ∃ r0 : Nat, 0 < r0 ∧
      (halves (Nn (D + 1)).leaf c.i last []).2.2 = r0 ∧
      (∀ c' z, (c', z) ∈ (halves (Nn (D + 1)).leaf c.i last []).1.liveAt c.i → c' < r0 ∧
        (c', z) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i) ∧
      (∀ c' z, (c', z) ∈ (halves (Nn (D + 1)).leaf c.i last []).2.1.liveAt c.i → ∃ c0, r0 ≤ c0 ∧
        c' = splitLocalCv (Nn (D + 1)).leaf r0 c0 ∧
        (c0, z) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i) ∧
      ((Nn D).leaf = false →
        K (D + 1) ≤ r0 ∧ ∀ c'' z', (c'', z') ∈ (Nn D).live → K (D + 1) < c'' → r0 < c''))
    (hpfirst : (Nn (D + 1)).firstTime ≠ some c.i) (hql : (Nn D).leaf = false)
    (hnospace : ∀ cL cR m1 m2 last, mergeFullLast (Nn (D + 1)) c.i cL m1 cR m2 = some last →
      last.size ≤ c.p.splitAbove) :
    WriterWP (merge x d) c w (fun _ w' =>
      (SegFits (wNode c.p base w') c.i (c.p.fuel - 1) w'.top.rootKey ∨
          ¬ (s = 0 ∧ ¬ ChainRoom c (Nn 0) ∧ c.p.splitAbove < ((Nn 0).lastVersion c.i).size)) →
      ∀ key, wGet c.p c.i base w' key = wGet c.p c.i base w key) := by
  obtain ⟨hidn, hidv, hidt⟩ := hids
  have hfree : ∀ z, w.next ≤ z → wNode c.p base w z = none ∧ w.taken.contains z = false := by
    intro z hz
    have htz : w.taken.contains z = false := by
      cases h' : w.taken.contains z with
      | false => rfl
      | true => have := hidt z h'; omega
    have hnz : w.nodes.lookup z = none := by
      cases h' : w.nodes.lookup z with
      | none => rfl
      | some _ => have := hidn z (by rw [h']; rfl); omega
    exact ⟨by simp only [wNode, htz, Bool.false_eq_true, ↓reduceIte, hnz, hbaseF z hz], htz⟩
  unfold merge
  simp only [writerWP_bind, writerWP_read]
  unfold pathNode
  simp only [writerWP_bind, writerWP_get]
  split
  · rename_i e he
    simp only [writerWP_pure]
    obtain ⟨hpR, pn0, hpn0, hpleaf, hpwf, hpt, hch⟩ := hpar e.2 (by rw [he]; rfl)
    have hXp : X (D + 1) = e.2 := by
      have h1 : (w.path[d - 1]?).map (·.2) = some (X (D + 1)) := by
        rw [hd]; exact hX (D + 1) (by omega) (Nat.le_refl _)
      rw [he] at h1
      simp only [Option.map_some, Option.some.injEq] at h1
      exact h1.symm
    refine writerWP_mono (writerWP_and (writerWP_getNode_all e.2 c w base hvc)
      (writerWP_getNode_cache e.2 c w)) ?_
    intro pn w1 ⟨⟨hr1, hlk1, hwn1, hpre1, hsrc1⟩, _, _, hp1⟩
    rw [hwn1 (hRt _ hpR)] at hpn0
    cases hpn0
    -- the tail from any state that reads as w
    have hpn : wNode c.p base w e.2 = some pn0 := hwn1 (hRt _ hpR)
    have hpRS := tReach_reachS _ c.i _ _ hpR
    have tailOK : ∀ (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId)
        (rn : KNode) (ir cL cR : Nat) (xn : KNode) (w3 : W), ReadsAs c.p base w w3 →
        w1.nodes <+: w3.nodes → (∀ z, (w3.nodes.lookup z).isSome = true → z < w.next) →
        w3.path = w.path →
        pn0.ks[il]? = some (.key cL l) → LastLive pn0.ks pn0.lastBitmap il cL →
        pn0.ks[ir]? = some (.key cR r) → LastLive pn0.ks pn0.lastBitmap ir cR → cL < cR →
        (∀ cc z, (cc, z) ∈ pn0.liveAt c.i → cc ≤ cL ∨ cR ≤ cc) →
        ln.leaf = xn.leaf → rn.leaf = xn.leaf →
        (x = l ∨ x = r) → wNode c.p base w l = some ln → wNode c.p base w r = some rn →
        WriterWP (mergeTail c x d e.2 pn0 xn leftSome l ln il r rn ir) c w3
          (fun _ w' => (SegFits (wNode c.p base w') c.i (c.p.fuel - 1) w'.top.rootKey ∨
            ¬ (s = 0 ∧ ¬ ChainRoom c (Nn 0) ∧ c.p.splitAbove < ((Nn 0).lastVersion c.i).size)) →
            ∀ key, wGet c.p c.i base w' key = wGet c.p c.i base w key) := by
      intro leftSome l ln il r rn ir cL cR xn w3 hr3 hpre3 hsrc3 hp3 hL hLL hR' hRL hclt hadj hll hrl
        hxlr hln hrn
      have hNp : Nn (D + 1) = pn0 := by
        have h1 := (hS2 (D + 1) (by omega) (Nat.le_refl _)).1
        rw [hXp] at h1
        have h2 := lookup_of_prefix _ _ hpre1 _ _ h1
        rw [hlk1] at h2
        exact (Option.some.inj h2).symm
      have hmemL : (cL, l) ∈ pn0.liveAt c.i := by
        rw [KNode.liveAt_of_times pn0 c.i hpt]
        apply mem_of_lookup_nodup
        rw [KNode.live_lookup]
        exact keyLookup_of_last _ _ _ il l hL hLL
      have hmemR : (cR, r) ∈ pn0.liveAt c.i := by
        rw [KNode.liveAt_of_times pn0 c.i hpt]
        apply mem_of_lookup_nodup
        rw [KNode.live_lookup]
        exact keyLookup_of_last _ _ _ ir r hR' hRL
      obtain ⟨hlr1, hlr2⟩ := mrg_child_range (wNode c.p base w) c.i w.top.rootKey hR e.2 pn0 hpRS hpn
        hpleaf cL l ln hmemL hln
      obtain ⟨hrr1, hrr2⟩ := mrg_child_range (wNode c.p base w) c.i w.top.rootKey hR e.2 pn0 hpRS hpn
        hpleaf cR r rn hmemR hrn
      refine writerWP_mono (writerWP_mergeTail_full_get c base x d e.2 pn0 xn leftSome l ln il r rn ir cL cR
        (wNode c.p base w) w.top.rootKey w.next w3 hT hpR hpn hL hLL hR' hRL (by omega) hxlr
        hln hrn hpwf hpt hch hr3.1 (by rw [hr3.2.1]) hr3.2.2.2.2
        (lookup_of_prefix _ _ hpre3 _ _ hlk1) hsrc3
        (fun z hz => ⟨(hfree z hz).1, by rw [hr3.2.2.1]; exact (hfree z hz).2⟩) hfreshT
        hpleaf hclt hcap hadj hll hrl
        (fun cc z h => hlr2 cR r hmemR hclt cc z h)
        (by
          intro cc z h
          have h1 := hlr1 cc z h
          rw [hll] at h1
          constructor
          · intro hin
            have hxl : xn.leaf = false := by simpa using hin
            rcases (h1.2 hxl) with h0 | h0
            · exact Or.inl h0
            · rcases Nat.eq_zero_or_pos cL with hc0 | hc0
              · rcases Nat.eq_zero_or_pos cc with hcc | hcc
                · exact Or.inl hcc
                · exact Or.inr (by omega)
              · exact Or.inr (h0 hc0)
          · intro hin
            have hxl : xn.leaf = true := by simpa using hin
            rcases Nat.eq_zero_or_pos cL with hc0 | hc0
            · omega
            · exact h1.1 hxl hc0)
        (by
          intro cc z h
          have h1 := hrr1 cc z h
          rw [hrl] at h1
          constructor
          · intro hin
            have hxl : xn.leaf = false := by simpa using hin
            rcases (h1.2 hxl) with h0 | h0
            · exact Or.inl h0
            · exact Or.inr (h0 (by omega))
          · intro hin
            have hxl : xn.leaf = true := by simpa using hin
            exact h1.1 hxl (by omega))
        (fun k z hk hkc cc z' h => hrr2 k z hk hkc cc z' h)
        htimesN hwfN (fun y yn hy => by
          rw [wValue_congr' base w3 w hr3.2.2.1 hr3.2.2.2.1]; exact hnoval y yn hy)
        hvc hlinksAll hbaseF
        (fun z hz => by rw [wValue_congr' base w3 w hr3.2.2.1 hr3.2.2.2.1]; exact hfreshV z hz)
        s D X K Nn hsD hd (by rw [hp3]; exact hX) (by rw [hp3]; exact hK) hlinkK hrange hlen hwf htimes
        htop hdist hspace hXp hNp
        (fun i h1 h2 => ⟨lookup_of_prefix _ _ (hpre1.trans hpre3) _ _ (hS2 i h1 h2).1,
          by rw [hr3.2.2.1]; exact (hS2 i h1 h2).2⟩)
        hS4 hR0 hXx (fun m1 m2 last h => hhalves cL cR m1 m2 last (by rw [hNp]; exact h))
        (by rw [← hNp]; exact hpfirst) hql
        (fun m1 m2 last h => hnospace cL cR m1 m2 last (by rw [hNp]; exact h))) ?_
      intro _ w' h hq key
      rw [h hq key]
      unfold wGet
      rw [hr3.1, hr3.2.1, wValue_congr' base w3 w hr3.2.2.1 hr3.2.2.2.1]
    -- a klong of p that is the last live one of its compare value names a reached node
    have hchild : ∀ i cv y, pn0.ks[i]? = some (.key cv y) → LastLive pn0.ks pn0.lastBitmap i cv →
        (cv, y) ∈ pn0.liveAt c.i ∧ TReach (wNode c.p base w) c.i w.top.rootKey y := by
      intro i cv y hk hl
      have hm : (cv, y) ∈ pn0.liveAt c.i := by
        rw [KNode.liveAt_of_times pn0 c.i hpt]
        apply mem_of_lookup_nodup
        rw [KNode.live_lookup]
        exact keyLookup_of_last _ _ _ i y hk hl
      exact ⟨hm, TReach.link hpR ⟨pn0, hpn, hm⟩⟩
    have hptrk : ∀ i cv y, LastLive pn0.ks pn0.lastBitmap i cv → pn0.ptr? i = some y →
        pn0.ks[i]? = some (.key cv y) := by
      intro i cv y hl hy
      obtain ⟨⟨y0, hy0⟩, _, _⟩ := hl
      simp only [KNode.ptr?, hy0, Option.some.injEq] at hy
      rw [hy0, hy]
    refine writerWP_mono (writerWP_and (writerWP_getNode_all x c w1 base hvc)
      (writerWP_getNode_cache x c w1)) ?_
    intro xn w2 ⟨⟨hr2, hlk2, hwn2, hpre2, hsrc2⟩, _, _, hp2⟩
    have hp02 : w2.path = w.path := by rw [hp2, hp1]
    have hr02 := ReadsAs.trans _ _ _ _ _ hr1 hr2
    have hpre02 : w1.nodes <+: w2.nodes := hpre2
    have hsrc02 : ∀ z, (w2.nodes.lookup z).isSome = true → z < w.next := by
      intro z hz
      rcases hsrc2 z hz with h | h
      · rcases hsrc1 z h with h' | h'
        · exact hidn z h'
        · exact hidv z h'
      · exact hidv z h
    unfold klongAt
    simp only [writerWP_bind, writerWP_get]
    split
    · rename_i cx _ hcx
      simp only [writerWP_pure]
      generalize hmi : mergeIdx pn0 cx = mi
      obtain ⟨ixo, ia, ib⟩ := mi
      have hML := mergeIdx_last pn0 cx
      rw [hmi] at hML
      obtain ⟨hMx, hMa, hMb⟩ := hML
      split
      · rename_i ix hix
        simp only [writerWP_bind, writerWP_pure]
        have hLx := hMx ix hix
        refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun hptr => ?_)
        · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
        have hpx : pn0.ptr? ix = some x := by simpa using hptr
        have hkx := hptrk ix cx x hLx hpx
        obtain ⟨_, hxR⟩ := hchild ix cx x hkx hLx
        have hxn : wNode c.p base w x = some xn := by
          rw [← hr1.1]; exact hwn2 (by rw [hr1.2.2.1]; exact hRt x hxR)
        -- the step after a sibling is read: both nodes known
        have hsib : ∀ (wb : W) (i cv : Nat) (sn : NodeId × KNode) (w3 : W),
            ReadsAs c.p base w wb → w1.nodes <+: wb.nodes →
            (∀ z, (wb.nodes.lookup z).isSome = true → z < w.next) →
            LastLive pn0.ks pn0.lastBitmap i cv →
            pn0.ptr? i = some sn.1 → ReadsAs c.p base wb w3 → wb.nodes <+: w3.nodes →
            (∀ z, (w3.nodes.lookup z).isSome = true → (wb.nodes.lookup z).isSome = true ∨
              (c.view z).isSome = true) →
            (wb.taken.contains sn.1 = false → wNode c.p base wb sn.1 = some sn.2) →
            pn0.ks[i]? = some (.key cv sn.1) ∧ wNode c.p base w sn.1 = some sn.2 ∧
              ReadsAs c.p base w w3 ∧ w1.nodes <+: w3.nodes ∧
              (∀ z, (w3.nodes.lookup z).isSome = true → z < w.next) := by
          intro wb i cv sn w3 hrb hpreb hsrcb hl hp hr3 hpre3 hsrc3 hwn3
          have hk := hptrk i cv sn.1 hl hp
          obtain ⟨_, hsR⟩ := hchild i cv sn.1 hk hl
          refine ⟨hk, ?_, ReadsAs.trans _ _ _ _ _ hrb hr3, hpreb.trans hpre3, ?_⟩
          · rw [← hrb.1]; exact hwn3 (by rw [hrb.2.2.1]; exact hRt _ hsR)
          · intro z hz
            rcases hsrc3 z hz with h | h
            · exact hsrcb z h
            · exact hidv z h
        -- the right sibling, read from a state wb
        have hright : ∀ (wb : W) (ia0 cva : Nat), ReadsAs c.p base w wb → w1.nodes <+: wb.nodes →
            (∀ z, (wb.nodes.lookup z).isSome = true → z < w.next) → wb.path = w.path →
            LastLive pn0.ks pn0.lastBitmap ia0 cva → cx < cva →
            (mergeIdx pn0 cx).2.1 = some (ia0, cva) →
            WriterWP (do
              let __x ← sibling e.2 pn0 ia0 !xn.leaf
              mergeTail c x d e.2 pn0 xn false x xn ix __x.1 __x.2 ia0) c wb
              (fun _ w' => (SegFits (wNode c.p base w') c.i (c.p.fuel - 1) w'.top.rootKey ∨
                ¬ (s = 0 ∧ ¬ ChainRoom c (Nn 0) ∧ c.p.splitAbove < ((Nn 0).lastVersion c.i).size)) →
                ∀ key, wGet c.p c.i base w' key = wGet c.p c.i base w key) := by
          intro wb ia0 cva hrb hpreb hsrcb hpb hLa hax hia
          rw [writerWP_bind]
          refine writerWP_mono (writerWP_and (writerWP_sibling_leaf e.2 pn0 ia0 (!xn.leaf) c wb base hvc)
            (writerWP_sibling_path e.2 pn0 ia0 (!xn.leaf) c wb)) ?_
          rintro ⟨rs, rsn⟩ w4 ⟨⟨hs1, hr4, _, hwn4, hpre4, hsrc4, hsl⟩, hp4⟩
          obtain ⟨hka, hrn, hr04, hpre14, hsrc04⟩ :=
            hsib wb ia0 cva (rs, rsn) w4 hrb hpreb hsrcb hLa hs1 hr4 hpre4 hsrc4 hwn4
          have hmin := mergeIdx_right_min pn0 cx ia0 cva hia
          exact tailOK false x xn ix rs rsn ia0 cx cva xn w4 hr04 hpre14 hsrc04 (by rw [hp4, hpb]) hkx hLx hka hLa
            hax (by
              intro cc z hm
              rcases Nat.lt_or_ge cx cc with h | h
              · have hm' : (cc, z) ∈ pn0.live := by rw [← KNode.liveAt_of_times pn0 c.i hpt]; exact hm
                exact Or.inr (hmin cc z hm' h)
              · exact Or.inl h) rfl (by rw [hsl]; simp) (Or.inl rfl) hxn hrn
        split
        · rename_i ib0 cvb
          obtain ⟨hLb, hbx⟩ := hMb ib0 cvb rfl
          simp only [writerWP_bind]
          refine writerWP_mono (writerWP_and (writerWP_sibling_leaf e.2 pn0 ib0 (!xn.leaf) c w2 base hvc)
            (writerWP_sibling_path e.2 pn0 ib0 (!xn.leaf) c w2)) ?_
          rintro ⟨ls, lsn⟩ w3 ⟨⟨hs1, hr3, _, hwn3, hpre3, hsrc3, hsl⟩, hp3⟩
          obtain ⟨hkb, hln, hr03, hpre13, hsrc03⟩ :=
            hsib w2 ib0 cvb (ls, lsn) w3 hr02 hpre02 hsrc02 hLb hs1 hr3 hpre3 hsrc3 hwn3
          refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_)
          · show WriterWP (mergeTail c x d e.2 pn0 xn true ls lsn ib0 x xn ix) c w3 _
            have hmax := mergeIdx_left_max pn0 cx ib0 cvb (by rw [hmi])
            exact tailOK true ls lsn ib0 x xn ix cvb cx xn w3 hr03 hpre13 hsrc03 (by rw [hp3, hp02]) hkb hLb hkx hLx
              hbx (by
                intro cc z hm
                rcases Nat.lt_or_ge cc cx with h | h
                · have hm' : (cc, z) ∈ pn0.live := by rw [← KNode.liveAt_of_times pn0 c.i hpt]; exact hm
                  exact Or.inl (hmax cc z hm' h)
                · exact Or.inr h) (by rw [hsl]; simp) rfl (Or.inr rfl) hln hxn
          · rw [writerWP_bind, writerWP_pure]
            dsimp only
            split
            · rename_i ia0 cva _
              obtain ⟨hLa, hax⟩ := hMa ia0 cva rfl
              exact hright w3 ia0 cva hr03 hpre13 hsrc03 (by rw [hp3, hp02]) hLa hax (by rw [hmi])
            · exact writerWP_throw _ _ _ _
        · rw [writerWP_bind, writerWP_pure]
          dsimp only
          split
          · rename_i ia0 cva
            obtain ⟨hLa, hax⟩ := hMa ia0 cva rfl
            exact hright w2 ia0 cva hr02 hpre02 hsrc02 hp02 hLa hax (by rw [hmi])
          · exact writerWP_throw _ _ _ _
      · exact writerWP_throw _ _ _ _
    · exact writerWP_throw _ _ _ _
  · exact writerWP_throw _ _ _ _

end SIS.Tree
