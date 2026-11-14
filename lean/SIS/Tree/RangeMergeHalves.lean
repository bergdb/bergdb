import SIS.Tree.RangeMergeFull
import SIS.Tree.MergeLastOrd
import SIS.Tree.MergeTreeInv

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-! The merge keeps the walk's ranges with the full parent's halves from the
walk's ranges (bergdb 024-12, case (4), the merge step's `RangeOrder` part):
without the premises `hhalves` and `hhalvesR` for every merge value that
prover putinv's first form asked. -/

/-- The halves of the merge's full parent's last version, for the merge's values
(`MergeGOrd`), from the walk's ranges: the premises `hhalves` and `hhalvesR` of
`writerWP_mergeTail_any_range2` (`hhalves_of_sorted`, `mergeLast_range`). -/
theorem mergeLast_halves (c : Ctx) (N : NodeId → Option KNode) (root : NodeId)
    (hR : RangeOrder N c.i root) (q : NodeId) (qn : KNode) (K : Nat) (p : NodeId) (pn : KNode)
    (hq : TReach N c.i root q) (hqn : N q = some qn)
    (hK : (K, p) ∈ qn.liveAt c.i) (hpn : N p = some pn) (hpl : pn.leaf = false)
    (hpRS : ReachS N c.i root p)
    (hpt : ∀ s, Klong.time s ∈ pn.ks → s ≤ c.i) (hqt : ∀ s, Klong.time s ∈ qn.ks → s ≤ c.i)
    (cL cR : Nat) (l r : NodeId) (ln rn : KNode) (hclt : cL < cR)
    (hpL : (cL, l) ∈ pn.liveAt c.i) (hpR : (cR, r) ∈ pn.liveAt c.i)
    (hln : N l = some ln) (hrn : N r = some rn) (hsa2 : 2 ≤ c.p.splitAbove)
    (m1 : NodeId) (m2 : Option (NodeId × Nat)) (last : KNode)
    (hlast : mergeFullLast pn c.i cL m1 cR m2 = some last) (hg : MergeGOrd ln rn cR m2 c.i)
    (hsp : c.p.splitAbove < last.size) :
    (∃ r0 : Nat, 0 < r0 ∧
      (halves pn.leaf c.i last []).2.2 = r0 ∧
      (∀ c' z, (c', z) ∈ (halves pn.leaf c.i last []).1.liveAt c.i → c' < r0 ∧
        (c', z) ∈ (⟨pn.leaf, last.ks⟩ : KNode).liveAt c.i) ∧
      (∀ c' z, (c', z) ∈ (halves pn.leaf c.i last []).2.1.liveAt c.i → ∃ c0, r0 ≤ c0 ∧
        c' = splitLocalCv pn.leaf r0 c0 ∧
        (c0, z) ∈ (⟨pn.leaf, last.ks⟩ : KNode).liveAt c.i) ∧
      (qn.leaf = false →
        K ≤ r0 ∧ ∀ c'' z', (c'', z') ∈ qn.live → K < c'' → r0 < c'')) ∧
    (∀ r0, (halves pn.leaf c.i last []).2.2 = r0 →
      (∃ zs, (r0, zs) ∈ (⟨pn.leaf, last.ks⟩ : KNode).liveAt c.i) ∧
      ∃ c0 z0, (c0, z0) ∈ (⟨pn.leaf, last.ks⟩ : KNode).liveAt c.i ∧ c0 < r0) := by
  obtain ⟨hl1, hl2⟩ := mrg_child_range N c.i root hR p pn hpRS hpn hpl cL l ln hpL hln
  obtain ⟨hr1, hr2⟩ := mrg_child_range N c.i root hR p pn hpRS hpn hpl cR r rn hpR hrn
  -- the second node's compare value is no live one of the parent's but cR
  have hg2none : ∀ y g, m2 = some (y, g) → g ≠ cR → pn.live.lookup g = none := by
    intro y g hm hgc
    obtain ⟨hg0, hw⟩ := hg y g hm
    cases hlk : pn.live.lookup g with
    | none => rfl
    | some z =>
      exfalso
      have hz : (g, z) ∈ pn.liveAt c.i := by
        rw [KNode.liveAt_of_times pn c.i hpt]; exact bk_mem_of_lookup _ g z hlk
      rcases hw with hgc' | ⟨z1, hz1⟩ | ⟨⟨z1, hz1⟩, c0, z0, hc0, hc0g⟩
      · exact hgc hgc'
      · obtain ⟨ha, hb⟩ := hr1 g z1 hz1
        have hcg : cR < g := by
          cases hrl : rn.leaf
          · rcases hb hrl with h | h
            · omega
            · exact h (by omega)
          · have := ha hrl (by omega); omega
        have := hr2 g z hz hcg g z1 hz1
        omega
      · have hcg : cL < g := by
          rcases Nat.eq_zero_or_pos cL with h0 | h0
          · omega
          · cases hll : ln.leaf
            · rcases (hl1 g z1 hz1).2 hll with h | h
              · omega
              · exact h h0
            · have := (hl1 c0 z0 hc0).1 hll h0; omega
        have := hl2 g z hz hcg g z1 hz1
        omega
  obtain ⟨pairs, hks, hs⟩ := mergeFullLast_sorted pn c.i cL m1 cR m2 last hlast hg2none
  have hleaf := (mergeFullLast_lookup pn c.i cL m1 cR m2 last hlast).1
  refine ⟨hhalves_of_sorted c pn last pairs hleaf hks hs qn K (fun _ hql' c' z hz hpos =>
    mergeLast_range c N root hR q qn K p pn hq hqn hql' hK hpn hpl hpt hqt cL cR l r ln rn hpL hpR
      hln hrn m1 m2 last hlast (MergeGOrd.toGOK hg) c' z hz hpos) hsa2 hsp, ?_⟩
  intro r0 hr0
  have hxe : (⟨pn.leaf, last.ks⟩ : KNode) = ⟨pn.leaf, newKlongs c.i pairs⟩ := by rw [hks]
  have hlv : (⟨pn.leaf, last.ks⟩ : KNode).lastVersion c.i = last := by
    rw [hxe, KNode.lastVersion_newKlongs_sorted _ _ _ hs, ← hks]
    cases last with
    | mk lf ks => simp only at hleaf; rw [hleaf]
  have h2 : 2 ≤ (⟨pn.leaf, last.ks⟩ : KNode).live.length := by
    rw [hxe, KNode.live_newKlongs_sorted _ _ _ hs]
    have : last.size = pairs.length + 1 := by simp [KNode.size, hks, newKlongs]
    omega
  have ht : ∀ s, Klong.time s ∈ (⟨pn.leaf, last.ks⟩ : KNode).ks → s ≤ c.i := by
    show ∀ s, Klong.time s ∈ last.ks → s ≤ c.i
    rw [hks]; exact newKlongs_times c.i pairs
  obtain ⟨_, _, _, ⟨y, hy⟩, ⟨q0, hq0, hq0lt⟩⟩ :=
    halves_node (⟨pn.leaf, last.ks⟩ : KNode) c.i [] ht h2 List.Pairwise.nil
  rw [hlv] at hy hq0lt
  have hy' : ((halves pn.leaf c.i last []).2.2, y) ∈ (⟨pn.leaf, last.ks⟩ : KNode).live := hy
  have hq0lt' : q0.1 < (halves pn.leaf c.i last []).2.2 := hq0lt
  rw [hr0] at hy' hq0lt'
  refine ⟨⟨y, by rw [KNode.liveAt_of_times _ c.i ht]; exact hy'⟩, q0.1, q0.2,
    by rw [KNode.liveAt_of_times _ c.i ht]; exact hq0, hq0lt'⟩

/-- The writer's merge keeps the walk's ranges, the parent with room or full
(with `RangeOrder`), with the full parent's halves from the walk's ranges
(`mergeLast_halves`). -/
theorem writerWP_merge_any_range2 (x : NodeId) (d : Nat) (c : Ctx) (base : View BVal)
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
    (hlinksAll : ∀ u c' z, TLink (wNode c.p base w) c.i u c' z → z < w.next)
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
    (hS2 : ∀ i, s ≤ i → i ≤ D + 1 →
      w.nodes.lookup (X i) = some (Nn i) ∧ w.taken.contains (X i) = false)
    (hS4 : ∀ i, s ≤ i → i ≤ D + 1 → TReach (wNode c.p base w) c.i w.top.rootKey (X i))
    (hR0 : s = 0 → w.top.rootKey = X 0)
    (hXx : ∀ i, s ≤ i → i ≤ D + 1 → X i ≠ x)
    (hR : RangeOrder (wNode c.p base w) c.i w.top.rootKey) (hcap : 1 ≤ c.p.mergeMax)
    (hsa2 : 2 ≤ c.p.splitAbove) :
    WriterWP (merge x d) c w (fun _ w' => RangeOrder (wNode c.p base w') c.i w'.top.rootKey) := by
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
    have hpn : wNode c.p base w e.2 = some pn0 := hwn1 (hRt _ hpR)
    have hpRS := tReach_reachS _ c.i _ _ hpR
    -- the tail from any state that reads as w
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
          (fun _ w' => RangeOrder (wNode c.p base w') c.i w'.top.rootKey) := by
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
        apply bk_mem_of_lookup
        rw [KNode.live_lookup]
        exact keyLookup_of_last _ _ _ il l hL hLL
      have hmemR : (cR, r) ∈ pn0.liveAt c.i := by
        rw [KNode.liveAt_of_times pn0 c.i hpt]
        apply bk_mem_of_lookup
        rw [KNode.live_lookup]
        exact keyLookup_of_last _ _ _ ir r hR' hRL
      obtain ⟨hlr1, hlr2⟩ := mrg_child_range (wNode c.p base w) c.i w.top.rootKey hR e.2 pn0 hpRS hpn
        hpleaf cL l ln hmemL hln
      obtain ⟨hrr1, hrr2⟩ := mrg_child_range (wNode c.p base w) c.i w.top.rootKey hR e.2 pn0 hpRS hpn
        hpleaf cR r rn hmemR hrn
      have hwD : wNode c.p base w (X D) = some (Nn D) := by
        obtain ⟨a, b⟩ := hS2 D (by omega) (by omega)
        simp only [wNode, b, Bool.false_eq_true, ↓reduceIte, a]
      have hkD : (K (D + 1), e.2) ∈ (Nn D).liveAt c.i := by
        have h1 := hlinkK (D + 1) (by omega) (Nat.le_refl _)
        rw [hXp] at h1
        simpa using h1
      apply writerWP_mergeTail_any_range2 c base x d e.2 pn0 xn leftSome l ln il r rn ir cL cR
        (wNode c.p base w) w.top.rootKey w.next w3 hT hpR (hwn1 (hRt _ hpR)) hL hLL hR' hRL (by omega) hxlr
        hln hrn hpwf hpt hch hr3.1 (by rw [hr3.2.1]) hr3.2.2.2.2
        (lookup_of_prefix _ _ hpre3 _ _ hlk1) hsrc3
        (fun z hz => ⟨(hfree z hz).1, by rw [hr3.2.2.1]; exact (hfree z hz).2⟩) hfreshT hvc hlinksAll
        hbaseF s D X K Nn hsD hd (by rw [hp3]; exact hX) (by rw [hp3]; exact hK) hlinkK hrange hlen
        hwf htimes htop hdist hXp hNp
        (fun i h1 h2 => ⟨lookup_of_prefix _ _ (hpre1.trans hpre3) _ _ (hS2 i h1 h2).1,
          by rw [hr3.2.2.1]; exact (hS2 i h1 h2).2⟩)
        hS4
        hR0 hXx
        (fun m1 m2 last h hg hsp => by
          rw [hNp]
          exact (mergeLast_halves c (wNode c.p base w) w.top.rootKey hR (X D) (Nn D) (K (D + 1)) e.2 pn0
            (hS4 D (by omega) (by omega)) hwD hkD hpn hpleaf hpRS hpt (htimes D (by omega) (by omega)) cL cR l r ln rn
            hclt hmemL hmemR hln hrn hsa2 m1 m2 last h hg hsp).1)
        (fun m1 m2 last h hg hsp => by
          rw [hNp]
          exact (mergeLast_halves c (wNode c.p base w) w.top.rootKey hR (X D) (Nn D) (K (D + 1)) e.2 pn0
            (hS4 D (by omega) (by omega)) hwD hkD hpn hpleaf hpRS hpt (htimes D (by omega) (by omega)) cL cR l r ln rn
            hclt hmemL hmemR hln hrn hsa2 m1 m2 last h hg hsp).2)
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
        hR
    -- a klong of p that is the last live one of its compare value names a reached node
    have hchild : ∀ i cv y, pn0.ks[i]? = some (.key cv y) → LastLive pn0.ks pn0.lastBitmap i cv →
        (cv, y) ∈ pn0.liveAt c.i ∧ TReach (wNode c.p base w) c.i w.top.rootKey y := by
      intro i cv y hk hl
      have hm : (cv, y) ∈ pn0.liveAt c.i := by
        rw [KNode.liveAt_of_times pn0 c.i hpt]
        apply bk_mem_of_lookup
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
              (fun _ w' => RangeOrder (wNode c.p base w') c.i w'.top.rootKey) := by
          intro wb ia0 cva hrb hpreb hsrcb hpb hLa hax hia
          rw [writerWP_bind]
          refine writerWP_mono (writerWP_and (writerWP_sibling_leaf e.2 pn0 ia0 (!xn.leaf) c wb base hvc)
            (writerWP_sibling_path e.2 pn0 ia0 (!xn.leaf) c wb)) ?_
          rintro ⟨rs, rsn⟩ w4 ⟨⟨hs1, hr4, _, hwn4, hpre4, hsrc4, hsl⟩, hp4⟩
          obtain ⟨hka, hrn, hr04, hpre14, hsrc04⟩ :=
            hsib wb ia0 cva (rs, rsn) w4 hrb hpreb hsrcb hLa hs1 hr4 hpre4 hsrc4 hwn4
          have hmin := mergeIdx_right_min pn0 cx ia0 cva hia
          exact tailOK false x xn ix rs rsn ia0 cx cva xn w4 hr04 hpre14 hsrc04 (by rw [hp4, hpb]) hkx hLx
            hka hLa hax (by
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
            exact tailOK true ls lsn ib0 x xn ix cvb cx xn w3 hr03 hpre13 hsrc03 (by rw [hp3, hp02]) hkb hLb
              hkx hLx hbx (by
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
