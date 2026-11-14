/-
The merge keeps the take-back's facts (bergdb 024-12, TP7, case (4)): latest's
`writerWP_merge_any_get` walk with `TakeJ2` as its post, the tail by
`writerWP_mergeTail_any_j2`.
-/
import SIS.Tree.TakeMergeTail
import SIS.Tree.TakeDelMerge
import SIS.Tree.TakeBaseStart

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

set_option maxHeartbeats 3200000 in
/-- The writer's merge keeps `TakeJ2` with the parent at depth D + 1 full or with
room: `writerWP_merge_any_get`'s premises, with `J2N` before, B at most the
next id and above the values, the cascade's levels ordered (`hord`) and the
path's nodes at their depths (`hXdepth`). -/
theorem writerWP_merge_any_j2 (fuelR : Nat) (hfR : 2 ≤ fuelR) (x : NodeId) (d : Nat) (c : Ctx) (base : View BVal)
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
      c.p.splitAbove < ((Nn i).lastVersion c.i).size → i = 0 ∨ (s < i ∧ ((Nn (i - 1)).leaf = false ∨
        ((Nn i).firstTime ≠ some c.i → ∀ i', s < i' → i' < i → ChainOrd c K Nn i'))))
    (hS2 : ∀ i, s ≤ i → i ≤ D + 1 →
      w.nodes.lookup (X i) = some (Nn i) ∧ w.taken.contains (X i) = false)
    (hS4 : ∀ i, s ≤ i → i ≤ D + 1 → TReach (wNode c.p base w) c.i w.top.rootKey (X i))
    (hR0 : s = 0 → w.top.rootKey = X 0)
    (hXx : ∀ i, s ≤ i → i ≤ D + 1 → X i ≠ x)
    (hsa2 : 2 ≤ c.p.splitAbove)
    (hspaceL : ∀ cL cR m1 m2 last, mergeFullLast (Nn (D + 1)) c.i cL m1 cR m2 = some last →
      c.p.splitAbove < last.size → (Nn D).leaf = false ∨
        ((Nn (D + 1)).firstTime ≠ some c.i → ∀ i', s < i' → i' < D + 1 → ChainOrd c K Nn i'))
    (B : NodeId) (hpos : 0 < c.i) (hJ : J2N (wNode c.p base w) c.i w.top.rootKey B (w.vals.map (·.1)))
    (hBnx : B ≤ w.next) (hvnx : ∀ y ∈ w.vals.map (·.1), y < w.next)
    (hord : ∀ i, s < i → i ≤ D → ChainOrd c K Nn i)
    (hXdepth : ∀ i, s ≤ i → i ≤ D + 1 → PathLen (wNode c.p base w) c.i w.top.rootKey (X i) i) :
    WriterWP (merge x d) c w (fun _ w' => TakeJ2 c base B w') := by
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
        w3.nodes.lookup l = some ln → w3.nodes.lookup r = some rn →
        WriterWP (mergeTail c x d e.2 pn0 xn leftSome l ln il r rn ir) c w3
          (fun _ w' => TakeJ2 c base B w') := by
      intro leftSome l ln il r rn ir cL cR xn w3 hr3 hpre3 hsrc3 hp3 hL hLL hR' hRL hclt hadj hll hrl
        hxlr hln hrn h3l h3r
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
      exact (writerWP_mergeTail_any_j2 fuelR hfR c base x d e.2 pn0 xn leftSome l ln il r rn ir cL cR
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
        hS4 hR0 hXx hsa2
        (fun m1 m2 last h hg _ hqlD => by
          have hwD : wNode c.p base w (X D) = some (Nn D) := by
            obtain ⟨a, b⟩ := hS2 D (by omega) (by omega)
            simp only [wNode, b, Bool.false_eq_true, ↓reduceIte, a]
          have hkD : (K (D + 1), e.2) ∈ (Nn D).liveAt c.i := by
            have h1 := hlinkK (D + 1) (by omega) (Nat.le_refl _)
            rw [hXp] at h1
            simpa using h1
          exact mergeLast_range c (wNode c.p base w) w.top.rootKey hR (X D) (Nn D) (K (D + 1)) e.2 pn0
            (hS4 D (by omega) (by omega)) hwD hqlD hkD hpn hpleaf hpt (htimesN _ _ hwD)
            cL cR l r ln rn hmemL hmemR hln hrn m1 m2 last h hg)
        (fun m1 m2 last h => by rw [← hNp]; exact hspaceL cL cR m1 m2 last (by rw [hNp]; exact h))
        B hpos (by rw [hr3.2.2.2.1]; exact hJ) hBnx
        (by rw [hr3.2.2.2.1]; exact hvnx) hR hord h3l h3r hXdepth)
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
            (mergeIdx pn0 cx).2.1 = some (ia0, cva) → wb.nodes.lookup x = some xn →
            WriterWP (do
              let __x ← sibling e.2 pn0 ia0 !xn.leaf
              mergeTail c x d e.2 pn0 xn false x xn ix __x.1 __x.2 ia0) c wb
              (fun _ w' => TakeJ2 c base B w') := by
          intro wb ia0 cva hrb hpreb hsrcb hpb hLa hax hia hxb
          rw [writerWP_bind]
          refine writerWP_mono (writerWP_and (writerWP_sibling_leaf e.2 pn0 ia0 (!xn.leaf) c wb base hvc)
            (writerWP_sibling_path e.2 pn0 ia0 (!xn.leaf) c wb)) ?_
          rintro ⟨rs, rsn⟩ w4 ⟨⟨hs1, hr4, hlk4s, hwn4, hpre4, hsrc4, hsl⟩, hp4⟩
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
              (lookup_of_prefix _ _ hpre4 _ _ hxb) hlk4s
        split
        · rename_i ib0 cvb
          obtain ⟨hLb, hbx⟩ := hMb ib0 cvb rfl
          simp only [writerWP_bind]
          refine writerWP_mono (writerWP_and (writerWP_sibling_leaf e.2 pn0 ib0 (!xn.leaf) c w2 base hvc)
            (writerWP_sibling_path e.2 pn0 ib0 (!xn.leaf) c w2)) ?_
          rintro ⟨ls, lsn⟩ w3 ⟨⟨hs1, hr3, hlk3s, hwn3, hpre3, hsrc3, hsl⟩, hp3⟩
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
              hlk3s (lookup_of_prefix _ _ hpre3 _ _ hlk2)
          · rw [writerWP_bind, writerWP_pure]
            dsimp only
            split
            · rename_i ia0 cva _
              obtain ⟨hLa, hax⟩ := hMa ia0 cva rfl
              exact hright w3 ia0 cva hr03 hpre13 hsrc03 (by rw [hp3, hp02]) hLa hax (by rw [hmi])
                (lookup_of_prefix _ _ hpre3 _ _ hlk2)
            · exact writerWP_throw _ _ _ _
        · rw [writerWP_bind, writerWP_pure]
          dsimp only
          split
          · rename_i ia0 cva
            obtain ⟨hLa, hax⟩ := hMa ia0 cva rfl
            exact hright w2 ia0 cva hr02 hpre02 hsrc02 hp02 hLa hax (by rw [hmi]) hlk2
          · exact writerWP_throw _ _ _ _
      · exact writerWP_throw _ _ _ _
    · exact writerWP_throw _ _ _ _
  · exact writerWP_throw _ _ _ _

/-- Obligation: a merge with the parent at the space root (d = 1) keeps `TakeJ2`
(`MergeStepJ2OKF` at d = 1; it needs the root's split with the reach-back and the
shapes, `writerWP_handleFull_rootVReach`, latest). -/
def MergeRootJ2OKF (c : Ctx) (base : View BVal) (f : Nat) (B : NodeId) : Prop :=
  ∀ (w0 : W) (key : Key) (x q : NodeId) (d : Nat) (v : W) (qn xn : KNode) (X : Nat → NodeId)
    (K : Nat → Nat) (Nn : Nat → KNode), d = 1 →
    DelInvJF c base w0 key f B v → 0 < d → (v.path[d]?).map (·.2) = some x →
    (v.path[d - 1]?).map (·.2) = some q → v.nodes.lookup q = some qn → qn.leaf = false →
    v.nodes.lookup x = some xn → xn.cnt < c.p.mergeBelow →
    PathOK c v d X K Nn → X d = x →
    WriterWP (merge x d) c v (fun _ v' => TakeJ2 c base B v')

/-- A merge keeps `TakeJ2` at every depth: at depth 2 or more by
`writerWP_merge_any_j2` with its premises from the delete's invariant and the
path (as `writerWP_merge_get_inv` has them), at depth 1 by the obligation. -/
theorem mergeStepJ2OKF_of_root (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base) (f : Nat)
    (B : NodeId) (hpos : 0 < c.i) (hcap : 1 ≤ c.p.mergeMax) (hsa2 : 2 ≤ c.p.splitAbove)
    (hRoot : MergeRootJ2OKF c base f B) : MergeStepJ2OKF c base f B := by
  intro w0 key x q d v qn xn X K Nn hIJ hd0 hxp hq hqn hql hxn hcnt hP hx
  by_cases hd1 : d = 1
  · exact hRoot w0 key x q d v qn xn X K Nn hd1 hIJ hd0 hxp hq hqn hql hxn hcnt hP hx
  obtain ⟨⟨hI, hG, hRO, _, _, _, _⟩, hJ, hBn⟩ := hIJ
  have hP' := hP
  obtain ⟨hX, hK, hS2, hlink, h0⟩ := hP'
  have hT := hI.tree
  have hreach := pathOK_reach c base v d X K Nn hP
  have hdist := pathOK_dist c base v d X K Nn hP hT
  have hw : ∀ j, j ≤ d → wNode c.p base v (X j) = some (Nn j) := by
    intro j hj
    obtain ⟨a, b⟩ := hS2 j hj
    simp only [wNode, b, Bool.false_eq_true, ↓reduceIte, a]
  have hXq : X (d - 1) = q := by
    have := hX (d - 1) (by omega)
    rw [hq] at this
    exact (Option.some.inj this).symm
  have hNq : Nn (d - 1) = qn := by
    have := (hS2 (d - 1) (by omega)).1
    rw [hXq, hqn] at this
    exact (Option.some.inj this).symm
  have hql' : (Nn (d - 1)).leaf = false := by rw [hNq]; exact hql
  have hO := ordG_of_rangeOrder c _ _ hRO hI.times
  have hpar : ∀ p, (v.path[d - 1]?).map (·.2) = some p →
      TReach (wNode c.p base v) c.i v.top.rootKey p ∧ ∃ pn, wNode c.p base v p = some pn ∧
        pn.leaf = false ∧ klongsWf pn.ks = true ∧ (∀ s, Klong.time s ∈ pn.ks → s ≤ c.i) ∧
        ∀ cc z zn, (cc, z) ∈ pn.liveAt c.i → wNode c.p base v z = some zn →
          ∀ s, Klong.time s ∈ zn.ks → s ≤ c.i := by
    intro p hp
    have hpX : p = X (d - 1) := by
      rw [hX (d - 1) (by omega)] at hp; exact (Option.some.inj hp).symm
    subst hpX
    exact ⟨hreach (d - 1) (by omega), Nn (d - 1), hw (d - 1) (by omega), hql',
      hI.wf _ _ (hw (d - 1) (by omega)), hI.times _ _ (hw (d - 1) (by omega)),
      fun cc z zn _ hz => hI.times z zn hz⟩
  have hRt : ∀ y, TReach (wNode c.p base v) c.i v.top.rootKey y → v.taken.contains y = false :=
    fun y hy => hI.untaken y (tReach_reachS _ _ _ _ hy)
  have hids : (∀ z, (v.nodes.lookup z).isSome = true → z < v.next) ∧
      (∀ z, (c.view z).isSome = true → z < v.next) ∧ (∀ z, v.taken.contains z = true → z < v.next) :=
    ⟨hI.ids.1, hI.ids.2.1, hI.ids.2.2.1⟩
  have hbaseF : ∀ z, v.next ≤ z → knodeOf c.p base z = none := fun z hz => (hI.fresh z hz).1
  have hlinksAll : ∀ u c' z, TLink (wNode c.p base v) c.i u c' z → z < v.next :=
    fun u c' z ⟨un, hun, hl⟩ => hG.links u un c' z hun hl
  have hfreshT : ∀ z, v.next ≤ z → ∀ u c', TReach (wNode c.p base v) c.i v.top.rootKey u →
      ¬ TLink (wNode c.p base v) c.i u c' z := by
    intro z hz u c' _ hl; have := hlinksAll u c' z hl; omega
  have hfreshV : ∀ z, v.next ≤ z → wValue base v z = none := by
    intro z hz
    have htz : v.taken.contains z = false := by
      cases h' : v.taken.contains z with
      | false => rfl
      | true => have := hI.ids.2.2.1 z h'; omega
    have hvz : v.vals.lookup z = none := by
      cases h' : v.vals.lookup z with
      | none => rfl
      | some _ =>
        have hm := lookup_some_mem h'
        have := hI.ids.2.2.2.1 _ hm
        simp only at this; omega
    simp only [wValue, htz, Bool.false_eq_true, ↓reduceIte, hvz, (hI.fresh z hz).2]
  have hvnx : ∀ y ∈ v.vals.map (·.1), y < v.next := by
    intro y hy
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy
    have := hI.ids.2.2.2.1 _ he
    simpa using this
  have hd2 : 2 ≤ d := by omega
  exact writerWP_merge_any_j2 2 (Nat.le_refl _) x d c base hvc v hT hpar hRt hids hbaseF hfreshT hRO
    hcap hI.times hI.wf hI.keyNoValue hlinksAll hfreshV 0 (d - 2) X K Nn (Nat.zero_le _)
    (by omega)
    (fun i _ hi => hX i (by omega))
    (fun i h1 hi => hK i h1 (by omega))
    (fun i h1 hi => hlink i h1 (by omega))
    (fun i h1 hi hNR hql' c' z hz hpos =>
      rangeG_of_rangeOrder c _ _ hRO hI.times (X (i - 1)) (Nn (i - 1)) (X i) (Nn i) (K i)
        (hreach (i - 1) (by omega)) (hw (i - 1) (by omega)) hql' (hlink i h1 (by omega))
        (hw i (by omega)) hNR c' z hz hpos)
    (fun i _ hi hNR hsp => lenG_of_splitAbove c _ _ hsa2 (X i) (Nn i) (hreach i (by omega))
      (hw i (by omega)) hNR hsp)
    (fun i _ hi => hI.wf _ _ (hw i (by omega)))
    (fun i _ hi => hI.times _ _ (hw i (by omega)))
    (Or.inr rfl)
    (fun i i' _ hi _ hi' he => hdist i i' (by omega) (by omega) he)
    (by
      intro i _ hi hNR hsp
      rcases Nat.eq_zero_or_pos i with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, Or.inr (fun _ i' h1 h2 =>
          chainOrd_of_ordG c base v d X K Nn hP hO i' h1 (by omega))⟩)
    (fun i _ hi => hS2 i (by omega))
    (fun i _ hi => hreach i (by omega))
    (fun _ => by rw [h0])
    (fun i _ hi he => by
      have := hdist i d (by omega) (Nat.le_refl _) (by rw [he, hx]); omega)
    hsa2
    (by
      have he : d - 2 + 1 = d - 1 := by omega
      rw [he]
      intro cL cR m1 m2 last hl hsp
      exact Or.inr (fun _ i' h1 h2 => chainOrd_of_ordG c base v d X K Nn hP hO i' h1 (by omega)))
    B hpos (by unfold TakeJ2 at hJ; exact hJ) hBn hvnx
    (fun i h1 h2 => chainOrd_of_ordG c base v d X K Nn hP hO i h1 (by omega))
    (fun i _ h2 => pathOK_depth c base v d X K Nn hP i (by omega))

end SIS.Tree
