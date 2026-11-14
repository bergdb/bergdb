/-
The merge's tail keeps the nodes reached untaken (bergdb 024-12, TP7,
`MergeStepOKF3`'s first part): `writerWP_mergeTail_any_j2`'s walk with the
nodes reached after the merge, untaken, as its post.
-/
import SIS.Tree.TakeMergeFull
import SIS.Tree.GetMergeAny

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A node reached after a change that adds no link out of the nodes reached
before was reached before. -/
theorem tReach_back_step (N N' : NodeId → Option KNode) (t : Time) (root : NodeId)
    (hstep : ∀ x c z, TReach N t root x → TLink N' t x c z → TLink N t x c z) :
    ∀ z, TReach N' t root z → TReach N t root z := by
  intro z hz
  induction hz with
  | root => exact TReach.root
  | link _ hl ih => exact TReach.link ih (hstep _ _ _ ih hl)

set_option maxHeartbeats 3200000 in
/-- The merge's tail, the parent p at depth D + 1 with room or full, keeps the
nodes reached untaken: a node reached after was reached before (untaken,
`hRt`) or is one of the merge's new nodes or the cascade's; the two nodes
merged are reached no more. On `writerWP_mergeTail_any_j2`'s premises without
`TakeJ2`'s. -/
theorem writerWP_mergeTail_any_untaken (fuelR : Nat) (hfR : 2 ≤ fuelR) (c : Ctx) (base : View BVal) (x : NodeId) (d : Nat) (p : NodeId)
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
      c.p.splitAbove < ((Nn i).lastVersion c.i).size → i = 0 ∨ (s < i ∧ ((Nn (i - 1)).leaf = false ∨
        ((Nn i).firstTime ≠ some c.i → ∀ i', s < i' → i' < i → ChainOrd c K Nn i'))))
    (hXp : X (D + 1) = p) (hNp : Nn (D + 1) = pn)
    (hS2 : ∀ i, s ≤ i → i ≤ D + 1 →
      w3.nodes.lookup (X i) = some (Nn i) ∧ w3.taken.contains (X i) = false)
    (hS4 : ∀ i, s ≤ i → i ≤ D + 1 → TReach N c.i root (X i))
    (hR0 : s = 0 → root = X 0)
    (hXx : ∀ i, s ≤ i → i ≤ D + 1 → X i ≠ x)
    (hsa2 : 2 ≤ c.p.splitAbove)
    (hrangeL : ∀ m1 m2 last, mergeFullLast pn c.i cL m1 cR m2 = some last →
      MergeGOK ln rn cR m2 c.i → c.p.splitAbove < last.size → (Nn D).leaf = false →
      ∀ c' z, (c', z) ∈ (⟨pn.leaf, last.ks⟩ : KNode).live → 0 < c' →
      K (D + 1) ≤ c' ∧ ∀ c'' z', (c'', z') ∈ (Nn D).live → K (D + 1) < c'' → c' < c'')
    (hspaceL : ∀ m1 m2 last, mergeFullLast pn c.i cL m1 cR m2 = some last →
      c.p.splitAbove < last.size →
      (Nn D).leaf = false ∨ (pn.firstTime ≠ some c.i → ∀ i', s < i' → i' < D + 1 → ChainOrd c K Nn i'))
    (hpos : 0 < c.i) (hRt : ∀ y, TReach N c.i root y → w3.taken.contains y = false)
    (hRO : RangeOrder N c.i root)
    (hord : ∀ i, s < i → i ≤ D → ChainOrd c K Nn i)
    (h3l : w3.nodes.lookup l = some ln) (h3r : w3.nodes.lookup r = some rn)
    (hXdepth : ∀ i, s ≤ i → i ≤ D + 1 → PathLen N c.i root (X i) i) :
    WriterWP (mergeTail c x d p pn xn leftSome l ln il r rn ir) c w3
      (fun _ w' => ∀ y, TReach (wNode c.p base w') c.i w'.top.rootKey y → w'.taken.contains y = false) := by
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
  obtain ⟨xn3, hx3⟩ : ∃ n, w3.nodes.lookup x = some n := by
    rcases hxlr with h | h
    · rw [h]; exact ⟨ln, h3l⟩
    · rw [h]; exact ⟨rn, h3r⟩
  refine writerWP_mono (writerWP_and (writerWP_and (writerWP_ghOf_frame x c _) (writerWP_ghOf_reads x c _ base hvc))
    (writerWP_ghOf_cached x xn3 c _ (by exact hx3) (fun _ w' => w'.nodes.lookup x = some xn3)
      (fun _ => by exact hx3))) ?_
  intro gh w4 ⟨⟨⟨h4t, h4top, h4n, h4v, h4p, h4m, h4l⟩, hr4⟩, h4x⟩
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
              (TReach N c.i root z ∨ z = m1 ∨ some z = (none : Option NodeId)) ∧ z ≠ l ∧ z ≠ r) ∧
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
            exact this
          · have h6nx : w6.next = m1 + 2 := by rw [h6next, h5next, hw4m1]
            rcases hnoneL rfl c' z hm with ⟨_, h⟩ | ⟨h, _, _⟩
            · omega
            · have := hlinksAll p c' z ⟨pn, hpn, h⟩; omega
        obtain ⟨hVt, hVlr, hvx⟩ := hV6 last hlast
        obtain ⟨htl, hleafl, _, _⟩ := mergeFullLast_liveAt pn c.i cL m1 cR none last hlast hpt
        obtain ⟨hiffN, _⟩ := mergeFullLast_iff pn c.i cL m1 cR none last hlast hpt
        obtain ⟨pairsL, hksL⟩ := mergeFullLast_ks pn c.i cL m1 cR none last hlast
        have hlwf : klongsWf last.ks = true := by rw [hksL]; exact klongsWf_newKlongs c.i pairsL
        have hlasteq : (⟨pn.leaf, last.ks⟩ : KNode) = last := by
          cases last with
          | mk lf ks => simp only at hleafl; rw [hleafl]
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
        obtain ⟨pairsS, hksS, hsS⟩ := mergeFullLast_sorted pn c.i cL m1 cR none last hlast
          (fun _ _ h => by cases h)
        have hxe : (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode) = ⟨pn.leaf, newKlongs c.i pairsS⟩ := by
          rw [hNp, hksS]
        have hlastV : (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).lastVersion c.i = last := by
          rw [hxe, KNode.lastVersion_newKlongs_sorted _ _ _ hsS, ← hksS]; exact hlasteq
        have hlen2 : c.p.splitAbove < last.size → 2 ≤ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).live.length := by
          intro h
          rw [hxe, KNode.live_newKlongs_sorted _ _ _ hsS]
          have : last.size = pairsS.length + 1 := by simp [KNode.size, hksS, newKlongs]
          omega
        have hrangeL' : c.p.splitAbove < last.size → (Nn D).leaf = false →
            ∀ c' z, (c', z) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).live → 0 < c' →
            K (D + 1) ≤ c' ∧ ∀ c'' z', (c'', z') ∈ (Nn D).live → K (D + 1) < c'' → c' < c'' := by
          rw [hNp]; exact hrangeL m1 none last hlast (fun y g h => by cases h)
        have hspaceL' : (!compact && decide (last.size > c.p.splitAbove)) = true →
            (Nn D).leaf = false ∨ ((Nn (D + 1)).firstTime ≠ some c.i →
              ∀ i', s < i' → i' < D + 1 → ChainOrd c K Nn i') := by
          intro h
          have h' : c.p.splitAbove < last.size := by cases compact <;> simp at h <;> omega
          rw [hNp]; exact hspaceL m1 none last hlast h'
        have hlevel := writerWP_handleFull_lastVF2 fuelR hfR c base w3.path s D X K Nn hsD hX hK hlinkK hrange hlen
          hwf htimes htop hdist hspace last compact hlwf htl hlastV hlen2 hrangeL' hspaceL'
          ({ w6 with trail := s7 :: w6.trail } : W)
          (by show w6.path = w3.path; rw [h6p, h5p, h4p])
          h6S2 h6T h6S4 h6S5 h6S6 (fun h0 _ => h6R0 h0) hW6
          (by rw [hXp, hNp]; exact hVt) (by rw [hNp]; exact hvx)
        rw [hXp] at hlevel
        have hlr : l < w6.next ∧ r < w6.next := ⟨by rw [h6next, h5next, hw4m1]; omega, by rw [h6next, h5next, hw4m1]; omega⟩
        have hpV : TReach (updN (wNode c.p base w6) p ⟨pn.leaf, last.ks⟩) c.i w6.top.rootKey p := by
          rw [← hXp]
          exact tReach_updN_self _ c.i _ _ _ h6T (h6S4 (D + 1) (by omega) (Nat.le_refl _))
        have hLO : LastOrd c K Nn D last := by
          intro hsp hql
          have hK1 : (K (D + 1), p) ∈ (Nn D).liveAt c.i := by
            have := hlinkK (D + 1) (by omega) (Nat.le_refl _)
            rw [show D + 1 - 1 = D by omega, hXp] at this; exact this
          have hND : N (X D) = some (Nn D) := by
            obtain ⟨hl3, ht3⟩ := hS2 D hsD (by omega)
            rw [← hNw3]; simp only [wNode, ht3, Bool.false_eq_true, ↓reduceIte, hl3]
          refine lastOrd_of_inner c K Nn D last (by rw [hNp]; exact hpleaf) ?_ hsp hql
          intro c' z hz
          rw [hNp] at hz
          exact mergeLast_ord c N root hRO (X D) (Nn D) (K (D + 1)) p pn (hS4 D hsD (by omega)) hND hql hK1
            hpn hpleaf hpt cL cR l r ln rn hclt hpL hpR hln hrn m1 none last hlast (fun _ _ h => by cases h)
            c' z hz
        have h6nx : w6.next = m1 + 2 := by rw [h6next, h5next, hw4m1]
        have hshapeL := writerWP_handleFull_lastShape c w3.path s D X K Nn hsD hX hK hlinkK hrange hlen hord
          htimes htop hdist last compact ⟨pairsS, hksS, List.pairwise_map.mpr (hsS.imp (by intro a b hab; omega))⟩
          hlastV hlen2 hrangeL' hLO ({ w6 with trail := s7 :: w6.trail } : W)
          (by show w6.path = w3.path; rw [h6p, h5p, h4p])
          (fun i h1 h2 => ⟨(h6S2 i h1 h2).1, by have := hXlt i h1 h2; show X i < w6.next; omega⟩)
          (fun z hz => (h6S5 z hz).1)
        rw [hXp] at hshapeL
        have hcache7 := @state_handleFullWith_compact (cachedFromInvariant ({ w6 with trail := s7 :: w6.trail } : W))
          (fun q more => appendKlongs D q more) (D + 1) p [] last compact
          (fun q more => @state_appendKlongs (cachedFromInvariant ({ w6 with trail := s7 :: w6.trail } : W)) D q more)
          c ({ w6 with trail := s7 :: w6.trail } : W) (cachedFrom_refl _ c)
        refine writerWP_mono (writerWP_and (writerWP_and hlevel hshapeL) hcache7) ?_
        rintro _ w7 ⟨⟨⟨hT7, ⟨_, ht7, _, _, hv7⟩, hfr7, hreach7, hW7', hR7, hP7, hRB1, hRB2⟩, hSP7⟩, hca7⟩
        have hW7 : ∀ z zn, TReach (wNode c.p base w7) c.i w7.top.rootKey z →
            wNode c.p base w7 z = some zn → klongsWf zn.ks = true := fun z zn _ h => hW7' z zn h
        have hl7 : ¬ TReach (wNode c.p base w7) c.i w7.top.rootKey l := by
          intro h
          rcases hreach7 l h with h' | h'
          · rw [hNp] at h'; exact (hVlr l h').2.1 rfl
          · have := hlr.1; simp only at h'; omega
        have hr7 : ¬ TReach (wNode c.p base w7) c.i w7.top.rootKey r := by
          intro h
          rcases hreach7 r h with h' | h'
          · rw [hNp] at h'; exact (hVlr r h').2.2 rfl
          · have := hlr.2; simp only at h'; omega
        have hkeys : ∀ (b1 b2 : Bool), TReach (wNode c.p base w7) c.i w7.top.rootKey p →
            ∀ n, wNode c.p base w7 p = some n →
            ∀ cv y, Klong.key cv y ∈ n.ks → ∀ q ∈ [(l, b1), (r, b2)], y ≠ (q : NodeId × Bool).1 := by
          intro b1 b2 hp n hn cv y hk
          have hk' := hP7 hp n hn cv y hk
          rw [hksS] at hk'
          have hlv := key_mem_newKlongs_liveAt pn.leaf c.i pairsS hsS cv y hk'
          rw [← hksS] at hlv
          have hyV := TReach.link hpV ⟨_, updN_self _ _ _, hlv⟩
          obtain ⟨_, h1, h2⟩ := hVlr y hyV
          intro q hq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with hq | hq <;> rw [hq] <;> assumption
        -- the chain, l and r
        have hPl : PathLen N c.i root l (D + 1 + 1) := by
          have := PathLen.link (hXdepth (D + 1) (by omega) (Nat.le_refl _)) (by rw [hXp]; exact hlink_l)
          exact this
        have hPr : PathLen N c.i root r (D + 1 + 1) := by
          have := PathLen.link (hXdepth (D + 1) (by omega) (Nat.le_refl _)) (by rw [hXp]; exact hlink_r)
          exact this
        have hlX : ∀ i, s ≤ i → i ≤ D + 1 → l ≠ X i := by
          intro i h1 h2 he
          have := PathLen.depth_unique hT _ _ _ hPl (by rw [he]; exact hXdepth i h1 h2)
          omega
        have hrX : ∀ i, s ≤ i → i ≤ D + 1 → r ≠ X i := by
          intro i h1 h2 he
          have := PathLen.depth_unique hT _ _ _ hPr (by rw [he]; exact hXdepth i h1 h2)
          omega
        have hlr' : l ≠ r := fun h => hc (hT.oneLink p cL p cR r hp hp ⟨pn, hpn, by rw [← h]; exact hpL⟩
          ⟨pn, hpn, hpR⟩).2
        have hx4 : ∀ y, w3.nodes.lookup y ≠ none → w4.nodes.lookup y = w3.nodes.lookup y := by
          intro y hy
          by_cases hyx : y = x
          · rw [hyx, h4x, hx3]
          · exact h4l y hyx
        have hw6lk : ∀ y, y ≠ m1 → w3.nodes.lookup y ≠ none → w6.nodes.lookup y = w3.nodes.lookup y := by
          intro y hym hy
          rw [h6n, h5n, lookup_append_single_ne _ _ _ _ (by rw [hw4m1]; exact hym), hx4 y hy]
        have hw6'n : ({ w6 with trail := s7 :: w6.trail } : W).nodes = w6.nodes := rfl
        have hw6'x : ({ w6 with trail := s7 :: w6.trail } : W).next = m1 + 2 := h6nx
        have hfr7' : ∀ z, z < m1 + 2 → (∀ i, s ≤ i → i ≤ D + 1 → z ≠ X i) →
            w7.nodes.lookup z = w6.nodes.lookup z := by
          intro z hz hnc
          have := hfr7 z (by rw [hw6'x]; exact hz) (fun i h1 h2 => hnc i h1 h2)
          rw [this]
        have hl7lk : w7.nodes.lookup l = some ln := by
          rw [hfr7' l (by omega) hlX, hw6lk l hlm1 (by rw [h3l]; simp), h3l]
        have hr7lk : w7.nodes.lookup r = some rn := by
          rw [hfr7' r (by omega) hrX, hw6lk r hrm1 (by rw [h3r]; simp), h3r]
        have hp7c : (w7.nodes.lookup p).isSome = true := hca7 p (by rw [hw6'n, hw6p]; rfl)
        obtain ⟨pn7, hp7⟩ : ∃ n, w7.nodes.lookup p = some n := Option.isSome_iff_exists.mp hp7c
        have hpt7 : w7.taken.contains p = false := by rw [ht7]; show w6.taken.contains p = false; rw [h6taken]; exact hpT
        have hwp7 : wNode c.p base w7 p = some pn7 := by
          simp only [wNode, hpt7, Bool.false_eq_true, ↓reduceIte, hp7]
        have hnone7 : pn7.lastTime = some c.i → ∀ cv y, Klong.key cv y ∈ pn7.ks → y ≠ l ∧ y ≠ r := by
          intro hlt7 cv y hk
          rcases (hRB2 hord hLO).1 (D + 1) (by omega) (Nat.le_refl _) with hR7p | hprev
          · rw [hXp] at hR7p
            have := hkeys false false hR7p pn7 hwp7 cv y hk
            exact ⟨this (l, false) (by simp), this (r, false) (by simp)⟩
          · exfalso
            rw [hXp, hp7, hNp] at hprev
            cases hprev
            obtain ⟨m, _, hm⟩ := KNode.lastTime_anchor _ _ hlt7
            exact time_not_mem_toPrev pn c.i hpos (List.mem_of_getElem? hm)
        refine writerWP_mono (writerWP_mergeCleanup_F p m1 c l r _ _ pn7 ln rn w7 hlr' (Ne.symm hpl)
          (Ne.symm hpr) hp7 hl7lk hr7lk hnone7) ?_
        rintro _ w8 ⟨h8top, h8v, h8tk, h8tl, h8tr, h8tkl, h8tkr, h8n, h8ul, h8ur⟩
        try simp only [writerWP_pure]
        -- the nodes reached after the merge, untaken
        have hN87 : ∀ y, y ≠ l → y ≠ r → wNode c.p base w8 y = wNode c.p base w7 y := by
          intro y hyl hyr
          simp only [wNode, h8tk y hyl hyr, h8n y hyl hyr]
        have hback : ∀ y, TReach (wNode c.p base w8) c.i w8.top.rootKey y →
            TReach (wNode c.p base w7) c.i w7.top.rootKey y := by
          rw [h8top]
          refine tReach_back_step (wNode c.p base w7) (wNode c.p base w8) c.i w7.top.rootKey ?_
          intro u cc z hu hlk
          have hul : u ≠ l := fun h => hl7 (by rw [← h]; exact hu)
          have hur : u ≠ r := fun h => hr7 (by rw [← h]; exact hu)
          unfold TLink at hlk ⊢
          rw [← hN87 u hul hur]
          exact hlk
        intro y hy
        have hy7 := hback y hy
        have hyl : y ≠ l := fun h => hl7 (by rw [← h]; exact hy7)
        have hyr : y ≠ r := fun h => hr7 (by rw [← h]; exact hy7)
        rw [h8tk y hyl hyr, ht7]
        show w6.taken.contains y = false
        rw [h6taken]
        rcases hreach7 y hy7 with h' | h'
        · rw [hNp] at h'
          rcases (hVlr y h').1 with h | h | h
          · exact hRt y h
          · rw [h]; exact hm1T
          · cases h
        · simp only at h'
          exact (hfree y (by have := h'.1; omega)).2
      intro s7
      generalize hw7 : ({ ({ w6 with trail := s7 :: w6.trail } : W) with
        nodes := upsert w6.nodes p (mergeParentNode pn c.i il cL m1 ir cR none) } : W) = w7
      have h7n : w7.nodes = upsert w6.nodes p (mergeParentNode pn c.i il cL m1 ir cR none) := by rw [← hw7]
      have h7t : w7.taken = w6.taken := by rw [← hw7]
      have h7top : w7.top = w6.top := by rw [← hw7]
      have h7v : w7.vals = w6.vals := by rw [← hw7]
      have hlk7 : w7.nodes.lookup p = some (mergeParentNode pn c.i il cL m1 ir cR none) := by
        rw [h7n, lookup_upsert]; simp
      have hcRl : cR ∈ pn.live.map Prod.fst := by
        have h := hpR
        rw [KNode.liveAt_of_times pn c.i hpt] at h
        exact List.mem_map.mpr ⟨_, h, rfl⟩
      have hlT3 : w3.taken.contains l = false := (hlrS l (Or.inl rfl)).1
      have hrT3 : w3.taken.contains r = false := (hlrS r (Or.inr rfl)).1
      have h6x : w6.nodes.lookup x = w3.nodes.lookup x := by
        rw [h6n, h5n, lookup_append_single_ne _ _ _ _ (by rw [hw4m1]; omega), h4x, hx3]
      have hlr : l ≠ r := fun h => by
        have := (hT.oneLink p cL p cR r hp hp ⟨pn, hpn, by rw [← h]; exact hpL⟩ ⟨pn, hpn, hpR⟩).2
        omega
      obtain ⟨hwf7, hlt7, ti7, hti7, hk7⟩ := mergeParentNode_last pn c.i il cL m1 ir cR none hpos hpwf
        hcRl hpt
      have hfacts7 := mergeParentNode_facts pn c.i il cL m1 ir cR none hpos hpt
      have h7lr : ∀ y, (y = l ∨ y = r) → w7.nodes.lookup y = w3.nodes.lookup y := by
        intro y hy
        have hyp : y ≠ p := by
          rcases hy with h | h
          · rw [h]; exact Ne.symm hpl
          · rw [h]; exact Ne.symm hpr
        have hym : y ≠ m1 := by rcases hy with h | h <;> rw [h] <;> omega
        rw [h7n, lookup_upsert]
        simp only [hyp, ↓reduceIte]
        by_cases hyx' : y = x
        · rw [hyx']; exact h6x
        · exact h6old y hyx' hym
      refine writerWP_mono (writerWP_and (writerWP_mergeCleanup_keep p m1 c.i c _ w7 _ (hne' _ _) hlk7
        (fun q hq c' hm => by
          rcases hchar1 c' q.1 hm with ⟨_, h⟩ | ⟨hold, h1, h2⟩
          · rcases hlr' _ _ q hq with h' | h' <;> rw [h'] at h
            · exact hlm1 h
            · exact hrm1 h
          · exact hnoOld q.1 (hlr' _ _ q hq) c' hold h1 h2))
        (writerWP_mergeCleanup_K p m1 c l r _ _ _ ln rn ti7 w7 hlr (Ne.symm hpl) (Ne.symm hpr) hlk7
          (by rw [h7lr l (Or.inl rfl)]; exact h3l) (by rw [h7lr r (Or.inr rfl)]; exact h3r) hlt7 hti7)) ?_
      intro _ w8 ⟨⟨h8top, _, h8t, h8l, pn8, h8p, h8leaf, h8sub⟩, _, _, h8v, _, h8tl, h8tr, h8tkl, h8tkr, _,
        h8ul, h8ur, pn8', h8p', hR8⟩
      have hpn8 : pn8' = pn8 := by rw [h8p] at h8p'; exact (Option.some.inj h8p').symm
      rw [hpn8] at hR8
      have h8fl : w8.taken.contains l = true ∨ w8.nodes.lookup l = some (unlinkedNode ln c.i) := by
        first | exact Or.inl (h8tl rfl) | exact Or.inr (h8ul rfl)
      have h8fr : w8.taken.contains r = true ∨ w8.nodes.lookup r = some (unlinkedNode rn c.i) := by
        first | exact Or.inl (h8tr rfl) | exact Or.inr (h8ur rfl)
      try simp only [writerWP_pure]
      have h8tc : ∀ y, y ≠ l → y ≠ r → w8.taken.contains y = w3.taken.contains y := by
        intro y hyl hyr; rw [h8t y (hcl' _ _ y hyl hyr), h7t, h6taken]
      have h8l' : ∀ y, y ≠ p → y ≠ l → y ≠ r → w8.nodes.lookup y = w6.nodes.lookup y := by
        intro y hyp hyl hyr; rw [h8l y hyp (hcl' _ _ y hyl hyr), h7n, lookup_upsert]; simp [hyp]
      have hN8m1 : wNode c.p base w8 m1 = some ⟨!!xn.leaf, newKlongs c.i first⟩ := by
        simp only [wNode, h8tc m1 (Ne.symm hlm1) (Ne.symm hrm1), hm1T, Bool.false_eq_true, ↓reduceIte]
        rw [h8l' m1 (Ne.symm hpm1) (Ne.symm hlm1) (Ne.symm hrm1), hw6m1]
      have hN8p : wNode c.p base w8 p = some pn8 := by
        simp only [wNode, h8tc p hpl hpr, hpT, Bool.false_eq_true, ↓reduceIte, h8p]
      have hndF : (first.map Prod.fst).Nodup := by rw [hfirst]; exact hndE
      have hother8 : ∀ y, y ≠ p → y ≠ l → y ≠ r → y ∉ [m1] → wNode c.p base w8 y = N y := by
        intro y hyp hyl hyr hym
        have hym' : y ≠ m1 := fun h => hym (by rw [h]; exact List.mem_singleton_self _)
        rw [← hNw3 y]
        unfold wNode
        rw [h8tc y hyl hyr, h8l' y hyp hyl hyr, h6old y (hyx y hyl hyr) hym']
      have hkeep8 : ∀ cc z, (cc, z) ∈ pn.liveAt c.i → cc ≠ cL → cc ≠ cR → (cc, z) ∈ pn8.liveAt c.i :=
        fun cc z hm hc1 hc2 => (h8sub cc z).mpr ((hparOne cc z).mpr (Or.inr ⟨hm, hc1, hc2⟩))
      have hnew8 : ∃ cc, (cc, m1) ∈ pn8.liveAt c.i :=
        ⟨cL, (h8sub cL m1).mpr ((hparOne cL m1).mpr (Or.inl ⟨rfl, rfl⟩))⟩
      intro y hy
      rw [h8top, h7top, h6top'] at hy
      have hreach := mergeV_reach N (wNode c.p base w8) c.i root p l r m1 none pn ln rn pn8 cL cR hT hp hpn
        hpL hpR hln hrn hN8p
        (fun cc z hm => by
          rcases (hparOne cc z).mp ((h8sub cc z).mp hm) with ⟨_, h⟩ | h
          · exact Or.inl h
          · exact Or.inr (Or.inr h))
        (fun m mn hm hmn' cc z hz => by
          rcases hm with hm | hm
          · rw [hm, hN8m1] at hmn'
            cases hmn'
            have hm2 := liveAt_newKlongs_mem (!!xn.leaf) c.i c.i first cc z hz
            rw [hfirst] at hm2
            have hz' : z ∈ (ln.live ++ rn.live).map Prod.snd := by
              rw [List.map_append, ← mergeList_map_snd (!xn.leaf) cR]
              exact List.mem_map.mpr ⟨(cc, z), hm2, rfl⟩
            obtain ⟨q', hq', he⟩ := List.mem_map.mp hz'
            rcases List.mem_append.mp hq' with h | h
            · exact Or.inl ⟨q'.1, by rw [KNode.liveAt_of_times ln c.i hlt, ← he]; exact h⟩
            · exact Or.inr ⟨q'.1, by rw [KNode.liveAt_of_times rn c.i hrt, ← he]; exact h⟩
          · cases hm)
        (fun y hyp hyl hyr hym _ => hother8 y hyp hyl hyr (by simp only [List.mem_singleton]; exact hym))
        hm1R (fun m hm => by cases hm) y hy
      obtain ⟨hyN, hyl, hyr⟩ := hreach
      rw [h8tc y hyl hyr]
      rcases hyN with h | h | h
      · exact hRt y h
      · rw [h]; exact hm1T
      · cases h
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
              (TReach N c.i root z ∨ z = m1 ∨ some z = some (m1 + 2)) ∧ z ≠ l ∧ z ≠ r) ∧
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
            exact this
          · rcases hsomeL (m1 + 2) g2 rfl c' z hm with ⟨_, h⟩ | ⟨_, h⟩ | ⟨h, _, _⟩
            · omega
            · omega
            · have := hlinksAll p c' z ⟨pn, hpn, h⟩; omega
        obtain ⟨hVt, hVlr, hvx⟩ := hV8 last hlast
        obtain ⟨htl, hleafl, _, _⟩ := mergeFullLast_liveAt pn c.i cL m1 cR _ last hlast hpt
        obtain ⟨_, hiffS⟩ := mergeFullLast_iff pn c.i cL m1 cR _ last hlast hpt
        obtain ⟨pairsL, hksL⟩ := mergeFullLast_ks pn c.i cL m1 cR _ last hlast
        have hlwf : klongsWf last.ks = true := by rw [hksL]; exact klongsWf_newKlongs c.i pairsL
        have hlasteq : (⟨pn.leaf, last.ks⟩ : KNode) = last := by
          cases last with
          | mk lf ks => simp only at hleafl; rw [hleafl]
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
        have hg2none : ∀ y g, some (m1 + 2, g2) = some (y, g) → g ≠ cR → pn.live.lookup g = none := by
          intro y g hyg hgc
          simp only [Option.some.injEq, Prod.mk.injEq] at hyg
          obtain ⟨_, rfl⟩ := hyg
          cases hlk : pn.live.lookup g2 with
          | none => rfl
          | some z =>
            exfalso
            have hm : (g2, z) ∈ pn.liveAt c.i := by
              rw [KNode.liveAt_of_times pn c.i hpt]; exact mem_of_lookup_nodup _ _ _ hlk
            rcases hadj g2 z hm with h | h
            · omega
            · have := hgU g2 z hm (by omega); omega
        obtain ⟨pairsS, hksS, hsS⟩ := mergeFullLast_sorted pn c.i cL m1 cR (some (m1 + 2, g2)) last
          hlast hg2none
        have hxe : (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode) = ⟨pn.leaf, newKlongs c.i pairsS⟩ := by
          rw [hNp, hksS]
        have hlastV : (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).lastVersion c.i = last := by
          rw [hxe, KNode.lastVersion_newKlongs_sorted _ _ _ hsS, ← hksS]; exact hlasteq
        have hlen2 : c.p.splitAbove < last.size → 2 ≤ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).live.length := by
          intro h
          rw [hxe, KNode.live_newKlongs_sorted _ _ _ hsS]
          have : last.size = pairsS.length + 1 := by simp [KNode.size, hksS, newKlongs]
          omega
        have hrangeL' : c.p.splitAbove < last.size → (Nn D).leaf = false →
            ∀ c' z, (c', z) ∈ (⟨(Nn (D + 1)).leaf, last.ks⟩ : KNode).live → 0 < c' →
            K (D + 1) ≤ c' ∧ ∀ c'' z', (c'', z') ∈ (Nn D).live → K (D + 1) < c'' → c' < c'' := by
          rw [hNp]; exact hrangeL m1 (some (m1 + 2, g2)) last hlast
            (mergeGOK_two _ ln rn c.i cR _ g2 yg (m1 + 2) hlt hrt hgs)
        have hspaceL' : (!compact && decide (last.size > c.p.splitAbove)) = true →
            (Nn D).leaf = false ∨ ((Nn (D + 1)).firstTime ≠ some c.i →
              ∀ i', s < i' → i' < D + 1 → ChainOrd c K Nn i') := by
          intro h
          have h' : c.p.splitAbove < last.size := by cases compact <;> simp at h <;> omega
          rw [hNp]; exact hspaceL m1 (some (m1 + 2, g2)) last hlast h'
        have hlevel := writerWP_handleFull_lastVF2 fuelR hfR c base w3.path s D X K Nn hsD hX hK hlinkK hrange hlen
          hwf htimes htop hdist hspace last compact hlwf htl hlastV hlen2 hrangeL' hspaceL'
          ({ w8 with trail := s9 :: w8.trail } : W)
          (by show w8.path = w3.path; rw [h8p, h7p, h6p, h5p, h4p])
          h8S2 h8T h8S4 h8S5 h8S6 (fun h0 _ => h8R0 h0) hW8
          (by rw [hXp, hNp]; exact hVt) (by rw [hNp]; exact hvx)
        rw [hXp] at hlevel
        have hlr : l < w8.next ∧ r < w8.next := ⟨by omega, by omega⟩
        have hpV : TReach (updN (wNode c.p base w8) p ⟨pn.leaf, last.ks⟩) c.i w8.top.rootKey p := by
          rw [← hXp]
          exact tReach_updN_self _ c.i _ _ _ h8T (h8S4 (D + 1) (by omega) (Nat.le_refl _))
        have hLO : LastOrd c K Nn D last := by
          intro hsp hql
          have hK1 : (K (D + 1), p) ∈ (Nn D).liveAt c.i := by
            have := hlinkK (D + 1) (by omega) (Nat.le_refl _)
            rw [show D + 1 - 1 = D by omega, hXp] at this; exact this
          have hND : N (X D) = some (Nn D) := by
            obtain ⟨hl3, ht3⟩ := hS2 D hsD (by omega)
            rw [← hNw3]; simp only [wNode, ht3, Bool.false_eq_true, ↓reduceIte, hl3]
          refine lastOrd_of_inner c K Nn D last (by rw [hNp]; exact hpleaf) ?_ hsp hql
          intro c' z hz
          rw [hNp] at hz
          exact mergeLast_ord c N root hRO (X D) (Nn D) (K (D + 1)) p pn (hS4 D hsD (by omega)) hND hql hK1
            hpn hpleaf hpt cL cR l r ln rn hclt hpL hpR hln hrn m1 (some (m1 + 2, g2)) last hlast
            (mergeGOrd_two _ ln rn c.i cR _ g2 yg (m1 + 2) hlt hrt hsortE (by omega) hgs)
            c' z hz
        have hshapeL := writerWP_handleFull_lastShape c w3.path s D X K Nn hsD hX hK hlinkK hrange hlen hord
          htimes htop hdist last compact ⟨pairsS, hksS, List.pairwise_map.mpr (hsS.imp (by intro a b hab; omega))⟩
          hlastV hlen2 hrangeL' hLO ({ w8 with trail := s9 :: w8.trail } : W)
          (by show w8.path = w3.path; rw [h8p, h7p, h6p, h5p, h4p])
          (fun i h1 h2 => ⟨(h8S2 i h1 h2).1, by have := hXlt i h1 h2; show X i < w8.next; omega⟩)
          (fun z hz => (h8S5 z hz).1)
        rw [hXp] at hshapeL
        have hcache11 := @state_handleFullWith_compact
          (cachedFromInvariant ({ w8 with trail := s9 :: w8.trail } : W))
          (fun q more => appendKlongs D q more) (D + 1) p [] last compact
          (fun q more => @state_appendKlongs (cachedFromInvariant ({ w8 with trail := s9 :: w8.trail } : W)) D q more)
          c ({ w8 with trail := s9 :: w8.trail } : W) (cachedFrom_refl _ c)
        refine writerWP_mono (writerWP_and (writerWP_and hlevel hshapeL) hcache11) ?_
        rintro _ w11 ⟨⟨⟨hT11, ⟨_, ht11, _, _, hv11⟩, hfr11, hreach11, hW11', hR11, hP11, hRB1, hRB2⟩, hSP11⟩,
          hca11⟩
        have hl11 : ¬ TReach (wNode c.p base w11) c.i w11.top.rootKey l := by
          intro h
          rcases hreach11 l h with h' | h'
          · rw [hNp] at h'; exact (hVlr l h').2.1 rfl
          · have := hlr.1; simp only at h'; omega
        have hr11 : ¬ TReach (wNode c.p base w11) c.i w11.top.rootKey r := by
          intro h
          rcases hreach11 r h with h' | h'
          · rw [hNp] at h'; exact (hVlr r h').2.2 rfl
          · have := hlr.2; simp only at h'; omega
        have hkeys : ∀ (b1 b2 : Bool), TReach (wNode c.p base w11) c.i w11.top.rootKey p →
            ∀ n, wNode c.p base w11 p = some n →
            ∀ cv y, Klong.key cv y ∈ n.ks → ∀ q ∈ [(l, b1), (r, b2)], y ≠ (q : NodeId × Bool).1 := by
          intro b1 b2 hp n hn cv y hk
          have hk' := hP11 hp n hn cv y hk
          rw [hksS] at hk'
          have hlv := key_mem_newKlongs_liveAt pn.leaf c.i pairsS hsS cv y hk'
          rw [← hksS] at hlv
          have hyV := TReach.link hpV ⟨_, updN_self _ _ _, hlv⟩
          obtain ⟨_, h1, h2⟩ := hVlr y hyV
          intro q hq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
          rcases hq with hq | hq <;> rw [hq] <;> assumption
        -- the chain, l and r
        have hPl : PathLen N c.i root l (D + 1 + 1) :=
          PathLen.link (hXdepth (D + 1) (by omega) (Nat.le_refl _)) (by rw [hXp]; exact hlink_l)
        have hPr : PathLen N c.i root r (D + 1 + 1) :=
          PathLen.link (hXdepth (D + 1) (by omega) (Nat.le_refl _)) (by rw [hXp]; exact hlink_r)
        have hlX : ∀ i, s ≤ i → i ≤ D + 1 → l ≠ X i := by
          intro i h1 h2 he
          have := PathLen.depth_unique hT _ _ _ hPl (by rw [he]; exact hXdepth i h1 h2)
          omega
        have hrX : ∀ i, s ≤ i → i ≤ D + 1 → r ≠ X i := by
          intro i h1 h2 he
          have := PathLen.depth_unique hT _ _ _ hPr (by rw [he]; exact hXdepth i h1 h2)
          omega
        have hlr' : l ≠ r := fun h => hc (hT.oneLink p cL p cR r hp hp ⟨pn, hpn, by rw [← h]; exact hpL⟩
          ⟨pn, hpn, hpR⟩).2
        have hx4 : ∀ y, w3.nodes.lookup y ≠ none → w4.nodes.lookup y = w3.nodes.lookup y := by
          intro y hy
          by_cases hyx : y = x
          · rw [hyx, h4x, hx3]
          · exact h4l y hyx
        have hw8lk : ∀ y, y ≠ m1 → y ≠ m1 + 2 → w3.nodes.lookup y ≠ none →
            w8.nodes.lookup y = w3.nodes.lookup y := by
          intro y hym hym2 hy
          rw [h8l, lookup_append_single_ne _ _ _ _ hym2, h6n, h5n,
            lookup_append_single_ne _ _ _ _ (by rw [hw4m1]; exact hym), hx4 y hy]
        have hw8'n : ({ w8 with trail := s9 :: w8.trail } : W).nodes = w8.nodes := rfl
        have hw8'x : ({ w8 with trail := s9 :: w8.trail } : W).next = m1 + 4 := h8nx
        have hfr11' : ∀ z, z < m1 + 4 → (∀ i, s ≤ i → i ≤ D + 1 → z ≠ X i) →
            w11.nodes.lookup z = w8.nodes.lookup z := by
          intro z hz hnc
          have := hfr11 z (by rw [hw8'x]; exact hz) (fun i h1 h2 => hnc i h1 h2)
          rw [this]
        have hl11lk : w11.nodes.lookup l = some ln := by
          rw [hfr11' l (by omega) hlX, hw8lk l hlm1 (by omega) (by rw [h3l]; simp), h3l]
        have hr11lk : w11.nodes.lookup r = some rn := by
          rw [hfr11' r (by omega) hrX, hw8lk r hrm1 (by omega) (by rw [h3r]; simp), h3r]
        have hp11c : (w11.nodes.lookup p).isSome = true := hca11 p (by rw [hw8'n, hw8p]; rfl)
        obtain ⟨pn11, hp11⟩ : ∃ n, w11.nodes.lookup p = some n := Option.isSome_iff_exists.mp hp11c
        have hpt11 : w11.taken.contains p = false := by
          rw [ht11]; show w8.taken.contains p = false; rw [h8taken]; exact hpT
        have hwp11 : wNode c.p base w11 p = some pn11 := by
          simp only [wNode, hpt11, Bool.false_eq_true, ↓reduceIte, hp11]
        have hnone11 : pn11.lastTime = some c.i → ∀ cv y, Klong.key cv y ∈ pn11.ks → y ≠ l ∧ y ≠ r := by
          intro hlt11 cv y hk
          rcases (hRB2 hord hLO).1 (D + 1) (by omega) (Nat.le_refl _) with hR11p | hprev
          · rw [hXp] at hR11p
            have := hkeys false false hR11p pn11 hwp11 cv y hk
            exact ⟨this (l, false) (by simp), this (r, false) (by simp)⟩
          · exfalso
            rw [hXp, hp11, hNp] at hprev
            cases hprev
            obtain ⟨m, _, hm⟩ := KNode.lastTime_anchor _ _ hlt11
            exact time_not_mem_toPrev pn c.i hpos (List.mem_of_getElem? hm)
        refine writerWP_mono (writerWP_mergeCleanup_F p m1 c l r _ _ pn11 ln rn w11 hlr' (Ne.symm hpl)
          (Ne.symm hpr) hp11 hl11lk hr11lk hnone11) ?_
        rintro _ w12 ⟨h12top, h12v, h12tk, h12tl, h12tr, h12tkl, h12tkr, h12n, h12ul, h12ur⟩
        try simp only [writerWP_pure]
        -- the nodes reached after the merge, untaken
        have hN1211 : ∀ y, y ≠ l → y ≠ r → wNode c.p base w12 y = wNode c.p base w11 y := by
          intro y hyl hyr
          simp only [wNode, h12tk y hyl hyr, h12n y hyl hyr]
        have hback : ∀ y, TReach (wNode c.p base w12) c.i w12.top.rootKey y →
            TReach (wNode c.p base w11) c.i w11.top.rootKey y := by
          rw [h12top]
          refine tReach_back_step (wNode c.p base w11) (wNode c.p base w12) c.i w11.top.rootKey ?_
          intro u cc z hu hlk
          have hul : u ≠ l := fun h => hl11 (by rw [← h]; exact hu)
          have hur : u ≠ r := fun h => hr11 (by rw [← h]; exact hu)
          unfold TLink at hlk ⊢
          rw [← hN1211 u hul hur]
          exact hlk
        intro y hy
        have hy11 := hback y hy
        have hyl : y ≠ l := fun h => hl11 (by rw [← h]; exact hy11)
        have hyr : y ≠ r := fun h => hr11 (by rw [← h]; exact hy11)
        rw [h12tk y hyl hyr, ht11]
        show w8.taken.contains y = false
        rw [h8taken]
        rcases hreach11 y hy11 with h' | h'
        · rw [hNp] at h'
          rcases (hVlr y h').1 with h | h | h
          · exact hRt y h
          · rw [h]; exact hm1T
          · simp only [Option.some.injEq] at h; rw [h]; exact hm2T
        · simp only at h'
          exact (hfree y (by have := h'.1; omega)).2
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
      have hcRl : cR ∈ pn.live.map Prod.fst := by
        have h := hpR
        rw [KNode.liveAt_of_times pn c.i hpt] at h
        exact List.mem_map.mpr ⟨_, h, rfl⟩
      have hlT3 : w3.taken.contains l = false := (hlrS l (Or.inl rfl)).1
      have hrT3 : w3.taken.contains r = false := (hlrS r (Or.inr rfl)).1
      have h6x : w6.nodes.lookup x = w3.nodes.lookup x := by
        rw [h6n, h5n, lookup_append_single_ne _ _ _ _ (by rw [hw4m1]; omega), h4x, hx3]
      have hlr : l ≠ r := fun h => by
        have := (hT.oneLink p cL p cR r hp hp ⟨pn, hpn, by rw [← h]; exact hpL⟩ ⟨pn, hpn, hpR⟩).2
        omega
      obtain ⟨hwf9, hlt9, ti9, hti9, hk9⟩ := mergeParentNode_last pn c.i il cL m1 ir cR (some (m1 + 2, g2))
        hpos hpwf hcRl hpt
      have hfacts9 := mergeParentNode_facts pn c.i il cL m1 ir cR (some (m1 + 2, g2)) hpos hpt
      have h9lr : ∀ y, (y = l ∨ y = r) → w9.nodes.lookup y = w3.nodes.lookup y := by
        intro y hy
        have hyp : y ≠ p := by
          rcases hy with h | h
          · rw [h]; exact Ne.symm hpl
          · rw [h]; exact Ne.symm hpr
        have hym : y ≠ m1 := by rcases hy with h | h <;> rw [h] <;> omega
        have hym2 : y ≠ m1 + 2 := by rcases hy with h | h <;> rw [h] <;> omega
        rw [h9n, lookup_upsert]
        simp only [hyp, ↓reduceIte]
        rw [h8l, lookup_append_single_ne _ _ _ _ hym2]
        by_cases hyx' : y = x
        · rw [hyx']; exact h6x
        · exact h6old y hyx' hym
      refine writerWP_mono (writerWP_and (writerWP_mergeCleanup_keep p m1 c.i c _ w9 _ (hne' _ _) hlk9
        (fun q hq c' hm => by
          rcases hchar2 (m1 + 2) g2 c' q.1 hm with ⟨_, h⟩ | ⟨_, h⟩ | ⟨hold, h1, h2⟩
          · rcases hlr' _ _ q hq with h' | h' <;> rw [h'] at h
            · exact hlm1 h
            · exact hrm1 h
          · rcases hlr' _ _ q hq with h' | h' <;> rw [h'] at h <;> omega
          · exact hnoOld q.1 (hlr' _ _ q hq) c' hold h1 h2))
        (writerWP_mergeCleanup_K p m1 c l r _ _ _ ln rn ti9 w9 hlr (Ne.symm hpl) (Ne.symm hpr) hlk9
          (by rw [h9lr l (Or.inl rfl)]; exact h3l) (by rw [h9lr r (Or.inr rfl)]; exact h3r) hlt9 hti9)) ?_
      intro _ w10 ⟨⟨h10top, _, h10t, h10l, pn10, h10p, h10leaf, h10sub⟩, _, _, h10v, _, h10tl, h10tr, h10tkl,
        h10tkr, _, h10ul, h10ur, pn10', h10p', hR10⟩
      have hpn10 : pn10' = pn10 := by rw [h10p] at h10p'; exact (Option.some.inj h10p').symm
      rw [hpn10] at hR10
      have h10fl : w10.taken.contains l = true ∨ w10.nodes.lookup l = some (unlinkedNode ln c.i) := by
        first | exact Or.inl (h10tl rfl) | exact Or.inr (h10ul rfl)
      have h10fr : w10.taken.contains r = true ∨ w10.nodes.lookup r = some (unlinkedNode rn c.i) := by
        first | exact Or.inl (h10tr rfl) | exact Or.inr (h10ur rfl)
      try simp only [writerWP_pure]
      have h10tc : ∀ y, y ≠ l → y ≠ r → w10.taken.contains y = w3.taken.contains y := by
        intro y hyl hyr; rw [h10t y (hcl' _ _ y hyl hyr), h9t, h8t, h7t, h6taken]
      have h10l' : ∀ y, y ≠ p → y ≠ l → y ≠ r → w10.nodes.lookup y = w8.nodes.lookup y := by
        intro y hyp hyl hyr; rw [h10l y hyp (hcl' _ _ y hyl hyr), h9n, lookup_upsert]; simp [hyp]
      have hm2T : w3.taken.contains (m1 + 2) = false := (hfree _ (by omega)).2
      have hTD : List.Pairwise (fun a b : Nat × NodeId => a.1 < b.1)
          ((mergeList (!xn.leaf) cR ln.live rn.live).take (((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2) ++ (mergeList (!xn.leaf) cR ln.live rn.live).drop (((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2)) := by
        rw [List.take_append_drop]; exact hsortE
      have hTDlt := (List.pairwise_append.mp hTD).2.2
      have hgD : (g2, yg) ∈ (mergeList (!xn.leaf) cR ln.live rn.live).drop (((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2) := List.mem_of_head? hgs
      have hN10m1 : wNode c.p base w10 m1 = some ⟨!!xn.leaf, newKlongs c.i first⟩ := by
        simp only [wNode, h10tc m1 (Ne.symm hlm1) (Ne.symm hrm1), hm1T, Bool.false_eq_true, ↓reduceIte]
        rw [h10l' m1 (Ne.symm hpm1) (Ne.symm hlm1) (Ne.symm hrm1), h8l,
          lookup_append_single_ne _ _ _ _ (by omega), hw6m1]
      have hN10m2 : wNode c.p base w10 (m1 + 2) = some ⟨!!xn.leaf, newKlongs c.i ks2⟩ := by
        simp only [wNode, h10tc (m1 + 2) (by omega) (by omega), hm2T, Bool.false_eq_true, ↓reduceIte]
        rw [h10l' _ (by omega) (by omega) (by omega), h8l, lookup_append_single_self _ _ _ hw6m2]
      have hN10p : wNode c.p base w10 p = some pn10 := by
        simp only [wNode, h10tc p hpl hpr, hpT, Bool.false_eq_true, ↓reduceIte, h10p]
      have hkeep10 : ∀ cc z, (cc, z) ∈ pn.liveAt c.i → cc ≠ cL → cc ≠ cR → (cc, z) ∈ pn10.liveAt c.i := by
        intro cc z hm hc1 hc2
        have hcg : cc ≠ g2 := by
          rcases hadj cc z hm with h | h
          · omega
          · have := hgU cc z hm (by omega); omega
        exact (h10sub cc z).mpr ((hparTwo (m1 + 2) g2 cc z).mpr (Or.inr (Or.inr ⟨hcg, hc1, hc2, hm⟩)))
      have hnew10a : ∃ cc, (cc, m1) ∈ pn10.liveAt c.i := ⟨cL, (h10sub cL m1).mpr
            ((hparTwo (m1 + 2) g2 cL m1).mpr (Or.inr (Or.inl ⟨by omega, rfl, rfl⟩)))⟩
      have hnew10b : ∃ cc, (cc, m1 + 2) ∈ pn10.liveAt c.i :=
        ⟨g2, (h10sub g2 (m1 + 2)).mpr ((hparTwo (m1 + 2) g2 g2 (m1 + 2)).mpr (Or.inl ⟨rfl, rfl⟩))⟩
      have hother10 : ∀ y, y ≠ p → y ≠ l → y ≠ r → y ∉ [m1, m1 + 2] → wNode c.p base w10 y = N y := by
        intro y hyp hyl hyr hym
        have hym1 : y ≠ m1 := fun h => hym (by rw [h]; exact List.mem_cons_self)
        have hym2 : y ≠ m1 + 2 := fun h => hym (by rw [h]; exact List.mem_cons_of_mem _ List.mem_cons_self)
        rw [← hNw3 y]
        unfold wNode
        rw [h10tc y hyl hyr, h10l' y hyp hyl hyr, h8l, lookup_append_single_ne _ _ _ _ hym2,
          h6old y (hyx y hyl hyr) hym1]
      intro y hy
      rw [h10top, h9top, h8top, h7top, h6top'] at hy
      have hreach := mergeV_reach N (wNode c.p base w10) c.i root p l r m1 (some (m1 + 2)) pn ln rn pn10
        cL cR hT hp hpn hpL hpR hln hrn hN10p
        (fun cc z hm => by
          rcases (hparTwo (m1 + 2) g2 cc z).mp ((h10sub cc z).mp hm) with ⟨_, h⟩ | ⟨_, _, h⟩ |
              ⟨_, h1, h2, h3⟩
          · exact Or.inr (Or.inl (by rw [h]))
          · exact Or.inl h
          · exact Or.inr (Or.inr ⟨h3, h1, h2⟩))
        (fun m mn hm hmn' cc z hz => by
          have hmem : (cc, z) ∈ first ++ ks2 := by
            rcases hm with hm | hm
            · rw [hm, hN10m1] at hmn'
              cases hmn'
              exact List.mem_append_left _ (liveAt_newKlongs_mem _ c.i c.i first cc z hz)
            · simp only [Option.some.injEq] at hm
              rw [hm, hN10m2] at hmn'
              cases hmn'
              exact List.mem_append_right _ (liveAt_newKlongs_mem _ c.i c.i ks2 cc z hz)
          have hz' : z ∈ (ln.live ++ rn.live).map Prod.snd := by
            rw [← hE]; exact List.mem_map.mpr ⟨(cc, z), hmem, rfl⟩
          obtain ⟨q', hq', he⟩ := List.mem_map.mp hz'
          rcases List.mem_append.mp hq' with h | h
          · exact Or.inl ⟨q'.1, by rw [KNode.liveAt_of_times ln c.i hlt, ← he]; exact h⟩
          · exact Or.inr ⟨q'.1, by rw [KNode.liveAt_of_times rn c.i hrt, ← he]; exact h⟩)
        (fun y hyp hyl hyr hym hym2 => hother10 y hyp hyl hyr (by
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          rintro (h | h)
          · exact hym h
          · exact hym2 (by rw [h])))
        hm1R (fun m hm => by
          simp only [Option.some.injEq] at hm
          rw [hm]; exact not_reach_fresh N c.i root _ hT (hfree _ (by omega)).1 (hfreshT _ (by omega)))
        y hy
      obtain ⟨hyN, hyl, hyr⟩ := hreach
      rw [h10tc y hyl hyr]
      rcases hyN with h | h | h
      · exact hRt y h
      · rw [h]; exact hm1T
      · simp only [Option.some.injEq] at h; rw [h]; exact hm2T


end SIS.Tree
