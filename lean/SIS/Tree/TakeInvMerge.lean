/-
The merge under a parent with room keeps the take-back's (B) (bergdb 024-12,
TP4; `TtReachedN`, TakeInvTree.lean): the two nodes merged, l and r, give way
to the new nodes, which the parent names; every node reached before but l and r
is reached after (`reach_merge`), and l and r, unlinked, keep no klong of the
transaction's time.
-/
import SIS.Tree.TakeInvUp
import SIS.Tree.RangeMergeW
import SIS.Tree.RangeMergeMade

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A merge at node-map level: under the reached parent p, its children l and rr
(by klongs cL and cR) give way to new nodes ms that p names; the live children
of l and rr are children of the new nodes; p keeps its other live klongs.
Every node reached before is reached after, or is l or rr, and then p is. -/
theorem reach_merge (N N' : NodeId → Option KNode) (t : Time) (r p l rr : NodeId) (ms : List NodeId)
    (pn ln rn pn' : KNode) (cL cR : Nat) (hT : TreeOK N t r) (hp : TReach N t r p)
    (hpn : N p = some pn) (hl : (cL, l) ∈ pn.liveAt t) (hrr : (cR, rr) ∈ pn.liveAt t)
    (hln : N l = some ln) (hrn : N rr = some rn) (hmsN : ∀ m ∈ ms, N m = none)
    (hN'p : N' p = some pn')
    (hpkeep : ∀ c z, (c, z) ∈ pn.liveAt t → c ≠ cL → c ≠ cR → (c, z) ∈ pn'.liveAt t)
    (hpnew : ∀ m ∈ ms, ∃ c, (c, m) ∈ pn'.liveAt t)
    (hcover : ∀ c z, ((c, z) ∈ ln.liveAt t ∨ (c, z) ∈ rn.liveAt t) →
      ∃ m ∈ ms, ∃ mn c', N' m = some mn ∧ (c', z) ∈ mn.liveAt t)
    (hother : ∀ y, y ≠ p → y ≠ l → y ≠ rr → y ∉ ms → N' y = N y) :
    ∀ u, TReach N t r u →
      ((u ≠ l ∧ u ≠ rr) ∧ TReach N' t r u) ∨ ((u = l ∨ u = rr) ∧ TReach N' t r p) := by
  have hlink_l : TLink N t p cL l := ⟨pn, hpn, hl⟩
  have hlink_r : TLink N t p cR rr := ⟨pn, hpn, hrr⟩
  have hlR : TReach N t r l := TReach.link hp hlink_l
  have hrR : TReach N t r rr := TReach.link hp hlink_r
  have hrootl : r ≠ l := fun h => hT.rootFree p cL hp (h ▸ hlink_l)
  have hrootr : r ≠ rr := fun h => hT.rootFree p cR hp (h ▸ hlink_r)
  -- a reached node linking l or rr is p
  have honlyP : ∀ a c, TReach N t r a → (TLink N t a c l → a = p ∧ c = cL) ∧
      (TLink N t a c rr → a = p ∧ c = cR) :=
    fun a c ha => ⟨fun h => hT.oneLink a c p cL l ha hp h hlink_l,
      fun h => hT.oneLink a c p cR rr ha hp h hlink_r⟩
  have hpl : p ≠ l := fun h => hT.no_self_link p cL hp (by rw [← h] at hlink_l; exact hlink_l)
  have hpr : p ≠ rr := fun h => hT.no_self_link p cR hp (by rw [← h] at hlink_r; exact hlink_r)
  intro u hu
  induction hu with
  | root => exact Or.inl ⟨⟨hrootl, hrootr⟩, TReach.root⟩
  | @link a c u ha hlk ih =>
    obtain ⟨an, han, hau⟩ := hlk
    have hlk' : TLink N t a c u := ⟨an, han, hau⟩
    by_cases hal : a = l ∨ a = rr
    · -- a child of l or rr: a child of a new node
      have hpR' : TReach N' t r p := by
        rcases ih with ⟨⟨h1, h2⟩, _⟩ | ⟨_, h⟩
        · rcases hal with h | h
          · exact absurd h h1
          · exact absurd h h2
        · exact h
      have hmem : (c, u) ∈ ln.liveAt t ∨ (c, u) ∈ rn.liveAt t := by
        rcases hal with h | h
        · rw [h, hln] at han; cases han; exact Or.inl hau
        · rw [h, hrn] at han; cases han; exact Or.inr hau
      obtain ⟨m, hm, mn, c', hmn, hmu⟩ := hcover c u hmem
      obtain ⟨cm, hcm⟩ := hpnew m hm
      have hmR : TReach N' t r m := TReach.link hpR' ⟨pn', hN'p, hcm⟩
      refine Or.inl ⟨⟨fun hul => ?_, fun hur => ?_⟩, TReach.link hmR ⟨mn, hmn, hmu⟩⟩
      · have := ((honlyP a c ha).1 (hul ▸ hlk')).1
        rcases hal with h | h
        · rw [h] at this; exact hpl this.symm
        · rw [h] at this; exact hpr this.symm
      · have := ((honlyP a c ha).2 (hur ▸ hlk')).1
        rcases hal with h | h
        · rw [h] at this; exact hpl this.symm
        · rw [h] at this; exact hpr this.symm
    · have haR' : TReach N' t r a := by
        rcases ih with ⟨_, h⟩ | ⟨h, _⟩
        · exact h
        · exact absurd h hal
      have hal' : a ≠ l ∧ a ≠ rr := ⟨fun h => hal (Or.inl h), fun h => hal (Or.inr h)⟩
      by_cases hap : a = p
      · rw [hap, hpn] at han
        cases han
        rw [hap] at haR' ha
        by_cases hcl : c = cL
        · rw [hcl] at hau
          exact Or.inr ⟨Or.inl (KNode.liveAt_fun pn t cL l u hl hau).symm, haR'⟩
        · by_cases hcr : c = cR
          · rw [hcr] at hau
            exact Or.inr ⟨Or.inr (KNode.liveAt_fun pn t cR rr u hrr hau).symm, haR'⟩
          · refine Or.inl ⟨⟨fun hul => ?_, fun hur => ?_⟩,
              TReach.link haR' ⟨pn', hN'p, hpkeep c u hau hcl hcr⟩⟩
            · rw [hul] at hau
              exact hcl ((honlyP p c hp).1 ⟨pn, hpn, hau⟩).2
            · rw [hur] at hau
              exact hcr ((honlyP p c hp).2 ⟨pn, hpn, hau⟩).2
      · have ham : a ∉ ms := fun h => by rw [hmsN a h] at han; cases han
        have hl2 : TLink N' t a c u := ⟨an, by rw [hother a hap hal'.1 hal'.2 ham]; exact han, hau⟩
        refine Or.inl ⟨⟨fun hul => ?_, fun hur => ?_⟩, TReach.link haR' hl2⟩
        · exact hap ((honlyP a c ha).1 (hul ▸ hlk')).1
        · exact hap ((honlyP a c ha).2 (hur ▸ hlk')).1

/-- (B) after a merge: l and rr without a klong of time t after. -/
theorem ttReachedN_merge (N N' : NodeId → Option KNode) (t : Time) (r p l rr : NodeId)
    (ms : List NodeId) (pn ln rn pn' : KNode) (cL cR : Nat) (hT : TreeOK N t r) (hp : TReach N t r p)
    (hpn : N p = some pn) (hl : (cL, l) ∈ pn.liveAt t) (hrr : (cR, rr) ∈ pn.liveAt t)
    (hln : N l = some ln) (hrn : N rr = some rn) (hmsN : ∀ m ∈ ms, N m = none)
    (hN'p : N' p = some pn')
    (hpkeep : ∀ c z, (c, z) ∈ pn.liveAt t → c ≠ cL → c ≠ cR → (c, z) ∈ pn'.liveAt t)
    (hpnew : ∀ m ∈ ms, ∃ c, (c, m) ∈ pn'.liveAt t)
    (hcover : ∀ c z, ((c, z) ∈ ln.liveAt t ∨ (c, z) ∈ rn.liveAt t) →
      ∃ m ∈ ms, ∃ mn c', N' m = some mn ∧ (c', z) ∈ mn.liveAt t)
    (hother : ∀ y, y ≠ p → y ≠ l → y ≠ rr → y ∉ ms → N' y = N y)
    (hfate : ∀ y yn, (y = l ∨ y = rr) → N' y = some yn → Klong.time t ∉ yn.ks)
    (hL : TtReachedN N t r) : TtReachedN N' t r := by
  have hR := reach_merge N N' t r p l rr ms pn ln rn pn' cL cR hT hp hpn hl hrr hln hrn hmsN hN'p
    hpkeep hpnew hcover hother
  have hlink_l : TLink N t p cL l := ⟨pn, hpn, hl⟩
  have hlink_r : TLink N t p cR rr := ⟨pn, hpn, hrr⟩
  have hpl : p ≠ l := fun h => hT.no_self_link p cL hp (by rw [← h] at hlink_l; exact hlink_l)
  have hpr : p ≠ rr := fun h => hT.no_self_link p cR hp (by rw [← h] at hlink_r; exact hlink_r)
  have hpR' : TReach N' t r p := by
    rcases hR p hp with ⟨_, h⟩ | ⟨h, _⟩
    · exact h
    · rcases h with h | h
      · exact absurd h hpl
      · exact absurd h hpr
  intro u un hu hm
  by_cases hulr : u = l ∨ u = rr
  · exact absurd hm (hfate u un hulr hu)
  · by_cases hums : u ∈ ms
    · obtain ⟨cm, hcm⟩ := hpnew u hums
      exact TReach.link hpR' ⟨pn', hN'p, hcm⟩
    · by_cases hup : u = p
      · rw [hup]; exact hpR'
      · rw [hother u hup (fun h => hulr (Or.inl h)) (fun h => hulr (Or.inr h)) hums] at hu
        rcases hR u (hL u un hu hm) with ⟨_, h⟩ | ⟨h, _⟩
        · exact h
        · exact absurd h hulr

/-! ## The writer's merge under a parent with room -/

/-- The merge's last step for two nodes the transaction did not make: both
unlinked, each keeps its klongs before the transaction only. -/
theorem writerWP_mergeCleanup_fate (A : NodeId × Bool → M (ForInStep PUnit)) (c : Ctx)
    (l r : NodeId) (ln rn : KNode) (w : W) (hlr : l ≠ r)
    (hl : w.nodes.lookup l = some ln) (hr : w.nodes.lookup r = some rn) :
    WriterWP (forIn [(l, false), (r, false)] PUnit.unit (fun q _ => if q.2 = true then A q else do
      unlink q.1
      pure (ForInStep.yield PUnit.unit))) c w (fun _ w' =>
      w'.nodes.lookup l = some (if ln.lastTime == some c.i then ln.toPrev (c.i - 1) else ln) ∧
      w'.nodes.lookup r = some (if rn.lastTime == some c.i then rn.toPrev (c.i - 1) else rn)) := by
  rw [List.forIn_cons]
  simp only [writerWP_bind, Bool.false_eq_true, ↓reduceIte]
  refine writerWP_mono (writerWP_unlink_fate l ln c w hl) ?_
  intro _ w1 ⟨_, _, _, h1x, h1l⟩
  simp only [writerWP_pure]
  rw [List.forIn_cons]
  simp only [writerWP_bind, Bool.false_eq_true, ↓reduceIte]
  refine writerWP_mono (writerWP_unlink_fate r rn c w1 (by rw [h1l r (Ne.symm hlr)]; exact hr)) ?_
  intro _ w2 ⟨_, _, _, h2x, h2l⟩
  simp only [writerWP_pure, List.forIn_nil]
  exact ⟨by rw [h2l l hlr]; exact h1x, h2x⟩

set_option maxHeartbeats 800000 in
/-- The merge's tail keeps the take-back's (B) (`TtReachedN`): two siblings l
and r under a reached inner parent p with room, which the transaction did not
make, merged into one node or two, both unlinked; the premises those of prover
cost's `writerWP_mergeTail_get`, l and r cached. -/
theorem writerWP_mergeTail_take (c : Ctx) (base : View BVal) (x : NodeId) (d : Nat) (p : NodeId)
    (pn xn : KNode) (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId)
    (rn : KNode) (ir : Nat) (cL cR : Nat) (N : NodeId → Option KNode) (root : NodeId) (nx : Nat)
    (w3 : W) (hT : TreeOK N c.i root) (hp : TReach N c.i root p) (hpn : N p = some pn)
    (hL : pn.ks[il]? = some (.key cL l)) (hLL : LastLive pn.ks pn.lastBitmap il cL)
    (hR : pn.ks[ir]? = some (.key cR r)) (hRL : LastLive pn.ks pn.lastBitmap ir cR)
    (hc : cL ≠ cR) (hxlr : x = l ∨ x = r) (hln : N l = some ln) (hrn : N r = some rn)
    (hroom : pn.size + 4 ≤ c.p.M)
    (hdead : ∀ il cL m1 ir cR m2, deadOver c.p (mergeParentNode pn c.i il cL m1 ir cR m2) = false)
    (hpwf : klongsWf pn.ks = true) (hpt : ∀ s, Klong.time s ∈ pn.ks → s ≤ c.i)
    (hch : ∀ cc z zn, (cc, z) ∈ pn.liveAt c.i → N z = some zn →
      zn.firstTime ≠ some c.i ∧ ∀ s, Klong.time s ∈ zn.ks → s ≤ c.i)
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
    (hpos : 0 < c.i) (hTt : TtReachedN N c.i root)
    (h3l : w3.nodes.lookup l = some ln) (h3r : w3.nodes.lookup r = some rn) :
    WriterWP (mergeTail c x d p pn xn leftSome l ln il r rn ir) c w3
      (fun _ w' => TtReachedN (wNode c.p base w') c.i w'.top.rootKey) := by
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
  obtain ⟨hlm, hlt⟩ := hch cL l ln hpL hln
  obtain ⟨hrm, hrt⟩ := hch cR r rn hpR hrn
  have hlm' : (ln.firstTime == some c.i) = false := by simpa using hlm
  have hrm' : (rn.firstTime == some c.i) = false := by simpa using hrm
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
  simp only [hlm', hrm', hcvL, hcvR, Bool.false_eq_true, ↓reduceIte]
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
  simp only [writerWP_bind, writerWP_modify]
  obtain ⟨xn3, hx3⟩ : ∃ n, w3.nodes.lookup x = some n := by
    rcases hxlr with h | h
    · rw [h]; exact ⟨ln, h3l⟩
    · rw [h]; exact ⟨rn, h3r⟩
  refine writerWP_mono (writerWP_and (writerWP_ghOf_frame x c _)
    (writerWP_ghOf_cached x xn3 c _ (by exact hx3) (fun _ w' => w'.nodes.lookup x = some xn3)
      (fun _ => by exact hx3))) ?_
  intro gh w4 ⟨⟨h4t, h4top, h4n, h4v, h4p, h4m, h4l⟩, h4x⟩
  simp only [writerWP_pure]
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
  have h6x : w6.nodes.lookup x = w3.nodes.lookup x := by
    rw [h6n, h5n, lookup_append_single_ne _ _ _ _ (by rw [h4n, h3next]; omega), h4x, hx3]
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
  have hlT3 : w3.taken.contains l = false := by
    have := hN3 ▸ hln
    unfold wNode at this
    split at this
    · cases this
    · rename_i h; simpa using h
  have hrT3 : w3.taken.contains r = false := by
    have := hN3 ▸ hrn
    unfold wNode at this
    split at this
    · cases this
    · rename_i h; simpa using h
  have hlr : l ≠ r := fun h => by
    have := (hT.oneLink p cL p cR r hp hp ⟨pn, hpn, by rw [← h]; exact hpL⟩ hlink_r).2
    omega
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
  have hcl : ∀ y, (∀ q ∈ [(l, false), (r, false)], y ≠ (q : NodeId × Bool).1) ↔ (y ≠ l ∧ y ≠ r) := by
    intro y; simp
  have hoBool : ∀ q ∈ [(l, false), (r, false)], (q : NodeId × Bool).2 = false := by simp
  have hyx : ∀ y, y ≠ l → y ≠ r → y ≠ x := by
    intro y hyl hyr; rcases hxlr with h | h <;> rw [h] <;> assumption
  have hpL' : (cL, l) ∈ pn.liveAt c.i := hpL
  have hadjR : ∀ q ∈ pn.liveAt c.i, cL < q.1 → cR ≤ q.1 :=
    fun q hq hlt => (hadj q.1 q.2 hq).resolve_left (by omega)
  have hhead : (!xn.leaf) = true → ∃ y, rn.live.head? = some (0, y) := by
    intro h
    obtain ⟨y0, tl, he⟩ := hrhead h
    exact ⟨y0, by rw [he]; rfl⟩
  cases hsec : second with
  | none =>
    rw [hsec] at hmkd
    have hfirst : first = mergeList (!xn.leaf) cR ln.live rn.live := splitMerged_one _ _ _ _ hmkd
    simp only [writerWP_bind, writerWP_pure]
    refine writerWP_mono (writerWP_mergeParent_room p pn (d - 1) il cL m1 ir cR none c w6 hw6p hroom
      (hdead _ _ _ _ _ _)) ?_
    intro _ w7 ⟨h7n, h7t, h7top, _, h7v, _, _, _⟩
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
    refine writerWP_mono (writerWP_and (writerWP_mergeCleanup_unmadeV _ c [(l, false), (r, false)] w7 hoBool)
      (writerWP_mergeCleanup_fate _ c l r ln rn w7 hlr (by rw [h7lr l (Or.inl rfl)]; exact h3l)
        (by rw [h7lr r (Or.inr rfl)]; exact h3r))) ?_
    intro _ w8 ⟨⟨h8t, h8top, _, h8v, h8l⟩, h8fl, h8fr⟩
    try simp only [writerWP_pure]
    have h8t' : w8.taken = w3.taken := by rw [h8t, h7t, h6taken]
    have h8l' : ∀ y, y ≠ l → y ≠ r → w8.nodes.lookup y =
        (upsert w6.nodes p (mergeParentNode pn c.i il cL m1 ir cR none)).lookup y := by
      intro y hyl hyr; rw [h8l y ((hcl y).mpr ⟨hyl, hyr⟩), h7n]
    have h8v' : w8.vals = w3.vals := by rw [h8v, h7v, h6v, h5v, h4v]
    have hV8 : wValue base w8 = wValue base w3 := wValue_congr' base w8 w3 h8t' h8v'
    have hN8m1 : wNode c.p base w8 m1 = some ⟨!!xn.leaf, newKlongs c.i first⟩ := by
      simp only [wNode, h8t', hm1T, Bool.false_eq_true, ↓reduceIte]
      rw [h8l' m1 (Ne.symm hlm1) (Ne.symm hrm1), lookup_upsert]
      simp only [Ne.symm hpm1, ↓reduceIte, hw6m1]
    have hN8p : wNode c.p base w8 p = some (mergeParentNode pn c.i il cL m1 ir cR none) := by
      simp only [wNode, h8t', hpT, Bool.false_eq_true, ↓reduceIte]
      rw [h8l' p hpl hpr, lookup_upsert]
      simp
    have hndF : (first.map Prod.fst).Nodup := by rw [hfirst]; exact hndE
    rw [h8top, h7top, h6top']
    refine ttReachedN_merge N (wNode c.p base w8) c.i root p l r [m1] pn ln rn
      (mergeParentNode pn c.i il cL m1 ir cR none) cL cR hT hp hpn hpL hpR hln hrn
      (by intro m hm; simp only [List.mem_singleton] at hm; rw [hm]; exact hm1N) hN8p
      (fun cc z hm hc1 hc2 => (hparOne cc z).mpr (Or.inr ⟨hm, hc1, hc2⟩))
      (fun m hm => by
        simp only [List.mem_singleton] at hm
        rw [hm]
        exact ⟨cL, (hparOne cL m1).mpr (Or.inl ⟨rfl, rfl⟩)⟩)
      ?_ ?_ ?_ hTt
    · intro cc z hz
      have hzs : z ∈ (mergeList (!xn.leaf) cR ln.live rn.live).map Prod.snd := by
        rw [mergeList_map_snd, List.mem_append]
        rcases hz with h | h
        · left; rw [KNode.liveAt_of_times ln c.i hlt] at h; exact List.mem_map.mpr ⟨_, h, rfl⟩
        · right; rw [KNode.liveAt_of_times rn c.i hrt] at h; exact List.mem_map.mpr ⟨_, h, rfl⟩
      obtain ⟨⟨c', z'⟩, hq, hqz⟩ := List.mem_map.mp hzs
      simp only at hqz
      rw [← hqz]
      refine ⟨m1, List.mem_singleton_self _, _, c', hN8m1, ?_⟩
      rw [mrg_newKlongs_liveAt_iff _ c.i first hndF, hfirst]
      exact hq
    · intro y hyp hyl hyr hym
      have hym' : y ≠ m1 := fun h => hym (by rw [h]; exact List.mem_singleton_self _)
      rw [← hNw3 y]
      apply wNode_congr _ _ _ _ _ h8t'
      rw [h8l' y hyl hyr, lookup_upsert]
      simp only [hyp, ↓reduceIte]
      exact h6old y (hyx y hyl hyr) hym'
    · intro y yn hy hyn
      rcases hy with hy | hy <;> rw [hy] at hyn
      · simp only [wNode, h8t', hlT3, Bool.false_eq_true, ↓reduceIte, h8fl, Option.some.injEq] at hyn
        rw [← hyn]
        exact unlinked_no_time ln c.i hpos (hwfN _ ln hln) hlt
      · simp only [wNode, h8t', hrT3, Bool.false_eq_true, ↓reduceIte, h8fr, Option.some.injEq] at hyn
        rw [← hyn]
        exact unlinked_no_time rn c.i hpos (hwfN _ rn hrn) hrt
  | some ksg =>
    obtain ⟨ks2, g2⟩ := ksg
    rw [hsec] at hmkd
    have hE : (first ++ ks2).map Prod.snd = (ln.live ++ rn.live).map Prod.snd := by
      rw [splitMerged_map_snd _ _ _ first ks2 g2 hmkd, mergeList_map_snd, List.map_append]
    simp only [writerWP_bind, writerWP_pure]
    refine writerWP_mono (writerWP_newKey_frame _ _ _ _ c w6) ?_
    intro m2 w7 ⟨hm2, h7n, h7t, h7top, _, h7v, _, _⟩
    have hm2' : m2 = m1 + 2 := by rw [hm2, h6next, h5next, hw4m1]
    subst hm2'
    refine writerWP_mono (writerWP_setMadeFor_frame _ _ c w7) ?_
    intro _ w8 ⟨h8n, h8t, h8top, _, h8v, _⟩
    try simp only [writerWP_pure]
    have hw6m2 : w6.nodes.lookup (m1 + 2) = none := by
      rw [h6n, h5n, lookup_append_single_ne _ _ _ _ (by rw [hw4m1]; omega),
        hlk4 _ (by omega)]
      exact hnone3 _ (by omega)
    have hw8p : w8.nodes.lookup p = some pn := by
      rw [h8n, h7n, h6next, h5next, hw4m1, lookup_append_single_ne _ _ _ _ (by omega)]
      exact hw6p
    refine writerWP_mono (writerWP_mergeParent_room p pn (d - 1) il cL m1 ir cR (some (m1 + 2, g2)) c
      w8 hw8p hroom (hdead _ _ _ _ _ _)) ?_
    intro _ w9 ⟨h9n, h9t, h9top, _, h9v, _, _, _⟩
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
      rw [h8n, h7n, h6next, h5next, hw4m1, lookup_append_single_ne _ _ _ _ hym2]
      by_cases hyx' : y = x
      · rw [hyx']; exact h6x
      · exact h6old y hyx' hym
    refine writerWP_mono (writerWP_and (writerWP_mergeCleanup_unmadeV _ c [(l, false), (r, false)] w9 hoBool)
      (writerWP_mergeCleanup_fate _ c l r ln rn w9 hlr (by rw [h9lr l (Or.inl rfl)]; exact h3l)
        (by rw [h9lr r (Or.inr rfl)]; exact h3r))) ?_
    intro _ w10 ⟨⟨h10t, h10top, _, h10v, h10l⟩, h10fl, h10fr⟩
    try simp only [writerWP_pure]
    have h10t' : w10.taken = w3.taken := by rw [h10t, h9t, h8t, h7t, h6taken]
    have h8l : ∀ y, w8.nodes.lookup y = (w6.nodes ++ [(m1 + 2,
        ({ leaf := !!xn.leaf, ks := newKlongs c.i ks2 } : KNode))]).lookup y := by
      intro y; rw [h8n, h7n, h6next, h5next, hw4m1]
    have h10l' : ∀ y, y ≠ l → y ≠ r → w10.nodes.lookup y =
        (upsert w8.nodes p (mergeParentNode pn c.i il cL m1 ir cR (some (m1 + 2, g2)))).lookup y := by
      intro y hyl hyr; rw [h10l y ((hcl y).mpr ⟨hyl, hyr⟩), h9n]
    have hm2T : w3.taken.contains (m1 + 2) = false := (hfree _ (by omega)).2
    have h10v' : w10.vals = w3.vals := by rw [h10v, h9v, h8v, h7v, h6v, h5v, h4v]
    have hV10 : wValue base w10 = wValue base w3 := wValue_congr' base w10 w3 h10t' h10v'
    -- the halves of the merged klongs
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
    have hTD : List.Pairwise (fun a b : Nat × NodeId => a.1 < b.1)
        ((mergeList (!xn.leaf) cR ln.live rn.live).take (((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2) ++ (mergeList (!xn.leaf) cR ln.live rn.live).drop (((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2)) := by
      rw [List.take_append_drop]; exact hsortE
    have hTDlt := (List.pairwise_append.mp hTD).2.2
    have hgD : (g2, yg) ∈ (mergeList (!xn.leaf) cR ln.live rn.live).drop (((mergeList (!xn.leaf) cR ln.live rn.live).length + 1) / 2) := List.mem_of_head? hgs
    have hN10m1 : wNode c.p base w10 m1 = some ⟨!!xn.leaf, newKlongs c.i first⟩ := by
      simp only [wNode, h10t', hm1T, Bool.false_eq_true, ↓reduceIte]
      rw [h10l' m1 (Ne.symm hlm1) (Ne.symm hrm1), lookup_upsert]
      simp only [Ne.symm hpm1, ↓reduceIte]
      rw [h8l, lookup_append_single_ne _ _ _ _ (by omega), hw6m1]
    have hN10m2 : wNode c.p base w10 (m1 + 2) = some ⟨!!xn.leaf, newKlongs c.i ks2⟩ := by
      simp only [wNode, h10t', hm2T, Bool.false_eq_true, ↓reduceIte]
      rw [h10l' _ (by omega) (by omega), lookup_upsert]
      simp only [show m1 + 2 ≠ p by omega, ↓reduceIte]
      rw [h8l, lookup_append_single_self _ _ _ hw6m2]
    have hN10p : wNode c.p base w10 p = some (mergeParentNode pn c.i il cL m1 ir cR (some (m1 + 2, g2))) := by
      simp only [wNode, h10t', hpT, Bool.false_eq_true, ↓reduceIte]
      rw [h10l' p hpl hpr, lookup_upsert]
      simp
    rw [h10top, h9top, h8top, h7top, h6top']
    refine ttReachedN_merge N (wNode c.p base w10) c.i root p l r [m1, m1 + 2] pn ln rn
      (mergeParentNode pn c.i il cL m1 ir cR (some (m1 + 2, g2))) cL cR hT hp hpn hpL hpR hln hrn
      (by
        intro m hm
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hm
        rcases hm with hm | hm <;> rw [hm]
        · exact hm1N
        · exact (hfree _ (by omega)).1) hN10p ?_ ?_ ?_ ?_ ?_ hTt
    · intro cc z hm hc1 hc2
      have hcg : cc ≠ g2 := by
        rcases hadj cc z hm with h | h
        · omega
        · have := hgU cc z hm (by omega); omega
      exact (hparTwo (m1 + 2) g2 cc z).mpr (Or.inr (Or.inr ⟨hcg, hc1, hc2, hm⟩))
    · intro m hm
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hm
      rcases hm with hm | hm <;> rw [hm]
      · exact ⟨cL, (hparTwo (m1 + 2) g2 cL m1).mpr (Or.inr (Or.inl ⟨by omega, rfl, rfl⟩))⟩
      · exact ⟨g2, (hparTwo (m1 + 2) g2 g2 (m1 + 2)).mpr (Or.inl ⟨rfl, rfl⟩)⟩
    · intro cc z hz
      have hzs : z ∈ (first ++ ks2).map Prod.snd := by
        rw [hE, List.map_append, List.mem_append]
        rcases hz with h | h
        · left; rw [KNode.liveAt_of_times ln c.i hlt] at h; exact List.mem_map.mpr ⟨_, h, rfl⟩
        · right; rw [KNode.liveAt_of_times rn c.i hrt] at h; exact List.mem_map.mpr ⟨_, h, rfl⟩
      rw [List.map_append, List.mem_append] at hzs
      rcases hzs with h | h
      · obtain ⟨⟨c', z'⟩, hq, hqz⟩ := List.mem_map.mp h
        simp only at hqz
        rw [← hqz]
        exact ⟨m1, List.mem_cons_self, _, c', hN10m1,
          (mrg_newKlongs_liveAt_iff _ c.i first hnd1 c' z').mpr hq⟩
      · obtain ⟨⟨c', z'⟩, hq, hqz⟩ := List.mem_map.mp h
        simp only at hqz
        rw [← hqz]
        exact ⟨m1 + 2, List.mem_cons_of_mem _ List.mem_cons_self, _, c', hN10m2,
          (mrg_newKlongs_liveAt_iff _ c.i ks2 hnd2 c' z').mpr hq⟩
    · intro y hyp hyl hyr hym
      have hym1 : y ≠ m1 := fun h => hym (by rw [h]; exact List.mem_cons_self)
      have hym2 : y ≠ m1 + 2 := fun h => hym (by rw [h]; exact List.mem_cons_of_mem _ List.mem_cons_self)
      rw [← hNw3 y]
      apply wNode_congr _ _ _ _ _ h10t'
      rw [h10l' y hyl hyr, lookup_upsert]
      simp only [hyp, ↓reduceIte]
      rw [h8l, lookup_append_single_ne _ _ _ _ hym2]
      exact h6old y (hyx y hyl hyr) hym1
    · intro y yn hy hyn
      rcases hy with hy | hy <;> rw [hy] at hyn
      · simp only [wNode, h10t', hlT3, Bool.false_eq_true, ↓reduceIte, h10fl, Option.some.injEq] at hyn
        rw [← hyn]
        exact unlinked_no_time ln c.i hpos (hwfN _ ln hln) hlt
      · simp only [wNode, h10t', hrT3, Bool.false_eq_true, ↓reduceIte, h10fr, Option.some.injEq] at hyn
        rw [← hyn]
        exact unlinked_no_time rn c.i hpos (hwfN _ rn hrn) hrt


/-- The writer's merge keeps the take-back's (B) (`TtReachedN`): x at depth d
merged with a sibling under a reached inner parent with room, neither made by
the transaction; the premises those of prover cost's `writerWP_merge_get`. -/
theorem writerWP_merge_take (x : NodeId) (d : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (w : W)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hpar : ∀ p, (w.path[d - 1]?).map (·.2) = some p →
      TReach (wNode c.p base w) c.i w.top.rootKey p ∧ ∃ pn, wNode c.p base w p = some pn ∧
        pn.leaf = false ∧ pn.size + 4 ≤ c.p.M ∧
        (∀ il cL m1 ir cR m2, deadOver c.p (mergeParentNode pn c.i il cL m1 ir cR m2) = false) ∧
        klongsWf pn.ks = true ∧ (∀ s, Klong.time s ∈ pn.ks → s ≤ c.i) ∧
        ∀ cc z zn, (cc, z) ∈ pn.liveAt c.i → wNode c.p base w z = some zn →
          zn.firstTime ≠ some c.i ∧ ∀ s, Klong.time s ∈ zn.ks → s ≤ c.i)
    (hRt : ∀ y, TReach (wNode c.p base w) c.i w.top.rootKey y → w.taken.contains y = false)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next))
    (hbaseF : ∀ z, w.next ≤ z → knodeOf c.p base z = none)
    (hfreshT : ∀ z, w.next ≤ z → ∀ u c', TReach (wNode c.p base w) c.i w.top.rootKey u →
      ¬ TLink (wNode c.p base w) c.i u c' z)
    (hR : RangeOrder (wNode c.p base w) c.i w.top.rootKey) (hcap : 1 ≤ c.p.mergeMax)
    (htimesN : ∀ y yn, wNode c.p base w y = some yn → ∀ s, Klong.time s ∈ yn.ks → s ≤ c.i)
    (hwfN : ∀ y yn, wNode c.p base w y = some yn → klongsWf yn.ks = true)
    (hpos : 0 < c.i) (hTt : TtReachedN (wNode c.p base w) c.i w.top.rootKey) :
    WriterWP (merge x d) c w (fun _ w' => TtReachedN (wNode c.p base w') c.i w'.top.rootKey) := by
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
    obtain ⟨hpR, pn0, hpn0, hpleaf, hroom, hdead, hpwf, hpt, hch⟩ := hpar e.2 (by rw [he]; rfl)
    refine writerWP_mono (writerWP_getNode_all e.2 c w base hvc) ?_
    intro pn w1 ⟨hr1, hlk1, hwn1, hpre1, hsrc1⟩
    rw [hwn1 (hRt _ hpR)] at hpn0
    cases hpn0
    -- the tail from any state that reads as w
    have hpn : wNode c.p base w e.2 = some pn0 := hwn1 (hRt _ hpR)
    have hpRS := tReach_reachS _ c.i _ _ hpR
    have tailOK : ∀ (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId)
        (rn : KNode) (ir cL cR : Nat) (xn : KNode) (w3 : W), ReadsAs c.p base w w3 →
        w1.nodes <+: w3.nodes → (∀ z, (w3.nodes.lookup z).isSome = true → z < w.next) →
        pn0.ks[il]? = some (.key cL l) → LastLive pn0.ks pn0.lastBitmap il cL →
        pn0.ks[ir]? = some (.key cR r) → LastLive pn0.ks pn0.lastBitmap ir cR → cL < cR →
        (∀ cc z, (cc, z) ∈ pn0.liveAt c.i → cc ≤ cL ∨ cR ≤ cc) →
        ln.leaf = xn.leaf → rn.leaf = xn.leaf →
        (x = l ∨ x = r) → wNode c.p base w l = some ln → wNode c.p base w r = some rn →
        w3.nodes.lookup l = some ln → w3.nodes.lookup r = some rn →
        WriterWP (mergeTail c x d e.2 pn0 xn leftSome l ln il r rn ir) c w3
          (fun _ w' => TtReachedN (wNode c.p base w') c.i w'.top.rootKey) := by
      intro leftSome l ln il r rn ir cL cR xn w3 hr3 hpre3 hsrc3 hL hLL hR' hRL hclt hadj hll hrl
        hxlr hln hrn h3l h3r
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
      refine writerWP_mono (writerWP_mergeTail_take c base x d e.2 pn0 xn leftSome l ln il r rn ir cL cR
        (wNode c.p base w) w.top.rootKey w.next w3 hT hpR hpn hL hLL hR' hRL (by omega) hxlr
        hln hrn hroom hdead hpwf hpt hch hr3.1 (by rw [hr3.2.1]) hr3.2.2.2.2
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
        htimesN hwfN hpos hTt h3l h3r) ?_
      intro _ w' h
      exact h
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
    refine writerWP_mono (writerWP_getNode_all x c w1 base hvc) ?_
    intro xn w2 ⟨hr2, hlk2, hwn2, hpre2, hsrc2⟩
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
            wb.nodes.lookup x = some xn →
            (∀ z, (wb.nodes.lookup z).isSome = true → z < w.next) →
            LastLive pn0.ks pn0.lastBitmap ia0 cva → cx < cva →
            (mergeIdx pn0 cx).2.1 = some (ia0, cva) →
            WriterWP (do
              let __x ← sibling e.2 pn0 ia0 !xn.leaf
              mergeTail c x d e.2 pn0 xn false x xn ix __x.1 __x.2 ia0) c wb
              (fun _ w' => TtReachedN (wNode c.p base w') c.i w'.top.rootKey) := by
          intro wb ia0 cva hrb hpreb hxb hsrcb hLa hax hia
          rw [writerWP_bind]
          refine writerWP_mono (writerWP_sibling_leaf e.2 pn0 ia0 (!xn.leaf) c wb base hvc) ?_
          rintro ⟨rs, rsn⟩ w4 ⟨hs1, hr4, hlk4s, hwn4, hpre4, hsrc4, hsl⟩
          obtain ⟨hka, hrn, hr04, hpre14, hsrc04⟩ :=
            hsib wb ia0 cva (rs, rsn) w4 hrb hpreb hsrcb hLa hs1 hr4 hpre4 hsrc4 hwn4
          have hmin := mergeIdx_right_min pn0 cx ia0 cva hia
          exact tailOK false x xn ix rs rsn ia0 cx cva xn w4 hr04 hpre14 hsrc04 hkx hLx hka hLa
            hax (by
              intro cc z hm
              rcases Nat.lt_or_ge cx cc with h | h
              · have hm' : (cc, z) ∈ pn0.live := by rw [← KNode.liveAt_of_times pn0 c.i hpt]; exact hm
                exact Or.inr (hmin cc z hm' h)
              · exact Or.inl h) rfl (by rw [hsl]; simp) (Or.inl rfl) hxn hrn
              (lookup_of_prefix _ _ hpre4 x xn hxb) hlk4s
        split
        · rename_i ib0 cvb
          obtain ⟨hLb, hbx⟩ := hMb ib0 cvb rfl
          simp only [writerWP_bind]
          refine writerWP_mono (writerWP_sibling_leaf e.2 pn0 ib0 (!xn.leaf) c w2 base hvc) ?_
          rintro ⟨ls, lsn⟩ w3 ⟨hs1, hr3, hlk3s, hwn3, hpre3, hsrc3, hsl⟩
          obtain ⟨hkb, hln, hr03, hpre13, hsrc03⟩ :=
            hsib w2 ib0 cvb (ls, lsn) w3 hr02 hpre02 hsrc02 hLb hs1 hr3 hpre3 hsrc3 hwn3
          refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_)
          · show WriterWP (mergeTail c x d e.2 pn0 xn true ls lsn ib0 x xn ix) c w3 _
            have hmax := mergeIdx_left_max pn0 cx ib0 cvb (by rw [hmi])
            exact tailOK true ls lsn ib0 x xn ix cvb cx xn w3 hr03 hpre13 hsrc03 hkb hLb hkx hLx
              hbx (by
                intro cc z hm
                rcases Nat.lt_or_ge cc cx with h | h
                · have hm' : (cc, z) ∈ pn0.live := by rw [← KNode.liveAt_of_times pn0 c.i hpt]; exact hm
                  exact Or.inl (hmax cc z hm' h)
                · exact Or.inr h) (by rw [hsl]; simp) rfl (Or.inr rfl) hln hxn hlk3s
                (lookup_of_prefix _ _ hpre3 x xn hlk2)
          · rw [writerWP_bind, writerWP_pure]
            dsimp only
            split
            · rename_i ia0 cva _
              obtain ⟨hLa, hax⟩ := hMa ia0 cva rfl
              exact hright w3 ia0 cva hr03 hpre13 (lookup_of_prefix _ _ hpre3 x xn hlk2) hsrc03 hLa hax
                (by rw [hmi])
            · exact writerWP_throw _ _ _ _
        · rw [writerWP_bind, writerWP_pure]
          dsimp only
          split
          · rename_i ia0 cva
            obtain ⟨hLa, hax⟩ := hMa ia0 cva rfl
            exact hright w2 ia0 cva hr02 hpre02 hlk2 hsrc02 hLa hax (by rw [hmi])
          · exact writerWP_throw _ _ _ _
      · exact writerWP_throw _ _ _ _
    · exact writerWP_throw _ _ _ _
  · exact writerWP_throw _ _ _ _

/-! ## The merge of nodes the transaction made or not -/

/-- One step of the merge's last loop: q.1 taken back (its parent retargeted) or
unlinked; another node but the parent keeps its node, a node taken back stays
so, and the parent stays cached. -/
theorem writerWP_mergeCleanup_step (p m1 : NodeId) (c : Ctx) (q : NodeId × Bool) (w : W)
    (pn qn : KNode) (hp : w.nodes.lookup p = some pn) (hq : w.nodes.lookup q.1 = some qn)
    (hqp : q.1 ≠ p) :
    WriterWP ((if q.2 = true then (do
        retarget p q.1 m1
        takenBack q.1
        note "merge.takeback"
        pure (ForInStep.yield PUnit.unit)) else (do
        unlink q.1
        pure (ForInStep.yield PUnit.unit))) : M (ForInStep PUnit)) c w (fun s w' =>
      s = ForInStep.yield PUnit.unit ∧
      (∀ y, y ≠ p → y ≠ q.1 → w'.nodes.lookup y = w.nodes.lookup y) ∧
      (∀ y, w.taken.contains y = true → w'.taken.contains y = true) ∧
      (∃ pn', w'.nodes.lookup p = some pn') ∧
      (w'.taken.contains q.1 = true ∨
        w'.nodes.lookup q.1 = some (if qn.lastTime == some c.i then qn.toPrev (c.i - 1) else qn))) := by
  split
  · simp only [writerWP_bind]
    refine writerWP_mono (writerWP_retarget_frameW p q.1 m1 pn c w hp) ?_
    rintro _ w1 ⟨h1t, _, _, _, _, h1n, pn', h1p, _⟩
    refine (writerWP_takenBack_iff _ c w1 _).mpr ?_
    refine (writerWP_note_iff _ c _ _).mpr ?_
    simp only [writerWP_pure]
    refine ⟨by first | rfl | trivial, fun y hyp _ => h1n y hyp, fun y hy => ?_, ⟨pn', h1p⟩, Or.inl ?_⟩
    · simp only [List.contains_cons, h1t, hy, Bool.or_true]
    · simp
  · simp only [writerWP_bind]
    refine writerWP_mono (writerWP_unlink_fate q.1 qn c w hq) ?_
    rintro _ w1 ⟨h1t, _, _, h1x, h1l⟩
    simp only [writerWP_pure]
    exact ⟨by first | rfl | trivial, fun y _ hyq => h1l y hyq, fun y hy => by rw [h1t]; exact hy,
      ⟨pn, by rw [h1l p (Ne.symm hqp)]; exact hp⟩, Or.inr h1x⟩

/-- The merge's last loop over the two nodes merged: each taken back or
unlinked. -/
theorem writerWP_mergeCleanup_fateM (p m1 : NodeId) (c : Ctx) (l r : NodeId) (bl br : Bool)
    (pn ln rn : KNode) (w : W) (hlr : l ≠ r) (hlp : l ≠ p) (hrp : r ≠ p)
    (hp : w.nodes.lookup p = some pn) (hl : w.nodes.lookup l = some ln)
    (hr : w.nodes.lookup r = some rn) :
    WriterWP (forIn [(l, bl), (r, br)] PUnit.unit (fun q _ => if q.2 = true then (do
        retarget p q.1 m1
        takenBack q.1
        note "merge.takeback"
        pure (ForInStep.yield PUnit.unit)) else (do
        unlink q.1
        pure (ForInStep.yield PUnit.unit)))) c w (fun _ w' =>
      (w'.taken.contains l = true ∨
        w'.nodes.lookup l = some (if ln.lastTime == some c.i then ln.toPrev (c.i - 1) else ln)) ∧
      (w'.taken.contains r = true ∨
        w'.nodes.lookup r = some (if rn.lastTime == some c.i then rn.toPrev (c.i - 1) else rn))) := by
  rw [List.forIn_cons, writerWP_bind]
  refine writerWP_mono (writerWP_mergeCleanup_step p m1 c (l, bl) w pn ln hp hl hlp) ?_
  rintro s w1 ⟨hs, h1n, h1t, ⟨pn1, h1p⟩, h1f⟩
  subst hs
  simp only
  rw [List.forIn_cons, writerWP_bind]
  refine writerWP_mono (writerWP_mergeCleanup_step p m1 c (r, br) w1 pn1 rn h1p
    (by rw [h1n r hrp (Ne.symm hlr)]; exact hr) hrp) ?_
  rintro s w2 ⟨hs, h2n, h2t, _, h2f⟩
  subst hs
  simp only [List.forIn_nil, writerWP_pure]
  refine ⟨?_, h2f⟩
  rcases h1f with h | h
  · exact Or.inl (h2t l h)
  · exact Or.inr (by rw [h2n l hlp hlr]; exact h)

set_option maxHeartbeats 1600000 in
/-- The merge's tail keeps the take-back's (B) (`TtReachedN`), whether the
transaction made the two nodes merged or not: each taken back or unlinked; the
premises those of `writerWP_mergeTail_made_range`, l and r cached. -/
theorem writerWP_mergeTail_made_take (c : Ctx) (base : View BVal) (x : NodeId) (d : Nat) (p : NodeId)
    (pn xn : KNode) (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId)
    (rn : KNode) (ir : Nat) (cL cR : Nat) (N : NodeId → Option KNode) (root : NodeId) (nx : Nat)
    (w3 : W) (hT : TreeOK N c.i root) (hp : TReach N c.i root p) (hpn : N p = some pn)
    (hL : pn.ks[il]? = some (.key cL l)) (hLL : LastLive pn.ks pn.lastBitmap il cL)
    (hR : pn.ks[ir]? = some (.key cR r)) (hRL : LastLive pn.ks pn.lastBitmap ir cR)
    (hc : cL ≠ cR) (hxlr : x = l ∨ x = r) (hln : N l = some ln) (hrn : N r = some rn)
    (hroom : pn.size + 4 ≤ c.p.M)
    (hdead : ∀ il cL m1 ir cR m2, deadOver c.p (mergeParentNode pn c.i il cL m1 ir cR m2) = false)
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
    (hwfN : ∀ y yn, N y = some yn → klongsWf yn.ks = true) (hpos : 0 < c.i)
    (hTt : TtReachedN N c.i root)
    (h3l : w3.nodes.lookup l = some ln) (h3r : w3.nodes.lookup r = some rn) :
    WriterWP (mergeTail c x d p pn xn leftSome l ln il r rn ir) c w3
      (fun _ w' => TtReachedN (wNode c.p base w') c.i w'.top.rootKey) := by
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
  have hadjR : ∀ q ∈ pn.liveAt c.i, cL < q.1 → cR ≤ q.1 :=
    fun q hq hlt => (hadj q.1 q.2 hq).resolve_left (by omega)
  have hhead : (!xn.leaf) = true → ∃ y, rn.live.head? = some (0, y) := by
    intro h
    obtain ⟨y0, tl, he⟩ := hrhead h
    exact ⟨y0, by rw [he]; rfl⟩
  simp only [writerWP_bind, writerWP_modify]
  obtain ⟨xn3, hx3⟩ : ∃ n, w3.nodes.lookup x = some n := by
    rcases hxlr with h | h
    · rw [h]; exact ⟨ln, h3l⟩
    · rw [h]; exact ⟨rn, h3r⟩
  have hlr : l ≠ r := fun h => by
    have := (hT.oneLink p cL p cR r hp hp ⟨pn, hpn, by rw [← h]; exact hpL⟩ ⟨pn, hpn, hpR⟩).2
    omega
  refine writerWP_mono (writerWP_and (writerWP_ghOf_frame x c _)
    (writerWP_ghOf_cached x xn3 c _ (by exact hx3) (fun _ w' => w'.nodes.lookup x = some xn3)
      (fun _ => by exact hx3))) ?_
  intro gh w4 ⟨⟨h4t, h4top, h4n, h4v, h4p, h4m, h4l⟩, h4x⟩
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
    have h6x : w6.nodes.lookup x = w3.nodes.lookup x := by
      rw [h6n, h5n, lookup_append_single_ne _ _ _ _ (by rw [h4n, h3next]; omega), h4x, hx3]
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
      refine writerWP_mono (writerWP_mergeParent_room p pn (d - 1) il cL m1 ir cR none c w6 hw6p hroom
        (hdead _ _ _ _ _ _)) ?_
      intro _ w7 ⟨h7n, h7t, h7top, _, _, _, _, _⟩
      have hlk7 : w7.nodes.lookup p = some (mergeParentNode pn c.i il cL m1 ir cR none) := by
        rw [h7n, lookup_upsert]; simp
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
        (writerWP_mergeCleanup_fateM p m1 c l r _ _ _ ln rn w7 hlr (Ne.symm hpl) (Ne.symm hpr) hlk7
          (by rw [h7lr l (Or.inl rfl)]; exact h3l) (by rw [h7lr r (Or.inr rfl)]; exact h3r))) ?_
      intro _ w8 ⟨⟨h8top, _, h8t, h8l, pn8, h8p, h8leaf, h8sub⟩, h8fl, h8fr⟩
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
      rw [h8top, h7top, h6top']
      refine ttReachedN_merge N (wNode c.p base w8) c.i root p l r [m1] pn ln rn pn8 cL cR hT hp hpn
        hpL hpR hln hrn
        (by intro m hm; simp only [List.mem_singleton] at hm; rw [hm]; exact hm1N) hN8p
        (fun cc z hm hc1 hc2 => (h8sub cc z).mpr ((hparOne cc z).mpr (Or.inr ⟨hm, hc1, hc2⟩)))
        (fun m hm => by
          simp only [List.mem_singleton] at hm
          rw [hm]
          exact ⟨cL, (h8sub cL m1).mpr ((hparOne cL m1).mpr (Or.inl ⟨rfl, rfl⟩))⟩)
        ?_ ?_ ?_ hTt
      · intro cc z hz
        have hzs : z ∈ (mergeList (!xn.leaf) cR ln.live rn.live).map Prod.snd := by
          rw [mergeList_map_snd, List.mem_append]
          rcases hz with h | h
          · left; rw [KNode.liveAt_of_times ln c.i hlt] at h; exact List.mem_map.mpr ⟨_, h, rfl⟩
          · right; rw [KNode.liveAt_of_times rn c.i hrt] at h; exact List.mem_map.mpr ⟨_, h, rfl⟩
        obtain ⟨⟨c', z'⟩, hq, hqz⟩ := List.mem_map.mp hzs
        simp only at hqz
        rw [← hqz]
        refine ⟨m1, List.mem_singleton_self _, _, c', hN8m1, ?_⟩
        rw [mrg_newKlongs_liveAt_iff _ c.i first hndF, hfirst]
        exact hq
      · intro y hyp hyl hyr hym
        have hym' : y ≠ m1 := fun h => hym (by rw [h]; exact List.mem_singleton_self _)
        rw [← hNw3 y]
        unfold wNode
        rw [h8tc y hyl hyr, h8l' y hyp hyl hyr, h6old y (hyx y hyl hyr) hym']
      · intro y yn hy hyn
        rcases hy with hy | hy <;> rw [hy] at hyn
        · rcases h8fl with h | h
          · unfold wNode at hyn; rw [h] at hyn; cases hyn
          · have hlt8 : w8.taken.contains l = false := by
              cases hc : w8.taken.contains l with
              | false => rfl
              | true => unfold wNode at hyn; rw [hc] at hyn; cases hyn
            simp only [wNode, hlt8, Bool.false_eq_true, ↓reduceIte, h, Option.some.injEq] at hyn
            rw [← hyn]
            exact unlinked_no_time ln c.i hpos (hwfN _ ln hln) hlt
        · rcases h8fr with h | h
          · unfold wNode at hyn; rw [h] at hyn; cases hyn
          · have hrt8 : w8.taken.contains r = false := by
              cases hc : w8.taken.contains r with
              | false => rfl
              | true => unfold wNode at hyn; rw [hc] at hyn; cases hyn
            simp only [wNode, hrt8, Bool.false_eq_true, ↓reduceIte, h, Option.some.injEq] at hyn
            rw [← hyn]
            exact unlinked_no_time rn c.i hpos (hwfN _ rn hrn) hrt
    | some ksg =>
      obtain ⟨ks2, g2⟩ := ksg
      rw [hsec] at hmkd
      have hE : (first ++ ks2).map Prod.snd = (ln.live ++ rn.live).map Prod.snd := by
        rw [splitMerged_map_snd _ _ _ first ks2 g2 hmkd, mergeList_map_snd, List.map_append]
      simp only [writerWP_bind, writerWP_pure, writerWP_get]
      refine writerWP_mono (writerWP_newKey_frame _ _ _ _ c w6) ?_
      intro m2 w7 ⟨hm2, h7n, h7t, h7top, _, _, _, _⟩
      have hm2' : m2 = m1 + 2 := by rw [hm2, h6next, h5next, hw4m1]
      subst hm2'
      try simp only [writerWP_bind, writerWP_pure, writerWP_get]
      refine writerWP_mono (writerWP_setMadeFor_frame _ _ c _) ?_
      intro _ w8 ⟨h8n, h8t, h8top, _, _, _⟩
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
      refine writerWP_mono (writerWP_mergeParent_room p pn (d - 1) il cL m1 ir cR (some (m1 + 2, g2)) c
        w8 hw8p hroom (hdead _ _ _ _ _ _)) ?_
      intro _ w9 ⟨h9n, h9t, h9top, _, _, _, _, _⟩
      have hlk9 : w9.nodes.lookup p = some (mergeParentNode pn c.i il cL m1 ir cR (some (m1 + 2, g2))) := by
        rw [h9n, lookup_upsert]; simp
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
        (writerWP_mergeCleanup_fateM p m1 c l r _ _ _ ln rn w9 hlr (Ne.symm hpl) (Ne.symm hpr) hlk9
          (by rw [h9lr l (Or.inl rfl)]; exact h3l) (by rw [h9lr r (Or.inr rfl)]; exact h3r))) ?_
      intro _ w10 ⟨⟨h10top, _, h10t, h10l, pn10, h10p, h10leaf, h10sub⟩, h10fl, h10fr⟩
      try simp only [writerWP_pure]
      have h10tc : ∀ y, y ≠ l → y ≠ r → w10.taken.contains y = w3.taken.contains y := by
        intro y hyl hyr; rw [h10t y (hcl' _ _ y hyl hyr), h9t, h8t, h7t, h6taken]
      have h10l' : ∀ y, y ≠ p → y ≠ l → y ≠ r → w10.nodes.lookup y = w8.nodes.lookup y := by
        intro y hyp hyl hyr; rw [h10l y hyp (hcl' _ _ y hyl hyr), h9n, lookup_upsert]; simp [hyp]
      have hm2T : w3.taken.contains (m1 + 2) = false := (hfree _ (by omega)).2
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
      rw [h10top, h9top, h8top, h7top, h6top']
      refine ttReachedN_merge N (wNode c.p base w10) c.i root p l r [m1, m1 + 2] pn ln rn pn10 cL cR
        hT hp hpn hpL hpR hln hrn
        (by
          intro m hm
          simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hm
          rcases hm with hm | hm <;> rw [hm]
          · exact hm1N
          · exact (hfree _ (by omega)).1) hN10p ?_ ?_ ?_ ?_ ?_ hTt
      · intro cc z hm hc1 hc2
        have hcg : cc ≠ g2 := by
          rcases hadj cc z hm with h | h
          · omega
          · have := hgU cc z hm (by omega); omega
        exact (h10sub cc z).mpr ((hparTwo (m1 + 2) g2 cc z).mpr (Or.inr (Or.inr ⟨hcg, hc1, hc2, hm⟩)))
      · intro m hm
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hm
        rcases hm with hm | hm <;> rw [hm]
        · exact ⟨cL, (h10sub cL m1).mpr
            ((hparTwo (m1 + 2) g2 cL m1).mpr (Or.inr (Or.inl ⟨by omega, rfl, rfl⟩)))⟩
        · exact ⟨g2, (h10sub g2 (m1 + 2)).mpr ((hparTwo (m1 + 2) g2 g2 (m1 + 2)).mpr (Or.inl ⟨rfl, rfl⟩))⟩
      · intro cc z hz
        have hzs : z ∈ (first ++ ks2).map Prod.snd := by
          rw [hE, List.map_append, List.mem_append]
          rcases hz with h | h
          · left; rw [KNode.liveAt_of_times ln c.i hlt] at h; exact List.mem_map.mpr ⟨_, h, rfl⟩
          · right; rw [KNode.liveAt_of_times rn c.i hrt] at h; exact List.mem_map.mpr ⟨_, h, rfl⟩
        rw [List.map_append, List.mem_append] at hzs
        rcases hzs with h | h
        · obtain ⟨⟨c', z'⟩, hq, hqz⟩ := List.mem_map.mp h
          simp only at hqz
          rw [← hqz]
          exact ⟨m1, List.mem_cons_self, _, c', hN10m1,
            (mrg_newKlongs_liveAt_iff _ c.i first hnd1 c' z').mpr hq⟩
        · obtain ⟨⟨c', z'⟩, hq, hqz⟩ := List.mem_map.mp h
          simp only at hqz
          rw [← hqz]
          exact ⟨m1 + 2, List.mem_cons_of_mem _ List.mem_cons_self, _, c', hN10m2,
            (mrg_newKlongs_liveAt_iff _ c.i ks2 hnd2 c' z').mpr hq⟩
      · intro y hyp hyl hyr hym
        have hym1 : y ≠ m1 := fun h => hym (by rw [h]; exact List.mem_cons_self)
        have hym2 : y ≠ m1 + 2 := fun h => hym (by rw [h]; exact List.mem_cons_of_mem _ List.mem_cons_self)
        rw [← hNw3 y]
        unfold wNode
        rw [h10tc y hyl hyr, h10l' y hyp hyl hyr, h8l, lookup_append_single_ne _ _ _ _ hym2,
          h6old y (hyx y hyl hyr) hym1]
      · intro y yn hy hyn
        rcases hy with hy | hy <;> rw [hy] at hyn
        · rcases h10fl with h | h
          · unfold wNode at hyn; rw [h] at hyn; cases hyn
          · have hlt8 : w10.taken.contains l = false := by
              cases hc : w10.taken.contains l with
              | false => rfl
              | true => unfold wNode at hyn; rw [hc] at hyn; cases hyn
            simp only [wNode, hlt8, Bool.false_eq_true, ↓reduceIte, h, Option.some.injEq] at hyn
            rw [← hyn]
            exact unlinked_no_time ln c.i hpos (hwfN _ ln hln) hlt
        · rcases h10fr with h | h
          · unfold wNode at hyn; rw [h] at hyn; cases hyn
          · have hrt8 : w10.taken.contains r = false := by
              cases hc : w10.taken.contains r with
              | false => rfl
              | true => unfold wNode at hyn; rw [hc] at hyn; cases hyn
            simp only [wNode, hrt8, Bool.false_eq_true, ↓reduceIte, h, Option.some.injEq] at hyn
            rw [← hyn]
            exact unlinked_no_time rn c.i hpos (hwfN _ rn hrn) hrt

/-- The writer's merge keeps the take-back's (B) (`TtReachedN`): x at depth d
merged with a sibling under a reached inner parent with room, made by the
transaction or not; the premises those of `writerWP_merge_made_range`. -/
theorem writerWP_merge_made_take (x : NodeId) (d : Nat) (c : Ctx) (base : View BVal)
    (hvc : ViewCoherent c base) (w : W)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hpar : ∀ p, (w.path[d - 1]?).map (·.2) = some p →
      TReach (wNode c.p base w) c.i w.top.rootKey p ∧ ∃ pn, wNode c.p base w p = some pn ∧
        pn.leaf = false ∧ pn.size + 4 ≤ c.p.M ∧
        (∀ il cL m1 ir cR m2, deadOver c.p (mergeParentNode pn c.i il cL m1 ir cR m2) = false) ∧
        klongsWf pn.ks = true ∧ (∀ s, Klong.time s ∈ pn.ks → s ≤ c.i) ∧
        ∀ cc z zn, (cc, z) ∈ pn.liveAt c.i → wNode c.p base w z = some zn →
          ∀ s, Klong.time s ∈ zn.ks → s ≤ c.i)
    (hRt : ∀ y, TReach (wNode c.p base w) c.i w.top.rootKey y → w.taken.contains y = false)
    (hids : (∀ z, (w.nodes.lookup z).isSome = true → z < w.next) ∧
      (∀ z, (c.view z).isSome = true → z < w.next) ∧ (∀ z, w.taken.contains z = true → z < w.next))
    (hbaseF : ∀ z, w.next ≤ z → knodeOf c.p base z = none)
    (hfreshT : ∀ z, w.next ≤ z → ∀ u c', TReach (wNode c.p base w) c.i w.top.rootKey u →
      ¬ TLink (wNode c.p base w) c.i u c' z)
    (hR : RangeOrder (wNode c.p base w) c.i w.top.rootKey) (hcap : 1 ≤ c.p.mergeMax)
    (hwfN : ∀ y yn, wNode c.p base w y = some yn → klongsWf yn.ks = true)
    (hpos : 0 < c.i) (hTt : TtReachedN (wNode c.p base w) c.i w.top.rootKey) :
    WriterWP (merge x d) c w (fun _ w' => TtReachedN (wNode c.p base w') c.i w'.top.rootKey) := by
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
    obtain ⟨hpR, pn0, hpn0, hpleaf, hroom, hdead, hpwf, hpt, hch⟩ := hpar e.2 (by rw [he]; rfl)
    refine writerWP_mono (writerWP_getNode_all e.2 c w base hvc) ?_
    intro pn w1 ⟨hr1, hlk1, hwn1, hpre1, hsrc1⟩
    rw [hwn1 (hRt _ hpR)] at hpn0
    cases hpn0
    -- the tail from any state that reads as w
    have hpn : wNode c.p base w e.2 = some pn0 := hwn1 (hRt _ hpR)
    have hpRS := tReach_reachS _ c.i _ _ hpR
    have tailOK : ∀ (leftSome : Bool) (l : NodeId) (ln : KNode) (il : Nat) (r : NodeId)
        (rn : KNode) (ir cL cR : Nat) (xn : KNode) (w3 : W), ReadsAs c.p base w w3 →
        w1.nodes <+: w3.nodes → (∀ z, (w3.nodes.lookup z).isSome = true → z < w.next) →
        pn0.ks[il]? = some (.key cL l) → LastLive pn0.ks pn0.lastBitmap il cL →
        pn0.ks[ir]? = some (.key cR r) → LastLive pn0.ks pn0.lastBitmap ir cR → cL < cR →
        (∀ cc z, (cc, z) ∈ pn0.liveAt c.i → cc ≤ cL ∨ cR ≤ cc) →
        ln.leaf = xn.leaf → rn.leaf = xn.leaf →
        (x = l ∨ x = r) → wNode c.p base w l = some ln → wNode c.p base w r = some rn →
        w3.nodes.lookup l = some ln → w3.nodes.lookup r = some rn →
        WriterWP (mergeTail c x d e.2 pn0 xn leftSome l ln il r rn ir) c w3
          (fun _ w' => TtReachedN (wNode c.p base w') c.i w'.top.rootKey) := by
      intro leftSome l ln il r rn ir cL cR xn w3 hr3 hpre3 hsrc3 hL hLL hR' hRL hclt hadj hll hrl
        hxlr hln hrn h3l h3r
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
      refine writerWP_mono (writerWP_mergeTail_made_take c base x d e.2 pn0 xn leftSome l ln il r rn ir cL cR
        (wNode c.p base w) w.top.rootKey w.next w3 hT hpR hpn hL hLL hR' hRL (by omega) hxlr
        hln hrn hroom hdead hpwf hpt hch hr3.1 (by rw [hr3.2.1]) hr3.2.2.2.2
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
        hwfN hpos hTt h3l h3r) ?_
      intro _ w' h
      exact h
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
    refine writerWP_mono (writerWP_getNode_all x c w1 base hvc) ?_
    intro xn w2 ⟨hr2, hlk2, hwn2, hpre2, hsrc2⟩
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
            wb.nodes.lookup x = some xn →
            (∀ z, (wb.nodes.lookup z).isSome = true → z < w.next) →
            LastLive pn0.ks pn0.lastBitmap ia0 cva → cx < cva →
            (mergeIdx pn0 cx).2.1 = some (ia0, cva) →
            WriterWP (do
              let __x ← sibling e.2 pn0 ia0 !xn.leaf
              mergeTail c x d e.2 pn0 xn false x xn ix __x.1 __x.2 ia0) c wb
              (fun _ w' => TtReachedN (wNode c.p base w') c.i w'.top.rootKey) := by
          intro wb ia0 cva hrb hpreb hxb hsrcb hLa hax hia
          rw [writerWP_bind]
          refine writerWP_mono (writerWP_sibling_leaf e.2 pn0 ia0 (!xn.leaf) c wb base hvc) ?_
          rintro ⟨rs, rsn⟩ w4 ⟨hs1, hr4, hlk4s, hwn4, hpre4, hsrc4, hsl⟩
          obtain ⟨hka, hrn, hr04, hpre14, hsrc04⟩ :=
            hsib wb ia0 cva (rs, rsn) w4 hrb hpreb hsrcb hLa hs1 hr4 hpre4 hsrc4 hwn4
          have hmin := mergeIdx_right_min pn0 cx ia0 cva hia
          exact tailOK false x xn ix rs rsn ia0 cx cva xn w4 hr04 hpre14 hsrc04 hkx hLx hka hLa
            hax (by
              intro cc z hm
              rcases Nat.lt_or_ge cx cc with h | h
              · have hm' : (cc, z) ∈ pn0.live := by rw [← KNode.liveAt_of_times pn0 c.i hpt]; exact hm
                exact Or.inr (hmin cc z hm' h)
              · exact Or.inl h) rfl (by rw [hsl]; simp) (Or.inl rfl) hxn hrn
              (lookup_of_prefix _ _ hpre4 x xn hxb) hlk4s
        split
        · rename_i ib0 cvb
          obtain ⟨hLb, hbx⟩ := hMb ib0 cvb rfl
          simp only [writerWP_bind]
          refine writerWP_mono (writerWP_sibling_leaf e.2 pn0 ib0 (!xn.leaf) c w2 base hvc) ?_
          rintro ⟨ls, lsn⟩ w3 ⟨hs1, hr3, hlk3s, hwn3, hpre3, hsrc3, hsl⟩
          obtain ⟨hkb, hln, hr03, hpre13, hsrc03⟩ :=
            hsib w2 ib0 cvb (ls, lsn) w3 hr02 hpre02 hsrc02 hLb hs1 hr3 hpre3 hsrc3 hwn3
          refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_)
          · show WriterWP (mergeTail c x d e.2 pn0 xn true ls lsn ib0 x xn ix) c w3 _
            have hmax := mergeIdx_left_max pn0 cx ib0 cvb (by rw [hmi])
            exact tailOK true ls lsn ib0 x xn ix cvb cx xn w3 hr03 hpre13 hsrc03 hkb hLb hkx hLx
              hbx (by
                intro cc z hm
                rcases Nat.lt_or_ge cc cx with h | h
                · have hm' : (cc, z) ∈ pn0.live := by rw [← KNode.liveAt_of_times pn0 c.i hpt]; exact hm
                  exact Or.inl (hmax cc z hm' h)
                · exact Or.inr h) (by rw [hsl]; simp) rfl (Or.inr rfl) hln hxn hlk3s
                (lookup_of_prefix _ _ hpre3 x xn hlk2)
          · rw [writerWP_bind, writerWP_pure]
            dsimp only
            split
            · rename_i ia0 cva _
              obtain ⟨hLa, hax⟩ := hMa ia0 cva rfl
              exact hright w3 ia0 cva hr03 hpre13 (lookup_of_prefix _ _ hpre3 x xn hlk2) hsrc03 hLa hax
                (by rw [hmi])
            · exact writerWP_throw _ _ _ _
        · rw [writerWP_bind, writerWP_pure]
          dsimp only
          split
          · rename_i ia0 cva
            obtain ⟨hLa, hax⟩ := hMa ia0 cva rfl
            exact hright w2 ia0 cva hr02 hpre02 hlk2 hsrc02 hLa hax (by rw [hmi])
          · exact writerWP_throw _ _ _ _
      · exact writerWP_throw _ _ _ _
    · exact writerWP_throw _ _ _ _
  · exact writerWP_throw _ _ _ _

end SIS.Tree
