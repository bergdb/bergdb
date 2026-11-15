/-
`DelInvJ` carried to the upward delete's call of `afterDelete` (bergdb 024-12,
section 1): the upward delete that empties its leaf, the climb, the loop over the
chain and the stop node's bitmap, for two copies that differ only at the stop
node's call (`rwp_deleteUpwardP2_climb`, `writerWP_deleteUpward_stepJG`'s walk
for the two copies).
-/
import SIS.Tree.DelHoleLeaf

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

set_option maxHeartbeats 3200000 in
/-- `writerWP_deleteUpward_stepJG` for two copies of the upward delete that differ
only at the stop node's call of `afterDelete`: the climb, the loop and the stop
node's reads are the same; at a segment leaf as the stop node, the bitmap leads
to a state where the two calls run alike (`hleafStep`). -/
theorem rwp_deleteUpwardP2_climb (aK aC1 aC2 : Key → Nat → Nat → M Unit) (key : Key)
    (c : Ctx) (base : View BVal) (X : Nat → NodeId)
    (Nn : Nat → KNode) (K : Nat → Nat) (depth cv : Nat)
    (B : NodeId) (w : W) (J : W → Prop) (hJ0 : J w)
    (hJnote : ∀ (s : String) (v : W), J v → J { v with trail := s :: v.trail })
    (hJtake : ∀ (x p : NodeId) (k : Nat) (v : W), J v → (∃ xn, v.nodes.lookup x = some xn) →
      (∃ pn, v.nodes.lookup p = some pn) → WriterWP (takeBack x p k) c v (fun _ v' => J v'))
    (hJunlink : ∀ (x : NodeId) (v : W), J v → (∃ xn, v.nodes.lookup x = some xn) →
      WriterWP (unlink x) c v (fun _ v' => J v'))
    (hMF : ∀ x o, w.madeFor.lookup x = some o → o < B) (hdepth : 0 < depth) (hpos : 0 < c.i)
    (hp : ∀ i, i ≤ depth → (w.path[i]?).map (·.2) = some (X i))
    (hk : ∀ i, 0 < i → i ≤ depth → w.path[i]? = some (some (K i), X i))
    (hlk : ∀ i, i ≤ depth → w.nodes.lookup (X i) = some (Nn i))
    (htk : ∀ i, i ≤ depth → w.taken.contains (X i) = false)
    (htimes : ∀ i, i ≤ depth → ∀ s, Klong.time s ∈ (Nn i).ks → s ≤ c.i)
    (hdist : ∀ i i', i ≤ depth → i' ≤ depth → X i = X i' → i = i')
    (hne : bitsUnion (Nn depth).lastBitmap ((Nn depth).bitsOf cv) ≠ (Nn depth).lastBitmap)
    (hall : (Nn depth).allKeysIn (bitsUnion (Nn depth).lastBitmap ((Nn depth).bitsOf cv)) = true)
    (hwf : ∀ x xn, TReach (wNode c.p base w) c.i w.top.rootKey x → wNode c.p base w x = some xn →
      klongsWf xn.ks = true)
    (hreach : ∀ i, i ≤ depth → TReach (wNode c.p base w) c.i w.top.rootKey (X i))
    (hleafStep : ∀ (stop : Nat) (w2 : W) (S : KNode), stop < depth →
      (∀ i, stop < i → i < depth →
        (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true) →
      UpLoopEnd c B X Nn depth stop w w2 S → J w2 → (Nn stop).leaf = true → ∀ gs hs : Nat,
      WriterWP (appendDeleteKlong (X stop) stop (K (stop + 1))) c
        { w2 with trail := "up.stop-at-segment-leaf" :: w2.trail }
        (fun _ w3 => RWP (aC1 key gs hs) (aC2 key gs hs) c w3)) :
    RWP (deleteUpwardP2 aK aC1 (X depth) depth cv key) (deleteUpwardP2 aK aC2 (X depth) depth cv key) c w := by
  unfold deleteUpwardP2
  refine rwp_read ?_
  refine rwp_getNode_known _ _ (hlk depth (Nat.le_refl _)) ?_
  have hne' : (bitsUnion (Nn depth).lastBitmap ((Nn depth).bitsOf cv) == (Nn depth).lastBitmap) = false := by
    simpa using hne
  simp only [hne', hall, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
  refine rwp_bind _ (writerWP_climb c X Nn K depth w hp hk hlk) ?_
  rintro stop w1 ⟨hw1, hst, hbetween, hmadeOK, hstopNode, hself⟩
  have hw1' := hw1.symm
  subst hw1'
  have hsd : stop ≠ depth := fun h => by have := (hself h).1; omega
  have hsd' : (stop == depth) = false := by simpa using hsd
  simp only [hsd', Bool.false_eq_true, ↓reduceIte]
  have hsD : stop < depth := by omega
  refine rwp_bind (fun _ v => v = { w with trail := "up.climb" :: w.trail })
    ((writerWP_note_iff _ c w _).mpr rfl) ?_
  rintro _ wv hwv
  subst wv
  have hJw0 : J { w with trail := "up.climb" :: w.trail } := hJnote _ w hJ0
  generalize hw0 : ({ w with trail := "up.climb" :: w.trail } : W) = w0
  rw [hw0] at hJw0
  have h0n : w0.nodes = w.nodes := by rw [← hw0]
  have h0p : w0.path = w.path := by rw [← hw0]
  have h0t : w0.taken = w.taken := by rw [← hw0]
  have h0top : w0.top = w.top := by rw [← hw0]
  have h0v : w0.vals = w.vals := by rw [← hw0]
  have h0m : w0.madeFor = w.madeFor := by rw [← hw0]
  have h0nx : w0.next = w.next := by rw [← hw0]
  refine rwp_bind (fun a v => a = w0 ∧ v = w0) ((writerWP_get c w0 _).mpr ⟨rfl, rfl⟩) ?_
  rintro a v ⟨ha, hv⟩
  subst a; subst v
  refine rwp_bind _ (writerWP_foldlM_getNode c (fun s n => if n.leaf = true then s + 1 else s)
    (List.take stop w0.path) 0 w0 ?_) ?_
  · intro e he
    obtain ⟨i, hie⟩ := List.mem_iff_getElem?.mp he
    rw [List.getElem?_take] at hie
    split at hie
    · rename_i hi
      have h1 := hp i (by omega)
      rw [← h0p, hie] at h1
      simp only [Option.map_some, Option.some.injEq] at h1
      rw [h1, h0n]
      exact ⟨_, hlk i (by omega)⟩
    · cases hie
  rintro seg w0' hw0'
  have hw0'' := hw0'.symm
  subst hw0''
  -- the loop: the chain's nodes unlinked or taken back
  let I : List Nat → W → Prop := fun rem v => J v ∧
    v.top = w0.top ∧ v.vals = w0.vals ∧ v.path = w0.path ∧
    (∀ y, (∀ k, stop < k → k ≤ depth → y ≠ X k) → v.taken.contains y = w0.taken.contains y) ∧
    (∀ y, y ≠ X stop → (∀ k, stop < k → k ≤ depth → y ≠ X k) → v.nodes.lookup y = w0.nodes.lookup y) ∧
    v.madeFor = w0.madeFor ∧ v.next = w0.next ∧
    ∃ a0, rem = List.range' a0 (depth - stop - a0) ∧ a0 ≤ depth - stop ∧
      (∀ j, j < a0 → ChainFate c.i v (X (depth - j))) ∧
      (∀ j, j < a0 → ChainFateW c.i B v (Nn (depth - j)) (X (depth - j))) ∧
      (∀ j, a0 ≤ j → j ≤ depth - stop → v.taken.contains (X (depth - j)) = false) ∧
      (∀ j, a0 < j → j ≤ depth - stop → v.nodes.lookup (X (depth - j)) = some (Nn (depth - j))) ∧
      ∃ S, v.nodes.lookup (X (depth - a0)) = some S ∧
        (S = Nn (depth - a0) ∨ ∃ ti dst, S = { Nn (depth - a0) with
          ks := retargetKlongs (Nn (depth - a0)).ks ti (X (depth - a0 + 1)) dst }) ∧
        RetFormS c.i B (Nn (depth - a0)) S ∧
        (0 < a0 → (Nn (depth - a0 + 1)).firstTime = some c.i →
          RetFrom c.i B (Nn (depth - a0)) (X (depth - a0 + 1)) S)
  refine rwp_bind _ (writerWP_forIn_inv c I _ ?_ (List.range (depth - stop)) w0
    ⟨hJw0, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ _ => rfl, rfl, rfl, 0, by rw [List.range_eq_range']; rfl,
      Nat.zero_le _, fun j hj => absurd hj (Nat.not_lt_zero _), fun j hj => absurd hj (Nat.not_lt_zero _),
      fun j _ hj => by rw [h0t]; exact htk _ (by omega),
      fun j _ hj => by rw [h0n]; exact hlk _ (by omega),
      Nn (depth - 0), by rw [h0n]; exact hlk _ (by omega), Or.inl rfl, Or.inl rfl,
      fun h => absurd h (Nat.lt_irrefl 0)⟩) ?_
  · intro a rest v ⟨hJv, hvtop, hvv, hvp, hvt, hvn, hvm, hvnx, a0, hrem, ha0, hfv, hfvJ, hnt, hexact, S, hSl, hS,
      hSR, hSF⟩
    have hlen : 0 < depth - stop - a0 := by
      rcases h : depth - stop - a0 with _ | m
      · rw [h] at hrem; simp at hrem
      · omega
    have hra : a = a0 ∧ rest = List.range' (a0 + 1) (depth - stop - (a0 + 1)) := by
      rw [show depth - stop - a0 = (depth - stop - (a0 + 1)) + 1 by omega, List.range'_succ] at hrem
      simp only [List.cons.injEq] at hrem
      exact hrem
    obtain ⟨hae, hrest⟩ := hra
    subst hae
    have hpar : v.nodes.lookup (X (depth - (a + 1))) = some (Nn (depth - (a + 1))) :=
      hexact (a + 1) (by omega) (by omega)
    have hpne : ∀ y, y ≠ X stop → (∀ k, stop < k → k ≤ depth → y ≠ X k) → y ≠ X (depth - (a + 1)) := by
      intro y hys hy he
      rcases Nat.lt_or_ge stop (depth - (a + 1)) with h | h
      · exact hy _ h (by omega) he
      · exact hys (by rw [he, show depth - (a + 1) = stop by omega])
    simp only [writerWP_bind]
    refine writerWP_pathNode_known (depth - a) (X (depth - a)) c v
      (by rw [hvp, h0p]; exact hp _ (by omega)) _ ?_
    rw [writerWP_getNode_known _ _ c v hSl]
    split
    · rename_i hmadeS
      simp only [writerWP_bind]
      refine writerWP_pathNode_known (depth - a - 1) (X (depth - (a + 1))) c v
        (by rw [hvp, h0p, show depth - a - 1 = depth - (a + 1) by omega]; exact hp _ (by omega)) _ ?_
      refine writerWP_klongAt_known (depth - a) (K (depth - a)) (X (depth - a)) c v
        (by rw [hvp, h0p]; exact hk _ (by omega) (by omega)) _ ?_
      refine writerWP_mono (writerWP_and (writerWP_takeBack_exact _ _ _ _ c v hpar)
        (hJtake _ _ _ v hJv ⟨_, hSl⟩ ⟨_, hpar⟩)) ?_
      rintro _ v2 ⟨⟨h2t, h2top, h2v, h2p, h2m, h2nx, h2n, hlt2, old, hold, h2l⟩, hJv2⟩
      have hn' : { Nn (depth - (a + 1)) with ks := (retargetKlongs (Nn (depth - (a + 1))).ks
            ((Nn (depth - (a + 1))).lastTimeIndex.getD 0) (X (depth - a)) old) } = Nn (depth - (a + 1)) ∨
          ∃ ti dst, { Nn (depth - (a + 1)) with ks := (retargetKlongs (Nn (depth - (a + 1))).ks
            ((Nn (depth - (a + 1))).lastTimeIndex.getD 0) (X (depth - a)) old) } =
            { Nn (depth - (a + 1)) with ks := (retargetKlongs (Nn (depth - (a + 1))).ks ti (X (depth - a)) dst) } :=
        Or.inr ⟨_, _, rfl⟩
      have holdB : old < B := hMF _ _ (by rw [← h0m, ← hvm]; exact hold)
      have hmadeN : (Nn (depth - a)).firstTime = some c.i := by
        rw [← retFormS_firstTime c.i B _ S hSR]; simpa using hmadeS
      simp only [writerWP_pure]
      refine ⟨by first | rfl | trivial, hJv2, h2top.trans hvtop, h2v.trans hvv, h2p.trans hvp, fun y hy => ?_,
        fun y hys hy => ?_, h2m.trans hvm, h2nx.trans hvnx, a + 1, hrest, by omega, fun j hj => ?_, fun j hj => ?_,
        fun j h1 h2 => ?_, fun j h1 h2 => ?_, _, h2l, ?_,
        Or.inr ⟨hlt2, X (depth - a), old, holdB, rfl⟩,
        fun _ _ => ⟨hlt2, old, holdB, by rw [show depth - (a + 1) + 1 = depth - a by omega]⟩⟩
      · have hne : (y == X (depth - a)) = false := by
          simpa using hy (depth - a) (by omega) (by omega)
        rw [h2t, List.contains_cons, hne, Bool.false_or]
        exact hvt y hy
      · rw [h2n y (hpne y hys hy)]
        exact hvn y hys hy
      · rcases Nat.lt_or_ge j a with hja | hja
        · rcases hfv j hja with h | ⟨S0, h1, h3⟩
          · left
            rw [h2t, List.contains_cons, h, Bool.or_true]
          · right
            refine ⟨S0, ?_, h3⟩
            rw [h2n _ (fun he => by have := hdist _ _ (by omega) (by omega) he; omega)]
            exact h1
        · have hja' : j = a := by omega
          rw [hja']
          left
          rw [h2t]
          simp
      · rcases Nat.lt_or_ge j a with hja | hja
        · obtain ⟨hm1, hm2⟩ := hfvJ j hja
          have hne : X (depth - j) ≠ X (depth - a) := fun he => by
            have := hdist _ _ (by omega) (by omega) he; omega
          refine ⟨fun h => ?_, fun h => ?_⟩
          · rw [h2t, List.contains_cons, hm1 h, Bool.or_true]
          · obtain ⟨ht0, S0, hS0, hl0⟩ := hm2 h
            refine ⟨by rw [h2t, List.contains_cons, ht0]; simpa using hne, S0, hS0, ?_⟩
            rw [h2n _ (fun he => by have := hdist _ _ (by omega) (by omega) he; omega)]
            exact hl0
        · have hja' : j = a := by omega
          rw [hja']
          refine ⟨fun _ => by rw [h2t]; simp, fun h => absurd hmadeN h⟩
      · have hne : X (depth - j) ≠ X (depth - a) := fun he => by
          have := hdist _ _ (by omega) (by omega) he; omega
        rw [h2t, List.contains_cons, hnt j (by omega) h2]
        simpa using hne
      · rw [h2n _ (fun he => by have := hdist _ _ (by omega) (by omega) he; omega)]
        exact hexact j (by omega) h2
      · rw [show depth - (a + 1) + 1 = depth - a by omega]
        exact hn'
    · rename_i hmadeS
      simp only [writerWP_bind]
      refine (writerWP_note_iff _ c v _).mpr ?_
      refine writerWP_mono (writerWP_and (writerWP_and (writerWP_unlink_frameP _ _ c _ hSl)
        (writerWP_unlink_fate _ _ c _ hSl)) (hJunlink _ _ (hJnote _ v hJv) ⟨_, hSl⟩)) ?_
      rintro _ v2 ⟨⟨⟨h2t, h2top, h2nx, h2v, h2p, h2m, h2l⟩, ⟨_, _, _, h2x, _⟩⟩, hJv2⟩
      have hmadeN : (Nn (depth - a)).firstTime ≠ some c.i := by
        rw [← retFormS_firstTime c.i B _ S hSR]; simpa using hmadeS
      simp only [writerWP_pure]
      refine ⟨by first | rfl | trivial, hJv2, h2top.trans hvtop, h2v.trans hvv, h2p.trans hvp,
        fun y hy => by rw [h2t]; exact hvt y hy, fun y hys hy => ?_, h2m.trans hvm, h2nx.trans hvnx, a + 1, hrest, by omega,
        fun j hj => ?_, fun j hj => ?_, fun j h1 h2 => by rw [h2t]; exact hnt j (by omega) h2,
        fun j h1 h2 => ?_, Nn (depth - (a + 1)), ?_, Or.inl rfl, Or.inl rfl,
        fun _ h => absurd (by rw [show depth - (a + 1) + 1 = depth - a by omega] at h; exact h) hmadeN⟩
      · rw [h2l y (hy (depth - a) (by omega) (by omega)), hvn y hys hy]
      · rcases Nat.lt_or_ge j a with hja | hja
        · rcases hfv j hja with h | ⟨S0, h1, h3⟩
          · left
            rw [h2t]
            exact h
          · right
            refine ⟨S0, ?_, h3⟩
            rw [h2l _ (fun he => by have := hdist _ _ (by omega) (by omega) he; omega)]
            exact h1
        · have hja' : j = a := by omega
          rw [hja']
          right
          have hNa : wNode c.p base w (X (depth - a)) = some (Nn (depth - a)) := by
            simp only [wNode, htk (depth - a) (by omega), Bool.false_eq_true, ↓reduceIte,
              hlk (depth - a) (by omega)]
          obtain ⟨hSw, hSt⟩ := retargetOr_wf_times (Nn (depth - a)) S _ c.i hS
            (hwf _ _ (hreach (depth - a) (by omega)) hNa) (htimes (depth - a) (by omega))
          exact ⟨_, h2x, unlinked_no_time S c.i hpos hSw hSt⟩
      · rcases Nat.lt_or_ge j a with hja | hja
        · obtain ⟨hm1, hm2⟩ := hfvJ j hja
          refine ⟨fun h => by rw [h2t]; exact hm1 h, fun h => ?_⟩
          obtain ⟨ht0, S0, hS0, hl0⟩ := hm2 h
          refine ⟨by rw [h2t]; exact ht0, S0, hS0, ?_⟩
          rw [h2l _ (fun he => by have := hdist _ _ (by omega) (by omega) he; omega)]
          exact hl0
        · have hja' : j = a := by omega
          rw [hja']
          refine ⟨fun h => absurd h hmadeN, fun _ => ⟨by rw [h2t]; exact hnt a (Nat.le_refl _) (by omega),
            S, hSR, h2x⟩⟩
      · rw [h2l _ (fun he => by have := hdist _ _ (by omega) (by omega) he; omega)]
        exact hexact j (by omega) h2
      · rw [h2l _ (fun he => by have := hdist _ _ (by omega) (by omega) he; omega)]
        exact hpar
  rintro _ w2 ⟨hJw2, h2top, h2v, h2p, h2t, h2n, h2m, h2nx, a0, hrem, ha0, hfv2, hfvJ2, hnt2, _, S, hSl, hS, hSR, hSF⟩
  have ha0' : a0 = depth - stop := by
    rcases h : depth - stop - a0 with _ | m
    · omega
    · rw [h, List.range'_succ] at hrem; cases hrem
  subst ha0'
  rw [show depth - (depth - stop) = stop by omega] at hSl hS hSR
  rw [show depth - (depth - stop) + 1 = stop + 1 by omega, show depth - (depth - stop) = stop by omega]
    at hSF
  have hSF' : (Nn (stop + 1)).firstTime = some c.i → RetFrom c.i B (Nn stop) (X (stop + 1)) S :=
    hSF (by omega)
  have hfateJ2 : ∀ k, stop < k → k ≤ depth → ChainFateW c.i B w2 (Nn k) (X k) := by
    intro k h1 h2
    have := hfvJ2 (depth - k) (by omega)
    rwa [show depth - (depth - k) = k by omega] at this
  have hfate2 : ∀ k, stop < k → k ≤ depth → ChainFate c.i w2 (X k) := by
    intro k h1 h2
    have := hfv2 (depth - k) (by omega)
    rwa [show depth - (depth - k) = k by omega] at this
  refine rwp_bind (fun a v => a = X stop ∧ v = w2)
    (writerWP_pathNode_known stop (X stop) c w2 (by rw [h2p, h0p]; exact hp stop (by omega)) _ ⟨rfl, rfl⟩) ?_
  rintro s v ⟨hs, hv⟩
  subst s; subst v
  refine rwp_bind (fun a v => a = K (stop + 1) ∧ v = w2)
    (writerWP_klongAt_known (stop + 1) (K (stop + 1)) (X (stop + 1)) c w2
      (by rw [h2p, h0p]; exact hk _ (by omega) (by omega)) _ ⟨rfl, rfl⟩) ?_
  rintro cs v ⟨hcs, hv⟩
  subst cs; subst v
  refine rwp_getNode_known _ _ hSl ?_
  refine rwp_bind (fun _ v => v = w2) (writerWP_ghOf_cached _ _ c w2 hSl _ (fun _ => rfl)) ?_
  rintro gh v hv
  subst v
  rcases gh with ⟨gs, hs⟩
  dsimp only
  have hLE : UpLoopEnd c B X Nn depth stop w w2 S :=
    ⟨fun y hy => by rw [h2t y hy, h0t], by rw [h2top, h0top], by rw [h2v, h0v], by rw [h2p, h0p],
      by rw [h2m, h0m], by rw [h2nx, h0nx], fun y hys hnc => by rw [h2n y hys hnc, h0n], hSl, hS, hSR, hSF', hfate2, hfateJ2⟩
  have hSleaf : S.leaf = (Nn stop).leaf := by rcases hS with rfl | ⟨ti, dst, rfl⟩ <;> rfl
  cases hsl : (Nn stop).leaf with
  | true =>
    have hsl' : S.leaf = true := hSleaf.trans hsl
    simp only [hsl', ↓reduceIte]
    refine rwp_bind (fun _ v => v = { w2 with trail := "up.stop-at-segment-leaf" :: w2.trail })
      ((writerWP_note_iff _ c w2 _).mpr rfl) ?_
    rintro _ v hv
    subst v
    refine rwp_bind _ (hleafStep stop w2 S hsD hbetween hLE hJw2 hsl gs hs) ?_
    intro _ w3 h3
    exact rwp_bind_left h3
  | false =>
    have hsl' : S.leaf = false := hSleaf.trans hsl
    simp only [hsl', Bool.false_eq_true, ↓reduceIte]
    exact rwp_refl _ _ _

set_option maxHeartbeats 1600000 in
/-- `takeJ2_deleteUpward_stepMBKG` for the two copies: at a segment leaf as the
stop node with room, the bitmap's state has `TakeJ2` and the collapse's reading
(`hleafM`); full, `hcascLeaf`. -/
theorem rwp_deleteUpwardP2_climbMB (aK aC1 aC2 : Key → Nat → Nat → M Unit) (c : Ctx) (base : View BVal)
    (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth cv : Nat) (pre : List Nat)
    (rk B : NodeId) (w : W) (hdepth : 0 < depth) (hfuel : 1 ≤ c.p.fuel) (hpos : 0 < c.i)
    (hp : ∀ i, i ≤ depth → (w.path[i]?).map (·.2) = some (X i))
    (hk : ∀ i, 0 < i → i ≤ depth → w.path[i]? = some (some (K i), X i))
    (hlk : ∀ i, i ≤ depth → w.nodes.lookup (X i) = some (Nn i))
    (htk : ∀ i, i ≤ depth → w.taken.contains (X i) = false)
    (htimes : ∀ i, i ≤ depth → ∀ s, Klong.time s ∈ (Nn i).ks → s ≤ c.i)
    (hdist : ∀ i i', i ≤ depth → i' ≤ depth → X i = X i' → i = i')
    (hne : bitsUnion (Nn depth).lastBitmap ((Nn depth).bitsOf cv) ≠ (Nn depth).lastBitmap)
    (hall : (Nn depth).allKeysIn (bitsUnion (Nn depth).lastBitmap ((Nn depth).bitsOf cv)) = true)
    (hleaf : (Nn depth).leaf = true)
    (hT : TreeOK (wNode c.p base w) c.i w.top.rootKey)
    (hR : RangeOrder (wNode c.p base w) c.i w.top.rootKey)
    (hwf : ∀ x xn, TReach (wNode c.p base w) c.i w.top.rootKey x → wNode c.p base w x = some xn →
      klongsWf xn.ks = true)
    (hRt : ∀ y, TReach (wNode c.p base w) c.i w.top.rootKey y → w.taken.contains y = false)
    (hTimesR : ∀ y yn, TReach (wNode c.p base w) c.i w.top.rootKey y → wNode c.p base w y = some yn →
      ∀ s, Klong.time s ∈ yn.ks → s ≤ c.i)
    (hICE : InnerChildrenExist (wNode c.p base w) c.i w.top.rootKey)
    (hfit : SegFits (wNode c.p base w) c.i (c.p.fuel - 1) w.top.rootKey)
    (hnovalAll : ∀ y yn, wNode c.p base w y = some yn → wValue base w y = none)
    (hreach : ∀ i, i ≤ depth → TReach (wNode c.p base w) c.i w.top.rootKey (X i))
    (hlinkK : ∀ i, 0 < i → i ≤ depth → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk) (hcv : cv ∉ pre)
    (hvisL : (X depth, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk)
    (huniq : ∀ key' x m, keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk → wNode c.p base w x = some m →
      m.leaf = true → key' = pre ++ [cv])
    (hkids : ∀ c' z, (c', z) ∈ (Nn depth).liveAt c.i → wNode c.p base w z = none)
    (hJ2 : TakeJ2 c base B w) (hMF : ∀ x o, w.madeFor.lookup x = some o → o < B)
    (J : W → Prop) (hJ0 : J w)
    (hJnote : ∀ (s : String) (v : W), J v → J { v with trail := s :: v.trail })
    (hJtake : ∀ (x p : NodeId) (k : Nat) (v : W), J v → (∃ xn, v.nodes.lookup x = some xn) →
      (∃ pn, v.nodes.lookup p = some pn) → WriterWP (takeBack x p k) c v (fun _ v' => J v'))
    (hJunlink : ∀ (x : NodeId) (v : W), J v → (∃ xn, v.nodes.lookup x = some xn) →
      WriterWP (unlink x) c v (fun _ v' => J v'))
    (hJadk : ∀ (x : NodeId) (d k : Nat) (v : W) (n : KNode), J v → (w.path[d]?).map (·.2) = some x →
      v.nodes.lookup x = some n → DelRoom c k n → WriterWP (appendDeleteKlong x d k) c v (fun _ v' => J v'))
    (hleafM : ∀ (stop : Nat) (w' : W) (sn' : KNode), stop < depth →
      (∀ i, stop < i → i < depth →
        (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true) →
      (∀ y, (∀ k, stop < k → k ≤ depth → y ≠ X k) → w'.taken.contains y = w.taken.contains y) →
      w'.top = w.top → w'.vals = w.vals →
      (∀ y, y ≠ X stop → (∀ k, stop < k → k ≤ depth → y ≠ X k) → w'.nodes.lookup y = w.nodes.lookup y) →
      w'.nodes.lookup (X stop) = some sn' → sn'.leaf = (Nn stop).leaf → klongsWf sn'.ks = true →
      (∀ s, Klong.time s ∈ sn'.ks → s ≤ c.i) →
      (∀ c' z, (c', z) ∈ sn'.liveAt c.i ↔ (c', z) ∈ (Nn stop).liveAt c.i ∧ c' ≠ K (stop + 1)) →
      (∀ key', keyWf key' = true →
        wGet c.p c.i base w' key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key') →
      (∀ k, stop < k → k ≤ depth → ChainFate c.i w' (X k)) →
      (∀ k, stop < k → k ≤ depth → ChainFateW c.i B w' (Nn k) (X k)) →
      (∃ S, RetFormS c.i B (Nn stop) S ∧
        ((Nn (stop + 1)).firstTime = some c.i → RetFrom c.i B (Nn stop) (X (stop + 1)) S) ∧
        BitmapOf S sn' c.i (K (stop + 1))) →
      TakeJ2 c base B w' → CollGetInv c base w' w' → J w' →
      ∀ gs hs : Nat, RWP (aC1 (pre ++ [cv]) gs hs) (aC2 (pre ++ [cv]) gs hs) c w')
    (hcascLeaf : ∀ (stop : Nat) (w2 : W) (S : KNode), stop < depth →
      (∀ i, stop < i → i < depth →
        (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true) →
      UpLoopEnd c B X Nn depth stop w w2 S → J w2 → (Nn stop).leaf = true →
      ¬ DelRoom c (K (stop + 1)) S → ∀ gs hs : Nat,
      WriterWP (appendDeleteKlong (X stop) stop (K (stop + 1))) c
        { w2 with trail := "up.stop-at-segment-leaf" :: w2.trail }
        (fun _ w3 => RWP (aC1 (pre ++ [cv]) gs hs) (aC2 (pre ++ [cv]) gs hs) c w3))
    :
    RWP (deleteUpwardP2 aK aC1 (X depth) depth cv (pre ++ [cv]))
      (deleteUpwardP2 aK aC2 (X depth) depth cv (pre ++ [cv])) c w := by
  obtain ⟨hTt, hD, hO, hS, hM, hV⟩ := hJ2
  have hN : ∀ i, i ≤ depth → wNode c.p base w (X i) = some (Nn i) := fun i hi => by
    simp only [wNode, htk i hi, Bool.false_eq_true, ↓reduceIte, hlk i hi]
  have hpost := collGetInv_after_upT c base X Nn K depth w hlk htk hdist hT hwf hRt hTimesR hICE hfit
    hnovalAll hreach hlinkK
  -- the facts after the stop node's change, before root collapse
  have hafter : ∀ (stop : Nat) (w' : W) (sn' : KNode), stop < depth →
      (∀ i, stop < i → i < depth →
        (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true) →
      (∀ y, (∀ k, stop < k → k ≤ depth → y ≠ X k) → w'.taken.contains y = w.taken.contains y) →
      w'.top = w.top →
      (∀ y, y ≠ X stop → (∀ k, stop < k → k ≤ depth → y ≠ X k) → w'.nodes.lookup y = w.nodes.lookup y) →
      w'.nodes.lookup (X stop) = some sn' →
      (∀ c' z, (c', z) ∈ (Nn stop).liveAt c.i → z ≠ X (stop + 1) → ∃ c'', (c'', z) ∈ sn'.liveAt c.i) →
      (∀ k, stop < k → k ≤ depth → ChainFate c.i w' (X k)) →
      TtReachedN (wNode c.p base w') c.i w'.top.rootKey := by
    intro stop w' sn' hsD hbetween ht htop hnodes hsn' hkeep hfate
    have hXs : ∀ k, stop < k → k ≤ depth → X stop ≠ X k :=
      fun k h1 h2 he => by have := hdist _ _ (by omega) h2 he; omega
    have hsnw : wNode c.p base w' (X stop) = some sn' := by
      simp only [wNode, ht (X stop) hXs, htk stop (by omega), Bool.false_eq_true, ↓reduceIte, hsn']
    have hone' : ∀ i, stop < i → i < depth → ∀ c' z, (c', z) ∈ (Nn i).liveAt c.i → z = X (i + 1) := by
      intro i h1 h2 c' z hm
      have hti := htimes i (by omega)
      have hm' : (c', z) ∈ (Nn i).live := by rw [← KNode.liveAt_of_times _ c.i hti]; exact hm
      have hc := allKeysIn_live_cv (Nn i) (K (i + 1)) (hbetween i h1 h2) c' z hm'
      have hl := hlinkK (i + 1) (by omega) (by omega)
      rw [show i + 1 - 1 = i by omega] at hl
      rw [KNode.liveAt_of_times _ c.i hti] at hl
      have hnd := KNode.live_keys_nodup (Nn i)
      have e1 := lookup_some_of_mem hnd hm'
      have e2 := lookup_some_of_mem hnd hl
      rw [hc] at e1
      rw [e1] at e2
      exact Option.some.inj e2
    rw [htop]
    refine ttReachedN_up (wNode c.p base w) (wNode c.p base w') c.i w.top.rootKey X Nn stop depth hsD
      (fun i _ h2 => hN i h2) hone' hkids sn' hsnw hkeep
      (fun u hus hnc => by simp only [wNode, ht u hnc, hnodes u hus hnc]) hXs (hreach stop (by omega))
      ?_ hTt
    intro k h1 h2 un hun
    rcases hfate k h1 h2 with hf | ⟨S0, hS1, hS2⟩
    · unfold wNode at hun
      rw [hf] at hun
      cases hun
    · have hkt : w'.taken.contains (X k) = false := by
        cases hc : w'.taken.contains (X k) with
        | false => rfl
        | true =>
          unfold wNode at hun
          rw [hc] at hun
          cases hun
      simp only [wNode, hkt, Bool.false_eq_true, ↓reduceIte, hS1, Option.some.injEq] at hun
      rw [← hun]
      exact hS2
  -- the stop node keeps its other live klongs, after a bitmap
  have hkeepBit : ∀ (stop : Nat) (sn' : KNode), stop < depth →
      (∀ c' z, (c', z) ∈ sn'.liveAt c.i ↔ (c', z) ∈ (Nn stop).liveAt c.i ∧ c' ≠ K (stop + 1)) →
      ∀ c' z, (c', z) ∈ (Nn stop).liveAt c.i → z ≠ X (stop + 1) → ∃ c'', (c'', z) ∈ sn'.liveAt c.i := by
    intro stop sn' hsD hlive' c' z hm hz
    refine ⟨c', (hlive' c' z).mpr ⟨hm, fun hck => hz ?_⟩⟩
    have hl := hlinkK (stop + 1) (by omega) (by omega)
    rw [show stop + 1 - 1 = stop by omega] at hl
    rw [hck] at hm
    exact (KNode.liveAt_fun _ _ _ _ _ hl hm).symm
  -- (C) and the node facts after the stop node's change
  have hrestJ : ∀ (stop : Nat) (w' : W) (sn' S : KNode) (Extra : NodeId → Prop), stop < depth →
      (∀ y, (∀ k, stop < k → k ≤ depth → y ≠ X k) → w'.taken.contains y = w.taken.contains y) →
      (∀ y, y ≠ X stop → (∀ k, stop < k → k ≤ depth → y ≠ X k) → w'.nodes.lookup y = w.nodes.lookup y) →
      w'.nodes.lookup (X stop) = some sn' →
      (∀ k, stop < k → k ≤ depth → ChainFateW c.i B w' (Nn k) (X k)) →
      RetFormS c.i B (Nn stop) S →
      ((Nn (stop + 1)).firstTime = some c.i → RetFrom c.i B (Nn stop) (X (stop + 1)) S) →
      prefixAt sn'.ks (c.i - 1) = prefixAt S.ks (c.i - 1) →
      (∀ s, S.firstTime = some s → sn'.firstTime = some s) →
      (∀ (i c' : Nat) (y : NodeId), sn'.ks[i]? = some (Klong.key c' y) →
        S.ks[i]? = some (Klong.key c' y) ∨ Extra y) →
      (∀ y, Extra y → (∃ c', (c', y) ∈ sn'.liveAt c.i) ∧ sn'.leaf = false) →
      (∀ c' y, (c', y) ∈ (Nn stop).liveAt c.i → c' ≠ K (stop + 1) → ∃ c'', (c'', y) ∈ sn'.liveAt c.i) →
      (sn'.leaf = true → S.leaf = true ∧ ∀ (i c' : Nat), LastLive S.ks S.lastBitmap i c' →
        c' ≠ K (stop + 1) → LastLive sn'.ks sn'.lastBitmap i c') →
      DeadLiveN (wNode c.p base w') c.i B (w.vals.map (·.1)) ∧ OldBelowN (wNode c.p base w') c.i B ∧
        OldStartN (wNode c.p base w') c.i B ∧ MadeStartN (wNode c.p base w') c.i B ∧
        ValsNoNodeN (wNode c.p base w') (w.vals.map (·.1)) := by
    intro stop w' sn' S Extra hsD ht hnodes hsn' hfJ hSR hSF hspre hsft hskey hsextra hskeep hsleaf
    have hXs : ∀ k, stop < k → k ≤ depth → X stop ≠ X k :=
      fun k h1 h2 he => by have := hdist _ _ (by omega) h2 he; omega
    have hsnw : wNode c.p base w' (X stop) = some sn' := by
      simp only [wNode, ht (X stop) hXs, htk stop (by omega), Bool.false_eq_true, ↓reduceIte, hsn']
    have hlink : (K (stop + 1), X (stop + 1)) ∈ (Nn stop).liveAt c.i := by
      have := hlinkK (stop + 1) (by omega) (by omega); simpa using this
    have hwfs : klongsWf (Nn stop).ks = true := hwf _ _ (hreach stop (by omega)) (hN stop (by omega))
    refine j2rest_up (wNode c.p base w) (wNode c.p base w') c.i B _ X Nn stop depth (K (stop + 1)) hsD
      hpos hD hO hS hM hV (fun i _ h2 => hN i h2) (fun i i' _ h2 _ h4 he => hdist i i' h2 h4 he) ?_
      hwfs (htimes stop (by omega)) hlink S sn' Extra hSR hSF hsnw hspre hsft hskey hsextra hskeep
      hsleaf (fun u hus hnc => by simp only [wNode, ht u hnc, hnodes u hus hnc])
    intro k h1 h2
    obtain ⟨hm, hu⟩ := hfJ k h1 h2
    refine ⟨fun hf => by simp only [wNode, hm hf, ↓reduceIte], fun hf => ?_⟩
    obtain ⟨ht0, S0, hS0, hl0⟩ := hu hf
    exact ⟨S0, hS0, by simp only [wNode, ht0, Bool.false_eq_true, ↓reduceIte, hl0]⟩
  refine rwp_deleteUpwardP2_climb aK aC1 aC2 (pre ++ [cv]) c base X Nn K depth cv B w J hJ0 hJnote hJtake
    hJunlink hMF hdepth hpos hp hk hlk htk htimes hdist hne hall hwf hreach ?_
  intro stop w2 S hsD hbetween hLE hJw2 hsl gs hs
  · by_cases hDR : DelRoom c (K (stop + 1)) S
    · have hJv := hJnote "up.stop-at-segment-leaf" w2 hJw2
      refine writerWP_mono (writerWP_and (writerWP_upStop_bitmapD c base X Nn K depth cv pre rk B w hfuel hlk htk
        htimes hdist hall hleaf hT hR hwf hreach hlinkK (fun i hi => hnovalAll _ _ (hN i hi)) hrk hcv hvisL huniq
        stop w2 S hsD hbetween hLE (Or.inl hsl) hDR ({ w2 with trail := "up.stop-at-segment-leaf" :: w2.trail } : W)
        rfl rfl rfl rfl
        (fun w' => J w' → RWP (aC1 (pre ++ [cv]) gs hs) (aC2 (pre ++ [cv]) gs hs) c w') ?_)
        (hJadk _ _ _ _ S hJv (hp stop (by omega)) hLE.2.2.2.2.2.2.2.1 hDR)) (fun _ w' h => h.1 h.2)
      · intro w' sn' ht htop hv hnodes hsn' hsl' hsw' hst' hlive' hread hfate hfJ hst hJw'
        have hI := hpost stop w' sn' id hsD ht htop hv hnodes hsn' hsl' hsw' hst'
          (fun c' z h => ⟨c', ((hlive' c' z).mp h).1, ((hlive' c' z).mp h).2, rfl⟩)
        have hst0 := hst
        obtain ⟨S', hSR, hSF, hbm⟩ := hst
        have hJ : TakeJ2 c base B w' := by
          unfold TakeJ2
          rw [hv]
          refine ⟨hafter stop w' sn' hsD hbetween ht htop hnodes hsn' (hkeepBit stop sn' hsD hlive') hfate, ?_⟩
          exact hrestJ stop w' sn' S' (fun _ => False) hsD ht hnodes hsn' hfJ hSR hSF
            (bitmapOf_prefix S' sn' c.i _ hbm hpos) (bitmapOf_firstTime S' sn' c.i _ hbm)
            (fun i c' y h => Or.inl (bitmapOf_key S' sn' c.i _ hbm i c' y h)) (fun y h => h.elim)
            (fun c' y hm hc => ⟨c', (hlive' c' y).mpr ⟨hm, hc⟩⟩)
            (fun hl => ⟨by rw [← bitmapOf_leaf S' sn' c.i _ hbm]; exact hl,
              fun i c' hL hc => bitmapOf_lastLive S' sn' c.i _ hbm i c' hL hc⟩)
        exact hleafM stop w' sn' hsD hbetween ht htop hv hnodes hsn' hsl' hsw' hst' hlive' hread hfate hfJ hst0
          hJ hI hJw' gs hs
    · exact hcascLeaf stop w2 S hsD hbetween hLE hJw2 hsl hDR gs hs


set_option maxHeartbeats 3200000 in
/-- `writerWP_del_emptyAnyMJKLHG` for the two copies, from the leaf the descent
found: the upward delete that empties a leaf below the space root reaches its
stop node's call of `afterDelete` at a state with `DelInvJ` and the books (with
room by the bitmap's facts, full by `UpCascJ2OKHG`), where the two calls run
alike (`hK`). -/
theorem rwp_climb_of_J (aK aC1 aC2 : Key → Nat → Nat → M Unit) (c : Ctx) (base : View BVal)
    (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B)
    (KO : KindOracle) (BK : NodeId) (hvB : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c)
    (hI : PutInv c base w) (hRO : RangeOrder (wNode c.p base w) c.i w.top.rootKey)
    (hF : SegFits (wNode c.p base w) c.i (c.p.fuel - 1) w.top.rootKey)
    (hICE : InnerChildrenExist (wNode c.p base w) c.i w.top.rootKey)
    (hkey : keyWf (pre ++ [cv]) = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (H : NodeId → Nat → Prop) (hC : UpCascJ2OKHG c base KO BK B H)
    (hLC : LiveCounts c.p (wNode c.p base w) c.i w.top.rootKey)
    (hsa2 : 2 ≤ c.p.splitAbove) (hICEk : ICEFromKinds c base KO BK)
    (hm : c.p.merges = true) (hpos : 0 < c.i)
    (hJ2 : TakeJ2 c base B w) (hMF : ∀ x o, w.madeFor.lookup x = some o → o < B)
    (hLV : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true → ∀ y, (cv, y) ∈ n.liveAt c.i →
      wNode c.p base w y = none)
    (hK : ∀ g h v, DelInvJ c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK B v → PutBook c B top0 v →
      RWP (aC1 (pre ++ [cv]) g h) (aC2 (pre ++ [cv]) g h) c v)
    (L : NodeId) (n : KNode) (P : List (Option Nat × NodeId)) (w3 : W)
    (hL : (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk) (hn : wNode c.p base w L = some n)
    (hnl : n.leaf = true) (hr03 : ReadsAs c.p base w w3)
    (hJ3 : KdHtJ c B top0 KO BK H w3 ∧ w3.madeFor = w.madeFor)
    (hp3' : w3.path = (none, w.top.rootKey) :: P)
    (hlinkP : LinkedFrom (wNode c.p base w) c.i w.top.rootKey P)
    (hXD : nodeAt w.top.rootKey P P.length = L)
    (hlkX : ∀ i, i ≤ P.length → w3.nodes.lookup (nodeAt w.top.rootKey P i) =
      some ((wNode c.p base w (nodeAt w.top.rootKey P i)).getD n))
    (hne : bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap)
    (hall : n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = true) (hLr : L ≠ w.top.rootKey) :
    RWP (deleteUpwardP2 aK aC1 L P.length cv (pre ++ [cv])) (deleteUpwardP2 aK aC2 L P.length cv (pre ++ [cv]))
      c w3 := by
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hb3 := hJ3.1.1
  have hlen3 : w3.path.length = P.length + 1 := by rw [hp3']; simp
  have hMF3 : ∀ x o, w3.madeFor.lookup x = some o → o < B := by rw [hJ3.2]; exact hMF
  have hJ23 : TakeJ2 c base B w3 := takeJ2_of_readsAs c base B w w3 hJ2 hr03
  have hdepth : 0 < P.length := by
    rcases Nat.eq_zero_or_pos P.length with h | h
    · exfalso; apply hLr; rw [← hXD, h]; simp [nodeAt]
    · exact h
  -- the path, at w
  have hgetP := LinkedFrom.get _ _ _ P hlinkP
  have hXN : ∀ i, i ≤ P.length → wNode c.p base w (nodeAt w.top.rootKey P i) =
      some ((wNode c.p base w (nodeAt w.top.rootKey P i)).getD n) := by
    intro i hi
    rcases Nat.lt_or_ge i P.length with hlt | hge
    · obtain ⟨_, n', _, h2, _⟩ := hgetP i hlt
      rw [h2]; rfl
    · have : i = P.length := by omega
      subst this
      rw [hXD, hn]; rfl
  have hKP : ∀ i, 0 < i → i ≤ P.length →
      P[i - 1]? = some (some (((P[i - 1]?).bind (·.1)).getD 0), nodeAt w.top.rootKey P i) ∧
      (((P[i - 1]?).bind (·.1)).getD 0, nodeAt w.top.rootKey P i) ∈
        ((wNode c.p base w (nodeAt w.top.rootKey P (i - 1))).getD n).liveAt c.i := by
    intro i h1 h2
    obtain ⟨k, n', e1, e2, e3⟩ := hgetP (i - 1) (by omega)
    have hi : i - 1 + 1 = i := by omega
    rw [hi] at e1 e3
    rw [e1, e2]
    exact ⟨rfl, e3⟩
  have hPL := LinkedFrom.pathLen _ _ _ P hlinkP
  have hreachX : ∀ i, i ≤ P.length →
      TReach (wNode c.p base w) c.i w.top.rootKey (nodeAt w.top.rootKey P i) :=
    fun i hi => (hPL i hi).reach
  have hdistP : ∀ i i', i ≤ P.length → i' ≤ P.length →
      nodeAt w.top.rootKey P i = nodeAt w.top.rootKey P i' → i = i' := by
    intro i i' h1 h2 he
    have a := hPL i h1
    have b := hPL i' h2
    rw [he] at a
    exact PathLen.depth_unique hI.tree _ _ _ a b
  have hpX : ∀ i, i ≤ P.length → (w3.path[i]?).map (·.2) = some (nodeAt w.top.rootKey P i) := by
    intro i hi
    have hl : i < (w.top.rootKey :: P.map (·.2)).length := by simp; omega
    rw [hp3', ← List.getElem?_map, List.map_cons, List.getElem?_eq_getElem hl]
    simp [nodeAt, List.getElem?_eq_getElem hl]
  have hpK : ∀ i, 0 < i → i ≤ P.length →
      w3.path[i]? = some (some (((P[i - 1]?).bind (·.1)).getD 0), nodeAt w.top.rootKey P i) := by
    intro i h1 h2
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    rw [hp3', List.getElem?_cons_succ]
    exact (hKP (j + 1) h1 h2).1
  -- the facts at w3
  have hN3 : ∀ i, i ≤ P.length → wNode c.p base w3 (nodeAt w.top.rootKey P i) =
      some ((wNode c.p base w (nodeAt w.top.rootKey P i)).getD n) := fun i hi => by
    rw [hr03.1]; exact hXN i hi
  have htk3 : ∀ i, i ≤ P.length → w3.taken.contains (nodeAt w.top.rootKey P i) = false := fun i hi => by
    rw [hr03.2.2.1]; exact hI.untaken _ (tReach_reachS _ _ _ _ (hreachX i hi))
  have hT3 : TreeOK (wNode c.p base w3) c.i w3.top.rootKey := by rw [hr03.1, hr03.2.1]; exact hI.tree
  have hR3 : RangeOrder (wNode c.p base w3) c.i w3.top.rootKey := by rw [hr03.1, hr03.2.1]; exact hRO
  have hwf3 : ∀ x xn, TReach (wNode c.p base w3) c.i w3.top.rootKey x → wNode c.p base w3 x = some xn →
      klongsWf xn.ks = true := fun x xn _ h => by rw [hr03.1] at h; exact hI.wf x xn h
  have hRt3 : ∀ y, TReach (wNode c.p base w3) c.i w3.top.rootKey y → w3.taken.contains y = false := by
    intro y hy
    rw [hr03.1, hr03.2.1] at hy
    rw [hr03.2.2.1]
    exact hI.untaken y (tReach_reachS _ _ _ _ hy)
  have hTimesR3 : ∀ y yn, TReach (wNode c.p base w3) c.i w3.top.rootKey y → wNode c.p base w3 y = some yn →
      ∀ s, Klong.time s ∈ yn.ks → s ≤ c.i := fun y yn _ h => by rw [hr03.1] at h; exact hI.times y yn h
  have hICE3 : InnerChildrenExist (wNode c.p base w3) c.i w3.top.rootKey := by
    rw [hr03.1, hr03.2.1]; exact hICE
  have hfit3 : SegFits (wNode c.p base w3) c.i (c.p.fuel - 1) w3.top.rootKey := by
    rw [hr03.1, hr03.2.1]; exact hF
  have hnovalAll3 : ∀ y yn, wNode c.p base w3 y = some yn → wValue base w3 y = none := by
    intro y yn h
    rw [hr03.1] at h
    rw [ReadsAs.value _ _ _ _ hr03]
    exact hI.keyNoValue y yn h
  have hreach3 : ∀ i, i ≤ P.length →
      TReach (wNode c.p base w3) c.i w3.top.rootKey (nodeAt w.top.rootKey P i) := fun i hi => by
    rw [hr03.1, hr03.2.1]; exact hreachX i hi
  have hlinkK : ∀ i, 0 < i → i ≤ P.length →
      (((P[i - 1]?).bind (·.1)).getD 0, nodeAt w.top.rootKey P i) ∈
        ((wNode c.p base w (nodeAt w.top.rootKey P (i - 1))).getD n).liveAt c.i :=
    fun i h1 h2 => (hKP i h1 h2).2
  have hNnD : (wNode c.p base w (nodeAt w.top.rootKey P P.length)).getD n = n := by rw [hXD, hn]; rfl
  -- DelInvF at a continuation of the upward delete
  have hD : ∀ (stop : Nat) (w' : W) (sn' : KNode) (f : Nat → Nat), stop < P.length →
      (∀ y, (∀ k, stop < k → k ≤ P.length → y ≠ nodeAt w.top.rootKey P k) →
        w'.taken.contains y = w3.taken.contains y) →
      w'.top = w3.top → w'.vals = w3.vals →
      (∀ y, y ≠ nodeAt w.top.rootKey P stop → (∀ k, stop < k → k ≤ P.length → y ≠ nodeAt w.top.rootKey P k) →
        w'.nodes.lookup y = w3.nodes.lookup y) →
      w'.nodes.lookup (nodeAt w.top.rootKey P stop) = some sn' →
      sn'.leaf = ((wNode c.p base w (nodeAt w.top.rootKey P stop)).getD n).leaf →
      klongsWf sn'.ks = true → (∀ s, Klong.time s ∈ sn'.ks → s ≤ c.i) →
      (∀ c' z, (c', z) ∈ sn'.liveAt c.i →
        ∃ c0, (c0, z) ∈ ((wNode c.p base w (nodeAt w.top.rootKey P stop)).getD n).liveAt c.i ∧
          c0 ≠ ((P[stop + 1 - 1]?).bind (·.1)).getD 0 ∧ f c0 = c') →
      RangeOrder (wNode c.p base w') c.i w'.top.rootKey →
      PutBook c B top0 w' →
      (∀ key', keyWf key' = true →
        wGet c.p c.i base w' key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w3 key') →
      DelInvF c base w (pre ++ [cv]) (c.p.fuel + 1) w' := by
    intro stop w' sn' f hsD ht htop hv hnodes hsn' hsl' hsw' hst' hlive' hRO' hb' hread
    have hCG := collGetInv_after_upT c base (fun i => nodeAt w.top.rootKey P i)
      (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
      (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length w3 hlkX htk3 hdistP hT3 hwf3 hRt3 hTimesR3
      hICE3 hfit3 hnovalAll3 hreach3 hlinkK stop w' sn' f hsD ht htop hv hnodes hsn' hsl' hsw' hst' hlive'
    exact delInvF_of_collGetInv c base B top0 hB w w3 w' (pre ++ [cv]) hI hF hr03 hCG hRO' hb' hread
  -- the frame facts at a continuation
  have hXs : ∀ stop, stop < P.length → ∀ k, stop < k → k ≤ P.length →
      nodeAt w.top.rootKey P stop ≠ nodeAt w.top.rootKey P k :=
    fun stop _ k h1 h2 he => by have := hdistP _ _ (by omega) h2 he; omega
  have hfr : ∀ (stop : Nat) (w' : W) (sn' : KNode), stop < P.length →
      (∀ y, (∀ k, stop < k → k ≤ P.length → y ≠ nodeAt w.top.rootKey P k) →
        w'.taken.contains y = w3.taken.contains y) →
      (∀ y, y ≠ nodeAt w.top.rootKey P stop → (∀ k, stop < k → k ≤ P.length → y ≠ nodeAt w.top.rootKey P k) →
        w'.nodes.lookup y = w3.nodes.lookup y) →
      w'.nodes.lookup (nodeAt w.top.rootKey P stop) = some sn' →
      (∀ u, u ≠ nodeAt w.top.rootKey P stop → (∀ i, stop < i → i ≤ P.length → u ≠ nodeAt w.top.rootKey P i) →
        wNode c.p base w' u = wNode c.p base w3 u) ∧
      wNode c.p base w' (nodeAt w.top.rootKey P stop) = some sn' := by
    intro stop w' sn' hsD ht hnodes hsn'
    refine ⟨fun u hus hnc => by simp only [wNode, ht u hnc, hnodes u hus hnc], ?_⟩
    simp only [wNode, ht _ (hXs stop hsD), htk3 stop (by omega), Bool.false_eq_true, ↓reduceIte, hsn']
  rw [← hXD]
  have hcvAll : ∀ c' z, (c', z) ∈ n.liveAt c.i → c' = cv := by
    intro c' z hm'
    have hnt := hI.times L n hn
    have hm2 : (c', z) ∈ n.live := by rw [← KNode.liveAt_of_times _ c.i hnt]; exact hm'
    exact allKeysIn_live_cv n cv hall c' z hm2
  have hvisw : (nodeAt w.top.rootKey P P.length, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk := by
    rw [hXD]; exact hL
  have hne' := hne
  have hall' := hall
  rw [← hNnD] at hne' hall'
  have hnl' : ((wNode c.p base w (nodeAt w.top.rootKey P P.length)).getD n).leaf = true := by
    rw [hNnD]; exact hnl
  have hkidsw : ∀ c' z, (c', z) ∈ ((wNode c.p base w (nodeAt w.top.rootKey P P.length)).getD n).liveAt c.i →
      wNode c.p base w z = none := by
    intro c' z hz
    rw [hNnD] at hz
    have := hcvAll c' z hz
    subst this
    exact hLV L n hL hn hnl z hz
  refine rwp_deleteUpwardP2_climbMB aK aC1 aC2 c base (fun i => nodeAt w.top.rootKey P i)
    (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
    (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length cv pre rk B w3 hdepth hfuel hpos hpX hpK hlkX htk3
    (fun i hi => hTimesR3 _ _ (hreach3 i hi) (hN3 i hi))
    hdistP (by rw [hNnD]; exact hne) (by rw [hNnD]; exact hall) (by rw [hNnD]; exact hnl) hT3 hR3 hwf3 hRt3
    hTimesR3 hICE3 hfit3 hnovalAll3 hreach3
    hlinkK (by rw [hr03.1, hr03.2.1]; exact hrk)
    (keyWf_last_notin pre cv hkey) (by rw [hr03.1, hXD]; exact hL)
    (by rw [hr03.1, hr03.2.1]; exact hI.keyUniq pre cv rk hkey hrk)
    (fun c' z hz => by
      rw [hNnD] at hz
      have := hcvAll c' z hz
      subst this
      rw [hr03.1]; exact hLV L n hL hn hnl z hz) hJ23 hMF3
    (fun v => KdJP c B top0 KO BK w3.path v ∧ v.gh = w3.gh) ⟨⟨hb3, rfl⟩, rfl⟩
    (fun s v hJ => ⟨kdJP_note c base B top0 hB KO BK hvB hk _ s v hJ.1, hJ.2⟩)
    (fun x q k v hJ hx hq => writerWP_mono (writerWP_and
      (kdJP_takeBack c base B top0 hB KO BK hvB hk _ x q k v hJ.1 hx) (writerWP_takeBack_gh x q k c v hq))
      (fun _ v' h => ⟨h.1, h.2.trans hJ.2⟩))
    (fun x v hJ hx => writerWP_mono (writerWP_and
      (kdJP_unlink c base B top0 hB KO BK hvB hk _ x v hJ.1) (writerWP_unlink_gh x c v hx))
      (fun _ v' h => ⟨h.1, h.2.trans hJ.2⟩))
    (fun x d k v xn hJ hx hxn hDR => writerWP_mono (writerWP_and
      (kdJP_appendDeleteKlong c base B top0 hB KO BK hvB hk _ x d k v hJ.1 hx)
      (writerWP_appendDeleteKlong_room_gh x d k xn c v hxn hDR))
      (fun _ v' h => ⟨h.1, h.2.trans hJ.2⟩)) ?_ ?_
  · intro stop w' sn' hsD hbetween ht htop hv hnodes hsn' hsl' hsw' hst' hlive' hread _ _ _ hJv _ hb'G gs hs
    have hb' := hb'G.1
    obtain ⟨hagree, hsnw⟩ := hfr stop w' sn' hsD ht hnodes hsn'
    have hRO' : RangeOrder (wNode c.p base w') c.i w'.top.rootKey := by
      rw [htop]
      exact rangeOrder_up_bitmap (wNode c.p base w3) (wNode c.p base w') c.i w3.top.rootKey _ _ _ stop
        P.length hsD hR3 hT3 (hreach3 stop (by omega)) (fun i _ h2 => hN3 i h2)
        (fun i h1 h2 => hlinkK i (by omega) h2) (fun i i' _ h2 _ h4 he => hdistP i i' h2 h4 he)
        hagree sn' hsnw hsl' (fun c' z h => (hlive' c' z).mp h)
    have hDv := hD stop w' sn' id hsD ht htop hv hnodes hsn' hsl' hsw' hst'
      (fun c' z h => ⟨c', ((hlive' c' z).mp h).1, ((hlive' c' z).mp h).2, rfl⟩) hRO' hb'.1.1 hread
    exact hK gs hs w' ⟨⟨hDv, hb'.1.2.1, hb'.1.2.2⟩, hJv, hb'.1.1.fresh.1⟩ hb'.1.1
  · intro stop w2 S hsD hbetween hLE hJw2G hsl hDR gs hs
    obtain ⟨hJw2, hgh2⟩ := hJw2G
    have hJv := kdJP_note c base B top0 hB KO BK hvB hk _ "up.stop-at-segment-leaf" w2 hJw2
    refine writerWP_mono (writerWP_and (hC w w3 top0 pre cv rk (fun i => nodeAt w.top.rootKey P i)
      (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
      (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length stop w2 _ S hm hLC hJ3.1 hlen3 hgh2 hsa2 hvB hk hICEk
      (by simp [nodeAt]) hpos hB hI hRO hF hICE hr03 hkey hrk
      hvisw hpX hpK hlkX hXN hlinkK hne' hall' hnl' hdepth hsD hbetween hLE (Or.inr ⟨_, rfl⟩)
      hJv (Or.inl hsl) hDR hJ2 hMF3 hkidsw)
      (kdJP_appendDeleteKlong c base B top0 hB KO BK hvB hk _ _ stop _ _ hJv (hpX stop (by omega)))) ?_
    rintro _ w' ⟨hD', hJ'⟩
    exact hK gs hs w' hD' hJ'.1.1

/-! ## The other leaves: no stop node's call -/

/-- A leaf whose bitmap changes nothing or that keeps a live klong: the stop
node's call is not reached. -/
theorem rwp_deleteUpwardP2_noClimb (aK aC1 aC2 : Key → Nat → Nat → M Unit) (c : Ctx) (L : NodeId) (n : KNode)
    (d cv : Nat) (key : Key) (w : W) (hlk : w.nodes.lookup L = some n)
    (h : bitsUnion n.lastBitmap (n.bitsOf cv) = n.lastBitmap ∨
      n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false) :
    RWP (deleteUpwardP2 aK aC1 L d cv key) (deleteUpwardP2 aK aC2 L d cv key) c w := by
  unfold deleteUpwardP2
  refine rwp_read ?_
  refine rwp_getNode_known L n hlk ?_
  refine rwp_ite (fun _ => rwp_refl _ _ _) (fun hne => ?_)
  refine rwp_ite (fun _ => rwp_refl _ _ _) (fun hk => ?_)
  exfalso
  rcases h with h | h
  · exact hne (by simp [h])
  · exact hk (by simp [h])

/-- The space root as the emptied leaf: the climb stops at it, and the stop node's
call is not reached. -/
theorem rwp_deleteUpwardP2_root (aK aC1 aC2 : Key → Nat → Nat → M Unit) (c : Ctx) (L : NodeId) (n : KNode)
    (cv : Nat) (key : Key) (w : W) (hlk : w.nodes.lookup L = some n)
    (hp0 : (w.path[0]?).map (·.2) = some L) :
    RWP (deleteUpwardP2 aK aC1 L 0 cv key) (deleteUpwardP2 aK aC2 L 0 cv key) c w := by
  unfold deleteUpwardP2
  refine rwp_read ?_
  refine rwp_getNode_known L n hlk ?_
  refine rwp_ite (fun _ => rwp_refl _ _ _) (fun _ => ?_)
  refine rwp_ite (fun _ => rwp_refl _ _ _) (fun _ => ?_)
  refine rwp_bind _ (writerWP_climb c (fun _ => L) (fun _ => n) (fun _ => 0) 0 w
    (fun i hi => by rw [show i = 0 by omega]; exact hp0) (fun i h1 h2 => by omega)
    (fun i _ => hlk)) ?_
  rintro stop v ⟨hv, hst, -⟩
  have h0 : stop = 0 := by omega
  subst h0
  simp only [beq_self_eq_true, ↓reduceIte]
  exact rwp_refl _ _ _

/-! ## The premise with the merges' check only -/

/-- The copy that checks, at each call of `afterDelete`, only that the merges'
loop runs as its copy with the merge's `checkFree`. -/
noncomputable def putKvDelChk8 (key : Key) : M Bool := putKvDP (afterDeleteJ (fun _ => True)) key

/-- `OpDelChk7OKR` with `putKvDelChk8`: at the deletes of the runs of R, the
delete runs as its copy whose only check is the merge's `checkFree`. -/
def OpDelChk8OKR (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre key post, tx.ops = pre ++ Op.del key :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w →
    RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey →
    LiveCounts p (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey →
    HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) w →
    J2At p (treeRun p ts) (ts.length + 1) tx.base w →
    ∀ r' v, putKv (.del key) (ctxOf p ts) w = .ok (r', v) →
      putKvDelChk8 key (ctxOf p ts) w = .ok (r', v)

/-- `OpDelChk8OKR` at the induction's runs. -/
def OpDelChk8OKL (p : Params) : Prop := OpDelChk8OKR p (RunTreeQ p (LatestQD p))

set_option maxHeartbeats 3200000 in
/-- `OpDelChk7OKR` from `OpDelChk8OKR`: at the upward delete's call of
`afterDelete`, after its stop node's bitmap, `DelHoleJ` holds
(`rwp_climb_of_J`; the other leaves do not reach that call). -/
theorem opDelChk7OKR_of_chk8 (p : Params) (R : Struct BVal → Time → Prop) (hM4 : 4 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove) (hm : p.merges = true)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRP : ∀ P t, R P t → PointersOK P)
    (hRK : ∀ P t, R P t → KindsAllOK p P) (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (htb : TakeBelowFuelDelOK p) (h8 : OpDelChk8OKR p R) : OpDelChk7OKR p R := by
  intro ts tx hw hr z top hz htop pre key post hs r w hpre hI hRO hLC hH hJ r' v he
  have h8' := h8 ts tx hw hr z top hz htop pre key post hs r w hpre hI hRO hLC hH hJ r' v he
  have hM : 2 ≤ p.M := by omega
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop pre r w hpre
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top pre (Op.del key :: post)
    hs r w hpre
  have hHS := htStart_of_ht p R hRL hRK hRH htb ts tx hw hr z top hz htop pre (Op.del key :: post) hs r w hpre hH
  have hF := segFits_of_htStart p ts tx w hHS
  obtain ⟨hvo, hkw, hbase, hHb, _, hhi, hwfw, hub⟩ := hHS
  have hICE := innerChildren_reachedR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top pre (Op.del key :: post) hs r w
    hpre (fun x hx => hI.untaken x (tReach_reachS _ _ _ _ hx))
  have hSV := leafVals_reached p hM ts tx hw top pre (Op.del key :: post) hs r w hpre (hRP _ _ hr) (hRK _ _ hr)
  have hkey' : keyWf key = true := within_op_keyWf p ts tx hw pre _ post hs
  have hJw : TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w := hJ
  have hMF := stateOK_madeFor p hM4 R hRL ts tx hw hr z top hz htop pre (Op.del key :: post) hs r w hpre
  have hpos : 0 < (ctxOf p ts).i := by simp [ctxOf]
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl (hRK _ _ hr)
      (hRP _ _ hr) hb hi.cache hun
  have hC := upCascJ2OKHGJ_of_noU (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base
    tx.base (htOracleOf p (treeRun p ts)) rfl (upCascFitsOKR_of _ _ _ _ _ hvo hbase hHb (by simp [ctxOf]))
  unfold putKvDelChk8 at h8'
  rw [putKvDP_eqG, deleteUpwardP_eq2] at h8'
  refine rwp_putKvG (ctxOf p ts) _ (viewCoherent_ctxOf p ts) w hI
    (fun v => KdHtJ (ctxOf p ts) tx.base top (kindOracleOf p (treeRun p ts)) tx.base (htOracleOf p (treeRun p ts)) v ∧
      v.madeFor = w.madeFor)
    (fun s f x v hJ' hx => writerWP_mono (writerWP_and
      (kdhtJ_descendLte _ top hB _ tx.base hv hk hvo hkw s f x v hJ'.1 hx)
      (writerWP_descendLte_madeFor s _ f x v)) (fun _ v' h => ⟨h.1, h.2.trans hJ'.2⟩))
    (fun s fd L n v hJ' hL hlk hleaf hfd =>
      ⟨kdhtJ_pathAdd _ top hB _ tx.base hv hvo s fd L n v hJ'.1 hL hlk hleaf hfd, hJ'.2⟩)
    ⟨kdhtJ_start _ top hB _ tx.base hv hvo w ⟨hbook, hb0, hi0⟩ hhi hwfw hub, rfl⟩ _ _ key ?_ _ h8'
  intro pre' cv rk L n P w3 hkey hrk hL hn hnl hr03 hJ3 hlk3 hp3' hlinkP hXD hlkX
  subst hkey
  by_cases hnc : bitsUnion n.lastBitmap (n.bitsOf cv) = n.lastBitmap ∨
      n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = false
  · exact rwp_deleteUpwardP2_noClimb _ _ _ _ L n _ cv _ w3 hlk3 hnc
  have hne : bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap := fun h => hnc (Or.inl h)
  have hall : n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = true := by
    cases h : n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) with
    | true => rfl
    | false => exact absurd (Or.inr h) hnc
  by_cases hLr : L = w.top.rootKey
  · have hP0 := path_nil_of_root _ _ w hI.tree P hlinkP (by rw [hXD, hLr])
    subst hP0
    exact rwp_deleteUpwardP2_root _ _ _ _ L n cv _ w3 hlk3 (by rw [hp3', ← hXD]; rfl)
  have hLV := leafVals_all hSV hkey' hrk
  exact rwp_climb_of_J _ _ _ (ctxOf p ts) _ pre' cv rk w tx.base top hB _ tx.base hv hk
    hI hRO hF hICE hkey' hrk _ hC hLC hsa2 hICEk hm hpos hJw hMF
    (fun L n hL hn hnl y hy => (hLV L n hL hn hnl y hy).1)
    (fun g h v hJv hbv => rwp_afterDeleteJ_true _ _ g h _ v ⟨hJv, hbv⟩)
    L n P w3 hL hn hnl hr03 hJ3 hp3' hlinkP hXD hlkX hne hall hLr

end SIS.Tree
