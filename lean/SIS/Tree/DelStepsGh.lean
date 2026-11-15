/-
The upward delete's walks with the heights' cache kept through the loop
(bergdb 024-12; that the loop keeps the heights' cache was a premise, now
proved): `writerWP_deleteUpward_stepJG` and `takeJ2_deleteUpward_stepMBKG` are
the upward delete's walks, of the reading (`writerWP_deleteUpward_stepJ`) and of
the take-back, whose steps know the nodes they read cached and, for the stop
node's bitmap with room, the room.
-/
import SIS.Tree.DelStepsHolderLive
import SIS.Tree.StopSwapBelow

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

set_option maxHeartbeats 1600000 in
/-- `writerWP_deleteUpward_stepJ` whose take-back and unlink steps know the
nodes they read cached. The upward delete that empties its leaf X depth, the merges on, given the
stop node's step at the loop's end (`UpLoopEnd`): a segment leaf's bitmap then
`afterDelete` (`hleafStep`), an inner node's bitmap (`hinnerStep`) or LE-b
(`hlebStep`) then the merges' loop and root collapse, each from the state the
loop leaves, with J kept through the loop (the notes, the take-backs, the
unlinks). -/
theorem writerWP_deleteUpward_stepJG (c : Ctx) (base : View BVal) (X : Nat → NodeId)
    (Nn : Nat → KNode) (K : Nat → Nat) (depth cv : Nat) (pre : List Nat)
    (B : NodeId) (w : W) (Q : W → Prop) (J : W → Prop) (hJ0 : J w)
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
    (hmerges : c.p.merges = true)
    (hleafStep : ∀ (stop : Nat) (w2 : W) (S : KNode), stop < depth →
      (∀ i, stop < i → i < depth →
        (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true) →
      UpLoopEnd c B X Nn depth stop w w2 S → J w2 → (Nn stop).leaf = true → ∀ gs hs : Nat,
      WriterWP (appendDeleteKlong (X stop) stop (K (stop + 1))) c
        { w2 with trail := "up.stop-at-segment-leaf" :: w2.trail }
        (fun _ w3 => WriterWP (afterDelete (pre ++ [cv]) gs hs) c w3 (fun _ w' => Q w')))
    (hinnerStep : ∀ (seg stop : Nat) (w2 : W) (S : KNode), stop < depth →
      (∀ i, stop < i → i < depth →
        (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true) →
      UpLoopEnd c B X Nn depth stop w w2 S → J w2 → (Nn stop).leaf = false → K (stop + 1) ≠ 0 →
      ∀ gs hs : Nat,
      WriterWP (appendDeleteKlong (X stop) stop (K (stop + 1))) c w2
        (fun _ w3 => WriterWP (mergeUp (pre ++ [cv]) gs c.p.fuel hs false) c w3 (fun _ w1 =>
          WriterWP (collapseRoot (pre ++ [cv]) seg c.p.fuel) c w1 (fun _ w' => Q w'))))
    (hlebStep : ∀ (seg stop : Nat) (w2 : W) (S : KNode), stop < depth →
      (∀ i, stop < i → i < depth →
        (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true) →
      UpLoopEnd c B X Nn depth stop w w2 S → J w2 → (Nn stop).leaf = false → K (stop + 1) = 0 →
      S.smallestLive = some 0 → ∀ gs hs : Nat,
      WriterWP (emptyKeyNext (X stop) stop) c w2
        (fun _ w3 => WriterWP (mergeUp (pre ++ [cv]) gs c.p.fuel hs false) c w3 (fun _ w1 =>
          WriterWP (collapseRoot (pre ++ [cv]) seg c.p.fuel) c w1 (fun _ w' => Q w')))) :
    WriterWP (deleteUpward (X depth) depth cv (pre ++ [cv])) c w (fun _ w' => Q w') := by
  unfold deleteUpward
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known _ _ c w (hlk depth (Nat.le_refl _))]
  have hne' : (bitsUnion (Nn depth).lastBitmap ((Nn depth).bitsOf cv) == (Nn depth).lastBitmap) = false := by
    simpa using hne
  simp only [hne', hall, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
  rw [writerWP_bind]
  refine writerWP_mono (writerWP_climb c X Nn K depth w hp hk hlk) ?_
  rintro stop w1 ⟨hw1, hst, hbetween, hmadeOK, hstopNode, hself⟩
  have hw1' := hw1.symm
  subst hw1'
  have hsd : stop ≠ depth := fun h => by have := (hself h).1; omega
  have hsd' : (stop == depth) = false := by simpa using hsd
  simp only [hsd', Bool.false_eq_true, ↓reduceIte]
  have hsD : stop < depth := by omega
  rw [writerWP_bind]
  refine (writerWP_note_iff _ c w _).mpr ?_
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
  rw [writerWP_bind, writerWP_get, writerWP_bind]
  refine writerWP_mono (writerWP_foldlM_getNode c (fun s n => if n.leaf = true then s + 1 else s)
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
  rw [writerWP_bind]
  refine writerWP_mono (writerWP_forIn_inv c I _ ?_ (List.range (depth - stop)) w0
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
  simp only [writerWP_bind]
  refine writerWP_pathNode_known stop (X stop) c w2 (by rw [h2p, h0p]; exact hp stop (by omega)) _ ?_
  refine writerWP_klongAt_known (stop + 1) (K (stop + 1)) (X (stop + 1)) c w2
    (by rw [h2p, h0p]; exact hk _ (by omega) (by omega)) _ ?_
  rw [writerWP_getNode_known _ _ c w2 hSl]
  refine writerWP_ghOf_cached _ _ c w2 hSl _ (fun gh => ?_)
  have hLE : UpLoopEnd c B X Nn depth stop w w2 S :=
    ⟨fun y hy => by rw [h2t y hy, h0t], by rw [h2top, h0top], by rw [h2v, h0v], by rw [h2p, h0p],
      by rw [h2m, h0m], by rw [h2nx, h0nx], fun y hys hnc => by rw [h2n y hys hnc, h0n], hSl, hS, hSR, hSF', hfate2, hfateJ2⟩
  have hSleaf : S.leaf = (Nn stop).leaf := by rcases hS with rfl | ⟨ti, dst, rfl⟩ <;> rfl
  cases hsl : (Nn stop).leaf with
  | true =>
    have hsl' : S.leaf = true := hSleaf.trans hsl
    simp only [hsl', ↓reduceIte, writerWP_bind]
    refine (writerWP_note_iff _ c w2 _).mpr ?_
    refine writerWP_mono (hleafStep stop w2 S hsD hbetween hLE hJw2 hsl gh.1 gh.2) ?_
    intro _ w3 h3
    refine writerWP_mono h3 ?_
    intro _ w4 h4
    simp only [writerWP_pure]
    exact h4
  | false =>
    have hsl' : S.leaf = false := hSleaf.trans hsl
    simp only [hsl', Bool.false_eq_true, ↓reduceIte]
    split
    · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
    rename_i hsm
    have hsm' : S.smallestLive = some 0 := by simpa using hsm
    by_cases hK0 : K (stop + 1) = 0
    · have hK0' : (K (stop + 1) != 0) = false := by simp [hK0]
      simp only [hK0', Bool.false_eq_true, ↓reduceIte, writerWP_bind]
      refine writerWP_mono (hlebStep seg stop w2 S hsD hbetween hLE hJw2 hsl hK0 hsm' gh.1 gh.2) ?_
      intro _ w3 h3
      try rw [hmerges]
      try simp only [↓reduceIte, writerWP_bind]
      refine writerWP_mono h3 ?_
      intro _ w4 h4
      refine writerWP_mono h4 ?_
      intro _ w5 h5
      simp only [writerWP_pure]
      exact h5
    have hK0' : (K (stop + 1) != 0) = true := by simpa using hK0
    simp only [hK0', ↓reduceIte, writerWP_bind]
    refine writerWP_mono (hinnerStep seg stop w2 S hsD hbetween hLE hJw2 hsl hK0 gh.1 gh.2) ?_
    intro _ w3 h3
    try rw [hmerges]
    try simp only [↓reduceIte, writerWP_bind]
    refine writerWP_mono h3 ?_
    intro _ w4 h4
    refine writerWP_mono h4 ?_
    intro _ w5 h5
    simp only [writerWP_pure]
    exact h5

set_option maxHeartbeats 1600000 in
/-- `takeJ2_deleteUpward_stepMBKG` with the fit at the start at any depth d, the
continuations given `CollGetInvD` at d (bergdb 025-05, step 7). -/
theorem takeJ2_deleteUpward_stepMBKGD (c : Ctx) (base : View BVal)
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
    (d : Nat) (hfit : SegFits (wNode c.p base w) c.i d w.top.rootKey)
    (hnovalAll : ∀ y yn, wNode c.p base w y = some yn → wValue base w y = none)
    (hreach : ∀ i, i ≤ depth → TReach (wNode c.p base w) c.i w.top.rootKey (X i))
    (hlinkK : ∀ i, 0 < i → i ≤ depth → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk) (hcv : cv ∉ pre)
    (hvisL : (X depth, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk)
    (huniq : ∀ key' x m, keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk → wNode c.p base w x = some m →
      m.leaf = true → key' = pre ++ [cv])
    (hmerges : c.p.merges = true)
    (hkids : ∀ c' z, (c', z) ∈ (Nn depth).liveAt c.i → wNode c.p base w z = none)
    (hJ2 : TakeJ2 c base B w) (hMF : ∀ x o, w.madeFor.lookup x = some o → o < B)
    (Q : W → Prop) (J : W → Prop) (hJ0 : J w)
    (hJnote : ∀ (s : String) (v : W), J v → J { v with trail := s :: v.trail })
    (hJtake : ∀ (x p : NodeId) (k : Nat) (v : W), J v → (∃ xn, v.nodes.lookup x = some xn) →
      (∃ pn, v.nodes.lookup p = some pn) → WriterWP (takeBack x p k) c v (fun _ v' => J v'))
    (hJunlink : ∀ (x : NodeId) (v : W), J v → (∃ xn, v.nodes.lookup x = some xn) →
      WriterWP (unlink x) c v (fun _ v' => J v'))
    (hJadk : ∀ (x : NodeId) (d k : Nat) (v : W) (n : KNode), J v → (w.path[d]?).map (·.2) = some x →
      v.nodes.lookup x = some n → DelRoom c k n → WriterWP (appendDeleteKlong x d k) c v (fun _ v' => J v'))
    (hcollM : ∀ (seg stop : Nat) (w' : W) (sn' : KNode), stop < depth →
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
      TakeJ2 c base B w' → CollGetInvD c base w' d → J w' →
      ∀ gs hs : Nat, WriterWP (mergeUp (pre ++ [cv]) gs c.p.fuel hs false) c w' (fun _ w1 =>
        WriterWP (collapseRoot (pre ++ [cv]) seg c.p.fuel) c w1 (fun _ w'' => Q w'')))
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
      TakeJ2 c base B w' → CollGetInvD c base w' d → J w' →
      ∀ gs hs : Nat, WriterWP (afterDelete (pre ++ [cv]) gs hs) c w' (fun _ w'' => Q w''))
    (hcascLeaf : ∀ (stop : Nat) (w2 : W) (S : KNode), stop < depth →
      (∀ i, stop < i → i < depth →
        (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true) →
      UpLoopEnd c B X Nn depth stop w w2 S → J w2 → (Nn stop).leaf = true →
      ¬ DelRoom c (K (stop + 1)) S → ∀ gs hs : Nat,
      WriterWP (appendDeleteKlong (X stop) stop (K (stop + 1))) c
        { w2 with trail := "up.stop-at-segment-leaf" :: w2.trail }
        (fun _ w3 => WriterWP (afterDelete (pre ++ [cv]) gs hs) c w3 (fun _ w' => Q w')))
    (hcascInner : ∀ (seg stop : Nat) (w2 : W) (S : KNode), stop < depth →
      (∀ i, stop < i → i < depth →
        (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true) →
      UpLoopEnd c B X Nn depth stop w w2 S → J w2 → (Nn stop).leaf = false → K (stop + 1) ≠ 0 →
      ¬ DelRoom c (K (stop + 1)) S → ∀ gs hs : Nat,
      WriterWP (appendDeleteKlong (X stop) stop (K (stop + 1))) c w2
        (fun _ w3 => WriterWP (mergeUp (pre ++ [cv]) gs c.p.fuel hs false) c w3 (fun _ w1 =>
          WriterWP (collapseRoot (pre ++ [cv]) seg c.p.fuel) c w1 (fun _ w' => Q w'))))
    (hlebStep : ∀ (seg stop : Nat) (w2 : W) (S : KNode), stop < depth →
      (∀ i, stop < i → i < depth →
        (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true) →
      UpLoopEnd c B X Nn depth stop w w2 S → J w2 → (Nn stop).leaf = false → K (stop + 1) = 0 →
      S.smallestLive = some 0 → ∀ gs hs : Nat,
      WriterWP (emptyKeyNext (X stop) stop) c w2
        (fun _ w3 => WriterWP (mergeUp (pre ++ [cv]) gs c.p.fuel hs false) c w3 (fun _ w1 =>
          WriterWP (collapseRoot (pre ++ [cv]) seg c.p.fuel) c w1 (fun _ w' => Q w')))) :
    WriterWP (deleteUpward (X depth) depth cv (pre ++ [cv])) c w (fun _ w' => Q w') := by
  obtain ⟨hTt, hD, hO, hS, hM, hV⟩ := hJ2
  have hN : ∀ i, i ≤ depth → wNode c.p base w (X i) = some (Nn i) := fun i hi => by
    simp only [wNode, htk i hi, Bool.false_eq_true, ↓reduceIte, hlk i hi]
  have hpost := collGetInvD_after_upT c base X Nn K depth w hlk htk hdist hT hwf hRt hTimesR hICE d hfit
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
  refine writerWP_deleteUpward_stepJG c base X Nn K depth cv pre B w Q J hJ0 hJnote hJtake hJunlink hMF hdepth
    hpos hp hk hlk htk htimes hdist hne hall hwf hreach hmerges ?_ ?_ ?_
  · intro stop w2 S hsD hbetween hLE hJw2 hsl gs hs
    by_cases hDR : DelRoom c (K (stop + 1)) S
    · have hJv := hJnote "up.stop-at-segment-leaf" w2 hJw2
      refine writerWP_mono (writerWP_and (writerWP_upStop_bitmapD c base X Nn K depth cv pre rk B w hfuel hlk htk
        htimes hdist hall hleaf hT hR hwf hreach hlinkK (fun i hi => hnovalAll _ _ (hN i hi)) hrk hcv hvisL huniq
        stop w2 S hsD hbetween hLE (Or.inl hsl) hDR ({ w2 with trail := "up.stop-at-segment-leaf" :: w2.trail } : W)
        rfl rfl rfl rfl
        (fun w' => J w' → WriterWP (afterDelete (pre ++ [cv]) gs hs) c w' (fun _ w'' => Q w'')) ?_)
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
  · intro seg stop w2 S hsD hbetween hLE hJw2 hsl hK0 gs hs
    by_cases hDR : DelRoom c (K (stop + 1)) S
    · refine writerWP_mono (writerWP_and (writerWP_upStop_bitmapD c base X Nn K depth cv pre rk B w hfuel hlk htk
        htimes hdist hall hleaf hT hR hwf hreach hlinkK (fun i hi => hnovalAll _ _ (hN i hi)) hrk hcv hvisL huniq
        stop w2 S hsD hbetween hLE (Or.inr hK0) hDR w2 rfl rfl rfl rfl
        (fun w' => J w' → WriterWP (mergeUp (pre ++ [cv]) gs c.p.fuel hs false) c w' (fun _ w1 =>
          WriterWP (collapseRoot (pre ++ [cv]) seg c.p.fuel) c w1 (fun _ w'' => Q w''))) ?_)
        (hJadk _ _ _ _ S hJw2 (hp stop (by omega)) hLE.2.2.2.2.2.2.2.1 hDR)) (fun _ w' h => h.1 h.2)
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
        exact hcollM seg stop w' sn' hsD hbetween ht htop hv hnodes hsn' hsl' hsw' hst' hlive' hread hfate hfJ
          hst0 hJ hI hJw' gs hs
    · exact hcascInner seg stop w2 S hsD hbetween hLE hJw2 hsl hK0 hDR gs hs
  · exact hlebStep

theorem takeJ2_deleteUpward_stepMBKG (c : Ctx) (base : View BVal)
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
    (hmerges : c.p.merges = true)
    (hkids : ∀ c' z, (c', z) ∈ (Nn depth).liveAt c.i → wNode c.p base w z = none)
    (hJ2 : TakeJ2 c base B w) (hMF : ∀ x o, w.madeFor.lookup x = some o → o < B)
    (Q : W → Prop) (J : W → Prop) (hJ0 : J w)
    (hJnote : ∀ (s : String) (v : W), J v → J { v with trail := s :: v.trail })
    (hJtake : ∀ (x p : NodeId) (k : Nat) (v : W), J v → (∃ xn, v.nodes.lookup x = some xn) →
      (∃ pn, v.nodes.lookup p = some pn) → WriterWP (takeBack x p k) c v (fun _ v' => J v'))
    (hJunlink : ∀ (x : NodeId) (v : W), J v → (∃ xn, v.nodes.lookup x = some xn) →
      WriterWP (unlink x) c v (fun _ v' => J v'))
    (hJadk : ∀ (x : NodeId) (d k : Nat) (v : W) (n : KNode), J v → (w.path[d]?).map (·.2) = some x →
      v.nodes.lookup x = some n → DelRoom c k n → WriterWP (appendDeleteKlong x d k) c v (fun _ v' => J v'))
    (hcollM : ∀ (seg stop : Nat) (w' : W) (sn' : KNode), stop < depth →
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
      ∀ gs hs : Nat, WriterWP (mergeUp (pre ++ [cv]) gs c.p.fuel hs false) c w' (fun _ w1 =>
        WriterWP (collapseRoot (pre ++ [cv]) seg c.p.fuel) c w1 (fun _ w'' => Q w'')))
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
      ∀ gs hs : Nat, WriterWP (afterDelete (pre ++ [cv]) gs hs) c w' (fun _ w'' => Q w''))
    (hcascLeaf : ∀ (stop : Nat) (w2 : W) (S : KNode), stop < depth →
      (∀ i, stop < i → i < depth →
        (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true) →
      UpLoopEnd c B X Nn depth stop w w2 S → J w2 → (Nn stop).leaf = true →
      ¬ DelRoom c (K (stop + 1)) S → ∀ gs hs : Nat,
      WriterWP (appendDeleteKlong (X stop) stop (K (stop + 1))) c
        { w2 with trail := "up.stop-at-segment-leaf" :: w2.trail }
        (fun _ w3 => WriterWP (afterDelete (pre ++ [cv]) gs hs) c w3 (fun _ w' => Q w')))
    (hcascInner : ∀ (seg stop : Nat) (w2 : W) (S : KNode), stop < depth →
      (∀ i, stop < i → i < depth →
        (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true) →
      UpLoopEnd c B X Nn depth stop w w2 S → J w2 → (Nn stop).leaf = false → K (stop + 1) ≠ 0 →
      ¬ DelRoom c (K (stop + 1)) S → ∀ gs hs : Nat,
      WriterWP (appendDeleteKlong (X stop) stop (K (stop + 1))) c w2
        (fun _ w3 => WriterWP (mergeUp (pre ++ [cv]) gs c.p.fuel hs false) c w3 (fun _ w1 =>
          WriterWP (collapseRoot (pre ++ [cv]) seg c.p.fuel) c w1 (fun _ w' => Q w'))))
    (hlebStep : ∀ (seg stop : Nat) (w2 : W) (S : KNode), stop < depth →
      (∀ i, stop < i → i < depth →
        (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true) →
      UpLoopEnd c B X Nn depth stop w w2 S → J w2 → (Nn stop).leaf = false → K (stop + 1) = 0 →
      S.smallestLive = some 0 → ∀ gs hs : Nat,
      WriterWP (emptyKeyNext (X stop) stop) c w2
        (fun _ w3 => WriterWP (mergeUp (pre ++ [cv]) gs c.p.fuel hs false) c w3 (fun _ w1 =>
          WriterWP (collapseRoot (pre ++ [cv]) seg c.p.fuel) c w1 (fun _ w' => Q w')))) :
    WriterWP (deleteUpward (X depth) depth cv (pre ++ [cv])) c w (fun _ w' => Q w') :=
  takeJ2_deleteUpward_stepMBKGD c base X Nn K depth cv pre rk B w hdepth hfuel hpos hp hk hlk htk htimes hdist hne hall
    hleaf hT hR hwf hRt hTimesR hICE (c.p.fuel - 1) hfit hnovalAll hreach hlinkK hrk hcv hvisL huniq hmerges
    hkids hJ2 hMF Q J hJ0 hJnote hJtake hJunlink hJadk
    (fun seg stop w' sn' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 hJ' hI hJw =>
      hcollM seg stop w' sn' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 hJ' (collGetInv_of_D c base w' hI) hJw)
    (fun stop w' sn' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 hJ' hI hJw =>
      hleafM stop w' sn' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 hJ' (collGetInv_of_D c base w' hI) hJw)
    hcascLeaf hcascInner hlebStep

set_option linter.unusedSimpArgs false in
/-- The stop node's bitmap with room, the node cached, keeps the heights'
cache. -/
theorem writerWP_appendDeleteKlong_room_gh (x : NodeId) (depth cv : Nat) (n : KNode) (c : Ctx) (w : W)
    (hlk : w.nodes.lookup x = some n) (hD : DelRoom c cv n) :
    WriterWP (appendDeleteKlong x depth cv) c w (fun _ w' => w'.gh = w.gh) := by
  have hR : ¬ ((∃ old, n.ks.getLast? = some (.del old)) ∧ n.lastTime = some c.i) →
      n.size + 1 < c.p.M ∧
      deadOver c.p (n.add c.i (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))) = false := by
    intro hn
    rcases hD with ⟨h1, h2, _⟩ | ⟨_, h3, h4⟩
    · exact absurd ⟨h1, h2⟩ hn
    · exact ⟨h3, h4⟩
  unfold appendDeleteKlong
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlk]
  split
  · exact writerWP_throw _ _ _ _
  · by_cases hne : bitsUnion n.lastBitmap (n.bitsOf cv) = n.lastBitmap
    · have hyes : (bitsUnion n.lastBitmap (n.bitsOf cv) == n.lastBitmap) = true := by simp [hne]
      simp only [hyes, Bool.not_true, Bool.false_eq_true, ↓reduceIte, writerWP_pure]
    · have hno : (bitsUnion n.lastBitmap (n.bitsOf cv) == n.lastBitmap) = false := by
        simpa using hne
      cases hgl : n.ks.getLast? with
      | none =>
        obtain ⟨hroom0, hdead2⟩ := hR (fun ⟨⟨old, h⟩, _⟩ => by rw [hgl] at h; cases h)
        have hroom' : decide (n.size + 1 < c.p.M) = true := by simpa using hroom0
        simp only [hno, hroom', hroom0, hdead2, Bool.not_false, Bool.false_and, Bool.false_eq_true,
          ↓reduceIte, note, putNode, writerWP_bind, writerWP_modify, writerWP_pure, hgl]
      | some k =>
        cases k with
        | del old =>
          cases hlt : (n.lastTime == some c.i)
          · obtain ⟨hroom0, hdead2⟩ := hR (fun ⟨_, h⟩ => by rw [h] at hlt; simp at hlt)
            have hroom' : decide (n.size + 1 < c.p.M) = true := by simpa using hroom0
            simp only [hno, hroom', hroom0, hdead2, hgl, hlt, Bool.not_false, Bool.true_and, Bool.and_false,
              Bool.false_eq_true, ↓reduceIte, note, putNode, writerWP_bind, writerWP_modify,
              writerWP_pure]
          · have hdead1 : deadOver c.p (n.setAt (n.size - 1)
                (.del (bitsUnion n.lastBitmap (n.bitsOf cv)))) = false := by
              rcases hD with ⟨_, _, h⟩ | ⟨hn, _, _⟩
              · exact h
              · exact absurd ⟨⟨old, hgl⟩, by simpa using hlt⟩ hn
            simp only [hno, hdead1, hgl, hlt, Bool.not_false, Bool.true_and, Bool.and_true,
              Bool.false_eq_true, ↓reduceIte, note, putNode, writerWP_bind, writerWP_modify,
              writerWP_pure]
        | _ =>
          obtain ⟨hroom0, hdead2⟩ := hR (fun ⟨⟨old, h⟩, _⟩ => by rw [hgl] at h; cases h)
          have hroom' : decide (n.size + 1 < c.p.M) = true := by simpa using hroom0
          simp only [hno, hroom', hroom0, hdead2, hgl, Bool.not_false, Bool.false_and, Bool.false_eq_true,
            ↓reduceIte, note, putNode, writerWP_bind, writerWP_modify, writerWP_pure]

/-- Obligation (the stop node's bitmap into a full node keeps `DelInv`, the
merges on, with the fill at the delete's start, the heights' invariant at the
descent's end and the loop keeping the heights' cache). -/
def UpCascOKHG (c : Ctx) (base : View BVal) (KO : KindOracle) (BK : NodeId) (H : NodeId → Nat → Prop) : Prop :=
  ∀ (w w3 : W) (B MB : NodeId) (top0 : Top) (pre : List Nat) (cv : Nat) (rk : NodeId)
    (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth stop : Nat) (w2 v : W) (S : KNode),
    c.p.merges = true → LiveCounts c.p (wNode c.p base w) c.i w.top.rootKey →
    KdHtJ c B top0 KO BK H w3 → w3.path.length = depth + 1 → w2.gh = w3.gh →
    2 ≤ c.p.splitAbove → ViewIdsBelow BK c.view → ViewKinds KO BK c → ICEFromKinds c base KO BK →
    X 0 = w.top.rootKey → PutBase c base B → PutInv c base w → RangeOrder (wNode c.p base w) c.i w.top.rootKey →
    SegFits (wNode c.p base w) c.i (c.p.fuel - 1) w.top.rootKey →
    InnerChildrenExist (wNode c.p base w) c.i w.top.rootKey → ReadsAs c.p base w w3 →
    keyWf (pre ++ [cv]) = true →
    segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk →
    (X depth, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
    (∀ i, i ≤ depth → (w3.path[i]?).map (·.2) = some (X i)) →
    (∀ i, 0 < i → i ≤ depth → w3.path[i]? = some (some (K i), X i)) →
    (∀ i, i ≤ depth → w3.nodes.lookup (X i) = some (Nn i)) →
    (∀ i, i ≤ depth → wNode c.p base w (X i) = some (Nn i)) →
    (∀ i, 0 < i → i ≤ depth → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i) →
    bitsUnion (Nn depth).lastBitmap ((Nn depth).bitsOf cv) ≠ (Nn depth).lastBitmap →
    (Nn depth).allKeysIn (bitsUnion (Nn depth).lastBitmap ((Nn depth).bitsOf cv)) = true →
    (Nn depth).leaf = true → 0 < depth → stop < depth →
    (∀ i, stop < i → i < depth →
      (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true) →
    UpLoopEnd c MB X Nn depth stop w3 w2 S →
    (v = w2 ∨ ∃ s, v = { w2 with trail := s :: w2.trail }) → KdJP c B top0 KO BK w3.path v →
    ((Nn stop).leaf = true ∨ K (stop + 1) ≠ 0) → ¬ DelRoom c (K (stop + 1)) S →
    WriterWP (appendDeleteKlong (X stop) stop (K (stop + 1))) c v
      (fun _ w' => DelInv c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK w')

/-- Obligation (the take-back's side of `UpCascOKHG`: the stop node's bitmap
into a full node keeps the take-back's invariant, with the fill at the delete's
start, the heights' invariant at the descent's end and the loop keeping the
heights' cache). -/
def UpCascJ2OKHG (c : Ctx) (base : View BVal) (KO : KindOracle) (BK B : NodeId) (H : NodeId → Nat → Prop) :
    Prop :=
  ∀ (w w3 : W) (top0 : Top) (pre : List Nat) (cv : Nat) (rk : NodeId)
    (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth stop : Nat) (w2 v : W) (S : KNode),
    c.p.merges = true → LiveCounts c.p (wNode c.p base w) c.i w.top.rootKey →
    KdHtJ c B top0 KO BK H w3 → w3.path.length = depth + 1 → w2.gh = w3.gh →
    2 ≤ c.p.splitAbove → ViewIdsBelow BK c.view → ViewKinds KO BK c → ICEFromKinds c base KO BK →
    X 0 = w.top.rootKey → 0 < c.i → PutBase c base B → PutInv c base w → RangeOrder (wNode c.p base w) c.i w.top.rootKey →
    SegFits (wNode c.p base w) c.i (c.p.fuel - 1) w.top.rootKey →
    InnerChildrenExist (wNode c.p base w) c.i w.top.rootKey → ReadsAs c.p base w w3 →
    keyWf (pre ++ [cv]) = true →
    segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk →
    (X depth, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
    (∀ i, i ≤ depth → (w3.path[i]?).map (·.2) = some (X i)) →
    (∀ i, 0 < i → i ≤ depth → w3.path[i]? = some (some (K i), X i)) →
    (∀ i, i ≤ depth → w3.nodes.lookup (X i) = some (Nn i)) →
    (∀ i, i ≤ depth → wNode c.p base w (X i) = some (Nn i)) →
    (∀ i, 0 < i → i ≤ depth → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i) →
    bitsUnion (Nn depth).lastBitmap ((Nn depth).bitsOf cv) ≠ (Nn depth).lastBitmap →
    (Nn depth).allKeysIn (bitsUnion (Nn depth).lastBitmap ((Nn depth).bitsOf cv)) = true →
    (Nn depth).leaf = true → 0 < depth → stop < depth →
    (∀ i, stop < i → i < depth →
      (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true) →
    UpLoopEnd c B X Nn depth stop w3 w2 S →
    (v = w2 ∨ ∃ s, v = { w2 with trail := s :: w2.trail }) → KdJP c B top0 KO BK w3.path v →
    ((Nn stop).leaf = true ∨ K (stop + 1) ≠ 0) → ¬ DelRoom c (K (stop + 1)) S →
    TakeJ2 c base B w → (∀ x o, w3.madeFor.lookup x = some o → o < B) →
    (∀ c' z, (c', z) ∈ (Nn depth).liveAt c.i → wNode c.p base w z = none) →
    WriterWP (appendDeleteKlong (X stop) stop (K (stop + 1))) c v
      (fun _ w' => DelInvJ c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK B w')

/-- `UpCascOKHG` from `UpHolderLiveRunOK` and cost's `UpCascFitsOKR`, without `hU`
(025-04, route (b): the stop node's split from the state with its bitmap). -/
theorem upCascOKHG_of_noU (c : Ctx) (base : View BVal) (KO : KindOracle) (BK : NodeId) (H : NodeId → Nat → Prop)
    (hHL : UpHolderLiveRunOK c base)
    (hFitR : UpCascFitsOKR c base KO BK H) : UpCascOKHG c base KO BK H := by
  intro w w3 B MB top0 pre cv rk X Nn K depth stop w2 v S hm hLC hJ3H hlen hgh hsa2 hvB hk hICEk hX0 hB hI hRO hF hICE hr03 hkey
    hrk hvis hpX hpK hlkX hXN hlinkK hne hall hleaf hdepth hsD hbetween hLE hv hJ hkind hfull
  obtain ⟨hlinks2, hwf2⟩ := linksWf_of_book c base B top0 v w2 hB hJ.1.1 hv
  have hFits := hFitR w w3 B MB top0 pre cv rk X Nn K depth stop w2 v S hm hLC hJ3H hlen
    hgh
    (upHolderOK_of_live c base KO BK B top0 H w3 MB X Nn depth stop w2 v S hB hJ3H hlkX hLE hv hJ.1.1
      (hHL w w3 MB X Nn K depth stop w2 S hI hr03 hlkX hlinkK hsD hLE)) hsa2 hvB hk hICEk hX0 hB hI hRO hF
    hICE hr03 hkey hrk hvis hpX hpK hlkX hXN hlinkK hne hall hleaf hdepth hsD hbetween hLE hv hJ hkind hfull
  rcases Nat.eq_zero_or_pos stop with hs | hs
  · subst hs
    exact writerWP_upCasc_root_del c base hB.coherent hsa2 KO BK hvB hk hICEk w w3 B MB top0 pre cv rk
      X Nn K depth w2 v S hB hI hRO hF hr03 hkey hrk hvis hpX hlkX hXN hlinkK hall hleaf hdepth hbetween
      hX0 hLE hv hJ hkind hfull hlinks2 hwf2 hFits
  · obtain ⟨D, rfl⟩ : ∃ D, stop = D + 1 := ⟨stop - 1, by omega⟩
    have hcu : CacheUnique v := cacheUnique_of_book hJ.1.1.book
    exact writerWP_upCasc_below_delS c base hsa2 KO BK hvB hk hICEk w w3 B MB top0 pre cv rk X Nn K depth D
      w2 v S hB hI hRO hF hr03 hkey hrk hvis hpX hpK hlkX hXN hlinkK hall hleaf hsD hbetween hX0 hLE hv hJ
      hfull hcu hlinks2 hwf2 hFits

set_option linter.unusedVariables false in
/-- `UpCascOKHG` from `UpUnlinkTreeOK`, `UpHolderLiveRunOK` and cost's `UpCascFitsOKR`. -/
theorem upCascOKHG_of (c : Ctx) (base : View BVal) (KO : KindOracle) (BK : NodeId) (H : NodeId → Nat → Prop)
    (hU : UpUnlinkTreeOK c base) (hHL : UpHolderLiveRunOK c base)
    (hFitR : UpCascFitsOKR c base KO BK H) : UpCascOKHG c base KO BK H :=
  upCascOKHG_of_noU c base KO BK H hHL hFitR

/-- `UpCascJ2OKHG` likewise, without `hU`. -/
theorem upCascJ2OKHG_of_noU (c : Ctx) (base : View BVal) (KO : KindOracle) (BK B : NodeId) (H : NodeId → Nat → Prop)
    (hHL : UpHolderLiveRunOK c base)
    (hFitR : UpCascFitsOKR c base KO BK H) : UpCascJ2OKHG c base KO BK B H := by
  intro w w3 top0 pre cv rk X Nn K depth stop w2 v S hm hLC hJ3H hlen hgh hsa2 hvB hk hICEk hX0 hpos hB hI hRO hF hICE hr03
    hkey hrk hvis hpX hpK hlkX hXN hlinkK hne hall hleaf hdepth hsD hbetween hLE hv hJ hkind hfull hJw
    _hMF hkidsw
  have hRead := upCascOKHG_of_noU c base KO BK H hHL hFitR
    w w3 B B top0 pre cv rk X Nn K depth stop w2 v S hm hLC hJ3H hlen hgh hsa2 hvB hk hICEk hX0 hB hI hRO hF hICE hr03 hkey
    hrk hvis hpX hpK hlkX hXN hlinkK hne hall hleaf hdepth hsD hbetween hLE hv hJ hkind hfull
  have hBn : B ≤ w.next := by
    have h1 : B ≤ v.next := hJ.1.1.fresh.1
    have h2 : v.next = w2.next := by
      rcases hv with rfl | ⟨s, rfl⟩ <;> rfl
    rw [h2, hLE.2.2.2.2.2.1, hr03.2.2.2.2] at h1
    exact h1
  have hcu : CacheUnique v := cacheUnique_of_book hJ.1.1.book
  obtain ⟨hlinks2, hwf2⟩ := linksWf_of_book c base B top0 v w2 hB hJ.1.1 hv
  have hJ2 : WriterWP (appendDeleteKlong (X stop) stop (K (stop + 1))) c v
      (fun _ w' => TakeJ2 c base B w' ∧ B ≤ w'.next) := by
    rcases Nat.eq_zero_or_pos stop with hs | hs
    · subst hs
      exact writerWP_upCasc_root_j2S c base hB.coherent hsa2 B hpos w w3 X Nn K depth w2 v S hI hr03 hJw
        hBn hkidsw hlkX hXN hlinkK hdepth hbetween hX0 hLE hv hfull hcu hlinks2 hwf2
    · obtain ⟨D, rfl⟩ : ∃ D, stop = D + 1 := ⟨stop - 1, by omega⟩
      exact writerWP_upCasc_below_j2S c base hsa2 B hpos w w3 X Nn K depth D w2 v S hI hRO hr03 hJw hBn
        hkidsw hpX hpK hlkX hXN hlinkK hsD hbetween hX0 hLE hv hJ.2 hfull hcu hlinks2 hwf2
  exact writerWP_mono (writerWP_and hRead hJ2) (fun _ w' h => ⟨h.1, h.2.1, h.2.2⟩)

set_option linter.unusedVariables false in
/-- `UpCascJ2OKHG` likewise. -/
theorem upCascJ2OKHG_of (c : Ctx) (base : View BVal) (KO : KindOracle) (BK B : NodeId) (H : NodeId → Nat → Prop)
    (hU : UpUnlinkTreeOK c base) (hHL : UpHolderLiveRunOK c base)
    (hFitR : UpCascFitsOKR c base KO BK H) : UpCascJ2OKHG c base KO BK B H :=
  upCascJ2OKHG_of_noU c base KO BK B H hHL hFitR

set_option maxHeartbeats 3200000 in
/-- The delete whose leaf, not the space root, empties, the merges on, whatever
room the stop node has: `writerWP_del_emptyRoomMK` on the walk cut at the stop
node's step (`writerWP_deleteUpward_stepJ`), the bitmap with the room of the
branch the writer takes proved, the cascade and LE-b from `UpCascOK` and
`UpLebOK`. -/
theorem writerWP_del_emptyAnyMKLHG (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (hbook : PutBook c B top0 w)
    (KO : KindOracle) (BK : NodeId) (hvB : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c)
    (hb0 : Book BK c w) (hi0 : KdInv KO BK w)
    (hI : PutInv c base w) (hRO : RangeOrder (wNode c.p base w) c.i w.top.rootKey)
    (hF : SegFits (wNode c.p base w) c.i (c.p.fuel - 1) w.top.rootKey)
    (hICE : InnerChildrenExist (wNode c.p base w) c.i w.top.rootKey)
    (hkey : keyWf (pre ++ [cv]) = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hleafC : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
      n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = true ∧ L ≠ w.top.rootKey)
    (H : NodeId → Nat → Prop) (hC : UpCascOKHG c base KO BK H)
    (hLC : LiveCounts c.p (wNode c.p base w) c.i w.top.rootKey)
    (hvo : ViewHtOK H BK c) (hkw : ViewKlongsWf c.p c.view) (hhi : HtInv H BK c w) (hwfw : WriterKlongsWf w)
    (hub : UntakenBound (c.p.fuel - 1) w)
    (hsa2 : 2 ≤ c.p.splitAbove) (hICEk : ICEFromKinds c base KO BK)
    (hm : c.p.merges = true) (hpos : 0 < c.i)
    (hA : ∀ g h v, DelInv c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK v →
      WriterWP (afterDelete (pre ++ [cv]) g h) c v (fun _ v' => DelInv c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK v'))
    (hMU : ∀ g h merged v, DelInv c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK v →
      WriterWP (mergeUp (pre ++ [cv]) g c.p.fuel h merged) c v
        (fun _ v' => DelInv c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK v'))
    (hCR : ∀ seg v, DelInv c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK v →
      WriterWP (collapseRoot (pre ++ [cv]) seg c.p.fuel) c v
        (fun _ v' => DelInv c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK v'))
    (Post : W → Prop) (hfresh : ∀ v, Post v → WriterWP fresh c v (fun _ v' => Post v'))
    (hpost : ∀ v, DelInv c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK v → Post v) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' => Post w') := by
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hJ0 : KdJ c B top0 KO BK w := ⟨hbook, hb0, hi0⟩
  refine writerWP_del_toLeafMKH c base hvc pre cv rk w (KdHtJ c B top0 KO BK H)
    (fun s f x v hJ hx => kdhtJ_descendLte base top0 hB KO BK hvB hk hvo hkw s f x v hJ hx)
    (fun s fd L n v hJ hL hlk hleaf hfd => kdhtJ_pathAdd base top0 hB KO BK hvB hvo s fd L n v hJ hL hlk hleaf hfd)
    (kdhtJ_start base top0 hB KO BK hvB hvo w hJ0 hhi hwfw hub) hrk (hI.pathUntaken _) hI.wf Post hfresh ?_
  intro L n P w3 hL hn hnl hr03 hb3H hlk3 hp3' hlinkP hXD hlkX
  have hb3 := hb3H.1
  have hlen3 : w3.path.length = P.length + 1 := by rw [hp3']; simp
  obtain ⟨hne, hall, hLr⟩ := hleafC L n hL hn hnl
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
  have hLeq : nodeAt w.top.rootKey P P.length = L := hXD
  have hXNw : ∀ i, i ≤ P.length → wNode c.p base w (nodeAt w.top.rootKey P i) =
      some ((wNode c.p base w (nodeAt w.top.rootKey P i)).getD n) := hXN
  have hrk3 : segRootR (wNode c.p base w3) c.i c.p.fuel pre w3.top.rootKey = some rk := by
    rw [hr03.1, hr03.2.1]; exact hrk
  have hvis3 : (nodeAt w.top.rootKey P P.length, cv) ∈ eqVisits (wNode c.p base w3) c.i cv c.p.fuel rk := by
    rw [hr03.1, hLeq]; exact hL
  have huniq3 := hI.keyUniq pre cv rk hkey hrk
  rw [← hr03.1, ← hr03.2.1] at huniq3
  have hvisw : (nodeAt w.top.rootKey P P.length, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk := by
    rw [hLeq]; exact hL
  have hne' := hne
  have hall' := hall
  rw [← hNnD] at hne' hall'
  have hnl' : ((wNode c.p base w (nodeAt w.top.rootKey P P.length)).getD n).leaf = true := by
    rw [hNnD]; exact hnl
  refine writerWP_deleteUpward_stepJG c base (fun i => nodeAt w.top.rootKey P i)
    (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
    (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length cv pre (madeForBound w3) w3 Post
    (fun v => KdJP c B top0 KO BK w3.path v ∧ v.gh = w3.gh) ⟨⟨hb3, rfl⟩, rfl⟩
    (fun s v hJ => ⟨kdJP_note c base B top0 hB KO BK hvB hk _ s v hJ.1, hJ.2⟩)
    (fun x q k v hJ hx hq => writerWP_mono (writerWP_and
      (kdJP_takeBack c base B top0 hB KO BK hvB hk _ x q k v hJ.1 hx) (writerWP_takeBack_gh x q k c v hq))
      (fun _ v' h => ⟨h.1, h.2.trans hJ.2⟩))
    (fun x v hJ hx => writerWP_mono (writerWP_and
      (kdJP_unlink c base B top0 hB KO BK hvB hk _ x v hJ.1) (writerWP_unlink_gh x c v hx))
      (fun _ v' h => ⟨h.1, h.2.trans hJ.2⟩))
    (madeFor_lt_bound w3) hdepth hpos hpX hpK hlkX htk3 (fun i hi => hTimesR3 _ _ (hreach3 i hi) (hN3 i hi))
    hdistP hne' hall' hwf3 hreach3 hm ?_ ?_ ?_
  · -- a segment leaf as the stop node
    intro stop w2 S hsD hbetween hLE hJ2G hsl gs hs
    obtain ⟨hJ2, hgh2⟩ := hJ2G
    have hJv := kdJP_note c base B top0 hB KO BK hvB hk _ "up.stop-at-segment-leaf" w2 hJ2
    by_cases hDR : DelRoom c (((P[stop + 1 - 1]?).bind (·.1)).getD 0) S
    · refine writerWP_mono (writerWP_and (writerWP_upStop_bitmapD c base (fun i => nodeAt w.top.rootKey P i)
        (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
        (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length cv pre rk (madeForBound w3) w3 hfuel hlkX htk3
        (fun i hi => hTimesR3 _ _ (hreach3 i hi) (hN3 i hi)) hdistP hall' hnl' hT3 hR3 hwf3 hreach3 hlinkK
        (fun i hi => hnovalAll3 _ _ (hN3 i hi)) hrk3 (keyWf_last_notin pre cv hkey) hvis3 huniq3
        stop w2 S hsD hbetween hLE (Or.inl hsl) hDR ({ w2 with trail := "up.stop-at-segment-leaf" :: w2.trail } : W)
        rfl rfl rfl rfl
        (fun w' => PutBook c B top0 w' → DelInvF c base w (pre ++ [cv]) (c.p.fuel + 1) w') ?_)
        (kdJP_appendDeleteKlong c base B top0 hB KO BK hvB hk _ _ stop _ _ hJv (hpX stop (by omega)))) ?_
      · intro w' sn' ht htop hv hnodes hsn' hsl' hsw' hst' hlive' hread _ _ _ hbk'
        obtain ⟨hagree, hsnw⟩ := hfr stop w' sn' hsD ht hnodes hsn'
        have hRO' : RangeOrder (wNode c.p base w') c.i w'.top.rootKey := by
          rw [htop]
          exact rangeOrder_up_bitmap (wNode c.p base w3) (wNode c.p base w') c.i w3.top.rootKey _ _ _ stop
            P.length hsD hR3 hT3 (hreach3 stop (by omega)) (fun i _ h2 => hN3 i h2)
            (fun i h1 h2 => hlinkK i (by omega) h2) (fun i i' _ h2 _ h4 he => hdistP i i' h2 h4 he)
            hagree sn' hsnw hsl' (fun c' z h => (hlive' c' z).mp h)
        exact hD stop w' sn' id hsD ht htop hv hnodes hsn' hsl' hsw' hst'
          (fun c' z h => ⟨c', ((hlive' c' z).mp h).1, ((hlive' c' z).mp h).2, rfl⟩) hRO' hbk' hread
      · rintro _ w' ⟨hDv, hJ'⟩
        exact writerWP_mono (hA gs hs w' ⟨hDv hJ'.1.1, hJ'.1.2.1, hJ'.1.2.2⟩) (fun _ w2 hD2 => hpost w2 hD2)
    · exact writerWP_mono (hC w w3 B (madeForBound w3) top0 pre cv rk (fun i => nodeAt w.top.rootKey P i)
        (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
        (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length stop w2 _ S hm hLC hb3H hlen3 hgh2 hsa2 hvB hk hICEk (by simp [nodeAt])
        hB hI hRO hF hICE hr03 hkey hrk
        hvisw hpX hpK hlkX hXNw hlinkK hne' hall' hnl' hdepth hsD hbetween hLE (Or.inr ⟨_, rfl⟩) hJv
        (Or.inl hsl) hDR)
        (fun _ w' hD' => writerWP_mono (hA gs hs w' hD') (fun _ w2 hD2 => hpost w2 hD2))
  · -- an inner stop node, its klong to the chain not the empty key's
    intro seg stop w2 S hsD hbetween hLE hJ2G hsl hK0 gs hs
    obtain ⟨hJ2, hgh2⟩ := hJ2G
    by_cases hDR : DelRoom c (((P[stop + 1 - 1]?).bind (·.1)).getD 0) S
    · refine writerWP_mono (writerWP_and (writerWP_upStop_bitmapD c base (fun i => nodeAt w.top.rootKey P i)
        (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
        (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length cv pre rk (madeForBound w3) w3 hfuel hlkX htk3
        (fun i hi => hTimesR3 _ _ (hreach3 i hi) (hN3 i hi)) hdistP hall' hnl' hT3 hR3 hwf3 hreach3 hlinkK
        (fun i hi => hnovalAll3 _ _ (hN3 i hi)) hrk3 (keyWf_last_notin pre cv hkey) hvis3 huniq3
        stop w2 S hsD hbetween hLE (Or.inr hK0) hDR _ rfl rfl rfl rfl
        (fun w' => PutBook c B top0 w' → DelInvF c base w (pre ++ [cv]) (c.p.fuel + 1) w') ?_)
        (kdJP_appendDeleteKlong c base B top0 hB KO BK hvB hk _ _ stop _ _ hJ2 (hpX stop (by omega)))) ?_
      · intro w' sn' ht htop hv hnodes hsn' hsl' hsw' hst' hlive' hread _ _ _ hbk'
        obtain ⟨hagree, hsnw⟩ := hfr stop w' sn' hsD ht hnodes hsn'
        have hRO' : RangeOrder (wNode c.p base w') c.i w'.top.rootKey := by
          rw [htop]
          exact rangeOrder_up_bitmap (wNode c.p base w3) (wNode c.p base w') c.i w3.top.rootKey _ _ _ stop
            P.length hsD hR3 hT3 (hreach3 stop (by omega)) (fun i _ h2 => hN3 i h2)
            (fun i h1 h2 => hlinkK i (by omega) h2) (fun i i' _ h2 _ h4 he => hdistP i i' h2 h4 he)
            hagree sn' hsnw hsl' (fun c' z h => (hlive' c' z).mp h)
        exact hD stop w' sn' id hsD ht htop hv hnodes hsn' hsl' hsw' hst'
          (fun c' z h => ⟨c', ((hlive' c' z).mp h).1, ((hlive' c' z).mp h).2, rfl⟩) hRO' hbk' hread
      · rintro _ w' ⟨hDv, hJ'⟩
        refine writerWP_mono (hMU gs hs false w' ⟨hDv hJ'.1.1, hJ'.1.2.1, hJ'.1.2.2⟩) ?_
        intro _ w1 hD1
        exact writerWP_mono (hCR seg w1 hD1) (fun _ w2 hD2 => hpost w2 hD2)
    · refine writerWP_mono (hC w w3 B (madeForBound w3) top0 pre cv rk (fun i => nodeAt w.top.rootKey P i)
        (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
        (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length stop w2 _ S hm hLC hb3H hlen3 hgh2 hsa2 hvB hk hICEk (by simp [nodeAt])
        hB hI hRO hF hICE hr03 hkey hrk
        hvisw hpX hpK hlkX hXNw hlinkK hne' hall' hnl' hdepth hsD hbetween hLE (Or.inl rfl) hJ2
        (Or.inr hK0) hDR) ?_
      intro _ w' hD'
      refine writerWP_mono (hMU gs hs false w' hD') ?_
      intro _ w1 hD1
      exact writerWP_mono (hCR seg w1 hD1) (fun _ w2 hD2 => hpost w2 hD2)
  · -- LE-b at an inner stop node: none, with the fill at the delete's start
    intro seg stop w2 S hsD hbetween hLE hJ2 hsl hK0 hsm gs hs
    exact (lebStop_false c base w hLC hm hI (fun i => nodeAt w.top.rootKey P i)
      (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
      (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length stop cv (by simp [nodeAt]) hXNw hlinkK hall'
      hsD hbetween hsl).elim

set_option maxHeartbeats 3200000 in
/-- `writerWP_del_emptyRoomMJK` whatever room the stop node has: the walk cut at
the stop node's step and the cascade from `UpCascJ2OKHG`, with the loop keeping
the heights' cache and the live counts at the delete's start (`hLC`). -/
theorem writerWP_del_emptyAnyMJKLHGG (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (hbook : PutBook c B top0 w)
    (KO : KindOracle) (BK : NodeId) (hvB : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c)
    (hb0 : Book BK c w) (hi0 : KdInv KO BK w)
    (hI : PutInv c base w) (hRO : RangeOrder (wNode c.p base w) c.i w.top.rootKey)
    (hF : SegFits (wNode c.p base w) c.i (c.p.fuel - 1) w.top.rootKey)
    (hICE : InnerChildrenExist (wNode c.p base w) c.i w.top.rootKey)
    (hkey : keyWf (pre ++ [cv]) = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hleafC : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
      n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = true ∧ L ≠ w.top.rootKey)
    (H : NodeId → Nat → Prop) (hC : UpCascJ2OKHG c base KO BK B H)
    (hLC : LiveCounts c.p (wNode c.p base w) c.i w.top.rootKey)
    (hvo : ViewHtOK H BK c) (hkw : ViewKlongsWf c.p c.view) (hhi : HtInv H BK c w) (hwfw : WriterKlongsWf w)
    (hub : UntakenBound (c.p.fuel - 1) w)
    (hsa2 : 2 ≤ c.p.splitAbove) (hICEk : ICEFromKinds c base KO BK)
    (hm : c.p.merges = true) (hpos : 0 < c.i)
    (hJ2 : TakeJ2 c base B w) (hMF : ∀ x o, w.madeFor.lookup x = some o → o < B)
    (hLV : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true → ∀ y, (cv, y) ∈ n.liveAt c.i →
      wNode c.p base w y = none)
    (Imid : W → Prop)
    (hA : ∀ g h v, DelInvJ c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK B v →
      WriterWP (afterDelete (pre ++ [cv]) g h) c v (fun _ v' => TakeJ2 c base B v'))
    (hMU : ∀ g h merged v, DelInvJ c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK B v →
      WriterWP (mergeUp (pre ++ [cv]) g c.p.fuel h merged) c v (fun _ v' => Imid v'))
    (hCR : ∀ seg v, Imid v →
      WriterWP (collapseRoot (pre ++ [cv]) seg c.p.fuel) c v (fun _ v' => TakeJ2 c base B v')) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' => TakeJ2 c base B w') := by
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  refine writerWP_del_toLeafMKH c base hvc pre cv rk w
    (fun v => KdHtJ c B top0 KO BK H v ∧ v.madeFor = w.madeFor)
    (fun s f x v hJ hx => writerWP_mono (writerWP_and
      (kdhtJ_descendLte base top0 hB KO BK hvB hk hvo hkw s f x v hJ.1 hx)
      (writerWP_descendLte_madeFor s c f x v)) (fun _ v' h => ⟨h.1, h.2.trans hJ.2⟩))
    (fun s fd L n v hJ hL hlk hleaf hfd =>
      ⟨kdhtJ_pathAdd base top0 hB KO BK hvB hvo s fd L n v hJ.1 hL hlk hleaf hfd, hJ.2⟩)
    ⟨kdhtJ_start base top0 hB KO BK hvB hvo w ⟨hbook, hb0, hi0⟩ hhi hwfw hub, rfl⟩ hrk (hI.pathUntaken _) hI.wf
    (TakeJ2 c base B) (fun v hv => by unfold fresh; wpSimplify; exact hv) ?_
  intro L n P w3 hL hn hnl hr03 hJ3 hlk3 hp3' hlinkP hXD hlkX
  have hb3 := hJ3.1.1
  have hlen3 : w3.path.length = P.length + 1 := by rw [hp3']; simp
  have hMF3 : ∀ x o, w3.madeFor.lookup x = some o → o < B := by rw [hJ3.2]; exact hMF
  have hJ23 : TakeJ2 c base B w3 := takeJ2_of_readsAs c base B w w3 hJ2 hr03
  obtain ⟨hne, hall, hLr⟩ := hleafC L n hL hn hnl
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
  refine takeJ2_deleteUpward_stepMBKG c base (fun i => nodeAt w.top.rootKey P i)
    (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
    (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length cv pre rk B w3 hdepth hfuel hpos hpX hpK hlkX htk3
    (fun i hi => hTimesR3 _ _ (hreach3 i hi) (hN3 i hi))
    hdistP (by rw [hNnD]; exact hne) (by rw [hNnD]; exact hall) (by rw [hNnD]; exact hnl) hT3 hR3 hwf3 hRt3
    hTimesR3 hICE3 hfit3 hnovalAll3 hreach3
    hlinkK (by rw [hr03.1, hr03.2.1]; exact hrk)
    (keyWf_last_notin pre cv hkey) (by rw [hr03.1, hXD]; exact hL)
    (by rw [hr03.1, hr03.2.1]; exact hI.keyUniq pre cv rk hkey hrk) hm
    (fun c' z hz => by
      rw [hNnD] at hz
      have := hcvAll c' z hz
      subst this
      rw [hr03.1]; exact hLV L n hL hn hnl z hz) hJ23 hMF3 _
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
      (fun _ v' h => ⟨h.1, h.2.trans hJ.2⟩)) ?_ ?_ ?_ ?_ ?_
  · intro seg stop w' sn' hsD hbetween ht htop hv hnodes hsn' hsl' hsw' hst' hlive' hread _ _ _ hJv _ hb'G gs hs
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
    refine writerWP_mono (hMU gs hs false w' ⟨⟨hDv, hb'.1.2.1, hb'.1.2.2⟩, hJv, hb'.1.1.fresh.1⟩) ?_
    intro _ w1 hD1
    exact hCR seg w1 hD1
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
    exact hA gs hs w' ⟨⟨hDv, hb'.1.2.1, hb'.1.2.2⟩, hJv, hb'.1.1.fresh.1⟩
  · intro stop w2 S hsD hbetween hLE hJw2G hsl hDR gs hs
    obtain ⟨hJw2, hgh2⟩ := hJw2G
    exact writerWP_mono (hC w w3 top0 pre cv rk (fun i => nodeAt w.top.rootKey P i)
      (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
      (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length stop w2 _ S hm hLC hJ3.1 hlen3 hgh2 hsa2 hvB hk hICEk
      (by simp [nodeAt]) hpos hB hI hRO hF hICE hr03 hkey hrk
      hvisw hpX hpK hlkX hXN hlinkK hne' hall' hnl' hdepth hsD hbetween hLE (Or.inr ⟨_, rfl⟩)
      (kdJP_note c base B top0 hB KO BK hvB hk _ "up.stop-at-segment-leaf" w2 hJw2) (Or.inl hsl) hDR hJ2 hMF3 hkidsw)
      (fun _ w' hD' => hA gs hs w' hD')
  · intro seg stop w2 S hsD hbetween hLE hJw2G hsl hK0 hDR gs hs
    obtain ⟨hJw2, hgh2⟩ := hJw2G
    refine writerWP_mono (hC w w3 top0 pre cv rk (fun i => nodeAt w.top.rootKey P i)
      (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
      (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length stop w2 _ S hm hLC hJ3.1 hlen3 hgh2 hsa2 hvB hk hICEk
      (by simp [nodeAt]) hpos hB hI hRO hF hICE hr03 hkey hrk
      hvisw hpX hpK hlkX hXN hlinkK hne' hall' hnl' hdepth hsD hbetween hLE (Or.inl rfl) hJw2
      (Or.inr hK0) hDR hJ2 hMF3 hkidsw) ?_
    intro _ w' hD'
    refine writerWP_mono (hMU gs hs false w' hD') ?_
    intro _ w1 hD1
    exact hCR seg w1 hD1
  · intro seg stop w2 S hsD hbetween hLE hJw2 hsl hK0 hsm gs hs
    exact (lebStop_false c base w hLC hm hI (fun i => nodeAt w.top.rootKey P i)
      (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
      (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length stop cv (by simp [nodeAt]) hXN hlinkK hall'
      hsD hbetween hsl).elim


/-- The walk with the obligations kept in `DelInvJ`: `writerWP_del_emptyAnyMJKLHGG`. -/
theorem writerWP_del_emptyAnyMJKLHG (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (hbook : PutBook c B top0 w)
    (KO : KindOracle) (BK : NodeId) (hvB : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c)
    (hb0 : Book BK c w) (hi0 : KdInv KO BK w)
    (hI : PutInv c base w) (hRO : RangeOrder (wNode c.p base w) c.i w.top.rootKey)
    (hF : SegFits (wNode c.p base w) c.i (c.p.fuel - 1) w.top.rootKey)
    (hICE : InnerChildrenExist (wNode c.p base w) c.i w.top.rootKey)
    (hkey : keyWf (pre ++ [cv]) = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hleafC : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
      n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = true ∧ L ≠ w.top.rootKey)
    (H : NodeId → Nat → Prop) (hC : UpCascJ2OKHG c base KO BK B H)
    (hLC : LiveCounts c.p (wNode c.p base w) c.i w.top.rootKey)
    (hvo : ViewHtOK H BK c) (hkw : ViewKlongsWf c.p c.view) (hhi : HtInv H BK c w) (hwfw : WriterKlongsWf w)
    (hub : UntakenBound (c.p.fuel - 1) w)
    (hsa2 : 2 ≤ c.p.splitAbove) (hICEk : ICEFromKinds c base KO BK)
    (hm : c.p.merges = true) (hpos : 0 < c.i)
    (hJ2 : TakeJ2 c base B w) (hMF : ∀ x o, w.madeFor.lookup x = some o → o < B)
    (hLV : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true → ∀ y, (cv, y) ∈ n.liveAt c.i →
      wNode c.p base w y = none)
    (hA : ∀ g h v, DelInvJ c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK B v →
      WriterWP (afterDelete (pre ++ [cv]) g h) c v (fun _ v' => DelInvJ c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK B v'))
    (hMU : ∀ g h merged v, DelInvJ c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK B v →
      WriterWP (mergeUp (pre ++ [cv]) g c.p.fuel h merged) c v
        (fun _ v' => DelInvJ c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK B v'))
    (hCR : ∀ seg v, DelInvJ c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK B v →
      WriterWP (collapseRoot (pre ++ [cv]) seg c.p.fuel) c v
        (fun _ v' => DelInvJ c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK B v')) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' => TakeJ2 c base B w') :=
  writerWP_del_emptyAnyMJKLHGG c base hvc pre cv rk w B top0 hB hbook KO BK hvB hk hb0 hi0 hI hRO hF
    hICE hkey hrk hleafC H hC hLC hvo hkw hhi hwfw hub hsa2 hICEk hm hpos hJ2 hMF hLV _ (fun g h v
    hv => writerWP_mono (hA g h v hv) (fun _ _ hv' => hv'.2.1)) hMU (fun seg v hv => writerWP_mono
    (hCR seg v hv) (fun _ _ hv' => hv'.2.1))
theorem delStepsCaseOK_emptyCascLHG (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts))
    (hRK : ∀ P t, R P t → KindsAllOK p P) (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (hht : OpHtDelOKUnder p R) (hdel : TakeBelowFuelDelOK p)
    (hU : ∀ ts, UpUnlinkTreeOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hHL : ∀ ts, UpHolderLiveRunOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hLC : StateOK p R (fun ts _ w => LiveCountsW p ts w)) :
    DelStepsCaseOK p R DelEmptyCascM := by
  intro ts tx hw hr z top hz htop ops op post hops r w hpre hI hRO hF key hop hPc hA hMU hCR
  have hLCw := hLC ts tx hw hr z top hz htop ops (op :: post) hops r w hpre
  obtain ⟨pre, cv, L0, n0, hop', hm, hK, hne0, hall0, P0, hP0, hX0, hl0, _⟩ := hPc
  subst hop'
  cases hop
  obtain ⟨hvo, hkw, hbase, hHb, _, hhi, hwfw, hub⟩ := htStart_reachedU p hM R hRL hRK hRH hht hdel ts tx hw hr z top
    hz htop ops (.del (pre ++ [cv]) :: post) hops r w hpre
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  have hICE := innerChildren_reached p hM hP ts tx hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
    (fun x hx => hI.untaken x (tReach_reachS _ _ _ _ hx))
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_context p hM hP ts tx hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
  have hwts : Within p ts := by
    have := within_take p (ts ++ [tx]) hw ts.length
    simpa using this
  have hKall := treeRun_kindsAllOK p hM hP ts hwts
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl hKall
      (hP ts hwts) hb hi.cache hun
  have hLr : L0 ≠ w.top.rootKey := by
    intro he
    obtain ⟨j, hj⟩ : ∃ j, P0.length = j + 1 := ⟨P0.length - 1, by omega⟩
    have hPL := LinkedFrom.pathLen _ _ _ P0 hP0
    have h1 := hPL P0.length (Nat.le_refl _)
    rw [hX0, he] at h1
    have h0 : PathLen (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey w.top.rootKey 0 :=
      PathLen.root
    have := PathLen.depth_unique hI.tree _ _ _ h1 h0
    omega
  refine writerWP_del_emptyAnyMKLHG (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w tx.base top hB hbook
    _ tx.base hv hk hb0 hi0 hI hRO hF hICE hkey hrk (keyLeaf_all2 hK hrk _ ⟨hne0, hall0, hLr⟩)
    _ (upCascOKHG_of _ _ _ _ _ (hU ts) (hHL ts)
      (upCascFitsOKR_of _ _ _ _ _ hvo hbase hHb (by simp [ctxOf]))) hLCw hvo hkw hhi hwfw hub
    (by simpa [ctxOf] using hsa2) hICEk hm (by simp [ctxOf]) hA hMU hCR
    _ (fun v hv' => by unfold fresh; wpSimplify; exact hv') ?_
  intro v hv' hFv key' hk'
  have := runGet_of_delInvF p ts w v (pre ++ [cv]) hv'.1 hI hF hFv key' hk'
  simpa [Op.key, Op.value] using this

theorem delStepsCaseJ2OK_emptyCascRLHG (p : Params) (R : Struct BVal → Time → Prop)
    (S : List Tx → Tx → W → Prop) (hM : 2 ≤ p.M) (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (hSI : ∀ ts tx w, S ts tx w → PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w)
    (hSV : ∀ ts tx w, S ts tx w → LeafVals (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w)
    (hSR : ∀ ts tx w, S ts tx w →
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey)
    (hSF : ∀ ts tx w, S ts tx w →
      SegFits (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) (p.fuel - 1) w.top.rootKey)
    (hSM : ∀ ts tx w, S ts tx w → ∀ x o, w.madeFor.lookup x = some o → o < tx.base)
    (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (hht : OpHtDelOKUnder p R) (hdel : TakeBelowFuelDelOK p)
    (hU : ∀ ts, UpUnlinkTreeOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hHL : ∀ ts, UpHolderLiveRunOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hLC : StateOK p R (fun ts _ w => LiveCountsW p ts w)) :
    DelStepsCaseJ2OK p R S DelEmptyCascM := by
  intro ts tx hw hr z top hz htop ops op post hops r w hpre hS hJ key hop hPc hA hMU hCR
  have hLCw := hLC ts tx hw hr z top hz htop ops (op :: post) hops r w hpre
  obtain ⟨pre, cv, L0, n0, hop', hm, hK, hne0, hall0, P0, hP0, hX0, hl0, _⟩ := hPc
  subst hop'
  cases hop
  obtain ⟨hvo, hkw, hbase, hHb, _, hhi, hwfw, hub⟩ := htStart_reachedU p hM R hRL hRK hRH hht hdel ts tx hw hr z top
    hz htop ops (.del (pre ++ [cv]) :: post) hops r w hpre
  have hI := hSI ts tx w hS
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  have hICE := innerChildren_reachedR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
    (fun x hx => hI.untaken x (tReach_reachS _ _ _ _ hx))
  have hLV := leafVals_all (hSV ts tx w hS) hkey hrk
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl (hRK _ _ hr)
      (hRP _ _ hr) hb hi.cache hun
  have hLr : L0 ≠ w.top.rootKey := by
    intro he
    obtain ⟨j, hj⟩ : ∃ j, P0.length = j + 1 := ⟨P0.length - 1, by omega⟩
    have hPL := LinkedFrom.pathLen _ _ _ P0 hP0
    have h1 := hPL P0.length (Nat.le_refl _)
    rw [hX0, he] at h1
    have h0 : PathLen (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey w.top.rootKey 0 :=
      PathLen.root
    have := PathLen.depth_unique hI.tree _ _ _ h1 h0
    omega
  exact writerWP_del_emptyAnyMJKLHG (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w tx.base top hB hbook
    _ tx.base hv hk hb0 hi0
    hI (hSR ts tx w hS) (hSF ts tx w hS) hICE hkey hrk (keyLeaf_all2 hK hrk _ ⟨hne0, hall0, hLr⟩)
    _ (upCascJ2OKHG_of _ _ _ _ _ _ (hU ts) (hHL ts)
      (upCascFitsOKR_of _ _ _ _ _ hvo hbase hHb (by simp [ctxOf]))) hLCw hvo hkw hhi hwfw hub
    (by simpa [ctxOf] using hsa2) hICEk hm
    (by simp [ctxOf]) hJ (hSM ts tx w hS) (fun L n hL hn hnl y hy => (hLV L n hL hn hnl y hy).1) hA hMU hCR

theorem delStepsCaseQd_emptyCascLHG (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (hht : OpHtDelOKUnder p R) (hdel : TakeBelowFuelDelOK p)
    (hU : ∀ ts, UpUnlinkTreeOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hHL : ∀ ts, UpHolderLiveRunOK (ctxOf p ts) (viewOf (treeRun p ts)))
    : DelStepsCaseQd p R DelEmptyCascML := by
  intro ts tx hw hr z top hz htop ops op post hops r w hpre hI hRO hF key hop hPcL hA hMU hCR
  obtain ⟨hPc, hLCw⟩ := hPcL
  obtain ⟨pre, cv, L0, n0, hop', hm, hK, hne0, hall0, P0, hP0, hX0, hl0, _⟩ := hPc
  subst hop'
  cases hop
  obtain ⟨hvo, hkw, hbase, hHb, _, hhi, hwfw, hub⟩ := htStart_reachedU p hM R hRL hRK hRH hht hdel ts tx hw hr z top
    hz htop ops (.del (pre ++ [cv]) :: post) hops r w hpre
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  have hICE := innerChildren_reachedR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
    (fun x hx => hI.untaken x (tReach_reachS _ _ _ _ hx))
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
  have hwts : Within p ts := by
    have := within_take p (ts ++ [tx]) hw ts.length
    simpa using this
  have hKall := hRK _ _ hr
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl hKall
      (hRP _ _ hr) hb hi.cache hun
  have hLr : L0 ≠ w.top.rootKey := by
    intro he
    obtain ⟨j, hj⟩ : ∃ j, P0.length = j + 1 := ⟨P0.length - 1, by omega⟩
    have hPL := LinkedFrom.pathLen _ _ _ P0 hP0
    have h1 := hPL P0.length (Nat.le_refl _)
    rw [hX0, he] at h1
    have h0 : PathLen (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey w.top.rootKey 0 :=
      PathLen.root
    have := PathLen.depth_unique hI.tree _ _ _ h1 h0
    omega
  refine writerWP_del_emptyAnyMKLHG (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w tx.base top hB hbook
    _ tx.base hv hk hb0 hi0 hI hRO hF hICE hkey hrk (keyLeaf_all2 hK hrk _ ⟨hne0, hall0, hLr⟩)
    _ (upCascOKHG_of _ _ _ _ _ (hU ts) (hHL ts)
      (upCascFitsOKR_of _ _ _ _ _ hvo hbase hHb (by simp [ctxOf]))) hLCw hvo hkw hhi hwfw hub
    (by simpa [ctxOf] using hsa2) hICEk hm (by simp [ctxOf]) hA hMU hCR
    (QdW p ts) (fun v hv' => qdW_fresh p ts v hv') (fun v hv' => ⟨hv'.1.1, hv'.1.2.2.1⟩)

/-- `DelStepsOK` with the fill at every operation's start (`hLC`) and the fuel
after the stop node's split from the heights (cost's `upCascFitsOKR_of`): open
are the state after the upward loop as a tree (`UpUnlinkTreeOK`) and holding
no taken-back node (`UpHolderLiveRunOK`), and the heights at every run; the
loop keeps the heights' cache (`writerWP_deleteUpward_stepJG`). -/
theorem delStepsOK_of_open (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts))
    (hRK : ∀ P t, R P t → KindsAllOK p P) (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (hht : OpHtDelOKUnder p R) (hdel : TakeBelowFuelDelOK p)
    (hU : ∀ ts, UpUnlinkTreeOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hHL : ∀ ts, UpHolderLiveRunOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hLC : StateOK p R (fun ts _ w => LiveCountsW p ts w)) :
    DelStepsOK p R :=
  delStepsOK_of_cases p R (delStepsCaseOK_noLeaf p R) (delStepsCaseOK_noop p R)
    (delStepsCaseOK_or p R _ _ _ delEmptyM_split (delStepsCaseOK_emptyRoom p R hM hRL hP)
      (delStepsCaseOK_or p R _ _ _ delEmptyOther_split (delStepsCaseOK_emptyRoot p R hM hsa2 hRL hP)
        (delStepsCaseOK_emptyCascLHG p R hM hsa2 hRL hP hRK hRH hht hdel hU hHL hLC)))
    (delStepsCaseOK_room p R hM hRL hP)
    (delStepsCaseOK_fullH p R hM hsa2 hRL hP hRK hRH hht hdel (fun ts => delFullRootStepOK_ctx p ts))

/-- `DelStepsJ2OK` (over R's pointers and kinds) with the fill
at every operation's start and the fuel after the stop node's split from the
heights: open are `UpUnlinkTreeOK`, `UpHolderLiveRunOK`, the heights at every
run and the S inputs. -/
theorem delStepsJ2OK_of_openR (p : Params) (R : Struct BVal → Time → Prop)
    (S : List Tx → Tx → W → Prop) (hM : 2 ≤ p.M) (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (hSI : ∀ ts tx w, S ts tx w → PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w)
    (hSV : ∀ ts tx w, S ts tx w → LeafVals (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w)
    (hSB : ∀ ts tx w, S ts tx w → tx.base ≤ w.next)
    (hSR : ∀ ts tx w, S ts tx w →
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey)
    (hSF : ∀ ts tx w, S ts tx w →
      SegFits (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) (p.fuel - 1) w.top.rootKey)
    (hSM : ∀ ts tx w, S ts tx w → ∀ x o, w.madeFor.lookup x = some o → o < tx.base)
    (hRH : ∀ P t, R P t → HeightAllOK p P t) (hht : OpHtDelOKUnder p R) (hdel : TakeBelowFuelDelOK p)
    (hU : ∀ ts, UpUnlinkTreeOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hHL : ∀ ts, UpHolderLiveRunOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hLC : StateOK p R (fun ts _ w => LiveCountsW p ts w)) :
    DelStepsJ2OK p R S :=
  delStepsJ2OK_of_cases p R S (delStepsCaseJ2OK_noLeaf p R S hSI) (delStepsCaseJ2OK_noop p R S hSI)
    (delStepsCaseJ2OK_or p R S _ _ _ delEmptyM_split
      (delStepsCaseJ2OK_emptyRoomR p R S hM hRL hRP hRK hSI hSV hSR hSF hSM)
      (delStepsCaseJ2OK_or p R S _ _ _ delEmptyOther_split
        (delStepsCaseJ2OK_emptyRootR p R S hM hsa2 hRL hRP hRK hSI hSV hSB hSR)
        (delStepsCaseJ2OK_emptyCascRLHG p R S hM hsa2 hRL hRP hRK hSI hSV hSR hSF hSM hRH hht hdel hU hHL
          hLC)))
    (delStepsCaseJ2OK_roomR p R S hM hRL hRP hRK hSI hSV hSB hSR hSF)
    (delStepsCaseJ2OK_fullRH p R S hM hsa2 hRL hRP hRK hSI hSV hSB hSR hSF hRH hht hdel)

/-- `DelStepsQdL` with the fuel after the stop node's split from the heights:
open are `UpUnlinkTreeOK`, `UpHolderLiveRunOK` and the heights at every run. -/
theorem delStepsQdL_of_openR (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (hht : OpHtDelOKUnder p R) (hdel : TakeBelowFuelDelOK p)
    (hU : ∀ ts, UpUnlinkTreeOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hHL : ∀ ts, UpHolderLiveRunOK (ctxOf p ts) (viewOf (treeRun p ts))):
    DelStepsQdL p R := by
  intro ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop hmL hA hMU hCR
  obtain ⟨⟨key', hop', hm'⟩, hLCw⟩ := hmL
  rw [hop] at hop'
  cases hop'
  rcases delMerge_cover (ctxOf p ts) (viewOf (treeRun p ts)) w key hm' with h | h | h | h | h
  · exact delStepsCaseQd_noLeaf p R ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop
      (hop ▸ h) hA hMU hCR
  · exact delStepsCaseQd_noop p R hRL ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop
      (hop ▸ h) hA hMU hCR
  · rcases delEmptyM_split _ _ _ _ h with h1 | h1
    · exact delStepsCaseQd_emptyRoom p R hM hRL hRP hRK ts tx hw hr z top hz htop pre op post hops r w hpre
        hI hRO hF key hop (hop ▸ h1) hA hMU hCR
    · rcases delEmptyOther_split _ _ _ _ h1 with h2 | h2
      · exact delStepsCaseQd_emptyRoot p R hM hsa2 hRL hRP hRK ts tx hw hr z top hz htop pre op post hops r w
          hpre hI hRO hF key hop (hop ▸ h2) hA hMU hCR
      · exact delStepsCaseQd_emptyCascLHG p R hM hsa2 hRL hRP hRK hRH hht hdel hU hHL
          ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop (hop ▸ ⟨h2, hLCw⟩) hA hMU hCR
  · exact delStepsCaseQd_room p R hM hRL hRP hRK ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF
      key hop (hop ▸ h) hA hMU hCR
  · exact delStepsCaseQd_fullH p R hM hsa2 hRL hRP hRK hRH hht hdel (fun ts => delFullRootStepOK_ctx p ts)
      ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop (hop ▸ h) hA hMU hCR

end SIS.Tree
