/-
The upward delete's walk of the stratum (`takeJ2_deleteUpward_stepMBKGD`,
DelStepsGh.lean) whose continuations at a segment leaf stop node also know the
climb's stop (the space root if the stop node empties too) and the stop node's
entry in `gh` (bergdb 030-01, step 6): near-copies, the old walks unchanged.
-/
import SIS.Tree.DelStepsGh
import SIS.Tree.LiveSplitRoom2

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

set_option maxHeartbeats 1600000 in
/-- `writerWP_deleteUpward_stepJG` whose leaf step also knows the climb's stop (the
space root if the stop node empties) and the stop node's entry in `gh` (bergdb
030-01, step 6). `writerWP_deleteUpward_stepJ` whose take-back and unlink steps know the
nodes they read cached. The upward delete that empties its leaf X depth, the merges on, given the
stop node's step at the loop's end (`UpLoopEnd`): a segment leaf's bitmap then
`afterDelete` (`hleafStep`), an inner node's bitmap (`hinnerStep`) or LE-b
(`hlebStep`) then the merges' loop and root collapse, each from the state the
loop leaves, with J kept through the loop (the notes, the take-backs, the
unlinks). -/
theorem writerWP_deleteUpward_stepJGS (c : Ctx) (base : View BVal) (X : Nat → NodeId)
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
      UpLoopEnd c B X Nn depth stop w w2 S → J w2 → (Nn stop).leaf = true →
      ((Nn stop).allKeysIn (bitsUnion (Nn stop).lastBitmap ((Nn stop).bitsOf (K (stop + 1)))) = true →
        stop = 0 ∧ (Nn 0).leaf = true) → ∀ gs hs : Nat, w2.gh.lookup (X stop) = some (gs, hs) →
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
  refine writerWP_ghOf_cachedL _ _ c w2 hSl _ (fun gh hgh => ?_)
  have hLE : UpLoopEnd c B X Nn depth stop w w2 S :=
    ⟨fun y hy => by rw [h2t y hy, h0t], by rw [h2top, h0top], by rw [h2v, h0v], by rw [h2p, h0p],
      by rw [h2m, h0m], by rw [h2nx, h0nx], fun y hys hnc => by rw [h2n y hys hnc, h0n], hSl, hS, hSR, hSF', hfate2, hfateJ2⟩
  have hSleaf : S.leaf = (Nn stop).leaf := by rcases hS with rfl | ⟨ti, dst, rfl⟩ <;> rfl
  cases hsl : (Nn stop).leaf with
  | true =>
    have hsl' : S.leaf = true := hSleaf.trans hsl
    simp only [hsl', ↓reduceIte, writerWP_bind]
    refine (writerWP_note_iff _ c w2 _).mpr ?_
    refine writerWP_mono (hleafStep stop w2 S hsD hbetween hLE hJw2 hsl (hstopNode hsD) gh.1 gh.2 hgh) ?_
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
/-- `takeJ2_deleteUpward_stepMBKGD` whose leaf continuations also know the climb's
stop and the stop node's entry in `gh`, and whose inner continuation with a bitmap
knows that the stop node is inner (bergdb 030-01, step 6). `takeJ2_deleteUpward_stepMBKG` with the fit at the start at any depth d, the
continuations given `CollGetInvD` at d (bergdb 025-05, step 7). -/
theorem takeJ2_deleteUpward_stepMBKGDS (c : Ctx) (base : View BVal)
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
      TakeJ2 c base B w' → CollGetInvD c base w' d → J w' → (Nn stop).leaf = false →
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
      ((Nn stop).allKeysIn (bitsUnion (Nn stop).lastBitmap ((Nn stop).bitsOf (K (stop + 1)))) = true →
        stop = 0 ∧ (Nn 0).leaf = true) →
      ∀ gs hs : Nat, (∃ v, J v ∧ v.gh.lookup (X stop) = some (gs, hs)) →
      WriterWP (afterDelete (pre ++ [cv]) gs hs) c w' (fun _ w'' => Q w''))
    (hcascLeaf : ∀ (stop : Nat) (w2 : W) (S : KNode), stop < depth →
      (∀ i, stop < i → i < depth →
        (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true) →
      UpLoopEnd c B X Nn depth stop w w2 S → J w2 → (Nn stop).leaf = true →
      ((Nn stop).allKeysIn (bitsUnion (Nn stop).lastBitmap ((Nn stop).bitsOf (K (stop + 1)))) = true →
        stop = 0 ∧ (Nn 0).leaf = true) →
      ¬ DelRoom c (K (stop + 1)) S → ∀ gs hs : Nat, w2.gh.lookup (X stop) = some (gs, hs) →
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
  refine writerWP_deleteUpward_stepJGS c base X Nn K depth cv pre B w Q J hJ0 hJnote hJtake hJunlink hMF hdepth
    hpos hp hk hlk htk htimes hdist hne hall hwf hreach hmerges ?_ ?_ ?_
  · intro stop w2 S hsD hbetween hLE hJw2 hsl hstp gs hs hgh
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
          hJ hI hJw' hstp gs hs ⟨w2, hJw2, hgh⟩
    · exact hcascLeaf stop w2 S hsD hbetween hLE hJw2 hsl hstp hDR gs hs hgh
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
          hst0 hJ hI hJw' hsl gs hs
    · exact hcascInner seg stop w2 S hsD hbetween hLE hJw2 hsl hK0 hDR gs hs
  · exact hlebStep
end SIS.Tree
