/-
The upward delete with its invariant's steps knowing the path
(`writerWP_deleteUpward_upT_getJMB` with `hJadk` and `hJekn` given the node's
place on the path, and for LE-b the node inner): for the kinds' books
(bergdb 024-12, latest's F3 route).
-/
import SIS.Tree.DelStepsUp

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

theorem writerWP_deleteUpward_upT_getJMBK (c : Ctx) (base : View BVal) (X : Nat → NodeId)
    (Nn : Nat → KNode) (K : Nat → Nat) (depth cv : Nat) (pre : List Nat) (rk : NodeId)
    (B : NodeId) (w : W) (Q : W → Prop) (J : W → Prop) (hJ0 : J w)
    (hJnote : ∀ (s : String) (v : W), J v → J { v with trail := s :: v.trail })
    (hJtake : ∀ (x p : NodeId) (k : Nat) (v : W), J v → (∃ xn, v.nodes.lookup x = some xn) →
      WriterWP (takeBack x p k) c v (fun _ v' => J v'))
    (hJunlink : ∀ (x : NodeId) (v : W), J v → WriterWP (unlink x) c v (fun _ v' => J v'))
    (hJadk : ∀ (x : NodeId) (d k : Nat) (v : W), J v → (w.path[d]?).map (·.2) = some x →
      WriterWP (appendDeleteKlong x d k) c v (fun _ v' => J v'))
    (hJekn : ∀ (x : NodeId) (d : Nat) (v : W) (xn : KNode), J v → (w.path[d]?).map (·.2) = some x →
      v.nodes.lookup x = some xn → xn.leaf = false → WriterWP (emptyKeyNext x d) c v (fun _ v' => J v'))
    (hMF : ∀ x o, w.madeFor.lookup x = some o → o < B) (hdepth : 0 < depth) (hfuel : 1 ≤ c.p.fuel) (hpos : 0 < c.i)
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
    (hreach : ∀ i, i ≤ depth → TReach (wNode c.p base w) c.i w.top.rootKey (X i))
    (hlinkK : ∀ i, 0 < i → i ≤ depth → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (hnoval : ∀ i, i ≤ depth → wValue base w (X i) = none)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk) (hcv : cv ∉ pre)
    (hvisL : (X depth, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk)
    (huniq : ∀ key' x m, keyWf key' = true →
      (x, cv) ∈ fromVisits (wNode c.p base w) c.i c.p.fuel key' w.top.rootKey →
      (x, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk → wNode c.p base w x = some m →
      m.leaf = true → key' = pre ++ [cv])
    (hstopOK : ∀ s, s < depth → (∀ i, s < i → i < depth →
        (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true) →
      (((Nn s).leaf = true ∨ K (s + 1) ≠ 0) → (Nn s).size + 1 < c.p.M ∧
        deadOver c.p ((Nn s).setAt ((Nn s).size - 1)
          (.del (bitsUnion (Nn s).lastBitmap ((Nn s).bitsOf (K (s + 1)))))) = false ∧
        deadOver c.p ((Nn s).add c.i (.del (bitsUnion (Nn s).lastBitmap ((Nn s).bitsOf (K (s + 1)))))) =
          false) ∧
      ((Nn s).leaf = false → K (s + 1) = 0 → (Nn s).size + 3 ≤ c.p.M ∧
        ∀ b1 b2 e jcv jy, deadOver c.p (lebNode (Nn s) c.i b1 b2 e jcv jy) = false))
    (hmerges : c.p.merges = true)
    (hcoll : ∀ (seg stop : Nat) (w' : W) (sn' : KNode), stop < depth →
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
      J w' → ∀ gs hs : Nat, WriterWP (mergeUp (pre ++ [cv]) gs c.p.fuel hs false) c w' (fun _ w1 =>
        WriterWP (collapseRoot (pre ++ [cv]) seg c.p.fuel) c w1 (fun _ w'' => Q w'')))
    (hleafQ : ∀ (stop : Nat) (w' : W) (sn' : KNode), stop < depth →
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
      J w' → ∀ gs hs : Nat, WriterWP (afterDelete (pre ++ [cv]) gs hs) c w' (fun _ w'' => Q w''))
    (hcollLeb : ∀ (seg stop : Nat) (w' : W) (sn' : KNode) (jcv : Nat) (jy : NodeId), stop < depth →
      (∀ i, stop < i → i < depth →
        (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true) →
      (∀ y, (∀ k, stop < k → k ≤ depth → y ≠ X k) → w'.taken.contains y = w.taken.contains y) →
      w'.top = w.top → w'.vals = w.vals →
      (∀ y, y ≠ X stop → (∀ k, stop < k → k ≤ depth → y ≠ X k) → w'.nodes.lookup y = w.nodes.lookup y) →
      w'.nodes.lookup (X stop) = some sn' → sn'.leaf = (Nn stop).leaf → klongsWf sn'.ks = true →
      (∀ s, Klong.time s ∈ sn'.ks → s ≤ c.i) → (Nn stop).leaf = false → K (stop + 1) = 0 →
      (jcv, jy) ∈ (Nn stop).liveAt c.i → 0 < jcv →
      (∀ c' z, (c', z) ∈ (Nn stop).liveAt c.i → c' ≠ 0 → jcv ≤ c') →
      (∀ c' z, (c', z) ∈ sn'.liveAt c.i ↔
        (c' = 0 ∧ z = jy) ∨ ((c', z) ∈ (Nn stop).liveAt c.i ∧ c' ≠ 0 ∧ c' ≠ jcv)) →
      (∀ key', keyWf key' = true →
        wGet c.p c.i base w' key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w key') →
      (∀ k, stop < k → k ≤ depth → ChainFate c.i w' (X k)) →
      (∀ k, stop < k → k ≤ depth → ChainFateW c.i B w' (Nn k) (X k)) →
      (∃ S, RetFormS c.i B (Nn stop) S ∧
        ((Nn (stop + 1)).firstTime = some c.i → RetFrom c.i B (Nn stop) (X (stop + 1)) S) ∧
        ∃ htd lip e0, sn' = lebNode S c.i htd lip e0 jcv jy ∧
          (htd = true → (∃ old, S.ks.getLast? = some (.del old)) ∧ S.lastTime = some c.i) ∧
          (lip = true → S.lastTime = some c.i ∧ ∃ ti, S.lastTimeIndex = some ti ∧ ti < e0)) →
      J w' → ∀ gs hs : Nat, WriterWP (mergeUp (pre ++ [cv]) gs c.p.fuel hs false) c w' (fun _ w1 =>
        WriterWP (collapseRoot (pre ++ [cv]) seg c.p.fuel) c w1 (fun _ w'' => Q w''))) :
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
  obtain ⟨hbitRoom, hlebRoom⟩ := hstopOK stop hsD hbetween
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
    v.madeFor = w0.madeFor ∧
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
    ⟨hJw0, rfl, rfl, rfl, fun _ _ => rfl, fun _ _ _ => rfl, rfl, 0, by rw [List.range_eq_range']; rfl,
      Nat.zero_le _, fun j hj => absurd hj (Nat.not_lt_zero _), fun j hj => absurd hj (Nat.not_lt_zero _),
      fun j _ hj => by rw [h0t]; exact htk _ (by omega),
      fun j _ hj => by rw [h0n]; exact hlk _ (by omega),
      Nn (depth - 0), by rw [h0n]; exact hlk _ (by omega), Or.inl rfl, Or.inl rfl,
      fun h => absurd h (Nat.lt_irrefl 0)⟩) ?_
  · intro a rest v ⟨hJv, hvtop, hvv, hvp, hvt, hvn, hvm, a0, hrem, ha0, hfv, hfvJ, hnt, hexact, S, hSl, hS,
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
        (hJtake _ _ _ v hJv ⟨_, hSl⟩)) ?_
      rintro _ v2 ⟨⟨h2t, h2top, h2v, h2p, h2m, _, h2n, hlt2, old, hold, h2l⟩, hJv2⟩
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
        fun y hys hy => ?_, h2m.trans hvm, a + 1, hrest, by omega, fun j hj => ?_, fun j hj => ?_,
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
        (writerWP_unlink_fate _ _ c _ hSl)) (hJunlink _ _ (hJnote _ v hJv))) ?_
      rintro _ v2 ⟨⟨⟨h2t, h2top, _, h2v, h2p, h2m, h2l⟩, ⟨_, _, _, h2x, _⟩⟩, hJv2⟩
      have hmadeN : (Nn (depth - a)).firstTime ≠ some c.i := by
        rw [← retFormS_firstTime c.i B _ S hSR]; simpa using hmadeS
      simp only [writerWP_pure]
      refine ⟨by first | rfl | trivial, hJv2, h2top.trans hvtop, h2v.trans hvv, h2p.trans hvp,
        fun y hy => by rw [h2t]; exact hvt y hy, fun y hys hy => ?_, h2m.trans hvm, a + 1, hrest, by omega,
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
  rintro _ w2 ⟨hJw2, h2top, h2v, h2p, h2t, h2n, _, a0, hrem, ha0, hfv2, hfvJ2, hnt2, _, S, hSl, hS, hSR, hSF⟩
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
  have hXs : ∀ k, stop < k → k ≤ depth → X stop ≠ X k :=
    fun k h1 h2 he => by have := hdist _ _ (by omega) h2 he; omega
  have hst_t : ∀ s', Klong.time s' ∈ (Nn stop).ks → s' ≤ c.i := htimes stop (by omega)
  have hsx : (K (stop + 1), X (stop + 1)) ∈ (Nn stop).liveAt c.i := by
    have := hlinkK (stop + 1) (by omega) (by omega); simpa using this
  have hneS : bitsUnion (Nn stop).lastBitmap ((Nn stop).bitsOf (K (stop + 1))) ≠ (Nn stop).lastBitmap := by
    apply KNode.delete_bitmap_changes_of_live
    rw [KNode.liveAt_of_times _ c.i hst_t] at hsx
    exact List.mem_map.mpr ⟨_, hsx, rfl⟩
  have hswf : klongsWf (Nn stop).ks = true := by
    have := hwf (X stop) (Nn stop) (hreach stop (by omega))
      (by simp only [wNode, htk stop (by omega), Bool.false_eq_true, ↓reduceIte, hlk stop (by omega)])
    exact this
  -- the stop node now: its node before, or that retargeted from the chain
  have hu : ∀ c', (c', X (stop + 1)) ∈ (Nn stop).liveAt c.i → c' = K (stop + 1) := by
    intro c' h
    have hNs : wNode c.p base w (X stop) = some (Nn stop) := by
      simp only [wNode, htk stop (by omega), Bool.false_eq_true, ↓reduceIte, hlk stop (by omega)]
    exact (hT.oneLink _ _ _ _ _ (hreach stop (by omega)) (hreach stop (by omega)) ⟨_, hNs, h⟩
      ⟨_, hNs, hsx⟩).2
  have hSf : S.shapeOf = (Nn stop).shapeOf ∧ S.leaf = (Nn stop).leaf ∧ klongsWf S.ks = true ∧
      (∀ s, Klong.time s ∈ S.ks → s ≤ c.i) ∧
      ∀ c' z, ((c', z) ∈ S.liveAt c.i ∧ c' ≠ K (stop + 1)) ↔
        ((c', z) ∈ (Nn stop).liveAt c.i ∧ c' ≠ K (stop + 1)) := by
    rcases hS with rfl | ⟨ti, dst, rfl⟩
    · exact ⟨rfl, rfl, hswf, hst_t, fun _ _ => Iff.rfl⟩
    · exact ⟨KNode.retarget_shapeOf _ _ _ _, rfl, by rw [klongsWf_retargetKlongs]; exact hswf,
        KNode.retarget_times _ _ _ _ _ hst_t, KNode.retarget_liveAt_ne _ _ _ _ _ _ hu⟩
  obtain ⟨hSsh, hSleaf, hSwf, hSt, hSlive⟩ := hSf
  -- the chain's facts
  have hone : ∀ i, stop < i → i < depth → ∀ c' z, (c', z) ∈ (Nn i).liveAt c.i → z = X (i + 1) := by
    intro i h1 h2 c' z hm
    have ht := htimes i (by omega)
    have hm' : (c', z) ∈ (Nn i).live := by rw [← KNode.liveAt_of_times _ c.i ht]; exact hm
    have hc := allKeysIn_live_cv (Nn i) (K (i + 1)) (hbetween i h1 h2) c' z hm'
    have hl := hlinkK (i + 1) (by omega) (by omega)
    rw [show i + 1 - 1 = i by omega] at hl
    rw [KNode.liveAt_of_times _ c.i ht] at hl
    have hnd := KNode.live_keys_nodup (Nn i)
    have e1 := lookup_some_of_mem hnd hm'
    have e2 := lookup_some_of_mem hnd hl
    rw [hc] at e1
    rw [e1] at e2
    exact Option.some.inj e2
  have honly : ∀ c' z, (c', z) ∈ (Nn depth).liveAt c.i → c' = cv := by
    intro c' z hm
    have hm' : (c', z) ∈ (Nn depth).live := by
      rw [← KNode.liveAt_of_times _ c.i (htimes depth (Nat.le_refl _))]; exact hm
    exact allKeysIn_live_cv (Nn depth) cv hall c' z hm'
  -- the bitmap at the stop node, from any state with w2's nodes
  have hbit : ((Nn stop).leaf = true ∨ K (stop + 1) ≠ 0) →
      ∀ (v : W), v.nodes = w2.nodes → v.taken = w2.taken → v.top = w2.top → v.vals = w2.vals → J v →
      ∀ (post : W → Prop), (∀ w3 n',
        (∀ y, (∀ k, stop < k → k ≤ depth → y ≠ X k) → w3.taken.contains y = w.taken.contains y) →
        w3.top = w.top → w3.vals = w.vals →
        (∀ y, y ≠ X stop → (∀ k, stop < k → k ≤ depth → y ≠ X k) →
          w3.nodes.lookup y = w.nodes.lookup y) →
        w3.nodes.lookup (X stop) = some n' → n'.leaf = (Nn stop).leaf → klongsWf n'.ks = true →
        (∀ s, Klong.time s ∈ n'.ks → s ≤ c.i) →
        (∀ c' z, (c', z) ∈ n'.liveAt c.i ↔ (c', z) ∈ (Nn stop).liveAt c.i ∧ c' ≠ K (stop + 1)) →
        (∀ key', keyWf key' = true → wGet c.p c.i base w3 key' =
          if pre ++ [cv] == key' then none else wGet c.p c.i base w key') →
        (∀ k, stop < k → k ≤ depth → ChainFate c.i w3 (X k)) →
        (∀ k, stop < k → k ≤ depth → ChainFateW c.i B w3 (Nn k) (X k)) →
        (∃ S', RetFormS c.i B (Nn stop) S' ∧
          ((Nn (stop + 1)).firstTime = some c.i → RetFrom c.i B (Nn stop) (X (stop + 1)) S') ∧
          BitmapOf S' n' c.i (K (stop + 1))) → J w3 → post w3) →
      WriterWP (appendDeleteKlong (X stop) stop (K (stop + 1))) c v (fun _ w3 => post w3) := by
    intro hkind v hvn hvt hvtop hvv hJv post hpost
    obtain ⟨hroom, hd1, hd2⟩ := hbitRoom hkind
    have hneS' : bitsUnion S.lastBitmap (S.bitsOf (K (stop + 1))) ≠ S.lastBitmap := by
      rw [KNode.lastBitmap_of_shapeOf hSsh, KNode.bitsOf_of_shapeOf hSsh]; exact hneS
    have hroom' : S.size + 1 < c.p.M := by rw [KNode.size_of_shapeOf hSsh]; exact hroom
    have hd1' : deadOver c.p (S.setAt (S.size - 1)
        (.del (bitsUnion S.lastBitmap (S.bitsOf (K (stop + 1)))))) = false := by
      rw [deadOver_of_shapeOf c.p (KNode.setAt_shapeOf hSsh _ _), KNode.size_of_shapeOf hSsh,
        KNode.lastBitmap_of_shapeOf hSsh, KNode.bitsOf_of_shapeOf hSsh]
      exact hd1
    have hd2' : deadOver c.p (S.add c.i (.del (bitsUnion S.lastBitmap (S.bitsOf (K (stop + 1)))))) =
        false := by
      rw [deadOver_of_shapeOf c.p (KNode.add_shapeOf hSsh _ _),
        KNode.lastBitmap_of_shapeOf hSsh, KNode.bitsOf_of_shapeOf hSsh]
      exact hd2
    refine writerWP_mono (writerWP_and (writerWP_appendDeleteKlong_room_exact (X stop) stop (K (stop + 1)) S
      c v (by rw [hvn]; exact hSl) hSt hSwf hneS' hroom' hd1' hd2') (hJadk _ _ _ v hJv (hp stop (by omega)))) ?_
    rintro _ w3 ⟨⟨h3t, h3top, h3v, _, _, _, n', h3n, hn'l, hn'w, hn't, hn'lk, hbm⟩, hJ3⟩
    have h3tw : ∀ y, (∀ k, stop < k → k ≤ depth → y ≠ X k) → w3.taken.contains y = w.taken.contains y := by
      intro y hy; rw [h3t, hvt, h2t y hy, h0t]
    have h3top' : w3.top = w.top := by rw [h3top, hvtop, h2top, h0top]
    have h3v' : w3.vals = w.vals := by rw [h3v, hvv, h2v, h0v]
    have hfr : ∀ y, y ≠ X stop → (∀ k, stop < k → k ≤ depth → y ≠ X k) →
        w3.nodes.lookup y = w.nodes.lookup y := by
      intro y hys hnc
      rw [h3n, lookup_upsert]
      simp only [hys, ↓reduceIte]
      rw [hvn, h2n y hys hnc, h0n]
    have hsn3 : w3.nodes.lookup (X stop) = some n' := by rw [h3n, lookup_upsert]; simp
    have hlive' : ∀ c' z, (c', z) ∈ n'.liveAt c.i ↔ (c', z) ∈ (Nn stop).liveAt c.i ∧ c' ≠ K (stop + 1) := by
      intro c' z
      rw [liveAt_iff_of_delete_lookup S n' c.i (K (stop + 1)) hSt hn't hn'lk c' z]
      exact hSlive c' z
    have hfate3 : ∀ k, stop < k → k ≤ depth → ChainFate c.i w3 (X k) := by
      intro k h1 h2
      refine chainFate_frame c.i w2 w3 (X k) (hfate2 k h1 h2) (by rw [h3t, hvt]) ?_
      rw [h3n, lookup_upsert]
      simp only [Ne.symm (hXs k h1 h2), ↓reduceIte]
      rw [hvn]
    have hfateJ3 : ∀ k, stop < k → k ≤ depth → ChainFateW c.i B w3 (Nn k) (X k) := by
      intro k h1 h2
      refine chainFateW_frame c.i B w2 w3 (Nn k) (X k) (hfateJ2 k h1 h2) (by rw [h3t, hvt]) ?_
      rw [h3n, lookup_upsert]
      simp only [Ne.symm (hXs k h1 h2), ↓reduceIte]
      rw [hvn]
    refine hpost w3 n' h3tw h3top' h3v' hfr hsn3 (by rw [hn'l, hSleaf]) hn'w hn't hlive' ?_ hfate3
      hfateJ3 ⟨S, hSR, hSF', hbm⟩ hJ3
    intro key' hkw
    have hV3 : wValue base w3 = wValue base w :=
      wValue_eq_of_taken base w w3 h3v' (fun y => ∃ k, stop < k ∧ k ≤ depth ∧ y = X k)
        (fun y hy => h3tw y (fun k h1 h2 he => hy ⟨k, h1, h2, he⟩))
        (fun y ⟨k, _, h2, he⟩ => by rw [he]; exact ⟨htk k h2, hnoval k h2⟩)
    have hagree : ∀ u, TReach (wNode c.p base w) c.i w.top.rootKey u → u ≠ X stop →
        (∀ i, stop < i → i ≤ depth → u ≠ X i) → wNode c.p base w3 u = wNode c.p base w u := by
      intro u _ hus hnc
      simp only [wNode, h3tw u hnc, hfr u hus hnc]
    have hsnw : wNode c.p base w3 (X stop) = some n' := by
      simp only [wNode, h3tw (X stop) hXs, htk stop (by omega), Bool.false_eq_true, ↓reduceIte, hsn3]
    unfold wGet
    rw [hV3, h3top']
    cases hl : (Nn stop).leaf with
    | false =>
      have hK0 : K (stop + 1) ≠ 0 := by
        rcases hkind with h | h
        · rw [hl] at h; cases h
        · exact h
      exact getFromR_up_inner (wNode c.p base w) (wNode c.p base w3) (wValue base w) c.i c.p.fuel hfuel
        w.top.rootKey X Nn K stop depth hsD pre cv rk hT hR hwf (hreach stop (by omega))
        (fun i h1 h2 => by simp only [wNode, htk i h2, Bool.false_eq_true, ↓reduceIte, hlk i h2])
        (fun i h1 h2 => hlinkK i (by omega) h2) hone hleaf honly (fun i h1 h2 => hnoval i h2)
        (fun i h1 h2 he => by have := hdist i depth (by omega) (Nat.le_refl _) he; omega)
        hrk hcv hvisL huniq hagree n' hl hsnw (by rw [hn'l, hSleaf]; exact hl) hlive' key' hkw
    | true =>
      exact getFromR_up_leaf (wNode c.p base w) (wNode c.p base w3) (wValue base w) c.i c.p.fuel hfuel
        w.top.rootKey X Nn K stop depth hsD pre cv rk hT hR hwf (hreach stop (by omega))
        (fun i h1 h2 => by simp only [wNode, htk i h2, Bool.false_eq_true, ↓reduceIte, hlk i h2])
        (fun i h1 h2 => hlinkK i (by omega) h2) hone hleaf honly (fun i h1 h2 => hnoval i h2)
        (fun i h1 h2 he => by have := hdist i depth (by omega) (Nat.le_refl _) he; omega)
        hrk hcv hvisL huniq hagree n' hl hsnw (by rw [hn'l, hSleaf]; exact hl) hn'w hlive' key' hkw
  cases hsl : (Nn stop).leaf with
  | true =>
    have hsl' : S.leaf = true := hSleaf.trans hsl
    simp only [hsl', ↓reduceIte, writerWP_bind]
    refine (writerWP_note_iff _ c w2 _).mpr ?_
    refine hbit (Or.inl hsl) _ ?_ ?_ ?_ ?_ (hJnote _ w2 hJw2) _ ?_
    rotate_left 4
    · intro w3 n' h3t h3top h3v hfr hsn3 hn'l hn'w hn't hlive' hread hf3 hf3J hst3 hJ3
      refine writerWP_mono (hleafQ stop w3 n' hsD hbetween h3t h3top h3v hfr hsn3 hn'l hn'w hn't hlive' hread
        hf3 hf3J hst3 hJ3 gh.1 gh.2) ?_
      intro _ w4 h4
      simp only [writerWP_pure]
      exact h4
    all_goals rfl
  | false =>
    have hsl' : S.leaf = false := hSleaf.trans hsl
    simp only [hsl', Bool.false_eq_true, ↓reduceIte]
    split
    · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
    by_cases hK0 : K (stop + 1) = 0
    · -- LE-b
      have hK0' : (K (stop + 1) != 0) = false := by simp [hK0]
      simp only [hK0', Bool.false_eq_true, ↓reduceIte, writerWP_bind]
      obtain ⟨hroomL, hdeadL⟩ := hlebRoom hsl hK0
      have hroomL' : S.size + 3 ≤ c.p.M := by rw [KNode.size_of_shapeOf hSsh]; exact hroomL
      have hdeadL' : ∀ b1 b2 e jcv jy, deadOver c.p (lebNode S c.i b1 b2 e jcv jy) = false := by
        intro b1 b2 e jcv jy
        rw [deadOver_of_shapeOf c.p (lebNode_shapeOf hSsh _ _ _ _ _ _)]
        exact hdeadL _ _ _ _ _
      refine writerWP_mono (writerWP_and (writerWP_emptyKeyNext_room_exact (X stop) stop S c w2 hSl hSwf hSt
        hroomL' hdeadL') (hJekn _ _ w2 S hJw2 (hp stop (by omega)) hSl hsl')) ?_
      rintro _ w3 ⟨⟨h3t, h3top, h3v, _, _, _, n', jcv, jy, h3n, hn'l, hn'w, hn't, hjS, hj0, hmin, hn'lk,
        htdL, lipL, e0L, hleb, hhtdL, hlipL⟩, hJ3⟩
      have hj : (jcv, jy) ∈ (Nn stop).liveAt c.i :=
        ((hSlive jcv jy).mp ⟨hjS, by rw [hK0]; omega⟩).1
      have h3tw : ∀ y, (∀ k, stop < k → k ≤ depth → y ≠ X k) → w3.taken.contains y = w.taken.contains y := by
        intro y hy; rw [h3t, h2t y hy, h0t]
      have h3top' : w3.top = w.top := by rw [h3top, h2top, h0top]
      have h3v' : w3.vals = w.vals := by rw [h3v, h2v, h0v]
      have hfr : ∀ y, y ≠ X stop → (∀ k, stop < k → k ≤ depth → y ≠ X k) →
          w3.nodes.lookup y = w.nodes.lookup y := by
        intro y hys hnc
        rw [h3n, lookup_upsert]
        simp only [hys, ↓reduceIte]
        rw [h2n y hys hnc, h0n]
      have hsn3 : w3.nodes.lookup (X stop) = some n' := by rw [h3n, lookup_upsert]; simp
      have hfate3 : ∀ k, stop < k → k ≤ depth → ChainFate c.i w3 (X k) := by
        intro k h1 h2
        refine chainFate_frame c.i w2 w3 (X k) (hfate2 k h1 h2) (by rw [h3t]) ?_
        rw [h3n, lookup_upsert]
        simp only [Ne.symm (hXs k h1 h2), ↓reduceIte]
      have hfateJ3 : ∀ k, stop < k → k ≤ depth → ChainFateW c.i B w3 (Nn k) (X k) := by
        intro k h1 h2
        refine chainFateW_frame c.i B w2 w3 (Nn k) (X k) (hfateJ2 k h1 h2) (by rw [h3t]) ?_
        rw [h3n, lookup_upsert]
        simp only [Ne.symm (hXs k h1 h2), ↓reduceIte]
      have hliveS := liveAt_iff_of_leb_lookup S n' c.i jcv jy hSt hn't hn'lk
      have hlive' : ∀ c' z, (c', z) ∈ n'.liveAt c.i ↔
          (c' = 0 ∧ z = jy) ∨ ((c', z) ∈ (Nn stop).liveAt c.i ∧ c' ≠ 0 ∧ c' ≠ jcv) := by
        intro c' z
        rw [hliveS c' z]
        have e := hSlive c' z
        rw [hK0] at e
        constructor
        · rintro (h | ⟨h1, h2, h3⟩)
          · exact Or.inl h
          · exact Or.inr ⟨(e.mp ⟨h1, h2⟩).1, h2, h3⟩
        · rintro (h | ⟨h1, h2, h3⟩)
          · exact Or.inl h
          · exact Or.inr ⟨(e.mpr ⟨h1, h2⟩).1, h2, h3⟩
      have hmin' : ∀ c' z, (c', z) ∈ (Nn stop).liveAt c.i → c' = 0 ∨ jcv ≤ c' := by
        intro c' z hm
        by_cases hc : c' = 0
        · exact Or.inl hc
        · right
          have hm' := ((hSlive c' z).mpr ⟨hm, by rw [hK0]; exact hc⟩).1
          rw [KNode.liveAt_of_times _ c.i hSt] at hm'
          exact hmin c' z hm' hc
      refine writerWP_mono (hcollLeb seg stop w3 n' jcv jy hsD hbetween h3tw h3top' h3v' hfr hsn3
        (by rw [hn'l, hSleaf]) hn'w
        hn't hsl hK0 hj hj0 (fun c' z hm hc => by
          rcases hmin' c' z hm with h | h
          · exact absurd h hc
          · exact h) hlive' ?_ hfate3 hfateJ3
        ⟨S, hSR, hSF', htdL, lipL, e0L, hleb, hhtdL, hlipL⟩ hJ3 gh.1 gh.2) ?_
      · intro key' hkw
        have hV3 : wValue base w3 = wValue base w :=
          wValue_eq_of_taken base w w3 h3v' (fun y => ∃ k, stop < k ∧ k ≤ depth ∧ y = X k)
            (fun y hy => h3tw y (fun k h1 h2 he => hy ⟨k, h1, h2, he⟩))
            (fun y ⟨k, _, h2, he⟩ => by rw [he]; exact ⟨htk k h2, hnoval k h2⟩)
        have hagree : ∀ u, TReach (wNode c.p base w) c.i w.top.rootKey u → u ≠ X stop →
            (∀ i, stop < i → i ≤ depth → u ≠ X i) → wNode c.p base w3 u = wNode c.p base w u := by
          intro u _ hus hnc
          simp only [wNode, h3tw u hnc, hfr u hus hnc]
        have hsnw : wNode c.p base w3 (X stop) = some n' := by
          simp only [wNode, h3tw (X stop) hXs, htk stop (by omega), Bool.false_eq_true, ↓reduceIte, hsn3]
        unfold wGet
        rw [hV3, h3top']
        exact getFromR_up_leb (wNode c.p base w) (wNode c.p base w3) (wValue base w) c.i c.p.fuel hfuel
          w.top.rootKey X Nn K stop depth hsD pre cv rk hT hR hwf (hreach stop (by omega))
          (fun i h1 h2 => by simp only [wNode, htk i h2, Bool.false_eq_true, ↓reduceIte, hlk i h2])
          (fun i h1 h2 => hlinkK i (by omega) h2) hone hleaf honly (fun i h1 h2 => hnoval i h2)
          (fun i h1 h2 he => by have := hdist i depth (by omega) (Nat.le_refl _) he; omega)
          hrk hcv hvisL huniq hagree n' jy jcv hK0 hsl hj hj0 hmin' hsnw (by rw [hn'l, hSleaf]; exact hsl)
          hlive' key' hkw
      · intro _ w4 h4
        simp only [writerWP_pure]
        exact h4
    have hK0' : (K (stop + 1) != 0) = true := by simpa using hK0
    simp only [hK0', ↓reduceIte, writerWP_bind]
    refine hbit (Or.inr hK0) _ ?_ ?_ ?_ ?_ hJw2 _ ?_
    rotate_left 4
    · intro w3 n' h3t h3top h3v hfr hsn3 hn'l hn'w hn't hlive' hread hf3 hf3J hst3 hJ3
      refine writerWP_mono (hcoll seg stop w3 n' hsD hbetween h3t h3top h3v hfr hsn3 hn'l hn'w hn't
        hlive' hread hf3 hf3J hst3 hJ3 gh.1 gh.2) ?_
      intro _ w4 h4
      simp only [writerWP_pure]
      exact h4
    all_goals rfl

end SIS.Tree
