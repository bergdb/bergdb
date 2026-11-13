/-
The upward delete with the take-back keeps the take-back's (B) (bergdb 024-12,
TP4; `TtReachedN`, TakeInvTree.lean). Prover cost's
`writerWP_deleteUpward_upT_get`, here with what becomes of the chain below the
stop node (`writerWP_deleteUpward_upT_getF`): each of its nodes is taken back or
keeps no klong of the transaction's time (`ChainFate`).
-/
import SIS.Tree.TakeInvCollapse
import SIS.Tree.WriterGetUpTake

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A node of the chain after the upward delete: taken back, or without a klong
of time t. -/
def ChainFate (t : Time) (v : W) (y : NodeId) : Prop :=
  v.taken.contains y = true ∨ ∃ S0, v.nodes.lookup y = some S0 ∧ Klong.time t ∉ S0.ks

theorem chainFate_frame (t : Time) (v v' : W) (y : NodeId) (h : ChainFate t v y)
    (ht : v'.taken = v.taken) (hl : v'.nodes.lookup y = v.nodes.lookup y) : ChainFate t v' y := by
  rcases h with h | ⟨S0, h1, h2⟩
  · left; rw [ht]; exact h
  · right; exact ⟨S0, by rw [hl]; exact h1, h2⟩

theorem retargetOr_wf_times (n S : KNode) (y : NodeId) (t : Time)
    (hS : S = n ∨ ∃ ti dst, S = { n with ks := retargetKlongs n.ks ti y dst })
    (hw : klongsWf n.ks = true) (ht : ∀ s, Klong.time s ∈ n.ks → s ≤ t) :
    klongsWf S.ks = true ∧ ∀ s, Klong.time s ∈ S.ks → s ≤ t := by
  rcases hS with rfl | ⟨ti, dst, rfl⟩
  · exact ⟨hw, ht⟩
  · exact ⟨by rw [klongsWf_retargetKlongs]; exact hw, KNode.retarget_times _ _ _ _ _ ht⟩

/-- cost's `writerWP_deleteUpward_upT_get`, each continuation also given that
every node of the chain is taken back or keeps no klong of the transaction's
time. -/
theorem writerWP_deleteUpward_upT_getF (c : Ctx) (base : View BVal) (X : Nat → NodeId)
    (Nn : Nat → KNode) (K : Nat → Nat) (depth cv : Nat) (pre : List Nat) (rk : NodeId)
    (w : W) (Q : W → Prop) (hdepth : 0 < depth) (hfuel : 1 ≤ c.p.fuel) (hpos : 0 < c.i)
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
    (hmerges : c.p.merges = false)
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
      WriterWP (collapseRoot (pre ++ [cv]) seg c.p.fuel) c w' (fun _ w'' => Q w''))
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
      Q w')
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
      WriterWP (collapseRoot (pre ++ [cv]) seg c.p.fuel) c w' (fun _ w'' => Q w'')) :
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
  generalize hw0 : ({ w with trail := "up.climb" :: w.trail } : W) = w0
  have h0n : w0.nodes = w.nodes := by rw [← hw0]
  have h0p : w0.path = w.path := by rw [← hw0]
  have h0t : w0.taken = w.taken := by rw [← hw0]
  have h0top : w0.top = w.top := by rw [← hw0]
  have h0v : w0.vals = w.vals := by rw [← hw0]
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
  let I : List Nat → W → Prop := fun rem v =>
    v.top = w0.top ∧ v.vals = w0.vals ∧ v.path = w0.path ∧
    (∀ y, (∀ k, stop < k → k ≤ depth → y ≠ X k) → v.taken.contains y = w0.taken.contains y) ∧
    (∀ y, y ≠ X stop → (∀ k, stop < k → k ≤ depth → y ≠ X k) → v.nodes.lookup y = w0.nodes.lookup y) ∧
    ∃ a0, rem = List.range' a0 (depth - stop - a0) ∧ a0 ≤ depth - stop ∧
      (∀ j, j < a0 → ChainFate c.i v (X (depth - j))) ∧
      (∀ j, a0 < j → j ≤ depth - stop → v.nodes.lookup (X (depth - j)) = some (Nn (depth - j))) ∧
      ∃ S, v.nodes.lookup (X (depth - a0)) = some S ∧
        (S = Nn (depth - a0) ∨ ∃ ti dst, S = { Nn (depth - a0) with
          ks := retargetKlongs (Nn (depth - a0)).ks ti (X (depth - a0 + 1)) dst })
  rw [writerWP_bind]
  refine writerWP_mono (writerWP_forIn_inv c I _ ?_ (List.range (depth - stop)) w0
    ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ _ _ => rfl, 0, by rw [List.range_eq_range']; rfl, Nat.zero_le _, fun j hj => absurd hj (Nat.not_lt_zero _),
      fun j _ hj => by rw [h0n]; exact hlk _ (by omega),
      Nn (depth - 0), by rw [h0n]; exact hlk _ (by omega), Or.inl rfl⟩) ?_
  · intro a rest v ⟨hvtop, hvv, hvp, hvt, hvn, a0, hrem, ha0, hfv, hexact, S, hSl, hS⟩
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
    · simp only [writerWP_bind]
      refine writerWP_pathNode_known (depth - a - 1) (X (depth - (a + 1))) c v
        (by rw [hvp, h0p, show depth - a - 1 = depth - (a + 1) by omega]; exact hp _ (by omega)) _ ?_
      refine writerWP_klongAt_known (depth - a) (K (depth - a)) (X (depth - a)) c v
        (by rw [hvp, h0p]; exact hk _ (by omega) (by omega)) _ ?_
      refine writerWP_mono (writerWP_takeBack_frame _ _ _ _ c v hpar) ?_
      rintro _ v2 ⟨h2t, h2top, h2v, h2p, h2n, n', h2l, hn'⟩
      simp only [writerWP_pure]
      refine ⟨by first | rfl | trivial, h2top.trans hvtop, h2v.trans hvv, h2p.trans hvp, fun y hy => ?_,
        fun y hys hy => ?_, a + 1, hrest, by omega, fun j hj => ?_, fun j h1 h2 => ?_, n', h2l, ?_⟩
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
      · rw [h2n _ (fun he => by have := hdist _ _ (by omega) (by omega) he; omega)]
        exact hexact j (by omega) h2
      · rw [show depth - (a + 1) + 1 = depth - a by omega]
        exact hn'
    · simp only [writerWP_bind]
      refine (writerWP_note_iff _ c v _).mpr ?_
      refine writerWP_mono (writerWP_and (writerWP_unlink_frameP _ _ c _ hSl)
        (writerWP_unlink_fate _ _ c _ hSl)) ?_
      rintro _ v2 ⟨⟨h2t, h2top, _, h2v, h2p, _, h2l⟩, ⟨_, _, _, h2x, _⟩⟩
      simp only [writerWP_pure]
      refine ⟨by first | rfl | trivial, h2top.trans hvtop, h2v.trans hvv, h2p.trans hvp,
        fun y hy => by rw [h2t]; exact hvt y hy, fun y hys hy => ?_, a + 1, hrest, by omega,
        fun j hj => ?_, fun j h1 h2 => ?_, Nn (depth - (a + 1)), ?_, Or.inl rfl⟩
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
      · rw [h2l _ (fun he => by have := hdist _ _ (by omega) (by omega) he; omega)]
        exact hexact j (by omega) h2
      · rw [h2l _ (fun he => by have := hdist _ _ (by omega) (by omega) he; omega)]
        exact hpar
  rintro _ w2 ⟨h2top, h2v, h2p, h2t, h2n, a0, hrem, ha0, hfv2, _, S, hSl, hS⟩
  have ha0' : a0 = depth - stop := by
    rcases h : depth - stop - a0 with _ | m
    · omega
    · rw [h, List.range'_succ] at hrem; cases hrem
  subst ha0'
  rw [show depth - (depth - stop) = stop by omega] at hSl hS
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
      ∀ (v : W), v.nodes = w2.nodes → v.taken = w2.taken → v.top = w2.top → v.vals = w2.vals →
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
        (∀ k, stop < k → k ≤ depth → ChainFate c.i w3 (X k)) → post w3) →
      WriterWP (appendDeleteKlong (X stop) stop (K (stop + 1))) c v (fun _ w3 => post w3) := by
    intro hkind v hvn hvt hvtop hvv post hpost
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
    refine writerWP_mono (writerWP_appendDeleteKlong_room_frame (X stop) stop (K (stop + 1)) S
      c v (by rw [hvn]; exact hSl) hSt hSwf hneS' hroom' hd1' hd2') ?_
    rintro _ w3 ⟨h3t, h3top, h3v, _, _, _, n', h3n, hn'l, hn'w, hn't, hn'lk⟩
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
    refine hpost w3 n' h3tw h3top' h3v' hfr hsn3 (by rw [hn'l, hSleaf]) hn'w hn't hlive' ?_ hfate3
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
    refine hbit (Or.inl hsl) _ ?_ ?_ ?_ ?_ _ ?_
    rotate_left 4
    · intro w3 n' h3t h3top h3v hfr hsn3 hn'l hn'w hn't hlive' hread hf3
      unfold afterDelete
      simp only [writerWP_bind, writerWP_read, hmerges, Bool.false_eq_true, ↓reduceIte, writerWP_pure]
      exact hleafQ stop w3 n' hsD hbetween h3t h3top h3v hfr hsn3 hn'l hn'w hn't hlive' hread hf3
    all_goals rfl
  | false =>
    have hsl' : S.leaf = false := hSleaf.trans hsl
    simp only [hsl', Bool.false_eq_true, ↓reduceIte]
    split
    · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
    by_cases hK0 : K (stop + 1) = 0
    · -- LE-b
      have hK0' : (K (stop + 1) != 0) = false := by simp [hK0]
      simp only [hK0', Bool.false_eq_true, ↓reduceIte, writerWP_bind, hmerges]
      obtain ⟨hroomL, hdeadL⟩ := hlebRoom hsl hK0
      have hroomL' : S.size + 3 ≤ c.p.M := by rw [KNode.size_of_shapeOf hSsh]; exact hroomL
      have hdeadL' : ∀ b1 b2 e jcv jy, deadOver c.p (lebNode S c.i b1 b2 e jcv jy) = false := by
        intro b1 b2 e jcv jy
        rw [deadOver_of_shapeOf c.p (lebNode_shapeOf hSsh _ _ _ _ _ _)]
        exact hdeadL _ _ _ _ _
      refine writerWP_mono (writerWP_emptyKeyNext_room_frame (X stop) stop S c w2 hSl hSwf hSt
        hroomL' hdeadL') ?_
      rintro _ w3 ⟨h3t, h3top, h3v, _, _, _, n', jcv, jy, h3n, hn'l, hn'w, hn't, hjS, hj0, hmin, hn'lk⟩
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
          · exact h) hlive' ?_ hfate3) ?_
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
    simp only [hK0', ↓reduceIte, writerWP_bind, hmerges, Bool.false_eq_true]
    refine hbit (Or.inr hK0) _ ?_ ?_ ?_ ?_ _ ?_
    rotate_left 4
    · intro w3 n' h3t h3top h3v hfr hsn3 hn'l hn'w hn't hlive' hread hf3
      refine writerWP_mono (hcoll seg stop w3 n' hsD hbetween h3t h3top h3v hfr hsn3 hn'l hn'w hn't
        hlive' hread hf3) ?_
      intro _ w4 h4
      simp only [writerWP_pure]
      exact h4
    all_goals rfl


/-! ## At node-map level -/

/-- The upward delete at node-map level: a node reached before is reached after,
or is of the chain below the stop node, or no node (a value of the emptied
leaf). The stop node keeps every live klong but the one to the chain, perhaps
moved to another compare value. -/
theorem reach_up (N1 N2 : NodeId → Option KNode) (t : Time) (r : NodeId) (X : Nat → NodeId)
    (Nn : Nat → KNode) (stop depth : Nat) (hsD : stop < depth)
    (hN : ∀ i, stop ≤ i → i ≤ depth → N1 (X i) = some (Nn i))
    (hone : ∀ i, stop < i → i < depth → ∀ c z, (c, z) ∈ (Nn i).liveAt t → z = X (i + 1))
    (hkids : ∀ c z, (c, z) ∈ (Nn depth).liveAt t → N1 z = none)
    (sn' : KNode) (hsn : N2 (X stop) = some sn')
    (hkeep : ∀ c z, (c, z) ∈ (Nn stop).liveAt t → z ≠ X (stop + 1) → ∃ c', (c', z) ∈ sn'.liveAt t)
    (hagree : ∀ u, u ≠ X stop → (∀ k, stop < k → k ≤ depth → u ≠ X k) → N2 u = N1 u) :
    ∀ u, TReach N1 t r u →
      TReach N2 t r u ∨ (∃ k, stop < k ∧ k ≤ depth ∧ u = X k) ∨ N1 u = none := by
  intro u hu
  induction hu with
  | root => exact Or.inl TReach.root
  | @link a c u ha hl ih =>
    obtain ⟨an, han, hau⟩ := hl
    by_cases hac : ∃ k, stop < k ∧ k ≤ depth ∧ a = X k
    · obtain ⟨k, hk1, hk2, hka⟩ := hac
      rw [hka, hN k (by omega) hk2] at han
      cases han
      rcases Nat.lt_or_ge k depth with hkd | hkd
      · exact Or.inr (Or.inl ⟨k + 1, by omega, by omega, hone k hk1 hkd c u hau⟩)
      · have hkd' : k = depth := by omega
        rw [hkd'] at hau
        exact Or.inr (Or.inr (hkids c u hau))
    · have haR : TReach N2 t r a := by
        rcases ih with h | h | h
        · exact h
        · exact absurd h hac
        · rw [han] at h; cases h
      have hnc : ∀ k, stop < k → k ≤ depth → a ≠ X k := fun k h1 h2 he => hac ⟨k, h1, h2, he⟩
      by_cases has : a = X stop
      · rw [has, hN stop (Nat.le_refl _) (by omega)] at han
        cases han
        by_cases hux : u = X (stop + 1)
        · exact Or.inr (Or.inl ⟨stop + 1, by omega, by omega, hux⟩)
        · obtain ⟨c', hc'⟩ := hkeep c u hau hux
          rw [has] at haR
          exact Or.inl (TReach.link haR ⟨sn', hsn, hc'⟩)
      · exact Or.inl (TReach.link haR ⟨an, by rw [hagree a has hnc]; exact han, hau⟩)

/-- (B) after the upward delete, before root collapse: every node of the chain
taken back or without a klong of time t. -/
theorem ttReachedN_up (N1 N2 : NodeId → Option KNode) (t : Time) (r : NodeId) (X : Nat → NodeId)
    (Nn : Nat → KNode) (stop depth : Nat) (hsD : stop < depth)
    (hN : ∀ i, stop ≤ i → i ≤ depth → N1 (X i) = some (Nn i))
    (hone : ∀ i, stop < i → i < depth → ∀ c z, (c, z) ∈ (Nn i).liveAt t → z = X (i + 1))
    (hkids : ∀ c z, (c, z) ∈ (Nn depth).liveAt t → N1 z = none)
    (sn' : KNode) (hsn : N2 (X stop) = some sn')
    (hkeep : ∀ c z, (c, z) ∈ (Nn stop).liveAt t → z ≠ X (stop + 1) → ∃ c', (c', z) ∈ sn'.liveAt t)
    (hagree : ∀ u, u ≠ X stop → (∀ k, stop < k → k ≤ depth → u ≠ X k) → N2 u = N1 u)
    (hXs : ∀ k, stop < k → k ≤ depth → X stop ≠ X k)
    (hstopR : TReach N1 t r (X stop))
    (hfate : ∀ k, stop < k → k ≤ depth → ∀ un, N2 (X k) = some un → Klong.time t ∉ un.ks)
    (hL : TtReachedN N1 t r) : TtReachedN N2 t r := by
  have hR := reach_up N1 N2 t r X Nn stop depth hsD hN hone hkids sn' hsn hkeep hagree
  intro u un hu hm
  by_cases huc : ∃ k, stop < k ∧ k ≤ depth ∧ u = X k
  · obtain ⟨k, h1, h2, hk⟩ := huc
    rw [hk] at hu
    exact absurd hm (hfate k h1 h2 un hu)
  · have hnc : ∀ k, stop < k → k ≤ depth → u ≠ X k := fun k h1 h2 he => huc ⟨k, h1, h2, he⟩
    by_cases hus : u = X stop
    · rw [hus]
      rcases hR (X stop) hstopR with h | h | h
      · exact h
      · obtain ⟨k, h1, h2, he⟩ := h
        exact absurd he (hXs k h1 h2)
      · rw [hN stop (Nat.le_refl _) (by omega)] at h; cases h
    · rw [hagree u hus hnc] at hu
      rcases hR u (hL u un hu hm) with h | h | h
      · exact h
      · exact absurd h huc
      · rw [hu] at h; cases h

/-! ## The upward delete with the take-back -/

/-- The upward delete with the take-back keeps (A) and (B) in `TtReachedN`'s
form, root collapse at any segment included, given room in the segment leaf
above each segment root that is replaced, and the emptied leaf's live klongs to
no node (to values). -/
theorem takeInv_deleteUpward_upT (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth cv : Nat) (pre : List Nat)
    (rk : NodeId) (w : W) (hdepth : 0 < depth) (hfuel : 1 ≤ c.p.fuel) (hpos : 0 < c.i)
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
    (hstopOK : ∀ s, s < depth → (∀ i, s < i → i < depth →
        (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true) →
      (((Nn s).leaf = true ∨ K (s + 1) ≠ 0) → (Nn s).size + 1 < c.p.M ∧
        deadOver c.p ((Nn s).setAt ((Nn s).size - 1)
          (.del (bitsUnion (Nn s).lastBitmap ((Nn s).bitsOf (K (s + 1)))))) = false ∧
        deadOver c.p ((Nn s).add c.i (.del (bitsUnion (Nn s).lastBitmap ((Nn s).bitsOf (K (s + 1)))))) =
          false) ∧
      ((Nn s).leaf = false → K (s + 1) = 0 → (Nn s).size + 3 ≤ c.p.M ∧
        ∀ b1 b2 e jcv jy, deadOver c.p (lebNode (Nn s) c.i b1 b2 e jcv jy) = false))
    (hmerges : c.p.merges = false)
    (hkids : ∀ c' z, (c', z) ∈ (Nn depth).liveAt c.i → wNode c.p base w z = none)
    (hTt : TtReachedN (wNode c.p base w) c.i w.top.rootKey)
    (hroom : ∀ w0 v x n leaf ln k, CollGetInv c base w0 v → TakeJ c base v → SegDesc c base x v →
      v.nodes.lookup x = some n → n.leaf = false → n.firstTime ≠ some c.i →
      TReach (wNode c.p base v) c.i v.top.rootKey leaf → v.nodes.lookup leaf = some ln →
      ln.leaf = true → (k, x) ∈ ln.liveAt c.i →
      ln.size + 1 + 1 ≤ c.p.M ∧ ∀ y, deadOver c.p (ln.add c.i (.key k y)) = false) :
    WriterWP (deleteUpward (X depth) depth cv (pre ++ [cv])) c w (fun _ w' =>
      (∀ y, TReach (wNode c.p base w') c.i w'.top.rootKey y → w'.taken.contains y = false) ∧
      TtReachedN (wNode c.p base w') c.i w'.top.rootKey) := by
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
  apply writerWP_deleteUpward_upT_getF c base X Nn K depth cv pre rk w _ hdepth hfuel hpos hp hk hlk htk
    htimes hdist hne hall hleaf hT hR hwf hreach hlinkK (fun i hi => hnovalAll _ _ (hN i hi))
    hrk hcv hvisL huniq hstopOK hmerges
  · intro seg stop w' sn' hsD hbetween ht htop hv hnodes hsn' hsl' hsw' hst' hlive' _ hfate
    have hI := hpost stop w' sn' id hsD ht htop hv hnodes hsn' hsl' hsw' hst'
      (fun c' z h => ⟨c', ((hlive' c' z).mp h).1, ((hlive' c' z).mp h).2, rfl⟩)
    have hJ : TakeJ c base w' := hafter stop w' sn' hsD hbetween ht htop hnodes hsn'
      (hkeepBit stop sn' hsD hlive') hfate
    refine writerWP_mono (writerWP_collapseRoot_take (pre ++ [cv]) seg c base hvc w' hpos (hroom w')
      c.p.fuel w' hI hJ) ?_
    intro _ w'' ⟨hI'', hJ''⟩
    exact ⟨hI''.1.2.1, hJ''⟩
  · intro stop w' sn' hsD hbetween ht htop hv hnodes hsn' hsl' hsw' hst' hlive' _ hfate
    have hI := hpost stop w' sn' id hsD ht htop hv hnodes hsn' hsl' hsw' hst'
      (fun c' z h => ⟨c', ((hlive' c' z).mp h).1, ((hlive' c' z).mp h).2, rfl⟩)
    exact ⟨hI.1.2.1, hafter stop w' sn' hsD hbetween ht htop hnodes hsn'
      (hkeepBit stop sn' hsD hlive') hfate⟩
  · intro seg stop w' sn' jcv jy hsD hbetween ht htop hv hnodes hsn' hsl' hsw' hst' _ hK0 hj hj0 _
      hlive' _ hfate
    have hI := hpost stop w' sn' (fun c' => if c' = jcv then 0 else c') hsD ht htop hv
      hnodes hsn' hsl' hsw' hst' (by
        intro c' z h
        rcases (hlive' c' z).mp h with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
        · refine ⟨jcv, by rw [h2]; exact hj, by omega, ?_⟩
          simp [h1]
        · exact ⟨c', h1, by omega, by simp [h3]⟩)
    have hkeep : ∀ c' z, (c', z) ∈ (Nn stop).liveAt c.i → z ≠ X (stop + 1) →
        ∃ c'', (c'', z) ∈ sn'.liveAt c.i := by
      intro c' z hm hz
      have hl := hlinkK (stop + 1) (by omega) (by omega)
      rw [show stop + 1 - 1 = stop by omega, hK0] at hl
      have hc0 : c' ≠ 0 := fun h => hz (by rw [h] at hm; exact (KNode.liveAt_fun _ _ _ _ _ hl hm).symm)
      by_cases hcj : c' = jcv
      · rw [hcj] at hm
        have hzy : jy = z := KNode.liveAt_fun _ _ _ _ _ hj hm
        exact ⟨0, (hlive' 0 z).mpr (Or.inl ⟨rfl, hzy.symm⟩)⟩
      · exact ⟨c', (hlive' c' z).mpr (Or.inr ⟨hm, hc0, hcj⟩)⟩
    have hJ : TakeJ c base w' := hafter stop w' sn' hsD hbetween ht htop hnodes hsn' hkeep hfate
    refine writerWP_mono (writerWP_collapseRoot_take (pre ++ [cv]) seg c base hvc w' hpos (hroom w')
      c.p.fuel w' hI hJ) ?_
    intro _ w'' ⟨hI'', hJ''⟩
    exact ⟨hI''.1.2.1, hJ''⟩

end SIS.Tree
