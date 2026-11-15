/-
The dead klongs' bound through the delete's cases (bergdb 024-12, section 1,
`d4`'s plan of 2026-11-15, step 4): the route lemmas of the reading with `DW`
carried beside `DelInv` to `afterDelete`, the merges' loop and root collapse
(`writerWP_del_emptyRoomMKD`: the upward loop's invariant J with `DW`).
-/
import SIS.Tree.DeadMergeLoop
import SIS.Tree.HeightsFillHolder
import SIS.Tree.DelStepsFullH
import SIS.Tree.DelStepsEmptyRoot

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

set_option maxHeartbeats 3200000 in
/-- `writerWP_del_emptyRoomMK` with `DW`: the upward loop keeps `DW` beside the
books, and `afterDelete`, the merges' loop and root collapse are given it. -/
theorem writerWP_del_emptyRoomMKDG (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
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
      n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = true ∧ UpRoom c base w L n)
    (hm : c.p.merges = true) (hpos : 0 < c.i) (hth : 2 ≤ c.p.theta ∨ c.p.theta = 0)
    (hdw : DW c base w)
    (hA : ∀ g h v, DelInv c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK v → DW c base v →
      WriterWP (afterDelete (pre ++ [cv]) g h) c v (fun _ v' => DW c base v'))
    (Imid : W → Prop)
    (hMU : ∀ g h merged v, DelInv c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK v → DW c base v →
      WriterWP (mergeUp (pre ++ [cv]) g c.p.fuel h merged) c v (fun _ v' => Imid v'))
    (hCR : ∀ seg v, Imid v →
      WriterWP (collapseRoot (pre ++ [cv]) seg c.p.fuel) c v (fun _ v' => DW c base v'))
    (Post : W → Prop) (hfresh : ∀ v, Post v → WriterWP fresh c v (fun _ v' => Post v'))
    (hpost : ∀ v, DW c base v → Post v) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' => Post w') := by
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hJ0 : KdJ c B top0 KO BK w := ⟨hbook, hb0, hi0⟩
  refine writerWP_del_toLeafMK c base hvc pre cv rk w (KdJ c B top0 KO BK) hJ0
    (fun s f x v hJ hx => kdJ_descendLte c base B top0 hB KO BK hvB hk s f x v hJ hx)
    (fun s x L n v hJ hL hlk hkm => kdJ_pathAdd c base B top0 hB KO BK hvB s x L n v hJ hL hlk hkm)
    (kdJ_start c base B top0 hB KO BK hvB w hJ0) hrk (hI.pathUntaken _) hI.wf Post hfresh ?_
  intro L n P w3 hL hn hnl hr03 hb3 hlk3 hp3' hlinkP hXD hlkX
  obtain ⟨hne, hall, hup⟩ := hleafC L n hL hn hnl
  obtain ⟨hdepth, hstopOK⟩ := hup P hlinkP hXD
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
  refine writerWP_deleteUpward_upT_getJMBK c base (fun i => nodeAt w.top.rootKey P i)
    (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
    (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length cv pre rk (madeForBound w3) w3 Post
    (fun v => KdJP c B top0 KO BK w3.path v ∧ DW c base v) ⟨⟨hb3, rfl⟩, dw_of_wNode hr03.1 hdw⟩
    (fun s v hJ => ⟨kdJP_note c base B top0 hB KO BK hvB hk _ s v hJ.1, dw_same rfl rfl hJ.2⟩)
    (fun x q k v hJ hx => writerWP_and (kdJP_takeBack c base B top0 hB KO BK hvB hk _ x q k v hJ.1 hx)
      (dw_takeBack base x q k c v hvc hth hJ.2))
    (fun x v hJ => writerWP_and (kdJP_unlink c base B top0 hB KO BK hvB hk _ x v hJ.1)
      (dw_unlink base x c v hvc hth hJ.2))
    (fun x d k v hJ hx => writerWP_and (kdJP_appendDeleteKlong c base B top0 hB KO BK hvB hk _ x d k v hJ.1 hx)
      (dw_appendDeleteKlong base x d k c v hvc hth hJ.2))
    (fun x d v xn hJ hx hl hxl => writerWP_and (kdJP_emptyKeyNext c base B top0 hB KO BK hvB hk _ x d v xn hJ.1 hx hl hxl)
      (dw_emptyKeyNext base x d c v hvc hth hJ.2))
    (madeFor_lt_bound w3) hdepth hfuel hpos hpX hpK hlkX htk3 (fun i hi => hTimesR3 _ _ (hreach3 i hi) (hN3 i hi))
    hdistP (by rw [hNnD]; exact hne) (by rw [hNnD]; exact hall) (by rw [hNnD]; exact hnl) hT3 hR3 hwf3 hreach3
    hlinkK (fun i hi => hnovalAll3 _ _ (hN3 i hi)) (by rw [hr03.1, hr03.2.1]; exact hrk)
    (keyWf_last_notin pre cv hkey) (by rw [hr03.1, hXD]; exact hL)
    (by rw [hr03.1, hr03.2.1]; exact hI.keyUniq pre cv rk hkey hrk) hstopOK hm ?_ ?_ ?_
  · intro seg stop w' sn' hsD hbetween ht htop hv hnodes hsn' hsl' hsw' hst' hlive' hread _ _ _ hb' gs hs
    obtain ⟨hagree, hsnw⟩ := hfr stop w' sn' hsD ht hnodes hsn'
    have hRO' : RangeOrder (wNode c.p base w') c.i w'.top.rootKey := by
      rw [htop]
      exact rangeOrder_up_bitmap (wNode c.p base w3) (wNode c.p base w') c.i w3.top.rootKey _ _ _ stop
        P.length hsD hR3 hT3 (hreach3 stop (by omega)) (fun i _ h2 => hN3 i h2)
        (fun i h1 h2 => hlinkK i (by omega) h2) (fun i i' _ h2 _ h4 he => hdistP i i' h2 h4 he)
        hagree sn' hsnw hsl' (fun c' z h => (hlive' c' z).mp h)
    have hDv := hD stop w' sn' id hsD ht htop hv hnodes hsn' hsl' hsw' hst'
      (fun c' z h => ⟨c', ((hlive' c' z).mp h).1, ((hlive' c' z).mp h).2, rfl⟩) hRO' hb'.1.1.1 hread
    refine writerWP_mono (hMU gs hs false w' ⟨hDv, hb'.1.1.2.1, hb'.1.1.2.2⟩ hb'.2) ?_
    intro _ w1 hD1
    exact writerWP_mono (hCR seg w1 hD1) (fun _ w2 hD2 => hpost w2 hD2)
  · intro stop w' sn' hsD hbetween ht htop hv hnodes hsn' hsl' hsw' hst' hlive' hread _ _ _ hb' gs hs
    obtain ⟨hagree, hsnw⟩ := hfr stop w' sn' hsD ht hnodes hsn'
    have hRO' : RangeOrder (wNode c.p base w') c.i w'.top.rootKey := by
      rw [htop]
      exact rangeOrder_up_bitmap (wNode c.p base w3) (wNode c.p base w') c.i w3.top.rootKey _ _ _ stop
        P.length hsD hR3 hT3 (hreach3 stop (by omega)) (fun i _ h2 => hN3 i h2)
        (fun i h1 h2 => hlinkK i (by omega) h2) (fun i i' _ h2 _ h4 he => hdistP i i' h2 h4 he)
        hagree sn' hsnw hsl' (fun c' z h => (hlive' c' z).mp h)
    have hDv := hD stop w' sn' id hsD ht htop hv hnodes hsn' hsl' hsw' hst'
      (fun c' z h => ⟨c', ((hlive' c' z).mp h).1, ((hlive' c' z).mp h).2, rfl⟩) hRO' hb'.1.1.1 hread
    exact writerWP_mono (hA gs hs w' ⟨hDv, hb'.1.1.2.1, hb'.1.1.2.2⟩ hb'.2) (fun _ w2 hD2 => hpost w2 hD2)
  · intro seg stop w' sn' jcv jy hsD hbetween ht htop hv hnodes hsn' hsl' hsw' hst' hsl hK0 hj hj0 hmin
      hlive' hread _ _ _ hb' gs hs
    obtain ⟨hagree, hsnw⟩ := hfr stop w' sn' hsD ht hnodes hsn'
    have hRO' : RangeOrder (wNode c.p base w') c.i w'.top.rootKey := by
      rw [htop]
      exact rangeOrder_up_leb (wNode c.p base w3) (wNode c.p base w') c.i w3.top.rootKey _ _ _ stop
        P.length hsD hR3 hT3 (hreach3 stop (by omega)) (fun i _ h2 => hN3 i h2)
        (fun i h1 h2 => hlinkK i (by omega) h2) (fun i i' _ h2 _ h4 he => hdistP i i' h2 h4 he)
        hagree sn' hsnw hsl hsl' hK0 jcv jy hj hj0 hmin hlive'
    have hDv := hD stop w' sn' (fun c' => if c' = jcv then 0 else c') hsD ht htop hv hnodes hsn' hsl' hsw' hst'
      (by
        intro c' z h
        rcases (hlive' c' z).mp h with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
        · refine ⟨jcv, by rw [h2]; exact hj, by omega, ?_⟩
          simp [h1]
        · exact ⟨c', h1, by omega, by simp [h3]⟩) hRO' hb'.1.1.1 hread
    refine writerWP_mono (hMU gs hs false w' ⟨hDv, hb'.1.1.2.1, hb'.1.1.2.2⟩ hb'.2) ?_
    intro _ w1 hD1
    exact writerWP_mono (hCR seg w1 hD1) (fun _ w2 hD2 => hpost w2 hD2)

/-- The walk with the merges' loop kept in `DelInv` and `DW`: `writerWP_del_emptyRoomMKDG`. -/
theorem writerWP_del_emptyRoomMKD (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
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
      n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = true ∧ UpRoom c base w L n)
    (hm : c.p.merges = true) (hpos : 0 < c.i) (hth : 2 ≤ c.p.theta ∨ c.p.theta = 0)
    (hdw : DW c base w)
    (hA : ∀ g h v, DelInv c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK v → DW c base v →
      WriterWP (afterDelete (pre ++ [cv]) g h) c v (fun _ v' => DW c base v'))
    (hMU : ∀ g h merged v, DelInv c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK v → DW c base v →
      WriterWP (mergeUp (pre ++ [cv]) g c.p.fuel h merged) c v
        (fun _ v' => DelInv c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK v' ∧ DW c base v'))
    (hCR : ∀ seg v, DW c base v →
      WriterWP (collapseRoot (pre ++ [cv]) seg c.p.fuel) c v (fun _ v' => DW c base v'))
    (Post : W → Prop) (hfresh : ∀ v, Post v → WriterWP fresh c v (fun _ v' => Post v'))
    (hpost : ∀ v, DW c base v → Post v) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' => Post w') :=
  writerWP_del_emptyRoomMKDG c base hvc pre cv rk w B top0 hB hbook KO BK hvB hk hb0 hi0 hI hRO hF
    hICE hkey hrk hleafC hm hpos hth hdw hA _ hMU (fun seg v hv => hCR seg v hv.2) Post hfresh
    hpost

set_option maxHeartbeats 3200000 in
/-- `writerWP_del_emptyAnyMKLHGJ` with `DW`: the upward loop keeps `DW` beside its
invariant, the stop node's step keeps it (`dw_appendDeleteKlong`), and
`afterDelete`, the merges' loop and root collapse are given it. -/
theorem writerWP_del_emptyAnyMKLHGJDG (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
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
    (H : NodeId → Nat → Prop) (hC : UpCascOKHGJ c base KO BK H)
    (hLC : LiveCounts c.p (wNode c.p base w) c.i w.top.rootKey)
    (hvo : ViewHtOK H BK c) (hkw : ViewKlongsWf c.p c.view) (hhi : HtInv H BK c w) (hwfw : WriterKlongsWf w)
    (hub : UntakenBound (c.p.fuel - 1) w)
    (hsa2 : 2 ≤ c.p.splitAbove) (hICEk : ICEFromKinds c base KO BK)
    (hm : c.p.merges = true) (hpos : 0 < c.i)
    (hTJ2 : TakeJ2 c base B w) (hTA : TakenAbove B w) (hMF : ∀ x o, w.madeFor.lookup x = some o → o < B)
    (hth : 2 ≤ c.p.theta ∨ c.p.theta = 0) (hdw : DW c base w)
    (hA : ∀ g h v, DelInv c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK v → DW c base v →
      WriterWP (afterDelete (pre ++ [cv]) g h) c v (fun _ v' => DW c base v'))
    (Imid : W → Prop)
    (hMU : ∀ g h merged v, DelInv c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK v → DW c base v →
      WriterWP (mergeUp (pre ++ [cv]) g c.p.fuel h merged) c v (fun _ v' => Imid v'))
    (hCR : ∀ seg v, Imid v →
      WriterWP (collapseRoot (pre ++ [cv]) seg c.p.fuel) c v (fun _ v' => DW c base v'))
    (Post : W → Prop) (hfresh : ∀ v, Post v → WriterWP fresh c v (fun _ v' => Post v'))
    (hpost : ∀ v, DW c base v → Post v) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' => Post w') := by
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hJ0 : KdJ c B top0 KO BK w := ⟨hbook, hb0, hi0⟩
  refine writerWP_del_toLeafMKH c base hvc pre cv rk w
    (fun v => KdHtJ c B top0 KO BK H v ∧ v.madeFor = w.madeFor)
    (fun s f x v hJ hx => writerWP_mono (writerWP_and
      (kdhtJ_descendLte base top0 hB KO BK hvB hk hvo hkw s f x v hJ.1 hx)
      (writerWP_descendLte_madeFor s c f x v)) (fun _ v' h => ⟨h.1, h.2.trans hJ.2⟩))
    (fun s fd L n v hJ hL hlk hleaf hfd =>
      ⟨kdhtJ_pathAdd base top0 hB KO BK hvB hvo s fd L n v hJ.1 hL hlk hleaf hfd, hJ.2⟩)
    ⟨kdhtJ_start base top0 hB KO BK hvB hvo w hJ0 hhi hwfw hub, rfl⟩ hrk (hI.pathUntaken _) hI.wf Post hfresh ?_
  intro L n P w3 hL hn hnl hr03 hJ3 hlk3 hp3' hlinkP hXD hlkX
  have hb3H := hJ3.1
  have hb3 := hb3H.1
  have hMF3 : ∀ x o, w3.madeFor.lookup x = some o → o < B := by rw [hJ3.2]; exact hMF
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
    (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length cv pre B w3 Post
    (fun v => KdJP c B top0 KO BK w3.path v ∧ v.gh = w3.gh ∧ DW c base v)
    ⟨⟨hb3, rfl⟩, rfl, dw_of_wNode hr03.1 hdw⟩
    (fun s v hJ => ⟨kdJP_note c base B top0 hB KO BK hvB hk _ s v hJ.1, hJ.2.1, dw_same rfl rfl hJ.2.2⟩)
    (fun x q k v hJ hx hq => writerWP_mono (writerWP_and (writerWP_and
      (kdJP_takeBack c base B top0 hB KO BK hvB hk _ x q k v hJ.1 hx) (writerWP_takeBack_gh x q k c v hq))
      (dw_takeBack base x q k c v hvc hth hJ.2.2))
      (fun _ v' h => ⟨h.1.1, h.1.2.trans hJ.2.1, h.2⟩))
    (fun x v hJ hx => writerWP_mono (writerWP_and (writerWP_and
      (kdJP_unlink c base B top0 hB KO BK hvB hk _ x v hJ.1) (writerWP_unlink_gh x c v hx))
      (dw_unlink base x c v hvc hth hJ.2.2))
      (fun _ v' h => ⟨h.1.1, h.1.2.trans hJ.2.1, h.2⟩))
    hMF3 hdepth hpos hpX hpK hlkX htk3 (fun i hi => hTimesR3 _ _ (hreach3 i hi) (hN3 i hi))
    hdistP hne' hall' hwf3 hreach3 hm ?_ ?_ ?_
  · -- a segment leaf as the stop node
    intro stop w2 S hsD hbetween hLE hJ2G hsl gs hs
    obtain ⟨hJ2, hgh2, hdw2⟩ := hJ2G
    have hJv := kdJP_note c base B top0 hB KO BK hvB hk _ "up.stop-at-segment-leaf" w2 hJ2
    by_cases hDR : DelRoom c (((P[stop + 1 - 1]?).bind (·.1)).getD 0) S
    · refine writerWP_mono (writerWP_and (writerWP_upStop_bitmapD c base (fun i => nodeAt w.top.rootKey P i)
        (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
        (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length cv pre rk B w3 hfuel hlkX htk3
        (fun i hi => hTimesR3 _ _ (hreach3 i hi) (hN3 i hi)) hdistP hall' hnl' hT3 hR3 hwf3 hreach3 hlinkK
        (fun i hi => hnovalAll3 _ _ (hN3 i hi)) hrk3 (keyWf_last_notin pre cv hkey) hvis3 huniq3
        stop w2 S hsD hbetween hLE (Or.inl hsl) hDR ({ w2 with trail := "up.stop-at-segment-leaf" :: w2.trail } : W)
        rfl rfl rfl rfl
        (fun w' => PutBook c B top0 w' → DelInvF c base w (pre ++ [cv]) (c.p.fuel + 1) w') ?_)
        (writerWP_and (kdJP_appendDeleteKlong c base B top0 hB KO BK hvB hk _ _ stop _ _ hJv (hpX stop (by omega)))
          (dw_appendDeleteKlong base _ stop _ c _ hvc hth (dw_same rfl rfl hdw2)))) ?_
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
      · rintro _ w' ⟨hDv, hJ', hdw'⟩
        exact writerWP_mono (hA gs hs w' ⟨hDv hJ'.1.1, hJ'.1.2.1, hJ'.1.2.2⟩ hdw') (fun _ w2 hD2 => hpost w2 hD2)
    · exact writerWP_mono (hC w w3 B top0 pre cv rk (fun i => nodeAt w.top.rootKey P i)
        (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
        (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length stop w2 _ S hm hLC hb3H hlen3 hgh2 hsa2 hvB hk hICEk (by simp [nodeAt])
        hB hI hRO hF hICE hr03 hkey hrk
        hvisw hpX hpK hlkX hXNw hlinkK hne' hall' hnl' hdepth hsD hbetween hLE (Or.inr ⟨_, rfl⟩) hJv
        (Or.inl hsl) hDR hTJ2 hTA |> writerWP_and <| dw_appendDeleteKlong base _ stop _ c _ hvc hth
          (dw_same rfl rfl hdw2))
        (fun _ w' hD' => writerWP_mono (hA gs hs w' hD'.1 hD'.2) (fun _ w2 hD2 => hpost w2 hD2))
  · -- an inner stop node, its klong to the chain not the empty key's
    intro seg stop w2 S hsD hbetween hLE hJ2G hsl hK0 gs hs
    obtain ⟨hJ2, hgh2, hdw2⟩ := hJ2G
    by_cases hDR : DelRoom c (((P[stop + 1 - 1]?).bind (·.1)).getD 0) S
    · refine writerWP_mono (writerWP_and (writerWP_upStop_bitmapD c base (fun i => nodeAt w.top.rootKey P i)
        (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
        (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length cv pre rk B w3 hfuel hlkX htk3
        (fun i hi => hTimesR3 _ _ (hreach3 i hi) (hN3 i hi)) hdistP hall' hnl' hT3 hR3 hwf3 hreach3 hlinkK
        (fun i hi => hnovalAll3 _ _ (hN3 i hi)) hrk3 (keyWf_last_notin pre cv hkey) hvis3 huniq3
        stop w2 S hsD hbetween hLE (Or.inr hK0) hDR _ rfl rfl rfl rfl
        (fun w' => PutBook c B top0 w' → DelInvF c base w (pre ++ [cv]) (c.p.fuel + 1) w') ?_)
        (writerWP_and (kdJP_appendDeleteKlong c base B top0 hB KO BK hvB hk _ _ stop _ _ hJ2 (hpX stop (by omega)))
          (dw_appendDeleteKlong base _ stop _ c _ hvc hth hdw2))) ?_
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
      · rintro _ w' ⟨hDv, hJ', hdw'⟩
        refine writerWP_mono (hMU gs hs false w' ⟨hDv hJ'.1.1, hJ'.1.2.1, hJ'.1.2.2⟩ hdw') ?_
        intro _ w1 hD1
        exact writerWP_mono (hCR seg w1 hD1) (fun _ w2 hD2 => hpost w2 hD2)
    · refine writerWP_mono (hC w w3 B top0 pre cv rk (fun i => nodeAt w.top.rootKey P i)
        (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
        (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length stop w2 _ S hm hLC hb3H hlen3 hgh2 hsa2 hvB hk hICEk (by simp [nodeAt])
        hB hI hRO hF hICE hr03 hkey hrk
        hvisw hpX hpK hlkX hXNw hlinkK hne' hall' hnl' hdepth hsD hbetween hLE (Or.inl rfl) hJ2
        (Or.inr hK0) hDR hTJ2 hTA |> writerWP_and <| dw_appendDeleteKlong base _ stop _ c _ hvc hth hdw2) ?_
      intro _ w' hD'
      refine writerWP_mono (hMU gs hs false w' hD'.1 hD'.2) ?_
      intro _ w1 hD1
      exact writerWP_mono (hCR seg w1 hD1) (fun _ w2 hD2 => hpost w2 hD2)
  · -- LE-b at an inner stop node: none, with the fill at the delete's start
    intro seg stop w2 S hsD hbetween hLE hJ2 hsl hK0 hsm gs hs
    exact (lebStop_false c base w hLC hm hI (fun i => nodeAt w.top.rootKey P i)
      (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
      (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length stop cv (by simp [nodeAt]) hXNw hlinkK hall'
      hsD hbetween hsl).elim

/-- The walk with the merges' loop kept in `DelInv` and `DW`: `writerWP_del_emptyAnyMKLHGJDG`. -/
theorem writerWP_del_emptyAnyMKLHGJD (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
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
    (H : NodeId → Nat → Prop) (hC : UpCascOKHGJ c base KO BK H)
    (hLC : LiveCounts c.p (wNode c.p base w) c.i w.top.rootKey)
    (hvo : ViewHtOK H BK c) (hkw : ViewKlongsWf c.p c.view) (hhi : HtInv H BK c w) (hwfw : WriterKlongsWf w)
    (hub : UntakenBound (c.p.fuel - 1) w)
    (hsa2 : 2 ≤ c.p.splitAbove) (hICEk : ICEFromKinds c base KO BK)
    (hm : c.p.merges = true) (hpos : 0 < c.i)
    (hTJ2 : TakeJ2 c base B w) (hTA : TakenAbove B w) (hMF : ∀ x o, w.madeFor.lookup x = some o → o < B)
    (hth : 2 ≤ c.p.theta ∨ c.p.theta = 0) (hdw : DW c base w)
    (hA : ∀ g h v, DelInv c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK v → DW c base v →
      WriterWP (afterDelete (pre ++ [cv]) g h) c v (fun _ v' => DW c base v'))
    (hMU : ∀ g h merged v, DelInv c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK v → DW c base v →
      WriterWP (mergeUp (pre ++ [cv]) g c.p.fuel h merged) c v
        (fun _ v' => DelInv c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK v' ∧ DW c base v'))
    (hCR : ∀ seg v, DW c base v →
      WriterWP (collapseRoot (pre ++ [cv]) seg c.p.fuel) c v (fun _ v' => DW c base v'))
    (Post : W → Prop) (hfresh : ∀ v, Post v → WriterWP fresh c v (fun _ v' => Post v'))
    (hpost : ∀ v, DW c base v → Post v) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' => Post w') :=
  writerWP_del_emptyAnyMKLHGJDG c base hvc pre cv rk w B top0 hB hbook KO BK hvB hk hb0 hi0 hI hRO
    hF hICE hkey hrk hleafC H hC hLC hvo hkw hhi hwfw hub hsa2 hICEk hm hpos hTJ2 hTA hMF hth hdw
    hA _ hMU (fun seg v hv => hCR seg v hv.2) Post hfresh hpost
/-! ## The cases of a delete with the merges, for `DW` -/

/-- `DelStepsCaseOK` for the dead klongs' bound: `DW` from the operation's start
to its end, given `afterDelete` and the merges' loop with `DelInv` and `DW`, and
root collapse with `DW`. -/
def DelStepsCaseDOK (p : Params) (R : Struct BVal → Time → Prop)
    (P : Ctx → View BVal → W → Op → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w →
    RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey →
    SegFits (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) (p.fuel - 1) w.top.rootKey →
    ∀ key, op = .del key → P (ctxOf p ts) (viewOf (treeRun p ts)) w op →
    (∀ g h v, DelInv (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1)
        (kindOracleOf p (treeRun p ts)) tx.base v → DW (ctxOf p ts) (viewOf (treeRun p ts)) v →
      WriterWP (afterDelete key g h) (ctxOf p ts) v (fun _ v' => DW (ctxOf p ts) (viewOf (treeRun p ts)) v')) →
    (∀ g h merged v, DelInv (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1)
        (kindOracleOf p (treeRun p ts)) tx.base v → DW (ctxOf p ts) (viewOf (treeRun p ts)) v →
      WriterWP (mergeUp key g p.fuel h merged) (ctxOf p ts) v
        (fun _ v' => DelInv (ctxOf p ts) (viewOf (treeRun p ts)) w key (p.fuel + 1)
          (kindOracleOf p (treeRun p ts)) tx.base v' ∧ DW (ctxOf p ts) (viewOf (treeRun p ts)) v')) →
    (∀ seg v, DW (ctxOf p ts) (viewOf (treeRun p ts)) v →
      WriterWP (collapseRoot key seg p.fuel) (ctxOf p ts) v
        (fun _ v' => DW (ctxOf p ts) (viewOf (treeRun p ts)) v')) →
    (2 ≤ p.theta ∨ p.theta = 0) →
    DW (ctxOf p ts) (viewOf (treeRun p ts)) w →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' => DW (ctxOf p ts) (viewOf (treeRun p ts)) w')


/-- `DelStepsCaseDOK` with the obligations over an invariant I (bergdb 025-05, P4):
I holds where `DelInv` at p.fuel + 1 holds; the end is `DW`, which speaks of no fuel. -/
def DelStepsCaseDOKG (p : Params) (R : Struct BVal → Time → Prop)
    (P : Ctx → View BVal → W → Op → Prop) (I : List Tx → Tx → W → Key → W → Prop) : Prop :=
  ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
    lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
    topOf p (ctxOf p ts).view z = .ok top →
    ∀ pre op post, tx.ops = pre ++ op :: post →
    ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
    PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w →
    RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey →
    SegFits (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) (p.fuel - 1) w.top.rootKey →
    ∀ key, op = .del key → P (ctxOf p ts) (viewOf (treeRun p ts)) w op →
    (∀ v, DelInvI p ts tx w key v → I ts tx w key v) →
    (∀ g h v, I ts tx w key v → DW (ctxOf p ts) (viewOf (treeRun p ts)) v →
      WriterWP (afterDelete key g h) (ctxOf p ts) v (fun _ v' => DW (ctxOf p ts) (viewOf (treeRun p ts)) v')) →
    (∀ g h merged v, I ts tx w key v → DW (ctxOf p ts) (viewOf (treeRun p ts)) v →
      WriterWP (mergeUp key g p.fuel h merged) (ctxOf p ts) v
        (fun _ v' => I ts tx w key v' ∧ DW (ctxOf p ts) (viewOf (treeRun p ts)) v')) →
    (∀ seg v, DW (ctxOf p ts) (viewOf (treeRun p ts)) v →
      WriterWP (collapseRoot key seg p.fuel) (ctxOf p ts) v
        (fun _ v' => DW (ctxOf p ts) (viewOf (treeRun p ts)) v')) →
    (2 ≤ p.theta ∨ p.theta = 0) →
    DW (ctxOf p ts) (viewOf (treeRun p ts)) w →
    WriterWP (putKv op) (ctxOf p ts) w (fun _ w' => DW (ctxOf p ts) (viewOf (treeRun p ts)) w')


/-- The old case is the instance at `DelInvI`. -/
theorem delStepsCaseDOK_of_G (p : Params) (R : Struct BVal → Time → Prop)
    (P : Ctx → View BVal → W → Op → Prop) (h : DelStepsCaseDOKG p R P (DelInvI p)) :
    DelStepsCaseDOK p R P :=
  fun ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop hP hA hMU hCR hth hdw =>
    h ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop hP (fun _ hv => hv)
      hA hMU hCR hth hdw

/-- And back: the old case gives the family at `DelInvI`. -/
theorem delStepsCaseDOK_to_G (p : Params) (R : Struct BVal → Time → Prop)
    (P : Ctx → View BVal → W → Op → Prop) (h : DelStepsCaseDOK p R P) :
    DelStepsCaseDOKG p R P (DelInvI p) :=
  fun ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop hP _ hA hMU hCR hth hdw =>
    h ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop hP hA hMU hCR hth hdw
theorem delStepsCaseDOK_orG (p : Params) (R : Struct BVal → Time → Prop)
    (P P1 P2 : Ctx → View BVal → W → Op → Prop) (I : List Tx → Tx → W → Key → W → Prop)
    (hs : ∀ c base w op, P c base w op → P1 c base w op ∨ P2 c base w op)
    (h1 : DelStepsCaseDOKG p R P1 I) (h2 : DelStepsCaseDOKG p R P2 I) : DelStepsCaseDOKG p R P I := by
  intro ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop hPc hin hA hMU hCR hth hdw
  rcases hs _ _ _ _ hPc with h | h
  · exact h1 ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop h hin hA hMU hCR hth hdw
  · exact h2 ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop h hin hA hMU hCR hth hdw


theorem delStepsCaseDOK_or (p : Params) (R : Struct BVal → Time → Prop)
    (P P1 P2 : Ctx → View BVal → W → Op → Prop)
    (hs : ∀ c base w op, P c base w op → P1 c base w op ∨ P2 c base w op)
    (h1 : DelStepsCaseDOK p R P1) (h2 : DelStepsCaseDOK p R P2) : DelStepsCaseDOK p R P :=
  delStepsCaseDOK_of_G p R P (delStepsCaseDOK_orG p R P P1 P2 _ hs (delStepsCaseDOK_to_G p R P1 h1)
    (delStepsCaseDOK_to_G p R P2 h2))
/-- No leaf: the delete reads only. -/
theorem delStepsCaseDOK_noLeafG (p : Params) (R : Struct BVal → Time → Prop)
    (I : List Tx → Tx → W → Key → W → Prop) : DelStepsCaseDOKG p R DelNoLeafM I := by
  intro ts tx hw _ _ _ _ _ ops op post hops _ w _ hI _ _ key0 _ hP _ _ _ _ _ hdw
  obtain ⟨key, hop, _, hno⟩ := hP
  subst hop
  have hkey : keyWf key = true := within_op_keyWf p ts tx hw ops _ post hops
  have hne : key ≠ [] := by intro h; subst h; simp [keyWf] at hkey
  exact writerWP_mono (writerWP_del_noLeaf_reads (ctxOf p ts) _ (viewCoherent_ctxOf p ts) key w hI hne hno)
    (fun _ _ hr => dw_of_wNode hr.1 hdw)

theorem delStepsCaseDOK_noLeaf (p : Params) (R : Struct BVal → Time → Prop) :
    DelStepsCaseDOK p R DelNoLeafM :=
  delStepsCaseDOK_of_G p R _ (delStepsCaseDOK_noLeafG p R _)
/-- A noop: the delete reads only. -/
theorem delStepsCaseDOK_noopG (p : Params) (R : Struct BVal → Time → Prop)
    (I : List Tx → Tx → W → Key → W → Prop) : DelStepsCaseDOKG p R DelNoopM I := by
  intro ts tx _ _ _ _ _ _ _ op _ _ _ w _ hI _ _ _ _ hP _ _ _ _ _ hdw
  obtain ⟨pre, cv, L, n, hop, _, hK, hnoop⟩ := hP
  subst hop
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  exact writerWP_mono (writerWP_del_noop_reads (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w hI hrk
    (keyLeaf_all hK hrk (fun m => bitsUnion m.lastBitmap (m.bitsOf cv) = m.lastBitmap) hnoop))
    (fun _ _ hr => dw_of_wNode hr.1 hdw)

theorem delStepsCaseDOK_noop (p : Params) (R : Struct BVal → Time → Prop) :
    DelStepsCaseDOK p R DelNoopM :=
  delStepsCaseDOK_of_G p R _ (delStepsCaseDOK_noopG p R _)
/-- The upward delete with room for the stop node's bitmap. -/
theorem delStepsCaseDOK_emptyRoomG (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (I : List Tx → Tx → W → Key → W → Prop) : DelStepsCaseDOKG p R DelEmptyRoomM I := by
  intro ts tx hw hr z top _ htop ops op post hops r w hpre hI hRO hF key hop hPc hin hA hMU hCR hth hdw
  obtain ⟨pre, cv, L0, n0, hop', hm, hK, hne0, hall0, hup0⟩ := hPc
  subst hop'
  cases hop
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  have hICE := innerChildren_reachedR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
    (fun x hx => hI.untaken x (tReach_reachS _ _ _ _ hx))
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
  exact writerWP_del_emptyRoomMKDG (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w tx.base top hB hbook
    _ tx.base hv hk hb0 hi0 hI hRO hF hICE hkey hrk (keyLeaf_all2 hK hrk _ ⟨hne0, hall0, hup0⟩) hm
    (by simp [ctxOf]) (by simpa [ctxOf] using hth) hdw
    (fun g h v hv hdv => hA g h v (hin v hv) hdv) (fun v => I ts tx w (pre ++ [cv]) v ∧ DW (ctxOf p
      ts) (viewOf (treeRun p ts)) v) (fun g h m v hv hdv => hMU g h m v (hin v hv) hdv) (fun seg v
      hv => hCR seg v hv.2) _
    (fun v hv' => by unfold fresh; wpSimplify; exact dw_same rfl rfl hv') (fun _ h => h)

theorem delStepsCaseDOK_emptyRoom (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P) :
    DelStepsCaseDOK p R DelEmptyRoomM :=
  delStepsCaseDOK_of_G p R _ (delStepsCaseDOK_emptyRoomG p R hM hRL hRP hRK _)
/-- The space root emptied: its bitmap only. -/
theorem delStepsCaseDOK_emptyRootG (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (I : List Tx → Tx → W → Key → W → Prop) : DelStepsCaseDOKG p R DelEmptyRootM I := by
  intro ts tx hw hr z top _ htop ops op post hops r w hpre hI hRO hF key hop hPc _ _ _ _ hth hdw
  obtain ⟨pre, cv, L0, n0, hop', _, hK, hne0, hall0, hroot0⟩ := hPc
  subst hop'
  cases hop
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
  have hJ0 : KdJ (ctxOf p ts) tx.base top (kindOracleOf p (treeRun p ts)) tx.base w := ⟨hbook, hb0, hi0⟩
  refine writerWP_del_toLeafMK (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w _ hJ0
    (fun s f x v hJ hx => kdJ_descendLte _ _ tx.base top hB _ tx.base hv hk s f x v hJ hx)
    (fun s x L n v hJ hL hlk hkm => kdJ_pathAdd _ _ tx.base top hB _ tx.base hv s x L n v hJ hL hlk hkm)
    (kdJ_start _ _ tx.base top hB _ tx.base hv w hJ0) hrk (hI.pathUntaken _) hI.wf _ ?_ ?_
  · intro v hv'
    unfold fresh
    wpSimplify
    exact dw_same rfl rfl hv'
  · intro L n P w3 hL hn hnl hr03 _ hlk3 hp3' hlinkP hXD _
    obtain ⟨hne, hall, hLr⟩ := keyLeaf_all2 hK hrk
      (fun L' m => bitsUnion m.lastBitmap (m.bitsOf cv) ≠ m.lastBitmap ∧
        m.allKeysIn (bitsUnion m.lastBitmap (m.bitsOf cv)) = true ∧ L' = w.top.rootKey)
      ⟨hne0, hall0, hroot0⟩ L n hL hn hnl
    have hPnil := path_nil_of_root _ _ w hI.tree P hlinkP (by rw [hXD, hLr])
    subst hPnil
    have hp0 : (w3.path[0]?).map (·.2) = some L := by rw [hp3', hLr]; rfl
    exact writerWP_deleteUpward_rootEmpty (ctxOf p ts) L n cv (pre ++ [cv]) w3 hlk3 hp0 hnl hne hall _
      (dw_appendDeleteKlong _ L 0 cv (ctxOf p ts) _ (viewCoherent_ctxOf p ts) (by simpa [ctxOf] using hth)
        (dw_same rfl rfl (dw_of_wNode hr03.1 hdw)))

theorem delStepsCaseDOK_emptyRoot (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P) :
    DelStepsCaseDOK p R DelEmptyRootM :=
  delStepsCaseDOK_of_G p R _ (delStepsCaseDOK_emptyRootG p R hM hRL hRP hRK _)
/-- The upward delete whose stop node has no room. -/
theorem delStepsCaseDOK_emptyCascG (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P)
    (hRK : ∀ P t, R P t → KindsAllOK p P) (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (hht : OpHtDelOKUnder p R) (hdel : TakeBelowFuelDelOK p)
    (hLC : StateOK p R (fun ts _ w => LiveCountsW p ts w))
    (hJ2S : StateOK p R (fun ts tx w => TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w))
    (hMFS : StateOK p R (fun _ tx w => ∀ x o, w.madeFor.lookup x = some o → o < tx.base))
    (I : List Tx → Tx → W → Key → W → Prop) : DelStepsCaseDOKG p R DelEmptyCascM I := by
  intro ts tx hw hr z top hz htop ops op post hops r w hpre hI hRO hF key hop hPc hin hA hMU hCR hth hdw
  have hLCw := hLC ts tx hw hr z top hz htop ops (op :: post) hops r w hpre
  have hJ2w := hJ2S ts tx hw hr z top hz htop ops (op :: post) hops r w hpre
  have hMFw := hMFS ts tx hw hr z top hz htop ops (op :: post) hops r w hpre
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
  exact writerWP_del_emptyAnyMKLHGJDG (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w tx.base top hB hbook
    _ tx.base hv hk hb0 hi0 hI hRO hF hICE hkey hrk (keyLeaf_all2 hK hrk _ ⟨hne0, hall0, hLr⟩)
    _ (upCascOKHGJ_of_noU _ _ _ _ _
      (upCascFitsOKR_of _ _ _ _ _ hvo hbase hHb (by simp [ctxOf]))) hLCw hvo hkw hhi hwfw hub
    (by simpa [ctxOf] using hsa2) hICEk hm (by simp [ctxOf]) hJ2w
    (fun y hy => hhi.takenAbove y (by simpa using hy)) hMFw (by simpa [ctxOf] using hth) hdw
    (fun g h v hv hdv => hA g h v (hin v hv) hdv) (fun v => I ts tx w (pre ++ [cv]) v ∧ DW (ctxOf p
      ts) (viewOf (treeRun p ts)) v) (fun g h m v hv hdv => hMU g h m v (hin v hv) hdv) (fun seg v
      hv => hCR seg v hv.2)
    _ (fun v hv' => by unfold fresh; wpSimplify; exact dw_same rfl rfl hv') (fun _ h => h)

theorem delStepsCaseDOK_emptyCasc (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P)
    (hRK : ∀ P t, R P t → KindsAllOK p P) (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (hht : OpHtDelOKUnder p R) (hdel : TakeBelowFuelDelOK p)
    (hLC : StateOK p R (fun ts _ w => LiveCountsW p ts w))
    (hJ2S : StateOK p R (fun ts tx w => TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w))
    (hMFS : StateOK p R (fun _ tx w => ∀ x o, w.madeFor.lookup x = some o → o < tx.base)) :
    DelStepsCaseDOK p R DelEmptyCascM :=
  delStepsCaseDOK_of_G p R _ (delStepsCaseDOK_emptyCascG p R hM hsa2 hRL hRP hRK hRH hht hdel hLC
    hJ2S hMFS _)
/-- A leaf with room that keeps a live klong: its bitmap, then `afterDelete`. -/
theorem delStepsCaseDOK_roomG (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (I : List Tx → Tx → W → Key → W → Prop) : DelStepsCaseDOKG p R DelRoomM I := by
  intro ts tx hw hr z top _ htop ops op post hops r w hpre hI hRO hF key hop hPc hin hA _ _ hth hdw
  obtain ⟨pre, cv, L0, n0, hop', _, hK, hne0, hkeep0, hroom0⟩ := hPc
  subst hop'
  cases hop
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, hn0⟩ := keyLeaf_rk hK
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  have hICE := innerChildren_reachedR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
    (fun x hx => hI.untaken x (tReach_reachS _ _ _ _ hx))
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
  have hJ0 : KdJ (ctxOf p ts) tx.base top (kindOracleOf p (treeRun p ts)) tx.base w := ⟨hbook, hb0, hi0⟩
  refine writerWP_del_toLeafMK (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w _ hJ0
    (fun s f x v hJ hx => kdJ_descendLte _ _ tx.base top hB _ tx.base hv hk s f x v hJ hx)
    (fun s x L n v hJ hL hlk hkm => kdJ_pathAdd _ _ tx.base top hB _ tx.base hv s x L n v hJ hL hlk hkm)
    (kdJ_start _ _ tx.base top hB _ tx.base hv w hJ0) hrk (hI.pathUntaken _) hI.wf _ ?_ ?_
  · intro v hv'
    unfold fresh
    wpSimplify
    exact dw_same rfl rfl hv'
  · intro L n P w3 hL hn hnl hr03 hJ3 hlk3 hp3' _ hXD _
    obtain ⟨hwf, htimes, hne, hkeep, hroomD⟩ := keyLeaf_all hK hrk
      (fun m => klongsWf m.ks = true ∧ (∀ s, Klong.time s ∈ m.ks → s ≤ (ctxOf p ts).i) ∧
        bitsUnion m.lastBitmap (m.bitsOf cv) ≠ m.lastBitmap ∧
        m.allKeysIn (bitsUnion m.lastBitmap (m.bitsOf cv)) = false ∧ DelRoom (ctxOf p ts) cv m)
      ⟨hI.wf L0 n0 hn0, hI.times L0 n0 hn0, hne0, hkeep0, hroom0⟩ L n hL hn hnl
    have hLt : w.taken.contains L = false :=
      hI.pathUntaken _ (L, cv) (fromVisits_append _ _ _ pre cv _ rk hrk _ hL)
    obtain ⟨a, hpx⟩ := path_last_of_toLeaf w w3 P L hp3' hXD
    refine writerWP_deleteUpward_full (ctxOf p ts) L n P.length cv (pre ++ [cv]) w3 hlk3 hne hkeep
      (fun v => DelInv (ctxOf p ts) (viewOf (treeRun p ts)) w (pre ++ [cv]) (p.fuel + 1)
        (kindOracleOf p (treeRun p ts)) tx.base v ∧ DW (ctxOf p ts) (viewOf (treeRun p ts)) v) _ ?_ ?_
    · refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and
        (writerWP_appendDeleteKlong_room_exactD L _ cv n _ _ hlk3 htimes hwf hne hroomD)
        (putBook_appendDeleteKlong L _ cv _ _ tx.base top hB _ hJ3.1))
        (kd_appendDeleteKlong _ tx.base L P.length cv _ w3 hv hk hJ3.2.1 hJ3.2.2 a hpx))
        (dw_appendDeleteKlong _ L P.length cv _ w3 (viewCoherent_ctxOf p ts) (by simpa [ctxOf] using hth)
          (dw_of_wNode hr03.1 hdw))) ?_
      rintro _ v ⟨⟨⟨⟨h1, h2, h3, _, _, _, h7⟩, hbv⟩, hkv⟩, hdwv⟩
      exact ⟨⟨delInvF_after_bitmap (ctxOf p ts) _ tx.base top hB w w3 v pre cv rk L n hI hRO hICE hF
        hkey hrk hL hn hnl hr03 hLt h1 h2 h3 h7 hbv, hkv.1, hkv.2.1⟩, hdwv⟩
    · intro g h v hv'
      exact hA g h v (hin v hv'.1) hv'.2

theorem delStepsCaseDOK_room (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P) :
    DelStepsCaseDOK p R DelRoomM :=
  delStepsCaseDOK_of_G p R _ (delStepsCaseDOK_roomG p R hM hRL hRP hRK _)
set_option maxHeartbeats 1600000 in
/-- A full leaf: its split, then `afterDelete`. -/
theorem delStepsCaseDOK_fullG (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P)
    (hRK : ∀ P t, R P t → KindsAllOK p P) (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (hht : OpHtDelOKUnder p R) (hdel : TakeBelowFuelDelOK p)
    (hRoot : ∀ ts, DelFullRootStepOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (I : List Tx → Tx → W → Key → W → Prop) : DelStepsCaseDOKG p R DelFullM I := by
  intro ts tx hw hr z top hz htop ops op post hops r w hpre hI hRO hF key hop hPc hin hA _ _ hth hdw
  obtain ⟨pre, cv, L0, n0, hop', _, hK, hne0, hkeep0, hfull0⟩ := hPc
  subst hop'
  cases hop
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
  have hwts : Within p ts := by
    have := within_take p (ts ++ [tx]) hw ts.length
    simpa using this
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl (hRK _ _ hr)
      (hRP _ _ hr) hb hi.cache hun
  have hJ0 : KdJ (ctxOf p ts) tx.base top (kindOracleOf p (treeRun p ts)) tx.base w := ⟨hbook, hb0, hi0⟩
  obtain ⟨hvo, hkw, _, _, _, hhi, hwfw, hub⟩ := htStart_reachedU p hM R hRL hRK hRH hht hdel ts tx hw hr z top
    hz htop ops (.del (pre ++ [cv]) :: post) hops r w hpre
  refine writerWP_del_toLeafMKH (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w
    (KdHtJ (ctxOf p ts) tx.base top (kindOracleOf p (treeRun p ts)) tx.base (htOracleOf p (treeRun p ts)))
    (fun s f x v hJ hx => kdhtJ_descendLte _ top hB _ tx.base hv hk hvo hkw s f x v hJ hx)
    (fun s fd L n v hJ hL hlk hleaf hfd => kdhtJ_pathAdd _ top hB _ tx.base hv hvo s fd L n v hJ hL hlk hleaf hfd)
    (kdhtJ_start _ top hB _ tx.base hv hvo w hJ0 hhi hwfw hub) hrk (hI.pathUntaken _) hI.wf _ ?_ ?_
  · intro v hv'
    unfold fresh
    wpSimplify
    exact dw_same rfl rfl hv'
  · intro L n P w3 hL hn hnl hr03 hJ3 hlk3 hp3' hlinkP hXD hlkX
    obtain ⟨hne, hkeep, hfull⟩ := keyLeaf_all2 hK hrk
      (fun _ m => bitsUnion m.lastBitmap (m.bitsOf cv) ≠ m.lastBitmap ∧
        m.allKeysIn (bitsUnion m.lastBitmap (m.bitsOf cv)) = false ∧ ¬ DelRoom (ctxOf p ts) cv m)
      ⟨hne0, hkeep0, hfull0⟩ L n hL hn hnl
    refine writerWP_deleteUpward_full (ctxOf p ts) L n P.length cv (pre ++ [cv]) w3 hlk3 hne hkeep
      (fun v => DelInv (ctxOf p ts) (viewOf (treeRun p ts)) w (pre ++ [cv]) (p.fuel + 1)
        (kindOracleOf p (treeRun p ts)) tx.base v ∧ DW (ctxOf p ts) (viewOf (treeRun p ts)) v) _
      (writerWP_and (writerWP_appendDeleteKlong_full_delH (ctxOf p ts) _ (viewCoherent_ctxOf p ts) _ tx.base (hRoot ts) _
        (delFullFitsOKR_run p ts tx hw (hRL _ _ hr) (hRK _ _ hr) (hRH _ _ hr))
        hsa2 hv hk hICEk w pre cv rk tx.base top hB hI hRO hF hkey hrk L n P w3 hL hn hnl hne hfull
        hr03 hJ3.1 hJ3.2 hp3' hlinkP hXD hlkX)
        (dw_appendDeleteKlong _ L P.length cv _ w3 (viewCoherent_ctxOf p ts) (by simpa [ctxOf] using hth)
          (dw_of_wNode hr03.1 hdw))) ?_
    intro g h v hv'
    exact hA g h v (hin v hv'.1) hv'.2

theorem delStepsCaseDOK_full (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P)
    (hRK : ∀ P t, R P t → KindsAllOK p P) (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (hht : OpHtDelOKUnder p R) (hdel : TakeBelowFuelDelOK p)
    (hRoot : ∀ ts, DelFullRootStepOK (ctxOf p ts) (viewOf (treeRun p ts))) :
    DelStepsCaseDOK p R DelFullM :=
  delStepsCaseDOK_of_G p R _ (delStepsCaseDOK_fullG p R hM hsa2 hRL hRP hRK hRH hht hdel hRoot _)
/-- Every delete with the merges on, for `DW`: its five cases. -/
theorem delStepsCaseDOK_mergeG (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P)
    (hRK : ∀ P t, R P t → KindsAllOK p P) (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (hht : OpHtDelOKUnder p R) (hdel : TakeBelowFuelDelOK p)
    (hLC : StateOK p R (fun ts _ w => LiveCountsW p ts w))
    (hJ2S : StateOK p R (fun ts tx w => TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w))
    (hMFS : StateOK p R (fun _ tx w => ∀ x o, w.madeFor.lookup x = some o → o < tx.base))
    (I : List Tx → Tx → W → Key → W → Prop) : DelStepsCaseDOKG p R DelMergeCase I := by
  intro ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop hPc hin hA hMU hCR hth hdw
  obtain ⟨_, _, hm⟩ := hPc
  have c7 := delStepsCaseDOK_orG p R _ _ _ I delEmptyM_split (delStepsCaseDOK_emptyRoomG p R hM hRL hRP hRK I)
    (delStepsCaseDOK_orG p R _ _ _ I delEmptyOther_split (delStepsCaseDOK_emptyRootG p R hM hRL hRP hRK I)
      (delStepsCaseDOK_emptyCascG p R hM hsa2 hRL hRP hRK hRH hht hdel hLC hJ2S hMFS I))
  rcases delMerge_cover (ctxOf p ts) (viewOf (treeRun p ts)) w key hm with h | h | h | h | h
  · exact delStepsCaseDOK_noLeafG p R I ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop
      (hop ▸ h) hin hA hMU hCR hth hdw
  · exact delStepsCaseDOK_noopG p R I ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop
      (hop ▸ h) hin hA hMU hCR hth hdw
  · exact c7 ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop (hop ▸ h) hin hA hMU hCR hth hdw
  · exact delStepsCaseDOK_roomG p R hM hRL hRP hRK I ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF
      key hop (hop ▸ h) hin hA hMU hCR hth hdw
  · exact delStepsCaseDOK_fullG p R hM hsa2 hRL hRP hRK hRH hht hdel (fun ts => delFullRootStepOK_ctx p ts)
      I ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop (hop ▸ h) hin hA hMU hCR hth hdw

theorem delStepsCaseDOK_merge (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P)
    (hRK : ∀ P t, R P t → KindsAllOK p P) (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (hht : OpHtDelOKUnder p R) (hdel : TakeBelowFuelDelOK p)
    (hLC : StateOK p R (fun ts _ w => LiveCountsW p ts w))
    (hJ2S : StateOK p R (fun ts tx w => TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w))
    (hMFS : StateOK p R (fun _ tx w => ∀ x o, w.madeFor.lookup x = some o → o < tx.base)) :
    DelStepsCaseDOK p R DelMergeCase :=
  delStepsCaseDOK_of_G p R _ (delStepsCaseDOK_mergeG p R hM hsa2 hRL hRP hRK hRH hht hdel hLC hJ2S
    hMFS _)
/-- `d4`'s claim for every delete with the merges on (`QDead`): from the cases,
the merges' loop and `afterDelete` with `DelInv` and `DW` (`writerWP_mergeUp_delDW`,
`dw_afterDelete`, from `MergeStepOK`), root collapse (`dw_collapseRoot`), and the
fuel at the operation's start (`TxSegFitsOK`). -/
theorem opCaseOK_dead_delMerge (p : Params) (R : Struct BVal → Time → Prop)
    (hS : DelStepsCaseDOK p R DelMergeCase)
    (hMS : ∀ ts, MergeStepOK (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax) (hMM : 2 ≤ p.M)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (hfit : TxSegFitsOK p R) (hth : 2 ≤ p.theta ∨ p.theta = 0) :
    OpCaseOK p R (QDead p) DelMergeCase := by
  have hf2 : 2 ≤ p.fuel + 1 := by unfold Params.fuel; omega
  intro ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hP
  obtain ⟨key, hop, _⟩ := hP
  have hfresh : ∀ q ∈ treeRun p ts, q.1 < tx.base := by
    have := (hw.2 ts.length (by simp)).1
    simpa using this
  have hK := hRK _ _ hr
  have hv : ViewIdsBelow tx.base (ctxOf p ts).view :=
    viewIdsBelow_rootless _ _ (viewIdsBelow_view p (treeRun p ts) ts.length tx.base hfresh)
  have hk : ViewKinds (kindOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) :=
    viewKinds_of p (treeRun p ts) ts.length tx.base hfresh (treeRun_timesLE p ts) (hRP _ _ hr) hK
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl hK
      (hRP _ _ hr) hb hi.cache hun
  have hF := hfit ts tx hw hr z top hz htop pre (op :: post) hops r w hpre
  have hth' : 2 ≤ (ctxOf p ts).p.theta ∨ (ctxOf p ts).p.theta = 0 := hth
  by_cases hD0' : ¬ WDeadOK p (treeRun p ts) w
  · intro _ _ _ h
    exact absurd h hD0'
  have hD0 : WDeadOK p (treeRun p ts) w := Classical.byContradiction hD0'
  have hdw : DW (ctxOf p ts) (viewOf (treeRun p ts)) w := ⟨hD0, hI.wf⟩
  refine writerWP_mono (hS ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop ⟨key, hop, ?_⟩
    (fun g h v hv' hdv => dw_afterDelete key g h (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hMS ts) _ _ hv hk hICEk hsa2 hcap hth' w key v hv' hdv)
    (fun g h merged v hv' hdv => writerWP_mergeUp_delDW key g (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hMS ts) _ _ hv hk hICEk hsa2 hcap hth' w key p.fuel h merged v hv' hdv)
    (fun seg v hdv => dw_collapseRoot _ key seg p.fuel (ctxOf p ts) v (viewCoherent_ctxOf p ts) hth' hdv)
    hth hdw) ?_
  · assumption
  · intro _ w' hdw' _
    exact hdw'.1

end SIS.Tree
