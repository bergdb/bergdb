/-
The first stratum's delete with the merges (bergdb 025-05, step 7): the stop node's
cascade, the last of the family's cases, and the family whole (`delStepsTJA_holds`);
with it the first stratum from `hchk` alone (`jointHtJ_reachedS`).

The cascade needs no heights in the stratum: they served only the fit after the stop
node's split (`UpCascFitsOKR`). The obligation `UpCascJ2OKT` is `UpCascJ2OKHG` with
the kinds' walk in place of the heights' and the tree's facts as its end, proved by
the split's tree-facts forms (`writerWP_upCasc_root_delT`,
`writerWP_upCasc_below_delST`); the walk's fit at the start is P1's
(`takeJ2_deleteUpward_stepMBKGD` at the next id's depth).
-/
import SIS.Tree.StratumSteps

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- `UpCascJ2OKHG` in the first stratum (bergdb 025-05, step 7): no heights, no fit at
the start, the tree's facts after the stop node's bitmap (`DelInvJT`). -/
def UpCascJ2OKT (c : Ctx) (base : View BVal) (KO : KindOracle) (BK B : NodeId) : Prop :=
  ∀ (w w3 : W) (top0 : Top) (pre : List Nat) (cv : Nat) (rk : NodeId)
    (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth stop : Nat) (w2 v : W) (S : KNode),
    c.p.merges = true → LiveCounts c.p (wNode c.p base w) c.i w.top.rootKey →
    KdJ c B top0 KO BK w3 → w3.path.length = depth + 1 →
    2 ≤ c.p.splitAbove → ViewIdsBelow BK c.view → ViewKinds KO BK c → ICEFromKinds c base KO BK →
    X 0 = w.top.rootKey → 0 < c.i → PutBase c base B → PutInv c base w → RangeOrder (wNode c.p base w) c.i w.top.rootKey →
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
      (fun _ w' => DelInvJT c base KO BK B w')

/-- `UpCascJ2OKT` holds (`upCascJ2OKHGJ_of_noU` with no fits: the stop node's split by
`writerWP_upCasc_root_delT` and `writerWP_upCasc_below_delST`). -/
theorem upCascJ2OKT_holds (c : Ctx) (base : View BVal) (KO : KindOracle) (B : NodeId) :
    UpCascJ2OKT c base KO B B := by
  intro w w3 top0 pre cv rk X Nn K depth stop w2 v S _ _ _ _ hsa2 hvB hk hICEk hX0 hpos hB hI hRO _ hr03
    hkey hrk hvis hpX hpK hlkX hXN hlinkK _ hall hleaf hdepth hsD hbetween hLE hv hJ hkind hfull hJw
    _ hkidsw
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
  have hT : WriterWP (appendDeleteKlong (X stop) stop (K (stop + 1))) c v
      (fun _ w' => DelInvT c base KO B w') := by
    rcases Nat.eq_zero_or_pos stop with hs | hs
    · subst hs
      exact writerWP_mono (writerWP_upCasc_root_delT c base hB.coherent hsa2 KO B hvB hk hICEk w w3 B B top0
        pre cv rk X Nn K depth w2 v S hB hI hRO hr03 hkey hrk hvis hpX hlkX hXN hlinkK hall hleaf hdepth
        hbetween hX0 hLE hv hJ hkind hfull hlinks2 hwf2) (fun _ _ h => h.1)
    · obtain ⟨D, rfl⟩ : ∃ D, stop = D + 1 := ⟨stop - 1, by omega⟩
      exact writerWP_mono (writerWP_upCasc_below_delST c base hsa2 KO B hvB hk hICEk w w3 B B top0 pre cv rk
        X Nn K depth D w2 v S hB hI hRO hr03 hkey hrk hvis hpX hpK hlkX hXN hlinkK hall hleaf hsD hbetween
        hX0 hLE hv hJ hfull hcu hlinks2 hwf2) (fun _ _ h => h.1)
  exact writerWP_mono (writerWP_and hT hJ2) (fun _ _ h => ⟨h.1, h.2.1, h.2.2⟩)

set_option maxHeartbeats 3200000 in
/-- `writerWP_del_emptyAnyMJKLHGG` in the first stratum (bergdb 025-05, step 7): no fit at
the start and no heights, the continuations given the tree's facts (`DelInvJT`), the
stop node's cascade by `UpCascJ2OKT`. -/
theorem writerWP_del_emptyAnyMJKT (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (hbook : PutBook c B top0 w)
    (KO : KindOracle) (BK : NodeId) (hvB : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c)
    (hb0 : Book BK c w) (hi0 : KdInv KO BK w)
    (hI : PutInv c base w) (hRO : RangeOrder (wNode c.p base w) c.i w.top.rootKey)
    (hICE : InnerChildrenExist (wNode c.p base w) c.i w.top.rootKey)
    (hkey : keyWf (pre ++ [cv]) = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hleafC : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
      n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = true ∧ L ≠ w.top.rootKey)
    (hC : UpCascJ2OKT c base KO BK B)
    (hLC : LiveCounts c.p (wNode c.p base w) c.i w.top.rootKey)
    (hsa2 : 2 ≤ c.p.splitAbove) (hICEk : ICEFromKinds c base KO BK)
    (hm : c.p.merges = true) (hpos : 0 < c.i)
    (hJ2 : TakeJ2 c base B w) (hMF : ∀ x o, w.madeFor.lookup x = some o → o < B)
    (hLV : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true → ∀ y, (cv, y) ∈ n.liveAt c.i →
      wNode c.p base w y = none)
    (Post : W → Prop) (hfresh : ∀ v, Post v → WriterWP fresh c v (fun _ v' => Post v'))
    (Imid : W → Prop)
    (hA : ∀ g h v, DelInvJT c base KO BK B v →
      WriterWP (afterDelete (pre ++ [cv]) g h) c v (fun _ v' => Post v'))
    (hMU : ∀ g h merged v, DelInvJT c base KO BK B v →
      WriterWP (mergeUp (pre ++ [cv]) g c.p.fuel h merged) c v (fun _ v' => Imid v'))
    (hCR : ∀ seg v, Imid v →
      WriterWP (collapseRoot (pre ++ [cv]) seg c.p.fuel) c v (fun _ v' => Post v')) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' => Post w') := by
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  refine writerWP_del_toLeafMK c base hvc pre cv rk w (fun v => KdJ c B top0 KO BK v ∧ v.madeFor = w.madeFor)
    ⟨⟨hbook, hb0, hi0⟩, rfl⟩
    (fun s f x v hJ hx => writerWP_mono (writerWP_and (kdJ_descendLte c base B top0 hB KO BK hvB hk s f x v hJ.1 hx)
      (writerWP_descendLte_madeFor s c f x v)) (fun _ v' h => ⟨h.1, h.2.trans hJ.2⟩))
    (fun s x L n v hJ hL hlk hkm => ⟨kdJ_pathAdd c base B top0 hB KO BK hvB s x L n v hJ.1 hL hlk hkm, hJ.2⟩)
    ⟨kdJ_start c base B top0 hB KO BK hvB w ⟨hbook, hb0, hi0⟩, rfl⟩ hrk (hI.pathUntaken _) hI.wf
    Post hfresh ?_
  intro L n P w3 hL hn hnl hr03 hJ3 hlk3 hp3' hlinkP hXD hlkX
  have hb3 := hJ3.1
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
  have hfit3 : SegFits (wNode c.p base w3) c.i w3.next w3.top.rootKey :=
    segFits_next_of_putInv c base w3 (putInv_of_readsAs c base w w3 hI hr03)
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
  -- the tree's facts at a continuation of the upward delete
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
      PutBook c B top0 w' → Book BK c w' → KdInv KO BK w' →
      DelInvT c base KO BK w' := by
    intro stop w' sn' f hsD ht htop hv hnodes hsn' hsl' hsw' hst' hlive' hRO' hb' hbk hik
    have hCG := collGetInvD_after_upT c base (fun i => nodeAt w.top.rootKey P i)
      (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
      (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length w3 hlkX htk3 hdistP hT3 hwf3 hRt3 hTimesR3
      hICE3 w3.next hfit3 hnovalAll3 hreach3 hlinkK stop w' sn' f hsD ht htop hv hnodes hsn' hsl' hsw' hst' hlive'
    have hG := putInvG_of_book c base B top0 w' hB hb'
    have hPI : PutInv c base w' := putInv_of_parts c base w' hG hCG.1.1
      (fun y hy => hCG.1.2.1 y (reachS_tReach _ _ _ _ hy))
      (leafOrder_of_rangeOrder _ _ _ hRO' hG.times)
    exact ⟨hPI, hG, hRO', fun y yn cc z hy hyn hl hz => hCG.1.2.2.2 y yn cc z hy hyn hl hz,
      ⟨B, top0, hB, hb'⟩, hbk, hik⟩
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
  refine takeJ2_deleteUpward_stepMBKGD c base (fun i => nodeAt w.top.rootKey P i)
    (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
    (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length cv pre rk B w3 hdepth hfuel hpos hpX hpK hlkX htk3
    (fun i hi => hTimesR3 _ _ (hreach3 i hi) (hN3 i hi))
    hdistP (by rw [hNnD]; exact hne) (by rw [hNnD]; exact hall) (by rw [hNnD]; exact hnl) hT3 hR3 hwf3 hRt3
    hTimesR3 hICE3 w3.next hfit3 hnovalAll3 hreach3
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
  · intro seg stop w' sn' hsD hbetween ht htop hv hnodes hsn' hsl' hsw' hst' hlive' _ _ _ _ hJv _ hb'G gs hs
    have hb' := hb'G.1
    obtain ⟨hagree, hsnw⟩ := hfr stop w' sn' hsD ht hnodes hsn'
    have hRO' : RangeOrder (wNode c.p base w') c.i w'.top.rootKey := by
      rw [htop]
      exact rangeOrder_up_bitmap (wNode c.p base w3) (wNode c.p base w') c.i w3.top.rootKey _ _ _ stop
        P.length hsD hR3 hT3 (hreach3 stop (by omega)) (fun i _ h2 => hN3 i h2)
        (fun i h1 h2 => hlinkK i (by omega) h2) (fun i i' _ h2 _ h4 he => hdistP i i' h2 h4 he)
        hagree sn' hsnw hsl' (fun c' z h => (hlive' c' z).mp h)
    have hDv := hD stop w' sn' id hsD ht htop hv hnodes hsn' hsl' hsw' hst'
      (fun c' z h => ⟨c', ((hlive' c' z).mp h).1, ((hlive' c' z).mp h).2, rfl⟩) hRO' hb'.1.1 hb'.1.2.1 hb'.1.2.2
    refine writerWP_mono (hMU gs hs false w' ⟨hDv, hJv, hb'.1.1.fresh.1⟩) ?_
    intro _ w1 hD1
    exact hCR seg w1 hD1
  · intro stop w' sn' hsD hbetween ht htop hv hnodes hsn' hsl' hsw' hst' hlive' _ _ _ _ hJv _ hb'G gs hs
    have hb' := hb'G.1
    obtain ⟨hagree, hsnw⟩ := hfr stop w' sn' hsD ht hnodes hsn'
    have hRO' : RangeOrder (wNode c.p base w') c.i w'.top.rootKey := by
      rw [htop]
      exact rangeOrder_up_bitmap (wNode c.p base w3) (wNode c.p base w') c.i w3.top.rootKey _ _ _ stop
        P.length hsD hR3 hT3 (hreach3 stop (by omega)) (fun i _ h2 => hN3 i h2)
        (fun i h1 h2 => hlinkK i (by omega) h2) (fun i i' _ h2 _ h4 he => hdistP i i' h2 h4 he)
        hagree sn' hsnw hsl' (fun c' z h => (hlive' c' z).mp h)
    have hDv := hD stop w' sn' id hsD ht htop hv hnodes hsn' hsl' hsw' hst'
      (fun c' z h => ⟨c', ((hlive' c' z).mp h).1, ((hlive' c' z).mp h).2, rfl⟩) hRO' hb'.1.1 hb'.1.2.1 hb'.1.2.2
    exact hA gs hs w' ⟨hDv, hJv, hb'.1.1.fresh.1⟩
  · intro stop w2 S hsD hbetween hLE hJw2G hsl hDR gs hs
    obtain ⟨hJw2, _⟩ := hJw2G
    exact writerWP_mono (hC w w3 top0 pre cv rk (fun i => nodeAt w.top.rootKey P i)
      (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
      (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length stop w2 _ S hm hLC hJ3.1 hlen3 hsa2 hvB hk hICEk
      (by simp [nodeAt]) hpos hB hI hRO hICE hr03 hkey hrk
      hvisw hpX hpK hlkX hXN hlinkK hne' hall' hnl' hdepth hsD hbetween hLE (Or.inr ⟨_, rfl⟩)
      (kdJP_note c base B top0 hB KO BK hvB hk _ "up.stop-at-segment-leaf" w2 hJw2) (Or.inl hsl) hDR hJ2 hMF3 hkidsw)
      (fun _ w' hD' => hA gs hs w' hD')
  · intro seg stop w2 S hsD hbetween hLE hJw2G hsl hK0 hDR gs hs
    obtain ⟨hJw2, _⟩ := hJw2G
    refine writerWP_mono (hC w w3 top0 pre cv rk (fun i => nodeAt w.top.rootKey P i)
      (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
      (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length stop w2 _ S hm hLC hJ3.1 hlen3 hsa2 hvB hk hICEk
      (by simp [nodeAt]) hpos hB hI hRO hICE hr03 hkey hrk
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

set_option maxHeartbeats 1600000 in
/-- The stop node's cascade (`delStepsCaseJ2OK_emptyCascRLHGJ_noUG` over the stratum's walk
`writerWP_del_emptyAnyMJKT`; the live counts from `SJ0`). -/
theorem delStepsCaseTJ_emptyCasc (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (I : List Tx → Tx → W → Key → W → Prop) : DelStepsCaseTJ p R DelEmptyCascM I := by
  intro ts tx hw hr z top _ htop ops op post hops r w hpre hS hJ key hop hPc hin hout hA hMU hCR
  have hLCw : LiveCountsW p ts w := hS.2.2
  obtain ⟨pre, cv, L0, n0, hop', hm, hK, hne0, hall0, P0, hP0, hX0, hl0, _⟩ := hPc
  subst hop'
  cases hop
  have hI : PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w := hS.1.1.1.1.1
  have hRO : RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey := hS.1.1.2
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  have hICE := innerChildren_reachedR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
    (fun x hx => hI.untaken x (tReach_reachS _ _ _ _ hx))
  have hLV := leafVals_all hS.1.1.1.1.2 hkey hrk
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
  exact writerWP_del_emptyAnyMJKT (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w tx.base top hB hbook
    _ tx.base hv hk hb0 hi0 hI hRO hICE hkey hrk (keyLeaf_all2 hK hrk _ ⟨hne0, hall0, hLr⟩)
    (upCascJ2OKT_holds _ _ _ _) hLCw (by simpa [ctxOf] using hsa2) hICEk hm
    (by simp [ctxOf]) hJ hS.1.2 (fun L n hL hn hnl y hy => (hLV L n hL hn hnl y hy).1) _
    (fun v hv' => qdWJ_fresh p ts tx.base v hv') _
    (fun g h v hv => writerWP_mono (hA g h v (hin v hv)) (fun _ v' hv' => hout v' hv')) (fun g h m v
      hv => hMU g h m v (hin v hv)) (fun seg v hv => writerWP_mono (hCR seg v hv) (fun _ v' hv' =>
      hout v' hv'))

/-! ## The stratum's family, all cases -/

/-- The first stratum's family at its invariant: every delete with the merges keeps the
tree's facts and the take-back's, from a start with no fit and no heights' bound. -/
theorem delStepsTJA_holds (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P) : DelStepsTJA p R :=
  delStepsCaseTJ_of_cases p R _ (delStepsCaseTJ_noLeaf p R _) (delStepsCaseTJ_noop p R hRL _)
    (delStepsCaseTJ_or p R _ _ _ _ delEmptyM_split (delStepsCaseTJ_emptyRoom p R hM hRL hRP hRK _)
      (delStepsCaseTJ_or p R _ _ _ _ delEmptyOther_split (delStepsCaseTJ_emptyRoot p R hM hsa2 hRL hRP hRK _)
        (delStepsCaseTJ_emptyCasc p R hM hsa2 hRL hRP hRK _)))
    (delStepsCaseTJ_room p R hM hRL hRP hRK _) (delStepsCaseTJ_full p R hM hsa2 hRL hRP hRK _)

/-! ## The first stratum from `hchk` -/

/-- The first stratum (bergdb 025-05, step 7) with the family proved: the joint
induction with no `htb`, from the put cases, the live counts and `hchk`. -/
theorem jointHtJ_reachedS (p : Params) (R : Struct BVal → Time → Prop) (hm : p.merges = true)
    (hM : 2 ≤ p.M) (hM4 : 4 ≤ p.M) (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax)
    (hRB : BaseStartOK p R)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRT : ∀ P t, R P t → TreeAt p P t)
    (hRI : ∀ P t, R P t → InvOK p P t) (hRP : ∀ P t, R P t → PointersOK P)
    (hRK : ∀ P t, R P t → KindsAllOK p P) (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (hTp : OpCaseOK p R (QPut (QTree p)) AnyOp) (hPp : OpCaseOK p R (QPut (QPutInv p)) AnyOp)
    (hOp : OpCaseOK p R (QPut (QRange p)) AnyOp)
    (hLv : OpCaseOK p R (QLive p) AnyOp) (hchk : OpDelChk2ORJ p R)
    (ts : List Tx) (tx : Tx) (hw : Within p (ts ++ [tx])) (hr : R (treeRun p ts) ts.length)
    (z : NodeId) (top : Top)
    (hz : lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z)
    (htop : topOf p (ctxOf p ts).view z = .ok top) :
    ∀ pre post, tx.ops = pre ++ post → ∀ r w,
      (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w ∧
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey ∧
      LiveCounts p (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey ∧
      HtInv (htOracleOf p (treeRun p ts)) tx.base (ctxOf p ts) w ∧
      WriterTreeOK p (treeRun p ts) (ts.length + 1) w ∧ J2At p (treeRun p ts) (ts.length + 1) tx.base w :=
  jointHtJ_reachedT p R hm hM hM4 hsa2 hcap hRB hRL hRT hRI hRP hRK hRH hTp hPp hOp
    (delStepsTJA_holds p R hM hsa2 hRL hRP hRK) hLv hchk ts tx hw hr z top hz htop

end SIS.Tree
