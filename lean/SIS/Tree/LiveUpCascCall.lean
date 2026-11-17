/-
The upward delete whose stop node has no room (bergdb 030-01, step 6; `DelEmptyCascM`,
whose stop candidate need not be the climb's stop): the delete calls `afterDelete` at
the stop node's pair (g, 0) with the call's facts (`DelCaseLive`'s form, LiveAssembly.lean),
given one narrow obligation, the full stop node's split (`UpCascCallOK`). The walk is
`takeJ2_deleteUpward_stepMBKGDS` (LiveUpCascWalk.lean): where the stop node has room for
its bitmap, l4d's argument (`liveDel_upRoomH`, LiveUpRoomH.lean: the live frame
`liveEdgesH_up`, R1 by `holeAtW_stop`, the heights by `htInv_upFrame`); where it is full,
the obligation; an inner stop node is excluded by the live counts (`lebStop_false`).
-/
import SIS.Tree.LiveUpCascRoot
import SIS.Tree.LiveAssembly

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The full stop node's split (bergdb 030-01, step 6), the obligation left of the
upward delete: at the upward loop's end w2, the stop node X stop a full segment leaf
(no room for its bitmap, `DelRoom`), its bitmap (a split, maybe a cascade) ends at a
state with the facts of the call of `afterDelete` at its pair (g, 0): the tree's
(`DelInvJT`), the books, the heights and the hole that the merges' descent at (g, 0)
finds. The facts are those of the stratum's cascade (`UpCascJ2OKT`), with the live
counts at the delete's start, the heights' walk at the upward walk's start w3, the
climb's stop and the stop node's entry in `gh`. -/
def UpCascCallOK (c : Ctx) (base : View BVal) (KO : KindOracle) (B : NodeId)
    (H : NodeId → Nat → Prop) : Prop :=
  ∀ (w w3 : W) (top0 : Top) (pre : List Nat) (cv : Nat) (rk : NodeId)
    (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth stop : Nat) (w2 : W) (S : KNode)
    (g : Nat),
    ViewCoherent c base → c.p.merges = true → 2 ≤ c.p.splitAbove → MergeParamsOK c.p →
    ViewIdsBelow B c.view → ViewKinds KO B c → ICEFromKinds c base KO B →
    ViewHtOK H B c → ViewKlongsWf c.p c.view → 0 < c.i →
    PutBase c base B → PutBook c B top0 w → PutInv c base w →
    RangeOrder (wNode c.p base w) c.i w.top.rootKey →
    InnerChildrenExist (wNode c.p base w) c.i w.top.rootKey →
    LiveCounts c.p (wNode c.p base w) c.i w.top.rootKey →
    TakeJ2 c base B w → (∀ x o, w3.madeFor.lookup x = some o → o < B) →
    ReadsAs c.p base w w3 → KdJ c B top0 KO B w3 → HtInv H B c w3 → WriterKlongsWf w3 →
    w3.path.length = depth + 1 → X 0 = w.top.rootKey →
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
    (Nn depth).leaf = true →
    (∀ c' z, (c', z) ∈ (Nn depth).liveAt c.i → wNode c.p base w z = none) →
    0 < depth → stop < depth →
    (∀ i, stop < i → i < depth →
      (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true) →
    ((Nn stop).allKeysIn (bitsUnion (Nn stop).lastBitmap ((Nn stop).bitsOf (K (stop + 1)))) = true →
      stop = 0 ∧ (Nn 0).leaf = true) →
    UpLoopEnd c B X Nn depth stop w3 w2 S → KdJP c B top0 KO B w3.path w2 → w2.gh = w3.gh →
    (Nn stop).leaf = true → ¬ DelRoom c (K (stop + 1)) S →
    w2.gh.lookup (X stop) = some (g, 0) →
    WriterWP (appendDeleteKlong (X stop) stop (K (stop + 1))) c
      { w2 with trail := "up.stop-at-segment-leaf" :: w2.trail }
      (fun _ w' => DelInvJT c base KO B B w' ∧ PutBook c B top0 w' ∧ HtInv H B c w' ∧
        LiveHoleW (pre ++ [cv]) g 0 c base w')

set_option maxHeartbeats 6400000 in
/-- The upward delete that empties its leaf, not the space root, from the first
stratum's start with the live counts, whatever room its stop node has: the delete
calls `afterDelete key g 0`, (g, 0) the stop node's cached pair, from a state with
`DelInvJT`, `PutBook`, `HtInv` and `LiveHoleW key g 0`, given the full stop node's
split (`UpCascCallOK`). With room: l4d's `writerWP_del_upRoomLiveH`'s argument. -/
theorem writerWP_del_upCascCall (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B) (hbook : PutBook c B top0 w)
    (KO : KindOracle) (hvB : ViewIdsBelow B c.view) (hk : ViewKinds KO B c)
    (hb0 : Book B c w) (hi0 : KdInv KO B w)
    (hI : PutInv c base w) (hRO : RangeOrder (wNode c.p base w) c.i w.top.rootKey)
    (hICE : InnerChildrenExist (wNode c.p base w) c.i w.top.rootKey)
    (hkey : keyWf (pre ++ [cv]) = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hleafC : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true →
      bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
      n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = true ∧ L ≠ w.top.rootKey)
    (hsa2 : 2 ≤ c.p.splitAbove) (hp : MergeParamsOK c.p) (hICEk : ICEFromKinds c base KO B)
    (hm : c.p.merges = true) (hpos : 0 < c.i)
    (hJ2 : TakeJ2 c base B w) (hMF : ∀ x o, w.madeFor.lookup x = some o → o < B)
    (hLV : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true → ∀ y, (cv, y) ∈ n.liveAt c.i →
      wNode c.p base w y = none)
    (hLC : LiveCounts c.p (wNode c.p base w) c.i w.top.rootKey)
    {H : NodeId → Nat → Prop} (hvo : ViewHtOK H B c) (hkw : ViewKlongsWf c.p c.view)
    (hHi : HtInv H B c w) (hHwf : WriterKlongsWf w)
    (hC : UpCascCallOK c base KO B H)
    (Post : W → Prop) (hfresh : ∀ v, Post v → WriterWP fresh c v (fun _ v' => Post v'))
    (hA : ∀ g v, DelInvJT c base KO B B v → PutBook c B top0 v → HtInv H B c v →
      LiveHoleW (pre ++ [cv]) g 0 c base v →
      WriterWP (afterDelete (pre ++ [cv]) g 0) c v (fun _ v' => Post v')) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' => Post w') := by
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  refine writerWP_del_toLeafMKH c base hvc pre cv rk w
    (fun v => (KdJ c B top0 KO B v ∧ v.madeFor = w.madeFor) ∧ HtJ0 c H B v)
    (fun s f x v hJ hx => writerWP_mono (writerWP_and (writerWP_and
      (kdJ_descendLte c base B top0 hB KO B hvB hk s f x v hJ.1.1 hx)
      (writerWP_descendLte_madeFor s c f x v)) (htJ0_descendLte hvo hkw s f x v hJ.2 hx))
      (fun _ v' h => ⟨⟨h.1.1, h.1.2.trans hJ.1.2⟩, h.2⟩))
    (fun s fd L n v hJ hL hlk hleaf hfd =>
      ⟨⟨kdJ_pathAdd c base B top0 hB KO B hvB fd.c fd.y L n v hJ.1.1 hL hlk (kd_searchEq_mem n _ s fd hfd),
        hJ.1.2⟩, htJ0_pathAdd hvo s fd L n v hJ.2 hL hlk hleaf hfd⟩)
    ⟨⟨kdJ_start c base B top0 hB KO B hvB w ⟨hbook, hb0, hi0⟩, rfl⟩, htJ0_start hvo w hb0 hHi hHwf⟩
    hrk (hI.pathUntaken _) hI.wf Post hfresh ?_
  intro L n P w3 hL hn hnl hr03 hJ3h hlk3 hp3' hlinkP hXD hlkX
  have hJ3 := hJ3h.1
  have hH3 := hJ3h.2
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
      PutBook c B top0 w' → Book B c w' → KdInv KO B w' →
      DelInvT c base KO B w' := by
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
  have hallD := hall'
  have hX0 : nodeAt w.top.rootKey P 0 = w.top.rootKey := by simp [nodeAt]
  have hlinkK' := hlinkK
  refine takeJ2_deleteUpward_stepMBKGDS c base (fun i => nodeAt w.top.rootKey P i)
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
    (fun v => KdJP c B top0 KO B w3.path v ∧ v.gh = w3.gh) ⟨⟨hb3, rfl⟩, rfl⟩
    (fun s v hJ => ⟨kdJP_note c base B top0 hB KO B hvB hk _ s v hJ.1, hJ.2⟩)
    (fun x q k v hJ hx hq => writerWP_mono (writerWP_and
      (kdJP_takeBack c base B top0 hB KO B hvB hk _ x q k v hJ.1 hx) (writerWP_takeBack_gh x q k c v hq))
      (fun _ v' h => ⟨h.1, h.2.trans hJ.2⟩))
    (fun x v hJ hx => writerWP_mono (writerWP_and
      (kdJP_unlink c base B top0 hB KO B hvB hk _ x v hJ.1) (writerWP_unlink_gh x c v hx))
      (fun _ v' h => ⟨h.1, h.2.trans hJ.2⟩))
    (fun x d k v xn hJ hx hxn hDR => writerWP_mono (writerWP_and
      (kdJP_appendDeleteKlong c base B top0 hB KO B hvB hk _ x d k v hJ.1 hx)
      (writerWP_appendDeleteKlong_room_gh x d k xn c v hxn hDR))
      (fun _ v' h => ⟨h.1, h.2.trans hJ.2⟩)) ?_ ?_ ?_ ?_ ?_
  · -- an inner stop node with a bitmap: none, with the live counts at the start
    intro seg stop w' sn' hsD hbetween _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hNl
    exact (lebStop_false c base w hLC hm hI (fun i => nodeAt w.top.rootKey P i)
      (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
      (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length stop cv (by simp [nodeAt]) hXN hlinkK hall'
      hsD hbetween hNl).elim
  · intro stop w' sn' hsD hbetween ht htop hv hnodes hsn' hsl' hsw' hst' hlive' hread hfate hfJ hst hJv
      hCG hJw' hstp gs hs hgh
    obtain ⟨hagree, hsnw⟩ := hfr stop w' sn' hsD ht hnodes hsn'
    -- the stop node is a leaf
    cases hsl0 : ((wNode c.p base w (nodeAt w.top.rootKey P stop)).getD n).leaf with
    | false =>
      exfalso
      exact lebStop_false c base w hLC hm hI (fun i => nodeAt w.top.rootKey P i)
        (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
        (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length stop cv hX0 hXN hlinkK' hallD hsD hbetween hsl0
    | true =>
    have hRO' : RangeOrder (wNode c.p base w') c.i w'.top.rootKey := by
      rw [htop]
      exact rangeOrder_up_bitmap (wNode c.p base w3) (wNode c.p base w') c.i w3.top.rootKey _ _ _ stop
        P.length hsD hR3 hT3 (hreach3 stop (by omega)) (fun i _ h2 => hN3 i h2)
        (fun i h1 h2 => hlinkK i (by omega) h2) (fun i i' _ h2 _ h4 he => hdistP i i' h2 h4 he)
        hagree sn' hsnw hsl' (fun c' z h => (hlive' c' z).mp h)
    obtain ⟨⟨hkdj, hpp⟩, hgeq⟩ := hJw'
    have hgsub : ∀ e ∈ w3.gh, e ∈ w'.gh := fun e he => by rw [hgeq]; exact he
    have hDv := hD stop w' sn' id hsD ht htop hv hnodes hsn' hsl' hsw' hst'
      (fun c' z h => ⟨c', ((hlive' c' z).mp h).1, ((hlive' c' z).mp h).2, rfl⟩) hRO' hkdj.1 hkdj.2.1 hkdj.2.2
    -- the pair is the stop node's
    obtain ⟨g0, h0, hm0⟩ := kd_tag_of_lookup hb3.2.1 (hlkX stop (by omega))
    have hh0 : h0 = 0 := kd_h0 hb3.2.1 (hlkX stop (by omega)) hm0 hsl0
    subst hh0
    obtain ⟨v0, ⟨⟨hkdj0, _⟩, hgeq0⟩, hgh0⟩ := hgh
    rw [lookup_of_mem_nodup _ hkdj0.2.1.nodup _ _ (by rw [hgeq0]; exact hm0)] at hgh0
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hgh0)
    have hsn'l : sn'.leaf = true := by rw [hsl']; exact hsl0
    -- the heights at the call: the walk's start's, through the loop's frame
    have hHt' : HtInv H B c w' := by
      obtain ⟨S, hS1, _, hS3⟩ := hst
      refine htInv_upFrame B c base w3 w' (fun i => nodeAt w.top.rootKey P i)
        (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
        (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length stop hpos hH3.book hH3.inv hH3.wf hkdj.2.1
        hgsub hpp hJ23 hT3 (fun q qn hq s hs' => by rw [hr03.1] at hq; exact hI.times q qn hq s hs')
        hsD (by rw [hr03.2.1]; exact hX0) hlkX htk3 hdistP hreach3 hlinkK ht htop hnodes sn' hsn' hst' hlive'
        hfJ ⟨S, hS1, hS3⟩
    refine hA g0 w' ⟨hDv, hJv, hkdj.1.fresh.1⟩ hkdj.1 hHt' ?_
    -- the hole at the stop node
    have hroot' : w'.top.rootKey = w.top.rootKey := by rw [htop, hr03.2.1]
    have hagree' : ∀ u, u ≠ nodeAt w.top.rootKey P stop →
        (∀ i, stop < i → i ≤ P.length → u ≠ nodeAt w.top.rootKey P i) →
        wNode c.p base w' u = wNode c.p base w u := by
      intro u h1 h2; rw [hagree u h1 h2, hr03.1]
    have hE : LiveEdgesH c.p (wNode c.p base w') c.i w'.top.rootKey
        (fun y => y = nodeAt w.top.rootKey P stop) := by
      rw [hroot']
      by_cases hak : ((wNode c.p base w (nodeAt w.top.rootKey P stop)).getD n).allKeysIn
          (bitsUnion ((wNode c.p base w (nodeAt w.top.rootKey P stop)).getD n).lastBitmap
            (((wNode c.p base w (nodeAt w.top.rootKey P stop)).getD n).bitsOf
              (((P[stop + 1 - 1]?).bind (·.1)).getD 0))) = true
      · -- the stop node is the space root, a leaf, left empty
        obtain ⟨hs0, _⟩ := hstp hak
        have hroot0 : nodeAt w.top.rootKey P stop = w.top.rootKey := by rw [hs0]; simp [nodeAt]
        have hempty : sn'.liveAt c.i = [] := by
          cases hl' : sn'.liveAt c.i with
          | nil => rfl
          | cons q rest =>
            exfalso
            have hq : q ∈ sn'.liveAt c.i := by rw [hl']; exact List.mem_cons_self
            obtain ⟨hq1, hq2⟩ := (hlive' q.1 q.2).mp hq
            have hNt := hTimesR3 _ _ (hreach3 stop (by omega)) (hN3 stop (by omega))
            rw [KNode.liveAt_of_times _ c.i hNt] at hq1
            exact hq2 (allKeysIn_live_cv _ _ hak q.1 q.2 hq1)
        apply liveEdgesH_of_liveEdges
        rw [← hroot0]
        exact liveEdges_emptyRoot c.p _ c.i _ sn' hsnw hsn'l hempty
      · -- the stop node keeps a live klong
        have hak' := Bool.eq_false_iff.mpr hak
        obtain ⟨c1, z1, hc1, hz1⟩ := exists_live_of_keep _ _ hak'
        have hNt := hTimesR3 _ _ (hreach3 stop (by omega)) (hN3 stop (by omega))
        have hpos' : sn'.liveAt c.i ≠ [] := by
          intro h0
          have : (c1, z1) ∈ sn'.liveAt c.i :=
            (hlive' c1 z1).mpr ⟨by rw [KNode.liveAt_of_times _ c.i hNt]; exact hz1, hc1⟩
          rw [h0] at this
          cases this
        exact liveEdgesH_up c.p (wNode c.p base w) (wNode c.p base w') c.i w.top.rootKey
          (fun i => nodeAt w.top.rootKey P i) (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
          (fun i => ((P[i - 1]?).bind (·.1)).getD 0) stop P.length hsD hI.tree (hreachX stop (by omega))
          (fun i _ h2 => hXN i h2) (fun i h1 h2 => hlinkK i (by omega) h2)
          (fun i i' _ h2 _ h4 he => hdistP i i' h2 h4 he) hagree' sn' hsnw
          hsl' (fun c' z h => (hlive' c' z).mp h) hpos' (edges_of_liveCounts c.p _ _ _ hLC)
    refine liveHoleW_of_hole (pre ++ [cv]) g0 0 c base w' _ hE ?_
    have hs := segRd_of KO B c w' hkdj.2.1 hkdj.2.2 hk
    have hgL : rdG c w' (nodeAt w.top.rootKey P stop) = some (g0, 0) := by
      rw [rdG_of_lookup c w' _ sn' hsn']
      exact lookup_of_mem_nodup _ hkdj.2.1.nodup _ _ (hgsub _ hm0)
    refine holeAtW_stop c base hvc w w3 w' pre cv rk L n P stop g0 sn' hI.tree
      (fun y hy => hI.untaken y (tReach_reachS _ _ _ _ hy)) hI.wf hrk hL hn hnl hr03 hp3' hlinkP hXD hlkX
      hkey hsD hsl0 hnodes htop hsn' hsn'l ?_ hsw' hst' hs hgL
    intro z hz
    have hNt' : ∀ s, Klong.time s ∈ sn'.ks → s ≤ c.i := hst'
    have hz' : (((P[stop]?).bind (·.1)).getD 0, z) ∈ sn'.liveAt c.i := by
      rw [KNode.liveAt_of_times _ c.i hNt']; exact hz
    exact ((hlive' _ z).mp hz').2 (by simp)
  · -- the stop node full: the obligation, then the call
    intro stop w2 S hsD hbetween hLE hJw2G hsl hstp hDR gs hs hgh2
    obtain ⟨g0, h0, hm0⟩ := kd_tag_of_lookup hb3.2.1 (hlkX stop (by omega))
    have hh0 : h0 = 0 := kd_h0 hb3.2.1 (hlkX stop (by omega)) hm0 hsl
    subst hh0
    have hlook : w2.gh.lookup (nodeAt w.top.rootKey P stop) = some (g0, 0) := by
      rw [hJw2G.2]; exact lookup_of_mem_nodup _ hb3.2.1.nodup _ _ hm0
    rw [hlook] at hgh2
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hgh2)
    refine writerWP_mono (hC w w3 top0 pre cv rk (fun i => nodeAt w.top.rootKey P i)
      (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
      (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length stop w2 S g0 hvc hm hsa2 hp hvB hk hICEk hvo hkw hpos hB
      hbook hI hRO hICE hLC hJ2 hMF3 hr03 hJ3.1 hH3.inv hH3.wf hlen3 (by simp [nodeAt]) hkey hrk hvisw hpX hpK
      hlkX hXN hlinkK hne' hall' hnl' hkidsw hdepth hsD hbetween hstp hLE hJw2G.1 hJw2G.2 hsl hDR hlook) ?_
    rintro _ w' ⟨hD', hpb', hHt', hLH'⟩
    exact hA g0 w' hD' hpb' hHt' hLH'
  · -- an inner stop node, full: none
    intro seg stop w2 S hsD hbetween _ _ hsl
    exact (lebStop_false c base w hLC hm hI (fun i => nodeAt w.top.rootKey P i)
      (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
      (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length stop cv (by simp [nodeAt]) hXN hlinkK hall'
      hsD hbetween hsl).elim
  · -- LE-b at an inner stop node: none
    intro seg stop w2 S hsD hbetween _ _ hsl
    exact (lebStop_false c base w hLC hm hI (fun i => nodeAt w.top.rootKey P i)
      (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
      (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length stop cv (by simp [nodeAt]) hXN hlinkK hall'
      hsD hbetween hsl).elim

/-- `UpCascCallOK` at the contexts of the runs of R. -/
def UpCascCallRuns (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts (tx : Tx), Within p (ts ++ [tx]) → R (treeRun p ts) ts.length →
    UpCascCallOK (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base
      (htOracleOf p (treeRun p ts))

set_option maxHeartbeats 1600000 in
/-- The upward delete whose stop node has no room (`DelEmptyCascM`) in the delete
cases' form (bergdb 030-01, step 6), given the full stop node's split at the runs
(`UpCascCallRuns`): l4b's premise `hCasc` of `invGetScanOK_merges_noL4` reduced to the
full stop node. -/
theorem delCaseLive_emptyCasc (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove) (hp : MergeParamsOK p)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (hU : UpCascCallRuns p R) :
    DelCaseLive p R DelEmptyCascM := by
  intro ts tx hw hr z top _ htop ops op post hops r w hpre hS hJ key hop hPc Q hfresh hA
  obtain ⟨pre, cv, L0, n0, hop', hm, hK, hne0, hall0, P0, hlinkP0, hXD0, hP0, _⟩ := hPc
  subst hop'
  cases hop
  have hI : PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w := hS.1.1.1.1.1
  have hRO : RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey := hS.1.1.2
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  have hLr0 : L0 ≠ w.top.rootKey := by
    intro he
    have h1 := LinkedFrom.pathLen _ _ _ P0 hlinkP0 P0.length (Nat.le_refl _)
    rw [hXD0, he] at h1
    have := PathLen.depth_unique hI.tree _ _ _ h1 PathLen.root
    omega
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  have hICE := innerChildren_reachedR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
    (fun x hx => hI.untaken x (tReach_reachS _ _ _ _ hx))
  have hLV := leafVals_all hS.1.1.1.1.2 hkey hrk
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl (hRK _ _ hr)
      (hRP _ _ hr) hb hi.cache hun
  obtain ⟨hvo, hkw, _, _, _, hiw, hwfw⟩ := hS.2.1
  exact writerWP_del_upCascCall (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w tx.base top hB hbook
    _ hv hk hb0 hi0 hI hRO hICE hkey hrk
    (keyLeaf_all2 hK hrk (fun L n => bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
      n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = true ∧ L ≠ w.top.rootKey) ⟨hne0, hall0, hLr0⟩)
    hsa2 hp hICEk hm (by simp [ctxOf]) hJ hS.1.2 (fun L n hL hn hnl y hy => (hLV L n hL hn hnl y hy).1)
    hS.2.2 hvo hkw hiw hwfw (hU ts tx hw hr) Q hfresh hA

/-- TP7, TP10 and TP11 for Java's parameters without `l4` (bergdb 030-01, step 7), the
upward delete's premise narrowed to the full stop node's split (`UpCascCallRuns`): a
corollary of `invGetScanOK_merges_noL4` by `delCaseLive_emptyCasc`. -/
theorem invGetScanOK_merges_noL4U (p : Params) (hp : MergeParamsOK p)
    (hth : 2 ≤ p.theta ∨ p.theta = 0)
    (hF : MergeTailRuns p (RunTreeQ p (LatestQD p))) (hR3 : R3Calls p (RunTreeQ p (LatestQD p)))
    (hR4 : DelCaseLive p (RunTreeQ p (LatestQD p)) DelFullTimeCascM)
    (hU : UpCascCallRuns p (RunTreeQ p (LatestQD p))) :
    InvPreserved p ∧ GetOK p ∧ ScanOK p ∧ LatestGetOK p ∧ LatestScanOK p := by
  have hp' := hp
  unfold MergeParamsOK at hp'
  exact invGetScanOK_merges_noL4 p hp hth hF hR3 hR4
    (delCaseLive_emptyCasc p _ (by have := mergeParamsOK_M p hp; omega) (by omega) hp (fun _ _ h => h.1) (fun _ _ h => h.1.1)
      (fun _ _ h => h.2.2.1.2.2.1) hU)

end SIS.Tree
