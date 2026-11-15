/-
The first stratum's `hchk` (bergdb 025-05, step 7): the delete runs as its checked copy
at every reached delete, with no `htb`. The chain of `hchk`'s discharge
(`opDelChk5OKR_of_chk6A` from `OpDelChk6OKR`, `OpDelChk7OKR` and `OpDelChk8OKR`) asks
`DelHoleJ` at the calls of `afterDelete`: `DelInvJ` at p.fuel + 1, so the fit at the
delete's start, from `htb`. Here the calls carry `DelHoleJE` (route P's invariant with
the reference left open, from the tree's facts after the leaf's change), whose loops
need no fit; the leaf's change and the climb take their tree-facts forms, the walks the
kinds' books only. With it the first stratum holds with no premise of the heights:
`jointHtJ_reached1`.
-/
import SIS.Tree.StratumCasc

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- `OpDelChk6OKR` in the first stratum: the delete runs as its copy that checks
`DelHoleJE` and the merges' loop at each call of `afterDelete`. -/
def OpDelChk6TOKR (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
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
      putKvDelChk6 (DelHoleJE p ts tx top) key (ctxOf p ts) w = .ok (r', v)

/-- `OpDelChk7OKR` in the first stratum: `DelHoleJE` checked only at the upward
delete's call. -/
def OpDelChk7TOKR (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
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
      putKvDelChk7 (DelHoleJE p ts tx top) key (ctxOf p ts) w = .ok (r', v)

set_option maxHeartbeats 3200000 in
/-- `rwp_climb_of_J` in the first stratum (bergdb 025-05, step 7): no fit at the start and
no heights, the stop node's call given the tree's facts (`DelInvJT`), the cascade by
`UpCascJ2OKT`. -/
theorem rwp_climb_of_JT (aK aC1 aC2 : Key → Nat → Nat → M Unit) (c : Ctx) (base : View BVal)
    (pre : List Nat) (cv : Nat) (rk : NodeId) (w : W) (B : NodeId) (top0 : Top)
    (hB : PutBase c base B)
    (KO : KindOracle) (BK : NodeId) (hvB : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c)
    (hI : PutInv c base w) (hRO : RangeOrder (wNode c.p base w) c.i w.top.rootKey)
    (hICE : InnerChildrenExist (wNode c.p base w) c.i w.top.rootKey)
    (hkey : keyWf (pre ++ [cv]) = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hC : UpCascJ2OKT c base KO BK B)
    (hLC : LiveCounts c.p (wNode c.p base w) c.i w.top.rootKey)
    (hsa2 : 2 ≤ c.p.splitAbove) (hICEk : ICEFromKinds c base KO BK)
    (hm : c.p.merges = true) (hpos : 0 < c.i)
    (hJ2 : TakeJ2 c base B w) (hMF : ∀ x o, w.madeFor.lookup x = some o → o < B)
    (hLV : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true → ∀ y, (cv, y) ∈ n.liveAt c.i →
      wNode c.p base w y = none)
    (hK : ∀ g h v, DelInvJT c base KO BK B v → PutBook c B top0 v →
      RWP (aC1 (pre ++ [cv]) g h) (aC2 (pre ++ [cv]) g h) c v)
    (L : NodeId) (n : KNode) (P : List (Option Nat × NodeId)) (w3 : W)
    (hL : (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk) (hn : wNode c.p base w L = some n)
    (hnl : n.leaf = true) (hr03 : ReadsAs c.p base w w3)
    (hJ3 : KdJ c B top0 KO BK w3 ∧ w3.madeFor = w.madeFor)
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
  have hb3 := hJ3.1
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
  refine rwp_deleteUpwardP2_climbMBD aK aC1 aC2 c base (fun i => nodeAt w.top.rootKey P i)
    (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
    (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length cv pre rk B w3 hdepth hfuel hpos hpX hpK hlkX htk3
    (fun i hi => hTimesR3 _ _ (hreach3 i hi) (hN3 i hi))
    hdistP (by rw [hNnD]; exact hne) (by rw [hNnD]; exact hall) (by rw [hNnD]; exact hnl) hT3 hR3 hwf3 hRt3
    hTimesR3 hICE3 w3.next hfit3 hnovalAll3 hreach3
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
    exact hK gs hs w' ⟨hDv, hJv, hb'.1.1.fresh.1⟩ hb'.1.1
  · intro stop w2 S hsD hbetween hLE hJw2G hsl hDR gs hs
    obtain ⟨hJw2, _⟩ := hJw2G
    have hJv := kdJP_note c base B top0 hB KO BK hvB hk _ "up.stop-at-segment-leaf" w2 hJw2
    refine writerWP_mono (writerWP_and (hC w w3 top0 pre cv rk (fun i => nodeAt w.top.rootKey P i)
      (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
      (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length stop w2 _ S hm hLC hJ3.1 hlen3 hsa2 hvB hk hICEk
      (by simp [nodeAt]) hpos hB hI hRO hICE hr03 hkey hrk
      hvisw hpX hpK hlkX hXN hlinkK hne' hall' hnl' hdepth hsD hbetween hLE (Or.inr ⟨_, rfl⟩)
      hJv (Or.inl hsl) hDR hJ2 hMF3 hkidsw)
      (kdJP_appendDeleteKlong c base B top0 hB KO BK hvB hk _ _ stop _ _ hJv (hpX stop (by omega)))) ?_
    rintro _ w' ⟨hD', hJ'⟩
    exact hK gs hs w' hD' hJ'.1.1

set_option maxHeartbeats 3200000 in
/-- `OpDelChk8OKR` with no `htb` (`opDelChk8OKR_holdsA`'s route in the first stratum,
bergdb 025-05, step 7): at each call of `afterDelete` the state has `DelHoleJE`, where
the merges' loop runs as its checked copy (`rwp_mergeUp_of_JAE`). -/
theorem opDelChk8OKR_holdsT (p : Params) (R : Struct BVal → Time → Prop) (hM4 : 4 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove) (hm : p.merges = true)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRP : ∀ P t, R P t → PointersOK P)
    (hRK : ∀ P t, R P t → KindsAllOK p P)
    (hcap : 1 ≤ p.mergeMax) : OpDelChk8OKR p R := by
  intro ts tx hw hr z top hz htop pre key post hs r w hpre hI hRO hLC hH hJ r' v he
  have hM : 2 ≤ p.M := by omega
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop pre r w hpre
  have hG := putInvG_of_book _ _ tx.base top w hB hbook
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top pre (Op.del key :: post)
    hs r w hpre
  have hICE := innerChildren_reachedR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top pre (Op.del key :: post) hs r w
    hpre (fun x hx => hI.untaken x (tReach_reachS _ _ _ _ hx))
  have hSV := leafVals_reached p hM ts tx hw top pre (Op.del key :: post) hs r w hpre (hRP _ _ hr) (hRK _ _ hr)
  have hkey' : keyWf key = true := within_op_keyWf p ts tx hw pre _ post hs
  have hJw : TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w := hJ
  have hSB : tx.base ≤ w.next := hb0.next
  have hMF := stateOK_madeFor p hM4 R hRL ts tx hw hr z top hz htop pre (Op.del key :: post) hs r w hpre
  have hpos : 0 < (ctxOf p ts).i := by simp [ctxOf]
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl (hRK _ _ hr)
      (hRP _ _ hr) hb hi.cache hun
  have hC := upCascJ2OKT_holds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base
  obtain ⟨hvF, hkF, hICEkF⟩ := viewFacts_of_run p R hRP hRK ts tx hw hr
  have hmu : ∀ (k : Key) (g h : Nat) (v' : W),
      DelInvJAE (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base tx.base v' →
      PutBook (ctxOf p ts) tx.base top v' →
      RWP (afterDelete k g h) (afterDeleteJ (fun _ => True) k g h) (ctxOf p ts) v' :=
    fun k g h v' hJv hbv => rwp_afterDelete_T k g h _ v' (rwp_mergeUp_of_JAE k g (ctxOf p ts) _
      (viewCoherent_ctxOf p ts) _ tx.base hvF hkF hICEkF (by simpa [ctxOf] using hsa2) (by simpa [ctxOf] using hcap)
      hpos hB.good hB.wf top hB _ h false v' hJv hbv)
  rw [putKv_del_eqP, putKvDP_eqG, deleteUpwardP_eq2] at he
  unfold putKvDelChk8
  rw [putKvDP_eqG, deleteUpwardP_eq2]
  refine rwp_putKvG (ctxOf p ts) _ (viewCoherent_ctxOf p ts) w hI
    (fun v => KdJ (ctxOf p ts) tx.base top (kindOracleOf p (treeRun p ts)) tx.base v ∧ v.madeFor = w.madeFor)
    (fun s f x v hJ' hx => writerWP_mono (writerWP_and
      (kdJ_descendLte _ _ tx.base top hB _ tx.base hv hk s f x v hJ'.1 hx)
      (writerWP_descendLte_madeFor s _ f x v)) (fun _ v' h => ⟨h.1, h.2.trans hJ'.2⟩))
    (fun s fd L n v hJ' hL hlk _ hfd => ⟨kdJ_pathAdd _ _ tx.base top hB _ tx.base hv fd.c fd.y L n v hJ'.1 hL hlk
      (kd_searchEq_mem n _ s fd hfd), hJ'.2⟩)
    ⟨kdJ_start _ _ tx.base top hB _ tx.base hv w ⟨hbook, hb0, hi0⟩, rfl⟩ _ _ key ?_ _ he
  intro pre' cv rk L n P w3 hkey hrk hL hn hnl hr03 hJ3 hlk3 hp3' hlinkP hXD hlkX
  subst hkey
  refine rwp_trans (rwp_deleteUpwardP2_keeps afterDelete (afterDeleteJ (fun _ => True)) afterDelete (ctxOf p ts)
    L n P.length cv _ w3 hlk3 (DelHoleJE p ts tx top) ?_
    (fun g h v' hQ => hmu _ g h v' hQ.1 hQ.2)) ?_
  · have hJ3k := hJ3.1
    intro hne hkeep
    have hLV := leafVals_all hSV hkey' hrk
    have hLt : w.taken.contains L = false :=
      hI.pathUntaken _ (L, cv) (fromVisits_append _ _ _ pre' cv _ rk hrk _ hL)
    have hJ23 : TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w3 := takeJ2_of_readsAs _ _ _ w w3 hJw hr03
    by_cases hroom : DelRoom (ctxOf p ts) cv n
    · obtain ⟨a, hpx⟩ := path_last_of_toLeaf w w3 P L hp3' hXD
      refine writerWP_mono (writerWP_and (writerWP_and
        (writerWP_appendDeleteKlong_room_exactD L _ cv n _ _ hlk3 (hI.times L n hn) (hI.wf L n hn) hne hroom)
        (putBook_appendDeleteKlong L _ cv _ _ tx.base top hB _ hJ3k.1))
        (kd_appendDeleteKlong _ tx.base L P.length cv _ w3 hv hk hJ3k.2.1 hJ3k.2.2 a hpx)) ?_
      rintro _ v ⟨⟨⟨h1, h2, h3, _, h5, _, h7⟩, hbv⟩, hkv⟩
      obtain ⟨a1, a2, a3, a4⟩ := delInvFT_after_bitmap (ctxOf p ts) _ tx.base top hB w w3 v cv L n hI hRO hICE
        hn hnl hr03 hLt h1 h2 h3 h7 hbv
      refine ⟨delInvJAE_of_T _ _ _ _ _ v ⟨⟨a1, a2, a3, a4, ⟨tx.base, top, hB, hbv⟩, hkv.1, hkv.2.1⟩, ?_, ?_⟩, hbv⟩
      · exact takeJ2_after_bitmap (ctxOf p ts) _ tx.base w3 v cv L n hpos hJ23 hlk3
          (by rw [hr03.2.2.1]; exact hLt) (hI.times L n hn)
          (by rw [hr03.1, hr03.2.1]; exact keyLeaf_reached hI hrk L hL)
          (fun y hy => by rw [hr03.1]; exact (hLV L n hL hn hnl y hy).1)
          (fun y hy => by rw [hr03.2.2.2.1]; exact (hLV L n hL hn hnl y hy).2) h1 h2 h3 h7
      · rw [h5, hr03.2.2.2.2]; exact hSB
    · have hPOK := pathOK_of_toLeaf (ctxOf p ts) _ w w3 P n hI hr03 hp3' hlinkP hlkX
      have hJ2 := writerWP_appendDeleteKlong_full_j2_any (ctxOf p ts) _ tx.base hpos
        (delFullRootJ2OK_ctx p hsa2 ts tx.base) w3
        (putInv_of_readsAs _ _ w w3 hI hr03) (putInvG_of_readsAs _ _ w w3 hG hr03)
        (by rw [hr03.1, hr03.2.1]; exact hRO) hJ23 (by rw [hr03.2.2.2.2]; exact hSB) hsa2
        P.length _ _ _ hPOK cv n
        (by show (wNode _ _ w (nodeAt w.top.rootKey P P.length)).getD _ = n; rw [hXD, hn]; rfl)
        hnl hne hroom (fun y hy => by rw [hr03.1]; exact (hLV L n hL hn hnl y hy).1)
      simp only [hXD] at hJ2
      refine writerWP_mono (writerWP_and (writerWP_and (writerWP_appendDeleteKlong_full_delT (ctxOf p ts) _
        (viewCoherent_ctxOf p ts) _ tx.base (delFullRootStepOKT_ctx p ts) hsa2 hv hk hICEk w pre' cv rk tx.base top
        hB hI hRO hkey' hrk L n P w3 hL hn hnl hne hroom hr03 hJ3k hp3' hlinkP hXD hlkX) hJ2)
        (putBook_appendDeleteKlong L _ cv _ _ tx.base top hB _ hJ3k.1)) ?_
      rintro _ v ⟨⟨hv', hj⟩, hbv⟩
      exact ⟨delInvJAE_of_T _ _ _ _ _ v ⟨hv', hj.1, hj.2⟩, hbv⟩
  · by_cases hnc : bitsUnion n.lastBitmap (n.bitsOf cv) = n.lastBitmap ∨
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
    exact rwp_climb_of_JT _ _ _ (ctxOf p ts) _ pre' cv rk w tx.base top hB _ tx.base hv hk
      hI hRO hICE hkey' hrk hC hLC hsa2 hICEk hm hpos hJw hMF
      (fun L n hL hn hnl y hy => (hLV L n hL hn hnl y hy).1)
      (fun g h v hJv hbv => hmu _ g h v (delInvJAE_of_T _ _ _ _ _ v hJv) hbv)
      L n P w3 hL hn hnl hr03 hJ3 hp3' hlinkP hXD hlkX hne hall hLr


set_option maxHeartbeats 3200000 in
/-- `opDelChk7OKR_of_chk8` in the first stratum (bergdb 025-05, step 7): the upward delete's
call with `DelHoleJE`, no `htb` (`rwp_climb_of_JT`). -/
theorem opDelChk7TOKR_of_chk8 (p : Params) (R : Struct BVal → Time → Prop) (hM4 : 4 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove) (hm : p.merges = true)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRP : ∀ P t, R P t → PointersOK P)
    (hRK : ∀ P t, R P t → KindsAllOK p P) (h8 : OpDelChk8OKR p R) : OpDelChk7TOKR p R := by
  intro ts tx hw hr z top hz htop pre key post hs r w hpre hI hRO hLC hH hJ r' v he
  have h8' := h8 ts tx hw hr z top hz htop pre key post hs r w hpre hI hRO hLC hH hJ r' v he
  have hM : 2 ≤ p.M := by omega
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop pre r w hpre
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top pre (Op.del key :: post)
    hs r w hpre
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
  have hC := upCascJ2OKT_holds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base
  unfold putKvDelChk8 at h8'
  rw [putKvDP_eqG, deleteUpwardP_eq2] at h8'
  refine rwp_putKvG (ctxOf p ts) _ (viewCoherent_ctxOf p ts) w hI
    (fun v => KdJ (ctxOf p ts) tx.base top (kindOracleOf p (treeRun p ts)) tx.base v ∧ v.madeFor = w.madeFor)
    (fun s f x v hJ' hx => writerWP_mono (writerWP_and
      (kdJ_descendLte _ _ tx.base top hB _ tx.base hv hk s f x v hJ'.1 hx)
      (writerWP_descendLte_madeFor s _ f x v)) (fun _ v' h => ⟨h.1, h.2.trans hJ'.2⟩))
    (fun s fd L n v hJ' hL hlk _ hfd => ⟨kdJ_pathAdd _ _ tx.base top hB _ tx.base hv fd.c fd.y L n v hJ'.1 hL hlk
      (kd_searchEq_mem n _ s fd hfd), hJ'.2⟩)
    ⟨kdJ_start _ _ tx.base top hB _ tx.base hv w ⟨hbook, hb0, hi0⟩, rfl⟩ _ _ key ?_ _ h8'
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
  exact rwp_climb_of_JT _ _ _ (ctxOf p ts) _ pre' cv rk w tx.base top hB _ tx.base hv hk
    hI hRO hICE hkey' hrk hC hLC hsa2 hICEk hm hpos hJw hMF
    (fun L n hL hn hnl y hy => (hLV L n hL hn hnl y hy).1)
    (fun g h v hJv hbv => rwp_afterDeleteJ_true _ _ g h _ v ⟨delInvJAE_of_T _ _ _ _ _ v hJv, hbv⟩)
    L n P w3 hL hn hnl hr03 hJ3 hp3' hlinkP hXD hlkX hne hall hLr


set_option maxHeartbeats 3200000 in
/-- `opDelChk6OKR_of_chk7` in the first stratum (bergdb 025-05, step 7): the leaf's call with
`DelHoleJE`, no `htb`: the leaf's change by its tree-facts forms, the kinds' walk. -/
theorem opDelChk6TOKR_of_chk7T (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRP : ∀ P t, R P t → PointersOK P)
    (hRK : ∀ P t, R P t → KindsAllOK p P) (h7 : OpDelChk7TOKR p R) : OpDelChk6TOKR p R := by
  intro ts tx hw hr z top hz htop pre key post hs r w hpre hI hRO hL hH hJ r' v he
  have h7' := h7 ts tx hw hr z top hz htop pre key post hs r w hpre hI hRO hL hH hJ r' v he
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop pre r w hpre
  have hG := putInvG_of_book _ _ tx.base top w hB hbook
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top pre (Op.del key :: post)
    hs r w hpre
  have hICE := innerChildren_reachedR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top pre (Op.del key :: post) hs r w
    hpre (fun x hx => hI.untaken x (tReach_reachS _ _ _ _ hx))
  have hSV := leafVals_reached p hM ts tx hw top pre (Op.del key :: post) hs r w hpre (hRP _ _ hr) (hRK _ _ hr)
  have hkey' : keyWf key = true := within_op_keyWf p ts tx hw pre _ post hs
  have hJw : TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w := hJ
  have hSB : tx.base ≤ w.next := hb0.next
  have hpos : 0 < (ctxOf p ts).i := by simp [ctxOf]
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl (hRK _ _ hr)
      (hRP _ _ hr) hb hi.cache hun
  show putKvDP (afterDeleteJ (DelHoleJE p ts tx top)) key (ctxOf p ts) w = .ok (r', v)
  rw [putKvDP_eqG, deleteUpwardP_eq2]
  refine rwp_putKvG (ctxOf p ts) _ (viewCoherent_ctxOf p ts) w hI
    (KdJ (ctxOf p ts) tx.base top (kindOracleOf p (treeRun p ts)) tx.base)
    (fun s f x v hJ' hx => kdJ_descendLte _ _ tx.base top hB _ tx.base hv hk s f x v hJ' hx)
    (fun s fd L n v hJ' hL hlk _ hfd => kdJ_pathAdd _ _ tx.base top hB _ tx.base hv fd.c fd.y L n v hJ' hL hlk
      (kd_searchEq_mem n _ s fd hfd))
    (kdJ_start _ _ tx.base top hB _ tx.base hv w ⟨hbook, hb0, hi0⟩) _ _ key ?_ _ h7'
  intro pre' cv rk L n P w3 hkey hrk hL hn hnl hr03 hJ3 hlk3 hp3' hlinkP hXD hlkX
  subst hkey
  refine rwp_deleteUpwardP2_keeps _ _ _ (ctxOf p ts) L n P.length cv _ w3 hlk3
    (DelHoleJE p ts tx top) ?_ (fun g h v hQ => rwp_afterDeleteJ_true _ _ g h _ v hQ)
  intro hne hkeep
  have hLV := leafVals_all hSV hkey' hrk
  have hLt : w.taken.contains L = false :=
    hI.pathUntaken _ (L, cv) (fromVisits_append _ _ _ pre' cv _ rk hrk _ hL)
  have hJ23 : TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w3 := takeJ2_of_readsAs _ _ _ w w3 hJw hr03
  by_cases hroom : DelRoom (ctxOf p ts) cv n
  · obtain ⟨a, hpx⟩ := path_last_of_toLeaf w w3 P L hp3' hXD
    refine writerWP_mono (writerWP_and (writerWP_and
      (writerWP_appendDeleteKlong_room_exactD L _ cv n _ _ hlk3 (hI.times L n hn) (hI.wf L n hn) hne hroom)
      (putBook_appendDeleteKlong L _ cv _ _ tx.base top hB _ hJ3.1))
      (kd_appendDeleteKlong _ tx.base L P.length cv _ w3 hv hk hJ3.2.1 hJ3.2.2 a hpx)) ?_
    rintro _ v ⟨⟨⟨h1, h2, h3, _, h5, _, h7⟩, hbv⟩, hkv⟩
    obtain ⟨a1, a2, a3, a4⟩ := delInvFT_after_bitmap (ctxOf p ts) _ tx.base top hB w w3 v cv L n hI hRO hICE
      hn hnl hr03 hLt h1 h2 h3 h7 hbv
    refine ⟨delInvJAE_of_T _ _ _ _ _ v ⟨⟨a1, a2, a3, a4, ⟨tx.base, top, hB, hbv⟩, hkv.1, hkv.2.1⟩, ?_, ?_⟩, hbv⟩
    · exact takeJ2_after_bitmap (ctxOf p ts) _ tx.base w3 v cv L n hpos hJ23 hlk3
        (by rw [hr03.2.2.1]; exact hLt) (hI.times L n hn)
        (by rw [hr03.1, hr03.2.1]; exact keyLeaf_reached hI hrk L hL)
        (fun y hy => by rw [hr03.1]; exact (hLV L n hL hn hnl y hy).1)
        (fun y hy => by rw [hr03.2.2.2.1]; exact (hLV L n hL hn hnl y hy).2) h1 h2 h3 h7
    · rw [h5, hr03.2.2.2.2]; exact hSB
  · have hPOK := pathOK_of_toLeaf (ctxOf p ts) _ w w3 P n hI hr03 hp3' hlinkP hlkX
    have hJ2 := writerWP_appendDeleteKlong_full_j2_any (ctxOf p ts) _ tx.base hpos
      (delFullRootJ2OK_ctx p hsa2 ts tx.base) w3
      (putInv_of_readsAs _ _ w w3 hI hr03) (putInvG_of_readsAs _ _ w w3 hG hr03)
      (by rw [hr03.1, hr03.2.1]; exact hRO) hJ23 (by rw [hr03.2.2.2.2]; exact hSB) hsa2
      P.length _ _ _ hPOK cv n
      (by show (wNode _ _ w (nodeAt w.top.rootKey P P.length)).getD _ = n; rw [hXD, hn]; rfl)
      hnl hne hroom (fun y hy => by rw [hr03.1]; exact (hLV L n hL hn hnl y hy).1)
    simp only [hXD] at hJ2
    refine writerWP_mono (writerWP_and (writerWP_and (writerWP_appendDeleteKlong_full_delT (ctxOf p ts) _
      (viewCoherent_ctxOf p ts) _ tx.base (delFullRootStepOKT_ctx p ts) hsa2 hv hk hICEk w pre' cv rk tx.base top
      hB hI hRO hkey' hrk L n P w3 hL hn hnl hne hroom hr03 hJ3 hp3' hlinkP hXD hlkX) hJ2)
      (putBook_appendDeleteKlong L _ cv _ _ tx.base top hB _ hJ3.1)) ?_
    rintro _ v ⟨⟨hv', hj⟩, hbv⟩
    exact ⟨delInvJAE_of_T _ _ _ _ _ v ⟨hv', hj.1, hj.2⟩, hbv⟩


/-- `opDelChk5OKR_of_chk6A` in the first stratum: `afterDelete` runs as its checked copy
from `DelHoleJE` (`rwp_afterDelete_of_JAE`), with no `htb`. -/
theorem opDelChk5OKR_of_chk6T (p : Params) (R : Struct BVal → Time → Prop)
    (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRP : ∀ P t, R P t → PointersOK P)
    (hRK : ∀ P t, R P t → KindsAllOK p P) (h6 : OpDelChk6TOKR p R) : OpDelChk5OKR p R := by
  intro ts tx hw hr z top hz htop pre key post hs r w hpre hI hRO hL hH hJ r' v he
  have h6' := h6 ts tx hw hr z top hz htop pre key post hs r w hpre hI hRO hL hH hJ r' v he
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  obtain ⟨hv, hk, hICEk⟩ := viewFacts_of_run p R hRP hRK ts tx hw hr
  rw [putKvDelChk5_eq]
  refine rwp_putKvDP (afterDeleteJ (DelHoleJE p ts tx top)) afterDeleteChk (ctxOf p ts) ?_ key w _ h6'
  intro key' g h v'
  refine rwp_afterDeleteJ _ key' g h (ctxOf p ts) ?_ v'
  intro v'' hJ'' hmu
  exact rwp_afterDelete_of_JAE key' g h (ctxOf p ts) _ (viewCoherent_ctxOf p ts) (by simp [ctxOf]) _ tx.base hv hk
    hICEk (by simpa [ctxOf] using hsa2) (by simpa [ctxOf] using hcap) top hB v'' hJ''.1 hJ''.2 hmu

/-- `hchk` at the deletes of the runs of R with no `htb`: the delete runs as its checked
copy (`OpDelChk5OKR`). -/
theorem opDelChk5OKR_T (p : Params) (R : Struct BVal → Time → Prop) (hM4 : 4 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax) (hm : p.merges = true)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRP : ∀ P t, R P t → PointersOK P)
    (hRK : ∀ P t, R P t → KindsAllOK p P) : OpDelChk5OKR p R :=
  opDelChk5OKR_of_chk6T p R hsa2 hcap hRL hRP hRK
    (opDelChk6TOKR_of_chk7T p R (by omega) hsa2 hRL hRP hRK
      (opDelChk7TOKR_of_chk8 p R hM4 hsa2 hm hRL hRP hRK
        (opDelChk8OKR_holdsT p R hM4 hsa2 hm hRL hRP hRK hcap)))

/-- `hchk` in the joint induction's form (`OpDelChk2ORJ`) with no `htb`. -/
theorem opDelChk2ORJ_T (p : Params) (R : Struct BVal → Time → Prop) (hm : p.merges = true) (hM4 : 4 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRP : ∀ P t, R P t → PointersOK P)
    (hRK : ∀ P t, R P t → KindsAllOK p P) : OpDelChk2ORJ p R :=
  opDelChk2ORJ_of_chk5 p R hm hM4 hRL (opDelChk5OKR_T p R hM4 hsa2 hcap hm hRL hRP hRK)

/-- The first stratum (bergdb 025-05, step 7), whole: at every state that a transaction's
operations reach, `PutInv`, the ranges, the fill, the heights' walk, the writer's tree and
the take-back's node facts, from the put cases and the live counts, with no `htb`, no fit
and no heights' bound. -/
theorem jointHtJ_reached1 (p : Params) (R : Struct BVal → Time → Prop) (hm : p.merges = true)
    (hM : 2 ≤ p.M) (hM4 : 4 ≤ p.M) (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax)
    (hRB : BaseStartOK p R)
    (hRL : ∀ P t, R P t → RunLinksOK p P t) (hRT : ∀ P t, R P t → TreeAt p P t)
    (hRI : ∀ P t, R P t → InvOK p P t) (hRP : ∀ P t, R P t → PointersOK P)
    (hRK : ∀ P t, R P t → KindsAllOK p P) (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (hTp : OpCaseOK p R (QPut (QTree p)) AnyOp) (hPp : OpCaseOK p R (QPut (QPutInv p)) AnyOp)
    (hOp : OpCaseOK p R (QPut (QRange p)) AnyOp) (hLv : OpCaseOK p R (QLive p) AnyOp)
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
  jointHtJ_reachedS p R hm hM hM4 hsa2 hcap hRB hRL hRT hRI hRP hRK hRH hTp hPp hOp hLv
    (opDelChk2ORJ_T p R hm hM4 hsa2 hcap hRL hRP hRK) ts tx hw hr z top hz htop

end SIS.Tree
