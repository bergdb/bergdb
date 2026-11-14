/-
The upward delete with the fill at the delete's start (bergdb 024-12,
`LiveCounts`): with the merges on, the stop node of an upward delete is a
segment leaf (cost's `stopLeaf_of_liveCounts`), so LE-b never comes
(`lebStop_false`); `writerWP_del_emptyAnyMKL` and `writerWP_del_emptyAnyMJKL`
are the walks of `DelEmptyCascM` without LE-b's obligations.
-/
import SIS.Tree.DelStepsTree
import SIS.Tree.StopLeafLive

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The fill at a state of the transaction after the run ts. -/
def LiveCountsW (p : Params) (ts : List Tx) (w : W) : Prop :=
  LiveCounts p (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey

/-- `DelEmptyCascM` with the fill at the delete's start. -/
def DelEmptyCascML (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  DelEmptyCascM c base w op ∧ LiveCounts c.p (wNode c.p base w) c.i w.top.rootKey

/-- Case (4) with the fill at the operation's start. -/
def DelMergeCaseL (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  DelMergeCase c base w op ∧ LiveCounts c.p (wNode c.p base w) c.i w.top.rootKey


/-- With the fill at the delete's start and the merges on, the upward delete's
stop node is no inner node: the node below it empties. -/
theorem lebStop_false (c : Ctx) (base : View BVal) (w : W)
    (hLC : LiveCounts c.p (wNode c.p base w) c.i w.top.rootKey) (hm : c.p.merges = true)
    (hI : PutInv c base w) (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth stop cv : Nat)
    (hX0 : X 0 = w.top.rootKey)
    (hXN : ∀ i, i ≤ depth → wNode c.p base w (X i) = some (Nn i))
    (hlinkK : ∀ i, 0 < i → i ≤ depth → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (hall : (Nn depth).allKeysIn (bitsUnion (Nn depth).lastBitmap ((Nn depth).bitsOf cv)) = true)
    (hsD : stop < depth)
    (hbetween : ∀ i, stop < i → i < depth →
      (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true)
    (hsl : (Nn stop).leaf = false) : False := by
  rcases Nat.lt_or_ge (stop + 1) depth with h | h
  · exact stopLeaf_of_liveCounts c.p (wNode c.p base w) c.i w.top.rootKey hLC hm X Nn K depth hX0 hXN hlinkK
      stop (by omega) hsl (K (stop + 1 + 1)) (hI.times _ _ (hXN (stop + 1) (by omega)))
      (hbetween (stop + 1) (by omega) h)
  · have he : depth = stop + 1 := by omega
    subst he
    exact stopLeaf_of_liveCounts c.p (wNode c.p base w) c.i w.top.rootKey hLC hm X Nn K (stop + 1) hX0 hXN
      hlinkK stop (Nat.le_refl _) hsl cv (hI.times _ _ (hXN (stop + 1) (Nat.le_refl _))) hall

set_option maxHeartbeats 3200000 in
/-- The delete whose leaf, not the space root, empties, the merges on, whatever
room the stop node has: `writerWP_del_emptyRoomMK` on the walk cut at the stop
node's step (`writerWP_deleteUpward_stepJ`), the bitmap with the room of the
branch the writer takes proved, the cascade and LE-b from `UpCascOKF3` and
`UpLebOKF3`. -/
theorem writerWP_del_emptyAnyMKL (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
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
    (hC : UpCascOKF3 c base KO BK) (hLC : LiveCounts c.p (wNode c.p base w) c.i w.top.rootKey)
    (hsa2 : 2 ≤ c.p.splitAbove) (hICEk : ICEFromKinds c base KO BK)
    (hm : c.p.merges = true) (hpos : 0 < c.i)
    (hA : ∀ g h v, DelInvF3 c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK v →
      WriterWP (afterDelete (pre ++ [cv]) g h) c v (fun _ v' => DelInvF3 c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK v'))
    (hMU : ∀ g h merged v, DelInvF3 c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK v →
      WriterWP (mergeUp (pre ++ [cv]) g c.p.fuel h merged) c v
        (fun _ v' => DelInvF3 c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK v'))
    (hCR : ∀ seg v, DelInvF3 c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK v →
      WriterWP (collapseRoot (pre ++ [cv]) seg c.p.fuel) c v
        (fun _ v' => DelInvF3 c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK v'))
    (Post : W → Prop) (hfresh : ∀ v, Post v → WriterWP fresh c v (fun _ v' => Post v'))
    (hpost : ∀ v, DelInvF3 c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK v → Post v) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' => Post w') := by
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hJ0 : KdJ c B top0 KO BK w := ⟨hbook, hb0, hi0⟩
  refine writerWP_del_toLeafMK c base hvc pre cv rk w (KdJ c B top0 KO BK) hJ0
    (fun s f x v hJ hx => kdJ_descendLte c base B top0 hB KO BK hvB hk s f x v hJ hx)
    (fun s x L n v hJ hL hlk hkm => kdJ_pathAdd c base B top0 hB KO BK hvB s x L n v hJ hL hlk hkm)
    (kdJ_start c base B top0 hB KO BK hvB w hJ0) hrk (hI.pathUntaken _) hI.wf Post hfresh ?_
  intro L n P w3 hL hn hnl hr03 hb3 hlk3 hp3' hlinkP hXD hlkX
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
  refine writerWP_deleteUpward_stepJ c base (fun i => nodeAt w.top.rootKey P i)
    (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
    (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length cv pre (madeForBound w3) w3 Post
    (KdJP c B top0 KO BK w3.path) ⟨hb3, rfl⟩ (fun s v hJ => kdJP_note c base B top0 hB KO BK hvB hk _ s v hJ)
    (fun x q k v hJ hx => kdJP_takeBack c base B top0 hB KO BK hvB hk _ x q k v hJ hx)
    (fun x v hJ => kdJP_unlink c base B top0 hB KO BK hvB hk _ x v hJ)
    (madeFor_lt_bound w3) hdepth hpos hpX hpK hlkX htk3 (fun i hi => hTimesR3 _ _ (hreach3 i hi) (hN3 i hi))
    hdistP hne' hall' hwf3 hreach3 hm ?_ ?_ ?_
  · -- a segment leaf as the stop node
    intro stop w2 S hsD hbetween hLE hJ2 hsl gs hs
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
        (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length stop w2 _ S hsa2 hvB hk hICEk (by simp [nodeAt])
        hB hI hRO hF hICE hr03 hkey hrk
        hvisw hpX hpK hlkX hXNw hlinkK hne' hall' hnl' hdepth hsD hbetween hLE (Or.inr ⟨_, rfl⟩) hJv
        (Or.inl hsl) hDR)
        (fun _ w' hD' => writerWP_mono (hA gs hs w' hD') (fun _ w2 hD2 => hpost w2 hD2))
  · -- an inner stop node, its klong to the chain not the empty key's
    intro seg stop w2 S hsD hbetween hLE hJ2 hsl hK0 gs hs
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
        (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length stop w2 _ S hsa2 hvB hk hICEk (by simp [nodeAt])
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
the stop node's step (`takeJ2_deleteUpward_stepMBK`), the cascade and LE-b from
`UpCascJ2OKF3` and `UpLebJ2OKF3`. -/
theorem writerWP_del_emptyAnyMJKL (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
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
    (hC : UpCascJ2OKF3 c base KO BK B) (hLC : LiveCounts c.p (wNode c.p base w) c.i w.top.rootKey)
    (hsa2 : 2 ≤ c.p.splitAbove) (hICEk : ICEFromKinds c base KO BK)
    (hm : c.p.merges = true) (hpos : 0 < c.i)
    (hJ2 : TakeJ2 c base B w) (hMF : ∀ x o, w.madeFor.lookup x = some o → o < B)
    (hLV : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true → ∀ y, (cv, y) ∈ n.liveAt c.i →
      wNode c.p base w y = none)
    (hA : ∀ g h v, DelInvJF3 c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK B v →
      WriterWP (afterDelete (pre ++ [cv]) g h) c v (fun _ v' => DelInvJF3 c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK B v'))
    (hMU : ∀ g h merged v, DelInvJF3 c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK B v →
      WriterWP (mergeUp (pre ++ [cv]) g c.p.fuel h merged) c v
        (fun _ v' => DelInvJF3 c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK B v'))
    (hCR : ∀ seg v, DelInvJF3 c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK B v →
      WriterWP (collapseRoot (pre ++ [cv]) seg c.p.fuel) c v
        (fun _ v' => DelInvJF3 c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK B v')) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' => TakeJ2 c base B w') := by
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  refine writerWP_del_toLeafMK c base hvc pre cv rk w (fun v => KdJ c B top0 KO BK v ∧ v.madeFor = w.madeFor)
    ⟨⟨hbook, hb0, hi0⟩, rfl⟩
    (fun s f x v hJ hx => writerWP_mono (writerWP_and (kdJ_descendLte c base B top0 hB KO BK hvB hk s f x v hJ.1 hx)
      (writerWP_descendLte_madeFor s c f x v)) (fun _ v' h => ⟨h.1, h.2.trans hJ.2⟩))
    (fun s x L n v hJ hL hlk hkm => ⟨kdJ_pathAdd c base B top0 hB KO BK hvB s x L n v hJ.1 hL hlk hkm, hJ.2⟩)
    ⟨kdJ_start c base B top0 hB KO BK hvB w ⟨hbook, hb0, hi0⟩, rfl⟩ hrk (hI.pathUntaken _) hI.wf
    (TakeJ2 c base B) (fun v hv => by unfold fresh; wpSimplify; exact hv) ?_
  intro L n P w3 hL hn hnl hr03 hJ3 hlk3 hp3' hlinkP hXD hlkX
  have hb3 := hJ3.1
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
  refine takeJ2_deleteUpward_stepMBK c base (fun i => nodeAt w.top.rootKey P i)
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
    (KdJP c B top0 KO BK w3.path) ⟨hb3, rfl⟩ (fun s v hJ => kdJP_note c base B top0 hB KO BK hvB hk _ s v hJ)
    (fun x q k v hJ hx => kdJP_takeBack c base B top0 hB KO BK hvB hk _ x q k v hJ hx)
    (fun x v hJ => kdJP_unlink c base B top0 hB KO BK hvB hk _ x v hJ)
    (fun x d k v hJ hx => kdJP_appendDeleteKlong c base B top0 hB KO BK hvB hk _ x d k v hJ hx) ?_ ?_ ?_ ?_ ?_
  · intro seg stop w' sn' hsD hbetween ht htop hv hnodes hsn' hsl' hsw' hst' hlive' hread _ _ _ hJv _ hb' gs hs
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
    exact writerWP_mono (hCR seg w1 hD1) (fun _ w2 hD2 => hD2.2.1)
  · intro stop w' sn' hsD hbetween ht htop hv hnodes hsn' hsl' hsw' hst' hlive' hread _ _ _ hJv _ hb' gs hs
    obtain ⟨hagree, hsnw⟩ := hfr stop w' sn' hsD ht hnodes hsn'
    have hRO' : RangeOrder (wNode c.p base w') c.i w'.top.rootKey := by
      rw [htop]
      exact rangeOrder_up_bitmap (wNode c.p base w3) (wNode c.p base w') c.i w3.top.rootKey _ _ _ stop
        P.length hsD hR3 hT3 (hreach3 stop (by omega)) (fun i _ h2 => hN3 i h2)
        (fun i h1 h2 => hlinkK i (by omega) h2) (fun i i' _ h2 _ h4 he => hdistP i i' h2 h4 he)
        hagree sn' hsnw hsl' (fun c' z h => (hlive' c' z).mp h)
    have hDv := hD stop w' sn' id hsD ht htop hv hnodes hsn' hsl' hsw' hst'
      (fun c' z h => ⟨c', ((hlive' c' z).mp h).1, ((hlive' c' z).mp h).2, rfl⟩) hRO' hb'.1.1 hread
    exact writerWP_mono (hA gs hs w' ⟨⟨hDv, hb'.1.2.1, hb'.1.2.2⟩, hJv, hb'.1.1.fresh.1⟩) (fun _ w2 hD2 => hD2.2.1)
  · intro stop w2 S hsD hbetween hLE hJw2 hsl hDR gs hs
    exact writerWP_mono (hC w w3 top0 pre cv rk (fun i => nodeAt w.top.rootKey P i)
      (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
      (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length stop w2 _ S hsa2 hvB hk hICEk
      (by simp [nodeAt]) hpos hB hI hRO hF hICE hr03 hkey hrk
      hvisw hpX hpK hlkX hXN hlinkK hne' hall' hnl' hdepth hsD hbetween hLE (Or.inr ⟨_, rfl⟩)
      (kdJP_note c base B top0 hB KO BK hvB hk _ "up.stop-at-segment-leaf" w2 hJw2) (Or.inl hsl) hDR hJ2 hMF3 hkidsw)
      (fun _ w' hD' => writerWP_mono (hA gs hs w' hD') (fun _ w2 hD2 => hD2.2.1))
  · intro seg stop w2 S hsD hbetween hLE hJw2 hsl hK0 hDR gs hs
    refine writerWP_mono (hC w w3 top0 pre cv rk (fun i => nodeAt w.top.rootKey P i)
      (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
      (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length stop w2 _ S hsa2 hvB hk hICEk
      (by simp [nodeAt]) hpos hB hI hRO hF hICE hr03 hkey hrk
      hvisw hpX hpK hlkX hXN hlinkK hne' hall' hnl' hdepth hsD hbetween hLE (Or.inl rfl) hJw2
      (Or.inr hK0) hDR hJ2 hMF3 hkidsw) ?_
    intro _ w' hD'
    refine writerWP_mono (hMU gs hs false w' hD') ?_
    intro _ w1 hD1
    exact writerWP_mono (hCR seg w1 hD1) (fun _ w2 hD2 => hD2.2.1)
  · intro seg stop w2 S hsD hbetween hLE hJw2 hsl hK0 hsm gs hs
    exact (lebStop_false c base w hLC hm hI (fun i => nodeAt w.top.rootKey P i)
      (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
      (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length stop cv (by simp [nodeAt]) hXN hlinkK hall'
      hsD hbetween hsl).elim

theorem delStepsCaseOKF3_emptyCascLC (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts))
    (hC : ∀ ts BK, UpCascOKF3 (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) BK)
    (hLC : StateOK p R (fun ts _ w => LiveCountsW p ts w)) :
    DelStepsCaseOKF3 p R DelEmptyCascM := by
  intro ts tx hw hr z top hz htop ops op post hops r w hpre hI hRO hF key hop hPc hA hMU hCR
  have hLCw := hLC ts tx hw hr z top hz htop ops (op :: post) hops r w hpre
  obtain ⟨pre, cv, L0, n0, hop', hm, hK, hne0, hall0, P0, hP0, hX0, hl0, _⟩ := hPc
  subst hop'
  cases hop
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
  refine writerWP_del_emptyAnyMKL (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w tx.base top hB hbook
    _ tx.base hv hk hb0 hi0 hI hRO hF hICE hkey hrk (keyLeaf_all2 hK hrk _ ⟨hne0, hall0, hLr⟩)
    (hC ts tx.base) hLCw (by simpa [ctxOf] using hsa2) hICEk hm (by simp [ctxOf]) hA hMU hCR
    _ (fun v hv' => by unfold fresh; wpSimplify; exact hv') ?_
  intro v hv' hFv key' hk'
  have := runGet_of_delInvF p ts w v (pre ++ [cv]) hv'.1 hI hF hFv key' hk'
  simpa [Op.key, Op.value] using this

/-- The take-back of a delete whose leaf empties below the space root with a
stop node without room (`DelEmptyCascM`), on the F3 route, from `UpCascJ2OKF3`
and `UpLebJ2OKF3`. -/
theorem delStepsCaseJ2OKF3_emptyCascRLC (p : Params) (R : Struct BVal → Time → Prop)
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
    (hC : ∀ ts BK B, UpCascJ2OKF3 (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) BK B)
    (hLC : StateOK p R (fun ts _ w => LiveCountsW p ts w)) :
    DelStepsCaseJ2OKF3 p R S DelEmptyCascM := by
  intro ts tx hw hr z top hz htop ops op post hops r w hpre hS hJ key hop hPc hA hMU hCR
  have hLCw := hLC ts tx hw hr z top hz htop ops (op :: post) hops r w hpre
  obtain ⟨pre, cv, L0, n0, hop', hm, hK, hne0, hall0, P0, hP0, hX0, hl0, _⟩ := hPc
  subst hop'
  cases hop
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
  exact writerWP_del_emptyAnyMJKL (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w tx.base top hB hbook
    _ tx.base hv hk hb0 hi0
    hI (hSR ts tx w hS) (hSF ts tx w hS) hICE hkey hrk (keyLeaf_all2 hK hrk _ ⟨hne0, hall0, hLr⟩)
    (hC ts tx.base tx.base) hLCw (by simpa [ctxOf] using hsa2) hICEk hm
    (by simp [ctxOf]) hJ (hSM ts tx w hS) (fun L n hL hn hnl y hy => (hLV L n hL hn hnl y hy).1) hA hMU hCR

theorem delStepsCaseQd_emptyCascL (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (hC : ∀ ts BK, UpCascOKF3 (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) BK)
    : DelStepsCaseQd p R DelEmptyCascML := by
  intro ts tx hw hr z top _ htop ops op post hops r w hpre hI hRO hF key hop hPcL hA hMU hCR
  obtain ⟨hPc, hLCw⟩ := hPcL
  obtain ⟨pre, cv, L0, n0, hop', hm, hK, hne0, hall0, P0, hP0, hX0, hl0, _⟩ := hPc
  subst hop'
  cases hop
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
  refine writerWP_del_emptyAnyMKL (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w tx.base top hB hbook
    _ tx.base hv hk hb0 hi0 hI hRO hF hICE hkey hrk (keyLeaf_all2 hK hrk _ ⟨hne0, hall0, hLr⟩)
    (hC ts tx.base) hLCw (by simpa [ctxOf] using hsa2) hICEk hm (by simp [ctxOf]) hA hMU hCR
    (QdW p ts) (fun v hv' => qdW_fresh p ts v hv') (fun v hv' => ⟨hv'.1.1, hv'.1.2.2.1⟩)


/-- `DelStepsOKF3` with the fill at every operation's start (`hLC`): LE-b never
comes, so no LE-b obligation and no `UpLebFitsOK`; open are `UpUnlinkTreeOK`,
`UpCascFitsOK` and the heights at every run. -/
theorem delStepsOKF3_of_open13 (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts))
    (hRK : ∀ P t, R P t → KindsAllOK p P) (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (hht : OpHtDelOKUnder p R) (hdel : TakeBelowFuelDelOK p)
    (hU : ∀ ts, UpUnlinkTreeOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hFit : ∀ ts BK, UpCascFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) BK)
    (hLC : StateOK p R (fun ts _ w => LiveCountsW p ts w)) :
    DelStepsOKF3 p R :=
  delStepsOKF3_of_cases p R (delStepsCaseOKF3_noLeaf p R) (delStepsCaseOKF3_noop p R)
    (delStepsCaseOKF3_or p R _ _ _ delEmptyM_split (delStepsCaseOKF3_emptyRoom p R hM hRL hP)
      (delStepsCaseOKF3_or p R _ _ _ delEmptyOther_split (delStepsCaseOKF3_emptyRoot p R hM hsa2 hRL hP)
        (delStepsCaseOKF3_emptyCascLC p R hM hsa2 hRL hP
          (fun ts BK => upCascOKF3_of_parts3 _ _ _ _ (hU ts) (hFit ts BK)) hLC)))
    (delStepsCaseOKF3_room p R hM hRL hP)
    (delStepsCaseOKF3_fullH p R hM hsa2 hRL hP hRK hRH hht hdel (fun ts => delFullRootStepOK_ctx p ts))

/-- `DelStepsJ2OKF3` (the F3 route over R's pointers and kinds) with the fill
at every operation's start (`hLC`): open are `UpUnlinkTreeOK`, `UpCascFitsOK`,
the heights at every run and the S inputs. -/
theorem delStepsJ2OKF3_of_openR8 (p : Params) (R : Struct BVal → Time → Prop)
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
    (hFit : ∀ ts BK, UpCascFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) BK)
    (hLC : StateOK p R (fun ts _ w => LiveCountsW p ts w)) :
    DelStepsJ2OKF3 p R S :=
  delStepsJ2OKF3_of_cases p R S (delStepsCaseJ2OKF3_noLeaf p R S hSI) (delStepsCaseJ2OKF3_noop p R S hSI)
    (delStepsCaseJ2OKF3_or p R S _ _ _ delEmptyM_split
      (delStepsCaseJ2OKF3_emptyRoomR p R S hM hRL hRP hRK hSI hSV hSR hSF hSM)
      (delStepsCaseJ2OKF3_or p R S _ _ _ delEmptyOther_split
        (delStepsCaseJ2OKF3_emptyRootR p R S hM hsa2 hRL hRP hRK hSI hSV hSB hSR)
        (delStepsCaseJ2OKF3_emptyCascRLC p R S hM hsa2 hRL hRP hRK hSI hSV hSR hSF hSM
          (fun ts BK B => upCascJ2OKF3_of_parts3 _ _ _ _ B (hU ts) (hFit ts BK)) hLC)))
    (delStepsCaseJ2OKF3_roomR p R S hM hRL hRP hRK hSI hSV hSB hSR hSF)
    (delStepsCaseJ2OKF3_fullRH p R S hM hsa2 hRL hRP hRK hSI hSV hSB hSR hSF hRH hht hdel)

/-- The delete's steps with the post `QdW`, the merges on, the fill at the
operation's start in the case. -/
def DelStepsQdL (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  DelStepsCaseQd p R (fun c base w op => (∃ key, op = .del key ∧ c.p.merges = true) ∧
    LiveCounts c.p (wNode c.p base w) c.i w.top.rootKey)

/-- `DelStepsQdL` under the reading's premises without LE-b's: open are
`UpUnlinkTreeOK`, `UpCascFitsOK` and the heights at every run. -/
theorem delStepsQdL_of_openR (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (hht : OpHtDelOKUnder p R) (hdel : TakeBelowFuelDelOK p)
    (hU : ∀ ts, UpUnlinkTreeOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hFit : ∀ ts BK, UpCascFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) BK) :
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
      · exact delStepsCaseQd_emptyCascL p R hM hsa2 hRL hRP hRK
          (fun ts BK => upCascOKF3_of_parts3 _ _ _ _ (hU ts) (hFit ts BK))
          ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop (hop ▸ ⟨h2, hLCw⟩) hA hMU hCR
  · exact delStepsCaseQd_room p R hM hRL hRP hRK ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF
      key hop (hop ▸ h) hA hMU hCR
  · exact delStepsCaseQd_fullH p R hM hsa2 hRL hRP hRK hRH hht hdel (fun ts => delFullRootStepOK_ctx p ts)
      ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop (hop ▸ h) hA hMU hCR


/-- The delete with the merges on (case (4)) keeps `QdW`: `DelStepsQd` with the
merges' loop (`writerWP_mergeUp_delF3`) and root collapse
(`writerWP_collapseRoot_delF4`, `writerWP_afterDelete_delF4`), the fuel at the
operation's start from `TxSegFitsOK`. -/
theorem opCaseOK_qdW_delMergeRL (p : Params) (R : Struct BVal → Time → Prop) (hS : DelStepsQdL p R)
    (hM : ∀ ts, MergeStepOKF3 (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hC : ∀ ts, CollapseStepOKF4 (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P) (hfit : TxSegFitsOK p R) :
    OpCaseOK p R (fun ts _ _ w' => QdW p ts w') DelMergeCaseL := by
  have hf2 : 2 ≤ p.fuel + 1 := by unfold Params.fuel; omega
  intro ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hP
  obtain ⟨⟨key, hop, hmerges⟩, hLCw⟩ := hP
  have hF0 := hfit ts tx hw hr z top hz htop pre (op :: post) hops r w hpre
  have hwts : Within p ts := by
    have := within_take p (ts ++ [tx]) hw ts.length
    simpa using this
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
  exact hS ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF0 key hop ⟨⟨key, hop, hmerges⟩, hLCw⟩
    (fun g h v hv' => writerWP_afterDelete_delF4 key g h (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hM ts) (hC ts) _ _ hv hk hICEk hsa2 hcap w key v hv')
    (fun g h merged v hv' => writerWP_mergeUp_delF3 key g (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hM ts) _ _ hv hk hICEk hsa2 hcap w key p.fuel h merged v hv')
    (fun seg v hv' => writerWP_collapseRoot_delF4 key seg (ctxOf p ts) _ (viewCoherent_ctxOf p ts)
      (p.fuel + 1) hf2 (hC ts) w key _ _ hv hk hICEk hsa2 v hv')

/-- `t4`, `i4` and `r4` with the fill at the operation's start (`DelMergeCaseL`): the delete with the merges on keeps the writer's tree
(`QTree`), `PutInv` (`QPutInv`) and the walk's ranges (`QRange`). -/
theorem opCaseOK_treeInvRange_delMergeRL (p : Params) (R : Struct BVal → Time → Prop) (hS : DelStepsQdL p R)
    (hM : ∀ ts, MergeStepOKF3 (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hC : ∀ ts, CollapseStepOKF4 (ctxOf p ts) (viewOf (treeRun p ts)) (p.fuel + 1))
    (hsa2 : 2 ≤ p.splitAbove) (hcap : 1 ≤ p.mergeMax)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P) (hfit : TxSegFitsOK p R) :
    OpCaseOK p R (QTree p) DelMergeCaseL ∧ OpCaseOK p R (QPutInv p) DelMergeCaseL ∧
      OpCaseOK p R (QRange p) DelMergeCaseL := by
  have h := opCaseOK_qdW_delMergeRL p R hS hM hC hsa2 hcap hRP hRK hfit
  refine ⟨?_, ?_, ?_⟩
  · intro ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hP
    exact writerWP_mono (h ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hP)
      (fun _ w' hq => hq.1.tree)
  · intro ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hP
    exact writerWP_mono (h ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hP)
      (fun _ w' hq _ => hq.1)
  · intro ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hP
    exact writerWP_mono (h ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hP)
      (fun _ w' hq _ => hq.2)

end SIS.Tree
