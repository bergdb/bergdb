/-
The reading of a delete whose leaf empties below the space root, the merges on,
whatever room its stop node has (bergdb 024-12, case (4), `DelEmptyCascM`): the
stop node's bitmap with the room of the branch the writer takes is proved
(`writerWP_upStop_bitmapD`); its bitmap into a full node (`handleFull`, the
cascade) and its LE-b are named obligations, `UpCascOKF3` and `UpLebOKF3`.
-/
import SIS.Tree.DelStepsUpStop
import SIS.Tree.DelStepsEmptyRoot

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- Obligation (the stop node's bitmap into a full node, the cascade): at the
upward loop's end state w2 (`UpLoopEnd`, the walk from w3, the state at the
key's leaf, which reads as the delete's start state w), the stop node X stop's
bitmap for its klong to the chain without the room of the branch the writer
takes (`¬ DelRoom`) puts the state into `DelInvF3`. MB bounds the ids the
transaction's nodes replaced (`madeFor`). The proof is to take the writer's
tree after the loop as a tree (`UpUnlinkOK`, the take-back's). -/
def UpCascOKF3 (c : Ctx) (base : View BVal) (KO : KindOracle) (BK : NodeId) : Prop :=
  ∀ (w w3 : W) (B MB : NodeId) (top0 : Top) (pre : List Nat) (cv : Nat) (rk : NodeId)
    (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth stop : Nat) (w2 v : W) (S : KNode),
    PutBase c base B → PutInv c base w → RangeOrder (wNode c.p base w) c.i w.top.rootKey →
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
      (fun _ w' => DelInvF3 c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK w')

/-- Obligation (the stop node's LE-b, any room): `UpCascOKF3`'s premises for an
inner stop node whose klong to the chain is the empty key's; its LE-b
(`emptyKeyNext`) puts the state into `DelInvF3`. -/
def UpLebOKF3 (c : Ctx) (base : View BVal) (KO : KindOracle) (BK : NodeId) : Prop :=
  ∀ (w w3 : W) (B MB : NodeId) (top0 : Top) (pre : List Nat) (cv : Nat) (rk : NodeId)
    (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth stop : Nat) (w2 : W) (S : KNode),
    PutBase c base B → PutInv c base w → RangeOrder (wNode c.p base w) c.i w.top.rootKey →
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
    UpLoopEnd c MB X Nn depth stop w3 w2 S → KdJP c B top0 KO BK w3.path w2 →
    (Nn stop).leaf = false → K (stop + 1) = 0 → S.smallestLive = some 0 →
    WriterWP (emptyKeyNext (X stop) stop) c w2
      (fun _ w' => DelInvF3 c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK w')

set_option maxHeartbeats 3200000 in
/-- The delete whose leaf, not the space root, empties, the merges on, whatever
room the stop node has: `writerWP_del_emptyRoomMK` on the walk cut at the stop
node's step (`writerWP_deleteUpward_stepJ`), the bitmap with the room of the
branch the writer takes proved, the cascade and LE-b from `UpCascOKF3` and
`UpLebOKF3`. -/
theorem writerWP_del_emptyAnyMK (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
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
    (hC : UpCascOKF3 c base KO BK) (hLb : UpLebOKF3 c base KO BK)
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
        (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length stop w2 _ S hB hI hRO hF hICE hr03 hkey hrk
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
        (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length stop w2 _ S hB hI hRO hF hICE hr03 hkey hrk
        hvisw hpX hpK hlkX hXNw hlinkK hne' hall' hnl' hdepth hsD hbetween hLE (Or.inl rfl) hJ2
        (Or.inr hK0) hDR) ?_
      intro _ w' hD'
      refine writerWP_mono (hMU gs hs false w' hD') ?_
      intro _ w1 hD1
      exact writerWP_mono (hCR seg w1 hD1) (fun _ w2 hD2 => hpost w2 hD2)
  · -- LE-b at an inner stop node
    intro seg stop w2 S hsD hbetween hLE hJ2 hsl hK0 hsm gs hs
    refine writerWP_mono (hLb w w3 B (madeForBound w3) top0 pre cv rk (fun i => nodeAt w.top.rootKey P i)
      (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
      (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length stop w2 S hB hI hRO hF hICE hr03 hkey hrk
      hvisw hpX hpK hlkX hXNw hlinkK hne' hall' hnl' hdepth hsD hbetween hLE hJ2 hsl hK0 hsm) ?_
    intro _ w' hD'
    refine writerWP_mono (hMU gs hs false w' hD') ?_
    intro _ w1 hD1
    exact writerWP_mono (hCR seg w1 hD1) (fun _ w2 hD2 => hpost w2 hD2)

/-- The reading of a delete whose leaf empties below the space root with a stop
node without room (`DelEmptyCascM`), on the F3 route, from `UpCascOKF3` and
`UpLebOKF3`. -/
theorem delStepsCaseOKF3_emptyCasc (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts))
    (hC : ∀ ts BK, UpCascOKF3 (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) BK)
    (hLb : ∀ ts BK, UpLebOKF3 (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) BK) :
    DelStepsCaseOKF3 p R DelEmptyCascM := by
  intro ts tx hw hr z top _ htop ops op post hops r w hpre hI hRO hF key hop hPc hA hMU hCR
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
  refine writerWP_del_emptyAnyMK (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w tx.base top hB hbook
    _ tx.base hv hk hb0 hi0 hI hRO hF hICE hkey hrk (keyLeaf_all2 hK hrk _ ⟨hne0, hall0, hLr⟩)
    (hC ts tx.base) (hLb ts tx.base) hm (by simp [ctxOf]) hA hMU hCR
    _ (fun v hv' => by unfold fresh; wpSimplify; exact hv') ?_
  intro v hv' hFv key' hk'
  have := runGet_of_delInvF p ts w v (pre ++ [cv]) hv'.1 hI hF hFv key' hk'
  simpa [Op.key, Op.value] using this

/-- `DelStepsOKF3` with every case proved but the stop node's cascade and LE-b
of the upward delete (`UpCascOKF3`, `UpLebOKF3`), the fuel after a full leaf's
split (`DelFullFitsOK`, cost's). -/
theorem delStepsOKF3_of_open5 (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts))
    (hC : ∀ ts BK, UpCascOKF3 (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) BK)
    (hLb : ∀ ts BK, UpLebOKF3 (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) BK)
    (hFits : ∀ ts, DelFullFitsOK (ctxOf p ts) (viewOf (treeRun p ts))) : DelStepsOKF3 p R :=
  delStepsOKF3_of_open4 p R hM hsa2 hRL hP (delStepsCaseOKF3_emptyCasc p R hM hRL hP hC hLb) hFits

end SIS.Tree
