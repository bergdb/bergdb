/-
LE-b at the upward delete's stop node, the merges on (bergdb 024-12,
`UpLebOKF3`): `emptyKeyNext` either writes LE-b's node (`lebNode`, the room
branch) or replaces the node by its last version with the empty key in the next
klong's place (`handleFull`, the full branch); `writerWP_emptyKeyNext_cases`
splits the two, `lebLast_facts` gives the full branch's node.
-/
import SIS.Tree.DelStepsCascRoot
import SIS.Tree.TakeDeadUp
import SIS.Tree.TakeUpCasc

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- LE-b's two branches: the room branch writes LE-b's node (the facts of
`writerWP_emptyKeyNext_room_exact`), the full branch replaces the node by its
last version without the empty key's klong, the empty key in the next klong's
place. -/
theorem writerWP_emptyKeyNext_cases (x : NodeId) (depth : Nat) (n : KNode) (c : Ctx) (w : W)
    (P : Unit → W → Prop)
    (hlk : w.nodes.lookup x = some n)
    (hwf : klongsWf n.ks = true) (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ c.i)
    (hroom : ∀ (s : String) (n' : KNode) (jcv : Nat) (jy : NodeId),
      n'.leaf = n.leaf → klongsWf n'.ks = true → (∀ s, Klong.time s ∈ n'.ks → s ≤ c.i) →
      (jcv, jy) ∈ n.liveAt c.i → 0 < jcv →
      (∀ c' z, (c', z) ∈ n.live → c' ≠ 0 → jcv ≤ c') →
      (∀ c', n'.live.lookup c' = if c' = 0 then some jy else if c' = jcv then none else n.live.lookup c') →
      (∃ htd lip e0, n' = lebNode n c.i htd lip e0 jcv jy ∧
        (htd = true → (∃ old, n.ks.getLast? = some (.del old)) ∧ n.lastTime = some c.i) ∧
        (lip = true → n.lastTime = some c.i ∧ ∃ ti, n.lastTimeIndex = some ti ∧ ti < e0)) →
      P () { ({ w with trail := s :: w.trail } : W) with nodes := upsert w.nodes x n' })
    (hfull : ∀ (compact : Bool) (s : String) (t : Klong) (c1 : Nat) (y1 : NodeId) (r : List Klong),
      (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf 0))).ks = t :: .key c1 y1 :: r →
      WriterWP (handleFull depth x { n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf 0)) with
        ks := t :: .key 0 y1 :: r } compact) c ({ w with trail := s :: w.trail } : W) P) :
    WriterWP (emptyKeyNext x depth) c w P := by
  unfold emptyKeyNext
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x n c w hlk]
  split
  · rename_i e0 j0 jcv jy hE hJ
    have hJ' : n.ks.zipIdx.foldl (lebStep (bitsUnion n.lastBitmap (n.bitsOf 0))) none =
        some (j0, jcv, jy) := hJ
    obtain ⟨hkj, hjd, hjl⟩ := lebOK_fold _ n.ks j0 jcv jy hJ'
    have hmin := leb_min_live n j0 jcv jy hJ'
    have hb0 : j0 ∉ n.bitsOf 0 := fun h => hjd ((mem_bitsUnion_iff _ _ _).mpr (Or.inr h))
    have hj0 : jcv ≠ 0 := by
      intro h; subst h
      exact hb0 ((n.mem_bitsOf_iff 0 j0).mpr ⟨jy, List.mem_zipIdx_iff_getElem?.mpr hkj⟩)
    have hLL : LastLive n.ks n.lastBitmap j0 jcv := by
      refine ⟨⟨jy, hkj⟩, fun h => hjd ((mem_bitsUnion_iff _ _ _).mpr (Or.inl h)), ?_⟩
      intro j y' hij hj
      rcases (mem_bitsUnion_iff _ _ _).mp (hjl j y' hij hj) with h | h
      · exact h
      · obtain ⟨y'', hy''⟩ := (n.mem_bitsOf_iff 0 j).mp h
        rw [List.mem_zipIdx_iff_getElem?.mp hy''] at hj
        simp only [Option.some.injEq, Klong.key.injEq] at hj
        exact absurd hj.1.symm hj0
    have hjlive : (jcv, jy) ∈ n.liveAt c.i := by
      rw [KNode.liveAt_of_times n c.i hnt]
      apply mem_of_lookup_nodup
      rw [KNode.live_lookup]
      exact keyLookup_of_last _ _ _ j0 jy hkj hLL
    have hne : bitsUnion n.lastBitmap (n.bitsOf jcv) ≠ n.lastBitmap := by
      intro he
      have : j0 ∈ bitsUnion n.lastBitmap (n.bitsOf jcv) := (mem_bitsUnion_iff _ _ _).mpr
        (Or.inr ((n.mem_bitsOf_iff jcv j0).mpr ⟨jy, List.mem_zipIdx_iff_getElem?.mpr hkj⟩))
      rw [he] at this
      exact hLL.2.1 this
    have he0 : ∃ y0, n.ks[e0]? = some (.key 0 y0) := by
      have hm : e0 ∈ n.bitsOf 0 := List.mem_of_getLast? hE
      obtain ⟨y0, hy0⟩ := (n.mem_bitsOf_iff 0 e0).mp hm
      exact ⟨y0, List.mem_zipIdx_iff_getElem?.mp hy0⟩
    obtain ⟨y0, hy0⟩ := he0
    have helast : ∀ j y', e0 < j → n.ks[j]? = some (.key 0 y') → False := by
      intro j y' hj hjk
      have hm : j ∈ n.bitsOf 0 := (n.mem_bitsOf_iff 0 j).mpr ⟨y', List.mem_zipIdx_iff_getElem?.mpr hjk⟩
      have := bitsOf_le_last n 0 e0 hE j hm
      omega
    have htdh : ∀ b : Bool, (b = ((match n.ks.getLast? with
        | some (.del _) => true
        | _ => false) && n.lastTime == some c.i)) → b = true → ∃ old, n.ks.getLast? = some (.del old) := by
      intro b hb h
      rw [hb] at h
      cases hg : n.ks.getLast? with
      | none => rw [hg] at h; simp at h
      | some k =>
        cases k with
        | del old => exact ⟨old, rfl⟩
        | time t => rw [hg] at h; simp at h
        | key a y => rw [hg] at h; simp at h
    refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun hed => ?_)
    · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
    have helive : e0 ∉ n.lastBitmap := by simpa using hed
    -- the full branch
    have hF : ∀ compact : Bool, WriterWP (do
        let last := n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf 0))
        match last.ks with
        | t :: .key c1 y1 :: r =>
          if c1 != jcv then
            throw s!"Bug: LE-b at {c.i} in key node {x}: the last version does not start with the next child"
          note (if compact then "leb.dead" else "leb.full")
          handleFull depth x { last with ks := t :: .key 0 y1 :: r } compact
        | _ => throw s!"Bug: LE-b at {c.i} in key node {x}: the last version does not start with the next child")
        c w P := by
      intro compact
      simp only []
      split
      · rename_i t c1 y1 r hks
        refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_)
        · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
        · simp only [note, writerWP_bind, writerWP_modify]
          exact hfull compact _ t c1 y1 r hks
      · exact writerWP_throw _ _ _ _
    refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun _ => hF false)
    refine writerWP_if _ _ _ _ _ _ (fun _ => hF true) (fun hd => ?_)
    simp only [note, putNode, writerWP_bind, writerWP_modify]
    obtain ⟨hw', ht'⟩ := lebNode_wf_times n c.i _ _ e0 jcv jy hwf hnt (htdh _ rfl) hne
    refine hroom _ _ jcv jy (lebNode_leaf _ _ _ _ _ _ _) hw' ht' hjlive (Nat.pos_of_ne_zero hj0)
      (fun c' z hm hc => hmin c' z hm hc) ?_ ⟨_, _, e0, rfl, ?_, ?_⟩
    · intro c'
      exact lebNode_live_lookup n c.i _ _ e0 jcv jy y0 hwf (htdh _ rfl) hy0 helive helast hj0 hne c'
    · intro h
      refine ⟨htdh _ rfl h, ?_⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact h.2
    · intro h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨h1, h2⟩ := h
      refine ⟨h1, ?_⟩
      split at h2
      · rename_i ti hti
        exact ⟨ti, hti, by simpa using h2⟩
      · cases h2
  · exact writerWP_throw _ _ _ _
  · exact writerWP_throw _ _ _ _

/-- The full branch's node: the last version without the empty key's klong,
the empty key in its first klong's place, the next child (c1, y1) the smallest
live compare value but the empty key's. -/
theorem lebLast_facts (c : Ctx) (n : KNode) (hsa2 : 2 ≤ c.p.splitAbove)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ c.i)
    (t : Klong) (c1 : Nat) (y1 : NodeId) (r : List Klong)
    (hks : (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf 0))).ks = t :: .key c1 y1 :: r) :
    (⟨n.leaf, t :: .key 0 y1 :: r⟩ : KNode) =
      { n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf 0)) with ks := t :: .key 0 y1 :: r } ∧
    klongsWf (t :: .key 0 y1 :: r) = true ∧ (∀ s, Klong.time s ∈ (t :: .key 0 y1 :: r) → s ≤ c.i) ∧
    (⟨n.leaf, t :: .key 0 y1 :: r⟩ : KNode).lastVersion c.i = ⟨n.leaf, t :: .key 0 y1 :: r⟩ ∧
    (c.p.splitAbove < (⟨n.leaf, t :: .key 0 y1 :: r⟩ : KNode).size →
      2 ≤ (⟨n.leaf, t :: .key 0 y1 :: r⟩ : KNode).live.length) ∧
    (c1, y1) ∈ n.liveAt c.i ∧ 0 < c1 ∧ (∀ c' z, (c', z) ∈ n.liveAt c.i → c' ≠ 0 → c1 ≤ c') ∧
    (∀ c' z, (c', z) ∈ (⟨n.leaf, t :: .key 0 y1 :: r⟩ : KNode).liveAt c.i ↔
      (c' = 0 ∧ z = y1) ∨ ((c', z) ∈ n.liveAt c.i ∧ c' ≠ 0 ∧ c' ≠ c1)) := by
  obtain ⟨hleq, _, hlt, _, _, _, hiff, _⟩ := delLast_split_facts c n 0 hsa2 hnt _ rfl
  obtain ⟨pairs, hp, hsorted⟩ := n.lastVersionGivenDel_order c.i (bitsUnion n.lastBitmap (n.bitsOf 0))
  rw [hp] at hks
  cases pairs with
  | nil => simp at hks
  | cons q rest =>
    simp only [List.map_cons, List.cons.injEq] at hks
    obtain ⟨ht, hq, hr⟩ := hks
    have hq1 : q.1 = c1 := (Klong.key.inj hq).1
    have hq2 : q.2 = y1 := (Klong.key.inj hq).2
    subst ht hr
    have hsr : CvSorted rest := hsorted.tail
    have hlt1 : ∀ b ∈ rest, c1 < b.1 := fun b hb => by rw [← hq1]; exact List.rel_of_pairwise_cons hsorted hb
    have hs' : CvSorted ((0, y1) :: rest) :=
      List.Pairwise.cons (fun b hb => by have := hlt1 b hb; show 0 < b.1; omega) hsr
    have hks' : (Klong.time c.i :: Klong.key 0 y1 :: rest.map (fun q => Klong.key q.1 q.2)) =
        newKlongs c.i ((0, y1) :: rest) := rfl
    -- the last version's live klongs
    have hlastLive : (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf 0))).live = q :: rest := by
      rw [← hleq, hp]
      exact KNode.live_newKlongs_sorted _ _ _ hsorted
    have hlastAt : ∀ c' z, (c', z) ∈ q :: rest ↔ (c', z) ∈ n.liveAt c.i ∧ c' ≠ 0 := by
      intro c' z
      rw [← hiff, KNode.liveAt_of_times _ c.i hlt, hlastLive]
    have hq' : q = (c1, y1) := by rw [← hq1, ← hq2]
    rw [hq'] at hlastAt
    have h1 := (hlastAt c1 y1).mp List.mem_cons_self
    have hlen : (⟨n.leaf, newKlongs c.i ((0, y1) :: rest)⟩ : KNode).live = (0, y1) :: rest :=
      KNode.live_newKlongs_sorted _ _ _ hs'
    have htimes' : ∀ s, Klong.time s ∈ newKlongs c.i ((0, y1) :: rest) → s ≤ c.i := by
      intro s hs
      simp only [newKlongs, List.mem_cons, Klong.time.injEq, List.map_cons, List.mem_map] at hs
      rcases hs with h | h | ⟨_, _, h⟩
      · omega
      · cases h
      · cases h
    refine ⟨rfl, by rw [hks']; exact klongsWf_newKlongs _ _, by rw [hks']; exact htimes',
      by rw [hks']; exact KNode.lastVersion_newKlongs_sorted _ _ _ hs', ?_,
      h1.1, Nat.pos_of_ne_zero h1.2, ?_, ?_⟩
    · intro hsp
      rw [hks', hlen]
      simp only [KNode.size, List.length_cons, List.length_map] at hsp
      simp only [List.length_cons]
      omega
    · intro c' z hm hc
      rcases List.mem_cons.mp ((hlastAt c' z).mpr ⟨hm, hc⟩) with h | h
      · exact Nat.le_of_eq (Prod.mk.inj h).1.symm
      · exact Nat.le_of_lt (hlt1 _ h)
    · intro c' z
      rw [hks', KNode.liveAt_of_times _ c.i htimes', hlen]
      constructor
      · intro h
        rcases List.mem_cons.mp h with h | h
        · exact Or.inl ⟨(Prod.mk.inj h).1, (Prod.mk.inj h).2⟩
        · have hc1 := hlt1 _ h
          have := (hlastAt c' z).mp (List.mem_cons_of_mem _ h)
          exact Or.inr ⟨this.1, this.2, fun he => by simp only at hc1; omega⟩
      · intro h
        rcases h with ⟨rfl, rfl⟩ | ⟨hm, h0, hc⟩
        · exact List.mem_cons_self
        · refine List.mem_cons_of_mem _ ?_
          rcases List.mem_cons.mp ((hlastAt c' z).mpr ⟨hm, h0⟩) with h | h
          · exact absurd (Prod.mk.inj h).1 hc
          · exact h

/-- Obligation (LE-b's full branch): `UpLebOKF3`'s premises, the stop node S
replaced by its last version with the empty key in the next klong's place
(`handleFull`); the state after it, with the books, is in `DelInvF3`. -/
def UpLebFullOKF3 (c : Ctx) (base : View BVal) (KO : KindOracle) (BK : NodeId) : Prop :=
  ∀ (w w3 : W) (B MB : NodeId) (top0 : Top) (pre : List Nat) (cv : Nat) (rk : NodeId)
    (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth stop : Nat) (w2 : W) (S : KNode),
    2 ≤ c.p.splitAbove → ViewIdsBelow BK c.view → ViewKinds KO BK c → ICEFromKinds c base KO BK →
    X 0 = w.top.rootKey → PutBase c base B →
    PutInv c base w → RangeOrder (wNode c.p base w) c.i w.top.rootKey →
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
    ∀ (compact : Bool) (s : String) (t : Klong) (c1 : Nat) (y1 : NodeId) (r : List Klong),
    (S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf 0))).ks = t :: .key c1 y1 :: r →
    WriterWP (handleFull stop (X stop)
      { S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf 0)) with ks := t :: .key 0 y1 :: r } compact)
      c ({ w2 with trail := s :: w2.trail } : W)
      (fun _ w' => PutBook c B top0 w' → Book BK c w' → KdInv KO BK w' →
        DelInvF3 c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK w')

set_option maxHeartbeats 3200000 in
/-- `UpLebOKF3` from its full branch (`UpLebFullOKF3`): LE-b's room branch
writes LE-b's node at the stop node, and the state is the walk's tree with the
empty key's child gone and the next child under the empty key
(`collGetInv_after_upT`, `rangeOrder_up_leb`, `getFromR_up_leb`). -/
theorem upLebOKF3_of_full (c : Ctx) (base : View BVal) (KO : KindOracle) (BK : NodeId)
    (hFull : UpLebFullOKF3 c base KO BK) : UpLebOKF3 c base KO BK := by
  intro w w3 B MB top0 pre cv rk X Nn K depth stop w2 S hsa2 hvB hk hICEk hX0 hB hI hRO hF hICE hr03 hkey
    hrk hvis hpX hpK hlkX hXN hlinkK hne hall hleaf hdepth hsD hbetween hLE hJ hsl hK0 hsm
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hT := hI.tree
  -- the path at w and at w3
  have hN3 : ∀ i, i ≤ depth → wNode c.p base w3 (X i) = some (Nn i) := fun i hi => by
    rw [hr03.1]; exact hXN i hi
  have hPL : ∀ i, i ≤ depth → PathLen (wNode c.p base w) c.i w.top.rootKey (X i) i := by
    intro i
    induction i with
    | zero => intro _; rw [hX0]; exact PathLen.root
    | succ i ih =>
      intro hi
      exact PathLen.link (ih (by omega)) ⟨Nn i, hXN i (by omega), by
        have := hlinkK (i + 1) (by omega) hi; simpa using this⟩
  have hreach : ∀ i, i ≤ depth → TReach (wNode c.p base w) c.i w.top.rootKey (X i) :=
    fun i hi => (hPL i hi).reach
  have hdist : ∀ i i', i ≤ depth → i' ≤ depth → X i = X i' → i = i' := by
    intro i i' h1 h2 he
    have a := hPL i h1
    have b := hPL i' h2
    rw [he] at a
    exact PathLen.depth_unique hT _ _ _ a b
  have htk3 : ∀ i, i ≤ depth → w3.taken.contains (X i) = false := fun i hi => by
    rw [hr03.2.2.1]; exact hI.untaken _ (tReach_reachS _ _ _ _ (hreach i hi))
  have hT3 : TreeOK (wNode c.p base w3) c.i w3.top.rootKey := by rw [hr03.1, hr03.2.1]; exact hT
  have hR3 : RangeOrder (wNode c.p base w3) c.i w3.top.rootKey := by rw [hr03.1, hr03.2.1]; exact hRO
  have hreach3 : ∀ i, i ≤ depth → TReach (wNode c.p base w3) c.i w3.top.rootKey (X i) := fun i hi => by
    rw [hr03.1, hr03.2.1]; exact hreach i hi
  have hwf3 : ∀ x xn, TReach (wNode c.p base w3) c.i w3.top.rootKey x → wNode c.p base w3 x = some xn →
      klongsWf xn.ks = true := fun x xn _ h => by rw [hr03.1] at h; exact hI.wf x xn h
  have hnoval3 : ∀ i, i ≤ depth → wValue base w3 (X i) = none := fun i hi => by
    rw [ReadsAs.value _ _ _ _ hr03]; exact hI.keyNoValue _ _ (hXN i hi)
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
  -- the loop's end
  have hLE0 := hLE
  obtain ⟨h2t, h2top, h2v, _, _, h2nx, h2n, hSl, hS, hSR, hSF', hfate2, hfateJ2⟩ := hLE
  have hXs : ∀ k, stop < k → k ≤ depth → X stop ≠ X k :=
    fun k h1 h2 he => by have := hdist stop k (by omega) h2 he; omega
  have hst_t : ∀ s', Klong.time s' ∈ (Nn stop).ks → s' ≤ c.i := hI.times _ _ (hXN stop (by omega))
  have hsx : (K (stop + 1), X (stop + 1)) ∈ (Nn stop).liveAt c.i := by
    have := hlinkK (stop + 1) (by omega) (by omega); simpa using this
  have hswf : klongsWf (Nn stop).ks = true := hI.wf _ _ (hXN stop (by omega))
  have hu : ∀ c', (c', X (stop + 1)) ∈ (Nn stop).liveAt c.i → c' = K (stop + 1) := by
    intro c' h
    exact (hT.oneLink _ _ _ _ _ (hreach stop (by omega)) (hreach stop (by omega)) ⟨_, hXN stop (by omega), h⟩
      ⟨_, hXN stop (by omega), hsx⟩).2
  have hSf : S.leaf = (Nn stop).leaf ∧ klongsWf S.ks = true ∧
      (∀ s, Klong.time s ∈ S.ks → s ≤ c.i) ∧
      ∀ c' z, ((c', z) ∈ S.liveAt c.i ∧ c' ≠ K (stop + 1)) ↔
        ((c', z) ∈ (Nn stop).liveAt c.i ∧ c' ≠ K (stop + 1)) := by
    rcases hS with rfl | ⟨ti, dst, rfl⟩
    · exact ⟨rfl, hswf, hst_t, fun _ _ => Iff.rfl⟩
    · exact ⟨rfl, by rw [klongsWf_retargetKlongs]; exact hswf,
        KNode.retarget_times _ _ _ _ _ hst_t, KNode.retarget_liveAt_ne _ _ _ _ _ _ hu⟩
  obtain ⟨hSleaf, hSwf, hSt, hSlive⟩ := hSf
  -- the chain's facts (as the walk's)
  have hone : ∀ i, stop < i → i < depth → ∀ c' z, (c', z) ∈ (Nn i).liveAt c.i → z = X (i + 1) := by
    intro i h1 h2 c' z hm
    have ht := hI.times _ _ (hXN i (by omega))
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
      rw [← KNode.liveAt_of_times _ c.i (hI.times _ _ (hXN depth (Nat.le_refl _)))]; exact hm
    exact allKeysIn_live_cv (Nn depth) cv hall c' z hm'
  have hrk3 : segRootR (wNode c.p base w3) c.i c.p.fuel pre w3.top.rootKey = some rk := by
    rw [hr03.1, hr03.2.1]; exact hrk
  have hvis3 : (X depth, cv) ∈ eqVisits (wNode c.p base w3) c.i cv c.p.fuel rk := by
    rw [hr03.1]; exact hvis
  have huniq3 := hI.keyUniq pre cv rk hkey hrk
  rw [← hr03.1, ← hr03.2.1] at huniq3
  -- LE-b
  have hmain : WriterWP (emptyKeyNext (X stop) stop) c w2 (fun _ w' =>
      PutBook c B top0 w' → Book BK c w' → KdInv KO BK w' →
        DelInvF3 c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK w') := by
    refine writerWP_emptyKeyNext_cases (X stop) stop S c w2 _ hSl hSwf hSt ?_
      (fun compact s t c1 y1 r hks => hFull w w3 B MB top0 pre cv rk X Nn K depth stop w2 S hsa2 hvB hk
        hICEk hX0 hB hI hRO hF hICE hr03 hkey hrk hvis hpX hpK hlkX hXN hlinkK hne hall hleaf hdepth hsD
        hbetween hLE0 hJ hsl hK0 hsm compact s t c1 y1 r hks)
    intro s n' jcv jy hn'l hn'w hn't hjS hj0 hminS hn'lk _ hbw hbkw hikw
    generalize hw'd : ({ ({ w2 with trail := s :: w2.trail } : W) with
      nodes := upsert w2.nodes (X stop) n' } : W) = w' at hbw hbkw hikw ⊢
    have h'n : w'.nodes = upsert w2.nodes (X stop) n' := by rw [← hw'd]
    have h't : w'.taken = w2.taken := by rw [← hw'd]
    have h'top : w'.top = w3.top := by rw [← hw'd]; exact h2top
    have h'v : w'.vals = w3.vals := by rw [← hw'd]; exact h2v
    have hj : (jcv, jy) ∈ (Nn stop).liveAt c.i :=
      ((hSlive jcv jy).mp ⟨hjS, by rw [hK0]; omega⟩).1
    have h3tw : ∀ y, (∀ k, stop < k → k ≤ depth → y ≠ X k) → w'.taken.contains y = w3.taken.contains y := by
      intro y hy; rw [h't, h2t y hy]
    have hfr : ∀ y, y ≠ X stop → (∀ k, stop < k → k ≤ depth → y ≠ X k) →
        w'.nodes.lookup y = w3.nodes.lookup y := by
      intro y hys hnc
      rw [h'n, lookup_upsert]
      simp only [hys, ↓reduceIte]
      rw [h2n y hys hnc]
    have hsn' : w'.nodes.lookup (X stop) = some n' := by rw [h'n, lookup_upsert]; simp
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
    have hmin : ∀ c' z, (c', z) ∈ (Nn stop).liveAt c.i → c' ≠ 0 → jcv ≤ c' := by
      intro c' z hm hc
      have hm' := ((hSlive c' z).mpr ⟨hm, by rw [hK0]; exact hc⟩).1
      rw [KNode.liveAt_of_times _ c.i hSt] at hm'
      exact hminS c' z hm' hc
    have hsl' : n'.leaf = (Nn stop).leaf := by rw [hn'l, hSleaf]
    have hsnw : wNode c.p base w' (X stop) = some n' := by
      simp only [wNode, h3tw (X stop) hXs, htk3 stop (by omega), Bool.false_eq_true, ↓reduceIte, hsn']
    have hagree : ∀ u, u ≠ X stop → (∀ i, stop < i → i ≤ depth → u ≠ X i) →
        wNode c.p base w' u = wNode c.p base w3 u := fun u hus hnc => by
      simp only [wNode, h3tw u hnc, hfr u hus hnc]
    have hCG := collGetInv_after_upT c base X Nn K depth w3 hlkX htk3 hdist hT3 hwf3 hRt3 hTimesR3
      hICE3 hfit3 hnovalAll3 hreach3 hlinkK stop w' n' (fun c' => if c' = jcv then 0 else c') hsD h3tw
      h'top h'v hfr hsn' hsl' hn'w hn't (by
        intro c' z h
        rcases (hlive' c' z).mp h with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
        · refine ⟨jcv, by rw [h2]; exact hj, by rw [hK0]; omega, ?_⟩
          simp [h1]
        · exact ⟨c', h1, by rw [hK0]; exact h2, by simp [h3]⟩)
    have hRO' : RangeOrder (wNode c.p base w') c.i w'.top.rootKey := by
      rw [h'top]
      exact rangeOrder_up_leb (wNode c.p base w3) (wNode c.p base w') c.i w3.top.rootKey X Nn K stop
        depth hsD hR3 hT3 (hreach3 stop (by omega)) (fun i _ h2 => hN3 i h2)
        (fun i h1 h2 => hlinkK i (by omega) h2) (fun i i' _ h2 _ h4 he => hdist i i' h2 h4 he)
        hagree n' hsnw hsl hsl' hK0 jcv jy hj hj0 hmin hlive'
    have hread : ∀ key', keyWf key' = true →
        wGet c.p c.i base w' key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w3 key' := by
      intro key' hkw
      have hV' : wValue base w' = wValue base w3 :=
        wValue_eq_of_taken base w3 w' h'v (fun y => ∃ k, stop < k ∧ k ≤ depth ∧ y = X k)
          (fun y hy => h3tw y (fun k h1 h2 he => hy ⟨k, h1, h2, he⟩))
          (fun y ⟨k, _, h2, he⟩ => by rw [he]; exact ⟨htk3 k h2, hnoval3 k h2⟩)
      unfold wGet
      rw [hV', h'top]
      exact getFromR_up_leb (wNode c.p base w3) (wNode c.p base w') (wValue base w3) c.i c.p.fuel hfuel
        w3.top.rootKey X Nn K stop depth hsD pre cv rk hT3 hR3 hwf3 (hreach3 stop (by omega))
        (fun i _ h2 => hN3 i h2) (fun i h1 h2 => hlinkK i (by omega) h2) hone hleaf honly
        (fun i _ h2 => hnoval3 i h2)
        (fun i h1 h2 he => by have := hdist i depth (by omega) (Nat.le_refl _) he; omega)
        hrk3 (keyWf_last_notin pre cv hkey) hvis3 huniq3 (fun u _ hus hnc => hagree u hus hnc) n' jy jcv
        hK0 hsl hj hj0 (fun c' z hm => by
          by_cases hc : c' = 0
          · exact Or.inl hc
          · exact Or.inr (hmin c' z hm hc)) hsnw (by rw [hsl']; exact hsl) hlive' key' hkw
    exact ⟨delInvF_of_collGetInv c base B top0 hB w w3 w' (pre ++ [cv]) hI hF hr03 hCG hRO' hbw hread,
      hbkw, hikw⟩
  have hpx : (w3.path[stop]?).map (·.2) = some (X stop) := hpX stop (by omega)
  refine writerWP_mono (writerWP_and hmain
    (kdJP_emptyKeyNext c base B top0 hB KO BK hvB hk _ (X stop) stop w2 S hJ hpx hSl
      (by rw [hSleaf]; exact hsl))) ?_
  rintro _ w' ⟨hM, hJ'⟩
  exact hM hJ'.1.1 hJ'.1.2.1 hJ'.1.2.2

/-- Obligation (the take-back's side of LE-b's full branch): `UpLebJ2OKF3`'s
premises, the stop node replaced by its last version with the empty key in the
next klong's place keeps `TakeJ2` with B at most the next id. -/
def UpLebFullJ2OK (c : Ctx) (base : View BVal) (KO : KindOracle) (BK B : NodeId) : Prop :=
  ∀ (w w3 : W) (top0 : Top) (pre : List Nat) (cv : Nat) (rk : NodeId)
    (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth stop : Nat) (w2 : W) (S : KNode),
    2 ≤ c.p.splitAbove → ViewIdsBelow BK c.view → ViewKinds KO BK c → ICEFromKinds c base KO BK →
    X 0 = w.top.rootKey → 0 < c.i → PutBase c base B → PutInv c base w →
    RangeOrder (wNode c.p base w) c.i w.top.rootKey →
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
    UpLoopEnd c B X Nn depth stop w3 w2 S → KdJP c B top0 KO BK w3.path w2 →
    (Nn stop).leaf = false → K (stop + 1) = 0 → S.smallestLive = some 0 →
    TakeJ2 c base B w → (∀ x o, w3.madeFor.lookup x = some o → o < B) →
    (∀ c' z, (c', z) ∈ (Nn depth).liveAt c.i → wNode c.p base w z = none) →
    ∀ (compact : Bool) (s : String) (t : Klong) (c1 : Nat) (y1 : NodeId) (r : List Klong),
    (S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf 0))).ks = t :: .key c1 y1 :: r →
    WriterWP (handleFull stop (X stop)
      { S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf 0)) with ks := t :: .key 0 y1 :: r } compact)
      c ({ w2 with trail := s :: w2.trail } : W) (fun _ w' => TakeJ2 c base B w' ∧ B ≤ w'.next)

set_option maxHeartbeats 3200000 in
/-- `UpLebJ2OKF3` from LE-b's full branch (`UpLebFullOKF3`, `UpLebFullJ2OK`):
the reading by `upLebOKF3_of_full`; in the room branch `TakeJ2` keeps, the nodes
of the transaction's time reached (`ttReachedN_up`) and the node facts
(`j2rest_up`, LE-b's node's klongs the node's or to the next child). -/
theorem upLebJ2OKF3_of_full (c : Ctx) (base : View BVal) (KO : KindOracle) (BK B : NodeId)
    (hFull : UpLebFullOKF3 c base KO BK) (hFullJ : UpLebFullJ2OK c base KO BK B) :
    UpLebJ2OKF3 c base KO BK B := by
  intro w w3 top0 pre cv rk X Nn K depth stop w2 S hsa2 hvB hk hICEk hX0 hpos hB hI hRO hF hICE hr03 hkey
    hrk hvis hpX hpK hlkX hXN hlinkK hne hall hleaf hdepth hsD hbetween hLE hJ hsl hK0 hsm hJw hMF hkidsw
  have hRead := upLebOKF3_of_full c base KO BK hFull w w3 B B top0 pre cv rk X Nn K depth stop w2 S hsa2 hvB
    hk hICEk hX0 hB hI hRO hF hICE hr03 hkey hrk hvis hpX hpK hlkX hXN hlinkK hne hall hleaf hdepth hsD
    hbetween hLE hJ hsl hK0 hsm
  have hT := hI.tree
  have hN3 : ∀ i, i ≤ depth → wNode c.p base w3 (X i) = some (Nn i) := fun i hi => by
    rw [hr03.1]; exact hXN i hi
  have hPL : ∀ i, i ≤ depth → PathLen (wNode c.p base w) c.i w.top.rootKey (X i) i := by
    intro i
    induction i with
    | zero => intro _; rw [hX0]; exact PathLen.root
    | succ i ih =>
      intro hi
      exact PathLen.link (ih (by omega)) ⟨Nn i, hXN i (by omega), by
        have := hlinkK (i + 1) (by omega) hi; simpa using this⟩
  have hreach : ∀ i, i ≤ depth → TReach (wNode c.p base w) c.i w.top.rootKey (X i) :=
    fun i hi => (hPL i hi).reach
  have hdist : ∀ i i', i ≤ depth → i' ≤ depth → X i = X i' → i = i' := by
    intro i i' h1 h2 he
    have a := hPL i h1
    have b := hPL i' h2
    rw [he] at a
    exact PathLen.depth_unique hT _ _ _ a b
  have htk3 : ∀ i, i ≤ depth → w3.taken.contains (X i) = false := fun i hi => by
    rw [hr03.2.2.1]; exact hI.untaken _ (tReach_reachS _ _ _ _ (hreach i hi))
  have hreach3 : ∀ i, i ≤ depth → TReach (wNode c.p base w3) c.i w3.top.rootKey (X i) := fun i hi => by
    rw [hr03.1, hr03.2.1]; exact hreach i hi
  have hJ3 : TakeJ2 c base B w3 := takeJ2_of_readsAs c base B w w3 hJw hr03
  obtain ⟨h2t, h2top, h2v, _, _, h2nx, h2n, hSl, hS, hSR, hSF', hfate2, hfateJ2⟩ := hLE
  have hXs : ∀ k, stop < k → k ≤ depth → X stop ≠ X k :=
    fun k h1 h2 he => by have := hdist stop k (by omega) h2 he; omega
  have hst_t : ∀ s', Klong.time s' ∈ (Nn stop).ks → s' ≤ c.i := hI.times _ _ (hXN stop (by omega))
  have hsx : (K (stop + 1), X (stop + 1)) ∈ (Nn stop).liveAt c.i := by
    have := hlinkK (stop + 1) (by omega) (by omega); simpa using this
  have hswf : klongsWf (Nn stop).ks = true := hI.wf _ _ (hXN stop (by omega))
  have hu : ∀ c', (c', X (stop + 1)) ∈ (Nn stop).liveAt c.i → c' = K (stop + 1) := by
    intro c' h
    exact (hT.oneLink _ _ _ _ _ (hreach stop (by omega)) (hreach stop (by omega)) ⟨_, hXN stop (by omega), h⟩
      ⟨_, hXN stop (by omega), hsx⟩).2
  have hSf : S.leaf = (Nn stop).leaf ∧ klongsWf S.ks = true ∧
      (∀ s, Klong.time s ∈ S.ks → s ≤ c.i) ∧
      ∀ c' z, ((c', z) ∈ S.liveAt c.i ∧ c' ≠ K (stop + 1)) ↔
        ((c', z) ∈ (Nn stop).liveAt c.i ∧ c' ≠ K (stop + 1)) := by
    rcases hS with rfl | ⟨ti, dst, rfl⟩
    · exact ⟨rfl, hswf, hst_t, fun _ _ => Iff.rfl⟩
    · exact ⟨rfl, by rw [klongsWf_retargetKlongs]; exact hswf,
        KNode.retarget_times _ _ _ _ _ hst_t, KNode.retarget_liveAt_ne _ _ _ _ _ _ hu⟩
  obtain ⟨hSleaf, hSwf, hSt, hSlive⟩ := hSf
  have hone : ∀ i, stop < i → i < depth → ∀ c' z, (c', z) ∈ (Nn i).liveAt c.i → z = X (i + 1) := by
    intro i h1 h2 c' z hm
    have ht := hI.times _ _ (hXN i (by omega))
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
  have hB2 : B ≤ w2.next := hJ.1.1.fresh.1
  have hJ2 : WriterWP (emptyKeyNext (X stop) stop) c w2
      (fun _ w' => TakeJ2 c base B w' ∧ B ≤ w'.next) := by
    refine writerWP_emptyKeyNext_cases (X stop) stop S c w2 _ hSl hSwf hSt ?_
      (fun compact s t c1 y1 r hks => hFullJ w w3 top0 pre cv rk X Nn K depth stop w2 S hsa2 hvB hk hICEk
        hX0 hpos hB hI hRO hF hICE hr03 hkey hrk hvis hpX hpK hlkX hXN hlinkK hne hall hleaf hdepth hsD
        hbetween ⟨h2t, h2top, h2v, ‹_›, ‹_›, h2nx, h2n, hSl, hS, hSR, hSF', hfate2, hfateJ2⟩ hJ hsl hK0 hsm
        hJw hMF hkidsw compact s t c1 y1 r hks)
    intro s n' jcv jy hn'l hn'w hn't hjS hj0 hminS hn'lk hlebEx
    obtain ⟨htd, lip, e0, hleb, hhtd, hlip⟩ := hlebEx
    generalize hw'd : ({ ({ w2 with trail := s :: w2.trail } : W) with
      nodes := upsert w2.nodes (X stop) n' } : W) = w'
    have h'n : w'.nodes = upsert w2.nodes (X stop) n' := by rw [← hw'd]
    have h't : w'.taken = w2.taken := by rw [← hw'd]
    have h'top : w'.top = w3.top := by rw [← hw'd]; exact h2top
    have h'v : w'.vals = w3.vals := by rw [← hw'd]; exact h2v
    have h'nx : w'.next = w2.next := by rw [← hw'd]
    have hj : (jcv, jy) ∈ (Nn stop).liveAt c.i :=
      ((hSlive jcv jy).mp ⟨hjS, by rw [hK0]; omega⟩).1
    have h3tw : ∀ y, (∀ k, stop < k → k ≤ depth → y ≠ X k) → w'.taken.contains y = w3.taken.contains y := by
      intro y hy; rw [h't, h2t y hy]
    have hfr : ∀ y, y ≠ X stop → (∀ k, stop < k → k ≤ depth → y ≠ X k) →
        w'.nodes.lookup y = w3.nodes.lookup y := by
      intro y hys hnc
      rw [h'n, lookup_upsert]
      simp only [hys, ↓reduceIte]
      rw [h2n y hys hnc]
    have hsn' : w'.nodes.lookup (X stop) = some n' := by rw [h'n, lookup_upsert]; simp
    have hlk2 : ∀ k, stop < k → k ≤ depth → w'.nodes.lookup (X k) = w2.nodes.lookup (X k) := by
      intro k h1 h2
      rw [h'n, lookup_upsert]
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
    have hsl' : n'.leaf = (Nn stop).leaf := by rw [hn'l, hSleaf]
    have hsnw : wNode c.p base w' (X stop) = some n' := by
      simp only [wNode, h3tw (X stop) hXs, htk3 stop (by omega), Bool.false_eq_true, ↓reduceIte, hsn']
    have hagree : ∀ u, u ≠ X stop → (∀ i, stop < i → i ≤ depth → u ≠ X i) →
        wNode c.p base w' u = wNode c.p base w3 u := fun u hus hnc => by
      simp only [wNode, h3tw u hnc, hfr u hus hnc]
    have hskeep : ∀ c' z, (c', z) ∈ (Nn stop).liveAt c.i → c' ≠ K (stop + 1) →
        ∃ c'', (c'', z) ∈ n'.liveAt c.i := by
      intro c' z hm hc
      rw [hK0] at hc
      by_cases hcj : c' = jcv
      · rw [hcj] at hm
        have hzy : jy = z := KNode.liveAt_fun _ _ _ _ _ hj hm
        exact ⟨0, (hlive' 0 z).mpr (Or.inl ⟨rfl, hzy.symm⟩)⟩
      · exact ⟨c', (hlive' c' z).mpr (Or.inr ⟨hm, hc, hcj⟩)⟩
    have hkeep : ∀ c' z, (c', z) ∈ (Nn stop).liveAt c.i → z ≠ X (stop + 1) →
        ∃ c'', (c'', z) ∈ n'.liveAt c.i := by
      intro c' z hm hz
      refine hskeep c' z hm (fun hck => hz ?_)
      rw [hck] at hm
      exact (KNode.liveAt_fun _ _ _ _ _ hsx hm).symm
    have hTt : TtReachedN (wNode c.p base w') c.i w'.top.rootKey := by
      rw [h'top]
      refine ttReachedN_up (wNode c.p base w3) (wNode c.p base w') c.i w3.top.rootKey X Nn stop depth hsD
        (fun i _ h2 => hN3 i h2) hone (fun c' z h => by rw [hr03.1]; exact hkidsw c' z h) n' hsnw hkeep
        hagree hXs (hreach3 stop (by omega)) ?_ hJ3.1
      intro k h1 h2 un hun
      have hf := chainFate_frame c.i w2 w' (X k) (hfate2 k h1 h2) h't (hlk2 k h1 h2)
      rcases hf with hf | ⟨S0, hS0, hnt0⟩
      · unfold wNode at hun; rw [hf] at hun; cases hun
      · have hkt : w'.taken.contains (X k) = false := by
          cases hc : w'.taken.contains (X k) with
          | false => rfl
          | true => unfold wNode at hun; rw [hc] at hun; cases hun
        simp only [wNode, hkt, Bool.false_eq_true, ↓reduceIte, hS0, Option.some.injEq] at hun
        rw [← hun]; exact hnt0
    have hlf := lebNode_facts S c.i htd lip e0 jcv jy hpos hSt hhtd hlip
    have hrest := j2rest_up (wNode c.p base w3) (wNode c.p base w') c.i B (w3.vals.map (·.1)) X Nn stop depth
      (K (stop + 1)) hsD hpos hJ3.2.1 hJ3.2.2.1 hJ3.2.2.2.1 hJ3.2.2.2.2.1 hJ3.2.2.2.2.2
      (fun i _ hi => hN3 i hi) (fun i i' _ hi _ hi' he => hdist i i' hi hi' he)
      (by
        intro k h1 h2
        obtain ⟨hm, hu'⟩ := chainFateW_frame c.i B w2 w' (Nn k) (X k) (hfateJ2 k h1 h2) h't (hlk2 k h1 h2)
        refine ⟨fun hf => by simp only [wNode, hm hf, ↓reduceIte], fun hf => ?_⟩
        obtain ⟨ht0, S0, hS0, hl0⟩ := hu' hf
        exact ⟨S0, hS0, by simp only [wNode, ht0, Bool.false_eq_true, ↓reduceIte, hl0]⟩)
      hswf hst_t hsx S n' (fun y => y = jy) hSR hSF' hsnw (by rw [hleb]; exact hlf.1)
      (fun s hs => by rw [hleb]; exact hlf.2 s hs)
      (fun i c' y h => by
        rw [hleb] at h
        exact lebNode_key S c.i htd lip e0 jcv jy (fun h => (hhtd h).1) i c' y h)
      (fun y hy => ⟨⟨0, (hlive' 0 y).mpr (Or.inl ⟨rfl, hy⟩)⟩, by rw [hsl', hsl]⟩) hskeep
      (fun hl => by rw [hsl', hsl] at hl; cases hl) hagree
    refine ⟨?_, by rw [h'nx]; exact hB2⟩
    unfold TakeJ2
    rw [h'v]
    exact ⟨hTt, hrest⟩
  exact writerWP_mono (writerWP_and hRead hJ2) (fun _ w' h => ⟨h.1, h.2.1, h.2.2⟩)

/-- `DelStepsOKF3` with LE-b's room branch proved (`upLebOKF3_of_full`): open
are LE-b's full branch (`UpLebFullOKF3`), the state after the upward loop
(`UpUnlinkOK`, `UpUnlinkLinksOK`) and the fuel after the splits
(`UpCascFitsOK`, `DelFullFitsOK`). -/
theorem delStepsOKF3_of_open8 (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts))
    (hU : ∀ ts, UpUnlinkOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hL : ∀ ts, UpUnlinkLinksOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hFit : ∀ ts BK, UpCascFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) BK)
    (hLbF : ∀ ts BK, UpLebFullOKF3 (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) BK)
    (hFits : ∀ ts, DelFullFitsOK (ctxOf p ts) (viewOf (treeRun p ts))) : DelStepsOKF3 p R :=
  delStepsOKF3_of_open7 p R hM hsa2 hRL hP hU hL hFit
    (fun ts BK => upLebOKF3_of_full _ _ _ _ (hLbF ts BK)) hFits

/-- `delStepsJ2OKF3_of_openR2` with LE-b's room branch proved
(`upLebJ2OKF3_of_full`): open are LE-b's full branch (`UpLebFullOKF3`,
`UpLebFullJ2OK`), the state after the upward loop (`UpUnlinkOK`,
`UpUnlinkLinksOK`), the fuel after the splits (`UpCascFitsOK`,
`DelFullFitsOK`) and the S inputs. -/
theorem delStepsJ2OKF3_of_openR3 (p : Params) (R : Struct BVal → Time → Prop)
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
    (hU : ∀ ts, UpUnlinkOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hL : ∀ ts, UpUnlinkLinksOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hFit : ∀ ts BK, UpCascFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) BK)
    (hLbF : ∀ ts BK, UpLebFullOKF3 (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) BK)
    (hLbFJ : ∀ ts BK B,
      UpLebFullJ2OK (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) BK B)
    (hFits : ∀ ts, DelFullFitsOK (ctxOf p ts) (viewOf (treeRun p ts))) :
    DelStepsJ2OKF3 p R S :=
  delStepsJ2OKF3_of_openR2 p R S hM hsa2 hRL hRP hRK hSI hSV hSB hSR hSF hSM hU hL hFit
    (fun ts BK B => upLebJ2OKF3_of_full _ _ _ _ B (hLbF ts BK) (hLbFJ ts BK B)) hFits

end SIS.Tree
