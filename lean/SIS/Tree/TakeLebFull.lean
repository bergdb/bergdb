/-
The take-back's facts through LE-b's full branch at the upward delete's stop
node (bergdb 024-12, `UpLebFullJ2OK`): as `writerWP_upCasc_root_j2` and
`writerWP_upCasc_below_j2`, with the stop node's last version with the empty key
in the next klong's place (`lebLast_facts`).
-/
import SIS.Tree.DelStepsLebFull

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The full branch's node is new klongs of the transaction's time, their
compare values distinct. -/
theorem lebLast_pairs (c : Ctx) (n : KNode)
    (t : Klong) (c1 : Nat) (y1 : NodeId) (r : List Klong)
    (hks : (n.lastVersionGivenDel c.i (bitsUnion n.lastBitmap (n.bitsOf 0))).ks = t :: .key c1 y1 :: r) :
    ∃ pairs, (t :: .key 0 y1 :: r) = newKlongs c.i pairs ∧ (pairs.map Prod.fst).Nodup := by
  obtain ⟨pairs, hp, hsorted⟩ := n.lastVersionGivenDel_order c.i (bitsUnion n.lastBitmap (n.bitsOf 0))
  rw [hp] at hks
  cases pairs with
  | nil => simp at hks
  | cons q rest =>
    simp only [List.map_cons, List.cons.injEq] at hks
    obtain ⟨ht, hq, hr⟩ := hks
    have hq1 : q.1 = c1 := (Klong.key.inj hq).1
    subst ht hr
    have hsr : CvSorted rest := hsorted.tail
    have hlt1 : ∀ b ∈ rest, c1 < b.1 := fun b hb => by rw [← hq1]; exact List.rel_of_pairwise_cons hsorted hb
    have hs' : CvSorted ((0, y1) :: rest) :=
      List.Pairwise.cons (fun b hb => by have := hlt1 b hb; show 0 < b.1; omega) hsr
    exact ⟨(0, y1) :: rest, rfl, List.pairwise_map.mpr (hs'.imp (by intro a b hab; omega))⟩

set_option maxHeartbeats 6400000 in
/-- The take-back's facts through LE-b's full branch at the space root
(`UpLebFullJ2OK` at stop 0): from the state after the upward loop as a tree
(`UpUnlinkOK`), its links and klongs, `TakeJ2` keeps with B at most the next id:
the node facts after the loop (`j2rest_up`), the nodes of the transaction's time
reached in the tree with the root's last version (`ttReachedN_up`), the root's
split (`writerWP_handleFull_root_j2U`). -/
theorem writerWP_upLebFull_root_j2 (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (hsa2 : 2 ≤ c.p.splitAbove) (B : NodeId) (hpos : 0 < c.i)
    (w w3 : W) (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth : Nat) (w2 : W) (S : KNode)
    (hI : PutInv c base w) (hr03 : ReadsAs c.p base w w3) (hJw : TakeJ2 c base B w) (hBn : B ≤ w.next)
    (hkidsw : ∀ c' z, (c', z) ∈ (Nn depth).liveAt c.i → wNode c.p base w z = none)
    (hlkX : ∀ i, i ≤ depth → w3.nodes.lookup (X i) = some (Nn i))
    (hXN : ∀ i, i ≤ depth → wNode c.p base w (X i) = some (Nn i))
    (hlinkK : ∀ i, 0 < i → i ≤ depth → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (hdepth : 0 < depth)
    (hbetween : ∀ i, 0 < i → i < depth →
      (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true)
    (hX0 : X 0 = w.top.rootKey)
    (hLE : UpLoopEnd c B X Nn depth 0 w3 w2 S)
    (hK0 : K 1 = 0)
    (hT2 : TreeOK (wNode c.p base w2) c.i w2.top.rootKey)
    (hlinks2 : ∀ u c' z, TLink (wNode c.p base w2) c.i u c' z → z < w2.next)
    (hwf2 : ∀ z zn, wNode c.p base w2 z = some zn → klongsWf zn.ks = true)
    (compact : Bool) (s : String) (t : Klong) (c1 : Nat) (y1 : NodeId) (r : List Klong)
    (hks : (S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf 0))).ks = t :: .key c1 y1 :: r) :
    WriterWP (handleFull 0 (X 0)
      { S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf 0)) with ks := t :: .key 0 y1 :: r } compact)
      c ({ w2 with trail := s :: w2.trail } : W) (fun _ w' => TakeJ2 c base B w' ∧ B ≤ w'.next) := by
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
  have hI3 := putInv_of_readsAs c base w w3 hI hr03
  have htk3 : ∀ i, i ≤ depth → w3.taken.contains (X i) = false := fun i hi => by
    rw [hr03.2.2.1]; exact hI.untaken _ (tReach_reachS _ _ _ _ (hreach i hi))
  have hT3 : TreeOK (wNode c.p base w3) c.i w3.top.rootKey := by rw [hr03.1, hr03.2.1]; exact hT
  have hreach3 : ∀ i, i ≤ depth → TReach (wNode c.p base w3) c.i w3.top.rootKey (X i) := fun i hi => by
    rw [hr03.1, hr03.2.1]; exact hreach i hi
  have hJ3 : TakeJ2 c base B w3 := takeJ2_of_readsAs c base B w w3 hJw hr03
  obtain ⟨h2t, h2top, h2v, _, _, h2nx, h2n, hSl, hS, hSR, hSF', hfate2, hfateJ2⟩ := hLE
  have hXs : ∀ k, 0 < k → k ≤ depth → X 0 ≠ X k :=
    fun k h1 h2 he => by have := hdist 0 k (by omega) h2 he; omega
  have hst_t : ∀ s', Klong.time s' ∈ (Nn 0).ks → s' ≤ c.i := hI.times _ _ (hXN 0 (by omega))
  have hsx : (K 1, X 1) ∈ (Nn 0).liveAt c.i := by
    have := hlinkK 1 (by omega) hdepth; simpa using this
  have hswf : klongsWf (Nn 0).ks = true := hI.wf _ _ (hXN 0 (by omega))
  have hu : ∀ c', (c', X 1) ∈ (Nn 0).liveAt c.i → c' = K 1 := by
    intro c' h
    exact (hT.oneLink _ _ _ _ _ (hreach 0 (by omega)) (hreach 0 (by omega)) ⟨_, hXN 0 (by omega), h⟩
      ⟨_, hXN 0 (by omega), hsx⟩).2
  have hSf : S.leaf = (Nn 0).leaf ∧ klongsWf S.ks = true ∧
      (∀ s, Klong.time s ∈ S.ks → s ≤ c.i) ∧
      ∀ c' z, ((c', z) ∈ S.liveAt c.i ∧ c' ≠ K 1) ↔ ((c', z) ∈ (Nn 0).liveAt c.i ∧ c' ≠ K 1) := by
    rcases hS with rfl | ⟨ti, dst, rfl⟩
    · exact ⟨rfl, hswf, hst_t, fun _ _ => Iff.rfl⟩
    · exact ⟨rfl, by rw [klongsWf_retargetKlongs]; exact hswf,
        KNode.retarget_times _ _ _ _ _ hst_t, KNode.retarget_liveAt_ne _ _ _ _ _ _ hu⟩
  obtain ⟨hSleaf, hSwf, hSt, hSlive⟩ := hSf
  have htk2 : w2.taken.contains (X 0) = false := by rw [h2t _ hXs]; exact htk3 0 (by omega)
  have hagree2 : ∀ u, u ≠ X 0 → (∀ i, 0 < i → i ≤ depth → u ≠ X i) →
      wNode c.p base w2 u = wNode c.p base w3 u := fun u hus hnc => by
    simp only [wNode, h2t u hnc, h2n u hus hnc]
  have hS2w : wNode c.p base w2 (X 0) = some S := by
    simp only [wNode, htk2, Bool.false_eq_true, ↓reduceIte, hSl]
  have hone : ∀ i, 0 < i → i < depth → ∀ c' z, (c', z) ∈ (Nn i).liveAt c.i → z = X (i + 1) := by
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
  -- the node facts after the loop
  have hrest2 := j2rest_up (wNode c.p base w3) (wNode c.p base w2) c.i B (w3.vals.map (·.1)) X Nn 0 depth
    (K 1) hdepth hpos hJ3.2.1 hJ3.2.2.1 hJ3.2.2.2.1 hJ3.2.2.2.2.1 hJ3.2.2.2.2.2 (fun i _ hi => hN3 i hi)
    (fun i i' _ hi _ hi' he => hdist i i' hi hi' he)
    (by
      intro k h1 h2
      obtain ⟨hm, hu'⟩ := hfateJ2 k h1 h2
      refine ⟨fun hf => by simp only [wNode, hm hf, ↓reduceIte], fun hf => ?_⟩
      obtain ⟨ht0, S0, hS0, hl0⟩ := hu' hf
      exact ⟨S0, hS0, by simp only [wNode, ht0, Bool.false_eq_true, ↓reduceIte, hl0]⟩)
    hswf hst_t hsx S S (fun _ => False) hSR hSF' hS2w rfl (fun s h => h)
    (fun i c' y h => Or.inl h) (fun y h => h.elim)
    (fun c' y hm hc => ⟨c', ((hSlive c' y).mpr ⟨hm, hc⟩).1⟩)
    (fun hl => ⟨hl, fun i c' hL _ => hL⟩) hagree2
  rw [hK0] at hSlive
  -- the root's last version with the empty key in the next klong's place
  obtain ⟨hleq', hlwf, hlt, hlastV, hlen2, hjS, hj0, hminS, hliveS⟩ := lebLast_facts c S hsa2 hSt t c1 y1 r hks
  obtain ⟨pairs, hpks, hpnd⟩ := lebLast_pairs c S t c1 y1 r hks
  generalize hlast : ({ S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf 0)) with
    ks := t :: .key 0 y1 :: r } : KNode) = last
  have hlks : last.ks = t :: .key 0 y1 :: r := by rw [← hlast]
  rw [← hlks] at hlwf hlt hlastV hlen2 hliveS hpks
  have hleqL : (⟨S.leaf, last.ks⟩ : KNode) = last := by rw [hlks, hleq', hlast]
  replace hlastV : (⟨S.leaf, last.ks⟩ : KNode).lastVersion c.i = last := hlastV.trans hleqL
  have hlen2' : c.p.splitAbove < last.size → 2 ≤ (⟨S.leaf, last.ks⟩ : KNode).live.length := by
    intro h; apply hlen2; rw [hleqL]; exact h
  have hj : (c1, y1) ∈ (Nn 0).liveAt c.i := ((hSlive c1 y1).mp ⟨hjS, by omega⟩).1
  have hliveL : ∀ c' z, (c', z) ∈ (⟨S.leaf, last.ks⟩ : KNode).liveAt c.i ↔
      (c' = 0 ∧ z = y1) ∨ ((c', z) ∈ (Nn 0).liveAt c.i ∧ c' ≠ 0 ∧ c' ≠ c1) := by
    intro c' z
    rw [hliveS c' z]
    constructor
    · rintro (h | ⟨h1, h2, h3⟩)
      · exact Or.inl h
      · exact Or.inr ⟨((hSlive c' z).mp ⟨h1, h2⟩).1, h2, h3⟩
    · rintro (h | ⟨h1, h2, h3⟩)
      · exact Or.inl h
      · exact Or.inr ⟨((hSlive c' z).mpr ⟨h1, h2⟩).1, h2, h3⟩
  have hliveF : ∀ c' z, (c', z) ∈ (⟨S.leaf, last.ks⟩ : KNode).liveAt c.i →
      ∃ c0, (c0, z) ∈ (Nn 0).liveAt c.i ∧ c0 ≠ K 1 ∧ (fun c'' => if c'' = c1 then 0 else c'') c0 = c' := by
    intro c' z h
    rcases (hliveL c' z).mp h with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · refine ⟨c1, by rw [h2]; exact hj, by rw [hK0]; omega, ?_⟩
      simp [h1]
    · exact ⟨c', h1, by rw [hK0]; exact h2, by simp [h3]⟩
  have hkeep : ∀ c' z, (c', z) ∈ (Nn 0).liveAt c.i → z ≠ X 1 →
      ∃ c'', (c'', z) ∈ (⟨S.leaf, last.ks⟩ : KNode).liveAt c.i := by
    intro c' z hm hz
    by_cases hcj : c' = c1
    · rw [hcj] at hm
      have hzy : y1 = z := KNode.liveAt_fun _ _ _ _ _ hj hm
      exact ⟨0, (hliveL 0 z).mpr (Or.inl ⟨rfl, hzy.symm⟩)⟩
    · have hc0 : c' ≠ 0 := by
        intro h0
        rw [h0] at hm
        have hsx0 : (0, X 1) ∈ (Nn 0).liveAt c.i := by have h := hsx; rw [hK0] at h; exact h
        exact hz (KNode.liveAt_fun _ _ _ _ _ hsx0 hm).symm
      exact ⟨c', (hliveL c' z).mpr (Or.inr ⟨hm, hc0, hcj⟩)⟩
  generalize hv0 : ({ w2 with trail := s :: w2.trail } : W) = v
  have hvn : v.nodes = w2.nodes := by rw [← hv0]
  have hvt : v.taken = w2.taken := by rw [← hv0]
  have hvtop : v.top = w2.top := by rw [← hv0]
  have hvv : v.vals = w2.vals := by rw [← hv0]
  have hvnx : v.next = w2.next := by rw [← hv0]
  have hwv : wNode c.p base v = wNode c.p base w2 := by
    funext z; simp only [wNode, hvn, hvt]
  have hlk' : v.nodes.lookup (X 0) = some S := by rw [hvn]; exact hSl
  have htk' : v.taken.contains (X 0) = false := by rw [hvt]; exact htk2
  have hroot' : v.top.rootKey = w3.top.rootKey := by rw [hvtop, h2top]
  have hrk' : v.top.rootKey = X 0 := by rw [hroot', hr03.2.1, hX0]
  have hnx' : v.next = w3.next := by rw [hvnx, h2nx]
  have hXlt : ∀ i, i ≤ depth → X i < w3.next := fun i hi => hI3.ids.1 (X i) (by rw [hlkX i hi]; rfl)
  have hS5 : ∀ z, v.next ≤ z → v.nodes.lookup z = none ∧ v.taken.contains z = false ∧
      knodeOf c.p base z = none := by
    intro z hz
    rw [hnx'] at hz
    have hzX : ∀ i, i ≤ depth → z ≠ X i := fun i hi he => by have := hXlt i hi; omega
    refine ⟨?_, ?_, (hI.fresh z (by rw [← hr03.2.2.2.2]; exact hz)).1⟩
    · rw [hvn, h2n z (hzX 0 (by omega)) (fun i _ hi => hzX i hi)]
      cases h' : w3.nodes.lookup z with
      | none => rfl
      | some _ => have := hI3.ids.1 z (by rw [h']; rfl); omega
    · rw [hvt, h2t z (fun i _ hi => hzX i hi)]
      cases h' : w3.taken.contains z with
      | false => rfl
      | true => have := hI3.ids.2.2.1 z h'; omega
  have hS6 : ∀ u c' z, TLink (wNode c.p base v) c.i u c' z → z < v.next := by
    rw [hwv, hvnx]; exact hlinks2
  have hW : ∀ z zn, wNode c.p base v z = some zn → klongsWf zn.ks = true := by
    rw [hwv]; exact hwf2
  have hagreeV : ∀ u, u ≠ X 0 → (∀ i, 0 < i → i ≤ depth → u ≠ X i) →
      updN (wNode c.p base v) (X 0) ⟨S.leaf, last.ks⟩ u = wNode c.p base w3 u := fun u hus hnc => by
    rw [updN_ne _ _ _ _ hus, hwv]; exact hagree2 u hus hnc
  have hsnV : updN (wNode c.p base v) (X 0) ⟨S.leaf, last.ks⟩ (X 0) = some ⟨S.leaf, last.ks⟩ :=
    updN_self _ _ _
  have hV : TreeOK (updN (wNode c.p base v) (X 0) ⟨S.leaf, last.ks⟩) c.i v.top.rootKey := by
    rw [hroot']
    exact treeOK_up_tr (wNode c.p base w3) _ c.i w3.top.rootKey X Nn K 0 depth hdepth hT3
      (hreach3 0 (by omega)) (fun i _ hi => hN3 i hi) (fun i h1 hi => hlinkK i h1 hi)
      (fun i i' _ hi _ hi' he => hdist i i' hi hi' he) hagreeV _ hsnV _ hliveF
  have hvx : ∀ c' z, (c', z) ∈ (⟨S.leaf, last.ks⟩ : KNode).liveAt c.i → z < v.next := by
    intro c' z h
    rw [hnx', hr03.2.2.2.2]
    obtain ⟨c0, hc0, _, _⟩ := hliveF c' z h
    exact hI.links (X 0) (Nn 0) c0 z (tReach_reachS _ _ _ _ (hreach 0 (by omega))) (hXN 0 (by omega)) hc0
  -- the nodes of the transaction's time, reached in the tree with the root's last version
  have hTtV := ttReachedN_up (wNode c.p base w3) (updN (wNode c.p base v) (X 0) ⟨S.leaf, last.ks⟩) c.i
    w3.top.rootKey X Nn 0 depth hdepth (fun i _ hi => hN3 i hi) hone
    (fun c' z h => by rw [hr03.1]; exact hkidsw c' z h) _ hsnV hkeep
    hagreeV hXs (hreach3 0 (by omega))
    (by
      intro k h1 h2 un hun
      rw [updN_ne _ _ _ _ (Ne.symm (hXs k h1 h2)), hwv] at hun
      rcases hfate2 k h1 h2 with hf | ⟨S0, hS0, hnt0⟩
      · unfold wNode at hun; rw [hf] at hun; cases hun
      · have hkt : w2.taken.contains (X k) = false := by
          cases hc : w2.taken.contains (X k) with
          | false => rfl
          | true => unfold wNode at hun; rw [hc] at hun; cases hun
        simp only [wNode, hkt, Bool.false_eq_true, ↓reduceIte, hS0, Option.some.injEq] at hun
        rw [← hun]; exact hnt0)
    hJ3.1
  have hTU : ∀ q qn, wNode c.p base v q = some qn → Klong.time c.i ∈ qn.ks →
      TReach (updN (wNode c.p base v) (X 0) ⟨S.leaf, last.ks⟩) c.i v.top.rootKey q := by
    intro q qn hq hm
    by_cases hq0 : q = X 0
    · rw [hq0, hrk']; exact TReach.root
    · rw [hroot']
      exact hTtV q qn (by rw [updN_ne _ _ _ _ hq0]; exact hq) hm
  have hvals2 : v.vals = w3.vals := by rw [hvv, h2v]
  have hrest' : DeadLiveN (wNode c.p base v) c.i B (v.vals.map (·.1)) ∧
      OldBelowN (wNode c.p base v) c.i B ∧ OldStartN (wNode c.p base v) c.i B ∧
      MadeStartN (wNode c.p base v) c.i B ∧ ValsNoNodeN (wNode c.p base v) (v.vals.map (·.1)) := by
    rw [hwv, hvals2]; exact hrest2
  exact writerWP_handleFull_root_j2U c base hvc B hpos (X 0) S last compact v
    hrest' (by rw [hnx', hr03.2.2.2.2]; exact hBn)
    (by
      intro y hy
      rw [hvals2] at hy
      rw [hnx']
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy
      exact hI3.ids.2.2.2.1 e he)
    (by rw [hwv, hvtop]; exact hT2)
    hlwf hlt hlastV hlen2' ⟨pairs, hpks, hpnd⟩ hlk' htk' hrk' hS5 hS6 hW hV hvx hSwf hSt hTU

set_option maxHeartbeats 6400000 in
/-- The take-back's facts through LE-b's full branch below the space root
(`UpLebFullJ2OK` at stop D + 1): as `writerWP_upLebFull_root_j2`, the cascade
above by `writerWP_handleFull_last_j2U`. -/
theorem writerWP_upLebFull_below_j2 (c : Ctx) (base : View BVal)
    (hsa2 : 2 ≤ c.p.splitAbove) (B : NodeId) (hpos : 0 < c.i)
    (w w3 : W) (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth D : Nat) (w2 : W) (S : KNode)
    (hI : PutInv c base w) (hRO : RangeOrder (wNode c.p base w) c.i w.top.rootKey)
    (hr03 : ReadsAs c.p base w w3) (hJw : TakeJ2 c base B w) (hBn : B ≤ w.next)
    (hkidsw : ∀ c' z, (c', z) ∈ (Nn depth).liveAt c.i → wNode c.p base w z = none)
    (hpX : ∀ i, i ≤ depth → (w3.path[i]?).map (·.2) = some (X i))
    (hpK : ∀ i, 0 < i → i ≤ depth → w3.path[i]? = some (some (K i), X i))
    (hlkX : ∀ i, i ≤ depth → w3.nodes.lookup (X i) = some (Nn i))
    (hXN : ∀ i, i ≤ depth → wNode c.p base w (X i) = some (Nn i))
    (hlinkK : ∀ i, 0 < i → i ≤ depth → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (hsD : D + 1 < depth)
    (hbetween : ∀ i, D + 1 < i → i < depth →
      (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true)
    (hX0 : X 0 = w.top.rootKey)
    (hLE : UpLoopEnd c B X Nn depth (D + 1) w3 w2 S)
    (hsl : (Nn (D + 1)).leaf = false) (hK0 : K (D + 1 + 1) = 0)
    (hT2 : TreeOK (wNode c.p base w2) c.i w2.top.rootKey)
    (hlinks2 : ∀ u c' z, TLink (wNode c.p base w2) c.i u c' z → z < w2.next)
    (hwf2 : ∀ z zn, wNode c.p base w2 z = some zn → klongsWf zn.ks = true)
    (compact : Bool) (s : String) (t : Klong) (c1 : Nat) (y1 : NodeId) (r : List Klong)
    (hks : (S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf 0))).ks = t :: .key c1 y1 :: r) :
    WriterWP (handleFull (D + 1) (X (D + 1))
      { S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf 0)) with ks := t :: .key 0 y1 :: r } compact)
      c ({ w2 with trail := s :: w2.trail } : W) (fun _ w' => TakeJ2 c base B w' ∧ B ≤ w'.next) := by
  have hT := hI.tree
  have hdepth : 0 < depth := by omega
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
  have hI3 := putInv_of_readsAs c base w w3 hI hr03
  have htk3 : ∀ i, i ≤ depth → w3.taken.contains (X i) = false := fun i hi => by
    rw [hr03.2.2.1]; exact hI.untaken _ (tReach_reachS _ _ _ _ (hreach i hi))
  have hT3 : TreeOK (wNode c.p base w3) c.i w3.top.rootKey := by rw [hr03.1, hr03.2.1]; exact hT
  have hR3 : RangeOrder (wNode c.p base w3) c.i w3.top.rootKey := by rw [hr03.1, hr03.2.1]; exact hRO
  have hreach3 : ∀ i, i ≤ depth → TReach (wNode c.p base w3) c.i w3.top.rootKey (X i) := fun i hi => by
    rw [hr03.1, hr03.2.1]; exact hreach i hi
  -- the chain's facts at w3 from its order
  have hP3 : PathOK c w3 depth X K Nn :=
    ⟨hpX, hpK, fun i hi => ⟨hlkX i hi, htk3 i hi⟩, hlinkK, by rw [hr03.2.1, hX0]⟩
  have hO := ordG_of_rangeOrder c _ _ hR3 (fun x n h => hI3.times x n h)
  have hwX : ∀ j, j ≤ depth → wNode c.p base w3 (X j) = some (Nn j) := hN3
  -- the loop's end
  obtain ⟨h2t, h2top, h2v, h2p, _, h2nx, h2n, hSl, hS, hSR, hSF', hfate2, hfateJ2⟩ := hLE
  -- the stop node now
  have hXs : ∀ k, D + 1 < k → k ≤ depth → X (D + 1) ≠ X k :=
    fun k h1 h2 he => by have := hdist (D + 1) k (by omega) h2 he; omega
  have hst_t : ∀ s', Klong.time s' ∈ (Nn (D + 1)).ks → s' ≤ c.i := hI.times _ _ (hXN (D + 1) (by omega))
  have hsx : (K (D + 1 + 1), X (D + 1 + 1)) ∈ (Nn (D + 1)).liveAt c.i := by
    have := hlinkK (D + 1 + 1) (by omega) (by omega); simpa using this
  have hswf : klongsWf (Nn (D + 1)).ks = true := hI.wf _ _ (hXN (D + 1) (by omega))
  have hu : ∀ c', (c', X (D + 1 + 1)) ∈ (Nn (D + 1)).liveAt c.i → c' = K (D + 1 + 1) := by
    intro c' h
    exact (hT.oneLink _ _ _ _ _ (hreach (D + 1) (by omega)) (hreach (D + 1) (by omega))
      ⟨_, hXN (D + 1) (by omega), h⟩ ⟨_, hXN (D + 1) (by omega), hsx⟩).2
  have hSf : S.leaf = (Nn (D + 1)).leaf ∧ klongsWf S.ks = true ∧
      (∀ s, Klong.time s ∈ S.ks → s ≤ c.i) ∧
      ∀ c' z, ((c', z) ∈ S.liveAt c.i ∧ c' ≠ K (D + 1 + 1)) ↔
        ((c', z) ∈ (Nn (D + 1)).liveAt c.i ∧ c' ≠ K (D + 1 + 1)) := by
    rcases hS with rfl | ⟨ti, dst, rfl⟩
    · exact ⟨rfl, hswf, hst_t, fun _ _ => Iff.rfl⟩
    · exact ⟨rfl, by rw [klongsWf_retargetKlongs]; exact hswf,
        KNode.retarget_times _ _ _ _ _ hst_t, KNode.retarget_liveAt_ne _ _ _ _ _ _ hu⟩
  obtain ⟨hSleaf, hSwf, hSt, hSlive⟩ := hSf
  have htk2 : w2.taken.contains (X (D + 1)) = false := by rw [h2t _ hXs]; exact htk3 (D + 1) (by omega)
  have hagree2 : ∀ u, u ≠ X (D + 1) → (∀ i, D + 1 < i → i ≤ depth → u ≠ X i) →
      wNode c.p base w2 u = wNode c.p base w3 u := fun u hus hnc => by
    simp only [wNode, h2t u hnc, h2n u hus hnc]
  -- the chain above the stop node, unchanged
  have hXne : ∀ i, i ≤ D → ∀ k, D + 1 ≤ k → k ≤ depth → X i ≠ X k :=
    fun i hi k h1 h2 he => by have := hdist i k (by omega) h2 he; omega
  have hlk2 : ∀ i, i ≤ D → w2.nodes.lookup (X i) = some (Nn i) := fun i hi => by
    rw [h2n (X i) (hXne i hi (D + 1) (Nat.le_refl _) (by omega))
      (fun k h1 h2 => hXne i hi k (by omega) h2)]
    exact hlkX i (by omega)
  have htk2' : ∀ i, i ≤ D → w2.taken.contains (X i) = false := fun i hi => by
    rw [h2t (X i) (fun k h1 h2 => hXne i hi k (by omega) h2)]; exact htk3 i (by omega)
  -- the chain with the stop node's current node
  generalize hNn' : (fun i => if i = D + 1 then S else Nn i) = Nn'
  have hNn'S : Nn' (D + 1) = S := by rw [← hNn']; simp
  have hNn'i : ∀ i, i ≤ D → Nn' i = Nn i := fun i hi => by
    rw [← hNn']; simp only [show i ≠ D + 1 by omega, ↓reduceIte]
  have hCO : ∀ i, 0 < i → i ≤ D → ChainOrd c K Nn' i := by
    intro i h1 h2
    have h := chainOrd_of_ordG c base w3 depth X K Nn hP3 hO i h1 (by omega)
    unfold ChainOrd at h ⊢
    rw [hNn'i i h2, hNn'i (i - 1) (by omega)]
    exact h
  have hJ3 : TakeJ2 c base B w3 := takeJ2_of_readsAs c base B w w3 hJw hr03
  have hone : ∀ i, D + 1 < i → i < depth → ∀ c' z, (c', z) ∈ (Nn i).liveAt c.i → z = X (i + 1) := by
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
  have hS2w : wNode c.p base w2 (X (D + 1)) = some S := by
    simp only [wNode, htk2, Bool.false_eq_true, ↓reduceIte, hSl]
  have hrest2 := j2rest_up (wNode c.p base w3) (wNode c.p base w2) c.i B (w3.vals.map (·.1)) X Nn (D + 1)
    depth (K (D + 1 + 1)) hsD hpos hJ3.2.1 hJ3.2.2.1 hJ3.2.2.2.1 hJ3.2.2.2.2.1 hJ3.2.2.2.2.2
    (fun i _ hi => hN3 i hi) (fun i i' _ hi _ hi' he => hdist i i' hi hi' he)
    (by
      intro k h1 h2
      obtain ⟨hm, hu'⟩ := hfateJ2 k h1 h2
      refine ⟨fun hf => by simp only [wNode, hm hf, ↓reduceIte], fun hf => ?_⟩
      obtain ⟨ht0, S0, hS0, hl0⟩ := hu' hf
      exact ⟨S0, hS0, by simp only [wNode, ht0, Bool.false_eq_true, ↓reduceIte, hl0]⟩)
    hswf hst_t hsx S S (fun _ => False) hSR hSF' hS2w rfl (fun s h => h)
    (fun i c' y h => Or.inl h) (fun y h => h.elim)
    (fun c' y hm hc => ⟨c', ((hSlive c' y).mpr ⟨hm, hc⟩).1⟩)
    (fun hl => ⟨hl, fun i c' hL _ => hL⟩) hagree2
  rw [hK0] at hSlive
  -- the stop node's last version with the empty key in the next klong's place
  obtain ⟨hleq', hlwf, hlt, hlastV, hlen2, hjS, hj0, hminS, hliveS⟩ := lebLast_facts c S hsa2 hSt t c1 y1 r hks
  obtain ⟨pairs, hpks, hpnd⟩ := lebLast_pairs c S t c1 y1 r hks
  generalize hlast : ({ S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf 0)) with
    ks := t :: .key 0 y1 :: r } : KNode) = last
  have hlks : last.ks = t :: .key 0 y1 :: r := by rw [← hlast]
  rw [← hlks] at hlwf hlt hlastV hlen2 hliveS hpks
  have hleqL : (⟨S.leaf, last.ks⟩ : KNode) = last := by rw [hlks, hleq', hlast]
  replace hlastV : (⟨S.leaf, last.ks⟩ : KNode).lastVersion c.i = last := hlastV.trans hleqL
  have hlen2' : c.p.splitAbove < last.size → 2 ≤ (⟨S.leaf, last.ks⟩ : KNode).live.length := by
    intro h; apply hlen2; rw [hleqL]; exact h
  have hj : (c1, y1) ∈ (Nn (D + 1)).liveAt c.i := ((hSlive c1 y1).mp ⟨hjS, by omega⟩).1
  have hliveL : ∀ c' z, (c', z) ∈ (⟨S.leaf, last.ks⟩ : KNode).liveAt c.i ↔
      (c' = 0 ∧ z = y1) ∨ ((c', z) ∈ (Nn (D + 1)).liveAt c.i ∧ c' ≠ 0 ∧ c' ≠ c1) := by
    intro c' z
    rw [hliveS c' z]
    constructor
    · rintro (h | ⟨h1, h2, h3⟩)
      · exact Or.inl h
      · exact Or.inr ⟨((hSlive c' z).mp ⟨h1, h2⟩).1, h2, h3⟩
    · rintro (h | ⟨h1, h2, h3⟩)
      · exact Or.inl h
      · exact Or.inr ⟨((hSlive c' z).mpr ⟨h1, h2⟩).1, h2, h3⟩
  have hliveF : ∀ c' z, (c', z) ∈ (⟨S.leaf, last.ks⟩ : KNode).liveAt c.i →
      ∃ c0, (c0, z) ∈ (Nn (D + 1)).liveAt c.i ∧ c0 ≠ K (D + 1 + 1) ∧
        (fun c'' => if c'' = c1 then 0 else c'') c0 = c' := by
    intro c' z h
    rcases (hliveL c' z).mp h with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · refine ⟨c1, by rw [h2]; exact hj, by rw [hK0]; omega, ?_⟩
      simp [h1]
    · exact ⟨c', h1, by rw [hK0]; exact h2, by simp [h3]⟩
  have hkeep : ∀ c' z, (c', z) ∈ (Nn (D + 1)).liveAt c.i → z ≠ X (D + 1 + 1) →
      ∃ c'', (c'', z) ∈ (⟨S.leaf, last.ks⟩ : KNode).liveAt c.i := by
    intro c' z hm hz
    by_cases hcj : c' = c1
    · rw [hcj] at hm
      have hzy : y1 = z := KNode.liveAt_fun _ _ _ _ _ hj hm
      exact ⟨0, (hliveL 0 z).mpr (Or.inl ⟨rfl, hzy.symm⟩)⟩
    · have hc0 : c' ≠ 0 := by
        intro h0
        rw [h0] at hm
        have hsx0 : (0, X (D + 1 + 1)) ∈ (Nn (D + 1)).liveAt c.i := by
          have h := hsx; rw [hK0] at h; exact h
        exact hz (KNode.liveAt_fun _ _ _ _ _ hsx0 hm).symm
      exact ⟨c', (hliveL c' z).mpr (Or.inr ⟨hm, hc0, hcj⟩)⟩
  generalize hv0 : ({ w2 with trail := s :: w2.trail } : W) = v
  have hvn : v.nodes = w2.nodes := by rw [← hv0]
  have hvt : v.taken = w2.taken := by rw [← hv0]
  have hvtop : v.top = w2.top := by rw [← hv0]
  have hvv : v.vals = w2.vals := by rw [← hv0]
  have hvnx : v.next = w2.next := by rw [← hv0]
  have hvp : v.path = w3.path := by rw [← hv0]; exact h2p
  have hwv : wNode c.p base v = wNode c.p base w2 := by
    funext z; simp only [wNode, hvn, hvt]
  have hlkv : v.nodes.lookup (X (D + 1)) = some S := by rw [hvn]; exact hSl
  have htk' : v.taken.contains (X (D + 1)) = false := by rw [hvt]; exact htk2
  have hroot' : v.top.rootKey = w3.top.rootKey := by rw [hvtop, h2top]
  have hnx' : v.next = w3.next := by rw [hvnx, h2nx]
  have hXlt : ∀ i, i ≤ depth → X i < w3.next := fun i hi => hI3.ids.1 (X i) (by rw [hlkX i hi]; rfl)
  have hS5 : ∀ z, v.next ≤ z → v.nodes.lookup z = none ∧ v.taken.contains z = false ∧
      knodeOf c.p base z = none := by
    intro z hz
    rw [hnx'] at hz
    have hzX : ∀ i, i ≤ depth → z ≠ X i := fun i hi he => by have := hXlt i hi; omega
    refine ⟨?_, ?_, (hI.fresh z (by rw [← hr03.2.2.2.2]; exact hz)).1⟩
    · rw [hvn, h2n z (hzX (D + 1) (by omega)) (fun i _ hi => hzX i hi)]
      cases h' : w3.nodes.lookup z with
      | none => rfl
      | some _ => have := hI3.ids.1 z (by rw [h']; rfl); omega
    · rw [hvt, h2t z (fun i _ hi => hzX i hi)]
      cases h' : w3.taken.contains z with
      | false => rfl
      | true => have := hI3.ids.2.2.1 z h'; omega
  have hS6 : ∀ u c' z, TLink (wNode c.p base v) c.i u c' z → z < v.next := by
    rw [hwv, hvnx]; exact hlinks2
  have hW : ∀ z zn, wNode c.p base v z = some zn → klongsWf zn.ks = true := by
    rw [hwv]; exact hwf2
  have hS2' : ∀ i, 0 ≤ i → i ≤ D + 1 →
      v.nodes.lookup (X i) = some (Nn' i) ∧ v.taken.contains (X i) = false := by
    intro i _ hi
    rcases Nat.lt_or_ge i (D + 1) with h | h
    · rw [hNn'i i (by omega)]
      exact ⟨by rw [hvn]; exact hlk2 i (by omega), by rw [hvt]; exact htk2' i (by omega)⟩
    · have hi' : i = D + 1 := by omega
      subst hi'
      rw [hNn'S]
      exact ⟨hlkv, htk'⟩
  have hT2' : TreeOK (wNode c.p base v) c.i v.top.rootKey := by
    rw [hwv, hvtop]; exact hT2
  have hS4' : ∀ i, 0 ≤ i → i ≤ D + 1 → TReach (wNode c.p base v) c.i v.top.rootKey (X i) := by
    intro i _ hi
    rw [hwv, hroot']
    induction i with
    | zero => rw [hr03.2.1, hX0]; exact TReach.root
    | succ i ih =>
      have hi' : i ≤ D := by omega
      refine TReach.link (ih (Nat.zero_le _) (by omega)) ⟨Nn i, ?_, by
        have := hlinkK (i + 1) (by omega) (by omega); simpa using this⟩
      simp only [wNode, htk2' i hi', Bool.false_eq_true, ↓reduceIte, hlk2 i hi']
  -- the tree with the stop node's last version
  have hagreeV : ∀ u, u ≠ X (D + 1) → (∀ i, D + 1 < i → i ≤ depth → u ≠ X i) →
      updN (wNode c.p base v) (X (D + 1)) ⟨S.leaf, last.ks⟩ u = wNode c.p base w3 u := fun u hus hnc => by
    rw [updN_ne _ _ _ _ hus, hwv]; exact hagree2 u hus hnc
  have hsnV : updN (wNode c.p base v) (X (D + 1)) ⟨S.leaf, last.ks⟩ (X (D + 1)) = some ⟨S.leaf, last.ks⟩ :=
    updN_self _ _ _
  have hV : TreeOK (updN (wNode c.p base v) (X (D + 1)) ⟨S.leaf, last.ks⟩) c.i v.top.rootKey := by
    rw [hroot']
    exact treeOK_up_tr (wNode c.p base w3) _ c.i w3.top.rootKey X Nn K (D + 1) depth hsD hT3
      (hreach3 (D + 1) (by omega)) (fun i _ hi => hN3 i hi) (fun i h1 hi => hlinkK i (by omega) hi)
      (fun i i' _ hi _ hi' he => hdist i i' hi hi' he) hagreeV _ hsnV _ hliveF
  have hvx : ∀ c' z, (c', z) ∈ (⟨S.leaf, last.ks⟩ : KNode).liveAt c.i → z < v.next := by
    intro c' z h
    rw [hnx', hr03.2.2.2.2]
    obtain ⟨c0, hc0, _, _⟩ := hliveF c' z h
    exact hI.links (X (D + 1)) (Nn (D + 1)) c0 z (tReach_reachS _ _ _ _ (hreach (D + 1) (by omega)))
      (hXN (D + 1) (by omega)) hc0
  -- the chain's ranges and lengths
  have hrange : ∀ i, 0 < i → i ≤ D → ¬ ChainRoom c (Nn' i) → (Nn' (i - 1)).leaf = false →
      ∀ c' z, (c', z) ∈ (Nn' i).live → 0 < c' →
      K i ≤ c' ∧ ∀ c'' z', (c'', z') ∈ (Nn' (i - 1)).live → K i < c'' → c' < c'' := by
    intro i h1 hi hNR hql' c' z hz hpos
    rw [hNn'i i hi] at hNR hz
    rw [hNn'i (i - 1) (by omega)] at hql' ⊢
    exact rangeG_of_rangeOrder c _ _ hR3 (fun x n h => hI3.times x n h) (X (i - 1)) (Nn (i - 1)) (X i) (Nn i)
      (K i) (hreach3 (i - 1) (by omega)) (hwX (i - 1) (by omega)) hql' (hlinkK i h1 (by omega))
      (hwX i (by omega)) hNR c' z hz hpos
  have hlen : ∀ i, 0 ≤ i → i ≤ D → ¬ ChainRoom c (Nn' i) →
      c.p.splitAbove < ((Nn' i).lastVersion c.i).size → 2 ≤ (Nn' i).live.length := by
    intro i _ hi hNR hsp
    rw [hNn'i i hi] at hNR hsp ⊢
    exact lenG_of_splitAbove c _ _ hsa2 (X i) (Nn i) (hreach3 i (by omega)) (hwX i (by omega)) hNR hsp
  have hwf' : ∀ i, 0 ≤ i → i ≤ D + 1 → klongsWf (Nn' i).ks = true := by
    intro i _ hi
    rcases Nat.lt_or_ge i (D + 1) with h | h
    · rw [hNn'i i (by omega)]; exact hI.wf _ _ (hXN i (by omega))
    · rw [show i = D + 1 by omega, hNn'S]; exact hSwf
  have htimes' : ∀ i, 0 ≤ i → i ≤ D + 1 → ∀ t, Klong.time t ∈ (Nn' i).ks → t ≤ c.i := by
    intro i _ hi
    rcases Nat.lt_or_ge i (D + 1) with h | h
    · rw [hNn'i i (by omega)]; exact hI.times _ _ (hXN i (by omega))
    · rw [show i = D + 1 by omega, hNn'S]; exact hSt
  have hlinkK' : ∀ i, 0 < i → i ≤ D + 1 → (K i, X i) ∈ (Nn' (i - 1)).liveAt c.i := by
    intro i h1 hi
    rw [hNn'i (i - 1) (by omega)]; exact hlinkK i h1 (by omega)
  have hdist' : ∀ i i', 0 ≤ i → i ≤ D + 1 → 0 ≤ i' → i' ≤ D + 1 → X i = X i' → i = i' :=
    fun i i' _ hi _ hi' he => hdist i i' (by omega) (by omega) he
  have hspace : ∀ i, 0 ≤ i → i ≤ D → ¬ ChainRoom c (Nn' i) →
      c.p.splitAbove < ((Nn' i).lastVersion c.i).size → i = 0 ∨ (0 < i ∧ ((Nn' (i - 1)).leaf = false ∨
        ((Nn' i).firstTime ≠ some c.i → ∀ i', 0 < i' → i' < i → ChainOrd c K Nn' i'))) := by
    intro i _ hi hNR hsp
    rcases Nat.eq_zero_or_pos i with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, Or.inr (fun _ i' h1 h2 => hCO i' h1 (by omega))⟩
  -- the stop node's last version under its parent
  have hkl : (K (D + 1), X (D + 1)) ∈ (Nn D).liveAt c.i := by
    have := hlinkK (D + 1) (by omega) (by omega); simpa using this
  have hrangeLn : (Nn D).leaf = false → ∀ c' z, (c', z) ∈ (⟨S.leaf, last.ks⟩ : KNode).live → 0 < c' →
      K (D + 1) ≤ c' ∧ ∀ c'' z', (c'', z') ∈ (Nn D).live → K (D + 1) < c'' → c' < c'' := by
    intro hql c' z hz hpos'
    have hz' : (c', z) ∈ (⟨S.leaf, last.ks⟩ : KNode).liveAt c.i := by
      rw [KNode.liveAt_of_times (⟨S.leaf, last.ks⟩ : KNode) c.i hlt]; exact hz
    have hzn : (c', z) ∈ (Nn (D + 1)).liveAt c.i := by
      rcases (hliveL c' z).mp hz' with ⟨h1, _⟩ | ⟨h1, _, _⟩
      · omega
      · exact h1
    obtain ⟨hP1, hP2⟩ := mrg_child_range (wNode c.p base w3) c.i w3.top.rootKey hR3 (X D) (Nn D)
      (tReach_reachS _ _ _ _ (hreach3 D (by omega))) (hwX D (by omega)) hql (K (D + 1)) (X (D + 1))
      (Nn (D + 1)) hkl (hwX (D + 1) (by omega))
    refine ⟨?_, ?_⟩
    · rcases Nat.eq_zero_or_pos (K (D + 1)) with hk0 | hk0
      · omega
      · cases hl : (Nn (D + 1)).leaf with
        | true => exact (hP1 c' z hzn).1 hl hk0
        | false =>
          rcases (hP1 c' z hzn).2 hl with h | h
          · omega
          · exact Nat.le_of_lt (h hk0)
    · intro c'' z' hz2 hlt2
      exact hP2 c'' z' (by rw [KNode.liveAt_of_times _ c.i (hI3.times _ _ (hwX D (by omega)))]; exact hz2)
        hlt2 c' z hzn
  -- the nodes of the transaction's time, reached in the tree with the stop node's last version
  have hTtV := ttReachedN_up (wNode c.p base w3) (updN (wNode c.p base v) (X (D + 1)) ⟨S.leaf, last.ks⟩) c.i
    w3.top.rootKey X Nn (D + 1) depth hsD (fun i _ hi => hN3 i hi) hone
    (fun c' z h => by rw [hr03.1]; exact hkidsw c' z h) _ hsnV hkeep
    hagreeV hXs (hreach3 (D + 1) (by omega))
    (by
      intro k h1 h2 un hun
      rw [updN_ne _ _ _ _ (Ne.symm (hXs k h1 h2)), hwv] at hun
      rcases hfate2 k h1 h2 with hf | ⟨S0, hS0, hnt0⟩
      · unfold wNode at hun; rw [hf] at hun; cases hun
      · have hkt : w2.taken.contains (X k) = false := by
          cases hc : w2.taken.contains (X k) with
          | false => rfl
          | true => unfold wNode at hun; rw [hc] at hun; cases hun
        simp only [wNode, hkt, Bool.false_eq_true, ↓reduceIte, hS0, Option.some.injEq] at hun
        rw [← hun]; exact hnt0)
    hJ3.1
  have hTU : ∀ q qn, wNode c.p base v q = some qn → Klong.time c.i ∈ qn.ks →
      TReach (updN (wNode c.p base v) (X (D + 1)) (⟨(Nn' (D + 1)).leaf, last.ks⟩ : KNode)) c.i
        v.top.rootKey q := by
    intro q qn hq hm
    rw [hNn'S]
    by_cases hqs : q = X (D + 1)
    · rw [hqs]
      exact tReach_updN_self _ c.i _ _ _ hT2' (hS4' (D + 1) (Nat.zero_le _) (Nat.le_refl _))
    · rw [hroot']
      exact hTtV q qn (by rw [updN_ne _ _ _ _ hqs]; exact hq) hm
  have hvals2 : v.vals = w3.vals := by rw [hvv, h2v]
  have hrest' : DeadLiveN (wNode c.p base v) c.i B (v.vals.map (·.1)) ∧
      OldBelowN (wNode c.p base v) c.i B ∧ OldStartN (wNode c.p base v) c.i B ∧
      MadeStartN (wNode c.p base v) c.i B ∧ ValsNoNodeN (wNode c.p base v) (v.vals.map (·.1)) := by
    rw [hwv, hvals2]; exact hrest2
  -- the order of the stop node's last version under its parent
  have hLO : LastOrd c K Nn' D last := by
    intro _ hql c' z hz
    rw [hNn'i D (Nat.le_refl _)] at hql
    rw [hNn'S] at hz ⊢
    have hz' : (c', z) ∈ (⟨S.leaf, last.ks⟩ : KNode).liveAt c.i := by
      rw [KNode.liveAt_of_times (⟨S.leaf, last.ks⟩ : KNode) c.i hlt]; exact hz
    have hSl' : S.leaf = (Nn (D + 1)).leaf := hSleaf
    have hnl : ¬ (S.leaf = true) := by rw [hSl', hsl]; simp
    simp only [hnl]
    rcases (hliveL c' z).mp hz' with ⟨h1, _⟩ | ⟨hzn, _, _⟩
    · exact Or.inl h1
    · obtain ⟨hP1, _⟩ := mrg_child_range (wNode c.p base w3) c.i w3.top.rootKey hR3 (X D) (Nn D)
        (tReach_reachS _ _ _ _ (hreach3 D (by omega))) (hwX D (by omega)) hql (K (D + 1)) (X (D + 1))
        (Nn (D + 1)) hkl (hwX (D + 1) (by omega))
      rcases (hP1 c' z hzn).2 hsl with h | h
      · exact Or.inl h
      · rcases Nat.eq_zero_or_pos (K (D + 1)) with hk0 | hk0
        · rcases Nat.eq_zero_or_pos c' with hc0 | hc0
          · exact Or.inl hc0
          · exact Or.inr (by omega)
        · exact Or.inr (h hk0)
  exact writerWP_handleFull_last_j2U (c.p.fuel + 1) (by unfold Params.fuel; omega) c base B hpos v
    hrest' (by rw [hnx', hr03.2.2.2.2]; exact hBn)
    (by
      intro y hy
      rw [hvals2] at hy
      rw [hnx']
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy
      exact hI3.ids.2.2.2.1 e he)
    D X K Nn' (fun i _ hi => by rw [hvp]; exact hpX i (by omega))
    (fun i h1 hi => by rw [hvp]; exact hpK i h1 (by omega)) hlinkK' hrange hlen hwf' htimes' hdist'
    hspace hCO last compact hlwf hlt (by rw [hNn'S]; exact hlastV) (by rw [hNn'S]; exact hlen2')
    (by
      intro _ hql c' z hz hpos'
      rw [hNn'S] at hz
      rw [hNn'i D (Nat.le_refl _)] at hql ⊢
      exact hrangeLn hql c' z hz hpos')
    (fun _ => Or.inr (fun _ i' h1 h2 => hCO i' h1 (by omega))) ⟨pairs, hpks, hpnd⟩ hLO hS2' hT2' hS4' hS5
    hS6 (by rw [hroot', hr03.2.1, hX0]) hW (by rw [hNn'S]; exact hV) (by rw [hNn'S]; exact hvx) hTU

/-- `UpLebFullJ2OK` from the state after the upward loop (`UpUnlinkOK`,
`UpUnlinkLinksOK`): at the space root by `writerWP_upLebFull_root_j2`, below it
by `writerWP_upLebFull_below_j2`. -/
theorem upLebFullJ2OK_of_parts (c : Ctx) (base : View BVal) (KO : KindOracle) (BK B : NodeId)
    (hU : UpUnlinkOK c base) (hL : UpUnlinkLinksOK c base) : UpLebFullJ2OK c base KO BK B := by
  intro w w3 top0 pre cv rk X Nn K depth stop w2 S hsa2 hvB hk hICEk hX0 hpos hB hI hRO hF hICE hr03 hkey
    hrk hvis hpX hpK hlkX hXN hlinkK hne hall hleaf hdepth hsD hbetween hLE hJ hsl hK0 hsm hJw _hMF hkidsw
    compact s t c1 y1 r hks
  have hBn : B ≤ w.next := by
    have h1 : B ≤ w2.next := hJ.1.1.fresh.1
    rw [hLE.2.2.2.2.2.1, hr03.2.2.2.2] at h1
    exact h1
  obtain ⟨hT2, _⟩ := hU w w3 B X Nn K depth stop w2 S hI hr03 hlkX hlinkK hsD hLE
  obtain ⟨hlinks2, hwf2⟩ := hL w w3 B X Nn K depth stop w2 S hI hr03 hlkX hlinkK hsD hLE
  rcases Nat.eq_zero_or_pos stop with hs | hs
  · subst hs
    exact writerWP_upLebFull_root_j2 c base hB.coherent hsa2 B hpos w w3 X Nn K depth w2 S hI hr03 hJw hBn
      hkidsw hlkX hXN hlinkK hdepth hbetween hX0 hLE hK0 hT2 hlinks2 hwf2 compact s t c1 y1 r hks
  · obtain ⟨D, rfl⟩ : ∃ D, stop = D + 1 := ⟨stop - 1, by omega⟩
    exact writerWP_upLebFull_below_j2 c base hsa2 B hpos w w3 X Nn K depth D w2 S hI hRO hr03 hJw hBn hkidsw
      hpX hpK hlkX hXN hlinkK hsD hbetween hX0 hLE hsl hK0 hT2 hlinks2 hwf2 compact s t c1 y1 r hks

/-- `DelStepsJ2OKF3` (the F3 route over R's pointers and kinds) with LE-b proved
(`upLebJ2OKF3_of_full`, `upLebFullOKF3_of_parts`, `upLebFullJ2OK_of_parts`):
open are the state after the upward loop (`UpUnlinkOK`, `UpUnlinkLinksOK`), the
fuel after the splits (`UpCascFitsOK`, `UpLebFitsOK`, `DelFullFitsOK`) and the
S inputs. -/
theorem delStepsJ2OKF3_of_openR4 (p : Params) (R : Struct BVal → Time → Prop)
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
    (hFitL : ∀ ts BK, UpLebFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) BK)
    (hFits : ∀ ts, DelFullFitsOK (ctxOf p ts) (viewOf (treeRun p ts))) :
    DelStepsJ2OKF3 p R S :=
  delStepsJ2OKF3_of_openR3 p R S hM hsa2 hRL hRP hRK hSI hSV hSB hSR hSF hSM hU hL hFit
    (fun ts BK => upLebFullOKF3_of_parts _ _ _ _ (hU ts) (hL ts) (hFitL ts BK))
    (fun ts _ B => upLebFullJ2OK_of_parts _ _ _ _ B (hU ts) (hL ts)) hFits

end SIS.Tree
