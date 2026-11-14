/-
The stop node's cascade below the space root from the state after the upward
loop as a tree, without its ranges (bergdb 024-12, `UpUnlinkTreeOK`): the split's
ranges come from the tree with the stop node's last version
(`rangeOrder_up_bitmap`, `writerWP_delSplit_chainGRangeV`), so `UpUnlinkOK`'s
`RangeOrder` part is not needed.
-/
import SIS.Tree.DelStepsLinks

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- Named input (the take-back's, checked on runs with `UpUnlinkOK`): the state
after the upward loop is a tree. -/
def UpUnlinkTreeOK (c : Ctx) (base : View BVal) : Prop :=
  ∀ (w w3 : W) (MB : NodeId) (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth stop : Nat)
    (w2 : W) (S : KNode),
    PutInv c base w → ReadsAs c.p base w w3 →
    (∀ i, i ≤ depth → w3.nodes.lookup (X i) = some (Nn i)) →
    (∀ i, 0 < i → i ≤ depth → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i) → stop < depth →
    UpLoopEnd c MB X Nn depth stop w3 w2 S →
    TreeOK (wNode c.p base w2) c.i w2.top.rootKey

theorem upUnlinkTreeOK_of (c : Ctx) (base : View BVal) (h : UpUnlinkOK c base) : UpUnlinkTreeOK c base :=
  fun w w3 MB X Nn K depth stop w2 S hI hr hl hk hs hLE => (h w w3 MB X Nn K depth stop w2 S hI hr hl hk hs hLE).1

set_option maxHeartbeats 6400000 in
/-- `UpCascOKF3` below the space root (stop D + 1), the bitmap kinds: from the
state after the upward loop as a tree in order (`hT2`, `hR2`, `UpUnlinkOK`), its
links below the next id and its klongs well formed, and the state after the
cascade fitting the fuel, the stop node's bitmap puts the state into `DelInvF3`
(`writerWP_handleFull_lastVF2`, `writerWP_delSplit_chainGRange`). -/
theorem writerWP_upCasc_below_delF3T (c : Ctx) (base : View BVal)
    (hsa2 : 2 ≤ c.p.splitAbove)
    (KO : KindOracle) (BK : NodeId) (hvB : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c)
    (hICEk : ICEFromKinds c base KO BK)
    (w w3 : W) (B MB : NodeId) (top0 : Top) (pre : List Nat) (cv : Nat) (rk : NodeId)
    (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth D : Nat) (w2 v : W) (S : KNode)
    (hB : PutBase c base B) (hI : PutInv c base w)
    (hRO : RangeOrder (wNode c.p base w) c.i w.top.rootKey)
    (hF : SegFits (wNode c.p base w) c.i (c.p.fuel - 1) w.top.rootKey)
    (hr03 : ReadsAs c.p base w w3) (hkey : keyWf (pre ++ [cv]) = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hvis : (X depth, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk)
    (hpX : ∀ i, i ≤ depth → (w3.path[i]?).map (·.2) = some (X i))
    (hpK : ∀ i, 0 < i → i ≤ depth → w3.path[i]? = some (some (K i), X i))
    (hlkX : ∀ i, i ≤ depth → w3.nodes.lookup (X i) = some (Nn i))
    (hXN : ∀ i, i ≤ depth → wNode c.p base w (X i) = some (Nn i))
    (hlinkK : ∀ i, 0 < i → i ≤ depth → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (hall : (Nn depth).allKeysIn (bitsUnion (Nn depth).lastBitmap ((Nn depth).bitsOf cv)) = true)
    (hleaf : (Nn depth).leaf = true) (hsD : D + 1 < depth)
    (hbetween : ∀ i, D + 1 < i → i < depth →
      (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true)
    (hX0 : X 0 = w.top.rootKey)
    (hLE : UpLoopEnd c MB X Nn depth (D + 1) w3 w2 S)
    (hv : v = w2 ∨ ∃ s, v = { w2 with trail := s :: w2.trail })
    (hJ : KdJP c B top0 KO BK w3.path v)
    (hfull : ¬ DelRoom c (K (D + 1 + 1)) S)
    (hT2 : TreeOK (wNode c.p base w2) c.i w2.top.rootKey)
    (hlinks2 : ∀ u c' z, TLink (wNode c.p base w2) c.i u c' z → z < w2.next)
    (hwf2 : ∀ z zn, wNode c.p base w2 z = some zn → klongsWf zn.ks = true)
    (hFits : WriterWP (appendDeleteKlong (X (D + 1)) (D + 1) (K (D + 1 + 1))) c v
      (fun _ w' => SegFits (wNode c.p base w') c.i c.p.fuel w'.top.rootKey)) :
    WriterWP (appendDeleteKlong (X (D + 1)) (D + 1) (K (D + 1 + 1))) c v
      (fun _ w' => DelInvF3 c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK w') := by
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  have hT := hI.tree
  have hdepth : 0 < depth := by omega
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
  have hI3 := putInv_of_readsAs c base w w3 hI hr03
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
  -- the chain's facts at w3 from its order
  have hP3 : PathOK c w3 depth X K Nn :=
    ⟨hpX, hpK, fun i hi => ⟨hlkX i hi, htk3 i hi⟩, hlinkK, by rw [hr03.2.1, hX0]⟩
  have hO := ordG_of_rangeOrder c _ _ hR3 (fun x n h => hI3.times x n h)
  have hwX : ∀ j, j ≤ depth → wNode c.p base w3 (X j) = some (Nn j) := hN3
  -- the loop's end
  obtain ⟨h2t, h2top, h2v, _, _, h2nx, h2n, hSl, hS, hSR, hSF', hfate2, hfateJ2⟩ := hLE
  have hvn : v.nodes = w2.nodes := by rcases hv with rfl | ⟨s, rfl⟩ <;> rfl
  have hvt : v.taken = w2.taken := by rcases hv with rfl | ⟨s, rfl⟩ <;> rfl
  have hvtop : v.top = w2.top := by rcases hv with rfl | ⟨s, rfl⟩ <;> rfl
  have hvv : v.vals = w2.vals := by rcases hv with rfl | ⟨s, rfl⟩ <;> rfl
  have hvnx : v.next = w2.next := by rcases hv with rfl | ⟨s, rfl⟩ <;> rfl
  have hvp : v.path = w3.path := hJ.2
  have hwv : wNode c.p base v = wNode c.p base w2 := by
    funext z; simp only [wNode, hvn, hvt]
  -- the stop node now
  have hXs : ∀ k, D + 1 < k → k ≤ depth → X (D + 1) ≠ X k :=
    fun k h1 h2 he => by have := hdist (D + 1) k (by omega) h2 he; omega
  have hst_t : ∀ s', Klong.time s' ∈ (Nn (D + 1)).ks → s' ≤ c.i := hI.times _ _ (hXN (D + 1) (by omega))
  have hsx : (K (D + 1 + 1), X (D + 1 + 1)) ∈ (Nn (D + 1)).liveAt c.i := by
    have := hlinkK (D + 1 + 1) (by omega) (by omega); simpa using this
  have hneS : bitsUnion (Nn (D + 1)).lastBitmap ((Nn (D + 1)).bitsOf (K (D + 1 + 1))) ≠
      (Nn (D + 1)).lastBitmap := by
    apply KNode.delete_bitmap_changes_of_live
    have hsx' := hsx
    rw [KNode.liveAt_of_times _ c.i hst_t] at hsx'
    exact List.mem_map.mpr ⟨_, hsx', rfl⟩
  have hswf : klongsWf (Nn (D + 1)).ks = true := hI.wf _ _ (hXN (D + 1) (by omega))
  have hu : ∀ c', (c', X (D + 1 + 1)) ∈ (Nn (D + 1)).liveAt c.i → c' = K (D + 1 + 1) := by
    intro c' h
    exact (hT.oneLink _ _ _ _ _ (hreach (D + 1) (by omega)) (hreach (D + 1) (by omega))
      ⟨_, hXN (D + 1) (by omega), h⟩ ⟨_, hXN (D + 1) (by omega), hsx⟩).2
  have hSf : S.shapeOf = (Nn (D + 1)).shapeOf ∧ S.leaf = (Nn (D + 1)).leaf ∧ klongsWf S.ks = true ∧
      (∀ s, Klong.time s ∈ S.ks → s ≤ c.i) ∧
      ∀ c' z, ((c', z) ∈ S.liveAt c.i ∧ c' ≠ K (D + 1 + 1)) ↔
        ((c', z) ∈ (Nn (D + 1)).liveAt c.i ∧ c' ≠ K (D + 1 + 1)) := by
    rcases hS with rfl | ⟨ti, dst, rfl⟩
    · exact ⟨rfl, rfl, hswf, hst_t, fun _ _ => Iff.rfl⟩
    · exact ⟨KNode.retarget_shapeOf _ _ _ _, rfl, by rw [klongsWf_retargetKlongs]; exact hswf,
        KNode.retarget_times _ _ _ _ _ hst_t, KNode.retarget_liveAt_ne _ _ _ _ _ _ hu⟩
  obtain ⟨hSsh, hSleaf, hSwf, hSt, hSlive⟩ := hSf
  have hneS' : bitsUnion S.lastBitmap (S.bitsOf (K (D + 1 + 1))) ≠ S.lastBitmap := by
    rw [KNode.lastBitmap_of_shapeOf hSsh, KNode.bitsOf_of_shapeOf hSsh]; exact hneS
  have hlkv : v.nodes.lookup (X (D + 1)) = some S := by rw [hvn]; exact hSl
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
  have hfullM : WriterWP (appendDeleteKlong (X (D + 1)) (D + 1) (K (D + 1 + 1))) c v (fun _ w' =>
      SegFits (wNode c.p base w') c.i c.p.fuel w'.top.rootKey → PutBook c B top0 w' → Book BK c w' →
      KdInv KO BK w' → DelInvF3 c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK w') := by
    refine writerWP_appendDeleteKlong_full_of (X (D + 1)) (D + 1) (K (D + 1 + 1)) S c v hlkv hneS' hfull _ ?_
    intro compact s
    generalize hlast : S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf (K (D + 1 + 1)))) = last
    obtain ⟨hleq, hlwf, hlt, hlastV, hlen2, _, hiff, _⟩ :=
      delLast_split_facts c S (K (D + 1 + 1)) hsa2 hSt last hlast
    have hliveL : ∀ c' z, (c', z) ∈ (⟨S.leaf, last.ks⟩ : KNode).liveAt c.i ↔
        (c', z) ∈ (Nn (D + 1)).liveAt c.i ∧ c' ≠ K (D + 1 + 1) := by
      intro c' z; rw [hleq, hiff c' z]; exact hSlive c' z
    have hlk' : ({ v with trail := s :: v.trail } : W).nodes.lookup (X (D + 1)) = some S := hlkv
    have hroot' : ({ v with trail := s :: v.trail } : W).top.rootKey = w3.top.rootKey := by
      show v.top.rootKey = _; rw [hvtop, h2top]
    have hnx' : ({ v with trail := s :: v.trail } : W).next = w3.next := by
      show v.next = _; rw [hvnx, h2nx]
    have hwv' : wNode c.p base ({ v with trail := s :: v.trail } : W) = wNode c.p base w2 := hwv
    have hXlt : ∀ i, i ≤ depth → X i < w3.next := fun i hi => hI3.ids.1 (X i) (by rw [hlkX i hi]; rfl)
    have hS5 : ∀ z, ({ v with trail := s :: v.trail } : W).next ≤ z →
        ({ v with trail := s :: v.trail } : W).nodes.lookup z = none ∧
        ({ v with trail := s :: v.trail } : W).taken.contains z = false ∧ knodeOf c.p base z = none := by
      intro z hz
      rw [hnx'] at hz
      have hzX : ∀ i, i ≤ depth → z ≠ X i := fun i hi he => by have := hXlt i hi; omega
      refine ⟨?_, ?_, (hI.fresh z (by rw [← hr03.2.2.2.2]; exact hz)).1⟩
      · show v.nodes.lookup z = none
        rw [hvn, h2n z (hzX (D + 1) (by omega)) (fun i _ hi => hzX i hi)]
        cases h' : w3.nodes.lookup z with
        | none => rfl
        | some _ => have := hI3.ids.1 z (by rw [h']; rfl); omega
      · show v.taken.contains z = false
        rw [hvt, h2t z (fun i _ hi => hzX i hi)]
        cases h' : w3.taken.contains z with
        | false => rfl
        | true => have := hI3.ids.2.2.1 z h'; omega
    have hS6 : ∀ u c' z, TLink (wNode c.p base ({ v with trail := s :: v.trail } : W)) c.i u c' z →
        z < ({ v with trail := s :: v.trail } : W).next := by
      rw [hwv']; intro u c' z hl
      show z < v.next
      rw [hvnx]; exact hlinks2 u c' z hl
    have hW : ∀ z zn, wNode c.p base ({ v with trail := s :: v.trail } : W) z = some zn →
        klongsWf zn.ks = true := by
      rw [hwv']; exact hwf2
    have hS2' : ∀ i, 0 ≤ i → i ≤ D + 1 →
        ({ v with trail := s :: v.trail } : W).nodes.lookup (X i) = some (Nn' i) ∧
        ({ v with trail := s :: v.trail } : W).taken.contains (X i) = false := by
      intro i _ hi
      rcases Nat.lt_or_ge i (D + 1) with h | h
      · rw [hNn'i i (by omega)]
        exact ⟨by show v.nodes.lookup _ = _; rw [hvn]; exact hlk2 i (by omega),
          by show v.taken.contains _ = false; rw [hvt]; exact htk2' i (by omega)⟩
      · have hi' : i = D + 1 := by omega
        subst hi'
        rw [hNn'S]
        exact ⟨hlkv, by show v.taken.contains _ = false; rw [hvt]; exact htk2⟩
    have hT2' : TreeOK (wNode c.p base ({ v with trail := s :: v.trail } : W)) c.i
        ({ v with trail := s :: v.trail } : W).top.rootKey := by
      rw [hwv']; show TreeOK _ c.i v.top.rootKey; rw [hvtop]; exact hT2
    have hS4' : ∀ i, 0 ≤ i → i ≤ D + 1 → TReach (wNode c.p base ({ v with trail := s :: v.trail } : W)) c.i
        ({ v with trail := s :: v.trail } : W).top.rootKey (X i) := by
      intro i _ hi
      rw [hwv', hroot']
      induction i with
      | zero => rw [hr03.2.1, hX0]; exact TReach.root
      | succ i ih =>
        have hi' : i ≤ D := by omega
        refine TReach.link (ih (Nat.zero_le _) (by omega)) ⟨Nn i, ?_, by
          have := hlinkK (i + 1) (by omega) (by omega); simpa using this⟩
        simp only [wNode, htk2' i hi', Bool.false_eq_true, ↓reduceIte, hlk2 i hi']
    have hpath' : ({ v with trail := s :: v.trail } : W).path = w3.path := hvp
    -- the tree with the stop node's last version
    have hagreeV : ∀ u, u ≠ X (D + 1) → (∀ i, D + 1 < i → i ≤ depth → u ≠ X i) →
        updN (wNode c.p base ({ v with trail := s :: v.trail } : W)) (X (D + 1)) ⟨S.leaf, last.ks⟩ u =
          wNode c.p base w3 u := fun u hus hnc => by
      rw [updN_ne _ _ _ _ hus, hwv']; exact hagree2 u hus hnc
    have hsnV : updN (wNode c.p base ({ v with trail := s :: v.trail } : W)) (X (D + 1)) ⟨S.leaf, last.ks⟩
        (X (D + 1)) = some ⟨S.leaf, last.ks⟩ := updN_self _ _ _
    have hV : TreeOK (updN (wNode c.p base ({ v with trail := s :: v.trail } : W)) (X (D + 1))
        ⟨S.leaf, last.ks⟩) c.i ({ v with trail := s :: v.trail } : W).top.rootKey := by
      rw [hroot']
      exact treeOK_up_tr (wNode c.p base w3) _ c.i w3.top.rootKey X Nn K (D + 1) depth hsD hT3
        (hreach3 (D + 1) (by omega)) (fun i _ hi => hN3 i hi) (fun i h1 hi => hlinkK i (by omega) hi)
        (fun i i' _ hi _ hi' he => hdist i i' hi hi' he) hagreeV _ hsnV id
        (fun c' z h => ⟨c', ((hliveL c' z).mp h).1, ((hliveL c' z).mp h).2, rfl⟩)
    have hvx : ∀ c' z, (c', z) ∈ (⟨S.leaf, last.ks⟩ : KNode).liveAt c.i →
        z < ({ v with trail := s :: v.trail } : W).next := by
      intro c' z h
      rw [hnx', hr03.2.2.2.2]
      exact hI.links (X (D + 1)) (Nn (D + 1)) c' z (tReach_reachS _ _ _ _ (hreach (D + 1) (by omega)))
        (hXN (D + 1) (by omega)) ((hliveL c' z).mp h).1
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
      have hzn := ((hliveL c' z).mp hz').1
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
    have hlevel := writerWP_handleFull_lastVF2 (c.p.fuel + 1) (by omega) c base w3.path 0 D X K Nn'
      (Nat.zero_le _) (fun i _ hi => hpX i (by omega)) (fun i h1 hi => hpK i h1 (by omega)) hlinkK'
      hrange hlen hwf' htimes' (Or.inr rfl) hdist' hspace last compact hlwf hlt
      (by rw [hNn'S]; exact hlastV) (by rw [hNn'S]; exact hlen2)
      (by
        intro _ hql c' z hz hpos'
        rw [hNn'S] at hz
        rw [hNn'i D (Nat.le_refl _)] at hql ⊢
        exact hrangeLn hql c' z hz hpos')
      (fun _ => Or.inr (fun _ i' h1 h2 => hCO i' h1 (by omega)))
      ({ v with trail := s :: v.trail } : W) hpath' hS2' hT2' hS4' hS5 hS6
      (fun _ _ => by rw [hroot', hr03.2.1, hX0]) hW (by rw [hNn'S]; exact hV) (by rw [hNn'S]; exact hvx)
    -- the halves of a space split
    have hhalves : c.p.splitAbove < last.size → ∃ r : Nat, 0 < r ∧
        (halves (Nn' (D + 1)).leaf c.i last []).2.2 = r ∧
        (∀ c' z, (c', z) ∈ (halves (Nn' (D + 1)).leaf c.i last []).1.liveAt c.i → c' < r ∧
          (c', z) ∈ (⟨(Nn' (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i) ∧
        (∀ c' z, (c', z) ∈ (halves (Nn' (D + 1)).leaf c.i last []).2.1.liveAt c.i → ∃ c0, r ≤ c0 ∧
          c' = splitLocalCv (Nn' (D + 1)).leaf r c0 ∧
          (c0, z) ∈ (⟨(Nn' (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i) ∧
        ((Nn' D).leaf = false →
          K (D + 1) ≤ r ∧ ∀ c'' z', (c'', z') ∈ (Nn' D).live → K (D + 1) < c'' → r < c'') := by
      intro hsp
      rw [hNn'S, hNn'i D (Nat.le_refl _)]
      obtain ⟨r, hdiv, hsc, hrm, hfh, hsh⟩ := halves_facts_nil c.i ⟨S.leaf, last.ks⟩ (hlen2 hsp) hlt
      rw [hlastV] at hdiv hfh hsh
      refine ⟨r.1, hsc, hdiv, hfh, hsh, fun hql => ?_⟩
      exact hrangeLn hql r.1 r.2 hrm hsc
    have hhalvesR : c.p.splitAbove < last.size → ∀ r, (halves (Nn' (D + 1)).leaf c.i last []).2.2 = r →
        (∃ zs, (r, zs) ∈ (⟨(Nn' (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i) ∧
        ∃ c0 z0, (c0, z0) ∈ (⟨(Nn' (D + 1)).leaf, last.ks⟩ : KNode).liveAt c.i ∧ c0 < r := by
      intro hsp r hr
      rw [hNn'S] at hr ⊢
      have h := halves_facts_nilR c.i ⟨S.leaf, last.ks⟩ (hlen2 hsp) hlt r
      rw [hlastV] at h
      exact h hr
    have hVR : RangeOrder (updN (wNode c.p base ({ v with trail := s :: v.trail } : W)) (X (D + 1))
        ⟨S.leaf, last.ks⟩) c.i ({ v with trail := s :: v.trail } : W).top.rootKey := by
      rw [hroot']
      exact rangeOrder_up_bitmap (wNode c.p base w3) _ c.i w3.top.rootKey X Nn K (D + 1) depth hsD hR3 hT3
        (hreach3 (D + 1) (by omega)) (fun i _ hi => hN3 i hi) (fun i h1 hi => hlinkK i (by omega) hi)
        (fun i i' _ hi _ hi' he => hdist i i' hi hi' he) hagreeV _ hsnV (by show S.leaf = _; exact hSleaf)
        (fun c' z h => (hliveL c' z).mp h)
    have hSwv : wNode c.p base ({ v with trail := s :: v.trail } : W) (X (D + 1)) = some S := by
      rw [hwv']; simp only [wNode, htk2, Bool.false_eq_true, ↓reduceIte, hSl]
    have hRV := tReach_updN_relabel _ c.i ({ v with trail := s :: v.trail } : W).top.rootKey _ S
      ⟨S.leaf, last.ks⟩ hSwv (fun c' z h => by rw [hleq] at h; exact ⟨c', ((hiff c' z).mp h).1⟩)
    have hrangeG := writerWP_delSplit_chainGRangeV c base w3.path 0 D X K Nn' last compact (Nat.zero_le _)
      (fun i _ hi => hpX i (by omega)) (fun i h1 hi => hpK i h1 (by omega)) hlinkK' hrange hlen hwf' htimes'
      (Or.inr rfl) hdist'
      hhalves hhalvesR ({ v with trail := s :: v.trail } : W) hpath' hS2' hT2' hS4' hS5 hS6
      (fun _ => by rw [hroot', hr03.2.1, hX0]) (by rw [hNn'S]; exact hV) (by rw [hNn'S]; exact hRV)
      (by rw [hNn'S]; exact hVR) (by rw [hNn'S]; exact hvx)
    refine writerWP_mono (writerWP_and hlevel hrangeG) ?_
    rintro _ w' ⟨⟨_, ⟨_, ht', _, _, hvals'⟩, _, hreach', _, hRead, _⟩, ⟨hTw, _, _, _, hRw⟩⟩ hFw hbw hbkw hikw
    rw [hNn'S] at hreach' hRead
    -- what is reached after is reached in the walk's tree, or new
    have hsub := tReach_up_sub_tr (wNode c.p base w3) _ c.i w3.top.rootKey X Nn K (D + 1) depth hsD hT3
      (hreach3 (D + 1) (by omega)) (fun i _ hi => hN3 i hi) (fun i h1 hi => hlinkK i (by omega) hi)
      (fun i i' _ hi _ hi' he => hdist i i' hi hi' he) hagreeV _ hsnV
      (fun c' z h => ⟨c', ((hliveL c' z).mp h).1, ((hliveL c' z).mp h).2⟩)
    have hun : ∀ y, TReach (wNode c.p base w') c.i w'.top.rootKey y → w'.taken.contains y = false := by
      intro y hy
      rw [ht']
      rcases hreach' y hy with h | h
      · rw [hroot'] at h
        obtain ⟨h3, hnc⟩ := hsub y h
        show v.taken.contains y = false
        rw [hvt, h2t y (fun k h1 h2 => hnc k h1 h2), hr03.2.2.1]
        rw [hr03.1, hr03.2.1] at h3
        exact hI.untaken y (tReach_reachS _ _ _ _ h3)
      · exact (hS5 y h.1).2.1
    obtain ⟨hPw, hGw⟩ := putInv_after_step c base w' B top0 hB hbw hTw
      (fun y hy => hun y (reachS_tReach _ _ _ _ hy)) hRw
    refine ⟨⟨hPw, hGw, hRw, hICEk w' hbkw hikw hun, by simpa using hFw, fun key' hk' => ?_, B, top0, hB, hbw⟩,
      hbkw, hikw⟩
    -- the reading, through the tree with the stop node's last version
    have hVal3 : wValue base ({ v with trail := s :: v.trail } : W) = wValue base w3 :=
      wValue_eq_of_taken base w3 _ (by show v.vals = w3.vals; rw [hvv, h2v])
        (fun y => ∃ k, D + 1 < k ∧ k ≤ depth ∧ y = X k)
        (fun y hy => by
          show v.taken.contains y = w3.taken.contains y
          rw [hvt]; exact h2t y (fun k h1 h2 he => hy ⟨k, h1, h2, he⟩))
        (fun y ⟨k, _, h2, he⟩ => by rw [he]; exact ⟨htk3 k h2, hnoval3 k h2⟩)
    have hValw' : wValue base w' = wValue base w3 := by
      rw [← hVal3]; exact wValue_congr' base w' _ ht' hvals'
    have hVal : ∀ z, (({ v with trail := s :: v.trail } : W).next ≤ z ∨ ∃ i, 0 ≤ i ∧ i ≤ D + 1 ∧ z = X i) →
        wValue base w' z = none := by
      intro z hz
      rw [hValw']
      rcases hz with hz | ⟨i, _, hi, rfl⟩
      · rw [hnx'] at hz
        rw [ReadsAs.value _ _ _ _ hr03]
        have htz : w.taken.contains z = false := by
          cases h' : w.taken.contains z with
          | false => rfl
          | true => have := hI.ids.2.2.1 z h'; rw [hr03.2.2.2.2] at hz; omega
        have hvz : w.vals.lookup z = none := by
          cases h' : w.vals.lookup z with
          | none => rfl
          | some _ =>
            have hm := lookup_some_mem h'
            have := hI.ids.2.2.2.1 _ hm
            rw [hr03.2.2.2.2] at hz
            simp only at this; omega
        simp only [wValue, htz, Bool.false_eq_true, ↓reduceIte, hvz,
          (hI.fresh z (by rw [← hr03.2.2.2.2]; exact hz)).2]
      · exact hnoval3 i (by omega)
    have hR := hRead (wValue base w') hVal (Or.inl (by simpa using hFw)) key'
    -- the virtual state with the stop node's last version
    have htk' : ({ v with trail := s :: v.trail } : W).taken.contains (X (D + 1)) = false := by
      show v.taken.contains _ = false; rw [hvt]; exact htk2
    have hwV : wNode c.p base ({ ({ v with trail := s :: v.trail } : W) with
        nodes := upsert v.nodes (X (D + 1)) ⟨S.leaf, last.ks⟩ } : W) =
        updN (wNode c.p base ({ v with trail := s :: v.trail } : W)) (X (D + 1)) ⟨S.leaf, last.ks⟩ :=
      wNode_upsert_updN c.p base _ _ (X (D + 1)) _ rfl rfl htk'
    generalize hwVd : ({ ({ v with trail := s :: v.trail } : W) with
        nodes := upsert v.nodes (X (D + 1)) ⟨S.leaf, last.ks⟩ } : W) = wV at hwV
    have hVtop : wV.top.rootKey = w3.top.rootKey := by rw [← hwVd]; exact hroot'
    have hVval : wValue base wV = wValue base w3 := by
      rw [← hwVd, ← hVal3]; exact wValue_congr' base _ _ rfl rfl
    have hRSV : ∀ u, ReachS (wNode c.p base wV) c.i wV.top.rootKey u →
        ReachS (wNode c.p base w3) c.i w3.top.rootKey u := by
      intro u hu
      rw [hwV, hVtop] at hu
      exact tReach_reachS _ _ _ _ (hsub u (reachS_tReach _ _ _ _ hu)).1
    have hF3 : SegFits (wNode c.p base w3) c.i (c.p.fuel - 1) w3.top.rootKey := by
      rw [hr03.1, hr03.2.1]; exact hF
    have hFV : SegFits (wNode c.p base wV) c.i (c.p.fuel - 1) wV.top.rootKey := by
      refine segFits_transfer _ _ c.i _ _ _ hF3 hRSV ?_
      intro u un' hu hun' hl
      by_cases hux : u = X (D + 1)
      · subst hux
        rw [hwV, hsnV] at hun'
        cases hun'
        exact ⟨Nn (D + 1), hN3 (D + 1) (by omega), by rw [← hSleaf]; exact hl,
          fun c' y hy => ⟨c', ((hliveL c' y).mp hy).1⟩⟩
      · have hu' := (hsub u (by rw [← hwV, ← hVtop]; exact reachS_tReach _ _ _ _ hu)).2
        rw [hwV, hagreeV u hux hu'] at hun'
        exact ⟨un', hun', hl, fun c' y hy => ⟨c', hy⟩⟩
    have hwfV : ∀ x xn, ReachS (wNode c.p base wV) c.i wV.top.rootKey x → wNode c.p base wV x = some xn →
        klongsWf xn.ks = true := by
      intro x xn _ h
      rw [hwV] at h
      by_cases hx : x = X (D + 1)
      · subst hx; rw [updN_self] at h; cases h; exact hlwf
      · rw [updN_ne _ _ _ _ hx] at h; exact hW x xn h
    have hwfS3 : ∀ x xn, ReachS (wNode c.p base w3) c.i w3.top.rootKey x → wNode c.p base w3 x = some xn →
        klongsWf xn.ks = true := fun x xn _ h => by rw [hr03.1] at h; exact hI.wf x xn h
    have hagreeR : ∀ u, TReach (wNode c.p base w3) c.i w3.top.rootKey u → u ≠ X (D + 1) →
        (∀ i, D + 1 < i → i ≤ depth → u ≠ X i) → wNode c.p base wV u = wNode c.p base w3 u :=
      fun u _ hus hnc => by rw [hwV]; exact hagreeV u hus hnc
    have hsnwV : wNode c.p base wV (X (D + 1)) = some ⟨S.leaf, last.ks⟩ := by rw [hwV]; exact hsnV
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
    have honly : ∀ c' z, (c', z) ∈ (Nn depth).liveAt c.i → c' = cv := by
      intro c' z hm
      have hm' : (c', z) ∈ (Nn depth).live := by
        rw [← KNode.liveAt_of_times _ c.i (hI.times _ _ (hXN depth (Nat.le_refl _)))]; exact hm
      exact allKeysIn_live_cv (Nn depth) cv hall c' z hm'
    have hreadV : wGet c.p c.i base wV key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w3 key' := by
      unfold wGet
      rw [hVval, hVtop]
      have hrk3 : segRootR (wNode c.p base w3) c.i c.p.fuel pre w3.top.rootKey = some rk := by
        rw [hr03.1, hr03.2.1]; exact hrk
      have hvis3 : (X depth, cv) ∈ eqVisits (wNode c.p base w3) c.i cv c.p.fuel rk := by
        rw [hr03.1]; exact hvis
      have huniq3 := hI.keyUniq pre cv rk hkey hrk
      rw [← hr03.1, ← hr03.2.1] at huniq3
      cases hsl : (Nn (D + 1)).leaf with
      | false =>
        exact getFromR_up_inner (wNode c.p base w3) (wNode c.p base wV) (wValue base w3) c.i c.p.fuel hfuel
          w3.top.rootKey X Nn K (D + 1) depth hsD pre cv rk hT3 hR3 hwf3 (hreach3 (D + 1) (by omega))
          (fun i _ hi => hN3 i hi) (fun i h1 hi => hlinkK i (by omega) hi) hone hleaf honly
          (fun i _ hi => hnoval3 i hi)
          (fun i _ hi he => by have := hdist i depth (by omega) (Nat.le_refl _) he; omega)
          hrk3 (keyWf_last_notin pre cv hkey) hvis3 huniq3 hagreeR _ hsl hsnwV
          (by show S.leaf = false; rw [hSleaf]; exact hsl) hliveL key' hk'
      | true =>
        exact getFromR_up_leaf (wNode c.p base w3) (wNode c.p base wV) (wValue base w3) c.i c.p.fuel hfuel
          w3.top.rootKey X Nn K (D + 1) depth hsD pre cv rk hT3 hR3 hwf3 (hreach3 (D + 1) (by omega))
          (fun i _ hi => hN3 i hi) (fun i h1 hi => hlinkK i (by omega) hi) hone hleaf honly
          (fun i _ hi => hnoval3 i hi)
          (fun i _ hi he => by have := hdist i depth (by omega) (Nat.le_refl _) he; omega)
          hrk3 (keyWf_last_notin pre cv hkey) hvis3 huniq3 hagreeR _ hsl hsnwV
          (by show S.leaf = true; rw [hSleaf]; exact hsl) hlwf hliveL key' hk'
    have h1 : wGetAt c.p c.i base w' (c.p.fuel + 1) key' = wGetAt c.p c.i base wV (c.p.fuel + 1) key' := by
      unfold wGetAt
      rw [hR, hValw', hVval, hwV, hVtop, hroot']
    rw [h1, wGetAt_eq_wGet c base wV _ (by omega) hwfV hFV, hreadV,
      ← wGetAt_eq_wGet c base w3 (c.p.fuel + 1) (by omega) hwfS3 hF3]
    have hw3w : wGetAt c.p c.i base w3 (c.p.fuel + 1) key' = wGetAt c.p c.i base w (c.p.fuel + 1) key' := by
      unfold wGetAt
      rw [hr03.1, hr03.2.1, ReadsAs.value _ _ _ _ hr03]
    rw [hw3w]
  have hpx : v.path[D + 1]? = some ((v.path[D + 1]?).map (·.1) |>.getD none, X (D + 1)) := by
    have h := hpX (D + 1) (by omega)
    rw [← hvp] at h
    cases hp : v.path[D + 1]? with
    | none => rw [hp] at h; cases h
    | some e =>
      rw [hp] at h
      simp only [Option.map_some, Option.some.injEq] at h
      simp [← h]
  refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and hfullM hFits)
    (putBook_appendDeleteKlong (X (D + 1)) (D + 1) (K (D + 1 + 1)) c base B top0 hB v hJ.1.1))
    (kd_appendDeleteKlong KO BK (X (D + 1)) (D + 1) (K (D + 1 + 1)) c v hvB hk hJ.1.2.1 hJ.1.2.2 _ hpx)) ?_
  rintro _ w' ⟨⟨⟨hM, hFw⟩, hbw⟩, hbkw, hikw, _, _⟩
  exact hM hFw hbw hbkw hikw


set_option maxHeartbeats 6400000 in
/-- The take-back's facts through the stop node's bitmap into a full node below
the space root (`UpCascJ2OKF3` at stop D + 1): as `writerWP_upCasc_root_j2`, the
cascade above by `writerWP_handleFull_last_j2U`. -/
theorem writerWP_upCasc_below_j2T (c : Ctx) (base : View BVal)
    (hsa2 : 2 ≤ c.p.splitAbove) (B : NodeId) (hpos : 0 < c.i)
    (w w3 : W) (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth D : Nat) (w2 v : W) (S : KNode)
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
    (hv : v = w2 ∨ ∃ s, v = { w2 with trail := s :: w2.trail })
    (hJ : v.path = w3.path)
    (hfull : ¬ DelRoom c (K (D + 1 + 1)) S)
    (hT2 : TreeOK (wNode c.p base w2) c.i w2.top.rootKey)
    (hlinks2 : ∀ u c' z, TLink (wNode c.p base w2) c.i u c' z → z < w2.next)
    (hwf2 : ∀ z zn, wNode c.p base w2 z = some zn → klongsWf zn.ks = true) :
    WriterWP (appendDeleteKlong (X (D + 1)) (D + 1) (K (D + 1 + 1))) c v
      (fun _ w' => TakeJ2 c base B w' ∧ B ≤ w'.next) := by
  have hT := hI.tree
  have hdepth : 0 < depth := by omega
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
  have hI3 := putInv_of_readsAs c base w w3 hI hr03
  have htk3 : ∀ i, i ≤ depth → w3.taken.contains (X i) = false := fun i hi => by
    rw [hr03.2.2.1]; exact hI.untaken _ (tReach_reachS _ _ _ _ (hreach i hi))
  have hT3 : TreeOK (wNode c.p base w3) c.i w3.top.rootKey := by rw [hr03.1, hr03.2.1]; exact hT
  have hR3 : RangeOrder (wNode c.p base w3) c.i w3.top.rootKey := by rw [hr03.1, hr03.2.1]; exact hRO
  have hreach3 : ∀ i, i ≤ depth → TReach (wNode c.p base w3) c.i w3.top.rootKey (X i) := fun i hi => by
    rw [hr03.1, hr03.2.1]; exact hreach i hi
  have hwf3 : ∀ x xn, TReach (wNode c.p base w3) c.i w3.top.rootKey x → wNode c.p base w3 x = some xn →
      klongsWf xn.ks = true := fun x xn _ h => by rw [hr03.1] at h; exact hI.wf x xn h
  -- the chain's facts at w3 from its order
  have hP3 : PathOK c w3 depth X K Nn :=
    ⟨hpX, hpK, fun i hi => ⟨hlkX i hi, htk3 i hi⟩, hlinkK, by rw [hr03.2.1, hX0]⟩
  have hO := ordG_of_rangeOrder c _ _ hR3 (fun x n h => hI3.times x n h)
  have hwX : ∀ j, j ≤ depth → wNode c.p base w3 (X j) = some (Nn j) := hN3
  -- the loop's end
  obtain ⟨h2t, h2top, h2v, _, _, h2nx, h2n, hSl, hS, hSR, hSF', hfate2, hfateJ2⟩ := hLE
  have hvn : v.nodes = w2.nodes := by rcases hv with rfl | ⟨s, rfl⟩ <;> rfl
  have hvt : v.taken = w2.taken := by rcases hv with rfl | ⟨s, rfl⟩ <;> rfl
  have hvtop : v.top = w2.top := by rcases hv with rfl | ⟨s, rfl⟩ <;> rfl
  have hvv : v.vals = w2.vals := by rcases hv with rfl | ⟨s, rfl⟩ <;> rfl
  have hvnx : v.next = w2.next := by rcases hv with rfl | ⟨s, rfl⟩ <;> rfl
  have hvp : v.path = w3.path := hJ
  have hwv : wNode c.p base v = wNode c.p base w2 := by
    funext z; simp only [wNode, hvn, hvt]
  -- the stop node now
  have hXs : ∀ k, D + 1 < k → k ≤ depth → X (D + 1) ≠ X k :=
    fun k h1 h2 he => by have := hdist (D + 1) k (by omega) h2 he; omega
  have hst_t : ∀ s', Klong.time s' ∈ (Nn (D + 1)).ks → s' ≤ c.i := hI.times _ _ (hXN (D + 1) (by omega))
  have hsx : (K (D + 1 + 1), X (D + 1 + 1)) ∈ (Nn (D + 1)).liveAt c.i := by
    have := hlinkK (D + 1 + 1) (by omega) (by omega); simpa using this
  have hneS : bitsUnion (Nn (D + 1)).lastBitmap ((Nn (D + 1)).bitsOf (K (D + 1 + 1))) ≠
      (Nn (D + 1)).lastBitmap := by
    apply KNode.delete_bitmap_changes_of_live
    have hsx' := hsx
    rw [KNode.liveAt_of_times _ c.i hst_t] at hsx'
    exact List.mem_map.mpr ⟨_, hsx', rfl⟩
  have hswf : klongsWf (Nn (D + 1)).ks = true := hI.wf _ _ (hXN (D + 1) (by omega))
  have hu : ∀ c', (c', X (D + 1 + 1)) ∈ (Nn (D + 1)).liveAt c.i → c' = K (D + 1 + 1) := by
    intro c' h
    exact (hT.oneLink _ _ _ _ _ (hreach (D + 1) (by omega)) (hreach (D + 1) (by omega))
      ⟨_, hXN (D + 1) (by omega), h⟩ ⟨_, hXN (D + 1) (by omega), hsx⟩).2
  have hSf : S.shapeOf = (Nn (D + 1)).shapeOf ∧ S.leaf = (Nn (D + 1)).leaf ∧ klongsWf S.ks = true ∧
      (∀ s, Klong.time s ∈ S.ks → s ≤ c.i) ∧
      ∀ c' z, ((c', z) ∈ S.liveAt c.i ∧ c' ≠ K (D + 1 + 1)) ↔
        ((c', z) ∈ (Nn (D + 1)).liveAt c.i ∧ c' ≠ K (D + 1 + 1)) := by
    rcases hS with rfl | ⟨ti, dst, rfl⟩
    · exact ⟨rfl, rfl, hswf, hst_t, fun _ _ => Iff.rfl⟩
    · exact ⟨KNode.retarget_shapeOf _ _ _ _, rfl, by rw [klongsWf_retargetKlongs]; exact hswf,
        KNode.retarget_times _ _ _ _ _ hst_t, KNode.retarget_liveAt_ne _ _ _ _ _ _ hu⟩
  obtain ⟨hSsh, hSleaf, hSwf, hSt, hSlive⟩ := hSf
  have hneS' : bitsUnion S.lastBitmap (S.bitsOf (K (D + 1 + 1))) ≠ S.lastBitmap := by
    rw [KNode.lastBitmap_of_shapeOf hSsh, KNode.bitsOf_of_shapeOf hSsh]; exact hneS
  have hlkv : v.nodes.lookup (X (D + 1)) = some S := by rw [hvn]; exact hSl
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
  refine writerWP_appendDeleteKlong_full_of (X (D + 1)) (D + 1) (K (D + 1 + 1)) S c v hlkv hneS' hfull _ ?_
  intro compact s
  generalize hlast : S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf (K (D + 1 + 1)))) = last
  obtain ⟨hleq, hlwf, hlt, hlastV, hlen2, hpairs, hiff, _⟩ :=
    delLast_split_facts c S (K (D + 1 + 1)) hsa2 hSt last hlast
  have hliveL : ∀ c' z, (c', z) ∈ (⟨S.leaf, last.ks⟩ : KNode).liveAt c.i ↔
      (c', z) ∈ (Nn (D + 1)).liveAt c.i ∧ c' ≠ K (D + 1 + 1) := by
    intro c' z; rw [hleq, hiff c' z]; exact hSlive c' z
  have hlk' : ({ v with trail := s :: v.trail } : W).nodes.lookup (X (D + 1)) = some S := hlkv
  have hroot' : ({ v with trail := s :: v.trail } : W).top.rootKey = w3.top.rootKey := by
    show v.top.rootKey = _; rw [hvtop, h2top]
  have hnx' : ({ v with trail := s :: v.trail } : W).next = w3.next := by
    show v.next = _; rw [hvnx, h2nx]
  have hwv' : wNode c.p base ({ v with trail := s :: v.trail } : W) = wNode c.p base w2 := hwv
  have hXlt : ∀ i, i ≤ depth → X i < w3.next := fun i hi => hI3.ids.1 (X i) (by rw [hlkX i hi]; rfl)
  have hS5 : ∀ z, ({ v with trail := s :: v.trail } : W).next ≤ z →
      ({ v with trail := s :: v.trail } : W).nodes.lookup z = none ∧
      ({ v with trail := s :: v.trail } : W).taken.contains z = false ∧ knodeOf c.p base z = none := by
    intro z hz
    rw [hnx'] at hz
    have hzX : ∀ i, i ≤ depth → z ≠ X i := fun i hi he => by have := hXlt i hi; omega
    refine ⟨?_, ?_, (hI.fresh z (by rw [← hr03.2.2.2.2]; exact hz)).1⟩
    · show v.nodes.lookup z = none
      rw [hvn, h2n z (hzX (D + 1) (by omega)) (fun i _ hi => hzX i hi)]
      cases h' : w3.nodes.lookup z with
      | none => rfl
      | some _ => have := hI3.ids.1 z (by rw [h']; rfl); omega
    · show v.taken.contains z = false
      rw [hvt, h2t z (fun i _ hi => hzX i hi)]
      cases h' : w3.taken.contains z with
      | false => rfl
      | true => have := hI3.ids.2.2.1 z h'; omega
  have hS6 : ∀ u c' z, TLink (wNode c.p base ({ v with trail := s :: v.trail } : W)) c.i u c' z →
      z < ({ v with trail := s :: v.trail } : W).next := by
    rw [hwv']; intro u c' z hl
    show z < v.next
    rw [hvnx]; exact hlinks2 u c' z hl
  have hW : ∀ z zn, wNode c.p base ({ v with trail := s :: v.trail } : W) z = some zn →
      klongsWf zn.ks = true := by
    rw [hwv']; exact hwf2
  have hS2' : ∀ i, 0 ≤ i → i ≤ D + 1 →
      ({ v with trail := s :: v.trail } : W).nodes.lookup (X i) = some (Nn' i) ∧
      ({ v with trail := s :: v.trail } : W).taken.contains (X i) = false := by
    intro i _ hi
    rcases Nat.lt_or_ge i (D + 1) with h | h
    · rw [hNn'i i (by omega)]
      exact ⟨by show v.nodes.lookup _ = _; rw [hvn]; exact hlk2 i (by omega),
        by show v.taken.contains _ = false; rw [hvt]; exact htk2' i (by omega)⟩
    · have hi' : i = D + 1 := by omega
      subst hi'
      rw [hNn'S]
      exact ⟨hlkv, by show v.taken.contains _ = false; rw [hvt]; exact htk2⟩
  have hT2' : TreeOK (wNode c.p base ({ v with trail := s :: v.trail } : W)) c.i
      ({ v with trail := s :: v.trail } : W).top.rootKey := by
    rw [hwv']; show TreeOK _ c.i v.top.rootKey; rw [hvtop]; exact hT2
  have hS4' : ∀ i, 0 ≤ i → i ≤ D + 1 → TReach (wNode c.p base ({ v with trail := s :: v.trail } : W)) c.i
      ({ v with trail := s :: v.trail } : W).top.rootKey (X i) := by
    intro i _ hi
    rw [hwv', hroot']
    induction i with
    | zero => rw [hr03.2.1, hX0]; exact TReach.root
    | succ i ih =>
      have hi' : i ≤ D := by omega
      refine TReach.link (ih (Nat.zero_le _) (by omega)) ⟨Nn i, ?_, by
        have := hlinkK (i + 1) (by omega) (by omega); simpa using this⟩
      simp only [wNode, htk2' i hi', Bool.false_eq_true, ↓reduceIte, hlk2 i hi']
  have hpath' : ({ v with trail := s :: v.trail } : W).path = w3.path := hvp
  -- the tree with the stop node's last version
  have hagreeV : ∀ u, u ≠ X (D + 1) → (∀ i, D + 1 < i → i ≤ depth → u ≠ X i) →
      updN (wNode c.p base ({ v with trail := s :: v.trail } : W)) (X (D + 1)) ⟨S.leaf, last.ks⟩ u =
        wNode c.p base w3 u := fun u hus hnc => by
    rw [updN_ne _ _ _ _ hus, hwv']; exact hagree2 u hus hnc
  have hsnV : updN (wNode c.p base ({ v with trail := s :: v.trail } : W)) (X (D + 1)) ⟨S.leaf, last.ks⟩
      (X (D + 1)) = some ⟨S.leaf, last.ks⟩ := updN_self _ _ _
  have hV : TreeOK (updN (wNode c.p base ({ v with trail := s :: v.trail } : W)) (X (D + 1))
      ⟨S.leaf, last.ks⟩) c.i ({ v with trail := s :: v.trail } : W).top.rootKey := by
    rw [hroot']
    exact treeOK_up_tr (wNode c.p base w3) _ c.i w3.top.rootKey X Nn K (D + 1) depth hsD hT3
      (hreach3 (D + 1) (by omega)) (fun i _ hi => hN3 i hi) (fun i h1 hi => hlinkK i (by omega) hi)
      (fun i i' _ hi _ hi' he => hdist i i' hi hi' he) hagreeV _ hsnV id
      (fun c' z h => ⟨c', ((hliveL c' z).mp h).1, ((hliveL c' z).mp h).2, rfl⟩)
  have hvx : ∀ c' z, (c', z) ∈ (⟨S.leaf, last.ks⟩ : KNode).liveAt c.i →
      z < ({ v with trail := s :: v.trail } : W).next := by
    intro c' z h
    rw [hnx', hr03.2.2.2.2]
    exact hI.links (X (D + 1)) (Nn (D + 1)) c' z (tReach_reachS _ _ _ _ (hreach (D + 1) (by omega)))
      (hXN (D + 1) (by omega)) ((hliveL c' z).mp h).1
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
    have hzn := ((hliveL c' z).mp hz').1
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
  have hTtV := ttReachedN_up (wNode c.p base w3)
    (updN (wNode c.p base ({ v with trail := s :: v.trail } : W)) (X (D + 1)) ⟨S.leaf, last.ks⟩) c.i
    w3.top.rootKey X Nn (D + 1) depth hsD (fun i _ hi => hN3 i hi) hone
    (fun c' z h => by rw [hr03.1]; exact hkidsw c' z h) _ hsnV
    (fun c' z hm hz => ⟨c', (hliveL c' z).mpr ⟨hm, fun hck => hz (by
      rw [hck] at hm; exact KNode.liveAt_fun _ _ _ _ _ hm hsx)⟩⟩)
    hagreeV hXs (hreach3 (D + 1) (by omega))
    (by
      intro k h1 h2 un hun
      rw [updN_ne _ _ _ _ (Ne.symm (hXs k h1 h2)), hwv'] at hun
      rcases hfate2 k h1 h2 with hf | ⟨S0, hS0, hnt0⟩
      · unfold wNode at hun; rw [hf] at hun; cases hun
      · have hkt : w2.taken.contains (X k) = false := by
          cases hc : w2.taken.contains (X k) with
          | false => rfl
          | true => unfold wNode at hun; rw [hc] at hun; cases hun
        simp only [wNode, hkt, Bool.false_eq_true, ↓reduceIte, hS0, Option.some.injEq] at hun
        rw [← hun]; exact hnt0)
    hJ3.1
  have hTU : ∀ q qn, wNode c.p base ({ v with trail := s :: v.trail } : W) q = some qn →
      Klong.time c.i ∈ qn.ks →
      TReach (updN (wNode c.p base ({ v with trail := s :: v.trail } : W)) (X (D + 1))
        (⟨(Nn' (D + 1)).leaf, last.ks⟩ : KNode)) c.i ({ v with trail := s :: v.trail } : W).top.rootKey q := by
    intro q qn hq hm
    rw [hNn'S]
    by_cases hqs : q = X (D + 1)
    · rw [hqs]
      exact tReach_updN_self _ c.i _ _ _ hT2' (hS4' (D + 1) (Nat.zero_le _) (Nat.le_refl _))
    · rw [hroot']
      exact hTtV q qn (by rw [updN_ne _ _ _ _ hqs]; exact hq) hm
  have hvals2 : ({ v with trail := s :: v.trail } : W).vals = w3.vals := by
    show v.vals = _; rw [hvv, h2v]
  have hrest' : DeadLiveN (wNode c.p base ({ v with trail := s :: v.trail } : W)) c.i B
      (({ v with trail := s :: v.trail } : W).vals.map (·.1)) ∧
      OldBelowN (wNode c.p base ({ v with trail := s :: v.trail } : W)) c.i B ∧
      OldStartN (wNode c.p base ({ v with trail := s :: v.trail } : W)) c.i B ∧
      MadeStartN (wNode c.p base ({ v with trail := s :: v.trail } : W)) c.i B ∧
      ValsNoNodeN (wNode c.p base ({ v with trail := s :: v.trail } : W))
        (({ v with trail := s :: v.trail } : W).vals.map (·.1)) := by
    rw [hwv', hvals2]; exact hrest2
  -- the order of the stop node's last version under its parent
  have hLO : LastOrd c K Nn' D last := by
    intro _ hql c' z hz
    rw [hNn'i D (Nat.le_refl _)] at hql
    rw [hNn'S] at hz ⊢
    have hz' : (c', z) ∈ (⟨S.leaf, last.ks⟩ : KNode).liveAt c.i := by
      rw [KNode.liveAt_of_times (⟨S.leaf, last.ks⟩ : KNode) c.i hlt]; exact hz
    have hzn := ((hliveL c' z).mp hz').1
    obtain ⟨hP1, _⟩ := mrg_child_range (wNode c.p base w3) c.i w3.top.rootKey hR3 (X D) (Nn D)
      (tReach_reachS _ _ _ _ (hreach3 D (by omega))) (hwX D (by omega)) hql (K (D + 1)) (X (D + 1))
      (Nn (D + 1)) hkl (hwX (D + 1) (by omega))
    have hSl' : S.leaf = (Nn (D + 1)).leaf := hSleaf
    split
    · rename_i hl
      rcases Nat.eq_zero_or_pos (K (D + 1)) with hk0 | hk0
      · omega
      · exact (hP1 c' z hzn).1 (by rw [← hSl']; exact hl) hk0
    · rename_i hl
      have hl' : (Nn (D + 1)).leaf = false := by rw [← hSl']; simpa using hl
      rcases (hP1 c' z hzn).2 hl' with h | h
      · exact Or.inl h
      · rcases Nat.eq_zero_or_pos (K (D + 1)) with hk0 | hk0
        · rcases Nat.eq_zero_or_pos c' with hc0 | hc0
          · exact Or.inl hc0
          · exact Or.inr (by omega)
        · exact Or.inr (h hk0)
  exact writerWP_handleFull_last_j2U (c.p.fuel + 1) (by unfold Params.fuel; omega) c base B hpos
    ({ v with trail := s :: v.trail } : W) hrest' (by rw [hnx', hr03.2.2.2.2]; exact hBn)
    (by
      intro y hy
      rw [hvals2] at hy
      rw [hnx']
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy
      exact hI3.ids.2.2.2.1 e he)
    D X K Nn' (fun i _ hi => by rw [hpath']; exact hpX i (by omega))
    (fun i h1 hi => by rw [hpath']; exact hpK i h1 (by omega)) hlinkK' hrange hlen hwf' htimes' hdist'
    hspace hCO last compact hlwf hlt (by rw [hNn'S]; exact hlastV) (by rw [hNn'S]; exact hlen2)
    (by
      intro _ hql c' z hz hpos'
      rw [hNn'S] at hz
      rw [hNn'i D (Nat.le_refl _)] at hql ⊢
      exact hrangeLn hql c' z hz hpos')
    (fun _ => Or.inr (fun _ i' h1 h2 => hCO i' h1 (by omega))) hpairs hLO hS2' hT2' hS4' hS5 hS6
    (by rw [hroot', hr03.2.1, hX0]) hW (by rw [hNn'S]; exact hV) (by rw [hNn'S]; exact hvx) hTU

/-- `UpCascOKF3` from `UpUnlinkTreeOK` and the fuel (`UpCascFitsOK`). -/
theorem upCascOKF3_of_parts3 (c : Ctx) (base : View BVal) (KO : KindOracle) (BK : NodeId)
    (hU : UpUnlinkTreeOK c base) (hFit : UpCascFitsOK c base KO BK) : UpCascOKF3 c base KO BK := by
  intro w w3 B MB top0 pre cv rk X Nn K depth stop w2 v S hsa2 hvB hk hICEk hX0 hB hI hRO hF hICE hr03 hkey
    hrk hvis hpX hpK hlkX hXN hlinkK hne hall hleaf hdepth hsD hbetween hLE hv hJ hkind hfull
  obtain ⟨hlinks2, hwf2⟩ := linksWf_of_book c base B top0 v w2 hB hJ.1.1 hv
  have hFits := hFit w w3 B MB top0 pre cv rk X Nn K depth stop w2 v S hsa2 hvB hk hICEk hX0 hB hI hRO hF
    hICE hr03 hkey hrk hvis hpX hpK hlkX hXN hlinkK hne hall hleaf hdepth hsD hbetween hLE hv hJ hkind hfull
  rcases Nat.eq_zero_or_pos stop with hs | hs
  · subst hs
    exact writerWP_upCasc_root_delF3 c base hB.coherent hsa2 KO BK hvB hk hICEk w w3 B MB top0 pre cv rk
      X Nn K depth w2 v S hB hI hRO hF hr03 hkey hrk hvis hpX hlkX hXN hlinkK hall hleaf hdepth hbetween
      hX0 hLE hv hJ hkind hfull hlinks2 hwf2 hFits
  · obtain ⟨D, rfl⟩ : ∃ D, stop = D + 1 := ⟨stop - 1, by omega⟩
    have hT2 := hU w w3 MB X Nn K depth (D + 1) w2 S hI hr03 hlkX hlinkK hsD hLE
    exact writerWP_upCasc_below_delF3T c base hsa2 KO BK hvB hk hICEk w w3 B MB top0 pre cv rk X Nn K depth D
      w2 v S hB hI hRO hF hr03 hkey hrk hvis hpX hpK hlkX hXN hlinkK hall hleaf hsD hbetween hX0 hLE hv hJ
      hfull hT2 hlinks2 hwf2 hFits

/-- `UpCascJ2OKF3` from `UpUnlinkTreeOK` and the fuel (`UpCascFitsOK`). -/
theorem upCascJ2OKF3_of_parts3 (c : Ctx) (base : View BVal) (KO : KindOracle) (BK B : NodeId)
    (hU : UpUnlinkTreeOK c base) (hFit : UpCascFitsOK c base KO BK) : UpCascJ2OKF3 c base KO BK B := by
  intro w w3 top0 pre cv rk X Nn K depth stop w2 v S hsa2 hvB hk hICEk hX0 hpos hB hI hRO hF hICE hr03
    hkey hrk hvis hpX hpK hlkX hXN hlinkK hne hall hleaf hdepth hsD hbetween hLE hv hJ hkind hfull hJw
    _hMF hkidsw
  have hRead := upCascOKF3_of_parts3 c base KO BK hU hFit
    w w3 B B top0 pre cv rk X Nn K depth stop w2 v S hsa2 hvB hk hICEk hX0 hB hI hRO hF hICE hr03 hkey
    hrk hvis hpX hpK hlkX hXN hlinkK hne hall hleaf hdepth hsD hbetween hLE hv hJ hkind hfull
  have hBn : B ≤ w.next := by
    have h1 : B ≤ v.next := hJ.1.1.fresh.1
    have h2 : v.next = w2.next := by
      rcases hv with rfl | ⟨s, rfl⟩ <;> rfl
    rw [h2, hLE.2.2.2.2.2.1, hr03.2.2.2.2] at h1
    exact h1
  have hT2 := hU w w3 B X Nn K depth stop w2 S hI hr03 hlkX hlinkK hsD hLE
  obtain ⟨hlinks2, hwf2⟩ := linksWf_of_book c base B top0 v w2 hB hJ.1.1 hv
  have hJ2 : WriterWP (appendDeleteKlong (X stop) stop (K (stop + 1))) c v
      (fun _ w' => TakeJ2 c base B w' ∧ B ≤ w'.next) := by
    rcases Nat.eq_zero_or_pos stop with hs | hs
    · subst hs
      exact writerWP_upCasc_root_j2 c base hB.coherent hsa2 B hpos w w3 X Nn K depth w2 v S hI hr03 hJw
        hBn hkidsw hlkX hXN hlinkK hdepth hbetween hX0 hLE hv hfull hT2 hlinks2 hwf2
    · obtain ⟨D, rfl⟩ : ∃ D, stop = D + 1 := ⟨stop - 1, by omega⟩
      exact writerWP_upCasc_below_j2T c base hsa2 B hpos w w3 X Nn K depth D w2 v S hI hRO hr03 hJw hBn
        hkidsw hpX hpK hlkX hXN hlinkK hsD hbetween hX0 hLE hv hJ.2 hfull hT2 hlinks2 hwf2
  exact writerWP_mono (writerWP_and hRead hJ2) (fun _ w' h => ⟨h.1, h.2.1, h.2.2⟩)

/-- `UpLebFullOKF3` from `UpUnlinkTreeOK` and the fuel (`UpLebFitsOK`). -/
theorem upLebFullOKF3_of_parts3 (c : Ctx) (base : View BVal) (KO : KindOracle) (BK : NodeId)
    (hU : UpUnlinkTreeOK c base) (hFit : UpLebFitsOK c base KO BK) : UpLebFullOKF3 c base KO BK := by
  intro w w3 B MB top0 pre cv rk X Nn K depth stop w2 S hsa2 hvB hk hICEk hX0 hB hI hRO hF hICE hr03 hkey
    hrk hvis hpX hpK hlkX hXN hlinkK hne hall hleaf hdepth hsD hbetween hLE hJ hsl hK0 hsm compact s t c1 y1 r hks
  have hFits := hFit w w3 B MB top0 pre cv rk X Nn K depth stop w2 S hsa2 hvB hk hICEk hX0 hB hI hRO hF hICE
    hr03 hkey hrk hvis hpX hpK hlkX hXN hlinkK hne hall hleaf hdepth hsD hbetween hLE hJ hsl hK0 hsm
    compact s t c1 y1 r hks
  obtain ⟨hlinks2, hwf2⟩ := linksWf_of_book c base B top0 w2 w2 hB hJ.1.1 (Or.inl rfl)
  rcases Nat.eq_zero_or_pos stop with hs | hs
  · subst hs
    exact writerWP_upLebFull_root_delF3 c base hB.coherent hsa2 KO BK hICEk w w3 B MB top0 pre cv rk
      X Nn K depth w2 S hB hI hRO hF hr03 hkey hrk hvis hlkX hXN hlinkK hall hleaf hdepth hbetween hX0 hLE
      hsl hK0 hlinks2 hwf2 compact s t c1 y1 r hks hFits
  · obtain ⟨D, rfl⟩ : ∃ D, stop = D + 1 := ⟨stop - 1, by omega⟩
    have hT2 := hU w w3 MB X Nn K depth (D + 1) w2 S hI hr03 hlkX hlinkK hsD hLE
    exact writerWP_upLebFull_below_delF3 c base hsa2 KO BK hICEk w w3 B MB top0 pre cv rk X Nn K depth D
      w2 S hB hI hRO hF hr03 hkey hrk hvis hpX hpK hlkX hXN hlinkK hall hleaf hsD hbetween hX0 hLE hsl hK0
      hT2 hlinks2 hwf2 compact s t c1 y1 r hks hFits

/-- `UpLebFullJ2OK` from `UpUnlinkTreeOK`. -/
theorem upLebFullJ2OK_of_parts3 (c : Ctx) (base : View BVal) (KO : KindOracle) (BK B : NodeId)
    (hU : UpUnlinkTreeOK c base) : UpLebFullJ2OK c base KO BK B := by
  intro w w3 top0 pre cv rk X Nn K depth stop w2 S hsa2 hvB hk hICEk hX0 hpos hB hI hRO hF hICE hr03 hkey
    hrk hvis hpX hpK hlkX hXN hlinkK hne hall hleaf hdepth hsD hbetween hLE hJ hsl hK0 hsm hJw _hMF hkidsw
    compact s t c1 y1 r hks
  have hBn : B ≤ w.next := by
    have h1 : B ≤ w2.next := hJ.1.1.fresh.1
    rw [hLE.2.2.2.2.2.1, hr03.2.2.2.2] at h1
    exact h1
  have hT2 := hU w w3 B X Nn K depth stop w2 S hI hr03 hlkX hlinkK hsD hLE
  obtain ⟨hlinks2, hwf2⟩ := linksWf_of_book c base B top0 w2 w2 hB hJ.1.1 (Or.inl rfl)
  rcases Nat.eq_zero_or_pos stop with hs | hs
  · subst hs
    exact writerWP_upLebFull_root_j2 c base hB.coherent hsa2 B hpos w w3 X Nn K depth w2 S hI hr03 hJw hBn
      hkidsw hlkX hXN hlinkK hdepth hbetween hX0 hLE hK0 hT2 hlinks2 hwf2 compact s t c1 y1 r hks
  · obtain ⟨D, rfl⟩ : ∃ D, stop = D + 1 := ⟨stop - 1, by omega⟩
    exact writerWP_upLebFull_below_j2 c base hsa2 B hpos w w3 X Nn K depth D w2 S hI hRO hr03 hJw hBn hkidsw
      hpX hpK hlkX hXN hlinkK hsD hbetween hX0 hLE hsl hK0 hT2 hlinks2 hwf2 compact s t c1 y1 r hks

/-- `DelStepsOKF3` with the upward delete's stop node proved at every stop and
kind: open are the state after the upward loop as a tree (`UpUnlinkTreeOK`) and
the fuel after the splits (`UpCascFitsOK`, `UpLebFitsOK`, `DelFullFitsOK`). -/
theorem delStepsOKF3_of_open11 (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts))
    (hU : ∀ ts, UpUnlinkTreeOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hFit : ∀ ts BK, UpCascFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) BK)
    (hFitL : ∀ ts BK, UpLebFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) BK)
    (hFits : ∀ ts, DelFullFitsOK (ctxOf p ts) (viewOf (treeRun p ts))) : DelStepsOKF3 p R :=
  delStepsOKF3_of_open5 p R hM hsa2 hRL hP
    (fun ts BK => upCascOKF3_of_parts3 _ _ _ _ (hU ts) (hFit ts BK))
    (fun ts BK => upLebOKF3_of_full _ _ _ _ (upLebFullOKF3_of_parts3 _ _ _ _ (hU ts) (hFitL ts BK))) hFits

/-- `DelStepsJ2OKF3` (the F3 route over R's pointers and kinds) with the upward
delete's stop node proved at every stop and kind: open are `UpUnlinkTreeOK`, the
fuel after the splits (`UpCascFitsOK`, `UpLebFitsOK`, `DelFullFitsOK`) and the
S inputs. -/
theorem delStepsJ2OKF3_of_openR6 (p : Params) (R : Struct BVal → Time → Prop)
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
    (hU : ∀ ts, UpUnlinkTreeOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hFit : ∀ ts BK, UpCascFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) BK)
    (hFitL : ∀ ts BK, UpLebFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) BK)
    (hFits : ∀ ts, DelFullFitsOK (ctxOf p ts) (viewOf (treeRun p ts))) :
    DelStepsJ2OKF3 p R S :=
  delStepsJ2OKF3_of_openR p R S hM hsa2 hRL hRP hRK hSI hSV hSB hSR hSF hSM
    (fun ts BK B => upCascJ2OKF3_of_parts3 _ _ _ _ B (hU ts) (hFit ts BK))
    (fun ts BK B => upLebJ2OKF3_of_full _ _ _ _ B (upLebFullOKF3_of_parts3 _ _ _ _ (hU ts) (hFitL ts BK))
      (upLebFullJ2OK_of_parts3 _ _ _ _ B (hU ts))) hFits

end SIS.Tree
