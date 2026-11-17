/-
The full stop node below the space root split in space (bergdb 030-01, step 6): a
stop node X (D + 1) that the transaction did not make, whose bitmap does not fit and
does not compact, with a last version of more than `splitAbove` klongs, splits into
two halves that are `HalfOK`, and its parent (inner or a segment leaf) takes their
klongs, through the cascade above (l4b's `writerWP_handleFull_spaceChain_live` and
`writerWP_handleFull_segSpaceChain_live`). No node is under the fill after. As for the
tree (`writerWP_upCasc_below_delST`, StopSwapBelow.lean), the split is applied at the
state whose stop node has its bitmap as if it had room (S'), where the tree is the
start's without the chain and S', holding more than `splitAbove` live klongs, is
filled; the heights come from the upward walk's start (`htInv_upFrame`) and the
split's heights' walk (`ht_handleFull`); all is moved by the swap.
`upCascCallBelowOK_of_rest` narrows the obligation to its other cases
(`UpCascSplitRestOK`).
-/
import SIS.Tree.LiveUpCascRootH

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

set_option maxHeartbeats 12800000 in
/-- The full stop node X (D + 1) below the space root, not made by the transaction,
split in space with no compaction: after the split the heights hold and the live
counts hold with no hole. -/
theorem writerWP_upCasc_below_spaceH (c : Ctx) (base : View BVal)
    (hsa2 : 2 ≤ c.p.splitAbove) (hp : MergeParamsOK c.p) (B : NodeId) (hpos : 0 < c.i)
    (w w3 : W) (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth D : Nat) (w2 v : W) (S : KNode)
    (hI : PutInv c base w)
    (hRO : RangeOrder (wNode c.p base w) c.i w.top.rootKey)
    (hr03 : ReadsAs c.p base w w3)
    (hLC : LiveCounts c.p (wNode c.p base w) c.i w.top.rootKey)
    (hpX : ∀ i, i ≤ depth → (w3.path[i]?).map (·.2) = some (X i))
    (hpK : ∀ i, 0 < i → i ≤ depth → w3.path[i]? = some (some (K i), X i))
    (hlkX : ∀ i, i ≤ depth → w3.nodes.lookup (X i) = some (Nn i))
    (hXN : ∀ i, i ≤ depth → wNode c.p base w (X i) = some (Nn i))
    (hlinkK : ∀ i, 0 < i → i ≤ depth → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (hsD : D + 1 < depth)
    (hX0 : X 0 = w.top.rootKey)
    (hLE : UpLoopEnd c B X Nn depth (D + 1) w3 w2 S)
    (hv : v = w2 ∨ ∃ s, v = { w2 with trail := s :: w2.trail })
    (hsl : (Nn (D + 1)).leaf = true) (hnm : (Nn (D + 1)).firstTime ≠ some c.i)
    (hcu : CacheUnique v)
    (hlinks2 : ∀ u c' z, TLink (wNode c.p base w2) c.i u c' z → z < w2.next)
    (hwf2 : ∀ z zn, wNode c.p base w2 z = some zn → klongsWf zn.ks = true)
    {H : NodeId → Nat → Prop} (hvo : ViewHtOK H B c) (hb3 : Book B c w3) (hi3 : HtInv H B c w3)
    (hkw3 : WriterKlongsWf w3) (hJ3 : TakeJ2 c base B w3) (hbv : Book B c v) (hghv : v.gh = w3.gh)
    (hpathv : v.path = w3.path)
    (compact : Bool) (hc : compact = false) (s : String)
    (hsp : c.p.splitAbove <
      (S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf (K (D + 1 + 1))))).size) :
    WriterWP (handleFull (D + 1) (X (D + 1))
        (S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf (K (D + 1 + 1))))) compact) c
      ({ v with trail := s :: v.trail } : W)
      (fun _ w' => HtInv H B c w' ∧ LiveEdges c.p (wNode c.p base w') c.i w'.top.rootKey) := by
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
  have hvp : v.path = w3.path := hpathv
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
  -- the stop node with its bitmap as if it had room (S')
  generalize hS'd : S.add c.i (.del (bitsUnion S.lastBitmap (S.bitsOf (K (D + 1 + 1))))) = S'
  have hbm : BitmapOf S S' c.i (K (D + 1 + 1)) := Or.inl hS'd.symm
  have hS'leaf : S'.leaf = S.leaf := bitmapOf_leaf S S' c.i _ hbm
  have hS'wf : klongsWf S'.ks = true := by rw [← hS'd]; exact KNode.add_delete_wf S c.i _ hSwf hneS'
  have hS't : ∀ s, Klong.time s ∈ S'.ks → s ≤ c.i := by
    rw [← hS'd]; exact KNode.add_times S c.i _ (fun s h => by cases h) hSt
  have hS'live : ∀ c' z, (c', z) ∈ S'.liveAt c.i ↔
      (c', z) ∈ (Nn (D + 1)).liveAt c.i ∧ c' ≠ K (D + 1 + 1) := by
    intro c' z
    rw [liveAt_iff_of_delete_lookup S S' c.i _ hSt hS't
      (fun c' => by rw [← hS'd]; exact S.add_delete_live_lookup c.i _ c')]
    exact hSlive c' z
  obtain ⟨s0, hs0, hs0m⟩ := KNode.firstTime_some_of_live (Nn (D + 1)) c.i hswf _ _ hsx
  have hs0S : S.firstTime = some s0 := by rw [KNode.firstTime_of_shapeOf hSsh]; exact hs0
  have hft : S.firstTime = S'.firstTime := by rw [hs0S, bitmapOf_firstTime S S' c.i _ hbm s0 hs0S]
  have hprev : S'.firstTime ≠ some c.i → S.toPrev (c.i - 1) = S'.toPrev (c.i - 1) := by
    intro hne
    have hpos : 0 < c.i := by
      rcases Nat.eq_zero_or_pos c.i with h0 | h0
      · exfalso
        have hle := hst_t s0 hs0m
        apply hne
        rw [← hft, hs0S, show s0 = c.i by omega]
      · exact h0
    show (⟨S.leaf, prefixAt S.ks (c.i - 1)⟩ : KNode) = ⟨S'.leaf, prefixAt S'.ks (c.i - 1)⟩
    rw [hS'leaf, bitmapOf_prefix S S' c.i _ hbm hpos]
  -- the chain with the stop node's node with its bitmap
  generalize hNn' : (fun i => if i = D + 1 then S' else Nn i) = Nn'
  have hNn'S : Nn' (D + 1) = S' := by rw [← hNn']; simp
  have hNn'i : ∀ i, i ≤ D → Nn' i = Nn i := fun i hi => by
    rw [← hNn']; simp only [show i ≠ D + 1 by omega, ↓reduceIte]
  have hCO : ∀ i, 0 < i → i ≤ D → ChainOrd c K Nn' i := by
    intro i h1 h2
    have h := chainOrd_of_ordG c base w3 depth X K Nn hP3 hO i h1 (by omega)
    unfold ChainOrd at h ⊢
    rw [hNn'i i h2, hNn'i (i - 1) (by omega)]
    exact h
  have hHO := halves_del_halfOK c.p hp S c.i (bitsUnion S.lastBitmap (S.bitsOf (K (D + 1 + 1))))
  have hflat := KNode.lastVersionGivenDel_flatAt S c.i (bitsUnion S.lastBitmap (S.bitsOf (K (D + 1 + 1))))
  have hord := KNode.lastVersionGivenDel_order S c.i (bitsUnion S.lastBitmap (S.bitsOf (K (D + 1 + 1))))
  generalize hlast : S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf (K (D + 1 + 1)))) = last
    at hsp hHO hflat hord ⊢
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
  have htkv : ({ v with trail := s :: v.trail } : W).taken.contains (X (D + 1)) = false := by
    show v.taken.contains _ = false; rw [hvt]; exact htk2
  -- the split moved from the state with S' to the writer's (the swap)
  have hswap : ∀ (post : Unit → W → Prop),
      WriterWP (handleFull (D + 1) (X (D + 1)) last compact) c
        (setX (X (D + 1)) S' ({ v with trail := s :: v.trail } : W)) post →
      WriterWP (handleFull (D + 1) (X (D + 1)) last compact) c ({ v with trail := s :: v.trail } : W) post := by
    intro post h
    have h2 := writerWP_handleFull_swap (X (D + 1)) S' S (D + 1) last compact c _ post (lookup_setX_self _ _ _)
      (by show X (D + 1) < v.next; rw [hvnx, h2nx]; exact hXlt (D + 1) (by omega))
      (by
        intro i e hi he
        have hp := hpX i (by omega)
        rw [← hvp] at hp
        change v.path[i]? = some e at he
        rw [he] at hp
        simp only [Option.map_some, Option.some.injEq] at hp
        rw [hp]
        intro hx
        have := hdist i (D + 1) (by omega) (by omega) hx
        omega)
      hft hS'leaf.symm hprev h
    rwa [setX_setX, setX_self _ _ _ (show CacheUnique ({ v with trail := s :: v.trail } : W) from hcu) hlk']
      at h2
  refine hswap _ ?_
  generalize hud : setX (X (D + 1)) S' ({ v with trail := s :: v.trail } : W) = u
  have hu_top : u.top = ({ v with trail := s :: v.trail } : W).top := by rw [← hud]; rfl
  have hu_next : u.next = ({ v with trail := s :: v.trail } : W).next := by rw [← hud]; rfl
  have hu_taken : u.taken = ({ v with trail := s :: v.trail } : W).taken := by rw [← hud]; rfl
  have hu_vals : u.vals = ({ v with trail := s :: v.trail } : W).vals := by rw [← hud]; rfl
  have hu_path : u.path = w3.path := by rw [← hud]; exact hvp
  have hwu : wNode c.p base u =
      updN (wNode c.p base ({ v with trail := s :: v.trail } : W)) (X (D + 1)) S' := by
    rw [← hud]; exact wNode_upsert_updN c.p base _ _ (X (D + 1)) S' rfl rfl htkv
  have hsnu : wNode c.p base u (X (D + 1)) = some S' := by rw [hwu]; exact updN_self _ _ _
  have hagreeU : ∀ u0, u0 ≠ X (D + 1) → (∀ i, D + 1 < i → i ≤ depth → u0 ≠ X i) →
      updN (wNode c.p base ({ v with trail := s :: v.trail } : W)) (X (D + 1)) S' u0 =
        wNode c.p base w3 u0 := fun u0 hus hnc => by
    rw [updN_ne _ _ _ _ hus, hwv']; exact hagree2 u0 hus hnc
  have hS2' : ∀ i, 0 ≤ i → i ≤ D + 1 →
      u.nodes.lookup (X i) = some (Nn' i) ∧ u.taken.contains (X i) = false := by
    intro i _ hi
    rcases Nat.lt_or_ge i (D + 1) with h | h
    · rw [hNn'i i (by omega), hu_taken]
      have hne : X i ≠ X (D + 1) := fun he => by
        have := hdist i (D + 1) (by omega) (by omega) he; omega
      refine ⟨?_, by show v.taken.contains _ = false; rw [hvt]; exact htk2' i (by omega)⟩
      rw [← hud]
      have := hlk2 i (by omega)
      simpa [setX, lookup_upsert, hne, hvn] using this
    · have hi' : i = D + 1 := by omega
      subst hi'
      rw [hNn'S, hu_taken]
      exact ⟨by rw [← hud]; exact lookup_setX_self _ _ _, htkv⟩
  have hT2' : TreeOK (wNode c.p base u) c.i u.top.rootKey := by
    rw [hu_top, hroot', hwu]
    exact treeOK_up_tr (wNode c.p base w3) _ c.i w3.top.rootKey X Nn K (D + 1) depth hsD hT3
      (hreach3 (D + 1) (by omega)) (fun i _ hi => hN3 i hi) (fun i h1 hi => hlinkK i (by omega) hi)
      (fun i i' _ hi _ hi' he => hdist i i' hi hi' he) hagreeU _ (updN_self _ _ _) id
      (fun c' z h => ⟨c', ((hS'live c' z).mp h).1, ((hS'live c' z).mp h).2, rfl⟩)
  have hS4' : ∀ i, 0 ≤ i → i ≤ D + 1 → TReach (wNode c.p base u) c.i u.top.rootKey (X i) := by
    intro i _ hi
    rw [hwu, hu_top, hroot']
    induction i with
    | zero => rw [hr03.2.1, hX0]; exact TReach.root
    | succ i ih =>
      have hi' : i ≤ D := by omega
      have hne : X i ≠ X (D + 1) := fun he => by
        have := hdist i (D + 1) (by omega) (by omega) he; omega
      refine TReach.link (ih (Nat.zero_le _) (by omega)) ⟨Nn i, ?_, by
        have := hlinkK (i + 1) (by omega) (by omega); simpa using this⟩
      rw [updN_ne _ _ _ _ hne, hwv']
      simp only [wNode, htk2' i hi', Bool.false_eq_true, ↓reduceIte, hlk2 i hi']
  have hS5u : ∀ z, u.next ≤ z → u.nodes.lookup z = none ∧ u.taken.contains z = false ∧
      knodeOf c.p base z = none := by
    intro z hz
    rw [hu_next] at hz
    obtain ⟨h1, h2, h3⟩ := hS5 z hz
    have hz0 : z ≠ X (D + 1) := fun he => by
      have := hXlt (D + 1) (by omega); rw [← hnx'] at this; omega
    refine ⟨?_, by rw [hu_taken]; exact h2, h3⟩
    rw [← hud]; simp only [setX, lookup_upsert, hz0, ↓reduceIte]; exact h1
  have hS6u : ∀ a c' z, TLink (wNode c.p base u) c.i a c' z → z < u.next := by
    intro a c' z ⟨an, han, hl⟩
    rw [hu_next]
    by_cases ha : a = X (D + 1)
    · rw [ha, hsnu] at han; cases han
      rw [hnx', hr03.2.2.2.2]
      exact hI.links (X (D + 1)) (Nn (D + 1)) c' z (tReach_reachS _ _ _ _ (hreach (D + 1) (by omega)))
        (hXN (D + 1) (by omega)) ((hS'live c' z).mp hl).1
    · rw [hwu, updN_ne _ _ _ _ ha] at han
      exact hS6 a c' z ⟨an, han, hl⟩
  have hWu : ∀ z zn, wNode c.p base u z = some zn → klongsWf zn.ks = true := by
    intro z zn hz
    by_cases hz0 : z = X (D + 1)
    · rw [hz0, hsnu] at hz; cases hz; exact hS'wf
    · rw [hwu, updN_ne _ _ _ _ hz0] at hz; exact hW z zn hz
  have hpath' : u.path = w3.path := hu_path
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
    · rw [show i = D + 1 by omega, hNn'S]; exact hS'wf
  have htimes' : ∀ i, 0 ≤ i → i ≤ D + 1 → ∀ t, Klong.time t ∈ (Nn' i).ks → t ≤ c.i := by
    intro i _ hi
    rcases Nat.lt_or_ge i (D + 1) with h | h
    · rw [hNn'i i (by omega)]; exact hI.times _ _ (hXN i (by omega))
    · rw [show i = D + 1 by omega, hNn'S]; exact hS't
  have hlinkK' : ∀ i, 0 < i → i ≤ D + 1 → (K i, X i) ∈ (Nn' (i - 1)).liveAt c.i := by
    intro i h1 hi
    rw [hNn'i (i - 1) (by omega)]; exact hlinkK i h1 (by omega)
  have hdist' : ∀ i i', 0 ≤ i → i ≤ D + 1 → 0 ≤ i' → i' ≤ D + 1 → X i = X i' → i = i' :=
    fun i i' _ hi _ hi' he => hdist i i' (by omega) (by omega) he
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
  -- the halves of the space split
  obtain ⟨r, hdiv, hsc, hrm, hfh, hsh⟩ := halves_facts_nil c.i ⟨S.leaf, last.ks⟩ (hlen2 hsp) hlt
  rw [hlastV] at hdiv hfh hsh
  obtain ⟨hfH, hsH⟩ := hHO hsp
  have hSl1 : S.leaf = true := hSleaf.trans hsl
  -- the stop node with its bitmap is filled: it holds a half's live klongs
  have hS'H : HalfOK c.p c.i S' := by
    have hle : ((halves S.leaf c.i last []).1.liveAt c.i).length ≤ (S'.liveAt c.i).length :=
      liveAt_length_le _ _ c.i (fun c' z h => ⟨z, (hS'live c' z).mpr ((hliveL c' z).mp (hfh c' z h).2)⟩)
    have h2 := hfH.2.1
    refine ⟨fun h0 => ?_, by omega, fun hm => by have := hfH.2.2 hm; omega⟩
    rw [h0] at hle
    simp only [List.length_nil] at hle
    omega
  -- the live counts at u: the start's without the chain, the stop node filled
  have hE3 : LiveEdges c.p (wNode c.p base w3) c.i w3.top.rootKey := by
    rw [hr03.1, hr03.2.1]; exact edges_of_liveCounts c.p _ _ _ hLC
  have hLu : LiveEdges c.p (wNode c.p base u) c.i u.top.rootKey := by
    have hHl := liveEdgesH_up c.p (wNode c.p base w3) (wNode c.p base u) c.i w3.top.rootKey X Nn K (D + 1)
      depth hsD hT3 (hreach3 (D + 1) (by omega)) (fun i _ hi => hN3 i hi) (fun i h1 hi => hlinkK i (by omega) hi)
      (fun i i' _ hi _ hi' he => hdist i i' hi hi' he) (fun u0 h1 h2 => by rw [hwu]; exact hagreeU u0 h1 h2)
      S' hsnu (by rw [hS'leaf, hSleaf]) (fun c' z h => (hS'live c' z).mp h) hS'H.1 hE3
    rw [hu_top, hroot']
    refine liveEdges_of_oneHole c.p _ c.i _ (X (D + 1)) _ hHl (fun y hy => hy) ?_ ?_
    · intro xn _ hxr _
      exfalso
      rw [hr03.2.1, ← hX0] at hxr
      have := hdist (D + 1) 0 (by omega) (by omega) hxr
      omega
    · intro u0 un cc xn _ _ _ hxn _
      rw [hsnu] at hxn
      cases hxn
      exact childOK_half c.p c.i un S' hS'H
  -- the heights at u: the walk's start's, through the loop's frame
  have hlku : u.nodes.lookup (X (D + 1)) = some S' := by rw [← hud]; exact lookup_setX_self _ _ _
  have htku : u.taken.contains (X (D + 1)) = false := (hS2' (D + 1) (Nat.zero_le _) (Nat.le_refl _)).2
  have hbu : Book B c u := by
    have hbv' : Book B c ({ v with trail := s :: v.trail } : W) :=
      ⟨hbv.next, hbv.ids, hbv.bound, hbv.nodup, hbv.leaf, hbv.tag, hbv.taken, hbv.top⟩
    have h := book_putNode B (X (D + 1)) S' c ({ v with trail := s :: v.trail } : W) hbv' ⟨S, hlk', hS'leaf⟩
    exact (h () u (by rw [← hud]; rfl)).1
  have hghu : u.gh = w3.gh := by rw [← hud]; exact hghv
  have htu : ∀ y, (∀ k, D + 1 < k → k ≤ depth → y ≠ X k) → u.taken.contains y = w3.taken.contains y := by
    intro y hy
    rw [hu_taken]; show v.taken.contains y = _; rw [hvt]; exact h2t y hy
  have htopu : u.top = w3.top := by rw [hu_top]; show v.top = _; rw [hvtop]; exact h2top
  have hnodesu : ∀ y, y ≠ X (D + 1) → (∀ k, D + 1 < k → k ≤ depth → y ≠ X k) →
      u.nodes.lookup y = w3.nodes.lookup y := by
    intro y h1 h2
    rw [← hud]; simp only [setX, lookup_upsert, h1, ↓reduceIte]
    show v.nodes.lookup y = _; rw [hvn]; exact h2n y h1 h2
  have hfJu : ∀ k, D + 1 < k → k ≤ depth → ChainFateW c.i B u (Nn k) (X k) := by
    intro k h1 h2
    refine chainFateW_frame c.i B w2 u (Nn k) (X k) (hfateJ2 k h1 h2) ?_ ?_
    · rw [hu_taken]; show v.taken = _; exact hvt
    · rw [← hud]; simp only [setX, lookup_upsert, Ne.symm (hXs k h1 h2), ↓reduceIte]
      show v.nodes.lookup _ = _; rw [hvn]
  have hX03 : X 0 = w3.top.rootKey := by rw [hr03.2.1, hX0]
  have hiu : HtInv H B c u :=
    htInv_upFrame B c base w3 u X Nn K depth (D + 1) hpos hb3 hi3 hkw3 hbu (fun e he => by rw [hghu]; exact he)
      hu_path hJ3 hT3 (fun q qn hq s' hs' => by rw [hr03.1] at hq; exact hI.times q qn hq s' hs') hsD hX03 hlkX
      htk3 hdist hreach3 hlinkK htu htopu hnodesu S' hlku hS't hS'live hfJu ⟨S, hSR, hbm⟩
  obtain ⟨g0, h0, hm0⟩ := kd_tag_of_lookup hb3 (hlkX (D + 1) (by omega))
  have hh0 : h0 = 0 := kd_h0 hb3 (hlkX (D + 1) (by omega)) hm0 hsl
  subst hh0
  have hxu : (X (D + 1), g0, 0) ∈ u.gh := by rw [hghu]; exact hm0
  have hpxu : u.path[D + 1]? = some (some (K (D + 1)), X (D + 1)) := by
    rw [hu_path]; exact hpK (D + 1) (by omega) (by omega)
  have hpf : PathFreeTo u (D + 1 + 1) := by
    intro d a' q hd hq
    have h := hpX d (by omega)
    rw [← hu_path, hq] at h
    simp only [Option.map_some, Option.some.injEq] at h
    rw [h]
    exact (hS2' d (Nat.zero_le _) (by omega)).2
  have hNu : NodeHt c H u 0 S' := ht_cache_at hlku hiu hxu htku (HtLe.refl u)
  have hlastK : kdKs (HtP c H u 0) last.ks := by
    intro c' y hm
    have hl0 := ht_flat_live hord hm
    have hl1 : (c', y) ∈ (⟨S.leaf, last.ks⟩ : KNode).liveAt c.i := by
      rw [hleq, KNode.liveAt_of_times _ c.i hlt]; exact hl0
    have hl2 := (hS'live c' y).mpr ((hliveL c' y).mp hl1)
    rw [KNode.liveAt_of_times _ c.i hS't] at hl2
    exact ⟨(hNu.live c' y hl2).1, fun h => absurd rfl h⟩
  have hHt : WriterWP (handleFull (D + 1) (X (D + 1)) last compact) c u (fun _ w' => HtInv H B c w') :=
    writerWP_mono (ht_handleFull B (D + 1) (X (D + 1)) last compact c u hvo hpos hbu hiu g0 0 hxu
      (some (K (D + 1))) hpxu hpf hflat hlastK) (fun _ _ h => h.2.1)
  -- the split's live counts, by the parent's kind
  have hf' : ∀ c' z, (c', z) ∈ (halves (Nn' (D + 1)).leaf c.i last []).1.liveAt c.i →
      c' < (halves (Nn' (D + 1)).leaf c.i last []).2.2 ∧ (c', z) ∈ (Nn' (D + 1)).liveAt c.i := by
    rw [hNn'S, hS'leaf, hdiv]
    intro c' z h
    exact ⟨(hfh c' z h).1, (hS'live c' z).mpr ((hliveL c' z).mp (hfh c' z h).2)⟩
  have hs' : ∀ c' z, (c', z) ∈ (halves (Nn' (D + 1)).leaf c.i last []).2.1.liveAt c.i →
      ∃ c0, (halves (Nn' (D + 1)).leaf c.i last []).2.2 ≤ c0 ∧
        c' = splitLocalCv (Nn' (D + 1)).leaf (halves (Nn' (D + 1)).leaf c.i last []).2.2 c0 ∧
        (c0, z) ∈ (Nn' (D + 1)).liveAt c.i := by
    rw [hNn'S, hS'leaf, hdiv]
    intro c' z h
    obtain ⟨c0, h1, h2, h3⟩ := hsh c' z h
    exact ⟨c0, h1, h2, (hS'live c0 z).mpr ((hliveL c0 z).mp h3)⟩
  have hfH' : HalfOK c.p c.i (halves (Nn' (D + 1)).leaf c.i last []).1 := by rw [hNn'S, hS'leaf]; exact hfH
  have hsH' : HalfOK c.p c.i (halves (Nn' (D + 1)).leaf c.i last []).2.1 := by rw [hNn'S, hS'leaf]; exact hsH
  have hfirst' : (Nn' (D + 1)).firstTime ≠ some c.i := by
    rw [hNn'S, ← hft, KNode.firstTime_of_shapeOf hSsh]; exact hnm
  have hR0 : u.top.rootKey = X 0 := by rw [hu_top, hroot', hr03.2.1, hX0]
  have hLv : WriterWP (handleFull (D + 1) (X (D + 1)) last compact) c u
      (fun _ w' => LiveEdges c.p (wNode c.p base w') c.i w'.top.rootKey) := by
    subst hc
    show WriterWP (handleFullWith (fun q more => appendKlongs D q more) (D + 1) (X (D + 1)) [] last false) c u _
    cases hql : (Nn D).leaf with
    | false =>
      refine writerWP_handleFull_spaceChain_live c base w3.path D X K Nn' last (fun i hi => hpX i (by omega))
        (fun i h1 hi => hpK i h1 (by omega)) hlinkK' hrange hlen (fun i hi => hwf' i (Nat.zero_le _) hi)
        (fun i hi => htimes' i (Nat.zero_le _) hi)
        (fun i i' hi hi' => hdist' i i' (Nat.zero_le _) hi (Nat.zero_le _) hi') hfirst'
        (by rw [hNn'i D (Nat.le_refl _)]; exact hql) hsp hf' hs' hfH' hsH' ?_ hp u hu_path
        (fun i hi => hS2' i (Nat.zero_le _) hi) hT2' (fun i hi => hS4' i (Nat.zero_le _) hi) hS5u hS6u hR0 hLu
      rw [hNn'S, hS'leaf, hNn'i D (Nat.le_refl _), hdiv]
      exact hrangeLn hql r.1 r.2 hrm hsc
    | true =>
      exact writerWP_handleFull_segSpaceChain_live c base w3.path D X K Nn' last (fun i hi => hpX i (by omega))
        (fun i h1 hi => hpK i h1 (by omega)) hlinkK' hrange hlen (fun i hi => hwf' i (Nat.zero_le _) hi)
        (fun i hi => htimes' i (Nat.zero_le _) hi)
        (fun i i' hi hi' => hdist' i i' (Nat.zero_le _) hi (Nat.zero_le _) hi') hfirst'
        (by rw [hNn'i D (Nat.le_refl _)]; exact hql) hsp (by rw [hNn'S, hS'leaf, hdiv]; exact hsc) hf' hs' hfH' hsH'
        hp u hu_path (fun i hi => hS2' i (Nat.zero_le _) hi) hT2' (fun i hi => hS4' i (Nat.zero_le _) hi) hS5u hS6u
        hR0 hLu
  exact writerWP_mono (writerWP_and hHt hLv) (fun _ _ h => h)


/-- The full stop node's cases left after the space root not made and the space split
below the root (bergdb 030-01, step 6): at the stop node's split (`handleFull`, after
the bitmap's note), where it is not a stop node below the root, not made by the
transaction, split in space with no compaction, the split ends with the heights and the
hole's form at the stop node's pair. Left: a split in time (the copy, or the stop node
made by the transaction, the hole) and a made stop node's split in space in place. -/
def UpCascSplitRestOK (c : Ctx) (base : View BVal) (KO : KindOracle) (B : NodeId)
    (H : NodeId → Nat → Prop) : Prop :=
  ∀ (w w3 : W) (top0 : Top) (pre : List Nat) (cv : Nat) (rk : NodeId)
    (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth stop : Nat) (w2 : W) (S : KNode)
    (g : Nat) (compact : Bool) (s : String),
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
    (0 < stop ∨ (Nn 0).firstTime = some c.i) →
    w2.gh.lookup (X stop) = some (g, 0) →
    ¬ (0 < stop ∧ (Nn stop).firstTime ≠ some c.i ∧ compact = false ∧
      c.p.splitAbove < (S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf (K (stop + 1))))).size) →
    WriterWP (handleFull stop (X stop)
        (S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf (K (stop + 1))))) compact) c
      ({ ({ w2 with trail := "up.stop-at-segment-leaf" :: w2.trail } : W) with
        trail := s :: ({ w2 with trail := "up.stop-at-segment-leaf" :: w2.trail } : W).trail } : W)
      (fun _ w' => HtInv H B c w' ∧ LiveHoleW (pre ++ [cv]) g 0 c base w')


set_option maxHeartbeats 3200000 in
/-- `UpCascCallBelowOK` from its cases left (`UpCascSplitRestOK`): the space split of a
stop node below the root that the transaction did not make is proved
(`writerWP_upCasc_below_spaceH`), the tree's facts by `upCascJ2OKT_holds`, the books by
`putBook_appendDeleteKlong`. -/
theorem upCascCallBelowOK_of_rest (c : Ctx) (base : View BVal) (KO : KindOracle) (B : NodeId)
    (H : NodeId → Nat → Prop) (h : UpCascSplitRestOK c base KO B H) : UpCascCallBelowOK c base KO B H := by
  intro w w3 top0 pre cv rk X Nn K depth stop w2 S g hvc hm hsa2 hp hvB hk hICEk hvo hkw hpos hB hbook hI
    hRO hICE hLC hJ2 hMF3 hr03 hJ3 hH3 hwf3 hlen3 hX0 hkey hrk hvis hpX hpK hlkX hXN hlinkK hne hall hleaf
    hkids hdepth hsD hbetween hstp hLE hJw2 hgeq hsl hDR hcase hlook
  have hJv := kdJP_note c base B top0 hB KO B hvB hk _ "up.stop-at-segment-leaf" w2 hJw2
  have hT := upCascJ2OKT_holds c base KO B w w3 top0 pre cv rk X Nn K depth stop w2 _ S hm hLC hJ3 hlen3
    hsa2 hvB hk hICEk hX0 hpos hB hI hRO hICE hr03 hkey hrk hvis hpX hpK hlkX hXN hlinkK hne hall hleaf
    hdepth hsD hbetween hLE (Or.inr ⟨_, rfl⟩) hJv (Or.inl hsl) hDR hJ2 hMF3 hkids
  have hPB := putBook_appendDeleteKlong (X stop) stop (K (stop + 1)) c base B top0 hB _ hJv.1.1
  have hcu : CacheUnique ({ w2 with trail := "up.stop-at-segment-leaf" :: w2.trail } : W) :=
    cacheUnique_of_book hJv.1.1.book
  obtain ⟨hlinks2, hwf2⟩ := linksWf_of_book c base B top0 _ w2 hB hJv.1.1 (Or.inr ⟨_, rfl⟩)
  -- the stop node at the loop's end and its bitmap's bits
  have hSl : ({ w2 with trail := "up.stop-at-segment-leaf" :: w2.trail } : W).nodes.lookup (X stop) = some S :=
    hLE.2.2.2.2.2.2.2.1
  have hsx : (K (stop + 1), X (stop + 1)) ∈ (Nn stop).liveAt c.i := by
    have := hlinkK (stop + 1) (by omega) (by omega); simpa using this
  have hst_t : ∀ s', Klong.time s' ∈ (Nn stop).ks → s' ≤ c.i := hI.times _ _ (hXN stop (by omega))
  have hSsh : S.shapeOf = (Nn stop).shapeOf := by
    rcases hLE.2.2.2.2.2.2.2.2.1 with h | ⟨ti, dst, h⟩
    · rw [h]
    · rw [h]; exact KNode.retarget_shapeOf _ _ _ _
  have hneS' : bitsUnion S.lastBitmap (S.bitsOf (K (stop + 1))) ≠ S.lastBitmap := by
    rw [KNode.lastBitmap_of_shapeOf hSsh, KNode.bitsOf_of_shapeOf hSsh]
    apply KNode.delete_bitmap_changes_of_live
    rw [KNode.liveAt_of_times _ c.i hst_t] at hsx
    exact List.mem_map.mpr ⟨_, hsx, rfl⟩
  have hHL : WriterWP (appendDeleteKlong (X stop) stop (K (stop + 1))) c
      ({ w2 with trail := "up.stop-at-segment-leaf" :: w2.trail } : W)
      (fun _ w' => HtInv H B c w' ∧ LiveHoleW (pre ++ [cv]) g 0 c base w') := by
    refine writerWP_appendDeleteKlong_full_of (X stop) stop (K (stop + 1)) S c _ hSl hneS' hDR _ ?_
    intro compact s
    by_cases hsp : 0 < stop ∧ (Nn stop).firstTime ≠ some c.i ∧ compact = false ∧
        c.p.splitAbove < (S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf (K (stop + 1))))).size
    · obtain ⟨hs0, hnm, hc, hsz⟩ := hsp
      obtain ⟨D, rfl⟩ : ∃ D, stop = D + 1 := ⟨stop - 1, by omega⟩
      refine writerWP_mono (writerWP_upCasc_below_spaceH c base hsa2 hp B hpos w w3 X Nn K depth D w2 _ S hI hRO
        hr03 hLC hpX hpK hlkX hXN hlinkK hsD hX0 hLE (Or.inr ⟨_, rfl⟩) hsl hnm hcu hlinks2 hwf2 hvo hJ3.2.1 hH3
        hwf3 (takeJ2_of_readsAs c base B w w3 hJ2 hr03) hJv.1.2.1 hgeq hJw2.2 compact hc s hsz) ?_
      rintro _ w' ⟨hHt, hE⟩
      exact ⟨hHt, liveEdgesH_of_liveEdges _ _ _ _ _ hE⟩
    · exact h w w3 top0 pre cv rk X Nn K depth stop w2 S g compact s hvc hm hsa2 hp hvB hk hICEk hvo hkw hpos hB
        hbook hI hRO hICE hLC hJ2 hMF3 hr03 hJ3 hH3 hwf3 hlen3 hX0 hkey hrk hvis hpX hpK hlkX hXN hlinkK hne hall
        hleaf hkids hdepth hsD hbetween hstp hLE hJw2 hgeq hsl hDR hcase hlook hsp
  refine writerWP_mono (writerWP_and (writerWP_and hT hPB) hHL) ?_
  rintro _ w' ⟨⟨hD', hpb'⟩, hHt', hLH'⟩
  exact ⟨hD', hpb', hHt', hLH'⟩

/-- `UpCascSplitRestOK` at the contexts of the runs of R. -/
def UpCascSplitRestRuns (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts (tx : Tx), Within p (ts ++ [tx]) → R (treeRun p ts) ts.length →
    UpCascSplitRestOK (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base
      (htOracleOf p (treeRun p ts))

/-- `UpCascCallRuns` (the premise of `delCaseLive_emptyCasc`) from the full stop node's
cases left at the runs (`UpCascSplitRestRuns`). -/
theorem upCascCallRuns_of_rest (p : Params) (R : Struct BVal → Time → Prop) (h : UpCascSplitRestRuns p R) :
    UpCascCallRuns p R :=
  upCascCallRuns_of_below p R (fun ts tx hw hr => upCascCallBelowOK_of_rest _ _ _ _ _ (h ts tx hw hr))

end SIS.Tree
