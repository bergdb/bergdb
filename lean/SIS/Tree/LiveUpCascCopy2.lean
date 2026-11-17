/-
The copy of a stop node below the space root, not made, split in time, under the fill
below an inner parent that the transaction made, full or compacting, whose own last version
is within a split's bound (bergdb 030-01, step 6): the parent splits in time in place and
its klong of the stop node names the copy, so the copy stays the hole under the same
parent (l4b's `writerWP_handleFull_timeMadeParent_liveGh`), and the merges' descent finds
it (`holeAtW_stopCopy`). `upCascSplitRest6OK_of_rest7` narrows the obligation
(`UpCascSplitRest7OK`).
-/
import SIS.Tree.LiveUpCascCopy

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

set_option maxHeartbeats 12800000 in
/-- The full stop node X (D + 1) below the space root, not made by the transaction,
split in time below an inner parent that the transaction made, with no room for the
copy's klong or compacting, whose own last version is within a split's bound: the
parent splits in time in place, its klong of the stop node naming the copy (l4b's
`writerWP_handleFull_timeMadeParent_liveGh`):
after the split the live counts hold but at the copy (l4a's
`writerWP_handleFull_timeRoom_liveGh` at the state with the stop node's bitmap, moved by
the swap), which the merges' descent at the copy's pair finds (`holeAtW_stopCopy`). -/
theorem writerWP_upCasc_below_copyMadeParent (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (hsa2 : 2 ≤ c.p.splitAbove) (B : NodeId) (hpos : 0 < c.i)
    (KO : KindOracle) (hvB : ViewIdsBelow B c.view) (hk : ViewKinds KO B c) (hB : PutBase c base B)
    (top0 : Top) (pre : List Nat) (cv : Nat) (rk : NodeId) (g : Nat)
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
    (hlen3 : w3.path.length = depth + 1) (hkey : keyWf (pre ++ [cv]) = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hvis : (X depth, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk) (hleaf : (Nn depth).leaf = true)
    (hstp : (Nn (D + 1)).allKeysIn (bitsUnion (Nn (D + 1)).lastBitmap ((Nn (D + 1)).bitsOf (K (D + 1 + 1)))) = true →
      D + 1 = 0 ∧ (Nn 0).leaf = true)
    (hql : (Nn D).leaf = false) (hD0 : 0 < D)
    (hfullq : ¬ ((Nn D).size + 2 ≤ c.p.M ∧ deadOver c.p ((Nn D).add c.i (.key (K (D + 1)) w2.next)) = false))
    (hqmade : (Nn D).firstTime = some c.i) (hqsz : ((Nn D).lastVersion c.i).size ≤ c.p.splitAbove)
    (hlook : w3.gh.lookup (X (D + 1)) = some (g, 0))
    (hcu : CacheUnique v)
    (hlinks2 : ∀ u c' z, TLink (wNode c.p base w2) c.i u c' z → z < w2.next)
    (hwf2 : ∀ z zn, wNode c.p base w2 z = some zn → klongsWf zn.ks = true)
    (hghv : v.gh = w3.gh) (hpathv : v.path = w3.path) (hJv : KdJP c B top0 KO B w3.path v)
    (compact : Bool) (s : String)
    (htime : (!compact && decide ((S.lastVersionGivenDel c.i
      (bitsUnion S.lastBitmap (S.bitsOf (K (D + 1 + 1))))).size > c.p.splitAbove)) = false) :
    WriterWP (handleFull (D + 1) (X (D + 1))
        (S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf (K (D + 1 + 1))))) compact) c
      ({ v with trail := s :: v.trail } : W)
      (fun _ w' => LiveHoleW (pre ++ [cv]) g 0 c base w') := by
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
  have hJv4 := kdJP_note c base B top0 hB KO B hvB hk _ s v hJv
  have hlk4 : ({ v with trail := s :: v.trail } : W).nodes.lookup (X (D + 1)) = some S := hlkv
  have hx4 : (X (D + 1), g, 0) ∈ ({ v with trail := s :: v.trail } : W).gh := by
    show (X (D + 1), g, 0) ∈ v.gh
    rw [hghv]; exact upf_mem_of_lookup _ _ _ hlook
  have hkdS : kdKs (KindKlong KO ({ v with trail := s :: v.trail } : W) g 0)
      (S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf (K (D + 1 + 1))))).ks :=
    kdKs_lastVersionGivenDel c.i _ (kd_cache_at hlk4 hJv4.1.2.2 hx4 (KdLe.refl _))
  have hflat := KNode.lastVersionGivenDel_flatAt S c.i (bitsUnion S.lastBitmap (S.bitsOf (K (D + 1 + 1))))
  have hord := KNode.lastVersionGivenDel_order S c.i (bitsUnion S.lastBitmap (S.bitsOf (K (D + 1 + 1))))
  generalize hlast : S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf (K (D + 1 + 1)))) = last
    at htime hkdS hflat hord ⊢
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
  generalize hud : setX (X (D + 1)) S' ({ v with trail := s :: v.trail } : W) = u at hswap
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
  have hVu : TreeOK (updN (wNode c.p base u) (X (D + 1)) ⟨S'.leaf, last.ks⟩) c.i u.top.rootKey := by
    rw [hwu, updN_updN_same, hS'leaf, hu_top]; exact hV
  have hvxu : ∀ c' z, (c', z) ∈ (⟨S'.leaf, last.ks⟩ : KNode).liveAt c.i → z < u.next := by
    rw [hS'leaf, hu_next]; exact hvx
  have hkl : (K (D + 1), X (D + 1)) ∈ (Nn D).liveAt c.i := by
    have := hlinkK (D + 1) (by omega) (by omega); simpa using this
  have hSl1 : S.leaf = true := hSleaf.trans hsl
  have hlku : u.nodes.lookup (X (D + 1)) = some S' := by rw [← hud]; exact lookup_setX_self _ _ _
  have htku : u.taken.contains (X (D + 1)) = false := (hS2' (D + 1) (Nat.zero_le _) (Nat.le_refl _)).2
  have hlqu : u.nodes.lookup (X D) = some (Nn D) := by
    have h := (hS2' D (Nat.zero_le _) (by omega)).1
    rwa [hNn'i D (Nat.le_refl _)] at h
  have hqtu : u.taken.contains (X D) = false := (hS2' D (Nat.zero_le _) (by omega)).2
  have hqx : X D ≠ X (D + 1) := fun he => by have := hdist D (D + 1) (by omega) (by omega) he; omega
  have hxnu : X (D + 1) < u.next := by rw [hu_next, hnx']; exact hXlt (D + 1) (by omega)
  have hqnu : X D < u.next := by rw [hu_next, hnx']; exact hXlt D (by omega)
  have hpq : (u.path[D]?).map (·.2) = some (X D) := by rw [hu_path]; exact hpX D (by omega)
  have hpxu : u.path[D + 1]? = some (some (K (D + 1)), X (D + 1)) := by
    rw [hu_path]; exact hpK (D + 1) (by omega) (by omega)
  have hfirstS' : S'.firstTime ≠ some c.i := by rw [← hft, KNode.firstTime_of_shapeOf hSsh]; exact hnm
  -- the copy keeps a live klong
  have hkeep : (Nn (D + 1)).allKeysIn (bitsUnion (Nn (D + 1)).lastBitmap
      ((Nn (D + 1)).bitsOf (K (D + 1 + 1)))) = false := by
    cases h : (Nn (D + 1)).allKeysIn (bitsUnion (Nn (D + 1)).lastBitmap
        ((Nn (D + 1)).bitsOf (K (D + 1 + 1)))) with
    | false => rfl
    | true => exact absurd (hstp h).1 (by omega)
  obtain ⟨c1, z1, hc1, hz1⟩ := exists_live_of_keep _ _ hkeep
  have hposL : (⟨S.leaf, last.ks⟩ : KNode).liveAt c.i ≠ [] := by
    intro h0
    have : (c1, z1) ∈ (⟨S.leaf, last.ks⟩ : KNode).liveAt c.i :=
      (hliveL c1 z1).mpr ⟨by rw [KNode.liveAt_of_times _ c.i hst_t]; exact hz1, hc1⟩
    rw [h0] at this
    cases this
  have hE3 : LiveEdges c.p (wNode c.p base w3) c.i w3.top.rootKey := by
    rw [hr03.1, hr03.2.1]; exact edges_of_liveCounts c.p _ _ _ hLC
  -- the tree with the stop node's last version at u: the live counts but at the stop node
  have hVlive : LiveEdgesH c.p (updN (wNode c.p base u) (X (D + 1)) ⟨S'.leaf, last.ks⟩) c.i u.top.rootKey
      (fun z => z = X (D + 1)) := by
    rw [hu_top, hroot']
    exact liveEdgesH_up c.p (wNode c.p base w3) _ c.i w3.top.rootKey X Nn K (D + 1) depth hsD hT3
      (hreach3 (D + 1) (by omega)) (fun i _ hi => hN3 i hi) (fun i h1 hi => hlinkK i (by omega) hi)
      (fun i i' _ hi _ hi' he => hdist i i' hi hi' he)
      (fun u0 h1 h2 => by rw [updN_ne _ _ _ _ h1, hwu]; exact hagreeU u0 h1 h2) _ (updN_self _ _ _)
      (by rw [hS'leaf, hSleaf]) (fun c' z h => by rw [hS'leaf] at h; exact (hliveL c' z).mp h)
      (by rw [hS'leaf]; exact hposL) hE3
  have hqRV : TReach (updN (wNode c.p base u) (X (D + 1)) ⟨S'.leaf, last.ks⟩) c.i u.top.rootKey (X D) := by
    have key : ∀ i, i ≤ D → TReach (updN (wNode c.p base u) (X (D + 1)) ⟨S'.leaf, last.ks⟩) c.i
        u.top.rootKey (X i) := by
      intro i
      induction i with
      | zero =>
        intro _
        rw [hu_top, hroot', hr03.2.1, ← hX0]
        exact TReach.root
      | succ i ih =>
        intro hi
        have hne : X i ≠ X (D + 1) := fun he => by have := hdist i (D + 1) (by omega) (by omega) he; omega
        refine TReach.link (ih (by omega)) ⟨Nn i, ?_, by
          have := hlinkK (i + 1) (by omega) (by omega); simpa using this⟩
        rw [updN_ne _ _ _ _ hne]
        have h := hS2' i (Nat.zero_le _) (by omega)
        rw [hNn'i i (by omega)] at h
        simp only [wNode, h.2, Bool.false_eq_true, ↓reduceIte, h.1]
    exact key D (Nat.le_refl _)
  have hfreshT : ∀ u0 c', TReach (updN (wNode c.p base u) (X (D + 1)) ⟨S'.leaf, last.ks⟩) c.i u.top.rootKey u0 →
      ¬ TLink (updN (wNode c.p base u) (X (D + 1)) ⟨S'.leaf, last.ks⟩) c.i u0 c' u.next := by
    intro u0 c' _ hl
    obtain ⟨m, hm, hc⟩ := hl
    by_cases hu0 : u0 = X (D + 1)
    · rw [hu0, updN_self] at hm
      cases hm
      have := hvxu c' u.next hc
      omega
    · rw [updN_ne _ _ _ _ hu0] at hm
      have := hS6u u0 c' u.next ⟨m, hm, hc⟩
      omega
  obtain ⟨hnl0, hnt0, hnb0⟩ := hS5u u.next (Nat.le_refl _)
  have hnxu' : wNode c.p base u u.next = none := by
    simp only [wNode, hnt0, Bool.false_eq_true, ↓reduceIte, hnl0]; exact hnb0
  have hfullqu : ¬ ((Nn D).size + 2 ≤ c.p.M ∧ deadOver c.p ((Nn D).add c.i (.key (K (D + 1)) u.next)) = false) := by
    rw [hu_next]; show ¬ ((Nn D).size + 2 ≤ c.p.M ∧ deadOver c.p ((Nn D).add c.i (.key (K (D + 1)) v.next)) = false)
    rw [hvnx]; exact hfullq
  have hU : WriterWP (handleFull (D + 1) (X (D + 1)) last compact) c u (fun _ w' =>
      LiveEdgesH c.p (wNode c.p base w') c.i w'.top.rootKey (fun z => z = u.next) ∧
        (∀ z, z ≠ X D → z ≠ X (D + 1) → z ≠ u.next → w'.nodes.lookup z = u.nodes.lookup z) ∧
        w'.nodes.lookup u.next = some ⟨S'.leaf, last.ks⟩ ∧
        (∃ l : KNode, klongsWf l.ks = true ∧ (∀ s, Klong.time s ∈ l.ks → s ≤ c.i) ∧
          (∀ c', l.live.lookup c' = if K (D + 1) == c' then some u.next else (Nn D).live.lookup c') ∧
          w'.nodes.lookup (X D) = some ⟨(Nn D).leaf, l.ks⟩) ∧
        w'.taken = u.taken ∧ w'.top = u.top ∧ w'.gh.lookup u.next = u.gh.lookup (X (D + 1))) := by
    obtain ⟨d'', rfl⟩ : ∃ d'', D = d'' + 1 := ⟨D - 1, by omega⟩
    have hlq0u : u.nodes.lookup (X d'') = some (Nn d'') := by
      have h := (hS2' d'' (Nat.zero_le _) (by omega)).1
      rwa [hNn'i d'' (by omega)] at h
    exact writerWP_handleFull_timeMadeParent_liveGh d'' (X (d'' + 1 + 1)) (X (d'' + 1)) (X d'') S' (Nn (d'' + 1))
      (Nn d'') (K (d'' + 1 + 1)) last compact c base u hlku hlqu hqtu hqx hxnu hqnu hlq0u
      (by rw [hu_next, hnx']; exact hXlt d'' (by omega)) hfirstS' htime
      (by rw [hu_path]; exact hpX d'' (by omega)) hpq hpxu (hI.times _ _ (hXN (d'' + 1) (by omega))) hqmade hqsz
      hfullqu hkl hVu hqRV hnxu' hnl0 hnt0 hfreshT hVlive
  have hA := hswap _ hU
  have hKd := kd_handleFull KO B (D + 1) (X (D + 1)) last compact c _ hvB hk hJv4.1.2.1 hJv4.1.2.2 g 0 hx4
    ⟨_, by show v.path[D + 1]? = _; rw [hpathv]; exact hpK (D + 1) (by omega) (by omega)⟩ hkdS
  refine writerWP_mono (writerWP_and hA hKd) ?_
  rintro _ wf ⟨⟨hEf, hlookf, hlyf, ⟨lq, _, hltq, hllk, hlqf⟩, _, htopf, hghy⟩, hfb, hfi, _, _⟩
  -- R1 at the copy, the key's path read from the walk's start
  obtain ⟨e0, rest, hpe⟩ : ∃ e0 rest, w3.path = e0 :: rest := by
    cases h : w3.path with
    | nil => rw [h] at hlen3; simp at hlen3
    | cons e0 rest => exact ⟨e0, rest, rfl⟩
  have hPl : rest.length = depth := by rw [hpe] at hlen3; simpa using hlen3
  have hnA : ∀ i, i ≤ depth → nodeAt w.top.rootKey rest i = X i := by
    intro i hi
    cases i with
    | zero => simp [nodeAt, hX0]
    | succ j =>
      have h := hpX (j + 1) hi
      rw [hpe] at h
      simp only [List.getElem?_cons_succ] at h
      simp only [nodeAt, List.getElem?_cons_succ, List.getElem?_map]
      rw [Option.map_eq_some_iff] at h
      obtain ⟨e, he, he2⟩ := h
      rw [he]; simp [he2]
  have hlinkP : LinkedFrom (wNode c.p base w) c.i w.top.rootKey rest := by
    refine linkedFrom_of_nodes _ c.i rest w.top.rootKey (fun i hi => ?_)
    rw [hPl] at hi
    have h := hpK (i + 1) (by omega) (by omega)
    rw [hpe] at h
    simp only [List.getElem?_cons_succ] at h
    refine ⟨K (i + 1), Nn i, by rw [hnA (i + 1) (by omega)]; exact h, by rw [hnA i (by omega)]; exact hXN i (by omega),
      by rw [hnA (i + 1) (by omega)]; have := hlinkK (i + 1) (by omega) (by omega); simpa using this⟩
  have hXD : nodeAt w.top.rootKey rest rest.length = X depth := by rw [hPl]; exact hnA depth (Nat.le_refl _)
  have hD1 : nodeAt w.top.rootKey rest (D + 1) = X (D + 1) := hnA (D + 1) (by omega)
  have hDq : nodeAt w.top.rootKey rest (D + 1 - 1) = X D := hnA D (by omega)
  have hlkX' : ∀ i, i ≤ rest.length → ({ w3 with path := (none, w.top.rootKey) :: rest } : W).nodes.lookup
      (nodeAt w.top.rootKey rest i) = some ((wNode c.p base w (nodeAt w.top.rootKey rest i)).getD (Nn depth)) := by
    intro i hi
    rw [hPl] at hi
    rw [hnA i hi, hXN i hi]
    exact hlkX i hi
  have hcut : ∀ z, (((rest[D + 1]?).bind (·.1)).getD 0, z) ∉ (⟨S'.leaf, last.ks⟩ : KNode).live := by
    intro z hz
    have h := hpK (D + 1 + 1) (by omega) (by omega)
    rw [hpe] at h
    simp only [List.getElem?_cons_succ] at h
    rw [h] at hz
    simp only [Option.bind_some, Option.getD_some] at hz
    rw [hS'leaf, ← KNode.liveAt_of_times (⟨S.leaf, last.ks⟩ : KNode) c.i hlt] at hz
    exact ((hliveL _ z).mp hz).2 rfl
  have hKD : ((rest[D + 1 - 1]?).bind (·.1)).getD 0 = K (D + 1) := by
    have h := hpK (D + 1) (by omega) (by omega)
    rw [hpe] at h
    simp only [List.getElem?_cons_succ] at h
    rw [show D + 1 - 1 = D by omega, h]; rfl
  have hy3 : ({ w3 with path := (none, w.top.rootKey) :: rest } : W).nodes.lookup u.next = none := by
    show w3.nodes.lookup u.next = none
    cases h' : w3.nodes.lookup u.next with
    | none => rfl
    | some _ =>
      have := hI3.ids.1 u.next (by rw [h']; rfl)
      rw [hu_next, hnx'] at this
      omega
  have hgL : rdG c wf u.next = some (g, 0) := by
    rw [rdG_of_lookup c wf _ _ hlyf, hghy, ← hud]
    show v.gh.lookup (X (D + 1)) = _
    rw [hghv]; exact hlook
  have hH := holeAtW_stopCopy c base hvc w ({ w3 with path := (none, w.top.rootKey) :: rest } : W) wf pre cv rk
    (X depth) (Nn depth) rest (D + 1) g u.next ⟨S'.leaf, last.ks⟩ ⟨(Nn D).leaf, lq.ks⟩ hT
    (fun y hy => hI.untaken y (tReach_reachS _ _ _ _ hy)) hI.wf hrk hvis (hXN depth (Nat.le_refl _)) hleaf
    ⟨hr03.1, hr03.2.1, hr03.2.2.1, hr03.2.2.2.1, hr03.2.2.2.2⟩ rfl hlinkP hXD hlkX' hkey (by omega) (by omega)
    hI.times (by rw [hD1, hXN (D + 1) (by omega)]; exact hsl) (by rw [hDq, hXN D (by omega)]; exact hql)
    (by
      intro z h1 h2 h3 h4
      rw [hDq] at h1
      rw [hD1] at h2
      rw [hlookf z h1 h2 h3, ← hud]
      simp only [setX, lookup_upsert, h2, ↓reduceIte]
      show v.nodes.lookup z = _
      rw [hvn, h2n z h2 (fun k hk1 hk2 hz => h4 k hk1 (by omega) (by rw [hnA k (by omega)]; exact hz))])
    hy3 (by rw [htopf, hu_top]; show v.top = w3.top; rw [hvtop]; exact h2top)
    (by rw [hDq]; exact hlqf) hql
    (by
      intro cc
      rw [hKD, hDq, hXN D (by omega)]
      exact KNode.searchLte_redirect (Nn D) ⟨(Nn D).leaf, lq.ks⟩ c.i (K (D + 1)) u.next
        (hI.times _ _ (hXN D (by omega))) hltq ⟨X (D + 1), by
          rw [← KNode.liveAt_of_times _ c.i (hI.times _ _ (hXN D (by omega)))]; exact hkl⟩
        (fun c' => by rw [upf_live_ks ⟨(Nn D).leaf, lq.ks⟩ lq rfl]; exact hllk c') cc)
    hlyf (by rw [hS'leaf]; exact hSl1) hcut hlwf hlt (segRd_of KO B c wf hfb hfi hk) hgL
  exact liveHoleW_of_hole (pre ++ [cv]) g 0 c base wf u.next hEf hH


/-- The full stop node's case left after the copy below a made parent split in time in
place (bergdb 030-01, step 6): a stop node below the space root, not made, split in time,
whose copy is under the fill below an inner parent without room or compacting, the parent
not made by the transaction, or split in space, or the space root: the hole at the copy
below the parent's split (030-01's R4). -/
def UpCascSplitRest7OK (c : Ctx) (base : View BVal) (KO : KindOracle) (B : NodeId)
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
    ¬ (0 < stop ∧ (Nn stop).firstTime = some c.i ∧ (!compact && decide ((S.lastVersionGivenDel c.i
      (bitsUnion S.lastBitmap (S.bitsOf (K (stop + 1))))).size > c.p.splitAbove)) = false) →
    ¬ (0 < stop ∧ (Nn stop).firstTime = some c.i ∧ compact = false ∧
      c.p.splitAbove < (S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf (K (stop + 1))))).size) →
    ¬ (0 < stop ∧ (Nn stop).firstTime ≠ some c.i ∧ (!compact && decide ((S.lastVersionGivenDel c.i
      (bitsUnion S.lastBitmap (S.bitsOf (K (stop + 1))))).size > c.p.splitAbove)) = false ∧
      ((Nn (stop - 1)).leaf = false → c.p.merges = true → c.p.mergeBelow ≤
        ((⟨S.leaf, (S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf (K (stop + 1))))).ks⟩ :
          KNode).liveAt c.i).length)) →
    0 < stop →
    ¬ ((Nn (stop - 1)).size + 2 ≤ c.p.M ∧
      deadOver c.p ((Nn (stop - 1)).add c.i (.key (K stop) w2.next)) = false) →
    ¬ (1 < stop ∧ (Nn (stop - 1)).firstTime = some c.i ∧
      ((Nn (stop - 1)).lastVersion c.i).size ≤ c.p.splitAbove) →
    WriterWP (handleFull stop (X stop)
        (S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf (K (stop + 1))))) compact) c
      ({ ({ w2 with trail := "up.stop-at-segment-leaf" :: w2.trail } : W) with
        trail := s :: ({ w2 with trail := "up.stop-at-segment-leaf" :: w2.trail } : W).trail } : W)
      (fun _ w' => HtInv H B c w' ∧ LiveHoleW (pre ++ [cv]) g 0 c base w')

set_option maxHeartbeats 3200000 in
/-- `UpCascSplitRest6OK` from its case left (`UpCascSplitRest7OK`): the copy below an inner
parent that the transaction made, full or compacting, split in time in place, is proved
(`writerWP_upCasc_below_copyMadeParent`, the heights by `writerWP_upCasc_below_ht`). -/
theorem upCascSplitRest6OK_of_rest7 (c : Ctx) (base : View BVal) (KO : KindOracle) (B : NodeId)
    (H : NodeId → Nat → Prop) (h : UpCascSplitRest7OK c base KO B H) : UpCascSplitRest6OK c base KO B H := by
  intro w w3 top0 pre cv rk X Nn K depth stop w2 S g compact s hvc hm hsa2 hp hvB hk hICEk hvo hkw hpos hB hbook
    hI hRO hICE hLC hJ2 hMF3 hr03 hJ3 hH3 hwf3 hlen3 hX0 hkey hrk hvis hpX hpK hlkX hXN hlinkK hne hall hleaf
    hkids hdepth hsD hbetween hstp hLE hJw2 hgeq hsl hDR hcase hlook hnsp hmt hms hmf hs0 hnroom
  by_cases hmpc : 1 < stop ∧ (Nn (stop - 1)).firstTime = some c.i ∧
      ((Nn (stop - 1)).lastVersion c.i).size ≤ c.p.splitAbove
  · obtain ⟨D, rfl⟩ : ∃ D, stop = D + 1 := ⟨stop - 1, by omega⟩
    obtain ⟨h1, hqmade, hqsz⟩ := hmpc
    have hnm : (Nn (D + 1)).firstTime ≠ some c.i := by
      intro hmade
      cases ht : (!compact && decide ((S.lastVersionGivenDel c.i
          (bitsUnion S.lastBitmap (S.bitsOf (K (D + 1 + 1))))).size > c.p.splitAbove)) with
      | false => exact hmt ⟨by omega, hmade, ht⟩
      | true =>
        simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at ht
        exact hms ⟨by omega, hmade, ht.1, ht.2⟩
    have htime : (!compact && decide ((S.lastVersionGivenDel c.i
        (bitsUnion S.lastBitmap (S.bitsOf (K (D + 1 + 1))))).size > c.p.splitAbove)) = false := by
      cases ht : (!compact && decide ((S.lastVersionGivenDel c.i
          (bitsUnion S.lastBitmap (S.bitsOf (K (D + 1 + 1))))).size > c.p.splitAbove)) with
      | false => rfl
      | true =>
        simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at ht
        exact absurd ⟨by omega, hnm, ht.1, ht.2⟩ hnsp
    have hql : (Nn D).leaf = false := by
      cases hl : (Nn D).leaf with
      | false => rfl
      | true => exact absurd ⟨by omega, hnm, htime, fun h' => by
          rw [show D + 1 - 1 = D by omega, hl] at h'; cases h'⟩ hmf
    have hJv := kdJP_note c base B top0 hB KO B hvB hk _ "up.stop-at-segment-leaf" w2 hJw2
    have hcu : CacheUnique ({ w2 with trail := "up.stop-at-segment-leaf" :: w2.trail } : W) :=
      cacheUnique_of_book hJv.1.1.book
    obtain ⟨hlinks2, hwf2⟩ := linksWf_of_book c base B top0 _ w2 hB hJv.1.1 (Or.inr ⟨_, rfl⟩)
    have hHt := writerWP_upCasc_below_ht c base hsa2 B hpos w w3 X Nn K depth D w2 _ S hI hRO hr03 hpX hpK hlkX
      hXN hlinkK hsD hX0 hLE (Or.inr ⟨_, rfl⟩) hsl hcu hlinks2 hwf2 hvo hJ3.2.1 hH3 hwf3
      (takeJ2_of_readsAs c base B w w3 hJ2 hr03) hJv.1.2.1 hgeq hJv.2 compact s
    have hL := writerWP_upCasc_below_copyMadeParent c base hvc hsa2 B hpos KO hvB hk hB top0 pre cv rk g w w3 X Nn K
      depth D w2 _ S hI hRO hr03 hLC hpX hpK hlkX hXN hlinkK hsD hX0 hLE (Or.inr ⟨_, rfl⟩) hsl hnm hlen3 hkey
      hrk hvis hleaf hstp hql (by omega) hnroom hqmade hqsz (by rw [← hgeq]; exact hlook) hcu hlinks2 hwf2 hgeq
      hJv.2 hJv compact s htime
    exact writerWP_mono (writerWP_and hHt hL) (fun _ _ h => h)
  · exact h w w3 top0 pre cv rk X Nn K depth stop w2 S g compact s hvc hm hsa2 hp hvB hk hICEk hvo hkw hpos hB
      hbook hI hRO hICE hLC hJ2 hMF3 hr03 hJ3 hH3 hwf3 hlen3 hX0 hkey hrk hvis hpX hpK hlkX hXN hlinkK hne hall
      hleaf hkids hdepth hsD hbetween hstp hLE hJw2 hgeq hsl hDR hcase hlook hnsp hmt hms hmf hs0 hnroom hmpc

/-- `UpCascSplitRest7OK` at the contexts of the runs of R. -/
def UpCascSplitRest7Runs (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts (tx : Tx), Within p (ts ++ [tx]) → R (treeRun p ts) ts.length →
    UpCascSplitRest7OK (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base
      (htOracleOf p (treeRun p ts))

/-- `UpCascCallRuns` (the premise of `delCaseLive_emptyCasc`) from the full stop node's
case left at the runs (`UpCascSplitRest7Runs`). -/
theorem upCascCallRuns_of_rest7 (p : Params) (R : Struct BVal → Time → Prop) (h : UpCascSplitRest7Runs p R) :
    UpCascCallRuns p R :=
  upCascCallRuns_of_rest6 p R (fun ts tx hw hr => upCascSplitRest6OK_of_rest7 _ _ _ _ _ (h ts tx hw hr))

end SIS.Tree
