/-
The full stop node at a space root that the transaction made (bergdb 030-01, step 6):
its split is in place, in time (the root a leaf) or in space, and leaves no hole
(`writerWP_upCasc_rootMade_H`). `upCascSplitRest4OK_of_rest5` narrows the obligation to
the copy under the fill below an inner parent (`UpCascSplitRest5OK`).
-/
import SIS.Tree.LiveUpCascTime

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

set_option maxHeartbeats 6400000 in
/-- The stop node's split at a full space root that the transaction made (stop 0), at
the split (after the bitmap's note): in place, in time (the root a leaf with fewer live
klongs, `liveEdges_root_shrink`) or in space (l4b's `writerWP_handleFull_rootSpaceMade_live`),
no hole is left; the heights as for the root not made, through the swap. -/
theorem writerWP_upCasc_rootMade_H (c : Ctx) (base : View BVal)
    (hsa2 : 2 ≤ c.p.splitAbove) (hp : MergeParamsOK c.p) (B : NodeId) (hpos : 0 < c.i)
    (w w3 : W) (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth : Nat) (w2 v : W) (S : KNode)
    (hI : PutInv c base w) (hr03 : ReadsAs c.p base w w3)
    (hLC : LiveCounts c.p (wNode c.p base w) c.i w.top.rootKey)
    (hlkX : ∀ i, i ≤ depth → w3.nodes.lookup (X i) = some (Nn i))
    (hXN : ∀ i, i ≤ depth → wNode c.p base w (X i) = some (Nn i))
    (hlinkK : ∀ i, 0 < i → i ≤ depth → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (hdepth : 0 < depth)
    (hX0 : X 0 = w.top.rootKey)
    (hLE : UpLoopEnd c B X Nn depth 0 w3 w2 S)
    (hv : v = w2 ∨ ∃ s, v = { w2 with trail := s :: w2.trail })
    (hsl : (Nn 0).leaf = true) (hmade : (Nn 0).firstTime = some c.i)
    (hcu : CacheUnique v)
    (hlinks2 : ∀ u c' z, TLink (wNode c.p base w2) c.i u c' z → z < w2.next)
    {H : NodeId → Nat → Prop} (hvo : ViewHtOK H B c) (hb3 : Book B c w3) (hi3 : HtInv H B c w3)
    (hwf3 : WriterKlongsWf w3) (hJ3 : TakeJ2 c base B w3) (hbv : Book B c v) (hghv : v.gh = w3.gh)
    (hpathv : v.path = w3.path)
    (hpX : ∀ i, i ≤ depth → (w3.path[i]?).map (·.2) = some (X i)) (compact : Bool) (s : String) :
    WriterWP (handleFull 0 (X 0) (S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf (K 1)))) compact) c
      ({ v with trail := s :: v.trail } : W)
      (fun _ w' => HtInv H B c w' ∧ LiveEdges c.p (wNode c.p base w') c.i w'.top.rootKey) := by
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
  have hE3 : LiveEdges c.p (wNode c.p base w3) c.i w3.top.rootKey := by
    rw [hr03.1, hr03.2.1]; exact edges_of_liveCounts c.p _ _ _ hLC
  obtain ⟨h2t, h2top, h2v, _, _, h2nx, h2n, hSl, hS, hSR, _, _, hfateJ2⟩ := hLE
  have hvn : v.nodes = w2.nodes := by rcases hv with rfl | ⟨s, rfl⟩ <;> rfl
  have hvt : v.taken = w2.taken := by rcases hv with rfl | ⟨s, rfl⟩ <;> rfl
  have hvtop : v.top = w2.top := by rcases hv with rfl | ⟨s, rfl⟩ <;> rfl
  have hvnx : v.next = w2.next := by rcases hv with rfl | ⟨s, rfl⟩ <;> rfl
  have hwv : wNode c.p base v = wNode c.p base w2 := by
    funext z; simp only [wNode, hvn, hvt]
  have hXs : ∀ k, 0 < k → k ≤ depth → X 0 ≠ X k :=
    fun k h1 h2 he => by have := hdist 0 k (by omega) h2 he; omega
  have hst_t : ∀ s', Klong.time s' ∈ (Nn 0).ks → s' ≤ c.i := hI.times _ _ (hXN 0 (by omega))
  have hsx : (K 1, X 1) ∈ (Nn 0).liveAt c.i := by
    have := hlinkK 1 (by omega) hdepth; simpa using this
  have hneS : bitsUnion (Nn 0).lastBitmap ((Nn 0).bitsOf (K 1)) ≠ (Nn 0).lastBitmap := by
    apply KNode.delete_bitmap_changes_of_live
    have hsx' := hsx
    rw [KNode.liveAt_of_times _ c.i hst_t] at hsx'
    exact List.mem_map.mpr ⟨_, hsx', rfl⟩
  have hswf : klongsWf (Nn 0).ks = true := hI.wf _ _ (hXN 0 (by omega))
  have hu : ∀ c', (c', X 1) ∈ (Nn 0).liveAt c.i → c' = K 1 := by
    intro c' h
    exact (hT.oneLink _ _ _ _ _ (hreach 0 (by omega)) (hreach 0 (by omega)) ⟨_, hXN 0 (by omega), h⟩
      ⟨_, hXN 0 (by omega), hsx⟩).2
  have hSf : S.shapeOf = (Nn 0).shapeOf ∧ S.leaf = (Nn 0).leaf ∧ klongsWf S.ks = true ∧
      (∀ s, Klong.time s ∈ S.ks → s ≤ c.i) ∧
      ∀ c' z, ((c', z) ∈ S.liveAt c.i ∧ c' ≠ K 1) ↔ ((c', z) ∈ (Nn 0).liveAt c.i ∧ c' ≠ K 1) := by
    rcases hS with rfl | ⟨ti, dst, rfl⟩
    · exact ⟨rfl, rfl, hswf, hst_t, fun _ _ => Iff.rfl⟩
    · exact ⟨KNode.retarget_shapeOf _ _ _ _, rfl, by rw [klongsWf_retargetKlongs]; exact hswf,
        KNode.retarget_times _ _ _ _ _ hst_t, KNode.retarget_liveAt_ne _ _ _ _ _ _ hu⟩
  obtain ⟨hSsh, hSleaf, hSwf, hSt, hSlive⟩ := hSf
  have hneS' : bitsUnion S.lastBitmap (S.bitsOf (K 1)) ≠ S.lastBitmap := by
    rw [KNode.lastBitmap_of_shapeOf hSsh, KNode.bitsOf_of_shapeOf hSsh]; exact hneS
  have hlkv : v.nodes.lookup (X 0) = some S := by rw [hvn]; exact hSl
  have htk2 : w2.taken.contains (X 0) = false := by rw [h2t _ hXs]; exact htk3 0 (by omega)
  have hagree2 : ∀ u, u ≠ X 0 → (∀ i, 0 < i → i ≤ depth → u ≠ X i) →
      wNode c.p base w2 u = wNode c.p base w3 u := fun u hus hnc => by
    simp only [wNode, h2t u hnc, h2n u hus hnc]
  have hSl1 : S.leaf = true := hSleaf.trans hsl
  -- the halves of a space split of the last version without the chain's klong
  have hH := delLast_halves S c.i (K 1) c.p.splitAbove hSl1 hsa2
  have hHO := halves_del_halfOK c.p hp S c.i (bitsUnion S.lastBitmap (S.bitsOf (K 1)))
  have hflat := KNode.lastVersionGivenDel_flatAt S c.i (bitsUnion S.lastBitmap (S.bitsOf (K 1)))
  have hord := KNode.lastVersionGivenDel_order S c.i (bitsUnion S.lastBitmap (S.bitsOf (K 1)))
  generalize hlast : S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf (K 1))) = last
    at hH hHO hflat hord ⊢
  obtain ⟨hleq, _, hltm, _, _, _, hiff, _⟩ := delLast_split_facts c S (K 1) hsa2 hSt last hlast
  have hliveL : ∀ c' z, (c', z) ∈ (⟨S.leaf, last.ks⟩ : KNode).liveAt c.i ↔
      (c', z) ∈ (Nn 0).liveAt c.i ∧ c' ≠ K 1 := by
    intro c' z; rw [hleq, hiff c' z]; exact hSlive c' z
  have hlk' : ({ v with trail := s :: v.trail } : W).nodes.lookup (X 0) = some S := hlkv
  have htk' : ({ v with trail := s :: v.trail } : W).taken.contains (X 0) = false := by
    show v.taken.contains _ = false; rw [hvt]; exact htk2
  have hroot' : ({ v with trail := s :: v.trail } : W).top.rootKey = w3.top.rootKey := by
    show v.top.rootKey = _; rw [hvtop, h2top]
  have hrk' : ({ v with trail := s :: v.trail } : W).top.rootKey = X 0 := by
    rw [hroot', hr03.2.1, hX0]
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
      rw [hvn, h2n z (hzX 0 (by omega)) (fun i _ hi => hzX i hi)]
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
  -- the stop node with its bitmap, S', and the state u with it
  have hft0 : ∃ s0, (Nn 0).firstTime = some s0 := by
    obtain ⟨s0, h1, _⟩ := KNode.firstTime_some_of_live (Nn 0) c.i hswf _ _ hsx
    exact ⟨s0, h1⟩
  generalize hS'd : S.add c.i (.del (bitsUnion S.lastBitmap (S.bitsOf (K 1)))) = S'
  have hbm : BitmapOf S S' c.i (K 1) := Or.inl hS'd.symm
  have hS'leaf : S'.leaf = S.leaf := bitmapOf_leaf S S' c.i (K 1) hbm
  have hS't : ∀ s, Klong.time s ∈ S'.ks → s ≤ c.i := by
    rw [← hS'd]; exact KNode.add_times S c.i _ (fun s h => by cases h) hSt
  have hS'live : ∀ c' z, (c', z) ∈ S'.liveAt c.i ↔ (c', z) ∈ (Nn 0).liveAt c.i ∧ c' ≠ K 1 := by
    intro c' z
    rw [liveAt_iff_of_delete_lookup S S' c.i (K 1) hSt hS't
      (fun c' => by rw [← hS'd]; exact S.add_delete_live_lookup c.i (K 1) c')]
    exact hSlive c' z
  have hft : S.firstTime = S'.firstTime := by
    obtain ⟨s0, hs0⟩ := hft0
    rw [← KNode.firstTime_of_shapeOf hSsh] at hs0
    rw [hs0, bitmapOf_firstTime S S' c.i _ hbm s0 hs0]
  have hprev : S.toPrev (c.i - 1) = S'.toPrev (c.i - 1) := by
    show (⟨S.leaf, prefixAt S.ks (c.i - 1)⟩ : KNode) = ⟨S'.leaf, prefixAt S'.ks (c.i - 1)⟩
    rw [hS'leaf, bitmapOf_prefix S S' c.i _ hbm hpos]
  generalize hud : setX (X 0) S' ({ v with trail := s :: v.trail } : W) = u
  have hlku : u.nodes.lookup (X 0) = some S' := by rw [← hud]; exact lookup_setX_self _ _ _
  have htku : u.taken.contains (X 0) = false := by rw [← hud]; exact htk'
  have hrku : u.top.rootKey = X 0 := by rw [← hud]; exact hrk'
  have hrootu : u.top.rootKey = w3.top.rootKey := by rw [← hud]; exact hroot'
  have hnxu : u.next = w3.next := by rw [← hud]; exact hnx'
  have hwu : wNode c.p base u = updN (wNode c.p base ({ v with trail := s :: v.trail } : W)) (X 0) S' := by
    rw [← hud]; exact wNode_upsert_updN c.p base _ _ (X 0) S' rfl rfl htk'
  have hsnu : wNode c.p base u (X 0) = some S' := by rw [hwu]; exact updN_self _ _ _
  have hagreeU : ∀ u0, u0 ≠ X 0 → (∀ i, 0 < i → i ≤ depth → u0 ≠ X i) →
      wNode c.p base u u0 = wNode c.p base w3 u0 := fun u0 hus hnc => by
    rw [hwu, updN_ne _ _ _ _ hus, hwv']; exact hagree2 u0 hus hnc
  -- the tree with S'
  have hTu : TreeOK (wNode c.p base u) c.i u.top.rootKey := by
    rw [hrootu]
    exact treeOK_up_tr (wNode c.p base w3) _ c.i w3.top.rootKey X Nn K 0 depth hdepth hT3
      (hreach3 0 (by omega)) (fun i _ hi => hN3 i hi) (fun i h1 hi => hlinkK i h1 hi)
      (fun i i' _ hi _ hi' he => hdist i i' hi hi' he) hagreeU _ hsnu id
      (fun c' z h => ⟨c', ((hS'live c' z).mp h).1, ((hS'live c' z).mp h).2, rfl⟩)
  have hTu0 : TreeOK (wNode c.p base u) c.i (X 0) := by rw [← hrku]; exact hTu
  -- the heights at u: the walk's start's, through the loop's frame
  have hbu : Book B c u := by
    have hbv' : Book B c ({ v with trail := s :: v.trail } : W) :=
      ⟨hbv.next, hbv.ids, hbv.bound, hbv.nodup, hbv.leaf, hbv.tag, hbv.taken, hbv.top⟩
    have h := book_putNode B (X 0) S' c ({ v with trail := s :: v.trail } : W) hbv' ⟨S, hlk', hS'leaf⟩
    exact (h () u (by rw [← hud]; rfl)).1
  have hghu : u.gh = w3.gh := by rw [← hud]; exact hghv
  have hpathu : u.path = w3.path := by rw [← hud]; exact hpathv
  have htu : ∀ y, (∀ k, 0 < k → k ≤ depth → y ≠ X k) → u.taken.contains y = w3.taken.contains y := by
    intro y hy
    rw [← hud]; show v.taken.contains y = _; rw [hvt]; exact h2t y hy
  have htopu : u.top = w3.top := by rw [← hud]; show v.top = _; rw [hvtop]; exact h2top
  have hnodesu : ∀ y, y ≠ X 0 → (∀ k, 0 < k → k ≤ depth → y ≠ X k) → u.nodes.lookup y = w3.nodes.lookup y := by
    intro y h1 h2
    rw [← hud]; simp only [setX, lookup_upsert, h1, ↓reduceIte]
    show v.nodes.lookup y = _; rw [hvn]; exact h2n y h1 h2
  have hfJu : ∀ k, 0 < k → k ≤ depth → ChainFateW c.i B u (Nn k) (X k) := by
    intro k h1 h2
    refine chainFateW_frame c.i B w2 u (Nn k) (X k) (hfateJ2 k h1 h2) ?_ ?_
    · rw [← hud]; show v.taken = _; exact hvt
    · rw [← hud]; simp only [setX, lookup_upsert, Ne.symm (hXs k h1 h2), ↓reduceIte]
      show v.nodes.lookup _ = _; rw [hvn]
  have hX03 : X 0 = w3.top.rootKey := by rw [hr03.2.1, hX0]
  have hiu : HtInv H B c u :=
    htInv_upFrame B c base w3 u X Nn K depth 0 hpos hb3 hi3 hwf3 hbu (fun e he => by rw [hghu]; exact he)
      hpathu hJ3 hT3 (fun q qn hq s' hs' => by rw [hr03.1] at hq; exact hI.times q qn hq s' hs') hdepth hX03 hlkX
      htk3 hdist hreach3 hlinkK htu htopu hnodesu S' hlku hS't hS'live hfJu ⟨S, hSR, hbm⟩
  obtain ⟨g0, h0, hm0⟩ := kd_tag_of_lookup hb3 (hlkX 0 (by omega))
  have hh0 : h0 = 0 := kd_h0 hb3 (hlkX 0 (by omega)) hm0 hsl
  subst hh0
  have hxu : (X 0, g0, 0) ∈ u.gh := by rw [hghu]; exact hm0
  obtain ⟨a, hpx⟩ : ∃ a, u.path[0]? = some (a, X 0) := by
    have h := hpX 0 (by omega)
    rw [← hpathu] at h
    cases hp0 : u.path[0]? with
    | none => rw [hp0] at h; cases h
    | some e =>
      rw [hp0] at h
      simp only [Option.map_some, Option.some.injEq] at h
      exact ⟨e.1, by rw [← h]⟩
  have hpf : PathFreeTo u (0 + 1) := by
    intro d a' q hd hq
    have hd0 : d = 0 := by omega
    subst hd0
    rw [hpx] at hq
    cases hq
    exact htku
  have hNu : NodeHt c H u 0 S' := ht_cache_at hlku hiu hxu htku (HtLe.refl u)
  have hlastK : kdKs (HtP c H u 0) last.ks := by
    intro c' y hm
    have hl0 := ht_flat_live hord hm
    have hl1 : (c', y) ∈ (⟨S.leaf, last.ks⟩ : KNode).liveAt c.i := by
      rw [hleq, KNode.liveAt_of_times _ c.i hltm]; exact hl0
    have hl2 := (hS'live c' y).mpr ((hliveL c' y).mp hl1)
    rw [KNode.liveAt_of_times _ c.i hS't] at hl2
    exact ⟨(hNu.live c' y hl2).1, fun h => absurd rfl h⟩
  have hmainH : WriterWP (handleFullWith rootUp 0 (X 0) [] last compact) c u (fun _ w' => HtInv H B c w') :=
    writerWP_mono (ht_handleFull B 0 (X 0) last compact c u hvo hpos hbu hiu g0 0 hxu a hpx hpf hflat hlastK)
      (fun _ _ h => h.2.1)
  -- the live counts with S': the start's without the chain, the root a leaf
  have hLu : LiveEdges c.p (wNode c.p base u) c.i (X 0) := by
    by_cases hE : S'.liveAt c.i = []
    · exact liveEdges_emptyRoot c.p _ c.i (X 0) S' hsnu (by rw [hS'leaf]; exact hSl1) hE
    · have hroot3 : w3.top.rootKey = X 0 := by rw [hr03.2.1, hX0]
      have hHl := liveEdgesH_up c.p (wNode c.p base w3) (wNode c.p base u) c.i w3.top.rootKey X Nn K 0 depth
        hdepth hT3 (hreach3 0 (by omega)) (fun i _ hi => hN3 i hi) (fun i h1 hi => hlinkK i h1 hi)
        (fun i i' _ hi _ hi' he => hdist i i' hi hi' he) hagreeU S' hsnu (by rw [hS'leaf, hSleaf])
        (fun c' z h => (hS'live c' z).mp h) hE hE3
      rw [hroot3] at hHl
      refine liveEdges_of_liveEdgesH c.p _ c.i (X 0) _ hHl ?_ ?_
      · intro rn hrn _ hl
        rw [hsnu] at hrn
        cases hrn
        rw [hS'leaf, hSl1] at hl
        cases hl
      · intro u0 un c' y yn hu0 hun hc _ hy
        subst hy
        exact absurd ⟨un, hun, hc⟩ (hTu0.rootFree u0 c' hu0)
  have hX0n : X 0 < u.next := by rw [hnxu]; exact hXlt 0 (by omega)
  have hfree : ∀ z, u.next ≤ z → wNode c.p base u z = none ∧ u.nodes.lookup z = none ∧
      u.taken.contains z = false := by
    intro z hz
    have hz' : ({ v with trail := s :: v.trail } : W).next ≤ z := by rw [hnx', ← hnxu]; exact hz
    obtain ⟨h1, h2, h3⟩ := hS5 z hz'
    have hz0 : z ≠ X 0 := fun he => by have := hXlt 0 (by omega); rw [← hnxu] at this; omega
    have h1u : u.nodes.lookup z = none := by
      rw [← hud]; simp only [setX, lookup_upsert, hz0, ↓reduceIte]; exact h1
    have h2u : u.taken.contains z = false := by rw [← hud]; exact h2
    refine ⟨?_, h1u, h2u⟩
    simp only [wNode, h2u, Bool.false_eq_true, ↓reduceIte, h1u]
    exact h3
  have hlinks : ∀ a c' z, TReach (wNode c.p base u) c.i (X 0) a → TLink (wNode c.p base u) c.i a c' z →
      z < u.next := by
    intro a c' z _ hl
    obtain ⟨an, han, hl⟩ := hl
    rw [hnxu]
    by_cases ha : a = X 0
    · rw [ha, hsnu] at han; cases han
      rw [hr03.2.2.2.2]
      exact hI.links (X 0) (Nn 0) c' z (tReach_reachS _ _ _ _ (hreach 0 (by omega))) (hXN 0 (by omega))
        ((hS'live c' z).mp hl).1
    · rw [hwu, updN_ne _ _ _ _ ha] at han
      rw [← hnx']; exact hS6 a c' z ⟨an, han, hl⟩
  have hsubL : ∀ c' z, (c', z) ∈ (⟨S'.leaf, last.ks⟩ : KNode).liveAt c.i → (c', z) ∈ S'.liveAt c.i := by
    intro c' z h
    rw [hS'leaf] at h
    exact (hS'live c' z).mpr ((hliveL c' z).mp h)
  have hhalves : c.p.splitAbove < last.size → 0 < (halves S'.leaf c.i last []).2.2 ∧
      (∀ c' z, (c', z) ∈ (halves S'.leaf c.i last []).1.liveAt c.i →
        c' < (halves S'.leaf c.i last []).2.2 ∧ (c', z) ∈ (⟨S'.leaf, last.ks⟩ : KNode).liveAt c.i) ∧
      (∀ c' z, (c', z) ∈ (halves S'.leaf c.i last []).2.1.liveAt c.i →
        ∃ c0, (halves S'.leaf c.i last []).2.2 ≤ c0 ∧
          c' = splitLocalCv S'.leaf (halves S'.leaf c.i last []).2.2 c0 ∧
          (c0, z) ∈ (⟨S'.leaf, last.ks⟩ : KNode).liveAt c.i) ∧
      HalfOK c.p c.i (halves S'.leaf c.i last []).1 ∧ HalfOK c.p c.i (halves S'.leaf c.i last []).2.1 := by
    intro hsp
    rw [hS'leaf]
    obtain ⟨r, hr0, _, hdiv, hfh, hsh⟩ := hH hsp
    obtain ⟨hfH, hsH⟩ := hHO hsp
    refine ⟨by rw [hdiv]; exact hr0, fun c' z h => ?_, fun c' z h => ?_, hfH, hsH⟩
    · obtain ⟨h1, h2⟩ := hfh c' z h
      exact ⟨by rw [hdiv]; exact h1, h2⟩
    · obtain ⟨c0, h1, h2, h3⟩ := hsh c' z h
      exact ⟨c0, by rw [hdiv]; exact h1, by rw [hdiv]; exact h2, h3⟩
  have hmade' : S'.firstTime = some c.i := by rw [← hft, KNode.firstTime_of_shapeOf hSsh]; exact hmade
  have hmainL : WriterWP (handleFullWith rootUp 0 (X 0) [] last compact) c u
      (fun _ w' => LiveEdges c.p (wNode c.p base w') c.i w'.top.rootKey) := by
    cases hcs : (!compact && decide (last.size > c.p.splitAbove)) with
    | false =>
      refine writerWP_mono (writerWP_handleFullWith_timeInPlace_nodesL rootUp 0 (X 0) S' last compact c u hlku
        hmade' hcs (fun e q he _ => by omega)) ?_
      rintro _ wf ⟨hfn, hft', hftop, _, _⟩
      rw [wNode_upsert_updN c.p base u wf (X 0) _ hfn hft' htku, hftop, hrku]
      exact liveEdges_root_shrink c.p (wNode c.p base u) c.i (X 0) S' ⟨S'.leaf, last.ks⟩ hTu0 hsnu rfl
        (by rw [hS'leaf]; exact hSl1) hsubL hLu
    | true =>
      have h' := hcs
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h'
      obtain ⟨hc, hsp⟩ := h'
      subst hc
      exact writerWP_handleFull_rootSpaceMade_live rootUp (X 0) S' last c base u hlku htku hmade' hsp hX0n hfree
        hlinks hTu0 hsubL hhalves hLu
  have hmain := writerWP_and hmainH hmainL
  have h2 := writerWP_handleFullWith_root_swap rootUp (X 0) S' S last compact c u _ hlku hX0n hft
    hS'leaf.symm (fun _ => hprev) hmain
  rw [← hud, setX_setX,
    setX_self _ _ _ (show CacheUnique ({ v with trail := s :: v.trail } : W) from hcu) hlk'] at h2
  exact h2


/-- The full stop node's case left (bergdb 030-01, step 6): a stop node below the space
root, not made by the transaction, split in time, whose copy is under the fill below an
inner parent: the hole at the copy, below a parent with room or with the cascade. -/
def UpCascSplitRest5OK (c : Ctx) (base : View BVal) (KO : KindOracle) (B : NodeId)
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
    WriterWP (handleFull stop (X stop)
        (S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf (K (stop + 1))))) compact) c
      ({ ({ w2 with trail := "up.stop-at-segment-leaf" :: w2.trail } : W) with
        trail := s :: ({ w2 with trail := "up.stop-at-segment-leaf" :: w2.trail } : W).trail } : W)
      (fun _ w' => HtInv H B c w' ∧ LiveHoleW (pre ++ [cv]) g 0 c base w')

set_option maxHeartbeats 3200000 in
/-- `UpCascSplitRest4OK` from its case left (`UpCascSplitRest5OK`): a space root made by
the transaction is proved (`writerWP_upCasc_rootMade_H`). -/
theorem upCascSplitRest4OK_of_rest5 (c : Ctx) (base : View BVal) (KO : KindOracle) (B : NodeId)
    (H : NodeId → Nat → Prop) (h : UpCascSplitRest5OK c base KO B H) : UpCascSplitRest4OK c base KO B H := by
  intro w w3 top0 pre cv rk X Nn K depth stop w2 S g compact s hvc hm hsa2 hp hvB hk hICEk hvo hkw hpos hB hbook
    hI hRO hICE hLC hJ2 hMF3 hr03 hJ3 hH3 hwf3 hlen3 hX0 hkey hrk hvis hpX hpK hlkX hXN hlinkK hne hall hleaf
    hkids hdepth hsD hbetween hstp hLE hJw2 hgeq hsl hDR hcase hlook hnsp hmt hms hmf
  rcases Nat.eq_zero_or_pos stop with hs0 | hs0
  · subst hs0
    have hmade : (Nn 0).firstTime = some c.i := hcase.resolve_left (by omega)
    have hJv := kdJP_note c base B top0 hB KO B hvB hk _ "up.stop-at-segment-leaf" w2 hJw2
    have hcu : CacheUnique ({ w2 with trail := "up.stop-at-segment-leaf" :: w2.trail } : W) :=
      cacheUnique_of_book hJv.1.1.book
    obtain ⟨hlinks2, _⟩ := linksWf_of_book c base B top0 _ w2 hB hJv.1.1 (Or.inr ⟨_, rfl⟩)
    refine writerWP_mono (writerWP_upCasc_rootMade_H c base hsa2 hp B hpos w w3 X Nn K depth w2 _ S hI hr03 hLC
      hlkX hXN hlinkK hdepth hX0 hLE (Or.inr ⟨_, rfl⟩) hsl hmade hcu hlinks2 hvo hJ3.2.1 hH3 hwf3
      (takeJ2_of_readsAs c base B w w3 hJ2 hr03) hJv.1.2.1 hgeq hJv.2 hpX compact s) ?_
    rintro _ w' ⟨hHt, hE⟩
    exact ⟨hHt, liveEdgesH_of_liveEdges _ _ _ _ _ hE⟩
  · exact h w w3 top0 pre cv rk X Nn K depth stop w2 S g compact s hvc hm hsa2 hp hvB hk hICEk hvo hkw hpos hB
      hbook hI hRO hICE hLC hJ2 hMF3 hr03 hJ3 hH3 hwf3 hlen3 hX0 hkey hrk hvis hpX hpK hlkX hXN hlinkK hne hall
      hleaf hkids hdepth hsD hbetween hstp hLE hJw2 hgeq hsl hDR hcase hlook hnsp hmt hms hmf hs0

/-- `UpCascSplitRest5OK` at the contexts of the runs of R. -/
def UpCascSplitRest5Runs (p : Params) (R : Struct BVal → Time → Prop) : Prop :=
  ∀ ts (tx : Tx), Within p (ts ++ [tx]) → R (treeRun p ts) ts.length →
    UpCascSplitRest5OK (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base
      (htOracleOf p (treeRun p ts))

/-- `UpCascCallRuns` (the premise of `delCaseLive_emptyCasc`) from the full stop node's
case left at the runs (`UpCascSplitRest5Runs`). -/
theorem upCascCallRuns_of_rest5 (p : Params) (R : Struct BVal → Time → Prop) (h : UpCascSplitRest5Runs p R) :
    UpCascCallRuns p R :=
  upCascCallRuns_of_rest4 p R (fun ts tx hw hr => upCascSplitRest4OK_of_rest5 _ _ _ _ _ (h ts tx hw hr))

end SIS.Tree
