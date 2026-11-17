/-
The upward delete whose stop node is the space root (bergdb 030-01, step 6): the
climb reaches the space root, a segment leaf, which gets its bitmap if it has room
or splits if it is full. Either way no node is left under the fill: the tree after
the bitmap is the start's without the chain (`liveEdgesH_up`), whose only hole is
the root, a leaf, which asks no count; the root's split (`writerWP_handleFull_root_live`,
LiveDelRoot.lean) is applied at the state whose root has its bitmap as if it had
room, and moved to the writer's state by the swap (`writerWP_handleFullWith_root_swap`),
as the tree's `writerWP_upCasc_root_j2S` (StopSwapRoot.lean) does. So the merges'
loop merges nothing (`writerWP_afterDelete_none`) and the delete keeps the live
counts with no premise and no heights.
-/
import SIS.Tree.LiveUpCascWalk
import SIS.Tree.StopSwapRoot
import SIS.Tree.LiveDelRoot
import SIS.Tree.LiveUpRoomH
import SIS.Tree.LiveNoMerge
import SIS.Tree.StratumCasc

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

set_option maxHeartbeats 6400000 in
/-- The stop node's bitmap into a full space root that the transaction did not
make (stop 0): from the state after the upward loop, the live counts hold after
the root's split. The split is applied at the state whose root has its bitmap
(S'), whose tree is the start's without the chain, and moved to the writer's state
by `writerWP_handleFullWith_root_swap`. -/
theorem writerWP_upCasc_root_live (c : Ctx) (base : View BVal)
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
    (hsl : (Nn 0).leaf = true) (hnm : (Nn 0).firstTime ≠ some c.i)
    (hfull : ¬ DelRoom c (K 1) S)
    (hcu : CacheUnique v)
    (hlinks2 : ∀ u c' z, TLink (wNode c.p base w2) c.i u c' z → z < w2.next) :
    WriterWP (appendDeleteKlong (X 0) 0 (K 1)) c v
      (fun _ w' => LiveEdges c.p (wNode c.p base w') c.i w'.top.rootKey) := by
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
  obtain ⟨h2t, h2top, h2v, _, _, h2nx, h2n, hSl, hS, _, _, _, _⟩ := hLE
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
  refine writerWP_appendDeleteKlong_full_of (X 0) 0 (K 1) S c v hlkv hneS' hfull _ ?_
  intro compact s
  -- the halves of a space split of the last version without the chain's klong
  have hH := delLast_halves S c.i (K 1) c.p.splitAbove hSl1 hsa2
  have hHO := halves_del_halfOK c.p hp S c.i (bitsUnion S.lastBitmap (S.bitsOf (K 1)))
  generalize hlast : S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf (K 1))) = last at hH hHO ⊢
  obtain ⟨hleq, _, _, _, _, _, hiff, _⟩ := delLast_split_facts c S (K 1) hsa2 hSt last hlast
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
  have hmain : WriterWP (handleFullWith rootUp 0 (X 0) [] last compact) c u
      (fun _ w' => LiveEdges c.p (wNode c.p base w') c.i w'.top.rootKey) := by
    refine writerWP_handleFull_root_live rootUp (X 0) S' last compact c base u hlku htku
      (by rw [hS'leaf]; exact hSl1) (by rw [← hft, KNode.firstTime_of_shapeOf hSsh]; exact hnm) hX0n
      ?_ ?_ hTu0 ?_ ?_ hLu
    · intro z hz
      have hz' : ({ v with trail := s :: v.trail } : W).next ≤ z := by rw [hnx', ← hnxu]; exact hz
      obtain ⟨h1, h2, h3⟩ := hS5 z hz'
      have hz0 : z ≠ X 0 := fun he => by have := hXlt 0 (by omega); rw [← hnxu] at this; omega
      have h1u : u.nodes.lookup z = none := by
        rw [← hud]; simp only [setX, lookup_upsert, hz0, ↓reduceIte]; exact h1
      have h2u : u.taken.contains z = false := by rw [← hud]; exact h2
      refine ⟨?_, h1u, h2u⟩
      simp only [wNode, h2u, Bool.false_eq_true, ↓reduceIte, h1u]
      exact h3
    · intro a c' z _ hl
      obtain ⟨an, han, hl⟩ := hl
      rw [hnxu]
      by_cases ha : a = X 0
      · rw [ha, hsnu] at han; cases han
        rw [hr03.2.2.2.2]
        exact hI.links (X 0) (Nn 0) c' z (tReach_reachS _ _ _ _ (hreach 0 (by omega))) (hXN 0 (by omega))
          ((hS'live c' z).mp hl).1
      · rw [hwu, updN_ne _ _ _ _ ha] at han
        rw [← hnx']; exact hS6 a c' z ⟨an, han, hl⟩
    · intro c' z h
      rw [hS'leaf] at h
      exact (hS'live c' z).mpr ((hliveL c' z).mp h)
    · intro hsp
      rw [hS'leaf]
      obtain ⟨r, hr0, _, hdiv, hfh, hsh⟩ := hH hsp
      obtain ⟨hfH, hsH⟩ := hHO hsp
      refine ⟨by rw [hdiv]; exact hr0, fun c' z h => ?_, fun c' z h => ?_, hfH, hsH⟩
      · obtain ⟨h1, h2⟩ := hfh c' z h
        exact ⟨by rw [hdiv]; exact h1, h2⟩
      · obtain ⟨c0, h1, h2, h3⟩ := hsh c' z h
        exact ⟨c0, by rw [hdiv]; exact h1, by rw [hdiv]; exact h2, h3⟩
  have h2 := writerWP_handleFullWith_root_swap rootUp (X 0) S' S last compact c u _ hlku hX0n hft
    hS'leaf.symm (fun _ => hprev) hmain
  rw [← hud, setX_setX,
    setX_self _ _ _ (show CacheUnique ({ v with trail := s :: v.trail } : W) from hcu) hlk'] at h2
  exact h2


/-- The upward delete's climb from the leaf L (node n) reaches the space root:
every node strictly between the space root and L on the path to L empties with the
delete, and the space root was not made by the transaction. -/
def UpToRoot (c : Ctx) (base : View BVal) (w : W) (L : NodeId) (n : KNode) : Prop :=
  ∀ P, LinkedFrom (wNode c.p base w) c.i w.top.rootKey P → nodeAt w.top.rootKey P P.length = L →
    (∀ i, 0 < i → i < P.length →
      ((wNode c.p base w (nodeAt w.top.rootKey P i)).getD n).allKeysIn
        (bitsUnion ((wNode c.p base w (nodeAt w.top.rootKey P i)).getD n).lastBitmap
          (((wNode c.p base w (nodeAt w.top.rootKey P i)).getD n).bitsOf
            (((P[i + 1 - 1]?).bind (·.1)).getD 0))) = true) ∧
    ((wNode c.p base w (nodeAt w.top.rootKey P 0)).getD n).firstTime ≠ some c.i

set_option maxHeartbeats 3200000 in
/-- The delete that empties its leaf, not the space root, whose climb reaches the
space root (`UpToRoot`), the merges on, from the first stratum's start with the live
counts: the space root, a segment leaf, gets its bitmap or splits, and no node is left
under the fill, so `afterDelete` merges nothing (`writerWP_afterDelete_none`) and the
delete ends with the live counts. The walk is the stratum's
(`writerWP_del_emptyAnyMJKT`) over `takeJ2_deleteUpward_stepMBKGDS`; the split's tree
facts by `upCascJ2OKT_holds`, its live counts by `writerWP_upCasc_root_live`. -/
theorem writerWP_del_upRootLive (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
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
      n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = true ∧ L ≠ w.top.rootKey ∧
      UpToRoot c base w L n)
    (hLC : LiveCounts c.p (wNode c.p base w) c.i w.top.rootKey)
    (hsa2 : 2 ≤ c.p.splitAbove) (hp : MergeParamsOK c.p) (hICEk : ICEFromKinds c base KO B)
    (hm : c.p.merges = true) (hpos : 0 < c.i)
    (hJ2 : TakeJ2 c base B w) (hMF : ∀ x o, w.madeFor.lookup x = some o → o < B)
    (hLV : ∀ L n, (L, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk →
      wNode c.p base w L = some n → n.leaf = true → ∀ y, (cv, y) ∈ n.liveAt c.i →
      wNode c.p base w y = none) :
    WriterWP (putKv (.del (pre ++ [cv]))) c w (fun _ w' =>
      LiveEdges c.p (wNode c.p base w') c.i w'.top.rootKey) := by
  have hfuel : 1 ≤ c.p.fuel := by unfold Params.fuel; omega
  refine writerWP_del_toLeafMK c base hvc pre cv rk w (fun v => KdJ c B top0 KO B v ∧ v.madeFor = w.madeFor)
    ⟨⟨hbook, hb0, hi0⟩, rfl⟩
    (fun s f x v hJ hx => writerWP_mono (writerWP_and (kdJ_descendLte c base B top0 hB KO B hvB hk s f x v hJ.1 hx)
      (writerWP_descendLte_madeFor s c f x v)) (fun _ v' h => ⟨h.1, h.2.trans hJ.2⟩))
    (fun s x L n v hJ hL hlk hkm => ⟨kdJ_pathAdd c base B top0 hB KO B hvB s x L n v hJ.1 hL hlk hkm, hJ.2⟩)
    ⟨kdJ_start c base B top0 hB KO B hvB w ⟨hbook, hb0, hi0⟩, rfl⟩ hrk (hI.pathUntaken _) hI.wf
    _ (fun v hv => by
      unfold fresh
      simp only [writerWP_bind, writerWP_get, writerWP_set, writerWP_pure]
      exact hv) ?_
  intro L n P w3 hL hn hnl hr03 hJ3 hlk3 hp3' hlinkP hXD hlkX
  have hb3 := hJ3.1
  have hlen3 : w3.path.length = P.length + 1 := by rw [hp3']; simp
  have hMF3 : ∀ x o, w3.madeFor.lookup x = some o → o < B := by rw [hJ3.2]; exact hMF
  have hJ23 : TakeJ2 c base B w3 := takeJ2_of_readsAs c base B w w3 hJ2 hr03
  obtain ⟨hne, hall, hLr, hUp⟩ := hleafC L n hL hn hnl
  have hUpP := hUp P hlinkP hXD
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
  · -- the space root with room: its bitmap; no hole, the root a leaf
    intro stop w' sn' hsD hbetween ht htop hv hnodes hsn' hsl' hsw' hst' hlive' _ _ _ _ _ _ hb'G hstp gs hs _
    have hs0 : stop = 0 := by
      rcases Nat.eq_zero_or_pos stop with h0 | h0
      · exact h0
      · exact (hstp (hUpP.1 stop h0 hsD)).1
    subst hs0
    have hb' := hb'G.1
    obtain ⟨hagree, hsnw⟩ := hfr 0 w' sn' hsD ht hnodes hsn'
    have hRO' : RangeOrder (wNode c.p base w') c.i w'.top.rootKey := by
      rw [htop]
      exact rangeOrder_up_bitmap (wNode c.p base w3) (wNode c.p base w') c.i w3.top.rootKey _ _ _ 0
        P.length hsD hR3 hT3 (hreach3 0 (by omega)) (fun i _ h2 => hN3 i h2)
        (fun i h1 h2 => hlinkK i (by omega) h2) (fun i i' _ h2 _ h4 he => hdistP i i' h2 h4 he)
        hagree sn' hsnw hsl' (fun c' z h => (hlive' c' z).mp h)
    have hDv := hD 0 w' sn' id hsD ht htop hv hnodes hsn' hsl' hsw' hst'
      (fun c' z h => ⟨c', ((hlive' c' z).mp h).1, ((hlive' c' z).mp h).2, rfl⟩) hRO' hb'.1.1 hb'.1.2.1 hb'.1.2.2
    cases hsl0 : ((wNode c.p base w (nodeAt w.top.rootKey P 0)).getD n).leaf with
    | false => exact (lebStop_false c base w hLC hm hI (fun i => nodeAt w.top.rootKey P i)
      (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
      (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length 0 cv (by simp [nodeAt]) hXN hlinkK hall'
      hsD hbetween hsl0).elim
    | true =>
    have hX0' : nodeAt w.top.rootKey P 0 = w.top.rootKey := by simp [nodeAt]
    have hroot' : w'.top.rootKey = w.top.rootKey := by rw [htop, hr03.2.1]
    have hsnw0 : wNode c.p base w' w.top.rootKey = some sn' := by rw [← hX0']; exact hsnw
    have hsn'l : sn'.leaf = true := by rw [hsl']; exact hsl0
    have hTw' : TreeOK (wNode c.p base w') c.i w.top.rootKey := by rw [← hroot']; exact hDv.1.tree
    have hagree' : ∀ u, u ≠ nodeAt w.top.rootKey P 0 →
        (∀ i, 0 < i → i ≤ P.length → u ≠ nodeAt w.top.rootKey P i) →
        wNode c.p base w' u = wNode c.p base w u := by
      intro u h1 h2; rw [hagree u h1 h2, hr03.1]
    have hE' : LiveEdges c.p (wNode c.p base w') c.i w'.top.rootKey := by
      rw [hroot']
      by_cases hE : sn'.liveAt c.i = []
      · exact liveEdges_emptyRoot c.p _ c.i _ sn' hsnw0 hsn'l hE
      · have hHl := liveEdgesH_up c.p (wNode c.p base w) (wNode c.p base w') c.i w.top.rootKey
          (fun i => nodeAt w.top.rootKey P i)
          (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
          (fun i => ((P[i - 1]?).bind (·.1)).getD 0) 0 P.length hsD hI.tree (hreachX 0 (by omega))
          (fun i _ h2 => hXN i h2) (fun i h1 h2 => hlinkK i (by omega) h2)
          (fun i i' _ h2 _ h4 he => hdistP i i' h2 h4 he) hagree' sn' hsnw hsl'
          (fun c' z h => (hlive' c' z).mp h) hE (edges_of_liveCounts c.p _ _ _ hLC)
        refine liveEdges_of_liveEdgesH c.p _ c.i _ _ hHl ?_ ?_
        · intro rn hrn _ hl
          rw [hsnw0] at hrn
          cases hrn
          rw [hsn'l] at hl
          cases hl
        · intro u0 un c' y yn hu0 hun hc _ hy
          have hy' : y = w.top.rootKey := by rw [hy, hX0']
          rw [hy'] at hc
          exact absurd ⟨un, hun, hc⟩ (hTw'.rootFree u0 c' hu0)
    have hPI := hDv.1
    refine writerWP_mono (writerWP_afterDelete_none (pre ++ [cv]) gs hs c base hvc w'
      (fun y hy => hPI.untaken y (tReach_reachS _ _ _ _ hy)) (fun y yn _ h => hPI.wf y yn h) hPI.times
      (liveCounts_of_edges c.p _ _ _ hE')) ?_
    intro _ v' hr'
    rw [hr'.1, hr'.2.1]
    exact hE'
  · -- the space root full: its split; no hole
    intro stop w2 S hsD hbetween hLE hJw2G hsl hstp hDR gs hs _
    obtain ⟨hJw2, _⟩ := hJw2G
    have hs0 : stop = 0 := by
      rcases Nat.eq_zero_or_pos stop with h0 | h0
      · exact h0
      · exact (hstp (hUpP.1 stop h0 hsD)).1
    subst hs0
    have hJv := kdJP_note c base B top0 hB KO B hvB hk _ "up.stop-at-segment-leaf" w2 hJw2
    have hT := upCascJ2OKT_holds c base KO B w w3 top0 pre cv rk (fun i => nodeAt w.top.rootKey P i)
      (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
      (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length 0 w2 _ S hm hLC hJ3.1 hlen3
      hsa2 hvB hk hICEk (by simp [nodeAt]) hpos hB hI hRO hICE hr03 hkey hrk
      hvisw hpX hpK hlkX hXN hlinkK hne' hall' hnl' hdepth hsD hbetween hLE (Or.inr ⟨_, rfl⟩)
      hJv (Or.inl hsl) hDR hJ2 hMF3 hkidsw
    have hcu : CacheUnique ({ w2 with trail := "up.stop-at-segment-leaf" :: w2.trail } : W) :=
      cacheUnique_of_book hJv.1.1.book
    obtain ⟨hlinks2, _⟩ := linksWf_of_book c base B top0 _ w2 hB hJv.1.1 (Or.inr ⟨_, rfl⟩)
    have hL := writerWP_upCasc_root_live c base hsa2 hp B hpos w w3 (fun i => nodeAt w.top.rootKey P i)
      (fun i => (wNode c.p base w (nodeAt w.top.rootKey P i)).getD n)
      (fun i => ((P[i - 1]?).bind (·.1)).getD 0) P.length w2 _ S hI hr03 hLC hlkX hXN
      hlinkK hdepth (by simp [nodeAt]) hLE (Or.inr ⟨_, rfl⟩) hsl hUpP.2 hDR hcu hlinks2
    refine writerWP_mono (writerWP_and hT hL) ?_
    rintro _ w' ⟨hD', hE'⟩
    have hPI := hD'.1.1
    refine writerWP_mono (writerWP_afterDelete_none (pre ++ [cv]) gs hs c base hvc w'
      (fun y hy => hPI.untaken y (tReach_reachS _ _ _ _ hy)) (fun y yn _ h => hPI.wf y yn h) hPI.times
      (liveCounts_of_edges c.p _ _ _ hE')) ?_
    intro _ v' hr'
    rw [hr'.1, hr'.2.1]
    exact hE'
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


/-- A delete, the merges on, that empties its leaf, not the space root, whose climb
reaches the space root, which the transaction did not make (`UpToRoot`): the stop
node is the space root, with room for its bitmap or full. -/
def DelEmptyUpRootM (c : Ctx) (base : View BVal) (w : W) (op : Op) : Prop :=
  ∃ pre cv L n, op = .del (pre ++ [cv]) ∧ c.p.merges = true ∧ KeyLeaf c base w pre cv L n ∧
    bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
    n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = true ∧ L ≠ w.top.rootKey ∧
    UpToRoot c base w L n

set_option maxHeartbeats 1600000 in
/-- The upward delete whose stop node is the space root keeps the live counts
(bergdb 030-01, step 6), the root with room or full, with no premise: from the first
stratum's start with the live counts, no node is left under the fill, so the merges'
loop merges nothing and root collapse does not run (`writerWP_del_upRootLive`). -/
theorem liveDel_upRoot_live (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove) (hp : MergeParamsOK p)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P) :
    ∀ ts tx, Within p (ts ++ [tx]) → R (treeRun p ts) ts.length → ∀ z top,
      lastTop (view (treeSpec p) (treeRun p ts) ts.length) = some z →
      topOf p (ctxOf p ts).view z = .ok top →
      ∀ pre op post, tx.ops = pre ++ op :: post →
      ∀ r w, (pre.mapM putKv) (ctxOf p ts) (wInit tx top) = .ok (r, w) →
      SJ0 p ts tx w → TakeJ2 (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w →
      ∀ key, op = .del key → DelEmptyUpRootM (ctxOf p ts) (viewOf (treeRun p ts)) w op →
      WriterWP (putKv op) (ctxOf p ts) w (fun _ w' =>
        LiveEdges p (wNode p (viewOf (treeRun p ts)) w') (ts.length + 1) w'.top.rootKey) := by
  intro ts tx hw hr z top _ htop ops op post hops r w hpre hS hJ key hop hPc
  obtain ⟨pre, cv, L0, n0, hop', hm, hK, hne0, hall0, hLr0, hup0⟩ := hPc
  subst hop'
  cases hop
  have hI : PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w := hS.1.1.1.1.1
  have hRO : RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey := hS.1.1.2
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  have hICE := innerChildren_reachedR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
    (fun x hx => hI.untaken x (tReach_reachS _ _ _ _ hx))
  have hLV := leafVals_all hS.1.1.1.1.2 hkey hrk
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl (hRK _ _ hr)
      (hRP _ _ hr) hb hi.cache hun
  exact writerWP_del_upRootLive (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w tx.base top hB hbook
    _ hv hk hb0 hi0 hI hRO hICE hkey hrk
    (keyLeaf_all2 hK hrk (fun L n => bitsUnion n.lastBitmap (n.bitsOf cv) ≠ n.lastBitmap ∧
      n.allKeysIn (bitsUnion n.lastBitmap (n.bitsOf cv)) = true ∧ L ≠ w.top.rootKey ∧
      UpToRoot (ctxOf p ts) (viewOf (treeRun p ts)) w L n) ⟨hne0, hall0, hLr0, hup0⟩)
    hS.2.2 hsa2 hp hICEk hm (by simp [ctxOf]) hJ hS.1.2 (fun L n hL hn hnl y hy => (hLV L n hL hn hnl y hy).1)

end SIS.Tree
