/-
`hU` out of the take-back's cascade at the space root (bergdb 025-04, route (b),
step 2): `writerWP_upCasc_root_j2` without the tree at the upward loop's end.
The root's split (`writerWP_handleFull_root_j2U`) is applied at the state whose
root has its bitmap as if it had room (S', `BitmapOf`), whose tree is the tree at
the delete's start without the chain (`treeOK_up_tr`), and its postcondition is
moved to the writer's state by the swap (`writerWP_handleFullWith_root_swap`,
StopSwap.lean).
-/
import SIS.Tree.TakeUpCasc
import SIS.Tree.StopSwap

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A node with a live klong and well-formed klongs has a time klong first. -/
theorem KNode.firstTime_some_of_live (n : KNode) (t : Time) (hw : klongsWf n.ks = true)
    (c : Nat) (y : NodeId) (h : (c, y) ∈ n.liveAt t) :
    ∃ s, n.firstTime = some s ∧ Klong.time s ∈ n.ks := by
  cases hks : n.ks with
  | nil =>
    exfalso
    have hl : n.liveAt t = [] := by
      simp [KNode.liveAt, hks, prefixAt, KNode.lastVersionGivenDel]
    rw [hl] at h; cases h
  | cons k rest =>
    rw [klongsWf_eq_fold, hks] at hw
    simp only [List.zipIdx_cons, List.foldl_cons] at hw
    have h0 := klongsWf_fold_ok _ _ _ hw
    cases k with
    | time s => exact ⟨s, by simp [KNode.firstTime, hks], by simp⟩
    | key _ _ => simp [klongsWfStep] at h0
    | del _ => simp [klongsWfStep] at h0

set_option maxHeartbeats 6400000 in
/-- `writerWP_upCasc_root_j2` without the tree at the loop's end (`hT2`, 025-04,
route (b)): the root's split is applied at the state whose root has its bitmap
(S'), a tree by `treeOK_up_tr`, and moved to the writer's state by
`writerWP_handleFullWith_root_swap`; the overlay holds one entry per id. -/
theorem writerWP_upCasc_root_j2S (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (hsa2 : 2 ≤ c.p.splitAbove) (B : NodeId) (hpos : 0 < c.i)
    (w w3 : W) (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth : Nat) (w2 v : W) (S : KNode)
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
    (hv : v = w2 ∨ ∃ s, v = { w2 with trail := s :: w2.trail })
    (hfull : ¬ DelRoom c (K 1) S)
    (hcu : CacheUnique v)
    (hlinks2 : ∀ u c' z, TLink (wNode c.p base w2) c.i u c' z → z < w2.next)
    (hwf2 : ∀ z zn, wNode c.p base w2 z = some zn → klongsWf zn.ks = true) :
    WriterWP (appendDeleteKlong (X 0) 0 (K 1)) c v
      (fun _ w' => TakeJ2 c base B w' ∧ B ≤ w'.next) := by
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
  have hvn : v.nodes = w2.nodes := by rcases hv with rfl | ⟨s, rfl⟩ <;> rfl
  have hvt : v.taken = w2.taken := by rcases hv with rfl | ⟨s, rfl⟩ <;> rfl
  have hvtop : v.top = w2.top := by rcases hv with rfl | ⟨s, rfl⟩ <;> rfl
  have hvv : v.vals = w2.vals := by rcases hv with rfl | ⟨s, rfl⟩ <;> rfl
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
  refine writerWP_appendDeleteKlong_full_of (X 0) 0 (K 1) S c v hlkv hneS' hfull _ ?_
  intro compact s
  generalize hlast : S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf (K 1))) = last
  obtain ⟨hleq, hlwf, hlt, hlastV, hlen2, hpairs, hiff, _⟩ := delLast_split_facts c S (K 1) hsa2 hSt last hlast
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
  have hW : ∀ z zn, wNode c.p base ({ v with trail := s :: v.trail } : W) z = some zn →
      klongsWf zn.ks = true := by
    rw [hwv']; exact hwf2
  have hagreeV : ∀ u, u ≠ X 0 → (∀ i, 0 < i → i ≤ depth → u ≠ X i) →
      updN (wNode c.p base ({ v with trail := s :: v.trail } : W)) (X 0) ⟨S.leaf, last.ks⟩ u =
        wNode c.p base w3 u := fun u hus hnc => by
    rw [updN_ne _ _ _ _ hus, hwv']; exact hagree2 u hus hnc
  have hsnV : updN (wNode c.p base ({ v with trail := s :: v.trail } : W)) (X 0) ⟨S.leaf, last.ks⟩ (X 0) =
      some ⟨S.leaf, last.ks⟩ := updN_self _ _ _
  have hV : TreeOK (updN (wNode c.p base ({ v with trail := s :: v.trail } : W)) (X 0) ⟨S.leaf, last.ks⟩)
      c.i ({ v with trail := s :: v.trail } : W).top.rootKey := by
    rw [hroot']
    exact treeOK_up_tr (wNode c.p base w3) _ c.i w3.top.rootKey X Nn K 0 depth hdepth hT3
      (hreach3 0 (by omega)) (fun i _ hi => hN3 i hi) (fun i h1 hi => hlinkK i h1 hi)
      (fun i i' _ hi _ hi' he => hdist i i' hi hi' he) hagreeV _ hsnV id
      (fun c' z h => ⟨c', ((hliveL c' z).mp h).1, ((hliveL c' z).mp h).2, rfl⟩)
  have hvx : ∀ c' z, (c', z) ∈ (⟨S.leaf, last.ks⟩ : KNode).liveAt c.i →
      z < ({ v with trail := s :: v.trail } : W).next := by
    intro c' z h
    rw [hnx', hr03.2.2.2.2]
    exact hI.links (X 0) (Nn 0) c' z (tReach_reachS _ _ _ _ (hreach 0 (by omega))) (hXN 0 (by omega))
      ((hliveL c' z).mp h).1
  -- the nodes of the transaction's time, reached in the tree with the root's last version
  have hTtV := ttReachedN_up (wNode c.p base w3)
    (updN (wNode c.p base ({ v with trail := s :: v.trail } : W)) (X 0) ⟨S.leaf, last.ks⟩) c.i
    w3.top.rootKey X Nn 0 depth hdepth (fun i _ hi => hN3 i hi) hone
    (fun c' z h => by rw [hr03.1]; exact hkidsw c' z h) _ hsnV
    (fun c' z hm hz => ⟨c', (hliveL c' z).mpr ⟨hm, fun hck => hz (by
      rw [hck] at hm; exact KNode.liveAt_fun _ _ _ _ _ hm hsx)⟩⟩)
    hagreeV hXs (hreach3 0 (by omega))
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
      TReach (updN (wNode c.p base ({ v with trail := s :: v.trail } : W)) (X 0) ⟨S.leaf, last.ks⟩) c.i
        ({ v with trail := s :: v.trail } : W).top.rootKey q := by
    intro q qn hq hm
    by_cases hq0 : q = X 0
    · rw [hq0, hrk']; exact TReach.root
    · rw [hroot']
      exact hTtV q qn (by rw [updN_ne _ _ _ _ hq0]; exact hq) hm
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
  -- the stop node with its bitmap, S', and the state u with it
  have hft0 : ∃ s0, (Nn 0).firstTime = some s0 := by
    obtain ⟨s0, h1, _⟩ := KNode.firstTime_some_of_live (Nn 0) c.i hswf _ _ hsx
    exact ⟨s0, h1⟩
  generalize hS'd : S.add c.i (.del (bitsUnion S.lastBitmap (S.bitsOf (K 1)))) = S'
  have hbm : BitmapOf S S' c.i (K 1) := Or.inl hS'd.symm
  have hS'leaf : S'.leaf = S.leaf := bitmapOf_leaf S S' c.i (K 1) hbm
  have hS'wf : klongsWf S'.ks = true := by rw [← hS'd]; exact KNode.add_delete_wf S c.i (K 1) hSwf hneS'
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
  have hvalsu : u.vals = w3.vals := by rw [← hud]; exact hvals2
  have hwu : wNode c.p base u = updN (wNode c.p base ({ v with trail := s :: v.trail } : W)) (X 0) S' := by
    rw [← hud]; exact wNode_upsert_updN c.p base _ _ (X 0) S' rfl rfl htk'
  have hsnu : wNode c.p base u (X 0) = some S' := by rw [hwu]; exact updN_self _ _ _
  have hagreeU : ∀ u0, u0 ≠ X 0 → (∀ i, 0 < i → i ≤ depth → u0 ≠ X i) →
      wNode c.p base u u0 = wNode c.p base w3 u0 := fun u0 hus hnc => by
    rw [hwu, updN_ne _ _ _ _ hus, hwv']; exact hagree2 u0 hus hnc
  have hwuk : ∀ k, 0 < k → k ≤ depth → wNode c.p base u (X k) = wNode c.p base w2 (X k) :=
    fun k h1 h2 => by rw [hwu, updN_ne _ _ _ _ (Ne.symm (hXs k h1 h2)), hwv']
  -- the tree with S'
  have hTu : TreeOK (wNode c.p base u) c.i u.top.rootKey := by
    rw [hrootu]
    exact treeOK_up_tr (wNode c.p base w3) _ c.i w3.top.rootKey X Nn K 0 depth hdepth hT3
      (hreach3 0 (by omega)) (fun i _ hi => hN3 i hi) (fun i h1 hi => hlinkK i h1 hi)
      (fun i i' _ hi _ hi' he => hdist i i' hi hi' he) hagreeU _ hsnu id
      (fun c' z h => ⟨c', ((hS'live c' z).mp h).1, ((hS'live c' z).mp h).2, rfl⟩)
  -- the node facts with S'
  have hrestU := j2rest_up (wNode c.p base w3) (wNode c.p base u) c.i B (w3.vals.map (·.1)) X Nn 0 depth
    (K 1) hdepth hpos hJ3.2.1 hJ3.2.2.1 hJ3.2.2.2.1 hJ3.2.2.2.2.1 hJ3.2.2.2.2.2 (fun i _ hi => hN3 i hi)
    (fun i i' _ hi _ hi' he => hdist i i' hi hi' he)
    (by
      intro k h1 h2
      unfold ChainFateN
      rw [hwuk k h1 h2]
      obtain ⟨hm, hu'⟩ := hfateJ2 k h1 h2
      refine ⟨fun hf => by simp only [wNode, hm hf, ↓reduceIte], fun hf => ?_⟩
      obtain ⟨ht0, S0, hS0, hl0⟩ := hu' hf
      exact ⟨S0, hS0, by simp only [wNode, ht0, Bool.false_eq_true, ↓reduceIte, hl0]⟩)
    hswf hst_t hsx S S' (fun _ => False) hSR hSF' hsnu (bitmapOf_prefix S S' c.i _ hbm hpos)
    (bitmapOf_firstTime S S' c.i _ hbm)
    (fun i c' y h => Or.inl (bitmapOf_key S S' c.i _ hbm i c' y h)) (fun y h => h.elim)
    (fun c' y hm hc => ⟨c', (hS'live c' y).mpr ⟨hm, hc⟩⟩)
    (fun hl => ⟨by rw [← hS'leaf]; exact hl, fun i c' hL hc => bitmapOf_lastLive S S' c.i _ hbm i c' hL hc⟩)
    hagreeU
  have hS5u : ∀ z, u.next ≤ z → u.nodes.lookup z = none ∧ u.taken.contains z = false ∧
      knodeOf c.p base z = none := by
    intro z hz
    have hz' : ({ v with trail := s :: v.trail } : W).next ≤ z := by rw [hnx', ← hnxu]; exact hz
    obtain ⟨h1, h2, h3⟩ := hS5 z hz'
    have hz0 : z ≠ X 0 := fun he => by have := hXlt 0 (by omega); rw [← hnxu] at this; omega
    refine ⟨?_, by rw [← hud]; exact h2, h3⟩
    rw [← hud]; simp only [setX, lookup_upsert, hz0, ↓reduceIte]; exact h1
  have hS6u : ∀ a c' z, TLink (wNode c.p base u) c.i a c' z → z < u.next := by
    intro a c' z ⟨an, han, hl⟩
    rw [hnxu]
    by_cases ha : a = X 0
    · rw [ha, hsnu] at han; cases han
      rw [hr03.2.2.2.2]
      exact hI.links (X 0) (Nn 0) c' z (tReach_reachS _ _ _ _ (hreach 0 (by omega))) (hXN 0 (by omega))
        ((hS'live c' z).mp hl).1
    · rw [hwu, updN_ne _ _ _ _ ha] at han
      rw [← hnx']; exact hS6 a c' z ⟨an, han, hl⟩
  have hWu : ∀ z zn, wNode c.p base u z = some zn → klongsWf zn.ks = true := by
    intro z zn hz
    by_cases hz0 : z = X 0
    · rw [hz0, hsnu] at hz; cases hz; exact hS'wf
    · rw [hwu, updN_ne _ _ _ _ hz0] at hz; exact hW z zn hz
  have hVu : TreeOK (updN (wNode c.p base u) (X 0) ⟨S'.leaf, last.ks⟩) c.i u.top.rootKey := by
    rw [hwu, updN_updN_same, hS'leaf, hrootu, ← hroot']; exact hV
  have hvxu : ∀ c' z, (c', z) ∈ (⟨S'.leaf, last.ks⟩ : KNode).liveAt c.i → z < u.next := by
    rw [hS'leaf, hnxu, ← hnx']; exact hvx
  have hTUu : ∀ q qn, wNode c.p base u q = some qn → Klong.time c.i ∈ qn.ks →
      TReach (updN (wNode c.p base u) (X 0) ⟨S'.leaf, last.ks⟩) c.i u.top.rootKey q := by
    intro q qn hq hm
    rw [hwu, updN_updN_same, hS'leaf, hrootu, ← hroot']
    by_cases hq0 : q = X 0
    · rw [hq0, hroot', ← hrootu, hrku]; exact TReach.root
    · rw [hwu, updN_ne _ _ _ _ hq0] at hq
      exact hTU q qn hq hm
  have hmain := writerWP_handleFull_root_j2U c base hvc B hpos (X 0) S' last compact u
    (by rw [hvalsu]; exact hrestU) (by rw [hnxu, hr03.2.2.2.2]; exact hBn)
    (by
      intro y hy
      rw [hvalsu] at hy
      rw [hnxu]
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hy
      exact hI3.ids.2.2.2.1 e he)
    hTu hlwf hlt (by rw [hS'leaf]; exact hlastV) (by rw [hS'leaf]; exact hlen2) hpairs hlku htku hrku
    hS5u hS6u hWu hVu hvxu hS'wf hS't hTUu
  have hX0n : X 0 < u.next := by rw [hnxu]; exact hXlt 0 (by omega)
  have h2 := writerWP_handleFullWith_root_swap rootUp (X 0) S' S last compact c u _ hlku hX0n hft
    hS'leaf.symm (fun _ => hprev) hmain
  rw [← hud, setX_setX,
    setX_self _ _ _ (show CacheUnique ({ v with trail := s :: v.trail } : W) from hcu) hlk'] at h2
  exact h2


end SIS.Tree
