/-
The stop node's bitmap into a full node at the space root (bergdb 024-12, case
(4), `UpCascOKF3` at stop 0): after the upward loop, the space root's last
version without its klong to the chain splits (`writerWP_handleFull_rootVF2`,
`writerWP_rootSplit_rangeL`). The tree with that last version is the walk's
tree without the chain (`treeOK_up_tr`, `rangeOrder_up_bitmap`) and reads as
the delete's (`getFromR_up_inner`, `getFromR_up_leaf`). No tree of the state
after the loop is needed at the root: only its links below the next id and its
klongs well formed.
-/
import SIS.Tree.DelStepsCascF3

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- The divider of a node's halves with nothing put is live, and a live compare
value is below it. -/
theorem halves_facts_nilR (t : Time) (n : KNode) (h2 : 2 ≤ n.live.length)
    (hnt : ∀ s, Klong.time s ∈ n.ks → s ≤ t) :
    ∀ r', (halves n.leaf t (n.lastVersion t) []).2.2 = r' →
      (∃ zs, (r', zs) ∈ n.liveAt t) ∧ ∃ c0 z0, (c0, z0) ∈ n.liveAt t ∧ c0 < r' := by
  intro r' hr'
  obtain ⟨r, hr⟩ := divider_exists n (by omega)
  have hsc := divider_pos' n r h2 hr
  obtain ⟨hdiv, _, _⟩ := halves_links_nil n.leaf t n rfl r hr hsc
  have hdiv' : (halves n.leaf t (n.lastVersion t) []).2.2 = r.1 := hdiv
  rw [hdiv'] at hr'
  subst hr'
  have hrm := divider_mem_live n r hr
  refine ⟨⟨r.2, by rw [KNode.liveAt_of_times n t hnt]; exact hrm⟩, ?_⟩
  have hleft := halves_left_lt_divider n.live (n.live.length / 2) n.live_order r hr
  obtain ⟨a, ha⟩ : ∃ a, a ∈ n.live.take (n.live.length / 2) := by
    cases h : n.live.take (n.live.length / 2) with
    | nil =>
      exfalso
      have := congrArg List.length h
      simp only [List.length_take, List.length_nil] at this
      omega
    | cons a _ => exact ⟨a, List.mem_cons_self⟩
  exact ⟨a.1, a.2, by rw [KNode.liveAt_of_times n t hnt]; exact List.mem_of_mem_take ha, hleft a ha⟩

set_option maxHeartbeats 6400000 in
/-- `UpCascOKF3` at the space root (stop 0), the bitmap kinds: from the state
after the upward loop with its links below the next id and its klongs well
formed (`hlinks2`, `hwf2`), and the state after the root's split fitting the
fuel (`hFits`), the stop node's bitmap puts the state into `DelInvF3`. -/
theorem writerWP_upCasc_root_delF3 (c : Ctx) (base : View BVal) (hvc : ViewCoherent c base)
    (hsa2 : 2 ≤ c.p.splitAbove)
    (KO : KindOracle) (BK : NodeId) (hvB : ViewIdsBelow BK c.view) (hk : ViewKinds KO BK c)
    (hICEk : ICEFromKinds c base KO BK)
    (w w3 : W) (B MB : NodeId) (top0 : Top) (pre : List Nat) (cv : Nat) (rk : NodeId)
    (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth : Nat) (w2 v : W) (S : KNode)
    (hB : PutBase c base B) (hI : PutInv c base w)
    (hRO : RangeOrder (wNode c.p base w) c.i w.top.rootKey)
    (hF : SegFits (wNode c.p base w) c.i (c.p.fuel - 1) w.top.rootKey)
    (hr03 : ReadsAs c.p base w w3) (hkey : keyWf (pre ++ [cv]) = true)
    (hrk : segRootR (wNode c.p base w) c.i c.p.fuel pre w.top.rootKey = some rk)
    (hvis : (X depth, cv) ∈ eqVisits (wNode c.p base w) c.i cv c.p.fuel rk)
    (hpX : ∀ i, i ≤ depth → (w3.path[i]?).map (·.2) = some (X i))
    (hlkX : ∀ i, i ≤ depth → w3.nodes.lookup (X i) = some (Nn i))
    (hXN : ∀ i, i ≤ depth → wNode c.p base w (X i) = some (Nn i))
    (hlinkK : ∀ i, 0 < i → i ≤ depth → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i)
    (hall : (Nn depth).allKeysIn (bitsUnion (Nn depth).lastBitmap ((Nn depth).bitsOf cv)) = true)
    (hleaf : (Nn depth).leaf = true) (hdepth : 0 < depth)
    (hbetween : ∀ i, 0 < i → i < depth →
      (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true)
    (hX0 : X 0 = w.top.rootKey)
    (hLE : UpLoopEnd c MB X Nn depth 0 w3 w2 S)
    (hv : v = w2 ∨ ∃ s, v = { w2 with trail := s :: w2.trail })
    (hJ : KdJP c B top0 KO BK w3.path v)
    (hkind : (Nn 0).leaf = true ∨ K 1 ≠ 0) (hfull : ¬ DelRoom c (K 1) S)
    (hlinks2 : ∀ u c' z, TLink (wNode c.p base w2) c.i u c' z → z < w2.next)
    (hwf2 : ∀ z zn, wNode c.p base w2 z = some zn → klongsWf zn.ks = true)
    (hFits : WriterWP (appendDeleteKlong (X 0) 0 (K 1)) c v
      (fun _ w' => SegFits (wNode c.p base w') c.i c.p.fuel w'.top.rootKey)) :
    WriterWP (appendDeleteKlong (X 0) 0 (K 1)) c v
      (fun _ w' => DelInvF3 c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK w') := by
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
  -- the chain's facts (as the walk's)
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
  have honly : ∀ c' z, (c', z) ∈ (Nn depth).liveAt c.i → c' = cv := by
    intro c' z hm
    have hm' : (c', z) ∈ (Nn depth).live := by
      rw [← KNode.liveAt_of_times _ c.i (hI.times _ _ (hXN depth (Nat.le_refl _)))]; exact hm
    exact allKeysIn_live_cv (Nn depth) cv hall c' z hm'
  -- the bitmap into the full root
  have hmain : WriterWP (appendDeleteKlong (X 0) 0 (K 1)) c v (fun _ w' =>
      SegFits (wNode c.p base w') c.i c.p.fuel w'.top.rootKey → PutBook c B top0 w' → Book BK c w' →
      KdInv KO BK w' → DelInvF3 c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK w') := by
    refine writerWP_appendDeleteKlong_full_of (X 0) 0 (K 1) S c v hlkv hneS' hfull _ ?_
    intro compact s
    generalize hlast : S.lastVersionGivenDel c.i (bitsUnion S.lastBitmap (S.bitsOf (K 1))) = last
    obtain ⟨hleq, hlwf, hlt, hlastV, hlen2, _, hiff, _⟩ := delLast_split_facts c S (K 1) hsa2 hSt last hlast
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
    -- the tree with the root's last version
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
    have hVR : RangeOrder (updN (wNode c.p base ({ v with trail := s :: v.trail } : W)) (X 0)
        ⟨S.leaf, last.ks⟩) c.i ({ v with trail := s :: v.trail } : W).top.rootKey := by
      rw [hroot']
      exact rangeOrder_up_bitmap (wNode c.p base w3) _ c.i w3.top.rootKey X Nn K 0 depth hdepth hR3 hT3
        (hreach3 0 (by omega)) (fun i _ hi => hN3 i hi) (fun i h1 hi => hlinkK i h1 hi)
        (fun i i' _ hi _ hi' he => hdist i i' hi hi' he) hagreeV _ hsnV (by show S.leaf = _; exact hSleaf)
        (fun c' z h => (hliveL c' z).mp h)
    have hvx : ∀ c' z, (c', z) ∈ (⟨S.leaf, last.ks⟩ : KNode).liveAt c.i →
        z < ({ v with trail := s :: v.trail } : W).next := by
      intro c' z h
      rw [hnx', hr03.2.2.2.2]
      exact hI.links (X 0) (Nn 0) c' z (tReach_reachS _ _ _ _ (hreach 0 (by omega))) (hXN 0 (by omega))
        ((hliveL c' z).mp h).1
    -- the halves of a space split
    have hH : c.p.splitAbove < last.size → ∃ r : Nat × NodeId, 0 < r.1 ∧
        (halves S.leaf c.i last []).2.2 = r.1 ∧
        (∀ c' z, (c', z) ∈ (halves S.leaf c.i last []).1.liveAt c.i →
          c' < r.1 ∧ (c', z) ∈ (⟨S.leaf, last.ks⟩ : KNode).liveAt c.i) ∧
        (∀ c' z, (c', z) ∈ (halves S.leaf c.i last []).2.1.liveAt c.i →
          ∃ c0, r.1 ≤ c0 ∧ c' = splitLocalCv S.leaf r.1 c0 ∧
            (c0, z) ∈ (⟨S.leaf, last.ks⟩ : KNode).liveAt c.i) := by
      intro hsp
      obtain ⟨r, hdiv, hsc, _, hfh, hsh⟩ := halves_facts_nil c.i ⟨S.leaf, last.ks⟩ (hlen2 hsp) hlt
      rw [hlastV] at hdiv hfh hsh
      exact ⟨r, hsc, hdiv, hfh, hsh⟩
    have hHR : c.p.splitAbove < last.size → ∀ r, (halves S.leaf c.i last []).2.2 = r →
        (∃ zs, (r, zs) ∈ (⟨S.leaf, last.ks⟩ : KNode).liveAt c.i) ∧
        ∃ c0 z0, (c0, z0) ∈ (⟨S.leaf, last.ks⟩ : KNode).liveAt c.i ∧ c0 < r := by
      intro hsp r hr
      have h := halves_facts_nilR c.i ⟨S.leaf, last.ks⟩ (hlen2 hsp) hlt r
      rw [hlastV] at h
      exact h hr
    have hlevel := writerWP_handleFull_rootVF2 (c.p.fuel + 1) (by omega) c base hvc rootUp (X 0) S last
      compact hlwf hlt hlastV hlen2 ({ v with trail := s :: v.trail } : W) hlk' htk' hrk' hS5 hS6 hW hV hvx
    have hrange := writerWP_rootSplit_rangeL c base hvc rootUp (X 0) S last compact hH hHR
      ({ v with trail := s :: v.trail } : W) hlk' htk' hrk' hS5 hS6 hV hVR hvx
    refine writerWP_mono (writerWP_and hlevel hrange) ?_
    rintro _ w' ⟨⟨_, ht', hvals', hreach', _, hRead, _, _, _, _, _⟩, ⟨hTw, _, hRw, _⟩⟩ hFw hbw hbkw hikw
    -- what is reached after is reached in the walk's tree, or new
    have hsub := tReach_up_sub_tr (wNode c.p base w3) _ c.i w3.top.rootKey X Nn K 0 depth hdepth hT3
      (hreach3 0 (by omega)) (fun i _ hi => hN3 i hi) (fun i h1 hi => hlinkK i h1 hi)
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
      · exact (hS5 y h).2.1
    obtain ⟨hPw, hGw⟩ := putInv_after_step c base w' B top0 hB hbw hTw
      (fun y hy => hun y (reachS_tReach _ _ _ _ hy)) hRw
    refine ⟨⟨hPw, hGw, hRw, hICEk w' hbkw hikw hun, by simpa using hFw, fun key' hk' => ?_, B, top0, hB, hbw⟩,
      hbkw, hikw⟩
    -- the reading, through the tree with the root's last version
    have hVal3 : wValue base ({ v with trail := s :: v.trail } : W) = wValue base w3 :=
      wValue_eq_of_taken base w3 _ (by show v.vals = w3.vals; rw [hvv, h2v])
        (fun y => ∃ k, 0 < k ∧ k ≤ depth ∧ y = X k)
        (fun y hy => by
          show v.taken.contains y = w3.taken.contains y
          rw [hvt]; exact h2t y (fun k h1 h2 he => hy ⟨k, h1, h2, he⟩))
        (fun y ⟨k, _, h2, he⟩ => by rw [he]; exact ⟨htk3 k h2, hnoval3 k h2⟩)
    have hValw' : wValue base w' = wValue base w3 := by
      rw [← hVal3]; exact wValue_congr' base w' _ ht' hvals'
    have hVal : ∀ z, (({ v with trail := s :: v.trail } : W).next ≤ z ∨ z = X 0) → wValue base w' z = none := by
      intro z hz
      rw [hValw']
      rcases hz with hz | rfl
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
      · exact hnoval3 0 (by omega)
    have hR := hRead (wValue base w') hVal (Or.inl (by simpa using hFw)) key'
    -- the virtual state with the root's last version
    have hwV : wNode c.p base ({ ({ v with trail := s :: v.trail } : W) with
        nodes := upsert v.nodes (X 0) ⟨S.leaf, last.ks⟩ } : W) =
        updN (wNode c.p base ({ v with trail := s :: v.trail } : W)) (X 0) ⟨S.leaf, last.ks⟩ :=
      wNode_upsert_updN c.p base _ _ (X 0) _ rfl rfl htk'
    generalize hwVd : ({ ({ v with trail := s :: v.trail } : W) with
        nodes := upsert v.nodes (X 0) ⟨S.leaf, last.ks⟩ } : W) = wV at hwV
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
      by_cases hux : u = X 0
      · subst hux
        rw [hwV, hsnV] at hun'
        cases hun'
        refine ⟨Nn 0, hN3 0 (by omega), by rw [← hSleaf]; exact hl, fun c' y hy => ⟨c', ((hliveL c' y).mp hy).1⟩⟩
      · have hu' := (hsub u (by rw [← hwV, ← hVtop]; exact reachS_tReach _ _ _ _ hu)).2
        rw [hwV, hagreeV u hux hu'] at hun'
        exact ⟨un', hun', hl, fun c' y hy => ⟨c', hy⟩⟩
    have hwfV : ∀ x xn, ReachS (wNode c.p base wV) c.i wV.top.rootKey x → wNode c.p base wV x = some xn →
        klongsWf xn.ks = true := by
      intro x xn _ h
      rw [hwV] at h
      by_cases hx : x = X 0
      · subst hx; rw [updN_self] at h; cases h; exact hlwf
      · rw [updN_ne _ _ _ _ hx] at h; exact hW x xn h
    have hwfS3 : ∀ x xn, ReachS (wNode c.p base w3) c.i w3.top.rootKey x → wNode c.p base w3 x = some xn →
        klongsWf xn.ks = true := fun x xn _ h => by rw [hr03.1] at h; exact hI.wf x xn h
    have hagreeR : ∀ u, TReach (wNode c.p base w3) c.i w3.top.rootKey u → u ≠ X 0 →
        (∀ i, 0 < i → i ≤ depth → u ≠ X i) → wNode c.p base wV u = wNode c.p base w3 u :=
      fun u _ hus hnc => by rw [hwV]; exact hagreeV u hus hnc
    have hsnwV : wNode c.p base wV (X 0) = some ⟨S.leaf, last.ks⟩ := by rw [hwV]; exact hsnV
    have hreadV : wGet c.p c.i base wV key' = if pre ++ [cv] == key' then none else wGet c.p c.i base w3 key' := by
      unfold wGet
      rw [hVval, hVtop]
      have hrk3 : segRootR (wNode c.p base w3) c.i c.p.fuel pre w3.top.rootKey = some rk := by
        rw [hr03.1, hr03.2.1]; exact hrk
      have hvis3 : (X depth, cv) ∈ eqVisits (wNode c.p base w3) c.i cv c.p.fuel rk := by
        rw [hr03.1]; exact hvis
      have huniq3 := hI.keyUniq pre cv rk hkey hrk
      rw [← hr03.1, ← hr03.2.1] at huniq3
      cases hsl : (Nn 0).leaf with
      | false =>
        have hK0 : K 1 ≠ 0 := by
          rcases hkind with h | h
          · rw [hsl] at h; cases h
          · exact h
        exact getFromR_up_inner (wNode c.p base w3) (wNode c.p base wV) (wValue base w3) c.i c.p.fuel hfuel
          w3.top.rootKey X Nn K 0 depth hdepth pre cv rk hT3 hR3 hwf3 (hreach3 0 (by omega))
          (fun i _ hi => hN3 i hi) (fun i h1 hi => hlinkK i h1 hi) hone hleaf honly
          (fun i _ hi => hnoval3 i hi)
          (fun i _ hi he => by have := hdist i depth (by omega) (Nat.le_refl _) he; omega)
          hrk3 (keyWf_last_notin pre cv hkey) hvis3 huniq3 hagreeR _ hsl hsnwV
          (by show S.leaf = false; rw [hSleaf]; exact hsl) hliveL key' hk'
      | true =>
        exact getFromR_up_leaf (wNode c.p base w3) (wNode c.p base wV) (wValue base w3) c.i c.p.fuel hfuel
          w3.top.rootKey X Nn K 0 depth hdepth pre cv rk hT3 hR3 hwf3 (hreach3 0 (by omega))
          (fun i _ hi => hN3 i hi) (fun i h1 hi => hlinkK i h1 hi) hone hleaf honly
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
  have hpx : v.path[0]? = some ((v.path[0]?).map (·.1) |>.getD none, X 0) := by
    have h := hpX 0 (by omega)
    rw [← hvp] at h
    cases hp : v.path[0]? with
    | none => rw [hp] at h; cases h
    | some e =>
      rw [hp] at h
      simp only [Option.map_some, Option.some.injEq] at h
      simp [← h]
  refine writerWP_mono (writerWP_and (writerWP_and (writerWP_and hmain hFits)
    (putBook_appendDeleteKlong (X 0) 0 (K 1) c base B top0 hB v hJ.1.1))
    (kd_appendDeleteKlong KO BK (X 0) 0 (K 1) c v hvB hk hJ.1.2.1 hJ.1.2.2 _ hpx)) ?_
  rintro _ w' ⟨⟨⟨hM, hFw⟩, hbw⟩, hbkw, hikw, _, _⟩
  exact hM hFw hbw hbkw hikw


/-- Named input (the take-back's, with `UpUnlinkOK`): the state after the
upward loop names ids below the next id from every node, and every node's klongs
are well formed (checked on runs with `UpUnlinkOK`). -/
def UpUnlinkLinksOK (c : Ctx) (base : View BVal) : Prop :=
  ∀ (w w3 : W) (MB : NodeId) (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth stop : Nat)
    (w2 : W) (S : KNode),
    PutInv c base w → ReadsAs c.p base w w3 →
    (∀ i, i ≤ depth → w3.nodes.lookup (X i) = some (Nn i)) →
    (∀ i, 0 < i → i ≤ depth → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i) → stop < depth →
    UpLoopEnd c MB X Nn depth stop w3 w2 S →
    (∀ u c' z, TLink (wNode c.p base w2) c.i u c' z → z < w2.next) ∧
    (∀ z zn, wNode c.p base w2 z = some zn → klongsWf zn.ks = true)

/-- Named input (cost's, the heights): after the stop node's bitmap into a full
node (`UpCascOKF3`'s premises), the state fits the writer's fuel. -/
def UpCascFitsOK (c : Ctx) (base : View BVal) (KO : KindOracle) (BK : NodeId) : Prop :=
  ∀ (w w3 : W) (B MB : NodeId) (top0 : Top) (pre : List Nat) (cv : Nat) (rk : NodeId)
    (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth stop : Nat) (w2 v : W) (S : KNode),
    2 ≤ c.p.splitAbove → ViewIdsBelow BK c.view → ViewKinds KO BK c → ICEFromKinds c base KO BK →
    X 0 = w.top.rootKey → PutBase c base B → PutInv c base w → RangeOrder (wNode c.p base w) c.i w.top.rootKey →
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
      (fun _ w' => SegFits (wNode c.p base w') c.i c.p.fuel w'.top.rootKey)

/-- Obligation: `UpCascOKF3` below the space root (0 < stop). -/
def UpCascBelowOKF3 (c : Ctx) (base : View BVal) (KO : KindOracle) (BK : NodeId) : Prop :=
  ∀ (w w3 : W) (B MB : NodeId) (top0 : Top) (pre : List Nat) (cv : Nat) (rk : NodeId)
    (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth stop : Nat) (w2 v : W) (S : KNode),
    2 ≤ c.p.splitAbove → ViewIdsBelow BK c.view → ViewKinds KO BK c → ICEFromKinds c base KO BK →
    X 0 = w.top.rootKey → PutBase c base B → PutInv c base w → RangeOrder (wNode c.p base w) c.i w.top.rootKey →
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
    (Nn depth).leaf = true → 0 < depth → 0 < stop → stop < depth →
    (∀ i, stop < i → i < depth →
      (Nn i).allKeysIn (bitsUnion (Nn i).lastBitmap ((Nn i).bitsOf (K (i + 1)))) = true) →
    UpLoopEnd c MB X Nn depth stop w3 w2 S →
    (v = w2 ∨ ∃ s, v = { w2 with trail := s :: w2.trail }) → KdJP c B top0 KO BK w3.path v →
    ((Nn stop).leaf = true ∨ K (stop + 1) ≠ 0) → ¬ DelRoom c (K (stop + 1)) S →
    WriterWP (appendDeleteKlong (X stop) stop (K (stop + 1))) c v
      (fun _ w' => DelInvF3 c base w (pre ++ [cv]) (c.p.fuel + 1) KO BK w')

/-- `UpCascOKF3` from its parts: at the space root by `writerWP_upCasc_root_delF3`
(the links and klongs after the loop, `UpUnlinkLinksOK`; the fuel after the
split, `UpCascFitsOK`), below it by `UpCascBelowOKF3`. -/
theorem upCascOKF3_of_parts (c : Ctx) (base : View BVal) (KO : KindOracle) (BK : NodeId)
    (hL : UpUnlinkLinksOK c base) (hFit : UpCascFitsOK c base KO BK) (hBel : UpCascBelowOKF3 c base KO BK) :
    UpCascOKF3 c base KO BK := by
  intro w w3 B MB top0 pre cv rk X Nn K depth stop w2 v S hsa2 hvB hk hICEk hX0 hB hI hRO hF hICE hr03 hkey
    hrk hvis hpX hpK hlkX hXN hlinkK hne hall hleaf hdepth hsD hbetween hLE hv hJ hkind hfull
  rcases Nat.eq_zero_or_pos stop with hs | hs
  · subst hs
    obtain ⟨hlinks2, hwf2⟩ := hL w w3 MB X Nn K depth 0 w2 S hI hr03 hlkX hlinkK hsD hLE
    exact writerWP_upCasc_root_delF3 c base hB.coherent hsa2 KO BK hvB hk hICEk w w3 B MB top0 pre cv rk
      X Nn K depth w2 v S hB hI hRO hF hr03 hkey hrk hvis hpX hlkX hXN hlinkK hall hleaf hdepth hbetween
      hX0 hLE hv hJ hkind hfull hlinks2 hwf2
      (hFit w w3 B MB top0 pre cv rk X Nn K depth 0 w2 v S hsa2 hvB hk hICEk hX0 hB hI hRO hF hICE hr03
        hkey hrk hvis hpX hpK hlkX hXN hlinkK hne hall hleaf hdepth hsD hbetween hLE hv hJ hkind hfull)
  · exact hBel w w3 B MB top0 pre cv rk X Nn K depth stop w2 v S hsa2 hvB hk hICEk hX0 hB hI hRO hF hICE
      hr03 hkey hrk hvis hpX hpK hlkX hXN hlinkK hne hall hleaf hdepth hs hsD hbetween hLE hv hJ hkind hfull

/-- `DelStepsOKF3` with the stop node's bitmap into a full node at the space
root proved (`upCascOKF3_of_parts`): open are that bitmap below the space root
(`UpCascBelowOKF3`), LE-b (`UpLebOKF3`), the links after the loop
(`UpUnlinkLinksOK`, the take-back's) and the fuel after the splits
(`UpCascFitsOK`, `DelFullFitsOK`, cost's). -/
theorem delStepsOKF3_of_open6 (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts))
    (hL : ∀ ts, UpUnlinkLinksOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hFit : ∀ ts BK, UpCascFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) BK)
    (hBel : ∀ ts BK, UpCascBelowOKF3 (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) BK)
    (hLb : ∀ ts BK, UpLebOKF3 (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) BK)
    (hFits : ∀ ts, DelFullFitsOK (ctxOf p ts) (viewOf (treeRun p ts))) : DelStepsOKF3 p R :=
  delStepsOKF3_of_open5 p R hM hsa2 hRL hP
    (fun ts BK => upCascOKF3_of_parts _ _ _ _ (hL ts) (hFit ts BK) (hBel ts BK)) hLb hFits

end SIS.Tree
