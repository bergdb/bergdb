/-
cost's `UpHolderOK` at the upward loop's end from its first part (bergdb
024-12): the times of the cached nodes come from the books (`putInvG_of_book`),
and a chain node taken back is the transaction's (`ChainFateW`, the node's books
at the descent's end, `blank_of_firstTime`). Named stays only that no node not
taken back holds a taken-back node (`UpHolderLiveRunOK`).
-/
import SIS.Tree.DelStepsHolder

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- Named input (the take-back's; cost's `UpHolderOK`'s first part, checked on
runs at 2529 loop ends): at the upward loop's end no node not taken back holds,
by a live klong now or before the transaction, a node taken back. -/
def UpHolderLiveRunOK (c : Ctx) (base : View BVal) : Prop :=
  ∀ (w w3 : W) (MB : NodeId) (X : Nat → NodeId) (Nn : Nat → KNode) (K : Nat → Nat) (depth stop : Nat)
    (w2 : W) (S : KNode),
    PutInv c base w → ReadsAs c.p base w w3 →
    (∀ i, i ≤ depth → w3.nodes.lookup (X i) = some (Nn i)) →
    (∀ i, 0 < i → i ≤ depth → (K i, X i) ∈ (Nn (i - 1)).liveAt c.i) → stop < depth →
    UpLoopEnd c MB X Nn depth stop w3 w2 S →
    ∀ y n, w2.nodes.lookup y = some n → w2.taken.contains y = false →
      ∀ cv z, ((cv, z) ∈ n.live ∨ (cv, z) ∈ (n.toPrev (c.i - 1)).live) → w2.taken.contains z = false

/-- `UpHolderOK` from its first part: the times from the books at the loop's
end, the chain nodes taken back the transaction's by the kinds' books at the
descent's end. -/
theorem upHolderOK_of_live (c : Ctx) (base : View BVal) (KO : KindOracle) (BK B : NodeId) (top0 : Top)
    (H : NodeId → Nat → Prop) (w3 : W) (MB : NodeId) (X : Nat → NodeId) (Nn : Nat → KNode)
    (depth stop : Nat) (w2 v : W) (S : KNode)
    (hB : PutBase c base B) (hJ3H : KdHtJ c B top0 KO BK H w3)
    (hlkX : ∀ i, i ≤ depth → w3.nodes.lookup (X i) = some (Nn i))
    (hLE : UpLoopEnd c MB X Nn depth stop w3 w2 S)
    (hv : v = w2 ∨ ∃ s, v = { w2 with trail := s :: w2.trail })
    (hbv : PutBook c B top0 v)
    (hA : ∀ y n, w2.nodes.lookup y = some n → w2.taken.contains y = false →
      ∀ cv z, ((cv, z) ∈ n.live ∨ (cv, z) ∈ (n.toPrev (c.i - 1)).live) → w2.taken.contains z = false) :
    UpHolderOK c BK X depth stop w2 := by
  refine ⟨hA, ?_, ?_⟩
  · intro y n hy ht s hs
    have hG := putInvG_of_book c base B top0 v hB hbv
    have hwv : wNode c.p base v = wNode c.p base w2 := by
      rcases hv with rfl | ⟨s, rfl⟩ <;> rfl
    have hyn : wNode c.p base w2 y = some n := by
      simp only [wNode, ht, Bool.false_eq_true, ↓reduceIte, hy]
    rw [← hwv] at hyn
    exact hG.times y n hyn s hs
  · intro k h1 h2 htk
    have hfw := hLE.2.2.2.2.2.2.2.2.2.2.2.2 k h1 h2
    have hft : (Nn k).firstTime = some c.i := by
      rcases Classical.em ((Nn k).firstTime = some c.i) with h | hne
      · exact h
      · have := (hfw.2 hne).1
        rw [this] at htk
        cases htk
    have hgood := cacheGood_lookup B c w3 hJ3H.1.1.good (X k) (Nn k) (hlkX k h2)
    have hbk : Book BK c w3 := hJ3H.1.2.1
    have hmem : X k ∈ w3.nodes.map (·.1) := by
      obtain ⟨pre, post, he, _⟩ := List.lookup_eq_some_iff.mp (hlkX k h2)
      rw [he]; simp
    rw [hbk.ids] at hmem
    obtain ⟨⟨x', g, h⟩, hq, hx'⟩ := List.mem_map.mp (List.mem_reverse.mp hmem)
    simp only at hx'
    subst hx'
    rcases hbk.tag (X k) g h hq with ⟨nd, hnd, hd, hl, _, _⟩ | ⟨hge, _, _⟩
    · exfalso
      have hbl := blank_of_firstTime B c (X k) (Nn k) hB.good.pos hgood (by simp [hft])
      have hb := hbl.1
      simp only [baseKlongs, hnd] at hb
      exact hB.good.nonempty (X k) nd hnd hd hl hb
    · exact hge

/-- `UpCascOKF3H` with `UpHolderOK` from its first part. -/
theorem upCascOKF3H_of2 (c : Ctx) (base : View BVal) (KO : KindOracle) (BK : NodeId) (H : NodeId → Nat → Prop)
    (hU : UpUnlinkTreeOK c base) (hHL : UpHolderLiveRunOK c base) (hG : UpGhOK c base)
    (hFitR : UpCascFitsOKR c base KO BK H) : UpCascOKF3H c base KO BK H := by
  intro w w3 B MB top0 pre cv rk X Nn K depth stop w2 v S hm hLC hJ3H hlen hsa2 hvB hk hICEk hX0 hB hI hRO hF hICE hr03 hkey
    hrk hvis hpX hpK hlkX hXN hlinkK hne hall hleaf hdepth hsD hbetween hLE hv hJ hkind hfull
  obtain ⟨hlinks2, hwf2⟩ := linksWf_of_book c base B top0 v w2 hB hJ.1.1 hv
  have hFits := hFitR w w3 B MB top0 pre cv rk X Nn K depth stop w2 v S hm hLC hJ3H hlen
    (hG w w3 MB X Nn K depth stop w2 S hI hr03 hlkX hlinkK hsD hLE)
    (upHolderOK_of_live c base KO BK B top0 H w3 MB X Nn depth stop w2 v S hB hJ3H hlkX hLE hv hJ.1.1
      (hHL w w3 MB X Nn K depth stop w2 S hI hr03 hlkX hlinkK hsD hLE)) hsa2 hvB hk hICEk hX0 hB hI hRO hF
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

/-- `UpCascJ2OKF3H` with `UpHolderOK` from its first part. -/
theorem upCascJ2OKF3H_of2 (c : Ctx) (base : View BVal) (KO : KindOracle) (BK B : NodeId) (H : NodeId → Nat → Prop)
    (hU : UpUnlinkTreeOK c base) (hHL : UpHolderLiveRunOK c base) (hG : UpGhOK c base)
    (hFitR : UpCascFitsOKR c base KO BK H) : UpCascJ2OKF3H c base KO BK B H := by
  intro w w3 top0 pre cv rk X Nn K depth stop w2 v S hm hLC hJ3H hlen hsa2 hvB hk hICEk hX0 hpos hB hI hRO hF hICE hr03
    hkey hrk hvis hpX hpK hlkX hXN hlinkK hne hall hleaf hdepth hsD hbetween hLE hv hJ hkind hfull hJw
    _hMF hkidsw
  have hRead := upCascOKF3H_of2 c base KO BK H hU hHL hG hFitR
    w w3 B B top0 pre cv rk X Nn K depth stop w2 v S hm hLC hJ3H hlen hsa2 hvB hk hICEk hX0 hB hI hRO hF hICE hr03 hkey
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

theorem delStepsCaseOKF3_emptyCascLH2 (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts))
    (hRK : ∀ P t, R P t → KindsAllOK p P) (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (hht : OpHtDelOKUnder p R) (hdel : TakeBelowFuelDelOK p)
    (hU : ∀ ts, UpUnlinkTreeOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hHL : ∀ ts, UpHolderLiveRunOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hG : ∀ ts, UpGhOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hLC : StateOK p R (fun ts _ w => LiveCountsW p ts w)) :
    DelStepsCaseOKF3 p R DelEmptyCascM := by
  intro ts tx hw hr z top hz htop ops op post hops r w hpre hI hRO hF key hop hPc hA hMU hCR
  have hLCw := hLC ts tx hw hr z top hz htop ops (op :: post) hops r w hpre
  obtain ⟨pre, cv, L0, n0, hop', hm, hK, hne0, hall0, P0, hP0, hX0, hl0, _⟩ := hPc
  subst hop'
  cases hop
  obtain ⟨hvo, hkw, hbase, hHb, _, hhi, hwfw, hub⟩ := htStart_reachedU p hM R hRL hRK hRH hht hdel ts tx hw hr z top
    hz htop ops (.del (pre ++ [cv]) :: post) hops r w hpre
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  have hICE := innerChildren_reached p hM hP ts tx hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
    (fun x hx => hI.untaken x (tReach_reachS _ _ _ _ hx))
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_context p hM hP ts tx hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
  have hwts : Within p ts := by
    have := within_take p (ts ++ [tx]) hw ts.length
    simpa using this
  have hKall := treeRun_kindsAllOK p hM hP ts hwts
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl hKall
      (hP ts hwts) hb hi.cache hun
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
  refine writerWP_del_emptyAnyMKLH (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w tx.base top hB hbook
    _ tx.base hv hk hb0 hi0 hI hRO hF hICE hkey hrk (keyLeaf_all2 hK hrk _ ⟨hne0, hall0, hLr⟩)
    _ (upCascOKF3H_of2 _ _ _ _ _ (hU ts) (hHL ts) (hG ts)
      (upCascFitsOKR_of _ _ _ _ _ hvo hbase hHb (by simp [ctxOf]))) hLCw hvo hkw hhi hwfw hub
    (by simpa [ctxOf] using hsa2) hICEk hm (by simp [ctxOf]) hA hMU hCR
    _ (fun v hv' => by unfold fresh; wpSimplify; exact hv') ?_
  intro v hv' hFv key' hk'
  have := runGet_of_delInvF p ts w v (pre ++ [cv]) hv'.1 hI hF hFv key' hk'
  simpa [Op.key, Op.value] using this

theorem delStepsCaseJ2OKF3_emptyCascRLH2 (p : Params) (R : Struct BVal → Time → Prop)
    (S : List Tx → Tx → W → Prop) (hM : 2 ≤ p.M) (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (hSI : ∀ ts tx w, S ts tx w → PutInv (ctxOf p ts) (viewOf (treeRun p ts)) w)
    (hSV : ∀ ts tx w, S ts tx w → LeafVals (ctxOf p ts) (viewOf (treeRun p ts)) tx.base w)
    (hSR : ∀ ts tx w, S ts tx w →
      RangeOrder (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) w.top.rootKey)
    (hSF : ∀ ts tx w, S ts tx w →
      SegFits (wNode p (viewOf (treeRun p ts)) w) (ts.length + 1) (p.fuel - 1) w.top.rootKey)
    (hSM : ∀ ts tx w, S ts tx w → ∀ x o, w.madeFor.lookup x = some o → o < tx.base)
    (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (hht : OpHtDelOKUnder p R) (hdel : TakeBelowFuelDelOK p)
    (hU : ∀ ts, UpUnlinkTreeOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hHL : ∀ ts, UpHolderLiveRunOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hG : ∀ ts, UpGhOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hLC : StateOK p R (fun ts _ w => LiveCountsW p ts w)) :
    DelStepsCaseJ2OKF3 p R S DelEmptyCascM := by
  intro ts tx hw hr z top hz htop ops op post hops r w hpre hS hJ key hop hPc hA hMU hCR
  have hLCw := hLC ts tx hw hr z top hz htop ops (op :: post) hops r w hpre
  obtain ⟨pre, cv, L0, n0, hop', hm, hK, hne0, hall0, P0, hP0, hX0, hl0, _⟩ := hPc
  subst hop'
  cases hop
  obtain ⟨hvo, hkw, hbase, hHb, _, hhi, hwfw, hub⟩ := htStart_reachedU p hM R hRL hRK hRH hht hdel ts tx hw hr z top
    hz htop ops (.del (pre ++ [cv]) :: post) hops r w hpre
  have hI := hSI ts tx w hS
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  have hICE := innerChildren_reachedR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
    (fun x hx => hI.untaken x (tReach_reachS _ _ _ _ hx))
  have hLV := leafVals_all (hSV ts tx w hS) hkey hrk
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl (hRK _ _ hr)
      (hRP _ _ hr) hb hi.cache hun
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
  exact writerWP_del_emptyAnyMJKLH (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w tx.base top hB hbook
    _ tx.base hv hk hb0 hi0
    hI (hSR ts tx w hS) (hSF ts tx w hS) hICE hkey hrk (keyLeaf_all2 hK hrk _ ⟨hne0, hall0, hLr⟩)
    _ (upCascJ2OKF3H_of2 _ _ _ _ _ _ (hU ts) (hHL ts) (hG ts)
      (upCascFitsOKR_of _ _ _ _ _ hvo hbase hHb (by simp [ctxOf]))) hLCw hvo hkw hhi hwfw hub
    (by simpa [ctxOf] using hsa2) hICEk hm
    (by simp [ctxOf]) hJ (hSM ts tx w hS) (fun L n hL hn hnl y hy => (hLV L n hL hn hnl y hy).1) hA hMU hCR

theorem delStepsCaseQd_emptyCascLH2 (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (hht : OpHtDelOKUnder p R) (hdel : TakeBelowFuelDelOK p)
    (hU : ∀ ts, UpUnlinkTreeOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hHL : ∀ ts, UpHolderLiveRunOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hG : ∀ ts, UpGhOK (ctxOf p ts) (viewOf (treeRun p ts)))
    : DelStepsCaseQd p R DelEmptyCascML := by
  intro ts tx hw hr z top hz htop ops op post hops r w hpre hI hRO hF key hop hPcL hA hMU hCR
  obtain ⟨hPc, hLCw⟩ := hPcL
  obtain ⟨pre, cv, L0, n0, hop', hm, hK, hne0, hall0, P0, hP0, hX0, hl0, _⟩ := hPc
  subst hop'
  cases hop
  obtain ⟨hvo, hkw, hbase, hHb, _, hhi, hwfw, hub⟩ := htStart_reachedU p hM R hRL hRK hRH hht hdel ts tx hw hr z top
    hz htop ops (.del (pre ++ [cv]) :: post) hops r w hpre
  have hkey : keyWf (pre ++ [cv]) = true := within_op_keyWf p ts tx hw ops _ post hops
  obtain ⟨rk, hrk, _⟩ := keyLeaf_rk hK
  have hB := putBase_of_run p ts tx hw (hRL _ _ hr)
  have hbook := putBook_reached p ts tx hw (hRL _ _ hr) z top htop ops r w hpre
  have hICE := innerChildren_reachedR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
    (fun x hx => hI.untaken x (tReach_reachS _ _ _ _ hx))
  obtain ⟨hv, hk, hb0, hi0⟩ := kd_contextR p hM ts tx (hRP _ _ hr) (hRK _ _ hr) hw top ops (.del (pre ++ [cv]) :: post) hops r w hpre
  have hwts : Within p ts := by
    have := within_take p (ts ++ [tx]) hw ts.length
    simpa using this
  have hKall := hRK _ _ hr
  have hICEk : ICEFromKinds (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) tx.base :=
    fun v hb hi hun => innerChildren_of_kinds p (treeRun p ts) tx.base (ctxOf p ts) v rfl hKall
      (hRP _ _ hr) hb hi.cache hun
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
  refine writerWP_del_emptyAnyMKLH (ctxOf p ts) _ (viewCoherent_ctxOf p ts) pre cv rk w tx.base top hB hbook
    _ tx.base hv hk hb0 hi0 hI hRO hF hICE hkey hrk (keyLeaf_all2 hK hrk _ ⟨hne0, hall0, hLr⟩)
    _ (upCascOKF3H_of2 _ _ _ _ _ (hU ts) (hHL ts) (hG ts)
      (upCascFitsOKR_of _ _ _ _ _ hvo hbase hHb (by simp [ctxOf]))) hLCw hvo hkw hhi hwfw hub
    (by simpa [ctxOf] using hsa2) hICEk hm (by simp [ctxOf]) hA hMU hCR
    (QdW p ts) (fun v hv' => qdW_fresh p ts v hv') (fun v hv' => ⟨hv'.1.1, hv'.1.2.2.1⟩)

/-- `DelStepsOKF3` with the fill at every operation's start (`hLC`) and the fuel
after the stop node's split from the heights (cost's `upCascFitsOKR_of`): open
are the state after the upward loop as a tree (`UpUnlinkTreeOK`), holding no taken-back node
(`UpHolderLiveRunOK`) and keeping the heights' cache (`UpGhOK`), and the
heights at every run. -/
theorem delStepsOKF3_of_open15 (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts))
    (hRK : ∀ P t, R P t → KindsAllOK p P) (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (hht : OpHtDelOKUnder p R) (hdel : TakeBelowFuelDelOK p)
    (hU : ∀ ts, UpUnlinkTreeOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hHL : ∀ ts, UpHolderLiveRunOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hG : ∀ ts, UpGhOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hLC : StateOK p R (fun ts _ w => LiveCountsW p ts w)) :
    DelStepsOKF3 p R :=
  delStepsOKF3_of_cases p R (delStepsCaseOKF3_noLeaf p R) (delStepsCaseOKF3_noop p R)
    (delStepsCaseOKF3_or p R _ _ _ delEmptyM_split (delStepsCaseOKF3_emptyRoom p R hM hRL hP)
      (delStepsCaseOKF3_or p R _ _ _ delEmptyOther_split (delStepsCaseOKF3_emptyRoot p R hM hsa2 hRL hP)
        (delStepsCaseOKF3_emptyCascLH2 p R hM hsa2 hRL hP hRK hRH hht hdel hU hHL hG hLC)))
    (delStepsCaseOKF3_room p R hM hRL hP)
    (delStepsCaseOKF3_fullH p R hM hsa2 hRL hP hRK hRH hht hdel (fun ts => delFullRootStepOK_ctx p ts))

/-- `DelStepsJ2OKF3` (the F3 route over R's pointers and kinds) with the fill
at every operation's start and the fuel after the stop node's split from the
heights: open are `UpUnlinkTreeOK`, `UpHolderLiveRunOK`, `UpGhOK`, the heights at
every run and the S inputs. -/
theorem delStepsJ2OKF3_of_openR10 (p : Params) (R : Struct BVal → Time → Prop)
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
    (hRH : ∀ P t, R P t → HeightAllOK p P t) (hht : OpHtDelOKUnder p R) (hdel : TakeBelowFuelDelOK p)
    (hU : ∀ ts, UpUnlinkTreeOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hHL : ∀ ts, UpHolderLiveRunOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hG : ∀ ts, UpGhOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hLC : StateOK p R (fun ts _ w => LiveCountsW p ts w)) :
    DelStepsJ2OKF3 p R S :=
  delStepsJ2OKF3_of_cases p R S (delStepsCaseJ2OKF3_noLeaf p R S hSI) (delStepsCaseJ2OKF3_noop p R S hSI)
    (delStepsCaseJ2OKF3_or p R S _ _ _ delEmptyM_split
      (delStepsCaseJ2OKF3_emptyRoomR p R S hM hRL hRP hRK hSI hSV hSR hSF hSM)
      (delStepsCaseJ2OKF3_or p R S _ _ _ delEmptyOther_split
        (delStepsCaseJ2OKF3_emptyRootR p R S hM hsa2 hRL hRP hRK hSI hSV hSB hSR)
        (delStepsCaseJ2OKF3_emptyCascRLH2 p R S hM hsa2 hRL hRP hRK hSI hSV hSR hSF hSM hRH hht hdel hU hHL hG
          hLC)))
    (delStepsCaseJ2OKF3_roomR p R S hM hRL hRP hRK hSI hSV hSB hSR hSF)
    (delStepsCaseJ2OKF3_fullRH p R S hM hsa2 hRL hRP hRK hSI hSV hSB hSR hSF hRH hht hdel)

/-- `DelStepsQdL` with the fuel after the stop node's split from the heights:
open are `UpUnlinkTreeOK`, `UpHolderLiveRunOK`, `UpGhOK` and the heights at every
run. -/
theorem delStepsQdL_of_openR3 (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hRP : ∀ P t, R P t → PointersOK P) (hRK : ∀ P t, R P t → KindsAllOK p P)
    (hRH : ∀ P t, R P t → HeightAllOK p P t)
    (hht : OpHtDelOKUnder p R) (hdel : TakeBelowFuelDelOK p)
    (hU : ∀ ts, UpUnlinkTreeOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hHL : ∀ ts, UpHolderLiveRunOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hG : ∀ ts, UpGhOK (ctxOf p ts) (viewOf (treeRun p ts))) :
    DelStepsQdL p R := by
  intro ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop hmL hA hMU hCR
  obtain ⟨⟨key', hop', hm'⟩, hLCw⟩ := hmL
  rw [hop] at hop'
  cases hop'
  rcases delMerge_cover (ctxOf p ts) (viewOf (treeRun p ts)) w key hm' with h | h | h | h | h
  · exact delStepsCaseQd_noLeaf p R ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop
      (hop ▸ h) hA hMU hCR
  · exact delStepsCaseQd_noop p R hRL ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop
      (hop ▸ h) hA hMU hCR
  · rcases delEmptyM_split _ _ _ _ h with h1 | h1
    · exact delStepsCaseQd_emptyRoom p R hM hRL hRP hRK ts tx hw hr z top hz htop pre op post hops r w hpre
        hI hRO hF key hop (hop ▸ h1) hA hMU hCR
    · rcases delEmptyOther_split _ _ _ _ h1 with h2 | h2
      · exact delStepsCaseQd_emptyRoot p R hM hsa2 hRL hRP hRK ts tx hw hr z top hz htop pre op post hops r w
          hpre hI hRO hF key hop (hop ▸ h2) hA hMU hCR
      · exact delStepsCaseQd_emptyCascLH2 p R hM hsa2 hRL hRP hRK hRH hht hdel hU hHL hG
          ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop (hop ▸ ⟨h2, hLCw⟩) hA hMU hCR
  · exact delStepsCaseQd_room p R hM hRL hRP hRK ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF
      key hop (hop ▸ h) hA hMU hCR
  · exact delStepsCaseQd_fullH p R hM hsa2 hRL hRP hRK hRH hht hdel (fun ts => delFullRootStepOK_ctx p ts)
      ts tx hw hr z top hz htop pre op post hops r w hpre hI hRO hF key hop (hop ▸ h) hA hMU hCR

/-- `unlink` of a cached node keeps the heights' cache (a step towards
`UpGhOK`). -/
theorem writerWP_unlink_gh (x : NodeId) (c : Ctx) (v : W) (hx : ∃ xn, v.nodes.lookup x = some xn) :
    WriterWP (unlink x) c v (fun _ v' => v'.gh = v.gh) := by
  obtain ⟨xn, hxn⟩ := hx
  unfold unlink
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known x xn c v hxn]
  split
  · simp only [putNode, writerWP_modify]
  · simp only [writerWP_pure]

/-- `takeBack` with the parent cached keeps the heights' cache (a step towards
`UpGhOK`). -/
theorem writerWP_takeBack_gh (x p : NodeId) (k : Nat) (c : Ctx) (v : W)
    (hp : ∃ pn, v.nodes.lookup p = some pn) :
    WriterWP (takeBack x p k) c v (fun _ v' => v'.gh = v.gh) := by
  obtain ⟨pn, hpn⟩ := hp
  unfold takeBack
  simp only [writerWP_bind, writerWP_read]
  rw [writerWP_getNode_known p pn c v hpn]
  unfold replacedBy
  simp only [writerWP_bind, writerWP_get, writerWP_pure]
  split
  · refine writerWP_if _ _ _ _ _ _ (fun _ => ?_) (fun _ => ?_)
    · simp only [writerWP_bind]; exact writerWP_throw _ _ _ _
    · unfold retarget takenBack note
      simp only [writerWP_bind, writerWP_read]
      rw [writerWP_getNode_known p pn c v hpn]
      split
      · simp only [putNode, writerWP_modify]
      · simp only [writerWP_pure, writerWP_modify]
  · exact writerWP_throw _ _ _ _

end SIS.Tree
