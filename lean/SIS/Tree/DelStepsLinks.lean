/-
The links and klongs of the state after the upward loop from its books (bergdb
024-12): `UpUnlinkLinksOK`'s facts hold at every state with the books
(`PutBook`, `putInvG_of_book`), so the stop node's cascade and LE-b need only
`UpUnlinkOK` and the fuel.
-/
import SIS.Tree.TakeLebFull

set_option autoImplicit false

namespace SIS.Tree

open SIS SIS.Check

/-- A state with the books names ids below the next id from every node, and
every node's klongs are well formed. -/
theorem linksWf_of_book (c : Ctx) (base : View BVal) (B : NodeId) (top0 : Top) (v w2 : W)
    (hB : PutBase c base B) (hb : PutBook c B top0 v)
    (hv : v = w2 ∨ ∃ s, v = { w2 with trail := s :: w2.trail }) :
    (∀ u c' z, TLink (wNode c.p base w2) c.i u c' z → z < w2.next) ∧
    (∀ z zn, wNode c.p base w2 z = some zn → klongsWf zn.ks = true) := by
  have hG := putInvG_of_book c base B top0 v hB hb
  have hwv : wNode c.p base v = wNode c.p base w2 := by
    rcases hv with rfl | ⟨s, rfl⟩ <;> rfl
  have hnx : v.next = w2.next := by rcases hv with rfl | ⟨s, rfl⟩ <;> rfl
  refine ⟨fun u c' z ⟨un, hun, hl⟩ => ?_, fun z zn h => ?_⟩
  · rw [← hwv] at hun
    rw [← hnx]
    exact hG.links u un c' z hun hl
  · rw [← hwv] at h
    exact hG.wf z zn h

/-- `UpCascOKF3` from `UpUnlinkOK` and the fuel (`UpCascFitsOK`), the links and
klongs after the loop from the books (`linksWf_of_book`). -/
theorem upCascOKF3_of_parts2 (c : Ctx) (base : View BVal) (KO : KindOracle) (BK : NodeId)
    (hU : UpUnlinkOK c base) (hFit : UpCascFitsOK c base KO BK) : UpCascOKF3 c base KO BK := by
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
    obtain ⟨hT2, hR2⟩ := hU w w3 MB X Nn K depth (D + 1) w2 S hI hr03 hlkX hlinkK hsD hLE
    exact writerWP_upCasc_below_delF3 c base hsa2 KO BK hvB hk hICEk w w3 B MB top0 pre cv rk X Nn K depth D
      w2 v S hB hI hRO hF hr03 hkey hrk hvis hpX hpK hlkX hXN hlinkK hall hleaf hsD hbetween hX0 hLE hv hJ
      hfull hT2 hR2 hlinks2 hwf2 hFits

/-- `UpCascJ2OKF3` from `UpUnlinkOK` and the fuel (`UpCascFitsOK`). -/
theorem upCascJ2OKF3_of_parts2 (c : Ctx) (base : View BVal) (KO : KindOracle) (BK B : NodeId)
    (hU : UpUnlinkOK c base) (hFit : UpCascFitsOK c base KO BK) : UpCascJ2OKF3 c base KO BK B := by
  intro w w3 top0 pre cv rk X Nn K depth stop w2 v S hsa2 hvB hk hICEk hX0 hpos hB hI hRO hF hICE hr03
    hkey hrk hvis hpX hpK hlkX hXN hlinkK hne hall hleaf hdepth hsD hbetween hLE hv hJ hkind hfull hJw
    _hMF hkidsw
  have hRead := upCascOKF3_of_parts2 c base KO BK hU hFit
    w w3 B B top0 pre cv rk X Nn K depth stop w2 v S hsa2 hvB hk hICEk hX0 hB hI hRO hF hICE hr03 hkey
    hrk hvis hpX hpK hlkX hXN hlinkK hne hall hleaf hdepth hsD hbetween hLE hv hJ hkind hfull
  have hBn : B ≤ w.next := by
    have h1 : B ≤ v.next := hJ.1.1.fresh.1
    have h2 : v.next = w2.next := by
      rcases hv with rfl | ⟨s, rfl⟩ <;> rfl
    rw [h2, hLE.2.2.2.2.2.1, hr03.2.2.2.2] at h1
    exact h1
  obtain ⟨hT2, hR2⟩ := hU w w3 B X Nn K depth stop w2 S hI hr03 hlkX hlinkK hsD hLE
  obtain ⟨hlinks2, hwf2⟩ := linksWf_of_book c base B top0 v w2 hB hJ.1.1 hv
  have hJ2 : WriterWP (appendDeleteKlong (X stop) stop (K (stop + 1))) c v
      (fun _ w' => TakeJ2 c base B w' ∧ B ≤ w'.next) := by
    rcases Nat.eq_zero_or_pos stop with hs | hs
    · subst hs
      exact writerWP_upCasc_root_j2 c base hB.coherent hsa2 B hpos w w3 X Nn K depth w2 v S hI hr03 hJw
        hBn hkidsw hlkX hXN hlinkK hdepth hbetween hX0 hLE hv hfull hT2 hlinks2 hwf2
    · obtain ⟨D, rfl⟩ : ∃ D, stop = D + 1 := ⟨stop - 1, by omega⟩
      exact writerWP_upCasc_below_j2 c base hsa2 B hpos w w3 X Nn K depth D w2 v S hI hRO hr03 hJw hBn
        hkidsw hpX hpK hlkX hXN hlinkK hsD hbetween hX0 hLE hv hJ.2 hfull hT2 hR2 hlinks2 hwf2
  exact writerWP_mono (writerWP_and hRead hJ2) (fun _ w' h => ⟨h.1, h.2.1, h.2.2⟩)

/-- `UpLebFullOKF3` from `UpUnlinkOK` and the fuel (`UpLebFitsOK`). -/
theorem upLebFullOKF3_of_parts2 (c : Ctx) (base : View BVal) (KO : KindOracle) (BK : NodeId)
    (hU : UpUnlinkOK c base) (hFit : UpLebFitsOK c base KO BK) : UpLebFullOKF3 c base KO BK := by
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
    obtain ⟨hT2, _⟩ := hU w w3 MB X Nn K depth (D + 1) w2 S hI hr03 hlkX hlinkK hsD hLE
    exact writerWP_upLebFull_below_delF3 c base hsa2 KO BK hICEk w w3 B MB top0 pre cv rk X Nn K depth D
      w2 S hB hI hRO hF hr03 hkey hrk hvis hpX hpK hlkX hXN hlinkK hall hleaf hsD hbetween hX0 hLE hsl hK0
      hT2 hlinks2 hwf2 compact s t c1 y1 r hks hFits

/-- `UpLebFullJ2OK` from `UpUnlinkOK`. -/
theorem upLebFullJ2OK_of_parts2 (c : Ctx) (base : View BVal) (KO : KindOracle) (BK B : NodeId)
    (hU : UpUnlinkOK c base) : UpLebFullJ2OK c base KO BK B := by
  intro w w3 top0 pre cv rk X Nn K depth stop w2 S hsa2 hvB hk hICEk hX0 hpos hB hI hRO hF hICE hr03 hkey
    hrk hvis hpX hpK hlkX hXN hlinkK hne hall hleaf hdepth hsD hbetween hLE hJ hsl hK0 hsm hJw _hMF hkidsw
    compact s t c1 y1 r hks
  have hBn : B ≤ w.next := by
    have h1 : B ≤ w2.next := hJ.1.1.fresh.1
    rw [hLE.2.2.2.2.2.1, hr03.2.2.2.2] at h1
    exact h1
  obtain ⟨hT2, _⟩ := hU w w3 B X Nn K depth stop w2 S hI hr03 hlkX hlinkK hsD hLE
  obtain ⟨hlinks2, hwf2⟩ := linksWf_of_book c base B top0 w2 w2 hB hJ.1.1 (Or.inl rfl)
  rcases Nat.eq_zero_or_pos stop with hs | hs
  · subst hs
    exact writerWP_upLebFull_root_j2 c base hB.coherent hsa2 B hpos w w3 X Nn K depth w2 S hI hr03 hJw hBn
      hkidsw hlkX hXN hlinkK hdepth hbetween hX0 hLE hK0 hT2 hlinks2 hwf2 compact s t c1 y1 r hks
  · obtain ⟨D, rfl⟩ : ∃ D, stop = D + 1 := ⟨stop - 1, by omega⟩
    exact writerWP_upLebFull_below_j2 c base hsa2 B hpos w w3 X Nn K depth D w2 S hI hRO hr03 hJw hBn hkidsw
      hpX hpK hlkX hXN hlinkK hsD hbetween hX0 hLE hsl hK0 hT2 hlinks2 hwf2 compact s t c1 y1 r hks

/-- `DelStepsOKF3` with the upward delete's stop node proved at every stop and
kind: open are the state after the upward loop as a tree in order
(`UpUnlinkOK`) and the fuel after the splits (`UpCascFitsOK`, `UpLebFitsOK`,
`DelFullFitsOK`). -/
theorem delStepsOKF3_of_open10 (p : Params) (R : Struct BVal → Time → Prop) (hM : 2 ≤ p.M)
    (hsa2 : 2 ≤ p.splitAbove)
    (hRL : ∀ P t, R P t → RunLinksOK p P t)
    (hP : ∀ ts, Within p ts → PointersOK (treeRun p ts))
    (hU : ∀ ts, UpUnlinkOK (ctxOf p ts) (viewOf (treeRun p ts)))
    (hFit : ∀ ts BK, UpCascFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) BK)
    (hFitL : ∀ ts BK, UpLebFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) BK)
    (hFits : ∀ ts, DelFullFitsOK (ctxOf p ts) (viewOf (treeRun p ts))) : DelStepsOKF3 p R :=
  delStepsOKF3_of_open5 p R hM hsa2 hRL hP
    (fun ts BK => upCascOKF3_of_parts2 _ _ _ _ (hU ts) (hFit ts BK))
    (fun ts BK => upLebOKF3_of_full _ _ _ _ (upLebFullOKF3_of_parts2 _ _ _ _ (hU ts) (hFitL ts BK))) hFits

/-- `DelStepsJ2OKF3` (the F3 route over R's pointers and kinds) with the upward
delete's stop node proved at every stop and kind: open are `UpUnlinkOK`, the
fuel after the splits (`UpCascFitsOK`, `UpLebFitsOK`, `DelFullFitsOK`) and the
S inputs. -/
theorem delStepsJ2OKF3_of_openR5 (p : Params) (R : Struct BVal → Time → Prop)
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
    (hFit : ∀ ts BK, UpCascFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) BK)
    (hFitL : ∀ ts BK, UpLebFitsOK (ctxOf p ts) (viewOf (treeRun p ts)) (kindOracleOf p (treeRun p ts)) BK)
    (hFits : ∀ ts, DelFullFitsOK (ctxOf p ts) (viewOf (treeRun p ts))) :
    DelStepsJ2OKF3 p R S :=
  delStepsJ2OKF3_of_openR p R S hM hsa2 hRL hRP hRK hSI hSV hSB hSR hSF hSM
    (fun ts BK B => upCascJ2OKF3_of_parts2 _ _ _ _ B (hU ts) (hFit ts BK))
    (fun ts BK B => upLebJ2OKF3_of_full _ _ _ _ B (upLebFullOKF3_of_parts2 _ _ _ _ (hU ts) (hFitL ts BK))
      (upLebFullJ2OK_of_parts2 _ _ _ _ B (hU ts))) hFits

end SIS.Tree
