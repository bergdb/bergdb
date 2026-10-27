/-
Proofs about reclaim with handles (bergdb 005-62), part 4 of T12 over handles:
one transaction of C, the run with handles after a restart from a cut stream,
against one of E, after the restart from the whole stream at the same point:
the same record, and memories that differ only in the root's object again
(`handleTrans_sim`, as `evictTrans_sim` of CutLaterTrans.lean); and the reads
and evictions between transactions (`ops_sim`).
-/
import SIS.Proof.HandleCutSim
import SIS.Proof.CutLaterTrans

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

section Trans

variable {sp : Spec V T} {al : Algo V T}

/-- One transaction of C, on the memory with another root object, the cut
streams and the logical state of the run that restarts from cut streams,
against one of E: the same record, and memories that differ only in the root's
object, which holds C's root history. -/
theorem handleTrans_sim (hsp : SpecOK sp) (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true)
    (hex : ExecRootOK sp) (hvl : VirtLiveOK sp) (hpol : PolicyCutOK al)
    {db1 db db' : DB V T} {j1 k c : Nat} (hev : EvLogic sp db k)
    (hL : Later sp db1 db j1 k) (hcut : CutOK sp c db1 j1)
    (hrel : CutRel sp c (lastFa db1.S) k db' db) (hfs : lastFa db.S ≤ lastSp db.S)
    {mE : HMem V} {oc oe : HObj V}
    (hm : HEInv sp db db1.S k mE) (hh : HInvH sp db db1.S k mE) (hc : CInvH sp db db1.S mE)
    (hra : mE.obj? mE.root = some oe) (hr : RootRelH sp (lastFa db1.S) oc oe)
    (hoc : ∀ n, db'.P.get? SIS.root = some n → oc.hist = n.hist)
    {tr : T} (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c)
    (hphys : PhysStep sp db.P (k + 1) (parts sp al db tr).c)
    (hcopy : CopyStep sp db.P (k + 1) (parts sp al db tr).c) (htree : treeAt sp db.P k)
    (hinv' : Inv sp (step sp al db tr) (k + 1)) :
    (handleTrans sp al (cutStream c db1.S) db' (mE.withRoot oc) tr).1 = step sp al db' tr ∧
      ∃ oc' oe', (handleTrans sp al (cutStream c db1.S) db' (mE.withRoot oc) tr).2 =
          (handleTrans sp al db1.S db mE tr).2.withRoot oc' ∧
        (handleTrans sp al db1.S db mE tr).2.obj? (handleTrans sp al db1.S db mE tr).2.root = some oe' ∧
        RootRelH sp (lastFa db1.S) oc' oe' ∧
        ∀ n, (step sp al db' tr).P.get? SIS.root = some n → oc'.hist = n.hist := by
  have hinv := hL.inv
  have hls : LiveSub sp := hsp.liveSub
  have hlen := hinv.len
  have hlen' : db'.S.length = k + 1 := by rw [hrel.stream, cutStream_length, hlen]
  have hK1 : k + 1 - 1 = k := by omega
  have hft : lastFa db1.S ≤ k := by have := hrel.fa; have := hfs; have := hinv.spLt; omega
  have hcs : c ≤ mE.s := by
    rw [hm.sEq]
    exact Nat.le_trans hcut.1 hL.fa1
  have hstep_e : StepOK sp db.P (k + 1) (sp.exec tr (k + 1) (view sp db.P k)) := by
    have := hstep; rw [parts_c, hlen, hK1] at this; exact this
  obtain ⟨-, hcq, hvs0, hD1, htaken, hvs, -⟩ :=
    step_congr_cut sp al hsp hinv hj hmk hex hvl hpol hrel hfs tr hstep_e
  -- E's root object holds the root's history.
  obtain ⟨o0, ho0, hc0, hn0⟩ := hm.root
  rw [hra, Option.some.injEq] at ho0
  subst ho0
  obtain ⟨n0, hn0', hoe0, -, -⟩ := hm.cc mE.root oe hra hc0
  rw [hn0] at hn0'
  -- the view
  obtain ⟨hm1, hv⟩ := hm.view_ok hinv hls hev
  have hh1 : HInvH sp db db1.S k (mE.view sp db1.S db.S k).1 := hh.read hinv hm k
  have hc1 : CInvH sp db db1.S (mE.view sp db1.S db.S k).1 := hc.read hinv hm k
  obtain ⟨oc1, oe1, tail, hrd, hlE, hra1, hr1, hhc1⟩ :=
    hc.read_sim hL hls hm hh hcut hft (Nat.le_refl k) hft hra hr
  have hcE : sp.exec tr (k + 1) (mE.view sp db1.S db.S k).2 = (parts sp al db tr).c := by
    rw [hv, parts_c, hlen, hK1]
  have hcC : sp.exec tr (k + 1) ((mE.withRoot oc).view sp (cutStream c db1.S) db'.S k).2 =
      (parts sp al db tr).c := by
    rw [← hcE]
    show sp.exec tr (k + 1) (fun x => ((mE.withRoot oc).read sp (cutStream c db1.S) db'.S k).2.lookup x) =
      sp.exec tr (k + 1) (fun x => (mE.read sp db1.S db.S k).2.lookup x)
    rw [hrel.stream, hrd, hlE]
    apply exec_rootSwap hex
    · intro hv' e he
      exact hr.vals hv' e (mem_upTo.mp he).1
    · intro hv' e he
      have he' : e ∈ oe.hist := (mem_upTo.mp he).1
      rw [hoe0] at he'
      obtain ⟨z, -, -, hval⟩ := (hinv.vr hv').rootEntry n0 hn0' e he'
      exact ⟨z, hval⟩
    · exact hr.live k hft
    · intro hv'; rw [hr.nv hv']
  rw [handleTrans_eq, handleTrans_eq, hlen', hlen, hK1, hcC, hcE, handleAfter_eq, handleAfter_eq, hlen', hlen]
  have hview1 : ((mE.withRoot oc).view sp (cutStream c db1.S) db'.S k).1 =
      (mE.view sp db1.S db.S k).1.withRoot oc1 := by
    show ((mE.withRoot oc).read sp (cutStream c db1.S) db'.S k).1 = (mE.read sp db1.S db.S k).1.withRoot oc1
    rw [hrel.stream, hrd]
  rw [hview1]
  have hra1' : (mE.view sp db1.S db.S k).1.obj? (mE.view sp db1.S db.S k).1.root = some oe1 := hra1
  generalize (mE.view sp db1.S db.S k).1 = m1E at hm1 hh1 hc1 hra1' ⊢
  -- E's root object after the read holds the root's history.
  obtain ⟨o1', ho1', hco1', hno1'⟩ := hm1.root
  rw [hra1', Option.some.injEq] at ho1'
  subst ho1'
  obtain ⟨n1, hn1, hoe1, -, -⟩ := hm1.cc m1E.root oe1 hra1' hco1'
  rw [hno1', hn0', Option.some.injEq] at hn1
  subst hn1
  -- The writer's paths, the same in both.
  have hroot : sp.virt = true → ∀ n, db.P.get? SIS.root = some n → ∀ e ∈ n.hist, ∃ z, e.val = sp.rootVal z := by
    intro hv n hn e he
    obtain ⟨z, -, -, hval⟩ := (hinv.vr hv).rootEntry n hn e he
    exact ⟨z, hval⟩
  have hadds : sp.virt = true → ∀ a ∈ (parts sp al db tr).c.adds, a.1 = SIS.root → ∃ z, a.2 = sp.rootVal z :=
    fun hv => (hstep.virt hv).root_adds
  have hag1 : CutAgree sp (lastFa db1.S) (k + 1) (db.P.apply (k + 1) (parts sp al db tr).c)
      (db'.P.apply (k + 1) (parts sp al db tr).c) :=
    hrel.agree.apply hft hls hinv.ptrs hinv.times hstep hvl hroot hadds
  have hPapp : (step sp al db tr).P = db.P.apply (k + 1) (parts sp al db tr).c := by
    rw [step_eq_parts]; exact parts_P' sp al db tr hlen
  have hp' : PtrsOK sp (db.P.apply (k + 1) (parts sp al db tr).c) := by rw [← hPapp]; exact hinv'.ptrs
  have hpatheq : pathOf sp db'.P (parts sp al db tr).c (k + 1) = pathOf sp db.P (parts sp al db tr).c (k + 1) :=
    hrel.agree.pathOf_eq hag1 hls hinv.ptrs hp' hft
  have hpr : ∀ p ∈ pathOf sp db.P (parts sp al db tr).c (k + 1), reachable sp db.P k p = true := by
    intro p hp; have := (mem_pathOf hp).1; rw [hK1] at this; exact this
  have hsorteq : (pathOf sp db.P (parts sp al db tr).c (k + 1)).mergeSort (fun a b => decide
      (((db'.P.get? b).map (·.level)).getD 0 ≤ ((db'.P.get? a).map (·.level)).getD 0)) =
      (pathOf sp db.P (parts sp al db tr).c (k + 1)).mergeSort (fun a b => decide
      (((db.P.get? b).map (·.level)).getD 0 ≤ ((db.P.get? a).map (·.level)).getD 0)) := by
    apply mergeSort_congr
    intro a ha b hb
    have e1 := hrel.agree.lev_eq hft (Nat.le_refl _) (hpr a ha)
    have e2 := hrel.agree.lev_eq hft (Nat.le_refl _) (hpr b hb)
    unfold lev at e1 e2
    rw [e1, e2]
  -- E's walk and change, as in `HEInv.handleTrans_ok`.
  have hparent : ∀ x ∈ pathOf sp db.P (parts sp al db tr).c (k + 1), x ≠ SIS.root →
      ∃ p ∈ pathOf sp db.P (parts sp al db tr).c (k + 1), ∃ np nx, db.P.get? p = some np ∧
        db.P.get? x = some nx ∧ nx.level < np.level ∧ x ∈ sp.live (np.hist.upTo k) := by
    intro x hx hxr
    have hrx := hpr x hx
    obtain ⟨p, np, nx, hrp, hnp, hnx, hlt, hxl⟩ := reach_parent hrx hxr
    refine ⟨p, pathOf_parent hx (by rw [hK1]; exact hrp) hnp (by rw [hK1]; exact hxl) hnx hlt, np, nx, hnp, hnx,
      hlt, hxl⟩
  have hpnd : (pathOf sp db.P (parts sp al db tr).c (k + 1)).Nodup := by
    unfold pathOf; exact nodup_filter (nodup_eraseDups _) _
  have hsorted := pairwise_byLevelDesc db.P (pathOf sp db.P (parts sp al db tr).c (k + 1))
  obtain ⟨hm2, hpd⟩ := HEInv.reachPath_ok (S0 := db1.S) hinv hls hev hpr hparent
    ((pathOf sp db.P (parts sp al db tr).c (k + 1)).mergeSort (fun a b => decide (lev db.P b ≤ lev db.P a))) []
    m1E hm1 (fun a ha => by cases ha)
    (fun x => by rw [List.nil_append]; exact (List.mergeSort_perm _ _).mem_iff)
    (by rw [List.nil_append]; exact (List.mergeSort_perm _ _).nodup_iff.mpr hpnd)
    (by rw [List.nil_append]; exact hsorted)
  have ha := hm2.applyChange_ok hinv hls hpd hstep hphys hcopy htree
  -- C's walk: E's.
  have hP : ∀ p ∈ pathOf sp db.P (parts sp al db tr).c (k + 1),
      (db'.P.get? p).map (fun n => sp.live (n.hist.upTo (k + 1 - 1))) =
        (db.P.get? p).map (fun n => sp.live (n.hist.upTo (k + 1 - 1))) := by
    intro p hp; rw [hK1]; exact hrel.agree.live_eq hft (Nat.le_refl _) (hpr p hp)
  have hPr1 : ∀ n, db.P.get? SIS.root = some n → ∀ x ∈ sp.live (n.hist.upTo k), x ∈ pointees sp oc1.hist := by
    intro n hn x hx
    rw [hn0', Option.some.injEq] at hn
    subst hn
    rw [← hoe1, ← hr1.live k hft] at hx
    exact mem_pointees_of_live hls hx
  have hwalkC : ((pathOf sp db.P (parts sp al db tr).c (k + 1)).mergeSort
      (fun a b => decide (lev db.P b ≤ lev db.P a))).foldl
      (HMem.reachOnPath sp (cutStream c db1.S) (cutStream c db.S) db'.P (k + 1)
        (pathOf sp db.P (parts sp al db tr).c (k + 1))) (m1E.withRoot oc1) =
      ((pathOf sp db.P (parts sp al db tr).c (k + 1)).mergeSort
      (fun a b => decide (lev db.P b ≤ lev db.P a))).foldl
      (HMem.reachOnPath sp (cutStream c db1.S) (cutStream c db.S) db.P (k + 1)
        (pathOf sp db.P (parts sp al db tr).c (k + 1))) (m1E.withRoot oc1) := by
    have hfun : HMem.reachOnPath sp (cutStream c db1.S) (cutStream c db.S) db'.P (k + 1)
        (pathOf sp db.P (parts sp al db tr).c (k + 1)) = HMem.reachOnPath sp (cutStream c db1.S)
        (cutStream c db.S) db.P (k + 1) (pathOf sp db.P (parts sp al db tr).c (k + 1)) := by
      funext m x
      exact HMem.reachOnPath_congrP hP _ _ m x
    rw [hfun]
  obtain ⟨oc2, oe2, hw1, hra2, hr2, hh2⟩ := HEInv.reachPath_sim hL hls hev hcut hpr
    ((pathOf sp db.P (parts sp al db tr).c (k + 1)).mergeSort (fun a b => decide (lev db.P b ≤ lev db.P a)))
    m1E oc1 oe1 hm1 hra1' hr1 hPr1
  generalize hW : ((pathOf sp db.P (parts sp al db tr).c (k + 1)).mergeSort
    (fun a b => decide (lev db.P b ≤ lev db.P a))).foldl
      (HMem.reachOnPath sp db1.S db.S db.P (k + 1) (pathOf sp db.P (parts sp al db tr).c (k + 1))) m1E = m2E
    at hw1 hra2 hm2 hpd ha
  -- The change on C's memory: E's.
  have hReach : ∀ x, reachable sp db'.P (k + 1 - 1) x = reachable sp db.P (k + 1 - 1) x := by
    intro x; rw [hK1]; exact hrel.agree.reachable_eq hls hinv.ptrs hft (Nat.le_refl _) x
  have hProot : (db'.P.get? SIS.root).map (fun n => sp.live (n.hist.upTo (k + 1 - 1))) =
      (db.P.get? SIS.root).map (fun n => sp.live (n.hist.upTo (k + 1 - 1))) := by
    rw [hK1]; exact hrel.agree.live_eq hft (Nat.le_refl _) (reachable_root hn0' k)
  obtain ⟨o2', ho2', hco2', hno2'⟩ := hm2.root
  rw [hra2, Option.some.injEq] at ho2'
  subst ho2'
  obtain ⟨n2, hn2, hoe2, -, -⟩ := hm2.cc m2E.root oe2 hra2 hco2'
  rw [hno2', hn0', Option.some.injEq] at hn2
  subst hn2
  have hPr2 : ∀ n, db.P.get? SIS.root = some n → ∀ y ∈ sp.live (n.hist.upTo (k + 1 - 1)),
      y ∈ pointees sp oc2.hist ∧ y ∈ pointees sp oe2.hist := by
    intro n hn y hy
    rw [hn0', Option.some.injEq] at hn
    subst hn
    rw [hK1, ← hoe2] at hy
    refine ⟨?_, mem_pointees_of_live hls hy⟩
    rw [← hr2.live k hft] at hy
    exact mem_pointees_of_live hls hy
  have hradds : sp.virt = true → ∀ a ∈ (parts sp al db tr).c.adds, a.1 = SIS.root →
      ∃ nn ∈ (parts sp al db tr).c.new, a.2 = sp.rootVal nn.id := by
    intro hv a ha' ha1
    have hmem : a ∈ (parts sp al db tr).c.adds.filter (fun a => a.1 == SIS.root) :=
      List.mem_filter.mpr ⟨ha', by simp [ha1]⟩
    rw [(hstep.virt hv).rootAdds] at hmem
    obtain ⟨nn, hnn, hnne⟩ := List.mem_map.mp hmem
    exact ⟨nn, (List.mem_filter.mp hnn).1, by rw [← hnne]⟩
  have hptrs : sp.virt = true → ∀ z, sp.ptrs (sp.rootVal z) = [z] := fun hv => (hinv.vr hv).rootPtrs
  have hvalsE : sp.virt = true → ∀ e ∈ oe2.hist, ∃ z, e.val = sp.rootVal z := by
    intro hv e he
    rw [hoe2] at he
    obtain ⟨z, -, -, hval⟩ := (hinv.vr hv).rootEntry n0 hn0' e he
    exact ⟨z, hval⟩
  obtain ⟨oc3, oe3, hr3, hra3, -, ⟨X, hX, hX'⟩, he3⟩ :=
    HMem.withRoot_applyChange (P' := db'.P) hvl hinv hm2 hstep hReach hProot hPr2 hradds hptrs hra2 hr2 hvalsE
  have hpreC : preWriteH sp (cutStream c db1.S) db' (parts sp al db tr).c (m1E.withRoot oc1) =
      (m2E.applyChange sp db.P (k + 1) (parts sp al db tr).c).withRoot oc3 := by
    have e0 : preWriteH sp (cutStream c db1.S) db' (parts sp al db tr).c (m1E.withRoot oc1) =
        (((pathOf sp db.P (parts sp al db tr).c (k + 1)).mergeSort
          (fun a b => decide (lev db.P b ≤ lev db.P a))).foldl
          (HMem.reachOnPath sp (cutStream c db1.S) (cutStream c db.S) db'.P (k + 1)
            (pathOf sp db.P (parts sp al db tr).c (k + 1))) (m1E.withRoot oc1)).applyChange sp db'.P (k + 1)
            (parts sp al db tr).c := by
      unfold preWriteH
      simp only [hlen']
      simp only [hpatheq, hsorteq, hrel.stream]
      rfl
    rw [e0, hwalkC, hw1, he3]
  have hpreE : preWriteH sp db1.S db (parts sp al db tr).c m1E = m2E.applyChange sp db.P (k + 1) (parts sp al db tr).c := by
    rw [← hW]
    unfold preWriteH
    rw [hlen]
    rfl
  rw [hpreC, hpreE]
  generalize hM3 : m2E.applyChange sp db.P (k + 1) (parts sp al db tr).c = m3E at ha hra3 he3 ⊢
  -- The writes.
  rw [hrel.dirty]
  have hdata : ((parts sp al db tr).c.new.filter (·.isData)).map (·.id) = dataIds sp al db tr := rfl
  rw [hdata]
  have hroot3 : m3E.root = m2E.root := by rw [← hM3]; rw [(changeFactsH sp db.P (k + 1) _ m2E).root,
    (hm2.addFactsH hinv hstep).root]
  have hra3' : m3E.obj? m3E.root = some oe3 := by rw [hroot3]; exact hra3
  have htnr3 : ∀ y b, m3E.canonicalOf y = some b → b = m3E.root → y = SIS.root := by
    intro y b hcb hbr
    obtain ⟨o3, ho3, hon3, -⟩ := ha.tbl.canonicalOf_node hcb
    obtain ⟨o4, ho4, -, hn4⟩ := ha.root
    rw [hbr, ho4, Option.some.injEq] at ho3
    subst ho3
    rw [← hon3, hn4]
  have hcs3 : c ≤ (m3E.withRoot oc3).s := by
    rw [HMem.withRoot_s, ha.sEq]
    exact Nat.le_trans hcut.1 hL.fa1
  have hxs : ∀ x ∈ dataIds sp al db tr, x ≠ SIS.root ∨ sp.virt = false := by
    intro x hx
    left
    obtain ⟨hnone, -⟩ := step_dataIds_spec sp al db tr hinv hstep hx
    intro hxr
    rw [hxr] at hnone
    obtain ⟨n0', h0'⟩ := Option.isSome_iff_exists.mp hinv.rootIn
    rw [h0'] at hnone; cases hnone
  have hW2 : HMem.writeNodes sp (cutStream c db1.S) db.D (k + 1) (m3E.withRoot oc3) (dataIds sp al db tr) =
      HMem.writeNodes sp db1.S db.D (k + 1) (m3E.withRoot oc3) (dataIds sp al db tr) := by
    rw [writeNodesH_eq_foldl, writeNodesH_eq_foldl, HMem.writeNodes_cutS0 _ _ _ hcs3]
  obtain ⟨oc4, oe4, hr4, hh4, hh4', ho4, hrt4, hs4, htnr4, he4⟩ :=
    HMem.withRoot_writeNodes (sp := sp) db1.S db.D (k + 1) (dataIds sp al db tr) m3E [] oc3 oe3 hra3' hr3 htnr3 hxs
  rw [← writeNodesH_eq_foldl, ← writeNodesH_eq_foldl] at he4
  rw [← writeNodesH_eq_foldl] at ho4 hrt4 hs4 htnr4
  rw [hW2, he4]
  obtain ⟨e1, -, e3, -⟩ := ha.loops_vs hsp hinv hmk hstep hinv'
  rw [e1]
  rw [e1] at e3
  have hD1C : D1Of sp al db' (parts sp al db tr).c (parts sp al db tr).vs0 = (parts sp al db tr).D1 := by
    rw [← hcq, ← hvs0, ← parts_D1Of, hD1]
  have htakenC : takenOf sp al db' tr (parts sp al db tr).c (parts sp al db tr).vs0 = (parts sp al db tr).taken := by
    rw [← hcq, ← hvs0, ← parts_takenOf, htaken]
  rw [hD1C, htakenC, ← parts_D1Of, ← parts_takenOf]
  have hxs' : ∀ x ∈ (parts sp al db tr).taken, x ≠ SIS.root ∨ sp.virt = false := by
    intro x hx
    cases hv : sp.virt with
    | false => right; rfl
    | true =>
      left
      obtain ⟨d, hxd, -⟩ := step_taken_inD (al := al) (tr := tr) hinv hx
      intro hxr
      rw [hxr] at hxd
      have := (hinv.vr hv).rootND
      rw [(inD_iff _ _).mpr ⟨d, hxd⟩] at this
      cases this
  generalize hw2 : m3E.writeNodes sp db1.S db.D (k + 1) (dataIds sp al db tr) = w2E at ho4 hrt4 hs4 htnr4 e3 ⊢
  have hra4 : w2E.1.obj? w2E.1.root = some oe4 := by rw [hrt4]; exact ho4
  have hcs4 : c ≤ (w2E.1.withRoot oc4).s := by
    rw [HMem.withRoot_s, hs4, ha.sEq]
    exact Nat.le_trans hcut.1 hL.fa1
  have hW6 : HMem.writeNodes sp (cutStream c db1.S) (parts sp al db tr).D1 (k + 1) (w2E.1.withRoot oc4)
      (parts sp al db tr).taken =
      HMem.writeNodes sp db1.S (parts sp al db tr).D1 (k + 1) (w2E.1.withRoot oc4) (parts sp al db tr).taken := by
    rw [writeNodesH_eq_foldl, writeNodesH_eq_foldl, HMem.writeNodes_cutS0 _ _ _ hcs4]
  obtain ⟨oc5, oe5, hr5, hh5, hh5', ho5, hrt5, -, -, he5⟩ :=
    HMem.withRoot_writeNodes (sp := sp) db1.S (parts sp al db tr).D1 (k + 1) (parts sp al db tr).taken w2E.1 []
      oc4 oe4 hra4 hr4 (by rw [hrt4]; exact htnr4) hxs'
  rw [← writeNodesH_eq_foldl, ← writeNodesH_eq_foldl] at he5
  rw [← writeNodesH_eq_foldl] at ho5 hrt5
  rw [hW6, he5]
  refine ⟨?_, oc5, oe5, rfl, by simp only; rw [hrt5]; exact ho5, hr5, ?_⟩
  · simp only
    rw [e3, step_eq_stepOf, hcq, hvs0, hvs]
  · -- the root's history
    intro n hn
    have hsP : (step sp al db' tr).P = db'.P.apply (k + 1) (parts sp al db tr).c := by
      rw [step_eq_parts]; simp only; rw [parts_P' sp al db' tr hlen', hcq]
    obtain ⟨n', hn'⟩ := Option.isSome_iff_exists.mp hrel.agree.rootP'
    rw [hsP, get?_apply_of_get? hn', Option.some.injEq] at hn
    subst hn
    simp only
    rw [hh5, hh4, hX, hh2, hhc1, hoc n' hn']
    congr 1
    -- X: the root's new entries, from E's root object
    obtain ⟨o3, ho3, hc3, hn3r⟩ := ha.root
    rw [hra3', Option.some.injEq] at ho3
    subst ho3
    obtain ⟨n3, hn3, hh3, -⟩ := ha.cc m3E.root oe3 hra3' hc3
    rw [hn3r, get?_apply_of_get? hn0', Option.some.injEq] at hn3
    subst hn3
    rw [hX', hoe2] at hh3
    exact List.append_cancel_left hh3

end Trans

end SIS
