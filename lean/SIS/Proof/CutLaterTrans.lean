/-
Proofs about reclaim, part 20 (bergdb item 001, WP R5, T12 with eviction): one
transaction of the physical writer after a restart from a cut stream. The run
that restarted from the cut stream (C) and the run that restarted from the
whole stream at the same points (E) write the same record: C's memory is E's
but for the root's object (`RootRel`) and where its entry is (`RootPerm`);
C's reads on the cut streams are E's on the whole streams (`NInv`, `Later`);
and C's structure agrees with E's from the first available time on
(`CutRel`).
-/
import SIS.Proof.CutLaterPerm
import SIS.Proof.CutRuns

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## The root apart, from the invariants -/

section Sep

variable {sp : Spec V T} {m : Mem V}

theorem RootSep.mk' (hroot : ∃ o, m.obj? m.root = some o ∧ o.node = root)
    (hfr : ∀ h, m.next ≤ h → m.obj? h = none) (htbl : TableNode m) (hsn : SlotsNode m)
    (hptr : ∀ h o, m.obj? h = some o → ∀ y ∈ pointees sp o.hist, y ≠ root) : RootSep sp m := by
  obtain ⟨o0, ho0, hn0⟩ := hroot
  refine ⟨fun o ho => by rw [ho0, Option.some.injEq] at ho; subst ho; exact hn0, ?_, ?_, ?_, hptr⟩
  · apply Nat.lt_of_not_le
    intro hle
    rw [hfr _ hle] at ho0
    cases ho0
  · intro h o y h' ho hsl hy he
    obtain ⟨o', ho', hn'⟩ := hsn h o ho y h' hsl
    rw [he, ho0, Option.some.injEq] at ho'
    subst ho'
    exact hy (hn'.symm.trans hn0)
  · intro y h ht hy he
    obtain ⟨o', ho', hn'⟩ := htbl y h ht
    rw [he, ho0, Option.some.injEq] at ho'
    subst ho'
    exact hy (hn'.symm.trans hn0)

theorem RootSep.of_einv {db : DB V T} {S0 : Stream V T} {k : Nat} (hinv : Inv sp db k)
    (hm : EInv sp db S0 k m) : RootSep sp m := by
  obtain ⟨o0, ho0, -, hn0⟩ := hm.root
  refine RootSep.mk' ⟨o0, ho0, hn0⟩ hm.fresh hm.tbl hm.slotsNode ?_
  intro h o ho y hy
  cases hc : o.canonical with
  | true =>
    obtain ⟨n, hn, hh, -⟩ := hm.cc h o ho hc
    rw [hh, mem_pointees] at hy
    obtain ⟨e, he, hye⟩ := hy
    exact hinv.ptr_ne_root hn he hye
  | false =>
    obtain ⟨r, w, -, hw, hh, -⟩ := hm.snap h o ho hc
    rw [hh] at hy
    exact hinv.pointee_ne_root hw hy

theorem RootSep.of_ainv {db : DB V T} {S0 : Stream V T} {k : Nat} {c : Changes V} {path : List NodeId}
    (hinv : Inv sp db k) (hinv' : ∀ x n, (db.P.apply (k + 1) c).get? x = some n → ∀ e ∈ n.hist,
      ∀ y ∈ sp.ptrs e.val, y ≠ root)
    (ha : AInv sp db S0 k c path m) : RootSep sp m := by
  obtain ⟨o0, ho0, -, hn0⟩ := ha.root
  refine RootSep.mk' ⟨o0, ho0, hn0⟩ ha.fresh ha.tbl ha.slotsNode ?_
  intro h o ho y hy
  cases hc : o.canonical with
  | true =>
    obtain ⟨n, hn, hh, -⟩ := ha.cc h o ho hc
    rw [hh, mem_pointees] at hy
    obtain ⟨e, he, hye⟩ := hy
    exact hinv' _ n hn e he y hye
  | false =>
    obtain ⟨r, w, -, hw, hh, -⟩ := ha.snap h o ho hc
    rw [hh] at hy
    exact hinv.pointee_ne_root hw hy

/-- No version of a run's stream points to the root, nor of the stream cut. -/
theorem Inv.streamNR {db : DB V T} {k : Nat} (hinv : Inv sp db k) : StreamNR sp db.S :=
  fun _ _ _ hw _ hz => hinv.pointee_ne_root hw hz

theorem StreamNR.cut {S : Stream V T} (hS : StreamNR sp S) (c : Nat) : StreamNR sp (cutStream c S) := by
  intro r y w hw
  by_cases hr : c ≤ r
  · rw [versionAt_cut_ge hr] at hw
    exact hS r y w hw
  · rw [versionAt_cut_lt (by omega)] at hw
    cases hw' : S.versionAt r y with
    | none => rw [hw'] at hw; cases hw
    | some w0 =>
      rw [hw'] at hw
      simp only [Option.map_some, Option.some.injEq] at hw
      subst hw
      intro z hz
      simp [Version.stub, pointees] at hz

end Sep

/-! ## With a virtual root, the root's object is the only source of a slot for a
live root child -/

section Only

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

theorem EInv.rootOnly (hinv : Inv sp db k) (hls : LiveSub sp) (hm : EInv sp db S0 k m) (hv : sp.virt = true) :
    RootOnly sp db.P (k + 1) m := by
  have hvi := hinv.vr hv
  intro y oR hro hsrc p hp hpr
  obtain ⟨o0, ho0, hc0, hn0⟩ := hm.root
  rw [ho0, Option.some.injEq] at hro
  subst hro
  have hw0 : written sp SIS.root = false := by simp [written, hv]
  -- y is a live root child at k: a root child, reachable at k.
  unfold srcOK4 at hsrc
  simp only [hn0, hw0, Bool.false_or, Bool.and_eq_true] at hsrc
  obtain ⟨⟨⟨⟨-, -⟩, -⟩, -⟩, hlive⟩ := hsrc
  simp only [Nat.add_sub_cancel] at hlive
  cases hn : db.P.get? SIS.root with
  | none => rw [hn] at hlive; cases hlive
  | some n0 =>
    rw [hn] at hlive
    simp only [List.contains_iff_mem] at hlive
    obtain ⟨e, he, hye⟩ := hls _ _ hlive
    obtain ⟨z, mz, hzt, hval⟩ := hvi.rootEntry n0 hn e (mem_upTo.mp he).1
    rw [hval, hvi.rootPtrs] at hye
    have hyz : y = z := List.mem_singleton.mp hye
    subst hyz
    have hyTop : isTop sp db.P y = true := isTop_iff.mpr ⟨hzt.2.1, mz, hzt.1, hzt.2.2.1⟩
    obtain ⟨my, hmy, hlt⟩ := hinv.ptrs SIS.root n0 hn e (mem_upTo.mp he).1 y (by rw [hval, hvi.rootPtrs]; simp)
    have hyR : reachable sp db.P k y = true :=
      (reachable_iff _ _ _ _).mpr (Reach.child (Reach.root n0 hn) hn hlive hmy hlt)
    -- the other source p: a root child pointing to y, so y is not reachable.
    unfold srcOK4
    cases hcan : p.2.canonical with
    | false => simp
    | true =>
      cases hsl : (p.2.slot? y).isSome with
      | false => simp
      | true =>
        cases hpt : (pointees sp p.2.hist).contains y with
        | false => simp
        | true =>
          simp only [Bool.true_and, Bool.and_eq_false_iff]
          left
          have hpo : m.obj? p.1 = some p.2 := obj?_of_mem_objs hm.objNodup hp
          obtain ⟨np, hnp, hhp, -⟩ := hm.cc p.1 p.2 hpo hcan
          have hpz : p.2.node ≠ SIS.root := by
            intro hz
            have h1 := hm.canonTbl p.1 p.2 hpo hcan
            have h2 := hm.canonTbl m.root o0 ho0 hc0
            rw [hz] at h1
            rw [hn0] at h2
            rw [h1, Option.some.injEq] at h2
            exact hpr h2
          have hyp : y ∈ pointees sp np.hist := by
            rw [← hhp]; simpa [List.contains_iff_mem] using hpt
          obtain ⟨e', he', hye'⟩ := (mem_pointees sp np.hist y).mp hyp
          obtain ⟨my', hmy', hlt'⟩ := hinv.ptrs p.2.node np hnp e' he' y hye'
          rw [hmy, Option.some.injEq] at hmy'
          subst hmy'
          have hmz : mz = my := by
            have := hzt.1; rw [hmy, Option.some.injEq] at this; exact this.symm
          have hpTop : isTop sp db.P p.2.node = true := isTop_iff.mpr ⟨hpz, np, hnp, by
            have := hzt.2.2.1; rw [hmz] at this; omega⟩
          have := hvi.deadTops p.2.node np hnp hpTop y hyp hyTop
          rw [hyR] at this
          cases this

theorem RootOnly.withRoot {P P' : Struct V} {j f : Time} {oc oe : Obj V} (hU : RootOnly sp P j m)
    (hReach : ∀ x, reachable sp P' (j - 1) x = reachable sp P (j - 1) x)
    (hProot : (P'.get? SIS.root).map (fun n => sp.live (n.hist.upTo (j - 1))) =
      (P.get? SIS.root).map (fun n => sp.live (n.hist.upTo (j - 1))))
    (hPr : ∀ n, P.get? SIS.root = some n → ∀ y ∈ sp.live (n.hist.upTo (j - 1)),
      y ∈ pointees sp oc.hist ∧ y ∈ pointees sp oe.hist)
    (hra : m.obj? m.root = some oe) (hr : RootRel sp f oc oe) (hnode : oe.node = SIS.root) :
    RootOnly sp P' j (m.withRoot oc) := by
  intro y oR hro hsrc p hp hpr
  rw [withRoot_root, withRoot_obj?_root hra, Option.some.injEq] at hro
  subst hro
  rw [withRoot_root] at hsrc hpr
  have hsrcE : srcOK4 sp P j y (m.root, oe) = true := by
    rw [← (srcOK4_rootRel hReach hProot hPr hr hnode y m.root).1]; exact hsrc
  have hpm : p ∈ m.objs := by
    unfold Mem.withRoot at hp
    obtain ⟨q, hq, hqe⟩ := List.mem_map.mp hp
    by_cases hq1 : q.1 = m.root
    · have : (q.1 == m.root) = true := by simp [hq1]
      simp only [this, ↓reduceIte] at hqe
      rw [← hqe] at hpr
      exact absurd rfl hpr
    · have : (q.1 == m.root) = false := by simp [hq1]
      simp only [this, Bool.false_eq_true, ↓reduceIte] at hqe
      rw [← hqe]; exact hq
  rw [srcOK4_congrP hReach hProot y p]
  exact hU y oe hra hsrcE p hpm hpr

end Only

/-! ## One transaction -/

/-- C's memory is E's but for the root's object and where its entry is;
without a virtual root, E's. -/
structure SimC (sp : Spec V T) (f : Time) (mC mE : Mem V) (oc oe : Obj V) : Prop where
  perm : RootPerm mC (mE.withRoot oc)
  nv : sp.virt = false → mC = mE.withRoot oc
  rootE : mE.obj? mE.root = some oe
  rel : RootRel sp f oc oe

section Trans

variable {sp : Spec V T} {al : Algo V T}

theorem view4_eq (S0 S : Stream V T) (m : Mem V) (t : Time) :
    m.view4 sp S0 S t = ((m.read4 sp S0 S t).1, fun x => (m.read4 sp S0 S t).2.lookup x) := rfl

/-- The view of the writer of C: E's, but for the root's node, from C's root object. -/
theorem view4_sim {f : Time} {db1 db : DB V T} {j1 k c : Nat} (hls : LiveSub sp) (hL : Later sp db1 db j1 k)
    (hcut : CutOK sp c db1 j1) (hft : lastFa db1.S ≤ k) (hf : f ≤ k)
    {mE mC : Mem V} {oc oe : Obj V} (hm : EInv sp db db1.S k mE) (hh : HInv sp db db1.S k mE)
    (hn : NInv db db1.S mE) (hsim : SimC sp f mC mE oc oe) :
    ∃ oc1 oe1 tail, SimC sp f (mC.read4 sp (cutStream c db1.S) (cutStream c db.S) k).1
        (mE.read4 sp db1.S db.S k).1 oc1 oe1 ∧ oc1.hist = oc.hist ∧ oe1.hist = oe.hist ∧
      (mC.read4 sp (cutStream c db1.S) (cutStream c db.S) k).2 = (SIS.root, oc.nodeAt k) :: tail ∧
      (mE.read4 sp db1.S db.S k).2 = (SIS.root, oe.nodeAt k) :: tail := by
  have hinv := hL.inv
  have hrs := RootSep.of_einv hinv hm
  have hS : StreamNR sp (cutStream c db.S) := hinv.streamNR.cut c
  have hra : mE.obj? mE.root = some oe := hsim.rootE
  obtain ⟨oc1, oe1, hr1, hh1, hh1', ho1, hrs1, hrt1, hrd, hhd⟩ :=
    read4_withRoot (S0 := cutStream c db1.S) hls hS hf hrs hra hsim.rel
  have hlat := NInv.read4_later hL hls hm hh hn hcut hft (Nat.le_refl k)
  rw [hlat] at ho1 hrs1 hrt1 hrd hhd
  have hnode : oe.node = SIS.root := hrs.rootNode oe hra
  have hnodec : oc.node = SIS.root := by rw [hsim.rel.node]; exact hnode
  obtain ⟨p1, p2⟩ := hsim.perm.read4 (sp := sp) (S0 := cutStream c db1.S) (S := cutStream c db.S) k
  rw [hrd] at p1 p2
  cases hl : (mE.read4 sp db1.S db.S k).2 with
  | nil => rw [hl] at hhd; cases hhd
  | cons a tail =>
    rw [hl] at hhd
    simp only [List.head?_cons, Option.some.injEq] at hhd
    subst hhd
    rw [hl] at p2
    simp only [List.tail_cons] at p2
    refine ⟨oc1, oe1, tail, ⟨p1, ?_, by rw [hrt1]; exact ho1, hr1⟩, hh1, hh1', by rw [p2, hnodec], by rw [hnode]⟩
    intro hv
    rw [hsim.nv hv, hrd]

theorem withRoot_keys (m : Mem V) (oc : Obj V) : (m.withRoot oc).objs.map (·.1) = m.objs.map (·.1) := by
  unfold Mem.withRoot
  simp only [List.map_map]
  apply List.map_congr_left
  intro p _
  simp only [Function.comp]
  split
  · rename_i h; simp at h; exact h.symm
  · rfl

/-- A memory with the other root object is related to itself. -/
theorem RootPerm.refl_withRoot {m : Mem V} {oc oe : Obj V} (hnd : (m.objs.map (·.1)).Nodup)
    (hfr : ∀ h, m.next ≤ h → m.obj? h = none) (hra : m.obj? m.root = some oe) :
    RootPerm (m.withRoot oc) (m.withRoot oc) := by
  have hlt : m.root < m.next := by
    apply Nat.lt_of_not_le; intro hle; rw [hfr _ hle] at hra; cases hra
  refine RootPerm.refl (by rw [withRoot_keys]; exact hnd) ?_ (by simpa using hlt)
  intro h hh
  rw [withRoot_next] at hh
  rw [withRoot_obj?_ne (by omega)]
  exact hfr h hh

/-- The writer's walk of C: E's. -/
theorem walk_sim {f : Time} {db1 db db' : DB V T} {j1 k c : Nat} (hls : LiveSub sp)
    (hL : Later sp db1 db j1 k) (hcut : CutOK sp c db1 j1) (hev : EvLogic sp db k)
    (hrel : CutRel sp c f k db' db) (hfk : f ≤ k) {path : List NodeId}
    (hpath : ∀ p ∈ path, reachable sp db.P k p = true) (L : List NodeId)
    {m1E m1C : Mem V} {oc1 oe1 : Obj V} (hm1 : EInv sp db db1.S k m1E) (hn1 : NInv db db1.S m1E)
    (hsim1 : SimC sp f m1C m1E oc1 oe1)
    (hPr : ∀ n, db.P.get? SIS.root = some n → ∀ x ∈ sp.live (n.hist.upTo k), x ∈ pointees sp oc1.hist) :
    ∃ oc2 oe2, SimC sp f (L.foldl (Mem.reachOnPath4 sp (cutStream c db1.S) (cutStream c db.S) db'.P (k + 1) path) m1C)
        (L.foldl (Mem.reachOnPath4 sp db1.S db.S db.P (k + 1) path) m1E) oc2 oe2 ∧
      oc2.hist = oc1.hist ∧ oe2.hist = oe1.hist := by
  have hinv := hL.inv
  have hrs := RootSep.of_einv hinv hm1
  have hS : StreamNR sp (cutStream c db.S) := hinv.streamNR.cut c
  have hk1 : k + 1 - 1 = k := by omega
  have hP : ∀ p ∈ path, (db'.P.get? p).map (fun n => sp.live (n.hist.upTo (k + 1 - 1))) =
      (db.P.get? p).map (fun n => sp.live (n.hist.upTo (k + 1 - 1))) := by
    intro p hp; rw [hk1]; exact hrel.agree.live_eq hfk (Nat.le_refl _) (hpath p hp)
  have hPnr : ∀ p n, db.P.get? p = some n → ∀ x ∈ sp.live (n.hist.upTo (k + 1 - 1)), x ≠ SIS.root := by
    intro p n hn x hx
    rw [hk1] at hx
    obtain ⟨e, he, hxe⟩ := hls _ _ hx
    exact hinv.ptr_ne_root hn (mem_upTo.mp he).1 hxe
  have hPr' : ∀ n, db.P.get? SIS.root = some n → ∀ x ∈ sp.live (n.hist.upTo (k + 1 - 1)),
      x ∈ pointees sp oc1.hist := by
    intro n hn x hx; rw [hk1] at hx; exact hPr n hn x hx
  rw [reachPath4_congrP hP L m1C]
  obtain ⟨oc2, oe2, hr2, hh2, hh2', ho2, hrs2, hrt2, he2⟩ :=
    reachPath4_withRoot (S0 := cutStream c db1.S) (path := path) (f := f) hS hPnr L m1E oc1 oe1 hPr' hrs
      hsim1.rootE hsim1.rel
  have hlat := NInv.reachPath4_later hL hls hev hcut hpath L m1E hm1 hn1
  rw [hlat] at ho2 hrs2 hrt2 he2
  refine ⟨oc2, oe2, ⟨?_, ?_, by rw [hrt2]; exact ho2, hr2⟩, hh2, hh2'⟩
  · rw [← he2]
    exact RootPerm.reachPath4 db.P (k + 1) path L _ _ hsim1.perm
  · intro hv
    rw [hsim1.nv hv, he2]

/-- The root's object of a memory with the invariant holds the root's history. -/
theorem EInv.root_hist {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V} (hm : EInv sp db S0 k m)
    {o : Obj V} (ho : m.obj? m.root = some o) : ∃ n, db.P.get? SIS.root = some n ∧ o.hist = n.hist := by
  obtain ⟨o0, ho0, hc0, hn0⟩ := hm.root
  rw [ho0, Option.some.injEq] at ho
  subst ho
  obtain ⟨n, hn, hh, -⟩ := hm.cc m.root o0 ho0 hc0
  rw [hn0] at hn
  exact ⟨n, hn, hh⟩

/-- The change of C: E's. -/
theorem change_sim (hvl : VirtLiveOK sp) {f : Time} {db1 db db' : DB V T} {k c : Nat} (hls : LiveSub sp)
    (hinv : Inv sp db k) (hrel : CutRel sp c f k db' db) (hfk : f ≤ k) {ch : Changes V}
    (hstep : StepOK sp db.P (k + 1) ch) {m2E m2C : Mem V} {oc2 oe2 : Obj V}
    (hm2 : EInv sp db db1.S k m2E) (hsim2 : SimC sp f m2C m2E oc2 oe2)
    (hnd3 : ((m2E.applyChange4 sp db.P (k + 1) ch).objs.map (·.1)).Nodup)
    (hfr3 : ∀ h, (m2E.applyChange4 sp db.P (k + 1) ch).next ≤ h → (m2E.applyChange4 sp db.P (k + 1) ch).obj? h = none) :
    ∃ oc3 oe3, SimC sp f (m2C.applyChange4 sp db'.P (k + 1) ch) (m2E.applyChange4 sp db.P (k + 1) ch) oc3 oe3 ∧
      ∃ X, oc3.hist = oc2.hist ++ X ∧ oe3.hist = oe2.hist ++ X := by
  have hrs := RootSep.of_einv hinv hm2
  have hra := hsim2.rootE
  have hnode : oe2.node = SIS.root := hrs.rootNode oe2 hra
  have hk1 : k + 1 - 1 = k := by omega
  have hReach : ∀ x, reachable sp db'.P (k + 1 - 1) x = reachable sp db.P (k + 1 - 1) x := by
    intro x; rw [hk1]; exact hrel.agree.reachable_eq hls hinv.ptrs hfk (Nat.le_refl _) x
  obtain ⟨n0, hn0⟩ := Option.isSome_iff_exists.mp hinv.rootIn
  have hProot : (db'.P.get? SIS.root).map (fun n => sp.live (n.hist.upTo (k + 1 - 1))) =
      (db.P.get? SIS.root).map (fun n => sp.live (n.hist.upTo (k + 1 - 1))) := by
    rw [hk1]; exact hrel.agree.live_eq hfk (Nat.le_refl _) (reachable_root hn0 k)
  obtain ⟨n2, hn2, hh2⟩ := hm2.root_hist hra
  have hPr : ∀ n, db.P.get? SIS.root = some n → ∀ y ∈ sp.live (n.hist.upTo (k + 1 - 1)),
      y ∈ pointees sp oc2.hist ∧ y ∈ pointees sp oe2.hist := by
    intro n hn y hy
    rw [hn2, Option.some.injEq] at hn
    subst hn
    rw [hk1, ← hh2] at hy
    refine ⟨?_, mem_pointees_of_live hls hy⟩
    rw [← hsim2.rel.live k hfk] at hy
    exact mem_pointees_of_live hls hy
  have hradds : sp.virt = true → ∀ a ∈ ch.adds, a.1 = SIS.root → ∃ nn ∈ ch.new, a.2 = sp.rootVal nn.id := by
    intro hv a ha ha1
    have hmem : a ∈ ch.adds.filter (fun a => a.1 == SIS.root) := List.mem_filter.mpr ⟨ha, by simp [ha1]⟩
    rw [(hstep.virt hv).rootAdds] at hmem
    obtain ⟨nn, hnn, hnne⟩ := List.mem_map.mp hmem
    exact ⟨nn, (List.mem_filter.mp hnn).1, by rw [← hnne]⟩
  have hvalsE : sp.virt = true → ∀ e ∈ oe2.hist, ∃ z, e.val = sp.rootVal z := by
    intro hv e he
    rw [hh2] at he
    obtain ⟨z, -, -, hval⟩ := (hinv.vr hv).rootEntry n2 hn2 e he
    exact ⟨z, hval⟩
  obtain ⟨oc3, oe3, hr3, ho3, hrt3, -, -, hX, he3⟩ :=
    applyChange4_withRoot (P' := db'.P) (P := db.P) (j := k + 1) (c := ch) hvl hReach hProot hPr hstep.distinct
      hradds (fun hv => (hinv.vr hv).rootPtrs) hrs hm2.objNodup hm2.fresh hra hsim2.rel hnode hvalsE
  refine ⟨oc3, oe3, ⟨?_, ?_, by rw [hrt3]; exact ho3, hr3⟩, hX⟩
  · cases hv : sp.virt with
    | true =>
      have hU : RootOnly sp db'.P (k + 1) (m2E.withRoot oc2) :=
        (hm2.rootOnly hinv hls hv).withRoot hReach hProot hPr hra hsim2.rel hnode
      have := (RootPerm.applyChange4 hsim2.perm.symm hU ch).symm
      rw [he3] at this
      exact this
    | false =>
      rw [hsim2.nv hv, he3]
      exact RootPerm.refl_withRoot hnd3 hfr3 (by rw [hrt3]; exact ho3)
  · intro hv
    rw [hsim2.nv hv, he3]

/-- The physical writer's loop of C: E's, with the same versions. -/
theorem writes_sim {f : Time} {S0 : Stream V T} {c : Nat} {D : Dirty} {i : Nat} (xs : List NodeId)
    {m3E m3C : Mem V} {oc3 oe3 : Obj V} (hrs3 : RootSep sp m3E) (hsim3 : SimC sp f m3C m3E oc3 oe3)
    (hcs : c ≤ m3C.s) (hxs : ∀ x ∈ xs, x ≠ SIS.root ∨ sp.virt = false) :
    ∃ oc4 oe4, SimC sp f (m3C.writeNodes sp (cutStream c S0) D i xs).1 (m3E.writeNodes sp S0 D i xs).1 oc4 oe4 ∧
      (m3C.writeNodes sp (cutStream c S0) D i xs).2 = (m3E.writeNodes sp S0 D i xs).2 ∧
      oc4.hist = oc3.hist ∧ oe4.hist = oe3.hist ∧ RootSep sp (m3E.writeNodes sp S0 D i xs).1 := by
  simp only [writeNodes_eq_foldl]
  rw [writeNodes_cutS0 xs m3C [] hcs]
  obtain ⟨oc4, oe4, hr4, hh4, hh4', ho4, hrt4, hrs4, he4⟩ :=
    writeNodes_withRoot (S0 := S0) (D := D) (i := i) xs m3E [] oc3 oe3 hrs3 hsim3.rootE hsim3.rel hxs
  obtain ⟨p1, p2⟩ := RootPerm.writeNodes (sp := sp) S0 D i xs m3C (m3E.withRoot oc3) [] hsim3.perm
  rw [he4] at p1 p2
  refine ⟨oc4, oe4, ⟨p1, ?_, by rw [hrt4]; exact ho4, hr4⟩, p2, hh4, hh4', hrs4⟩
  intro hv
  rw [hsim3.nv hv, he4]

theorem writeNodes_s (S0 : Stream V T) (D : Dirty) (i : Nat) :
    ∀ (xs : List NodeId) (m : Mem V), (m.writeNodes sp S0 D i xs).1.s = m.s := by
  intro xs m
  rw [writeNodes_eq_foldl]
  have : ∀ (xs : List NodeId) (acc : Mem V × List (Version V)), (xs.foldl (wnStep sp S0 D i) acc).1.s = acc.1.s := by
    intro xs
    induction xs with
    | nil => intro acc; rfl
    | cons x xs ih => intro acc; simp only [List.foldl_cons]; rw [ih, wnStep_fst, writeNode_s]
  exact this xs (m, [])

/-- One transaction of C after a restart from a cut stream: the record of the
run with restarts from cut streams (`runRestartsCut`'s step), and C's memory
stays E's but for the root's object, which holds C's root's history. -/
theorem evictTrans_sim (hsp : SpecOK sp) (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true)
    (hex : ExecRootOK sp) (hvl : VirtLiveOK sp) (hpol : PolicyCutOK al)
    {db1 db db' : DB V T} {j1 k c : Nat} (hev : EvLogic sp db k)
    (hL : Later sp db1 db j1 k) (hcut : CutOK sp c db1 j1)
    (hrel : CutRel sp c (lastFa db1.S) k db' db) (hfs : lastFa db.S ≤ lastSp db.S)
    {mE mC : Mem V} {oc oe : Obj V}
    (hm : EInv sp db db1.S k mE) (hh : HInv sp db db1.S k mE) (hn : NInv db db1.S mE)
    (hsim : SimC sp (lastFa db1.S) mC mE oc oe)
    (hoc : ∀ n, db'.P.get? SIS.root = some n → oc.hist = n.hist)
    {tr : T} (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c)
    (hphys : PhysStep sp db.P (k + 1) (parts sp al db tr).c)
    (hcopy : CopyStep sp db.P (k + 1) (parts sp al db tr).c) (htree : treeAt sp db.P k)
    (hinv' : Inv sp (step sp al db tr) (k + 1)) :
    (evictTrans sp al (cutStream c db1.S) db' mC tr).1 = step sp al db' tr ∧
    ∃ oc' oe', SimC sp (lastFa db1.S) (evictTrans sp al (cutStream c db1.S) db' mC tr).2
        (evictTrans sp al db1.S db mE tr).2 oc' oe' ∧
      ∀ n, (step sp al db' tr).P.get? SIS.root = some n → oc'.hist = n.hist := by
  have hinv := hL.inv
  have hls : LiveSub sp := hsp.liveSub
  have hlen := hinv.len
  have hlen' : db'.S.length = k + 1 := by rw [hrel.stream, cutStream_length, hlen]
  have hK1 : k + 1 - 1 = k := by omega
  have hsk : lastSp db.S ≤ k := by have := hinv.spLt; omega
  have hft : lastFa db1.S ≤ k := by have := hrel.fa; omega
  have hcs : c ≤ mC.s := by
    rw [hsim.perm.s, withRoot_s, hm.sEq]
    exact Nat.le_trans hcut.1 hL.fa1
  have hstep_e : StepOK sp db.P (k + 1) (sp.exec tr (k + 1) (view sp db.P k)) := by
    have := hstep; rw [parts_c, hlen, hK1] at this; exact this
  obtain ⟨-, hc, hvs0, hD1, htaken, hvs, -⟩ := step_congr_cut sp al hsp hinv hj hmk hex hvl hpol hrel hfs tr hstep_e
  -- the view
  obtain ⟨hm1, hv⟩ := hm.view4_ok hinv hls hev
  have hn1 : NInv db db1.S (mE.view4 sp db1.S db.S k).1 := hn.read4 hinv hm k
  obtain ⟨oc1, oe1, tail, hsim1, hh1, hh1', hlC, hlE⟩ := view4_sim hls hL hcut hft hft hm hh hn hsim
  have hraE := hsim.rootE
  have hrsE := RootSep.of_einv hinv hm
  have hnodeE : oe.node = SIS.root := hrsE.rootNode oe hraE
  obtain ⟨n0, hn0, hoe0⟩ := hm.root_hist hraE
  have hcE : sp.exec tr (k + 1) (mE.view4 sp db1.S db.S k).2 = (parts sp al db tr).c := by
    rw [hv, parts_c, hlen, hK1]
  have hcC : sp.exec tr (k + 1) (mC.view4 sp (cutStream c db1.S) db'.S k).2 = (parts sp al db tr).c := by
    rw [view4_eq, hrel.stream, hlC, ← hcE, view4_eq, hlE]
    apply exec_rootSwap hex
    · intro hv' e he
      exact hsim.rel.vals hv' e (mem_upTo.mp he).1
    · intro hv' e he
      have he' : e ∈ oe.hist := (mem_upTo.mp he).1
      rw [hoe0] at he'
      obtain ⟨z, -, -, hval⟩ := (hinv.vr hv').rootEntry n0 hn0 e he'
      exact ⟨z, hval⟩
    · exact hsim.rel.live k hft
    · intro hv'; rw [hsim.rel.nv hv']
  rw [evictTrans_eq, evictTrans_eq, hlen', hlen, hK1, hcC, hcE, evictAfter_eq, evictAfter_eq, hlen', hlen]
  have hsim1' : SimC sp (lastFa db1.S) (mC.view4 sp (cutStream c db1.S) db'.S k).1 (mE.view4 sp db1.S db.S k).1 oc1 oe1 := by
    rw [view4_eq, view4_eq, hrel.stream]; exact hsim1
  generalize (mC.view4 sp (cutStream c db1.S) db'.S k).1 = m1C at hsim1' ⊢
  generalize (mE.view4 sp db1.S db.S k).1 = m1E at hsim1' hm1 hn1 ⊢
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
  -- E's walk and change, as in `EInv.evictTrans_ok`.
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
  obtain ⟨hm2, hpd⟩ := EInv.reachPath4_ok (S0 := db1.S) hinv hls hev hpr hparent
    ((pathOf sp db.P (parts sp al db tr).c (k + 1)).mergeSort (fun a b => decide (lev db.P b ≤ lev db.P a))) []
    m1E hm1 (fun a ha => by cases ha)
    (fun x => by rw [List.nil_append]; exact (List.mergeSort_perm _ _).mem_iff)
    (by rw [List.nil_append]; exact (List.mergeSort_perm _ _).nodup_iff.mpr hpnd)
    (by rw [List.nil_append]; exact hsorted)
  have ha := hm2.applyChange4_ok hinv hls hpd hstep hphys hcopy htree
  -- C's walk and change: E's.
  have hPr1 : ∀ n, db.P.get? SIS.root = some n → ∀ x ∈ sp.live (n.hist.upTo k), x ∈ pointees sp oc1.hist := by
    intro n hn x hx
    rw [hn0, Option.some.injEq] at hn
    subst hn
    rw [← hoe0, ← hsim.rel.live k hft] at hx
    rw [hh1]
    exact mem_pointees_of_live hls hx
  obtain ⟨oc2, oe2, hsim2, hh2, hh2'⟩ := walk_sim hls hL hcut hev hrel hft hpr
    ((pathOf sp db.P (parts sp al db tr).c (k + 1)).mergeSort (fun a b => decide (lev db.P b ≤ lev db.P a)))
    hm1 hn1 hsim1' hPr1
  obtain ⟨oc3, oe3, hsim3, X, hX3, hX3'⟩ := change_sim (k := k) (db1 := db1) hvl hls hinv hrel hft hstep hm2 hsim2
    ha.objNodup ha.fresh
  have hpre : SimC sp (lastFa db1.S) (preWrite sp (cutStream c db1.S) db' (parts sp al db tr).c m1C)
      (preWrite sp db1.S db (parts sp al db tr).c m1E) oc3 oe3 := by
    unfold preWrite
    simp only [hlen, hlen']
    rw [hpatheq, hsorteq, hrel.stream]
    exact hsim3
  have hpreE : preWrite sp db1.S db (parts sp al db tr).c m1E =
      (((pathOf sp db.P (parts sp al db tr).c (k + 1)).mergeSort (fun a b => decide (lev db.P b ≤ lev db.P a))).foldl
        (Mem.reachOnPath4 sp db1.S db.S db.P (k + 1) (pathOf sp db.P (parts sp al db tr).c (k + 1))) m1E).applyChange4
        sp db.P (k + 1) (parts sp al db tr).c := by
    unfold preWrite; rw [hlen]; rfl
  rw [← hpreE] at ha
  have hcs3 : c ≤ (preWrite sp (cutStream c db1.S) db' (parts sp al db tr).c m1C).s := by
    rw [hpre.perm.s, withRoot_s, ha.sEq]
    exact Nat.le_trans hcut.1 hL.fa1
  generalize preWrite sp (cutStream c db1.S) db' (parts sp al db tr).c m1C = m3C at hpre hcs3 ⊢
  generalize preWrite sp db1.S db (parts sp al db tr).c m1E = m3E at hpre ha ⊢
  -- The writes.
  rw [hrel.dirty]
  have hptr' : ∀ x n, (db.P.apply (k + 1) (parts sp al db tr).c).get? x = some n → ∀ e ∈ n.hist,
      ∀ y ∈ sp.ptrs e.val, y ≠ SIS.root :=
    fun x n hn e he y hy => hinv'.ptr_ne_root (by rw [hPapp]; exact hn) he hy
  have hrs3 := RootSep.of_ainv hinv hptr' ha
  have hdata : ((parts sp al db tr).c.new.filter (·.isData)).map (·.id) = dataIds sp al db tr := rfl
  have hxs : ∀ x ∈ dataIds sp al db tr, x ≠ SIS.root ∨ sp.virt = false := by
    intro x hx
    left
    obtain ⟨hnone, -⟩ := step_dataIds_spec sp al db tr hinv hstep hx
    intro hxr
    rw [hxr] at hnone
    obtain ⟨n0', h0'⟩ := Option.isSome_iff_exists.mp hinv.rootIn
    rw [h0'] at hnone; cases hnone
  rw [hdata]
  obtain ⟨oc4, oe4, hsim4, hv4, hh4, hh4', hrs4⟩ :=
    writes_sim (S0 := db1.S) (D := db.D) (i := k + 1) (dataIds sp al db tr) hrs3 hpre hcs3 hxs
  obtain ⟨e1, -, e3, -⟩ := ha.loops_vs hsp hinv hmk hstep hinv'
  rw [hv4, e1]
  rw [e1] at e3
  have hD1C : D1Of sp al db' (parts sp al db tr).c (parts sp al db tr).vs0 = (parts sp al db tr).D1 := by
    rw [← hc, ← hvs0, ← parts_D1Of, hD1]
  have htakenC : takenOf sp al db' tr (parts sp al db tr).c (parts sp al db tr).vs0 = (parts sp al db tr).taken := by
    rw [← hc, ← hvs0, ← parts_takenOf, htaken]
  rw [hD1C, htakenC, ← parts_D1Of, ← parts_takenOf]
  have hcs4 : c ≤ (m3C.writeNodes sp (cutStream c db1.S) db.D (k + 1) (dataIds sp al db tr)).1.s := by
    rw [writeNodes_s]; exact hcs3
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
  generalize m3C.writeNodes sp (cutStream c db1.S) db.D (k + 1) (dataIds sp al db tr) = w2C at hsim4 hcs4 ⊢
  generalize m3E.writeNodes sp db1.S db.D (k + 1) (dataIds sp al db tr) = w2E at hsim4 hrs4 e3 ⊢
  obtain ⟨oc5, oe5, hsim5, hv5, hh5, hh5', -⟩ :=
    writes_sim (S0 := db1.S) (D := (parts sp al db tr).D1) (i := k + 1) (parts sp al db tr).taken hrs4 hsim4 hcs4 hxs'
  rw [hv5, e3]
  refine ⟨?_, oc5, oe5, hsim5, ?_⟩
  · rw [step_eq_stepOf, hc, hvs0, hvs]
  · -- the root's history
    intro n hn
    have hsP : (step sp al db' tr).P = db'.P.apply (k + 1) (parts sp al db tr).c := by
      rw [step_eq_parts]; simp only; rw [parts_P' sp al db' tr hlen', hc]
    obtain ⟨n', hn'⟩ := Option.isSome_iff_exists.mp hrel.agree.rootP'
    rw [hsP, get?_apply_of_get? hn', Option.some.injEq] at hn
    subst hn
    simp only
    rw [hh5, hh4, hX3, hh2, hh1, hoc n' hn']
    congr 1
    -- X: the root's new entries, from E's root object
    obtain ⟨o3, ho3, hc3, -⟩ := ha.root
    rw [hpre.rootE, Option.some.injEq] at ho3
    subst ho3
    obtain ⟨n3, hn3, hh3, -⟩ := ha.cc m3E.root oe3 hpre.rootE hc3
    have hnode3 : oe3.node = SIS.root := hrs3.rootNode oe3 hpre.rootE
    rw [hnode3, get?_apply_of_get? hn0, Option.some.injEq] at hn3
    subst hn3
    rw [hX3', hh2', hh1', hoe0] at hh3
    exact (List.append_cancel_left hh3)

end Trans

/-! ## The cache operations -/

section Ops

variable {sp : Spec V T}

/-- A cache read of C at a time t from f on: E's. -/
theorem read4_sim {f : Time} {db1 db : DB V T} {j1 k c : Nat} (hls : LiveSub sp) (hL : Later sp db1 db j1 k)
    (hcut : CutOK sp c db1 j1) {t : Time} (hft : lastFa db1.S ≤ t) (hf : f ≤ t) (htk : t ≤ k)
    {mE mC : Mem V} {oc oe : Obj V} (hm : EInv sp db db1.S k mE) (hh : HInv sp db db1.S k mE)
    (hn : NInv db db1.S mE) (hsim : SimC sp f mC mE oc oe) :
    ∃ oc1 oe1, SimC sp f (mC.read4 sp (cutStream c db1.S) (cutStream c db.S) t).1
        (mE.read4 sp db1.S db.S t).1 oc1 oe1 ∧ oc1.hist = oc.hist ∧ oe1.hist = oe.hist := by
  have hinv := hL.inv
  have hrs := RootSep.of_einv hinv hm
  have hS : StreamNR sp (cutStream c db.S) := hinv.streamNR.cut c
  have hra : mE.obj? mE.root = some oe := hsim.rootE
  obtain ⟨oc1, oe1, hr1, hh1, hh1', ho1, hrs1, hrt1, hrd, -⟩ :=
    read4_withRoot (S0 := cutStream c db1.S) hls hS hf hrs hra hsim.rel
  have hlat := NInv.read4_later hL hls hm hh hn hcut hft htk
  rw [hlat] at ho1 hrs1 hrt1 hrd
  obtain ⟨p1, -⟩ := hsim.perm.read4 (sp := sp) (S0 := cutStream c db1.S) (S := cutStream c db.S) t
  rw [hrd] at p1
  refine ⟨oc1, oe1, ⟨p1, ?_, by rw [hrt1]; exact ho1, hr1⟩, hh1, hh1'⟩
  intro hv
  rw [hsim.nv hv, hrd]

/-- E changes its root's slot for a pointee that C's root object does not have. -/
theorem RootRel.setSlotE {f : Time} {oc oe : Obj V} (hr : RootRel sp f oc oe) (hv : sp.virt = true)
    {y : NodeId} (hy : y ∉ pointees sp oc.hist) (sl : Slot) : RootRel sp f oc (oe.setSlot y sl) where
  nv := fun h => absurd h (by simp [hv])
  node := hr.node
  level := hr.level
  isData := hr.isData
  canonical := hr.canonical
  pos := hr.pos
  live := hr.live
  slots := by
    intro z hz
    rw [Obj.slot?_setSlot]
    have : z ≠ y := fun he => hy (he ▸ hz)
    simp only [this, ↓reduceIte]
    exact hr.slots z hz
  noSlot := hr.noSlot
  vals := hr.vals
  keysE := by
    intro _ z hz
    rw [Obj.slot?_setSlot] at hz
    rw [Obj.setSlot_hist]
    split at hz
    · rename_i he; subst he
      cases h : oe.slot? z with
      | none => rw [h] at hz; cases hz
      | some _ => exact hr.keysE hv z (by rw [h]; rfl)
    · exact hr.keysE hv z hz

/-- Moving the root's entry to the front. -/
theorem RootPerm.withRoot_setObj_root {m : Mem V} {oc oe : Obj V} (hnd : (m.objs.map (·.1)).Nodup)
    (hfr : ∀ h, m.next ≤ h → m.obj? h = none) (hra : m.obj? m.root = some oe) (X : Obj V) :
    RootPerm (m.withRoot oc) ((m.setObj m.root X).withRoot oc) := by
  have hlt : m.root < m.next := by
    apply Nat.lt_of_not_le; intro hle; rw [hfr _ hle] at hra; cases hra
  have hra' : (m.setObj m.root X).obj? (m.setObj m.root X).root = some X := Mem.obj?_setObj_self _ _ _
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_, by rw [withRoot_keys]; exact hnd,
    by rw [withRoot_keys]; exact nodup_setObj_keys _ _ _ hnd, ?_, by simpa using hlt⟩
  · simp only [withRoot_root, Mem.setObj_root]
    unfold Mem.withRoot Mem.setObj
    simp only [List.map_cons, beq_self_eq_true, ↓reduceIte, List.filter_cons, bne_self_eq_false,
      Bool.false_eq_true]
    rw [← filter_map_root, List.filter_filter]
    congr 1
    funext p
    simp only [Bool.and_self]
  · rw [withRoot_root, withRoot_obj?_root hra]
    exact (withRoot_obj?_root hra').symm
  · intro h hh
    rw [withRoot_next] at hh
    rw [withRoot_obj?_ne (by omega)]
    exact hfr h hh

theorem Mem.detachable_root (m : Mem V) (D : Dirty) : m.detachable D m.root = false := by
  unfold Mem.detachable Mem.pinned
  cases m.obj? m.root <;> simp

theorem detachable_withRoot_ne {m : Mem V} {oc : Obj V} {D : Dirty} {h : Nat} (hne : h ≠ m.root) :
    (m.withRoot oc).detachable D h = m.detachable D h :=
  Mem.detachable_congr rfl (by rw [withRoot_obj?_ne hne])

/-- An unswizzle of another object than the root's, on the memory with the other
root object. -/
theorem unswizzle_withRoot_ne {m : Mem V} {oc oe : Obj V} (hra : m.obj? m.root = some oe) (D : Dirty)
    {h : Nat} (hne : h ≠ m.root) (y : NodeId) :
    (m.withRoot oc).unswizzle D h y = (m.unswizzle D h y).withRoot oc ∧
      (m.unswizzle D h y).obj? m.root = some oe ∧ (m.unswizzle D h y).root = m.root := by
  unfold Mem.unswizzle
  rw [withRoot_obj?_ne hne]
  cases hop : m.obj? h with
  | none => exact ⟨rfl, hra, rfl⟩
  | some op =>
    simp only
    cases op.slot? y with
    | none => exact ⟨rfl, hra, rfl⟩
    | some sl =>
      cases sl with
      | stream r => exact ⟨rfl, hra, rfl⟩
      | mem h' =>
        simp only
        by_cases he : h' = m.root
        · subst he
          rw [withRoot_obj?_root hra, hra]
          simp only
          rw [show (m.withRoot oc).detachable D m.root = false from Mem.detachable_root (m.withRoot oc) D,
            Mem.detachable_root m D]
          exact ⟨rfl, hra, rfl⟩
        · rw [withRoot_obj?_ne he]
          cases m.obj? h' with
          | none => exact ⟨rfl, hra, rfl⟩
          | some o =>
            simp only
            rw [detachable_withRoot_ne he]
            split
            · refine ⟨withRoot_setObj_ne hne _, ?_, rfl⟩
              rw [Mem.obj?_setObj_ne _ _ (Ne.symm hne)]; exact hra
            · exact ⟨rfl, hra, rfl⟩

/-- An unswizzle of the root's slot for y on the memory with the other root
object, when the two root objects have the same slot for y: the same. -/
theorem unswizzle_withRoot_root {m : Mem V} {oc oe : Obj V} (hra : m.obj? m.root = some oe) (D : Dirty)
    {y : NodeId} (hsl : oc.slot? y = oe.slot? y) :
    ((m.withRoot oc).unswizzle D m.root y = (m.unswizzle D m.root y).withRoot oc ∧
        (m.unswizzle D m.root y).obj? m.root = some oe) ∨
      ∃ s, (m.withRoot oc).unswizzle D m.root y = (m.unswizzle D m.root y).withRoot (oc.setSlot y s) ∧
        (m.unswizzle D m.root y).obj? m.root = some (oe.setSlot y s) := by
  unfold Mem.unswizzle
  rw [withRoot_obj?_root hra, hra]
  simp only
  rw [hsl]
  cases oe.slot? y with
  | none => exact Or.inl ⟨rfl, hra⟩
  | some s =>
    cases s with
    | stream r => exact Or.inl ⟨rfl, hra⟩
    | mem h' =>
      simp only
      by_cases he : h' = m.root
      · subst he
        rw [withRoot_obj?_root hra, hra]
        simp only
        rw [show (m.withRoot oc).detachable D m.root = false from Mem.detachable_root (m.withRoot oc) D,
          Mem.detachable_root m D]
        exact Or.inl ⟨rfl, hra⟩
      · rw [withRoot_obj?_ne he]
        cases m.obj? h' with
        | none => exact Or.inl ⟨rfl, hra⟩
        | some o =>
          simp only
          rw [detachable_withRoot_ne he]
          split
          · exact Or.inr ⟨Slot.stream o.pos, withRoot_setObj_root _ _, Mem.obj?_setObj_self _ _ _⟩
          · exact Or.inl ⟨rfl, hra⟩

/-- An unswizzle of E's root's slot for a pointee that C's root object does not
have: C's memory is related to E's after it too. -/
theorem unswizzle_extra {m : Mem V} {oc oe : Obj V} (hnd : (m.objs.map (·.1)).Nodup)
    (hfr : ∀ h, m.next ≤ h → m.obj? h = none) (hra : m.obj? m.root = some oe) (D : Dirty) (y : NodeId) :
    RootPerm (m.withRoot oc) ((m.unswizzle D m.root y).withRoot oc) ∧
      (((m.unswizzle D m.root y).obj? m.root = some oe) ∨
        ∃ s, (m.unswizzle D m.root y).obj? m.root = some (oe.setSlot y s)) ∧
      ((m.unswizzle D m.root y).objs.map (·.1)).Nodup ∧
      (∀ h, (m.unswizzle D m.root y).next ≤ h → (m.unswizzle D m.root y).obj? h = none) ∧
      (m.unswizzle D m.root y).root = m.root := by
  have hlt : m.root < m.next := by
    apply Nat.lt_of_not_le; intro hle; rw [hfr _ hle] at hra; cases hra
  unfold Mem.unswizzle
  rw [hra]
  simp only
  have hrefl := RootPerm.refl_withRoot (oc := oc) hnd hfr hra
  cases oe.slot? y with
  | none => exact ⟨hrefl, Or.inl hra, hnd, hfr, rfl⟩
  | some s =>
    cases s with
    | stream r => exact ⟨hrefl, Or.inl hra, hnd, hfr, rfl⟩
    | mem h' =>
      simp only
      cases m.obj? h' with
      | none => exact ⟨hrefl, Or.inl hra, hnd, hfr, rfl⟩
      | some o =>
        simp only
        split
        · refine ⟨RootPerm.withRoot_setObj_root hnd hfr hra _, Or.inr ⟨_, Mem.obj?_setObj_self _ _ _⟩,
            nodup_setObj_keys _ _ _ hnd, ?_, rfl⟩
          intro h hh
          rw [Mem.setObj_next] at hh
          rw [Mem.obj?_setObj_ne _ _ (by omega)]
          exact hfr h hh
        · exact ⟨hrefl, Or.inl hra, hnd, hfr, rfl⟩

/-- E's root's slots that C's root object does not have name no object that
may be detached. -/
def ExtraOK (sp : Spec V T) (D : Dirty) (m : Mem V) (oc oe : Obj V) : Prop :=
  sp.virt = true → ∀ y h, y ∉ pointees sp oc.hist → oe.slot? y = some (Slot.mem h) → m.detachable D h = false

theorem slots_any_mem {o : Obj V} (hk : o.KeysND) (h : Nat) :
    o.slots.any (fun q => q.2 == Slot.mem h) = true ↔ ∃ y, o.slot? y = some (Slot.mem h) := by
  constructor
  · intro ha
    obtain ⟨q, hq, hqe⟩ := List.any_eq_true.mp ha
    have hq2 : q.2 = Slot.mem h := by simpa using hqe
    refine ⟨q.1, ?_⟩
    unfold Obj.slot?
    rw [← hq2]
    exact lookup_of_mem o.slots hk q hq
  · rintro ⟨y, hy⟩
    unfold Obj.slot? at hy
    exact List.any_eq_true.mpr ⟨(y, Slot.mem h), mem_of_lookup _ _ _ hy, by simp⟩

/-- A release on the memory with the other root object, when E's root's extra
slots name no object that may be detached: the same. -/
theorem release_withRoot {f : Time} {m : Mem V} {oc oe : Obj V} (hra : m.obj? m.root = some oe)
    (hnd : (m.objs.map (·.1)).Nodup) (hr : RootRel sp f oc oe) {D : Dirty} (hx : ExtraOK sp D m oc oe)
    (hkc : oc.KeysND) (hke : oe.KeysND) (h : Nat) :
    (m.withRoot oc).release D h = (m.release D h).withRoot oc ∧ (m.release D h).obj? m.root = some oe ∧
      (m.release D h).root = m.root := by
  by_cases hh : h = m.root
  · subst hh
    unfold Mem.release Mem.eligible
    have h1 : (m.withRoot oc).detachable D m.root = false := Mem.detachable_root (m.withRoot oc) D
    rw [h1, Mem.detachable_root m D]
    exact ⟨rfl, hra, rfl⟩
  · have hel : (m.withRoot oc).eligible D h = m.eligible D h := by
      unfold Mem.eligible
      rw [detachable_withRoot_ne hh]
      cases hd : m.detachable D h with
      | false => rfl
      | true =>
        simp only [Bool.true_and]
        congr 1
        unfold Mem.incoming
        rw [any_root_split _ (m.withRoot oc).root (m.withRoot oc).objs (by rw [withRoot_keys]; exact hnd),
          any_root_split _ m.root m.objs hnd]
        have hfil : (m.withRoot oc).objs.filter (fun p => p.1 != (m.withRoot oc).root) =
            m.objs.filter (fun p => p.1 != m.root) := by
          unfold Mem.withRoot
          simp only
          generalize m.objs = l
          induction l with
          | nil => rfl
          | cons q l ih =>
            simp only [List.map_cons]
            by_cases hq : q.1 = m.root
            · have : (q.1 == m.root) = true := by simp [hq]
              simp only [this, ↓reduceIte, List.filter_cons, bne_self_eq_false, Bool.false_eq_true]
              rw [ih]
              have : (q.1 != m.root) = false := by simp [hq]
              simp only [this, Bool.false_eq_true, ↓reduceIte]
            · have : (q.1 == m.root) = false := by simp [hq]
              simp only [this, Bool.false_eq_true, ↓reduceIte, List.filter_cons]
              have : (q.1 != m.root) = true := by simp [hq]
              simp only [this, ↓reduceIte, ih]
        rw [hfil, withRoot_root]
        have h1 : List.lookup m.root (m.withRoot oc).objs = some oc := withRoot_obj?_root hra
        have h2 : List.lookup m.root m.objs = some oe := hra
        rw [h1, h2]
        simp only [Option.map_some, Option.getD_some]
        congr 1
        apply Bool.eq_iff_iff.mpr
        rw [slots_any_mem hkc, slots_any_mem hke]
        cases hv : sp.virt with
        | false => rw [hr.nv hv]
        | true =>
          constructor
          · rintro ⟨y, hy⟩
            have hyp : y ∈ pointees sp oc.hist := by
              by_cases hyp : y ∈ pointees sp oc.hist
              · exact hyp
              · rw [hr.noSlot hv y hyp] at hy; cases hy
            exact ⟨y, by rw [← hr.slots y hyp]; exact hy⟩
          · rintro ⟨y, hy⟩
            by_cases hyp : y ∈ pointees sp oc.hist
            · exact ⟨y, by rw [hr.slots y hyp]; exact hy⟩
            · have := hx hv y h hyp hy
              rw [hd] at this; cases this
    unfold Mem.release
    rw [hel]
    split
    · refine ⟨?_, ?_, rfl⟩
      · unfold Mem.withRoot
        simp only
        rw [filter_map_root]
      · show List.lookup m.root (m.objs.filter (fun p => p.1 != h)) = some oe
        rw [lookup_filter_ne h m.root m.objs (Ne.symm hh)]
        exact hra
    · exact ⟨rfl, hra, rfl⟩

theorem unswizzle_root_slot {m : Mem V} {oe : Obj V} (hra : m.obj? m.root = some oe) (D : Dirty) (y : NodeId)
    (h : Nat) (hs : ((m.unswizzle D m.root y).obj? m.root).bind (·.slot? y) = some (Slot.mem h)) :
    m.detachable D h = false := by
  unfold Mem.unswizzle at hs
  rw [hra] at hs
  simp only at hs
  cases hsl : oe.slot? y with
  | none => rw [hsl] at hs; simp only [hra, Option.bind_some, hsl] at hs; cases hs
  | some sl =>
    rw [hsl] at hs
    cases sl with
    | stream r => simp only [hra, Option.bind_some, hsl] at hs; cases hs
    | mem h' =>
      simp only at hs
      cases ho : m.obj? h' with
      | none =>
        rw [ho] at hs
        simp only [hra, Option.bind_some, hsl, Option.some.injEq, Slot.mem.injEq] at hs
        subst hs
        unfold Mem.detachable; rw [ho]
      | some o =>
        rw [ho] at hs
        simp only at hs
        split at hs
        · rw [Mem.obj?_setObj_self] at hs
          simp only [Option.bind_some, Obj.slot?_setSlot, ↓reduceIte, hsl, Option.map_some] at hs
          cases hs
        · simp only [hra, Option.bind_some, hsl, Option.some.injEq, Slot.mem.injEq] at hs
          subst hs
          rename_i hd
          simpa using hd

/-- E's extra unswizzles before a release (C does nothing): afterwards E's root
names no object that may be detached through a slot for y of Y. -/
theorem extras_sim {f : Time} (hv : sp.virt = true) {S0 S : Stream V T} (D : Dirty) {oc : Obj V} :
    ∀ (Y : List NodeId) (m : Mem V) (oe : Obj V), (∀ y ∈ Y, y ∉ pointees sp oc.hist) →
      m.obj? m.root = some oe → (m.objs.map (·.1)).Nodup → (∀ h, m.next ≤ h → m.obj? h = none) →
      RootRel sp f oc oe →
      ∃ oe', RootPerm (m.withRoot oc) (((Y.map (CacheOp.unswizzle m.root)).foldl (Mem.cacheOp sp S0 S D) m).withRoot oc) ∧
        ((Y.map (CacheOp.unswizzle m.root)).foldl (Mem.cacheOp sp S0 S D) m).obj? m.root = some oe' ∧
        ((Y.map (CacheOp.unswizzle m.root)).foldl (Mem.cacheOp sp S0 S D) m).root = m.root ∧
        RootRel sp f oc oe' ∧ oe'.hist = oe.hist ∧
        (((Y.map (CacheOp.unswizzle m.root)).foldl (Mem.cacheOp sp S0 S D) m).objs.map (·.1)).Nodup ∧
        (∀ h, ((Y.map (CacheOp.unswizzle m.root)).foldl (Mem.cacheOp sp S0 S D) m).next ≤ h →
          ((Y.map (CacheOp.unswizzle m.root)).foldl (Mem.cacheOp sp S0 S D) m).obj? h = none) ∧
        (∀ y ∈ Y, ∀ h, oe'.slot? y = some (Slot.mem h) →
          ((Y.map (CacheOp.unswizzle m.root)).foldl (Mem.cacheOp sp S0 S D) m).detachable D h = false) ∧
        (∀ z, z ∉ Y → oe'.slot? z = oe.slot? z) ∧
        (∀ h, ((Y.map (CacheOp.unswizzle m.root)).foldl (Mem.cacheOp sp S0 S D) m).detachable D h = m.detachable D h) := by
  intro Y
  induction Y with
  | nil =>
    intro m oe _ hra hnd hfr hr
    exact ⟨oe, RootPerm.refl_withRoot hnd hfr hra, hra, rfl, hr, rfl, hnd, hfr, fun _ hy => by simp at hy,
      fun _ _ => rfl, fun _ => rfl⟩
  | cons y Y ih =>
    intro m oe hY hra hnd hfr hr
    simp only [List.map_cons, List.foldl_cons]
    have hstep : Mem.cacheOp sp S0 S D m (CacheOp.unswizzle m.root y) = m.unswizzle D m.root y := rfl
    rw [hstep]
    obtain ⟨p1, ho1, hnd1, hfr1, hrt1⟩ := unswizzle_extra (oc := oc) hnd hfr hra D y
    have hy : y ∉ pointees sp oc.hist := hY y List.mem_cons_self
    obtain ⟨oe1, ho1', hr1, hh1, hs1, hz1⟩ : ∃ oe1, (m.unswizzle D m.root y).obj? m.root = some oe1 ∧
        RootRel sp f oc oe1 ∧ oe1.hist = oe.hist ∧
        (∀ h, oe1.slot? y = some (Slot.mem h) → (m.unswizzle D m.root y).detachable D h = false) ∧
        (∀ z, z ≠ y → oe1.slot? z = oe.slot? z) := by
      have hsl : ∀ oe1, (m.unswizzle D m.root y).obj? m.root = some oe1 →
          ∀ h, oe1.slot? y = some (Slot.mem h) → (m.unswizzle D m.root y).detachable D h = false := by
        intro oe1 ho h hs
        rw [Mem.detachable_unswizzle]
        exact unswizzle_root_slot hra D y h (by rw [ho]; exact hs)
      rcases ho1 with ho | ⟨s, ho⟩
      · exact ⟨oe, ho, hr, rfl, hsl oe ho, fun _ _ => rfl⟩
      · refine ⟨oe.setSlot y s, ho, hr.setSlotE hv hy s, rfl, hsl _ ho, fun z hz => ?_⟩
        rw [Obj.slot?_setSlot]; simp [hz]
    have hra1 : (m.unswizzle D m.root y).obj? (m.unswizzle D m.root y).root = some oe1 := by rw [hrt1]; exact ho1'
    obtain ⟨oe', q1, q2, q3, q4, q5, q6, q7, q8, q9, q10⟩ :=
      ih (m.unswizzle D m.root y) oe1 (fun z hz => hY z (List.mem_cons_of_mem _ hz)) hra1 hnd1 hfr1 hr1
    rw [hrt1] at q1 q2 q3 q6 q7 q8 q10
    refine ⟨oe', p1.trans q1, q2, q3, q4, by rw [q5, hh1], q6, q7, ?_, ?_, ?_⟩
    · intro z hz h hs
      by_cases hzY : z ∈ Y
      · exact q8 z hzY h hs
      · rcases List.mem_cons.mp hz with rfl | hz'
        · rw [q9 z hzY] at hs
          rw [q10 h]
          exact hs1 h hs
        · exact absurd hz' hzY
    · intro z hz
      simp only [List.mem_cons, not_or] at hz
      rw [q9 z hz.2, hz1 z hz.1]
    · intro h
      rw [q10 h, Mem.detachable_unswizzle]

theorem follow4_root' {S0 S : Stream V T} (m : Mem V) (hp : Nat) (y : NodeId) (w : Bool) :
    (m.follow4 sp S0 S hp y w).1.root = m.root := by
  rw [follow4_eq]
  cases hrc : m.reached4 sp S0 S hp y with
  | none => rfl
  | some p =>
    obtain ⟨m1, h1⟩ := p
    have := reached4_root hrc
    cases w
    · simp only [Bool.false_eq_true, ↓reduceIte]; rw [swz_root', this]
    · simp only [↓reduceIte]; rw [promote_root, swz_root', this]

theorem readAt4_root {S0 S : Stream V T} : ∀ (fuel : Nat) (m : Mem V) (t : Time) (h : Nat),
    (m.readAt4 sp S0 S fuel t h).1.root = m.root := by
  intro fuel
  induction fuel with
  | zero => intro m t h; rfl
  | succ fuel ih =>
    intro m t h
    cases ho : m.obj? h with
    | none => simp only [Mem.readAt4, ho]
    | some o =>
      rw [readAt4_succ_eq sp S0 S fuel m t h ho]
      clear ho
      generalize sp.live (o.hist.upTo t) = L
      generalize ([(o.node, o.nodeAt t)] : List (NodeId × Node V)) = l0
      induction L generalizing m l0 with
      | nil => rfl
      | cons y L ihL =>
        simp only [List.foldl_cons]
        have : (readStep4 sp S0 S fuel t h o (m, l0) y).1.root = m.root := by
          unfold readStep4
          have hf := follow4_root' (sp := sp) (S0 := S0) (S := S) m h y false
          generalize m.follow4 sp S0 S h y false = F at hf
          obtain ⟨m1, r⟩ := F
          simp only at hf ⊢
          cases r with
          | none => exact hf
          | some h1 =>
            simp only
            cases m1.obj? h1 with
            | none => exact hf
            | some o1 =>
              simp only
              split
              · rw [ih]; exact hf
              · exact hf
        generalize readStep4 sp S0 S fuel t h o (m, l0) y = A at this
        obtain ⟨a, la⟩ := A
        rw [← this]
        exact ihL a la

theorem Mem.cacheOp_root {S0 S : Stream V T} (m : Mem V) (D : Dirty) (op : CacheOp) :
    (m.cacheOp sp S0 S D op).root = m.root := by
  cases op with
  | read t =>
    show (m.read4 sp S0 S t).1.root = m.root
    unfold Mem.read4
    cases m.obj? m.root with
    | none => rfl
    | some o => exact readAt4_root _ m t _
  | unswizzle h y =>
    show (m.unswizzle D h y).root = m.root
    unfold Mem.unswizzle
    split
    · split
      · split
        · split <;> rfl
        · rfl
      · rfl
    · rfl
  | release h =>
    show (m.release D h).root = m.root
    unfold Mem.release; split <;> rfl

theorem Mem.cacheOps_root {S0 S : Stream V T} (D : Dirty) :
    ∀ (ops : List CacheOp) (m : Mem V), (ops.foldl (Mem.cacheOp sp S0 S D) m).root = m.root := by
  intro ops
  induction ops with
  | nil => intro m; rfl
  | cons op ops ih => intro m; simp only [List.foldl_cons]; rw [ih, Mem.cacheOp_root]

/-- E's cache operations: C's, with the extra unswizzles X before each release. -/
def augment (X : List CacheOp) (ops : List CacheOp) : List CacheOp :=
  ops.flatMap (fun op => match op with
    | CacheOp.release h => X ++ [CacheOp.release h]
    | op => [op])

theorem augment_cons (X : List CacheOp) (op : CacheOp) (ops : List CacheOp) :
    augment X (op :: ops) = (match op with
      | CacheOp.release h => X ++ [CacheOp.release h]
      | op => [op]) ++ augment X ops := by
  unfold augment; rw [List.flatMap_cons]

theorem unswizzle_noSlot {m : Mem V} {o : Obj V} {D : Dirty} {hp : Nat} {y : NodeId} (ho : m.obj? hp = some o)
    (hs : o.slot? y = none) : m.unswizzle D hp y = m := by
  unfold Mem.unswizzle; rw [ho]; simp only [hs]

/-- The cache operations of C after a transaction, from the first available
time on: E's with the extra unswizzles. -/
theorem ops_sim {f : Time} {db1 db : DB V T} {j1 k c : Nat} (hls : LiveSub sp) (hL : Later sp db1 db j1 k)
    (hcut : CutOK sp c db1 j1) (hf : f = lastFa db1.S) (Y : List NodeId) (hYnv : sp.virt = false → Y = []) :
    ∀ (ops : List CacheOp) (mC mE : Mem V) (oc oe : Obj V),
      (∀ t, CacheOp.read t ∈ ops → lastFa db1.S ≤ t ∧ t ≤ k) →
      EInv sp db db1.S k mE → HInv sp db db1.S k mE → NInv db db1.S mE → SlotsND mC → SlotsND mE →
      SimC sp f mC mE oc oe → (∀ y ∈ Y, y ∉ pointees sp oc.hist) →
      (∀ y, y ∈ pointees sp oe.hist → y ∉ pointees sp oc.hist → y ∈ Y) →
      ∃ oc' oe', SimC sp f (ops.foldl (Mem.cacheOp sp (cutStream c db1.S) (cutStream c db.S) db.D) mC)
          ((augment (Y.map (CacheOp.unswizzle mE.root)) ops).foldl (Mem.cacheOp sp db1.S db.S db.D) mE) oc' oe' ∧
        oc'.hist = oc.hist ∧ oe'.hist = oe.hist := by
  have hinv := hL.inv
  intro ops
  induction ops with
  | nil =>
    intro mC mE oc oe _ _ _ _ _ _ hsim _ _
    exact ⟨oc, oe, hsim, rfl, rfl⟩
  | cons op ops ih =>
    intro mC mE oc oe hreads hm hh hn hsC hsE hsim hY hcov
    rw [augment_cons, List.foldl_append, List.foldl_cons]
    have hreads' : ∀ t, CacheOp.read t ∈ ops → lastFa db1.S ≤ t ∧ t ≤ k :=
      fun t ht => hreads t (List.mem_cons_of_mem _ ht)
    -- one operation, as a step to apply the induction to
    have key : ∀ (mC' mE' : Mem V) (oc' oe' : Obj V), mE'.root = mE.root →
        EInv sp db db1.S k mE' → HInv sp db db1.S k mE' → NInv db db1.S mE' → SlotsND mC' → SlotsND mE' →
        SimC sp f mC' mE' oc' oe' → oc'.hist = oc.hist → oe'.hist = oe.hist →
        ∃ oc'' oe'', SimC sp f (ops.foldl (Mem.cacheOp sp (cutStream c db1.S) (cutStream c db.S) db.D) mC')
            ((augment (Y.map (CacheOp.unswizzle mE.root)) ops).foldl (Mem.cacheOp sp db1.S db.S db.D) mE') oc'' oe'' ∧
          oc''.hist = oc.hist ∧ oe''.hist = oe.hist := by
      intro mC' mE' oc' oe' hrt' hm' hh' hn' hsC' hsE' hsim' hc' he'
      have := ih mC' mE' oc' oe' hreads' hm' hh' hn' hsC' hsE' hsim' (by rw [hc']; exact hY)
        (by rw [hc', he']; exact hcov)
      rw [hrt'] at this
      obtain ⟨oc'', oe'', h1, h2, h3⟩ := this
      exact ⟨oc'', oe'', h1, by rw [h2, hc'], by rw [h3, he']⟩
    have hraE : mE.obj? mE.root = some oe := hsim.rootE
    have hkc : oc.KeysND := hsC.obj (h := mC.root) (by
      rw [hsim.perm.rootObj, withRoot_root]; exact withRoot_obj?_root hraE)
    cases op with
    | read t =>
      simp only [List.foldl_cons, List.foldl_nil]
      have ht := hreads t List.mem_cons_self
      have hf' : f ≤ t := by rw [hf]; exact ht.1
      obtain ⟨oc1, oe1, hsim1, hh1, hh1'⟩ := read4_sim hls hL hcut ht.1 hf' ht.2 hm hh hn hsim
      exact key _ _ oc1 oe1 (Mem.cacheOp_root mE db.D (CacheOp.read t)) (hm.cacheOp hinv (CacheOp.read t))
        (hh.cacheOp hinv hls hm (CacheOp.read t)) (hn.cacheOp hinv hm (CacheOp.read t))
        (hsC.cacheOp sp _ _ db.D (CacheOp.read t)) (hsE.cacheOp sp _ _ db.D (CacheOp.read t)) hsim1 hh1 hh1'
    | unswizzle h y =>
      simp only [List.foldl_cons, List.foldl_nil]
      have hp1 := hsim.perm.unswizzle db.D h y
      have hrtU : (mE.unswizzle db.D h y).root = mE.root := Mem.cacheOp_root (sp := sp) (S0 := db1.S) (S := db.S)
        mE db.D (CacheOp.unswizzle h y)
      obtain ⟨oc1, oe1, hsim1, hh1, hh1'⟩ : ∃ oc1 oe1, SimC sp f (mC.unswizzle db.D h y) (mE.unswizzle db.D h y) oc1 oe1 ∧
          oc1.hist = oc.hist ∧ oe1.hist = oe.hist := by
        by_cases hhr : h = mE.root
        · subst hhr
          by_cases hA : y ∈ pointees sp oc.hist ∨ sp.virt = false
          · have hsl : oc.slot? y = oe.slot? y := by
              rcases hA with hA | hA
              · exact hsim.rel.slots y hA
              · rw [hsim.rel.nv hA]
            rcases unswizzle_withRoot_root hraE db.D hsl with ⟨e1, e2⟩ | ⟨s, e1, e2⟩
            · rw [e1] at hp1
              exact ⟨oc, oe, ⟨hp1, fun hv => by rw [hsim.nv hv, e1], by rw [hrtU]; exact e2, hsim.rel⟩, rfl, rfl⟩
            · rw [e1] at hp1
              exact ⟨oc.setSlot y s, oe.setSlot y s, ⟨hp1, fun hv => by rw [hsim.nv hv, e1], by rw [hrtU]; exact e2,
                hsim.rel.setSlot hA s⟩, rfl, rfl⟩
          · have hv : sp.virt = true := by
              cases hvv : sp.virt with
              | false => exact absurd (Or.inr hvv) hA
              | true => rfl
            have hy : y ∉ pointees sp oc.hist := fun h' => hA (Or.inl h')
            have hC : (mE.withRoot oc).unswizzle db.D mE.root y = mE.withRoot oc :=
              unswizzle_noSlot (withRoot_obj?_root hraE) (hsim.rel.noSlot hv y hy)
            obtain ⟨p2, ho2, -, -, hrt2⟩ := unswizzle_extra (oc := oc) hm.objNodup hm.fresh hraE db.D y
            rw [hC] at hp1
            rcases ho2 with ho2 | ⟨s, ho2⟩
            · exact ⟨oc, oe, ⟨hp1.trans p2, fun h' => absurd h' (by simp [hv]), by rw [hrt2]; exact ho2,
                hsim.rel⟩, rfl, rfl⟩
            · exact ⟨oc, oe.setSlot y s, ⟨hp1.trans p2, fun h' => absurd h' (by simp [hv]),
                by rw [hrt2]; exact ho2, hsim.rel.setSlotE hv hy s⟩, rfl, rfl⟩
        · obtain ⟨e1, e2, e3⟩ := unswizzle_withRoot_ne (oc := oc) hraE db.D hhr y
          rw [e1] at hp1
          exact ⟨oc, oe, ⟨hp1, fun hv => by rw [hsim.nv hv, e1], by rw [e3]; exact e2, hsim.rel⟩, rfl, rfl⟩
      exact key _ _ oc1 oe1 hrtU (hm.cacheOp hinv (CacheOp.unswizzle h y))
        (hh.cacheOp hinv hls hm (CacheOp.unswizzle h y)) (hn.cacheOp hinv hm (CacheOp.unswizzle h y))
        (hsC.cacheOp sp _ _ db.D (CacheOp.unswizzle h y)) (hsE.cacheOp sp _ _ db.D (CacheOp.unswizzle h y))
        hsim1 hh1 hh1'
    | release h =>
      simp only [List.foldl_cons, List.foldl_append, List.foldl_nil]
      have hmX := EInv.cacheOps hinv (Y.map (CacheOp.unswizzle mE.root)) mE hm
      have hhX := HInv.cacheOps hinv hls (Y.map (CacheOp.unswizzle mE.root)) mE hm hh
      have hnX := NInv.cacheOps hinv (Y.map (CacheOp.unswizzle mE.root)) mE hm hn
      have hsX := SlotsND.cacheOps sp db1.S db.S db.D (Y.map (CacheOp.unswizzle mE.root)) mE hsE
      have hrtX := Mem.cacheOps_root (sp := sp) (S0 := db1.S) (S := db.S) db.D (Y.map (CacheOp.unswizzle mE.root)) mE
      generalize hmXd : (Y.map (CacheOp.unswizzle mE.root)).foldl (Mem.cacheOp sp db1.S db.S db.D) mE = mX
        at hmX hhX hnX hsX hrtX
      obtain ⟨oeX, q1, q2, q4, q5, q6, q8⟩ : ∃ oeX, RootPerm (mE.withRoot oc) (mX.withRoot oc) ∧
          mX.obj? mX.root = some oeX ∧ RootRel sp f oc oeX ∧ oeX.hist = oe.hist ∧
          (mX.objs.map (·.1)).Nodup ∧ ExtraOK sp db.D mX oc oeX := by
        cases hv : sp.virt with
        | true =>
          obtain ⟨oeX, q1, q2, q3, q4, q5, q6, -, q8, -, -⟩ :=
            extras_sim (S0 := db1.S) (S := db.S) hv db.D Y mE oe hY hraE hm.objNodup hm.fresh hsim.rel
          rw [hmXd] at q1 q2 q3 q6 q8
          refine ⟨oeX, q1, by rw [hrtX]; exact q2, q4, q5, q6, ?_⟩
          intro _ y h' hy hs
          have hyE : y ∈ pointees sp oe.hist := by rw [← q5]; exact q4.keysE hv y (by rw [hs]; rfl)
          exact q8 y (hcov y hyE hy) h' hs
        | false =>
          have hY0 := hYnv hv
          subst hY0
          simp only [List.map_nil, List.foldl_nil] at hmXd
          subst hmXd
          exact ⟨oe, RootPerm.refl_withRoot hm.objNodup hm.fresh hraE, hraE, hsim.rel, rfl, hm.objNodup,
            fun h' => absurd h' (by simp [hv])⟩
      have hkeX : oeX.KeysND := hsX.obj q2
      obtain ⟨r1, r2, r3⟩ := release_withRoot q2 q6 q4 q8 hkc hkeX h
      have p1 := hsim.perm.release db.D h
      have p2 := q1.release db.D h
      rw [r1] at p2
      have hsimR : SimC sp f (mC.release db.D h) (mX.release db.D h) oc oeX := by
        refine ⟨p1.trans p2, ?_, by rw [r3]; exact r2, q4⟩
        intro hv
        have hY0 := hYnv hv
        subst hY0
        simp only [List.map_nil, List.foldl_nil] at hmXd
        subst hmXd
        rw [hsim.nv hv, r1]
      exact key _ _ oc oeX (show (mX.release db.D h).root = mE.root by rw [r3, hrtX])
        (hmX.cacheOp hinv (CacheOp.release h))
        (hhX.cacheOp hinv hls hmX (CacheOp.release h)) (hnX.cacheOp hinv hmX (CacheOp.release h))
        (hsC.cacheOp sp _ _ db.D (CacheOp.release h)) (hsX.cacheOp sp _ _ db.D (CacheOp.release h)) hsimR rfl q5

end Ops

end SIS
