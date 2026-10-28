/-
Proofs about rule 4 by position after a cut (bergdb 005-62, question 2):
`Rule4PosCut_handles` and `RunPosCut_handles` of SIS/HandleReclaimTheorems.lean.
The startup with handles from a stream cut safely holds, before rule 4, the
objects of the startup from the whole stream but for the root's object
(`sectionPos_sim`, SIS/Proof/CutLazyStart.lean). Rule 4 by position
(`HMem.linkDPosFrom`) differs from rule 4 by node id only at a pointer that it
leaves: one that Java skips, of a node of D below the stream's first position,
or one that neither `posToId` nor `byPos` finds. A skipped pointer names no node
with a canonical object (`cutSkip_none`): below the cut, a pointer of a node of
D names its pointee's latest version, which is then not in D and not current
from the first available time on, so no object of it is canonical. A pointer of
the whole stream's startup that rule 4 by position finds is found on the cut
stream too: `posToId` and the canonical objects' positions do not see the cut
(`inPosToId_cut`). Every restart of a run with cuts is from the run's stream cut
at the largest cut so far, where the cut is safe (T12's `RunSimH`), so the run
with rule 4 by position is the run with rule 4 by node id (`runPosCut_handles`).
-/
import SIS.Proof.HandleCutSkip
import SIS.Proof.HandleLinkPos

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## Rule 4 by position with a first position -/

/-- Rule 4 by position with a first position is rule 4 by position where every
pointer it skips (of a pinned object of a node of D, holding no handle, naming a
record below the first position) names a node without a canonical object, which
rule 4 by position leaves too. -/
theorem HMem.linkDPosFrom_eq_linkDPos (sp : Spec V T) (S : Stream V T) (first : Nat) (m : HMem V)
    (D : Dirty)
    (h : ∀ p ∈ m.objs, p.2.canonical = true → inD D p.2.node = true → ∀ q ∈ p.2.ptrs,
      q.2.handle = none → ∀ r, q.2.ref = some r → r < first → m.canonicalOf q.1 = none) :
    m.linkDPosFrom sp S first D = m.linkDPos sp S D := by
  unfold HMem.linkDPosFrom HMem.linkDPos
  congr 1
  apply List.map_congr_left
  intro p hp
  by_cases hpin : (p.2.canonical && (inD D p.2.node || p.1 == m.root)) = true
  · simp only [hpin, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    congr 2
    apply List.map_congr_left
    intro q hq
    obtain ⟨y, pt⟩ := q
    cases hh : pt.handle with
    | some n => simp
    | none =>
      cases hr : pt.ref with
      | none => simp
      | some r =>
        simp only
        by_cases hskip : (inD D p.2.node && decide (r < first)) = true
        · simp only [hskip, ↓reduceIte]
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hskip
          have hc : m.canonicalOf y = none :=
            h p hp (by simp only [Bool.and_eq_true] at hpin; exact hpin.1) hskip.1 (y, pt) hq hh r hr hskip.2
          have hbp : m.byPos y r = none := by unfold HMem.byPos; rw [hc]
          simp only [hc, hbp]
          split <;> simp
        · simp only [hskip, Bool.false_eq_true, ↓reduceIte]
  · simp [hpin]

/-- With first position 0, rule 4 by position with a first position is rule 4
by position. -/
theorem HMem.linkDPosFrom_zero (sp : Spec V T) (S : Stream V T) (m : HMem V) (D : Dirty) :
    m.linkDPosFrom sp S 0 D = m.linkDPos sp S D :=
  HMem.linkDPosFrom_eq_linkDPos sp S 0 m D (fun _ _ _ _ _ _ _ _ _ h => absurd h (Nat.not_lt_zero _))

/-- The startup with rule 4 by position with first position 0 is the startup with
rule 4 by position. -/
theorem handleStartupPosFrom_zero (sp : Spec V T) (S : Stream V T) :
    handleStartupPosFrom sp 0 S = handleStartupPos sp S := by
  unfold handleStartupPosFrom handleStartupPos
  exact HMem.linkDPosFrom_zero sp S _ _

/-! ## `posToId` on a cut stream -/

section Cut

variable {S : Stream V T} {c : Nat}

theorem take_cutStream (f : Nat) : (cutStream c S).take f = cutStream c (S.take f) := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_take, cutStream_getElem?, cutStream_getElem?, List.getElem?_take]
  by_cases hi : i < f <;> simp [hi]

/-- `posToId` does not see a cut at or before the startup pos: its records are
after the cut, and the latest version of a node before one of them keeps its
record. -/
theorem inPosToId_cut (sp : Spec V T) {s : Nat} (hcs : c ≤ s) (y : NodeId) (r : Nat) :
    inPosToId sp (cutStream c S) s y r = inPosToId sp S s y r := by
  unfold inPosToId
  rw [cutStream_length]
  have hany : ∀ (l : List Nat) (p : Nat → Bool), l.any p = (l.map p).any id := by
    intro l p; rw [List.any_map]; rfl
  conv => lhs; rw [hany]
  conv => rhs; rw [hany]
  congr 1
  apply List.map_congr_left
  intro f hf
  have hsf : s ≤ f := (List.mem_range'_1.mp hf).1
  rw [versionAt_cut_ge (Nat.le_trans hcs hsf), take_cutStream, lv_cut_recNo]

end Cut

/-! ## The pointers that rule 4 by position finds, on the whole stream -/

section Whole

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

/-- On the memory before rule 4 of the startup from the stream after T(k), each
pointer of a pinned object on a key level that holds no handle and names a
record, to a node with a canonical object, is in `posToId` or at the canonical
object's position (the condition of `HMem.linkDPos_eq_linkD`; `rule4Pos_handles`'s
argument). -/
theorem rule4Pos_cond (hok : RunOK sp al ts) (hph : PhysRunOK sp al ts) (hev : EvictRunOK sp al ts)
    (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) {k : Nat} (hk : k ≤ ts.length) :
    ∀ p ∈ (((lazyStartup sp (st sp al ts k).S).sectionPos (st sp al ts k).S).toH).objs,
      (p.2.canonical && (inD (startup sp (st sp al ts k).S).D p.2.node ||
        p.1 == (((lazyStartup sp (st sp al ts k).S).sectionPos (st sp al ts k).S).toH).root)) = true →
      isKeyLevel sp p.2.isData p.2.level = true → ∀ q ∈ p.2.ptrs, q.2.handle = none →
      ∀ r, q.2.ref = some r → ∀ b,
        (((lazyStartup sp (st sp al ts k).S).sectionPos (st sp al ts k).S).toH).canonicalOf q.1 = some b →
        inPosToId sp (st sp al ts k).S
            (((lazyStartup sp (st sp al ts k).S).sectionPos (st sp al ts k).S).toH).s q.1 r = true ∨
          ((((lazyStartup sp (st sp al ts k).S).sectionPos (st sp al ts k).S).toH).obj? b).bind (·.pos) =
            some r := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hinv := inv_st sp al ts hok hst k hk
  have hdo := dataOnce_st sp al ts hok hst k hk
  obtain ⟨hri, hm⟩ := rinv_lazyStartup hok hph hj hmk hev hk
  have hs0 : (lazyStartup sp (st sp al ts k).S).s = lastSp (st sp al ts k).S := hm.sEq
  have hnd : ((((lazyStartup sp (st sp al ts k).S).sectionPos (st sp al ts k).S).toH).objs.map
      (·.1)).Nodup := by
    rw [Mem.toH_objs, List.map_map]
    have h1 : (((lazyStartup sp (st sp al ts k).S).sectionPos (st sp al ts k).S).objs.map (·.1)).Nodup := by
      rw [Mem.sectionPos_keys]; exact hm.nodup
    exact (List.Sublist.map _ List.filter_sublist).nodup h1
  intro p hp _ hkl q hq hh r hr b hb
  obtain ⟨y, pt⟩ := q
  simp only at hh hr hb ⊢
  have hobj := lookup_of_mem _ hnd p hp
  obtain ⟨hver, hfr, hnear, hpt, n, hn, hnh, hnl⟩ := before_ptr_facts hok hph hj hmk hev hk hobj hq hh hr
  obtain ⟨hpos, -⟩ := before_canon hok hph hj hmk hev hk hb
  obtain ⟨u, hu⟩ := hver
  obtain ⟨-, hur, ny, hny, -, hnyl, hnyd⟩ := hinv.version_node hu
  have hdata : u.isData = true → (((((lazyStartup sp (st sp al ts k).S).sectionPos
      (st sp al ts k).S).toH).obj? b).bind (·.pos)) = some r := by
    intro hud
    rw [hpos, hdo y ny r u hny (by rw [← hnyd]; exact hud) hu, Option.map_some, hur]
  have hs1 : (((lazyStartup sp (st sp al ts k).S).sectionPos (st sp al ts k).S).toH).s =
      lastSp (st sp al ts k).S := hs0
  rw [hs1]
  by_cases hrs : lastSp (st sp al ts k).S ≤ r
  · cases hud : u.isData
    · exact Or.inl (inPosToId_of_section hrs hu hud)
    · exact Or.inr (hdata hud)
  · cases hnw : newest (st sp al ts k).S (lastSp (st sp al ts k).S) y with
    | none =>
      right
      rw [hpos]
      unfold ruleRRef at hfr
      rw [hnw] at hfr
      exact hfr.symm
    | some wn =>
      left
      obtain ⟨f0, hf0, hwf0⟩ := newest_some hnw
      obtain ⟨f, w, hsf, hwf, hmin⟩ := first_version (f0 + 1) f0 wn (by omega) hf0 hwf0
      obtain ⟨-, hwr, nw, hnw', -, hnwl, hnwd⟩ := hinv.version_node hwf
      rw [hny, Option.some.injEq] at hnw'
      subst hnw'
      have hfr' : r < f := by omega
      apply inPosToId_of_prev hsf hwf
      · have hwd : w.isData = false := by
          cases hwd : w.isData
          · rfl
          · exfalso
            have h1 := hdo y ny f w hny (by rw [← hnwd]; exact hwd) hwf
            have h2 := hdo y ny r u hny (by rw [← hnwd]; exact hwd) hu
            rw [h1, Option.some.injEq] at h2
            subst h2
            omega
        unfold isKeyLevel at hkl ⊢
        rw [hwd]
        simp only [Bool.not_false, Bool.true_and]
        cases hv : sp.virt
        · rfl
        · rw [hv] at hkl
          simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hkl
          simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq]
          have hyp : y ∈ pointees sp n.hist := by rw [← hnh]; exact hpt
          obtain ⟨e, he, hye⟩ := (mem_pointees sp _ y).mp hyp
          obtain ⟨my, hmy, hlt⟩ := hinv.ptrs p.2.node n hn e he y hye
          rw [hny, Option.some.injEq] at hmy
          subst hmy
          rw [hnwl]
          omega
      · have hl : Stream.lv ((st sp al ts k).S.take f) y = some u := by
          apply (lv_eq_some_iff _ y u).mpr
          refine ⟨r, ?_, fun r' hr' => ?_⟩
          · rw [versionAt_take]; simp [hfr', hu]
          · rw [versionAt_take]
            by_cases h' : r' < f
            · simp only [h', ↓reduceIte]
              by_cases h'' : r' < lastSp (st sp al ts k).S
              · exact hnear r' hr' h''
              · exact hmin r' (by omega) h'
            · simp [h']
        rw [hl, Option.map_some, hur]

end Whole

/-! ## The startup from a cut stream -/

section CutStart

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

/-- The same on the memory before rule 4, with handles: a pointer of the canonical
object of a node of D that holds no handle and names a record below c names a node
without a canonical object. -/
theorem cutSkip_none (hok : RunOK sp al ts) (hph : PhysRunOK sp al ts) (hev : EvictRunOK sp al ts)
    (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) {k c : Nat} (hk : k ≤ ts.length)
    (hcut : CutOK sp c (st sp al ts k) k) :
    ∀ p ∈ (((lazyStartup sp (st sp al ts k).S).sectionPos (st sp al ts k).S).toH).objs,
      p.2.canonical = true → inD (startup sp (st sp al ts k).S).D p.2.node = true →
      ∀ q ∈ p.2.ptrs, q.2.handle = none → ∀ r, q.2.ref = some r → r < c →
      (((lazyStartup sp (st sp al ts k).S).sectionPos (st sp al ts k).S).toH).canonicalOf q.1 = none := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  obtain ⟨-, hm⟩ := rinv_lazyStartup hok hph hj hmk hev hk
  have hD : (startup sp (st sp al ts k).S).D = (st sp al ts k).D := (T1_strong sp al ts hok hst hk).2
  have hnd : ((((lazyStartup sp (st sp al ts k).S).sectionPos (st sp al ts k).S).toH).objs.map
      (·.1)).Nodup := by
    rw [Mem.toH_objs, List.map_map]
    have h1 : (((lazyStartup sp (st sp al ts k).S).sectionPos (st sp al ts k).S).objs.map (·.1)).Nodup := by
      rw [Mem.sectionPos_keys]; exact hm.nodup
    exact (List.Sublist.map _ List.filter_sublist).nodup h1
  have hnd0 := tblND_lazyStartup sp (st sp al ts k).S
  intro p hp _ hpD q hq hh r hr hrc
  obtain ⟨y, pt⟩ := q
  simp only at hh hr ⊢
  have hobj := lookup_of_mem _ hnd p hp
  obtain ⟨o0, ho0, hsl, hn, -, -⟩ := before_ptr hok hph hj hmk hev hk hobj hq hh hr
  rw [hD, hn] at hpD
  have h0 := cutSkip_lazy hok hph hev hj hmk hk hcut ho0 hpD hsl hrc
  generalize hm0 : lazyStartup sp (st sp al ts k).S = m0 at hm hnd0 h0 ⊢
  have htbl1 : ∀ z a, (m0.sectionPos (st sp al ts k).S).tableOf z = some a →
      ∃ o, (m0.sectionPos (st sp al ts k).S).obj? a = some o ∧ o.node = z := by
    intro z a ht
    obtain ⟨o, ho, hon⟩ := hm.tbl z a ht
    refine ⟨_, by rw [Mem.sectionPos_obj?, ho]; rfl, ?_⟩
    exact (sectionPosObj_fields (st sp al ts k).S m0.s o).1.trans hon
  rw [Mem.toH_canonicalOf (m := m0.sectionPos (st sp al ts k).S) hnd0 htbl1, Mem.sectionPos_canonicalOf]
  exact h0

/-- The objects of a memory with handles with another object at the root's
address: the memory's other objects, and that object at the root's address. -/
theorem HMem.mem_withRoot_objs {m : HMem V} {o' : HObj V} {p : Nat × HObj V}
    (hp : p ∈ (m.withRoot o').objs) : (p.1 ≠ m.root ∧ p ∈ m.objs) ∨ (p.1 = m.root ∧ p.2 = o') := by
  unfold HMem.withRoot at hp
  obtain ⟨p0, hp0, rfl⟩ := List.mem_map.mp hp
  by_cases h : p0.1 = m.root
  · right
    have : (p0.1 == m.root) = true := by simp [h]
    simp only [this, ↓reduceIte]
    simp
  · left
    have : (p0.1 == m.root) = false := by simp [h]
    simp only [this, Bool.false_eq_true, ↓reduceIte]
    exact ⟨h, hp0⟩

/-- Rule 4 by position with a first position, on the stream after T(k) cut safely
at c, is rule 4 by node id, if no pointer that it skips (of the canonical object of
a node of D, in the memory before rule 4 from the whole stream, holding no handle,
naming a record below the first position) names a node with a canonical object. -/
theorem handleStartupPosFrom_cut (hok : RunOK sp al ts) (hph : PhysRunOK sp al ts)
    (hev : EvictRunOK sp al ts) (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true)
    (hex : ExecRootOK sp) (hvl : VirtLiveOK sp) {k c first : Nat} (hk : k ≤ ts.length)
    (hcut : CutOK sp c (st sp al ts k) k)
    (hskip : ∀ p ∈ (((lazyStartup sp (st sp al ts k).S).sectionPos (st sp al ts k).S).toH).objs,
      p.2.canonical = true → inD (startup sp (st sp al ts k).S).D p.2.node = true →
      ∀ q ∈ p.2.ptrs, q.2.handle = none → ∀ r, q.2.ref = some r → r < first →
      (((lazyStartup sp (st sp al ts k).S).sectionPos (st sp al ts k).S).toH).canonicalOf q.1 = none) :
    handleStartupPosFrom sp first (cutStream c (st sp al ts k).S) =
      handleStartup sp (cutStream c (st sp al ts k).S) := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hinv := inv_st sp al ts hok hst k hk
  obtain ⟨oc, oe, hsec, hraP, hrr, -⟩ := sectionPos_sim hok hph hev hj hmk hex hvl hk hcut
  have hfs := st_fa_le sp al ts hk
  have hcs : c ≤ lastSp (st sp al ts k).S := Nat.le_trans hcut.1 hfs
  have hD : (startup sp (cutStream c (st sp al ts k).S)).D = (startup sp (st sp al ts k).S).D := by
    rw [startup, startup, startup_D, startup_D, sectionD_cut hcs]
  obtain ⟨hri, hm⟩ := rinv_lazyStartup hok hph hj hmk hev hk
  have hcond := rule4Pos_cond hok hph hev hj hmk hk
  have hnd0 := tblND_lazyStartup sp (st sp al ts k).S
  have hs0 : (lazyStartup sp (st sp al ts k).S).s = lastSp (st sp al ts k).S := hm.sEq
  have hnd : ((((lazyStartup sp (st sp al ts k).S).sectionPos (st sp al ts k).S).toH).objs.map
      (·.1)).Nodup := by
    rw [Mem.toH_objs, List.map_map]
    have h1 : (((lazyStartup sp (st sp al ts k).S).sectionPos (st sp al ts k).S).objs.map (·.1)).Nodup := by
      rw [Mem.sectionPos_keys]; exact hm.nodup
    exact (List.Sublist.map _ List.filter_sublist).nodup h1
  -- The root's object is in the node table.
  obtain ⟨hrt, -⟩ := hm.root
  -- The cut startup's root object has no repeated slots.
  have hndC : oc.KeysND := by
    have hs := (slotsND_lazyStartup sp (cutStream c (st sp al ts k).S)).sectionPos
      (cutStream c (st sp al ts k).S)
    rw [hsec] at hs
    exact hs.obj (withRoot_obj?_root hraP)
  -- The root's node.
  have hoeN : oe.node = root := by
    obtain ⟨-, o0, ho0, -, hn0⟩ := hm.root
    have h := hraP
    rw [show ((lazyStartup sp (st sp al ts k).S).sectionPos (st sp al ts k).S).root =
      (lazyStartup sp (st sp al ts k).S).root from rfl, Mem.sectionPos_obj?, ho0] at h
    simp only [Option.map_some, Option.some.injEq] at h
    rw [← h]
    exact (sectionPosObj_fields (st sp al ts k).S _ o0).1.trans hn0
  unfold handleStartupPosFrom handleStartup
  rw [hsec, hD, Mem.toH_withRoot hraP hrr.pos]
  generalize hM1 : (lazyStartup sp (st sp al ts k).S).sectionPos (st sp al ts k).S = M1 at *
  have hheld : M1.heldA M1.root = true := by
    unfold Mem.heldA
    have hrt' : M1.tableOf root = some M1.root := by rw [← hM1]; exact hrt
    exact List.any_eq_true.mpr ⟨(_, M1.root), mem_of_lookup _ _ _ hrt', by simp⟩
  have hraH : M1.toH.obj? M1.toH.root = some (M1.objH oe) := by
    show M1.toH.obj? M1.root = _
    rw [Mem.toH_obj?, hheld, hraP]
    rfl
  have hcan : (M1.objH oc).canonical = (M1.objH oe).canonical := hrr.canonical
  have hcanW : ∀ y, (M1.toH.withRoot (M1.objH oc)).canonicalOf y = M1.toH.canonicalOf y :=
    HMem.withRoot_canonicalOf hraH hcan
  have hpoeH : (M1.toH.obj? M1.toH.root).isSome := by rw [hraH]; rfl
  have hroot0 : (M1.root, M1.objH oe) ∈ M1.toH.objs := mem_of_lookup _ _ _ hraH
  have hTD : (startup sp (st sp al ts k).S).D = (st sp al ts k).D := (T1_strong sp al ts hok hst hk).2
  -- The pointers of the cut startup's root object are the whole stream's.
  have hptrC : ∀ q ∈ (M1.objH oc).ptrs, q ∈ (M1.objH oe).ptrs := by
    intro q hq
    unfold Mem.objH at hq ⊢
    obtain ⟨sq, hsq, rfl⟩ := List.mem_map.mp hq
    apply List.mem_map.mpr
    refine ⟨sq, ?_, rfl⟩
    obtain ⟨y, sl⟩ := sq
    have hl : oc.slot? y = some sl := lookup_of_mem oc.slots hndC (y, sl) hsq
    cases hv : sp.virt with
    | false => rw [← hrr.nv hv]; exact hsq
    | true =>
      have hy : y ∈ pointees sp oc.hist := by
        by_cases hy : y ∈ pointees sp oc.hist
        · exact hy
        · rw [hrr.noSlot hv y hy] at hl; cases hl
      rw [hrr.slots y hy] at hl
      exact mem_of_lookup oe.slots y sl hl
  have hsC : (M1.toH.withRoot (M1.objH oc)).s = lastSp (st sp al ts k).S := by
    show M1.s = _
    rw [← hM1]; exact hs0
  rw [HMem.linkDPosFrom_eq_linkDPos, HMem.linkDPos_eq_linkD]
  · -- the pointers that rule 4 by position finds
    intro p hp hpin hkl q hq hh r hr b hb
    rw [hcanW] at hb
    rw [hsC, inPosToId_cut sp hcs]
    have hposb : ((M1.toH.withRoot (M1.objH oc)).obj? b).bind (fun o => o.pos) =
        (M1.toH.obj? b).bind (fun o => o.pos) := by
      by_cases hbr : b = M1.toH.root
      · subst hbr
        rw [HMem.withRoot_obj?_root hraH, hraH]
        simp only [Option.bind_some]
        exact hrr.pos
      · rw [HMem.withRoot_obj?_ne hbr]
    rw [hposb]
    have hs1 : M1.toH.s = lastSp (st sp al ts k).S := hsC
    rcases HMem.mem_withRoot_objs hp with ⟨hne, hp0⟩ | ⟨heq, hpo⟩
    · have h := hcond p hp0 hpin hkl q hq hh r hr b hb
      rw [hs1] at h
      exact h
    · obtain ⟨a, o⟩ := p
      simp only at heq hpo hpin hkl hq
      subst heq; subst hpo
      have hpin' : ((M1.root, M1.objH oe).2.canonical && (inD (startup sp (st sp al ts k).S).D
          (M1.root, M1.objH oe).2.node || (M1.root, M1.objH oe).1 == M1.toH.root)) = true := by
        have hc : (M1.objH oe).canonical = true := by
          rw [← hcan]; simp only [Bool.and_eq_true] at hpin; exact hpin.1
        have hr' : ((M1.root, M1.objH oe).1 == M1.toH.root) = true := by
          show (M1.root == M1.root) = true
          simp
        simp only [hc, hr', Bool.or_true, Bool.and_self]
      have h := hcond (M1.root, M1.objH oe) hroot0 hpin' (by
          show isKeyLevel sp oe.isData oe.level = true
          rw [← hrr.isData, ← hrr.level]; exact hkl) q (hptrC q hq) hh r hr b hb
      rw [hs1] at h
      exact h
  · -- the pointers that Java skips
    intro p hp hc hpD q hq hh r hr hrf
    rw [hcanW]
    rcases HMem.mem_withRoot_objs hp with ⟨-, hp0⟩ | ⟨-, hpo⟩
    · exact hskip p hp0 hc hpD q hq hh r hr hrf
    · obtain ⟨a, o⟩ := p
      simp only at hpo hc hpD hq
      subst hpo
      cases hv : sp.virt with
      | false =>
        rw [hrr.nv hv] at hq hpD hc
        exact hskip _ hroot0 hc hpD q hq hh r hr hrf
      | true =>
        exfalso
        have hn : (M1.objH oc).node = root := by
          show oc.node = root
          rw [hrr.node]; exact hoeN
        rw [hn, hTD, (hinv.vr hv).rootND] at hpD
        cases hpD

/-- Rule 4 by position (the model's, `handleStartupPos`, without Java's skip below
the stream's first position) after a safe cut is rule 4 by node id. -/
theorem rule4PosCut_zero (hok : RunOK sp al ts) (hph : PhysRunOK sp al ts) (hev : EvictRunOK sp al ts)
    (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) (hex : ExecRootOK sp) (hvl : VirtLiveOK sp)
    {k c : Nat} (hk : k ≤ ts.length) (hcut : CutOK sp c (st sp al ts k) k) :
    handleStartupPos sp (cutStream c (st sp al ts k).S) = handleStartup sp (cutStream c (st sp al ts k).S) := by
  rw [← handleStartupPosFrom_zero]
  exact handleStartupPosFrom_cut hok hph hev hj hmk hex hvl hk hcut
    (fun _ _ _ _ _ _ _ _ _ h => absurd h (Nat.not_lt_zero _))

/-- `Rule4PosCut_handles`: rule 4 by position after a safe cut, with Java's skip
below the stream's first position, links what rule 4 by node id links. -/
theorem rule4PosCut_handles (sp : Spec V T) (al : Algo V T) : Rule4PosCut_handles sp al := by
  intro ts hok hph hev hj hmk hex hvl k hk c first hcut hfc
  rw [show run sp al (ts.take k) = st sp al ts k from rfl] at hcut ⊢
  have hskip := cutSkip_none hok hph hev hj hmk hk hcut
  exact handleStartupPosFrom_cut hok hph hev hj hmk hex hvl hk hcut
    (fun p hp hc hpD q hq hh r hr hrf => hskip p hp hc hpD q hq hh r hr (by omega))

end CutStart

/-! ## Runs with cuts and rule 4 by position -/

section Run

variable {sp : Spec V T} {al : Algo V T}

theorem runHandlesCutPos_succ (cs : List (T × Option Nat × List HCacheOp)) {j : Nat} (hj : j < cs.length) :
    runHandlesCutPos sp al (cs.take (j + 1)) =
      (match cs[j].2.1 with
       | some c =>
         (startup sp (cutStream c (handleTrans sp al (runHandlesCutPos sp al (cs.take j)).2.2
            (runHandlesCutPos sp al (cs.take j)).1 (runHandlesCutPos sp al (cs.take j)).2.1 cs[j].1).1.S),
          handleStartupPosFrom sp c (cutStream c (handleTrans sp al (runHandlesCutPos sp al (cs.take j)).2.2
            (runHandlesCutPos sp al (cs.take j)).1 (runHandlesCutPos sp al (cs.take j)).2.1 cs[j].1).1.S),
          cutStream c (handleTrans sp al (runHandlesCutPos sp al (cs.take j)).2.2
            (runHandlesCutPos sp al (cs.take j)).1 (runHandlesCutPos sp al (cs.take j)).2.1 cs[j].1).1.S)
       | none =>
         ((handleTrans sp al (runHandlesCutPos sp al (cs.take j)).2.2 (runHandlesCutPos sp al (cs.take j)).1
            (runHandlesCutPos sp al (cs.take j)).2.1 cs[j].1).1,
          cs[j].2.2.foldl (HMem.cacheOp sp (runHandlesCutPos sp al (cs.take j)).2.2
            (handleTrans sp al (runHandlesCutPos sp al (cs.take j)).2.2 (runHandlesCutPos sp al (cs.take j)).1
              (runHandlesCutPos sp al (cs.take j)).2.1 cs[j].1).1.S
            (handleTrans sp al (runHandlesCutPos sp al (cs.take j)).2.2 (runHandlesCutPos sp al (cs.take j)).1
              (runHandlesCutPos sp al (cs.take j)).2.1 cs[j].1).1.D)
            (handleTrans sp al (runHandlesCutPos sp al (cs.take j)).2.2 (runHandlesCutPos sp al (cs.take j)).1
              (runHandlesCutPos sp al (cs.take j)).2.1 cs[j].1).2,
          (runHandlesCutPos sp al (cs.take j)).2.2)) := by
  have h1 : cs.take (j + 1) = cs.take j ++ [cs[j]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj]; rfl
  unfold runHandlesCutPos
  rw [h1, List.foldl_append]
  rfl

/-- `RunPosCut_handles`: every startup of a run with cuts is from the run's stream
cut at the largest cut so far, where the cut is safe (T12's `RunSimH`), and there
rule 4 by position with the restart's cut as the first position is rule 4 by node
id. -/
theorem runPosCut_handles (sp : Spec V T) (al : Algo V T) : RunPosCut_handles sp al := by
  intro cs hok hph hev hj hmk hex hvl hpol hcut hreads
  have hcut' : ∀ j (h : j < cs.length) c, cs[j].2.1 = some c →
      CutOK sp (cutMax ((cs.take (j + 1)).map (·.2.1))) (st sp al (cs.map (·.1)) (j + 1)) (j + 1) := hcut
  have hsim : ∀ j ≤ cs.length, RunSimH sp al cs j := by
    intro j
    induction j with
    | zero => intro _; exact runSimH_zero cs hok hph hev hj hmk hex hvl
    | succ j ih =>
      intro hj'
      exact runSimH_step cs hok hph hev hj hmk hex hvl hpol hcut' hreads (by omega) (ih (by omega))
  intro j
  induction j with
  | zero =>
    intro _
    have h0 := rule4PosCut_handles sp al (cs.map (·.1)) hok hph hev hj hmk hex hvl 0 (Nat.zero_le _) 0 0
      (CutOK.zero sp _ 0) (Nat.le_refl 0)
    simp only [List.take_zero] at h0
    rw [show run sp al [] = init sp from rfl, cutStream_zero] at h0
    simp only [List.take_zero, runHandlesCutPos, runHandlesCut, List.foldl_nil]
    rw [h0]
  | succ j ih =>
    intro hjc
    have hjl : j < cs.length := by omega
    rw [runHandlesCutPos_succ cs hjl, runHandlesCut_succ cs hjl, ih (by omega)]
    cases hc : cs[j].2.1 with
    | none => rfl
    | some c =>
      simp only
      -- The restart's stream: the run's cut at the largest cut so far.
      have hS := (hsim (j + 1) hjc).sC
      rw [runHandlesCut_succ cs hjl] at hS
      simp only [hc] at hS
      rw [lastR_succ_some cs hjl hc] at hS
      have hcm : c ≤ cutMax ((cs.take (j + 1)).map (·.2.1)) := by
        rw [cutMax_take_succ cs hjl, hc]
        exact Nat.le_max_right _ _
      have hpos := rule4PosCut_handles sp al (cs.map (·.1)) hok hph hev hj hmk hex hvl (j + 1)
        (by simp; omega) (cutMax ((cs.take (j + 1)).map (·.2.1))) c (hcut j hjl c hc) hcm
      rw [show run sp al ((cs.map (·.1)).take (j + 1)) = st sp al (cs.map (·.1)) (j + 1) from rfl,
        ← hS] at hpos
      rw [hpos]

end Run

end SIS
