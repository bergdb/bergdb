/-
Proofs about the physical layer with handles (bergdb item 009, step 2d), part 5:
the writer's walk. The writer's follow (the readers' follow, then the promote)
of a live pointer of the canonical object of a current node leaves the child's
canonical object, held by the child's live handle, which the pointer holds; and
the writer reaches every node of its paths, highest level first
(`HMem.reachOnPath`), as SIS/Proof/EvictPath.lean shows for Evict.lean.
-/
import SIS.Proof.HandleRead

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## The promote -/

theorem HMem.promote_eq {m : HMem V} {n b : Nat} {ob : HObj V} (hn : m.objOf n = some b)
    (hob : m.obj? b = some ob) : m.promote n = (m.setObj b { ob with canonical := true }, some b) := by
  unfold HMem.promote
  rw [hn]
  simp only [hob]

theorem hobj_canonical_true {o : HObj V} (h : o.canonical = true) : { o with canonical := true } = o := by
  cases o; simp only at h; subst h; rfl

/-- The keys of the objects after one is replaced do not repeat. -/
theorem HMem.setObj_nodup (m : HMem V) (a : Nat) (o : HObj V) (hnd : (m.objs.map (·.1)).Nodup) :
    ((m.setObj a o).objs.map (·.1)).Nodup := by
  unfold HMem.setObj
  simp only [List.map_cons, List.nodup_cons]
  refine ⟨?_, (List.Sublist.map _ List.filter_sublist).nodup hnd⟩
  intro hmem
  obtain ⟨q, hq, hqa⟩ := List.mem_map.mp hmem
  have := (List.mem_filter.mp hq).2
  rw [hqa] at this
  simp at this

section Promote

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : HMem V}

/-- The writer's promote of a snapshot b at the latest version of a written node y
not in D, current at k, held by y's live handle n: object b, now canonical (ob1:
ob with the flag set), is y's canonical object, and the invariant is kept. -/
theorem HEInv.promote_snap (hinv : Inv sp db k) (hev : EvLogic sp db k) (hls : LiveSub sp)
    (hm : HEInv sp db S0 k m) {n b : Nat} {y : NodeId} {ob ob1 : HObj V}
    (hn : m.objOf n = some b) (ht : m.tableOf y = some n) (hob : m.obj? b = some ob)
    (hco : ob.canonical = false) (hoy : ob.node = y) (hyD : inD db.D y = false)
    (hyw : written sp y = true) (hpos : ob.pos = (db.S.lv y).map (·.recNo))
    (hr : reachable sp db.P k y = true)
    (hc1 : ob1.canonical = true) (hn1 : ob1.node = ob.node) (hh1 : ob1.hist = ob.hist)
    (hl1 : ob1.level = ob.level) (hd1 : ob1.isData = ob.isData) (hp1 : ob1.pos = ob.pos)
    (hptr1 : ob1.ptrs = ob.ptrs) :
    HEInv sp db S0 k (m.setObj b ob1) := by
  have hptr : ∀ z, ob1.ptr? z = ob.ptr? z := by intro z; unfold HObj.ptr?; rw [hptr1]
  have hobj : ∀ x, (m.setObj b ob1).obj? x = if x = b then some ob1 else m.obj? x :=
    fun x => HMem.obj?_setObj m b x ob1
  have hlt : b < m.nextObj := Nat.lt_of_not_le (fun h => by rw [hm.freshO b h] at hob; cases hob)
  have hback : ∀ x ox, (m.setObj b ob1).obj? x = some ox →
      (x = b ∧ ox = ob1) ∨ (x ≠ b ∧ m.obj? x = some ox) := by
    intro x ox hx
    rw [hobj] at hx
    split at hx
    · rename_i h; simp only [Option.some.injEq] at hx; exact Or.inl ⟨h, hx.symm⟩
    · rename_i h; exact Or.inr ⟨h, hx⟩
  -- A handle that holds b is a handle of y.
  have hheld : ∀ n' hd, m.handle? n' = some hd → hd.obj = some b → hd.node = y := by
    intro n' hd hh hb
    obtain ⟨-, ob', hob', hon'⟩ := hm.tbl.obj_of_handle hh hb
    rw [hob, Option.some.injEq] at hob'
    subst hob'
    rw [← hon', hoy]
  -- The canonical objects: b is y's, the others as before.
  have hcan : ∀ z, (m.setObj b ob1).canonicalOf z = if z = y then some b else m.canonicalOf z := by
    intro z
    unfold HMem.canonicalOf
    rw [HMem.tableOf_setObj, HMem.objOf_setObj_fun]
    by_cases hz : z = y
    · subst hz
      simp only [ht, Option.bind_some, hn, hobj, ↓reduceIte, hc1]
    · simp only [hz, ↓reduceIte]
      cases htz : m.tableOf z with
      | none => rfl
      | some nz =>
        simp only [Option.bind_some]
        cases hbz : m.objOf nz with
        | none => rfl
        | some c =>
          simp only
          have hcb : c ≠ b := by
            intro hcb
            subst hcb
            obtain ⟨hd', c', o', hh', -, hny', hc', -, -⟩ := hm.tbl.entry htz
            have hcc : hd'.obj = some c := by
              have h0 := hbz; unfold HMem.objOf at h0; rw [hh'] at h0; exact h0
            exact hz (hny'.symm.trans (hheld nz hd' hh' hcc))
          rw [hobj]
          simp only [hcb, ↓reduceIte]
  -- The record rule: as before, but for a pointer whose handle holds b, a pointer
  -- for y, which now gives b's position, y's latest version.
  have hpr : ∀ z p, (∀ n' hd, p.handle = some n' → m.handle? n' = some hd → hd.node = z) →
      (m.setObj b ob1).ptrRef S0 z p = m.ptrRef S0 z p ∨
        (z = y ∧ (m.setObj b ob1).ptrRef S0 z p = (db.S.lv y).map (·.recNo)) := by
    intro z p hpz
    unfold HMem.ptrRef
    rw [HMem.handle?_setObj_fun, HMem.setObj_s]
    cases hph : p.handle.bind m.handle? with
    | none => left; rfl
    | some hd =>
      simp only
      cases hb : hd.obj with
      | none => left; rfl
      | some c =>
        simp only [Option.bind_some]
        rw [hobj]
        by_cases hcb : c = b
        · subst hcb
          right
          have hzy : z = y := by
            cases hpn : p.handle with
            | none => rw [hpn] at hph; cases hph
            | some n' =>
              rw [hpn] at hph
              simp only [Option.bind_some] at hph
              rw [← hpz n' hd hpn hph]; exact hheld n' hd hph hb
          refine ⟨hzy, ?_⟩
          simp only [↓reduceIte, hc1, hp1, hpos]
        · left
          simp only [hcb, ↓reduceIte]
  have hpz_of : ∀ x ox z p, m.obj? x = some ox → ox.ptr? z = some p →
      ∀ n' hd, p.handle = some n' → m.handle? n' = some hd → hd.node = z := by
    intro x ox z p hx hp n' hd h3 h4
    obtain ⟨hd', h5, h6⟩ := hm.tbl.ptrNode hx hp h3
    rw [h4, Option.some.injEq] at h5; subst h5; exact h6
  have hhl : ∀ z p, m.HoldsLive z p → (m.setObj b ob1).HoldsLive z p := by
    intro z p ⟨n', h1, h2, h3⟩
    refine ⟨n', h1, by rw [HMem.tableOf_setObj]; exact h2, ?_⟩
    rw [hcan]
    split
    · rfl
    · exact h3
  have hslotc : ∀ x ox z p, m.obj? x = some ox → ox.ptr? z = some p → HSlotInv S0 db m ox z p →
      HSlotInv S0 db (m.setObj b ob1) ox z p := by
    intro x ox z p hx hp h
    obtain ⟨h1, h2⟩ := h
    refine ⟨fun hD => ?_, fun hD => ?_⟩
    · rcases hpr z p (hpz_of x ox z p hx hp) with h | ⟨hzy, h⟩
      · rw [h]; exact h1 hD
      · rw [h, hzy]
    · rcases h2 hD with h | h
      · exact Or.inl (hhl z p h)
      · exact Or.inr h
  have hlivec : ∀ x ox z p, m.obj? x = some ox → ox.ptr? z = some p → HLiveInv S0 db m z p →
      HLiveInv S0 db (m.setObj b ob1) z p := by
    intro x ox z p hx hp h
    obtain ⟨h1, h2⟩ := h
    refine ⟨fun hD => hhl z p (h1 hD), fun hD => ?_⟩
    rcases hpr z p (hpz_of x ox z p hx hp) with h | ⟨hzy, h⟩
    · rw [h]; exact h2 hD
    · rw [h, hzy]
  -- The new canonical object: y's whole history, and its pointers' records.
  obtain ⟨nn, hnn⟩ := Option.isSome_iff_exists.mp (Reach.isSome ((reachable_iff _ _ _ _).mp hr))
  obtain ⟨v, hv, hvh, hvl, hvd⟩ := hinv.lv_whole hnn hyw hyD hr
  obtain ⟨r1, w1, e1, e2, e3, e4, e5, -, -⟩ := hm.snap b ob hob hco
  have hw1 : w1 = v := by
    rw [hpos, hv] at e1
    simp only [Option.map_some, Option.some.injEq] at e1
    rw [← e1, hoy, hinv.lv_at hv, Option.some.injEq] at e2
    exact e2.symm
  subst hw1
  have hnewptr : ∀ z ∈ pointees sp ob.hist, ∃ p, ob.ptr? z = some p ∧ inD db.D z = false ∧
      (m.setObj b ob1).ptrRef S0 z p = (db.S.lv z).map (·.recNo) := by
    intro z hz
    obtain ⟨p, hp, hzD, href⟩ := hm.snap_ptr hinv hev hob hco hoy hyD hyw hpos hr hz
    refine ⟨p, hp, hzD, ?_⟩
    rcases hpr z p (hpz_of b ob z p hob hp) with h | ⟨hzy, h⟩
    · rw [h]; exact href
    · rw [h, hzy]
  refine
    { len := hm.len
      pre := hm.pre
      sEq := by rw [HMem.setObj_s]; exact hm.sEq
      freshO := ?_
      freshH := fun n hn => hm.freshH n hn
      objNodup := HMem.setObj_nodup m b ob1 hm.objNodup
      hNodup := hm.hNodup
      root := ?_
      tbl := ?_
      liveW := hm.liveW
      cc := ?_
      pos := ?_
      dCanon := ?_
      snap := ?_
      ruleR := ?_
      wver := hm.wver
      rver := ?_
      slots := ?_
      live := ?_ }
  · intro x hx
    rw [HMem.setObj_nextObj] at hx
    rw [hobj]
    have : x ≠ b := by omega
    simp only [this, ↓reduceIte]
    exact hm.freshO x hx
  · obtain ⟨or, hor, hc', hn'⟩ := hm.root
    rw [HMem.setObj_root, hobj]
    have hrb : m.root ≠ b := by
      intro h; rw [h, hob, Option.some.injEq] at hor; subst hor; rw [hco] at hc'; cases hc'
    simp only [hrb, ↓reduceIte]
    exact ⟨or, hor, hc', hn'⟩
  · refine ⟨?_, hm.tbl.nodup, fun n hd hh hl => hm.tbl.liveIn hh hl,
      fun n hd hh hdd => hm.tbl.deadNone hh hdd, ?_, ?_⟩
    · intro z n' hz
      rw [HMem.tableOf_setObj] at hz
      obtain ⟨hd, c, oc, hh, hl, hny, hc, hoc, hon⟩ := hm.tbl.entry hz
      by_cases hcb : c = b
      · subst hcb
        rw [hob, Option.some.injEq] at hoc
        subst hoc
        exact ⟨hd, c, ob1, hh, hl, hny, hc, by rw [hobj]; simp, by rw [hn1]; exact hon⟩
      · exact ⟨hd, c, oc, hh, hl, hny, hc, by rw [hobj]; simp [hcb]; exact hoc, hon⟩
    · intro x ox hx
      rcases hback x ox hx with ⟨hxb, hox⟩ | ⟨-, hx'⟩
      · subst hox
        obtain ⟨n', ht', hob'⟩ := hm.tbl.held hob
        exact ⟨n', by rw [HMem.tableOf_setObj, hn1]; exact ht', by rw [hxb]; exact hob'⟩
      · exact hm.tbl.held hx'
    · intro x ox z q n' hx hq hn'
      rcases hback x ox hx with ⟨hxb, hox⟩ | ⟨-, hx'⟩
      · subst hox
        rw [hptr] at hq
        exact hm.tbl.ptrNode hob hq hn'
      · exact hm.tbl.ptrNode hx' hq hn'
  · intro x ox hx hcx
    rcases hback x ox hx with ⟨-, hox⟩ | ⟨-, hx'⟩
    · subst hox
      exact ⟨nn, by rw [hn1, hoy]; exact hnn, by rw [hh1, e3, hvh], by rw [hl1, e4, hvl],
        by rw [hd1, e5, hvd]⟩
    · exact hm.cc x ox hx' hcx
  · intro x ox hx hcx
    rcases hback x ox hx with ⟨-, hox⟩ | ⟨-, hx'⟩
    · subst hox; rw [hp1, hn1, hoy]; exact hpos
    · exact hm.pos x ox hx' hcx
  · intro z hz
    rw [hcan]
    have hzy : z ≠ y := by intro h; rw [h, hyD] at hz; cases hz
    simp only [hzy, ↓reduceIte]
    exact hm.dCanon z hz
  · intro x ox hx hcx
    rcases hback x ox hx with ⟨-, hox⟩ | ⟨-, hx'⟩
    · subst hox; rw [hc1] at hcx; cases hcx
    · exact (hm.snap x ox hx' hcx).of_s (HMem.setObj_s _ _ _)
  · intro n' hd c oc w hh hc hoc hcc hw
    rw [HMem.setObj_s] at hw
    rw [hobj] at hoc
    split at hoc
    · simp only [Option.some.injEq] at hoc; subst hoc; rw [hc1] at hcc; cases hcc
    · exact hm.ruleR n' hd c oc w hh hc hoc hcc hw
  · intro x ox z q r hx hq hr'
    rcases hback x ox hx with ⟨-, hox⟩ | ⟨-, hx'⟩
    · subst hox; rw [hptr] at hq; exact hm.rver b ob z q r hob hq hr'
    · exact hm.rver x ox z q r hx' hq hr'
  · intro x ox hx hrelx z hz
    rcases hback x ox hx with ⟨-, hox⟩ | ⟨-, hx'⟩
    · subst hox
      obtain ⟨p, hp, hzD, href⟩ := hnewptr z (by rw [← hh1]; exact hz)
      refine ⟨p, by rw [hptr]; exact hp, fun _ => href, fun hD => ?_⟩
      rw [hzD] at hD; cases hD
    · obtain ⟨q, hq, hi⟩ := hm.slots x ox hx' hrelx z hz
      exact ⟨q, hq, hslotc x ox z q hx' hq hi⟩
  · intro x ox hx hcx hrx z hz
    rcases hback x ox hx with ⟨-, hox⟩ | ⟨-, hx'⟩
    · subst hox
      obtain ⟨p, hp, hzD, href⟩ := hnewptr z (mem_pointees_of_liveH hls (by rw [← hh1]; exact hz))
      refine ⟨p, by rw [hptr]; exact hp, fun hD => ?_, fun _ => href⟩
      rw [hzD] at hD; cases hD
    · obtain ⟨q, hq, hi⟩ := hm.live x ox hx' hcx hrx z hz
      exact ⟨q, hq, hlivec x ox z q hx' hq hi⟩

/-- The writer's promote on y's live handle n, which holds a readable object b of
y, current at k: b becomes (or stays) y's canonical object, and the invariant is
kept. -/
theorem HEInv.promote_ok (hinv : Inv sp db k) (hev : EvLogic sp db k) (hls : LiveSub sp)
    (hm : HEInv sp db S0 k m) {n b : Nat} {y : NodeId} (hn : m.objOf n = some b)
    (ht : m.tableOf y = some n) (hrd : HReadable sp db m b y) (hr : reachable sp db.P k y = true) :
    ∃ ob, m.obj? b = some ob ∧ ob.node = y ∧
      m.promote n = (m.setObj b { ob with canonical := true }, some b) ∧
      HEInv sp db S0 k (m.setObj b { ob with canonical := true }) ∧
      (m.setObj b { ob with canonical := true }).canonicalOf y = some b := by
  obtain ⟨ob, hob, hoy, hc⟩ := hrd
  refine ⟨ob, hob, hoy, HMem.promote_eq hn hob, ?_⟩
  cases hco : ob.canonical with
  | true =>
    rw [hobj_canonical_true hco]
    have hsame : ∀ x, (m.setObj b ob).obj? x = m.obj? x := by
      intro x; rw [HMem.obj?_setObj]; split
      · rename_i h; subst h; exact hob.symm
      · rfl
    have hm' := hm.congr hsame (fun _ => rfl) (fun _ => rfl) rfl rfl rfl rfl
      (HMem.setObj_nodup m b ob hm.objNodup) hm.hNodup hm.tbl.nodup
    refine ⟨hm', ?_⟩
    rw [← hoy]; exact hm'.canonicalOf_of (by rw [hsame]; exact hob) hco
  | false =>
    rcases hc with hc | ⟨hyD, hyw, hpos⟩
    · rw [hco] at hc; cases hc
    have hm' := hm.promote_snap (ob1 := { ob with canonical := true }) hinv hev hls hn ht hob hco hoy hyD hyw
      hpos hr rfl rfl rfl rfl rfl rfl rfl
    refine ⟨hm', ?_⟩
    rw [← hoy]; exact hm'.canonicalOf_of (o := { ob with canonical := true }) (HMem.obj?_setObj_self _ _ _) rfl

end Promote

/-! ## The writer's follow -/

/-- What the writer's follow of the pointer of object a for y leaves, from m to
m': the pointer holds y's live handle, which holds y's canonical object; the
canonical objects of m stay where they are, canonical, with their pointers for
the other nodes; the table is as it was for the other nodes. -/
structure HWFollow (m m' : HMem V) (a : Nat) (y : NodeId) : Prop where
  holds : ∃ o' p', m'.obj? a = some o' ∧ o'.ptr? y = some p' ∧ m'.HoldsLive y p'
  canon : ∀ z c, m.canonicalOf z = some c → m'.canonicalOf z = some c
  frame : ∀ c oc, m.obj? c = some oc → oc.canonical = true → ∃ oc', m'.obj? c = some oc' ∧
    oc'.canonical = true ∧ ∀ z, z ≠ y → oc'.ptr? z = oc.ptr? z
  tables : ∀ z, z ≠ y → m'.tableOf z = m.tableOf z

section Writer

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : HMem V}

/-- The writer's follow of a live pointer of the canonical object of a current
node keeps the invariant, and leaves what `HWFollow` says. -/
theorem HEInv.follow_writer (hinv : Inv sp db k) (hls : LiveSub sp) (hev : EvLogic sp db k)
    (hm : HEInv sp db S0 k m) {a : Nat} {op : HObj V} (hop : m.obj? a = some op)
    (hco : op.canonical = true) (hr : reachable sp db.P k op.node = true) {y : NodeId}
    (hy : y ∈ sp.live op.hist) :
    HEInv sp db S0 k (m.follow sp S0 db.S a y true).1 ∧ HWFollow m (m.follow sp S0 db.S a y true).1 a y := by
  -- y: a live child at k, so a current written node below op's.
  obtain ⟨n, hn, hhist, -, -⟩ := hm.cc a op hop hco
  have hy' : y ∈ sp.live (n.hist.upTo k) := by
    rw [upTo_of_forall _ _ (hinv.times _ n hn), ← hhist]; exact hy
  obtain ⟨e, he, hye⟩ := hls _ _ hy'
  obtain ⟨ny, hny, hlt⟩ := hinv.ptrs op.node n hn e (mem_upTo.mp he).1 y hye
  have hyroot : y ≠ SIS.root := hinv.ptr_ne_root hn (mem_upTo.mp he).1 hye
  have hyw : written sp y = true := written_of_ne_root sp hyroot
  have hry : reachable sp db.P k y = true := by
    rw [reachable_iff] at hr ⊢; exact Reach.child hr hn hy' hny hlt
  have hyne : op.node ≠ y := by
    intro he; rw [← he, hn, Option.some.injEq] at hny; subst hny; omega
  obtain ⟨p, hp, hli1, hli2⟩ := hm.live a op hop hco hr y hy
  have hg : HPtrGood S0 db m y p := by
    cases hyD : inD db.D y with
    | true => exact Or.inl ⟨hyD, hli1 hyD⟩
    | false => exact Or.inr ⟨hyD, hli2 hyD⟩
  obtain ⟨m1, n1, b1, hf⟩ := hm.followR_some hinv hop hp hg hyw hry
  have hF := hm.followR_ok hinv hop hf
  have hrd := hF.readable op p hop hp hg hyw
  obtain ⟨ob, hob, hoy, hpe, hm2, hc2⟩ := hF.inv.promote_ok hinv hev hls hF.objOf hF.tableOf hrd hry
  have hfe : m.follow sp S0 db.S a y true = (m1.setObj b1 { ob with canonical := true }, some b1) := by
    unfold HMem.follow; rw [hf]; exact hpe
  rw [hfe]
  refine ⟨hm2, ?_⟩
  have hobj2 : ∀ x, (m1.setObj b1 { ob with canonical := true }).obj? x =
      if x = b1 then some { ob with canonical := true } else m1.obj? x := fun x => HMem.obj?_setObj _ _ _ _
  -- The parent is not y's object.
  obtain ⟨o', p', ho', hc', hp', hn', hothers⟩ := hF.parent op hop hyne
  have hab : a ≠ b1 := by
    intro he
    rw [he, hob, Option.some.injEq] at ho'
    subst ho'
    have e1 : ob.node = op.node := congrArg (fun c => c.1) hc'
    exact hyne (e1.symm.trans hoy)
  -- The canonical objects of m in m1, then after the promote.
  have hkeep : ∀ c oc, m.obj? c = some oc → oc.canonical = true →
      ∃ oc', (m1.setObj b1 { ob with canonical := true }).obj? c = some oc' ∧ oc'.canonical = true ∧
        oc'.node = oc.node ∧ ∀ z, z ≠ y → oc'.ptr? z = oc.ptr? z := by
    intro c oc hoc hcc
    by_cases hca : c = a
    · subst hca
      rw [hop, Option.some.injEq] at hoc
      subst hoc
      refine ⟨o', by rw [hobj2]; simp [hab]; exact ho', ?_, congrArg (fun c => c.1) hc', hothers⟩
      rw [show o'.canonical = op.canonical from congrArg (fun c => c.2.2.2.2.1) hc']; exact hcc
    · have h1 := hF.others c oc hoc hca (Or.inr hcc)
      by_cases hcb : c = b1
      · subst hcb
        rw [hob, Option.some.injEq] at h1
        subst h1
        refine ⟨{ ob with canonical := true }, by rw [hobj2]; simp, rfl, rfl, fun _ _ => rfl⟩
      · exact ⟨oc, by rw [hobj2]; simp [hcb]; exact h1, hcc, rfl, fun _ _ => rfl⟩
  refine ⟨⟨o', p', by rw [hobj2]; simp [hab]; exact ho', hp', n1, hn',
    by rw [HMem.tableOf_setObj]; exact hF.tableOf, by rw [hc2]; rfl⟩, ?_, ?_, ?_⟩
  · intro z c hz
    obtain ⟨oc, hoc, hcc, hon⟩ := hm.obj_of_canonicalOf hz
    obtain ⟨oc', hoc', hcc', hon', -⟩ := hkeep c oc hoc hcc
    rw [← hon, ← hon']
    exact hm2.canonicalOf_of hoc' hcc'
  · intro c oc hoc hcc
    obtain ⟨oc', hoc', hcc', -, hs⟩ := hkeep c oc hoc hcc
    exact ⟨oc', hoc', hcc', hs⟩
  · intro z hz
    rw [HMem.tableOf_setObj, hF.tables z hz]

end Writer

/-! ## The writer's paths -/

section Path

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : HMem V}

/-- Node a of the path is reached in m: it has a canonical object, and (but the
root) the canonical object of a node of the path that has a as a live child at
k has a pointer for a that holds a's live handle, which holds that canonical
object. -/
def HPathDone (sp : Spec V T) (P : Struct V) (k : Nat) (path : List NodeId) (m : HMem V) (a : NodeId) :
    Prop :=
  (m.canonicalOf a).isSome ∧
    (a ≠ root → ∃ p ∈ path, ∃ np bp op ptr, P.get? p = some np ∧ a ∈ sp.live (np.hist.upTo k) ∧
      m.canonicalOf p = some bp ∧ m.obj? bp = some op ∧ op.ptr? a = some ptr ∧ m.HoldsLive a ptr)

/-- The writer reaches one node x of a path. -/
theorem HEInv.reachOnPath_ok (hinv : Inv sp db k) (hls : LiveSub sp) (hev : EvLogic sp db k)
    (hm : HEInv sp db S0 k m) {path : List NodeId} (hpath : ∀ p ∈ path, reachable sp db.P k p = true)
    (x : NodeId) :
    HEInv sp db S0 k (m.reachOnPath sp S0 db.S db.P (k + 1) path x) ∧
      (∀ z c, m.canonicalOf z = some c →
        (m.reachOnPath sp S0 db.S db.P (k + 1) path x).canonicalOf z = some c) ∧
      (∀ c oc, m.obj? c = some oc → oc.canonical = true →
        ∃ oc', (m.reachOnPath sp S0 db.S db.P (k + 1) path x).obj? c = some oc' ∧
          ∀ z, z ≠ x → oc'.ptr? z = oc.ptr? z) ∧
      (∀ z, z ≠ x → (m.reachOnPath sp S0 db.S db.P (k + 1) path x).tableOf z = m.tableOf z) ∧
      ((∃ p ∈ path, ∃ np, db.P.get? p = some np ∧ m.canonicalOf p ≠ none ∧
          x ∈ sp.live (np.hist.upTo k)) →
        ∃ p ∈ path, ∃ np bp op ptr, db.P.get? p = some np ∧ x ∈ sp.live (np.hist.upTo k) ∧
          (m.reachOnPath sp S0 db.S db.P (k + 1) path x).canonicalOf p = some bp ∧
          (m.reachOnPath sp S0 db.S db.P (k + 1) path x).obj? bp = some op ∧
          op.ptr? x = some ptr ∧ (m.reachOnPath sp S0 db.S db.P (k + 1) path x).HoldsLive x ptr) := by
  unfold HMem.reachOnPath
  have hK1 : k + 1 - 1 = k := by omega
  cases hf : path.find? (fun p => match db.P.get? p, m.canonicalOf p with
      | some n, some _ => (sp.live (n.hist.upTo (k + 1 - 1))).contains x
      | _, _ => false) with
  | none =>
    simp only
    refine ⟨hm, fun _ _ h => h, fun c oc ho _ => ⟨oc, ho, fun _ _ => rfl⟩, fun _ _ => by trivial, ?_⟩
    rintro ⟨p, hp, np, hnp, hcp, hxl⟩
    exfalso
    rw [List.find?_eq_none] at hf
    apply hf p hp
    rw [hnp]
    cases hc : m.canonicalOf p with
    | none => exact absurd hc hcp
    | some _ => simp only [hK1]; exact List.contains_iff_mem.mpr hxl
  | some p =>
    simp only
    have hpp := List.find?_some hf
    have hpm := List.mem_of_find?_eq_some hf
    cases hnp : db.P.get? p with
    | none => rw [hnp] at hpp; simp at hpp
    | some np =>
      cases hcp : m.canonicalOf p with
      | none => rw [hnp, hcp] at hpp; simp at hpp
      | some bp =>
        simp only
        rw [hnp, hcp] at hpp
        simp only [hK1, List.contains_iff_mem] at hpp
        obtain ⟨op, hop, hco, hnode⟩ := hm.obj_of_canonicalOf hcp
        obtain ⟨nf, hnf, hh, -, -⟩ := hm.cc bp op hop hco
        rw [hnode, hnp, Option.some.injEq] at hnf
        subst hnf
        have hxop : x ∈ sp.live op.hist := by
          rw [hh, ← upTo_of_forall _ _ (hinv.times p np hnp)]; exact hpp
        obtain ⟨hm', hwf⟩ := hm.follow_writer hinv hls hev hop hco (by rw [hnode]; exact hpath p hpm) hxop
        refine ⟨hm', hwf.canon, fun c oc ho hc => ?_, hwf.tables, fun _ => ?_⟩
        · obtain ⟨oc', ho', -, hs⟩ := hwf.frame c oc ho hc
          exact ⟨oc', ho', hs⟩
        · obtain ⟨op', ptr, hop', hptr, hhl⟩ := hwf.holds
          exact ⟨p, hpm, np, bp, op', ptr, hnp, hpp, hwf.canon p bp hcp, hop', hptr, hhl⟩

/-- The writer reaches every node of the paths, highest level first. -/
theorem HEInv.reachPath_ok (hinv : Inv sp db k) (hls : LiveSub sp) (hev : EvLogic sp db k)
    {path : List NodeId} (hpath : ∀ p ∈ path, reachable sp db.P k p = true)
    (hparent : ∀ x ∈ path, x ≠ SIS.root → ∃ p ∈ path, ∃ np nx, db.P.get? p = some np ∧
      db.P.get? x = some nx ∧ nx.level < np.level ∧ x ∈ sp.live (np.hist.upTo k)) :
    ∀ (L A : List NodeId) (m : HMem V), HEInv sp db S0 k m → (∀ a ∈ A, HPathDone sp db.P k path m a) →
      (∀ x, x ∈ A ++ L ↔ x ∈ path) → (A ++ L).Nodup →
      (A ++ L).Pairwise (fun a b => lev db.P b ≤ lev db.P a) →
      HEInv sp db S0 k (L.foldl (HMem.reachOnPath sp S0 db.S db.P (k + 1) path) m) ∧
        ∀ x ∈ path, HPathDone sp db.P k path (L.foldl (HMem.reachOnPath sp S0 db.S db.P (k + 1) path) m) x := by
  intro L
  induction L with
  | nil =>
    intro A m hm hA hmem _ _
    refine ⟨hm, fun x hx => hA x ?_⟩
    have := (hmem x).mpr hx
    simpa using this
  | cons x L ih =>
    intro A m hm hA hmem hnd hsort
    simp only [List.foldl_cons]
    obtain ⟨hm1, hmono, hframe, htab, hc1⟩ := hm.reachOnPath_ok hinv hls hev hpath x
    -- x is reached now.
    have hx1 : HPathDone sp db.P k path (m.reachOnPath sp S0 db.S db.P (k + 1) path x) x := by
      by_cases hxr : x = SIS.root
      · subst hxr
        obtain ⟨o, ho, hco, hn⟩ := hm1.root
        refine ⟨?_, fun h => absurd rfl h⟩
        have := hm1.canonicalOf_of ho hco
        rw [hn] at this
        rw [this]; rfl
      · obtain ⟨p, hp, np, nx, hnp, hnx, hlt, hxl⟩ := hparent x ((hmem x).mp (by simp)) hxr
        -- p is before x in the sorted list: in A, so reached
        have hpA : p ∈ A := by
          have hpAL := (hmem p).mpr hp
          rcases List.mem_append.mp hpAL with h | h
          · exact h
          · exfalso
            rcases List.mem_cons.mp h with h | h
            · subst h; rw [hnp, Option.some.injEq] at hnx; subst hnx; omega
            · have hs := List.pairwise_append.mp hsort
              have := List.pairwise_cons.mp hs.2.1
              have := this.1 p h
              simp [lev, hnp, hnx] at this
              omega
        obtain ⟨hpc, -⟩ := hA p hpA
        have hpc' : m.canonicalOf p ≠ none := by
          intro h; rw [h] at hpc; cases hpc
        obtain ⟨q, hq, nq, bq, oq, ptr, hnq, hxq, hcq, hoq, hptr, hhl⟩ :=
          hc1 ⟨p, hp, np, hnp, hpc', hxl⟩
        obtain ⟨n0, h1, h2, hc0⟩ := hhl
        exact ⟨hc0, fun _ => ⟨q, hq, nq, bq, oq, ptr, hnq, hxq, hcq, hoq, hptr, n0, h1, h2, hc0⟩⟩
    -- The nodes reached before stay reached.
    have hA1 : ∀ a ∈ A ++ [x], HPathDone sp db.P k path (m.reachOnPath sp S0 db.S db.P (k + 1) path x) a := by
      intro a ha
      rcases List.mem_append.mp ha with haA | haA
      · have hax : a ≠ x := by
          intro he; subst he
          have := List.nodup_append.mp hnd
          exact this.2.2 a haA a (by simp) rfl
        obtain ⟨hac, hap⟩ := hA a haA
        unfold HPathDone
        refine ⟨?_, fun hr => ?_⟩
        · obtain ⟨c0, hc0⟩ := Option.isSome_iff_exists.mp hac
          rw [hmono a c0 hc0]; rfl
        · obtain ⟨p, hp, np, bp, op, ptr, hnp, hal, hcp, hop, hptr, n0, hn0, ht0, hca⟩ := hap hr
          obtain ⟨op0, hop0, hco0, -⟩ := hm.obj_of_canonicalOf hcp
          rw [hop, Option.some.injEq] at hop0
          subst hop0
          obtain ⟨op', hop', hs⟩ := hframe bp op hop hco0
          refine ⟨p, hp, np, bp, op', ptr, hnp, hal, hmono p bp hcp, hop', by rw [hs a hax]; exact hptr,
            n0, hn0, by rw [htab a hax]; exact ht0, ?_⟩
          obtain ⟨c0, hc0⟩ := Option.isSome_iff_exists.mp hca
          rw [hmono a c0 hc0]; rfl
      · rw [List.mem_singleton] at haA; subst haA; exact hx1
    exact ih (A ++ [x]) _ hm1 hA1 (by intro y; rw [← hmem y]; simp) (by simpa using hnd)
      (by simpa using hsort)

end Path

end SIS
