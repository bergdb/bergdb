/-
Proofs about reclaim with handles (bergdb 005-62), part 2 of T9 over handles:
one transaction of the physical writer with handles keeps T9's invariant
(`CInvH`). The writer's promote makes canonical a snapshot of a clean node's
latest version, whose pointers are at least as new as that version's
references; the change gives a new pointer its pointee's live handle with its
canonical object, or a copy of a pointer whose record is its pointee's latest
version; the writes leave a taken node's pointers holding canonical objects or
with the record rule's reference, its new version's; with a virtual root, the
root's object holds the live handles of the root children on the writer's paths
and of the new ones.
-/
import SIS.Proof.HandleCut
import SIS.Proof.CutPhysTrans

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## The writer's walk -/

section Walk

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : HMem V}

/-- The writer's promote of a readable object keeps T9's invariant: a snapshot
promoted is of the latest version of a clean node, and its pointers are at least
as new as that version's references after Rule R. -/
theorem CInvH.promote (hinv : Inv sp db k) (hm : HEInv sp db S0 k m) (hc : CInvH sp db S0 m)
    {b : Nat} {ob : HObj V} (hob : m.obj? b = some ob) {y : NodeId}
    (hrd : HReadable sp db m b y) : CInvH sp db S0 (m.setObj b { ob with canonical := true }) := by
  have hk := HMem.keepPtrs_promote m b ob
  -- Every object of the new memory is one of m with the same node, history and
  -- pointers; only b may have become canonical.
  have hback : ∀ x o', (m.setObj b { ob with canonical := true }).obj? x = some o' →
      ∃ o, m.obj? x = some o ∧ o'.node = o.node ∧ o'.hist = o.hist ∧ o'.ptrs = o.ptrs ∧
        (x ≠ b → o' = o) := by
    intro x o' hx
    rw [HMem.obj?_setObj] at hx
    split at hx
    · rename_i hxb
      subst hxb
      rw [Option.some.injEq] at hx
      subst hx
      exact ⟨ob, hob, rfl, rfl, rfl, fun h => absurd rfl h⟩
    · rename_i hxb
      exact ⟨o', hx, rfl, rfl, rfl, fun _ => rfl⟩
  have hroot : (m.setObj b { ob with canonical := true }).root = m.root := rfl
  -- The root's object is canonical, so the promote leaves it as it is.
  have hrootObj : ∀ o', (m.setObj b { ob with canonical := true }).obj? m.root = some o' →
      m.obj? m.root = some o' := by
    intro o' ho'
    rw [HMem.obj?_setObj] at ho'
    split at ho'
    · rename_i hrb
      rw [Option.some.injEq] at ho'
      subst ho'
      obtain ⟨o0, ho0, hc0, -⟩ := hm.root
      rw [hrb, hob, Option.some.injEq] at ho0
      subst ho0
      rw [hobj_canonical_true hc0, hrb]
      exact hob
    · exact ho'
  refine ⟨?_, ?_, ?_⟩
  · intro x o' hx hco hw hD v hv z p r0 hp hr0
    obtain ⟨o, hox, e1, -, e3, hsame⟩ := hback x o' hx
    have hp' : o.ptr? z = some p := by unfold HObj.ptr? at hp ⊢; rw [← e3]; exact hp
    rw [e1] at hw hD hv
    by_cases hxb : x = b
    · subst hxb
      rw [hob, Option.some.injEq] at hox
      subst hox
      cases hco' : ob.canonical with
      | true => exact (hc.mono x ob hob hco' hw hD v hv z p r0 hp' hr0).keep hm.tbl hk hob hp'
      | false =>
        -- A snapshot of y's latest version.
        obtain ⟨ob1, hob1, hoy, hcase⟩ := hrd
        rw [hob, Option.some.injEq] at hob1
        subst hob1
        rcases hcase with hcase | ⟨hyD, hyw, hpos⟩
        · rw [hco'] at hcase; cases hcase
        obtain ⟨r1, w1, e1', e2, -, -, -, -, hss⟩ := hm.snap x ob hob hco'
        rw [hoy] at hv e2
        rw [hpos, hv, Option.map_some, Option.some.injEq] at e1'
        subst e1'
        rw [hinv.lv_at hv, Option.some.injEq] at e2
        subst e2
        right
        obtain ⟨q1, hq1⟩ := ruleRRef_some_some S0 m.s z r0
        have h1 := ruleRRef_some_ge hq1
        obtain ⟨r2, hr2, hle2⟩ := hss z p hp' q1 (by rw [hr0]; exact hq1)
        obtain ⟨r3, hr3, hle3⟩ := HMem.slowRef_ge m S0 z p hr2
        exact ⟨r3, by rw [hk.slowRef S0 z (hm.tbl.ptr_handle hob hp')]; exact hr3, by omega⟩
    · rw [hsame hxb] at hco
      exact (hc.mono x o hox hco hw hD v hv z p r0 hp' hr0).keep hm.tbl hk hox hp'
  · intro hv o' ho' z p hp hzp hzD
    rw [hroot] at ho'
    have ho := hrootObj o' ho'
    exact hk.canon p (hc.rootD hv o' ho z p hp hzp hzD)
  · intro hv o' ho' z p hp hzp hzD u hu
    rw [hroot] at ho'
    have ho := hrootObj o' ho'
    exact (hc.rootClean hv o' ho z p hp hzp hzD u hu).keep hm.tbl hk ho hp

/-- The writer's follow of a live pointer of the canonical object of a current
node keeps T9's invariant. -/
theorem CInvH.follow_writer (hinv : Inv sp db k) (hls : LiveSub sp) (hev : EvLogic sp db k)
    (hm : HEInv sp db S0 k m) (hc : CInvH sp db S0 m) {a : Nat} {op : HObj V}
    (hop : m.obj? a = some op) (hco : op.canonical = true) (hr : reachable sp db.P k op.node = true)
    {y : NodeId} (hy : y ∈ sp.live op.hist) : CInvH sp db S0 (m.follow sp S0 db.S a y true).1 := by
  obtain ⟨n, hn, hhist, -, -⟩ := hm.cc a op hop hco
  have hy' : y ∈ sp.live (n.hist.upTo k) := by
    rw [upTo_of_forall _ _ (hinv.times _ n hn), ← hhist]; exact hy
  obtain ⟨e, he, hye⟩ := hls _ _ hy'
  obtain ⟨ny, hny, hlt⟩ := hinv.ptrs op.node n hn e (mem_upTo.mp he).1 y hye
  have hyroot : y ≠ SIS.root := hinv.ptr_ne_root hn (mem_upTo.mp he).1 hye
  have hyw : written sp y = true := written_of_ne_root sp hyroot
  have hry : reachable sp db.P k y = true := by
    rw [reachable_iff] at hr ⊢; exact Reach.child hr hn hy' hny hlt
  obtain ⟨p, hp, hli1, hli2⟩ := hm.live a op hop hco hr y hy
  have hg : HPtrGood S0 db m y p := by
    cases hyD : inD db.D y with
    | true => exact Or.inl ⟨hyD, hli1 hyD⟩
    | false => exact Or.inr ⟨hyD, hli2 hyD⟩
  obtain ⟨m1, n1, b1, hf⟩ := hm.followR_some hinv hop hp hg hyw hry
  have hF := hm.followR_ok hinv hop hf
  have hrd := hF.readable op p hop hp hg hyw
  have hc1 := hc.followR hinv hm hop hf
  obtain ⟨ob, hob, -, hpe, -, -⟩ := hF.inv.promote_ok hinv hev hls hF.objOf hF.tableOf hrd hry
  have hfe : m.follow sp S0 db.S a y true = (m1.setObj b1 { ob with canonical := true }, some b1) := by
    unfold HMem.follow; rw [hf]; exact hpe
  rw [hfe]
  exact hc1.promote hinv hF.inv hob hrd

/-- The writer reaches one node of a path. -/
theorem CInvH.reachOnPath (hinv : Inv sp db k) (hls : LiveSub sp) (hev : EvLogic sp db k)
    (hm : HEInv sp db S0 k m) (hc : CInvH sp db S0 m) {path : List NodeId}
    (hpath : ∀ p ∈ path, reachable sp db.P k p = true) (x : NodeId) :
    CInvH sp db S0 (m.reachOnPath sp S0 db.S db.P (k + 1) path x) := by
  unfold HMem.reachOnPath
  have hK1 : k + 1 - 1 = k := by omega
  cases hf : path.find? (fun p => match db.P.get? p, m.canonicalOf p with
      | some n, some _ => (sp.live (n.hist.upTo (k + 1 - 1))).contains x
      | _, _ => false) with
  | none => exact hc
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
        obtain ⟨nf, hnf, hh', -, -⟩ := hm.cc bp op hop hco
        rw [hnode, hnp, Option.some.injEq] at hnf
        subst hnf
        have hxop : x ∈ sp.live op.hist := by
          rw [hh', ← upTo_of_forall _ _ (hinv.times p np hnp)]; exact hpp
        exact hc.follow_writer hinv hls hev hm hop hco (by rw [hnode]; exact hpath p hpm) hxop

/-- The writer reaches the nodes of its paths: T9's invariant is kept. -/
theorem CInvH.reachPath (hinv : Inv sp db k) (hls : LiveSub sp) (hev : EvLogic sp db k)
    {path : List NodeId} (hpath : ∀ p ∈ path, reachable sp db.P k p = true) :
    ∀ (L : List NodeId) (m : HMem V), HEInv sp db S0 k m → CInvH sp db S0 m →
      CInvH sp db S0 (L.foldl (HMem.reachOnPath sp S0 db.S db.P (k + 1) path) m) := by
  intro L
  induction L with
  | nil => intro m _ hc; exact hc
  | cons x L ih =>
    intro m hm hc
    simp only [List.foldl_cons]
    exact ih _ (hm.reachOnPath_ok hinv hls hev hpath x).1 (hc.reachOnPath hinv hls hev hm hpath x)

end Walk

/-! ## The change -/

section Change

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : HMem V} {c : Changes V}

/-- The change keeps what the pointers give: the old handles and objects stay,
with their flags. -/
theorem HEInv.keepPtrs_applyChange (hinv : Inv sp db k) (hm : HEInv sp db S0 k m)
    (hstep : StepOK sp db.P (k + 1) c) : m.KeepPtrs (m.applyChange sp db.P (k + 1) c) := by
  have haf := hm.addFactsH hinv hstep
  have hcf := changeFactsH sp db.P (k + 1) c m
  have hhlt : ∀ n hd, m.handle? n = some hd → n < m.nextHandle := by
    intro n hd h; exact Nat.lt_of_not_le (fun hle => by rw [hm.freshH n hle] at h; cases h)
  have holt : ∀ a o, m.obj? a = some o → a < m.nextObj := by
    intro a o h; exact Nat.lt_of_not_le (fun hle => by rw [hm.freshO a hle] at h; cases h)
  refine ⟨by rw [hcf.s, haf.s], fun n hd h => ⟨hd, ?_, rfl⟩, fun q h => ?_⟩
  · rw [hcf.handle? n, haf.hold n (hhlt n hd h)]; exact h
  · obtain ⟨n', b', ob', hqn, hb', hob', hcb'⟩ := (m.holdsCanonical_iff q).mp h
    have hn'lt : n' < m.nextHandle := by
      unfold HMem.objOf at hb'
      cases hq' : m.handle? n' with
      | none => rw [hq'] at hb'; cases hb'
      | some hd' => exact hhlt n' hd' hq'
    refine ((m.applyChange sp db.P (k + 1) c).holdsCanonical_iff q).mpr ⟨n', b',
      updAllH sp db.P (k + 1) (c.new.foldl addNewH m)
        (c.adds.filter (fun e => (c.new.foldl addNewH m).canonicalOf e.1 == some b')) ob', hqn, ?_, ?_, ?_⟩
    · rw [hcf.objOf]; unfold HMem.objOf; rw [haf.hold n' hn'lt]; exact hb'
    · rw [hcf.obj b', haf.old b' (holt b' ob' hob'), hob']; rfl
    · rw [(updAllH_core _ _ _ _ _ ob').2.2.2.2.1]; exact hcb'


/-- The change keeps T9's invariant: the old pointers stay, and keep what they
give; a new pointer holds its pointee's live handle with its canonical object,
or is a copy of a pointer whose record is its pointee's latest version; a new
node has no version yet. -/
theorem CInvH.applyChange (hinv : Inv sp db k) (hm : HEInv sp db S0 k m)
    (hc : CInvH sp db S0 m) (hstep : StepOK sp db.P (k + 1) c)
    (hpd : ∀ x ∈ pathOf sp db.P c (k + 1), HPathDone sp db.P k (pathOf sp db.P c (k + 1)) m x)
    (hcopy : CopyStep sp db.P (k + 1) c) :
    CInvH sp db S0 (m.applyChange sp db.P (k + 1) c) := by
  have haf := hm.addFactsH hinv hstep
  have hcf := changeFactsH sp db.P (k + 1) c m
  have holt : ∀ a o, m.obj? a = some o → a < m.nextObj := by
    intro a o h; exact Nat.lt_of_not_le (fun hle => by rw [hm.freshO a hle] at h; cases h)
  have hk := hm.keepPtrs_applyChange hinv hstep
  -- Every pointee of an add has a new pointer.
  have hK1 : k + 1 - 1 = k := by omega
  have hpr : ∀ p ∈ pathOf sp db.P c (k + 1), reachable sp db.P k p = true := by
    intro p hp; have := (mem_pathOf hp).1; rw [hK1] at this; exact this
  have hpn : ∀ p ∈ pathOf sp db.P c (k + 1), (db.P.get? p).isSome := by
    intro p hp; obtain ⟨-, n, hn, -⟩ := mem_pathOf hp; rw [hn]; rfl
  have hNS : ∀ e ∈ c.adds, ∀ y ∈ sp.ptrs e.2, (NSH sp db.P (k + 1) (c.new.foldl addNewH m) y).isSome := by
    intro e he y hy
    by_cases hyn : y ∈ c.new.map (·.id)
    · exact hm.NSH_some hinv hpd hpr hpn hstep (Or.inl hyn)
    · rcases hcopy e he y hy hyn with h | ⟨z, hz, nz, hnz, hyz, hwl⟩
      · exact hm.NSH_some hinv hpd hpr hpn hstep (Or.inr (Or.inl h))
      · rw [hK1] at hwl
        exact hm.NSH_some hinv hpd hpr hpn hstep (Or.inr (Or.inr ⟨z, hz, nz, hnz, hyz, hwl⟩))
  -- A new pointer: what `PtrAtLeast` asks, for a record at most the pointee's
  -- latest version's; and it holds a canonical object if the pointee is in D.
  have hnew : ∀ y q, NSH sp db.P (k + 1) (c.new.foldl addNewH m) y = some q →
      ((m.applyChange sp db.P (k + 1) c).holdsCanonical q = true ∨
        (inD db.D y = false ∧ ∀ u, db.S.lv y = some u →
          ∃ r, (m.applyChange sp db.P (k + 1) c).slowRef S0 y q = some r ∧ u.recNo ≤ r)) := by
    intro y q hns
    rcases hm.NSH_good hinv hstep hns with ⟨b, hb, rfl⟩ | ⟨-, hzD, -, href, a0, o0, ho0, hq0⟩
    · left
      have hcs : ((m.applyChange sp db.P (k + 1) c).canonicalOf y).isSome = true := by
        rw [hcf.canonicalOf, hb]; rfl
      have := HMem.holdsCanonical_tableOf
        ({ ref := ((c.new.foldl addNewH m).obj? b).bind (·.pos),
           handle := (c.new.foldl addNewH m).tableOf y } : HPtr) hcs
      rw [hcf.tableOf] at this
      exact this
    · cases hhc : m.holdsCanonical q with
      | true => exact Or.inl (hk.canon q hhc)
      | false =>
        right
        refine ⟨hzD, fun u hu => ⟨u.recNo, ?_, Nat.le_refl _⟩⟩
        rw [hk.slowRef S0 y (hm.tbl.ptr_handle ho0 hq0), ← HMem.slowRef_of_not_holds hhc, href, hu]
        rfl
  -- The objects of the new memory.
  have hobj : ∀ a o3, (m.applyChange sp db.P (k + 1) c).obj? a = some o3 →
      ∃ o1, (c.new.foldl addNewH m).obj? a = some o1 ∧
        o3 = updAllH sp db.P (k + 1) (c.new.foldl addNewH m)
          (c.adds.filter (fun e => (c.new.foldl addNewH m).canonicalOf e.1 == some a)) o1 := by
    intro a o3 ho3
    rw [hcf.obj a] at ho3
    obtain ⟨o1, ho1, rfl⟩ := Option.map_eq_some_iff.mp ho3
    exact ⟨o1, ho1, rfl⟩
  -- A pointer of an old object for y: the new pointer, or the old one.
  have hptr : ∀ a o1 y p, m.obj? a = some o1 →
      (updAllH sp db.P (k + 1) (c.new.foldl addNewH m)
        (c.adds.filter (fun e => (c.new.foldl addNewH m).canonicalOf e.1 == some a)) o1).ptr? y = some p →
      (∃ e ∈ c.adds, y ∈ sp.ptrs e.2 ∧ NSH sp db.P (k + 1) (c.new.foldl addNewH m) y = some p) ∨
        (y ∉ (c.adds.filter (fun e => (c.new.foldl addNewH m).canonicalOf e.1 == some a)).flatMap
          (fun a => sp.ptrs a.2) ∧ o1.ptr? y = some p) := by
    intro a o1 y p ho1 hp
    rw [updAllH_ptr] at hp
    split at hp
    · rename_i hyL
      obtain ⟨e, heL, hye⟩ := List.mem_flatMap.mp hyL
      have he : e ∈ c.adds := (List.mem_filter.mp heL).1
      obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (hNS e he y hye)
      unfold comboH at hp
      rw [hq, Option.some_or] at hp
      exact Or.inl ⟨e, he, hye, by rw [hq, hp]⟩
    · rename_i hyL
      exact Or.inr ⟨hyL, hp⟩
  have hroot3 : (m.applyChange sp db.P (k + 1) c).root = m.root := by rw [hcf.root, haf.root]
  -- The root's object: the old one with new entries.
  obtain ⟨o0, ho0, hc0, hn0⟩ := hm.root
  have hroot1 : (c.new.foldl addNewH m).obj? m.root = some o0 := by
    rw [haf.old m.root (holt _ _ ho0)]; exact ho0
  have hrootObj : ∀ o3, (m.applyChange sp db.P (k + 1) c).obj? (m.applyChange sp db.P (k + 1) c).root =
      some o3 → o3 = updAllH sp db.P (k + 1) (c.new.foldl addNewH m)
        (c.adds.filter (fun e => (c.new.foldl addNewH m).canonicalOf e.1 == some m.root)) o0 := by
    intro o3 ho3
    rw [hroot3] at ho3
    obtain ⟨o1, ho1, rfl⟩ := hobj m.root o3 ho3
    rw [hroot1, Option.some.injEq] at ho1
    rw [ho1]
  -- A pointee of the root's new history is a pointee of the old one or of an add.
  have hpoint : ∀ y, y ∈ pointees sp (updAllH sp db.P (k + 1) (c.new.foldl addNewH m)
        (c.adds.filter (fun e => (c.new.foldl addNewH m).canonicalOf e.1 == some m.root)) o0).hist →
      y ∉ (c.adds.filter (fun e => (c.new.foldl addNewH m).canonicalOf e.1 == some m.root)).flatMap
        (fun a => sp.ptrs a.2) → y ∈ pointees sp o0.hist := by
    intro y hy hyL
    rw [(updAllH_core _ _ _ _ _ o0).2.2.2.1] at hy
    obtain ⟨e, he, hye⟩ := (mem_pointees sp _ _).mp hy
    rcases List.mem_append.mp he with he1 | he2
    · exact (mem_pointees sp _ _).mpr ⟨e, he1, hye⟩
    · exfalso
      obtain ⟨a', ha', rfl⟩ := List.mem_map.mp he2
      exact hyL (List.mem_flatMap.mpr ⟨a', ha', hye⟩)
  refine ⟨?_, ?_, ?_⟩
  · intro a o3 ho3 hco hw hD v hv y p r0 hp hr0
    obtain ⟨o1, ho1, rfl⟩ := hobj a o3 ho3
    obtain ⟨e1, -, -, -, e5, -⟩ := updAllH_core sp db.P (k + 1) (c.new.foldl addNewH m)
      (c.adds.filter (fun e => (c.new.foldl addNewH m).canonicalOf e.1 == some a)) o1
    rw [e1] at hw hD hv
    rw [e5] at hco
    rcases haf.cls a o1 ho1 with ⟨-, hold⟩ | ⟨-, nn, hnn, hon, -⟩
    · obtain ⟨u, hu, hle⟩ := hinv.ref_le_lv hv hr0
      rcases hptr a o1 y p hold hp with ⟨-, -, -, hq⟩ | ⟨-, hp1⟩
      · rcases hnew y p hq with h | ⟨-, h⟩
        · exact Or.inl h
        · obtain ⟨r, hr, hle'⟩ := h u hu
          exact Or.inr ⟨r, hr, by omega⟩
      · exact (hc.mono a o1 hold hco hw hD v hv y p r0 hp1 hr0).keep hm.tbl hk hold hp1
    · -- A new node has no version yet.
      exfalso
      have hfr := hstep.fresh nn hnn
      obtain ⟨-, -, n, hn, -⟩ := hinv.version_node (hinv.lv_at hv)
      rw [hon] at hn
      simp only [hnewObj] at hn
      rw [hfr] at hn; cases hn
  · intro hv o3 ho3 y p hp hyp hyD
    have e := hrootObj o3 ho3
    subst e
    rcases hptr m.root o0 y p ho0 hp with ⟨-, -, -, hq⟩ | ⟨hyL, hp1⟩
    · rcases hnew y p hq with h | ⟨hyD', -⟩
      · exact h
      · rw [hyD] at hyD'; cases hyD'
    · exact hk.canon p (hc.rootD hv o0 ho0 y p hp1 (hpoint y hyp hyL) hyD)
  · intro hv o3 ho3 y p hp hyp hyD u hu
    have e := hrootObj o3 ho3
    subst e
    rcases hptr m.root o0 y p ho0 hp with ⟨-, -, -, hq⟩ | ⟨hyL, hp1⟩
    · rcases hnew y p hq with h | ⟨-, h⟩
      · exact Or.inl h
      · obtain ⟨r, hr, hle'⟩ := h u hu
        exact Or.inr ⟨r, hr, hle'⟩
    · exact (hc.rootClean hv o0 ho0 y p hp1 (hpoint y hyp hyL) hyD u hu).keep hm.tbl hk ho0 hp1

end Change

/-! ## The root's pointers after the change -/

section Root

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : HMem V} {c : Changes V}

/-- With a virtual root, the root's new pointees are new root children. -/
theorem HEInv.rootNewH (hinv : Inv sp db k) (hm : HEInv sp db S0 k m) (hstep : StepOK sp db.P (k + 1) c)
    (hv : sp.virt = true) {y : NodeId}
    (hy : y ∈ (c.adds.filter (fun a => (c.new.foldl addNewH m).canonicalOf a.1 == some m.root)).flatMap
      (fun a => sp.ptrs a.2)) :
    y ∈ c.new.map (·.id) := by
  have haf := hm.addFactsH hinv hstep
  obtain ⟨a, ha, hya⟩ := List.mem_flatMap.mp hy
  obtain ⟨o0, ho0, hc0, hn0⟩ := hm.root
  have hcr : m.canonicalOf SIS.root = some m.root := by rw [← hn0]; exact hm.canonicalOf_of ho0 hc0
  have hrn : SIS.root ∉ c.new.map (·.id) := by
    intro hr
    obtain ⟨nn, hnn, he⟩ := List.mem_map.mp hr
    have := hstep.fresh nn hnn
    rw [he] at this
    obtain ⟨n0, h0⟩ := Option.isSome_iff_exists.mp hinv.rootIn
    rw [h0] at this; cases this
  have hcr' : (c.new.foldl addNewH m).canonicalOf SIS.root = some m.root := by
    rw [haf.canOld _ hrn]; exact hcr
  rw [adds_filter_nodeH haf.tbl hcr'] at ha
  have ha' : a ∈ c.adds.filter (fun a => a.1 == SIS.root) := ha
  rw [(hstep.virt hv).rootAdds] at ha'
  obtain ⟨nn, hnn, rfl⟩ := List.mem_map.mp ha'
  simp only [(hinv.vr hv).rootPtrs, List.mem_singleton] at hya
  subst hya
  exact List.mem_map.mpr ⟨nn, (List.mem_filter.mp hnn).1, rfl⟩

/-- With a virtual root, after the change: the root's object's pointer for a
root child on the writer's paths, or a new one, holds that node's live handle
with its canonical object (the walk reached it from the root; the change gave
the new one its new canonical object). -/
theorem HEInv.rootPtrs_change (hinv : Inv sp db k) (hls : LiveSub sp) (hm : HEInv sp db S0 k m)
    (hstep : StepOK sp db.P (k + 1) c) (hv : sp.virt = true) {path : List NodeId}
    (hpr : ∀ p ∈ path, reachable sp db.P k p = true) (hpn : ∀ p ∈ path, (db.P.get? p).isSome)
    (hpd : ∀ x ∈ path, HPathDone sp db.P k path m x) {o : HObj V}
    (ho : (m.applyChange sp db.P (k + 1) c).obj? (m.applyChange sp db.P (k + 1) c).root = some o)
    {y : NodeId} {p : HPtr} (hp : o.ptr? y = some p) (hyp : y ∈ pointees sp o.hist)
    (hy : y ∈ path ∨ y ∈ c.new.map (·.id)) :
    (m.applyChange sp db.P (k + 1) c).holdsCanonical p = true := by
  have haf := hm.addFactsH hinv hstep
  have hcf := changeFactsH sp db.P (k + 1) c m
  have hk := hm.keepPtrs_applyChange hinv hstep
  have hroot : (m.applyChange sp db.P (k + 1) c).root = m.root := by rw [hcf.root, haf.root]
  rw [hroot, hcf.obj] at ho
  obtain ⟨o1, ho1, rfl⟩ := Option.map_eq_some_iff.mp ho
  obtain ⟨o0, ho0, hc0, hn0⟩ := hm.root
  have hlt : m.root < m.nextObj := Nat.lt_of_not_le (fun hle => by rw [hm.freshO _ hle] at ho0; cases ho0)
  rw [haf.old _ hlt, ho0, Option.some.injEq] at ho1
  subst ho1
  obtain ⟨-, -, -, e4, -, -⟩ := updAllH_core sp db.P (k + 1) (c.new.foldl addNewH m)
    (c.adds.filter (fun a => (c.new.foldl addNewH m).canonicalOf a.1 == some m.root)) o0
  -- A new pointer for a node with a canonical object holds it.
  have hnewc : ∀ q, NSH sp db.P (k + 1) (c.new.foldl addNewH m) y = some q →
      ((c.new.foldl addNewH m).canonicalOf y).isSome = true →
      (m.applyChange sp db.P (k + 1) c).holdsCanonical q = true := by
    intro q hns hcs
    rcases hm.NSH_good hinv hstep hns with ⟨b, hb, rfl⟩ | ⟨hnone, -⟩
    · have hcs' : ((m.applyChange sp db.P (k + 1) c).canonicalOf y).isSome = true := by
        rw [hcf.canonicalOf, hb]; rfl
      have := HMem.holdsCanonical_tableOf
        ({ ref := ((c.new.foldl addNewH m).obj? b).bind (·.pos),
           handle := (c.new.foldl addNewH m).tableOf y } : HPtr) hcs'
      rw [hcf.tableOf] at this
      exact this
    · rw [hnone] at hcs; cases hcs
  rw [updAllH_ptr] at hp
  split at hp
  · -- a new root child
    rename_i hya
    have hyn := hm.rootNewH hinv hstep hv hya
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (hm.NSH_some hinv hpd hpr hpn hstep (Or.inl hyn))
    unfold comboH at hp
    rw [hq, Option.some_or, Option.some.injEq] at hp
    subst hp
    obtain ⟨nn, hnn, he⟩ := List.mem_map.mp hyn
    obtain ⟨a2, -, -, -, -, hc2, -⟩ := haf.canNew nn hnn
    exact hnewc q hq (by rw [← he, hc2]; rfl)
  · rename_i hya
    have hyp0 : y ∈ pointees sp o0.hist := by
      rw [e4] at hyp
      rcases pointees_append_mem hyp with h | h
      · exact h
      · exfalso
        obtain ⟨a, ha, hya'⟩ := pointees_adds_mem h
        exact hya (List.mem_flatMap.mpr ⟨a, ha, hya'⟩)
    obtain ⟨n0, hn0', hh0, -, -⟩ := hm.cc m.root o0 ho0 hc0
    rw [hn0] at hn0'
    rw [hh0] at hyp0
    obtain ⟨my, cy, htop⟩ := (hinv.vr hv).top_of_pointee hn0' hyp0
    have hyn : y ∉ c.new.map (·.id) := by
      intro hy'
      obtain ⟨nn, hnn, he⟩ := List.mem_map.mp hy'
      have := hstep.fresh nn hnn
      rw [he, htop.1] at this; cases this
    have hyp' : y ∈ path := by
      rcases hy with h | h
      · exact h
      · exact absurd h hyn
    obtain ⟨-, hpd2⟩ := hpd y hyp'
    obtain ⟨p', hpp, np, bp, op, ptr, hnp, hyl, hcp, hop, hptr, hhl⟩ := hpd2 htop.2.1
    have hpr' : p' = SIS.root := hinv.parent_of_top hls hv (hpr p' hpp) hnp hyl htop.isTop
    subst hpr'
    have hcr : m.canonicalOf SIS.root = some m.root := by rw [← hn0]; exact hm.canonicalOf_of ho0 hc0
    rw [hcr, Option.some.injEq] at hcp
    subst hcp
    rw [ho0, Option.some.injEq] at hop
    subst hop
    rw [hptr, Option.some.injEq] at hp
    subst hp
    exact hk.canon _ (HMem.holdsCanonical_of_holdsLive hhl)

end Root

/-! ## The next state -/

section Next

variable {sp : Spec V T} {al : Algo V T} {db : DB V T} {tr : T} {S0 : Stream V T} {k : Nat}

/-- After the writes, T9's invariant of the next state. A written node's new
version names its pointees' latest versions; its pointers hold canonical
objects (pinned, for D1), or have these as the record rule's references. A node
not written keeps its pointers and its version. -/
theorem CInvH.next (hsp : SpecOK sp) (hinv : Inv sp db k) (hmk : al.mark = true)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) (hinv' : Inv sp (step sp al db tr) (k + 1))
    {m3 m6 : HMem V}
    (ha : HAInv sp db S0 k (parts sp al db tr).c (pathOf sp db.P (parts sp al db tr).c (k + 1)) m3)
    (hc3 : CInvH sp db S0 m3)
    (hroot3 : sp.virt = true → ∀ o, m3.obj? m3.root = some o → ∀ y p, o.ptr? y = some p →
      y ∈ pointees sp o.hist → (y ∈ pathOf sp db.P (parts sp al db tr).c (k + 1) ∨
        y ∈ (parts sp al db tr).c.new.map (·.id)) → m3.holdsCanonical p = true)
    (hfr : LoopsFrameH S0 db.D (parts sp al db tr).D1 (dataIds sp al db tr) (parts sp al db tr).taken (k + 1)
      m3 m6) :
    CInvH sp (step sp al db tr) S0 m6 := by
  have hP : (parts sp al db tr).P = db.P.apply (k + 1) (parts sp al db tr).c := parts_P' sp al db tr hinv.len
  have hP' : (step sp al db tr).P = (parts sp al db tr).P := rfl
  have hS' : (step sp al db tr).S = Snew sp al db tr := rfl
  -- Objects of m6 come from m3.
  have hobj : ∀ a o6, m6.obj? a = some o6 → ∃ o3, m3.obj? a = some o3 ∧ o6.node = o3.node ∧
      o6.level = o3.level ∧ o6.isData = o3.isData ∧ o6.hist = o3.hist ∧ o6.canonical = o3.canonical ∧
      (∀ z, o6.ptr? z = o3.ptr? z ∨ o6.ptr? z = (o3.ptr? z).map (m3.resolveP S0 db.D z) ∨
        o6.ptr? z = (o3.ptr? z).map (m3.resolveP S0 (parts sp al db tr).D1 z)) ∧
      ((o3.node ∈ (parts sp al db tr).taken ∧ m3.canonicalOf o3.node = some a) →
        ∀ z, o6.ptr? z = (o3.ptr? z).map (m3.resolveP S0 (parts sp al db tr).D1 z)) ∧
      (¬ ((o3.node ∈ dataIds sp al db tr ∨ o3.node ∈ (parts sp al db tr).taken) ∧
        m3.canonicalOf o3.node = some a) → o6.pos = o3.pos ∧ ∀ z, o6.ptr? z = o3.ptr? z) := by
    intro a o6 ho6
    obtain ⟨o3, ho3⟩ : ∃ o3, m3.obj? a = some o3 := by
      cases h3 : m3.obj? a with
      | none => rw [hfr.none a h3] at ho6; cases ho6
      | some o3 => exact ⟨o3, rfl⟩
    obtain ⟨o6', ho6', rest⟩ := hfr.obj a o3 ho3
    rw [ho6, Option.some.injEq] at ho6'
    subst ho6'
    exact ⟨o3, ho3, rest⟩
  -- The handles and the startup pos stay, so the slow path's references do.
  have hhd : ∀ n, m6.handle? n = m3.handle? n := by intro n; unfold HMem.handle?; rw [hfr.handles]
  have hslow : ∀ z q, m6.slowRef S0 z q = m3.slowRef S0 z q := HMem.slowRef_congr S0 hfr.s hhd
  have hAL : ∀ z q r0, m3.PtrAtLeast S0 z q r0 → m6.PtrAtLeast S0 z q r0 := by
    intro z q r0 h
    rcases h with h | ⟨r, hr, hle⟩
    · exact Or.inl (by rw [hfr.hc]; exact h)
    · exact Or.inr ⟨r, by rw [hslow]; exact hr, hle⟩
  -- D after the transaction.
  have hD1D : ∀ y, inD db.D y = true → inD (parts sp al db tr).D1 y = true := by
    intro y hy
    obtain ⟨d, hd⟩ := (inD_iff _ _).mp hy
    exact (inD_iff _ _).mpr ⟨d, (step_D1_mem sp al db tr hinv.len _).mpr (Or.inl hd)⟩
  have hD'D1 : ∀ y, inD (parts sp al db tr).r7.1 y = true → inD (parts sp al db tr).D1 y = true :=
    fun y hy => step_r7_D1 sp al db tr hinv hy
  have hD1cases : ∀ y, inD (parts sp al db tr).D1 y = true →
      inD db.D y = true ∨ y ∈ pathOf sp db.P (parts sp al db tr).c (k + 1) ∨
        y ∈ (parts sp al db tr).c.new.map (·.id) := by
    intro y hy
    rcases step_D1_cases sp al db tr hmk hinv hy with h | h | h
    · exact Or.inl h
    · by_cases hn : y ∈ (parts sp al db tr).c.new.map (·.id)
      · exact Or.inr (Or.inr hn)
      · rw [hP] at h
        exact Or.inr (Or.inl (step_marked_path sp al db tr hsp hinv hstep h hn))
    · exact Or.inr (Or.inl (step_touched_path sp al db tr hstep h))
  have hnotw : ∀ z, z ∉ dataIds sp al db tr → z ∉ (parts sp al db tr).taken →
      (Snew sp al db tr).lv z = db.S.lv z := by
    intro z h1 h2
    apply lv_Snew_not_written
    intro w hw hwz
    have := (step_written_iff sp al db tr hinv hstep z).mp ⟨w, hw, hwz⟩
    rcases this with h | h
    · exact h1 h
    · exact h2 h
  have htakenD : ∀ x ∈ (parts sp al db tr).taken, ∃ d, (x, d) ∈ db.D ∧ d ≤ (parts sp al db tr).s :=
    fun x hx => step_taken_inD (al := al) (tr := tr) hinv hx
  have hdnew : ∀ x ∈ dataIds sp al db tr, x ∈ (parts sp al db tr).c.new.map (·.id) := by
    intro x hx
    simp only [dataIds, List.mem_map, List.mem_filter] at hx
    obtain ⟨nn, ⟨hnn, -⟩, rfl⟩ := hx
    exact List.mem_map.mpr ⟨nn, hnn, rfl⟩
  have htakenND : ∀ z, inD db.D z = false → z ∉ (parts sp al db tr).taken := by
    intro z hz hzt
    obtain ⟨d, hd, -⟩ := htakenD z hzt
    rw [(inD_iff _ _).mpr ⟨d, hd⟩] at hz; cases hz
  have hD2 : ∀ z, inD (parts sp al db tr).D1 z = true → z ∉ (parts sp al db tr).taken →
      inD (parts sp al db tr).r7.1 z = true := by
    intro z hz hzt
    obtain ⟨d, hd⟩ := (inD_iff _ _).mp hz
    have h2 := step_D2_of_not_taken sp al db tr hd hzt
    obtain ⟨d2, hd2⟩ := (inD_iff _ _).mp h2
    rw [(step_r7_shape sp al db tr hinv.len).1]
    exact (inD_iff _ _).mpr ⟨d2, List.mem_append_left _ hd2⟩
  -- The root is not written.
  have hroot6 : sp.virt = true → ∀ o6, m6.obj? m6.root = some o6 → ∃ o3, m3.obj? m3.root = some o3 ∧
      o6.hist = o3.hist ∧ ∀ z, o6.ptr? z = o3.ptr? z := by
    intro hv o6 ho6
    rw [hfr.root] at ho6
    obtain ⟨o3, ho3, -, -, -, e4, -, -, -, hun⟩ := hobj _ o6 ho6
    obtain ⟨o0, ho0, -, hn0⟩ := ha.root
    rw [ho3, Option.some.injEq] at ho0
    subst ho0
    refine ⟨o3, ho3, e4, (hun ?_).2⟩
    rintro ⟨h1 | h1, -⟩
    · rw [hn0] at h1
      obtain ⟨hnone, -⟩ := step_dataIds_spec sp al db tr hinv hstep h1
      have := hinv.rootIn
      rw [hnone] at this; cases this
    · rw [hn0] at h1
      exact htakenND _ (hinv.vr hv).rootND h1
  refine ⟨?_, ?_, ?_⟩
  · -- mono
    intro a o6 ho6 hco hw hD v hv y p r0 hp hr0
    obtain ⟨o3, ho3, e1, -, -, e4, e5, hsl6, hpin, hun⟩ := hobj a o6 ho6
    have hc3' : o3.canonical = true := by rw [← e5]; exact hco
    have hcx : m3.canonicalOf o3.node = some a := ha.tbl.canonicalOf_of ho3 hc3'
    by_cases hxw : o3.node ∈ dataIds sp al db tr ∨ o3.node ∈ (parts sp al db tr).taken
    · -- written in the record: v is its new version, of its node in the new structure
      obtain ⟨n, hn, hh, -, -⟩ := ha.cc a o3 ho3 hc3'
      have hn' : (parts sp al db tr).P.get? o3.node = some n := by rw [hP]; exact hn
      have hyv : y ∈ pointees sp v.hist := hinv'.ref_pointees hv hr0
      obtain ⟨-, -, n', hn'', hvh, -⟩ := hinv'.version_node (hinv'.lv_at hv)
      rw [hP', e1, hn', Option.some.injEq] at hn''
      subst hn''
      have hyn : y ∈ pointees sp n.hist := by
        obtain ⟨e, he, hye⟩ := (mem_pointees sp _ _).mp hyv
        rw [hvh] at he
        exact (mem_pointees sp _ _).mpr ⟨e, (mem_upTo.mp he).1, hye⟩
      rcases hxw with hxd | hxt
      · -- a data node has no pointers
        exfalso
        obtain ⟨-, n2, hn2, hd2⟩ := step_dataIds_spec sp al db tr hinv hstep hxd
        rw [hn', Option.some.injEq] at hn2
        subst hn2
        obtain ⟨e, he, hye⟩ := (mem_pointees sp _ _).mp hyn
        have := hinv'.data o3.node n (by rw [hP']; exact hn') hd2 e he
        rw [this] at hye; cases hye
      · obtain ⟨v', hv', hrefs⟩ := step_taken_refs sp al db tr hsp hinv hstep hxt hn'
        have hv2 : (Snew sp al db tr).lv o3.node = some v := by rw [← e1]; exact hv
        rw [hv2, Option.some.injEq] at hv'
        subst hv'
        have hr0' := hrefs y hyn
        rw [hr0] at hr0'
        obtain ⟨d, hd, -⟩ := htakenD _ hxt
        obtain ⟨p3, hp3, hA1, -⟩ := ha.slots a o3 ho3 hc3' (by rw [← e1]; exact hw)
          (Or.inr (Or.inl ((inD_iff _ _).mpr ⟨d, hd⟩))) y (by rw [hh]; exact hyn)
        have hp6 : p = m3.resolveP S0 (parts sp al db tr).D1 y p3 := by
          have := hpin ⟨hxt, hcx⟩ y
          rw [hp, hp3, Option.map_some, Option.some.injEq] at this
          exact this
        subst hp6
        rcases HMem.resolveP_cases S0 m3 (parts sp al db tr).D1 y p3 with ⟨h1, h2⟩ | ⟨-, -, hcs, h2⟩ |
            ⟨hnc, hnot, h2⟩
        · rw [h2]; exact Or.inl (by rw [hfr.hc]; exact h1)
        · rw [h2]; exact Or.inl (by rw [hfr.hc]; exact HMem.holdsCanonical_tableOf p3 hcs)
        · -- not pinned: y not in D1, so not in D, not taken
          have hyD1 : inD (parts sp al db tr).D1 y = false := by
            cases hy1 : inD (parts sp al db tr).D1 y with
            | false => rfl
            | true => exact absurd ⟨hy1, ha.canon_D1 hsp hinv hmk hstep hy1⟩ hnot
          have hyD : inD db.D y = false := by
            cases hy : inD db.D y with
            | false => rfl
            | true => rw [hD1D y hy] at hyD1; cases hyD1
          have hyt := htakenND y hyD
          by_cases hyd : y ∈ dataIds sp al db tr
          · have := HMem.holdsCanonical_of_holdsLive ((hA1 hyD).2 (hdnew y hyd))
            rw [hnc] at this; cases this
          · refine Or.inr ⟨r0, ?_, Nat.le_refl _⟩
            rw [h2, hslow, HMem.slowRef_ruleR, ← HMem.slowRef_of_not_holds hnc, (hA1 hyD).1,
              ← hnotw y hyd hyt]
            exact hr0'.symm
    · -- not written: its pointers and its version as before, and its node not in D
      rw [not_or] at hxw
      have hxD : inD db.D o3.node = false := by
        cases hx : inD db.D o3.node with
        | false => rfl
        | true =>
          exfalso
          have := hD2 _ (hD1D _ hx) hxw.2
          have hD6 : inD (parts sp al db tr).r7.1 o3.node = false := by rw [← e1]; exact hD
          rw [this] at hD6; cases hD6
      have hv3 : db.S.lv o3.node = some v := by rw [← hnotw _ hxw.1 hxw.2, ← e1]; exact hv
      obtain ⟨-, hsame⟩ := hun (fun ⟨h1, _⟩ => by
        rcases h1 with h1 | h1
        · exact hxw.1 h1
        · exact hxw.2 h1)
      rw [hsame y] at hp
      exact hAL y p r0 (hc3.mono a o3 ho3 hc3' (by rw [← e1]; exact hw) hxD v hv3 y p r0 hp hr0)
  · -- rootD
    intro hv o6 ho6 y p hp hyp hyD
    have hyD6 : inD (parts sp al db tr).r7.1 y = true := hyD
    obtain ⟨o3, ho3, e4, hsame⟩ := hroot6 hv o6 ho6
    rw [hsame y] at hp
    have hyp3 : y ∈ pointees sp o3.hist := by rw [← e4]; exact hyp
    rw [hfr.hc]
    cases hyDb : inD db.D y with
    | true => exact hc3.rootD hv o3 ho3 y p hp hyp3 hyDb
    | false =>
      have hy3 : y ∈ pathOf sp db.P (parts sp al db tr).c (k + 1) ∨
          y ∈ (parts sp al db tr).c.new.map (·.id) := by
        rcases hD1cases y (hD'D1 y hyD6) with h1 | h1
        · rw [hyDb] at h1; cases h1
        · exact h1
      exact hroot3 hv o3 ho3 y p hp hyp3 hy3
  · -- rootClean
    intro hv o6 ho6 y p hp hyp hyD u hu
    obtain ⟨o3, ho3, e4, hsame⟩ := hroot6 hv o6 ho6
    rw [hsame y] at hp
    have hyp3 : y ∈ pointees sp o3.hist := by rw [← e4]; exact hyp
    cases hyDb : inD db.D y with
    | true =>
      -- in D before: the pointer holds y's canonical object
      exact Or.inl (by rw [hfr.hc]; exact hc3.rootD hv o3 ho3 y p hp hyp3 hyDb)
    | false =>
      have hyt := htakenND y hyDb
      -- a root child is an index node
      have hyd : y ∉ dataIds sp al db tr := by
        intro hyd
        obtain ⟨o0, ho0, hc0, hn0⟩ := ha.root
        rw [ho3, Option.some.injEq] at ho0
        subst ho0
        obtain ⟨n, hn, hh, -, -⟩ := ha.cc _ o3 ho3 hc0
        rw [hn0, ← hP] at hn
        rw [hh] at hyp3
        obtain ⟨my, cy, htop⟩ := (hinv'.vr hv).top_of_pointee (by rw [hP']; exact hn) hyp3
        obtain ⟨-, n2, hn2, hd2⟩ := step_dataIds_spec sp al db tr hinv hstep hyd
        have := htop.1
        rw [hP', hn2, Option.some.injEq] at this
        subst this
        rw [htop.2.2.2.1] at hd2; cases hd2
      have hu3 : db.S.lv y = some u := by rw [← hnotw y hyd hyt]; exact hu
      exact hAL y p u.recNo (hc3.rootClean hv o3 ho3 y p hp hyp3 hyDb u hu3)

/-- One transaction of the physical writer with handles keeps T9's invariant:
its read, its walk to the paths, the change, and the writes. -/
theorem CInvH.handleTrans_ok (hsp : SpecOK sp) (hinv : Inv sp db k) (hmk : al.mark = true)
    {m : HMem V} (hm : HEInv sp db S0 k m) (hc : CInvH sp db S0 m) (hev : EvLogic sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) (hphys : PhysStep sp db.P (k + 1) (parts sp al db tr).c)
    (hcopy : CopyStep sp db.P (k + 1) (parts sp al db tr).c) (htree : treeAt sp db.P k)
    (hinv' : Inv sp (step sp al db tr) (k + 1)) :
    CInvH sp (step sp al db tr) S0 (handleTrans sp al S0 db m tr).2 := by
  have hls : LiveSub sp := hsp.liveSub
  have hlen := hinv.len
  have hK1 : k + 1 - 1 = k := by omega
  obtain ⟨hm1, hv⟩ := hm.view_ok hinv hls hev
  have hc1 : CInvH sp db S0 (m.view sp S0 db.S k).1 := hc.read hinv hm k
  have hcx : sp.exec tr db.S.length (m.view sp S0 db.S (db.S.length - 1)).2 = (parts sp al db tr).c := by
    rw [hlen, hK1, hv, parts_c, hlen, hK1]
  rw [handleTrans_eq, hcx, handleAfter_eq]
  have hm1' : HEInv sp db S0 k (m.view sp S0 db.S (db.S.length - 1)).1 := by rw [hlen, hK1]; exact hm1
  have hc1' : CInvH sp db S0 (m.view sp S0 db.S (db.S.length - 1)).1 := by rw [hlen, hK1]; exact hc1
  generalize (m.view sp S0 db.S (db.S.length - 1)).1 = m1 at hm1' hc1' ⊢
  -- The writer's paths.
  have hpr : ∀ p ∈ pathOf sp db.P (parts sp al db tr).c (k + 1), reachable sp db.P k p = true := by
    intro p hp; have := (mem_pathOf hp).1; rw [hK1] at this; exact this
  have hpn : ∀ p ∈ pathOf sp db.P (parts sp al db tr).c (k + 1), (db.P.get? p).isSome := by
    intro p hp; obtain ⟨-, n, hn, -⟩ := mem_pathOf hp; rw [hn]; rfl
  have hparent : ∀ x ∈ pathOf sp db.P (parts sp al db tr).c (k + 1), x ≠ SIS.root →
      ∃ p ∈ pathOf sp db.P (parts sp al db tr).c (k + 1), ∃ np nx, db.P.get? p = some np ∧
        db.P.get? x = some nx ∧ nx.level < np.level ∧ x ∈ sp.live (np.hist.upTo k) := by
    intro x hx hxr
    have hrx := (mem_pathOf hx).1
    rw [hK1] at hrx
    obtain ⟨p, np, nx, hrp, hnp, hnx, hlt, hxl⟩ := reach_parent hrx hxr
    refine ⟨p, pathOf_parent hx (by rw [hK1]; exact hrp) hnp (by rw [hK1]; exact hxl) hnx hlt, np, nx, hnp,
      hnx, hlt, hxl⟩
  have hpnd : (pathOf sp db.P (parts sp al db tr).c (k + 1)).Nodup := by
    unfold pathOf; exact nodup_filter (nodup_eraseDups _) _
  have hsorted := pairwise_byLevelDesc db.P (pathOf sp db.P (parts sp al db tr).c (k + 1))
  obtain ⟨hm2, hpd⟩ := HEInv.reachPath_ok (S0 := S0) hinv hls hev hpr hparent
    ((pathOf sp db.P (parts sp al db tr).c (k + 1)).mergeSort (fun a b => decide (lev db.P b ≤ lev db.P a))) []
    m1 hm1' (fun a ha => by cases ha)
    (fun x => by rw [List.nil_append]; exact (List.mergeSort_perm _ _).mem_iff)
    (by rw [List.nil_append]; exact (List.mergeSort_perm _ _).nodup_iff.mpr hpnd)
    (by rw [List.nil_append]; exact hsorted)
  have hc2 := CInvH.reachPath (S0 := S0) hinv hls hev hpr
    ((pathOf sp db.P (parts sp al db tr).c (k + 1)).mergeSort (fun a b => decide (lev db.P b ≤ lev db.P a)))
    m1 hm1' hc1'
  -- The change.
  have ha := hm2.applyChange_ok hinv hls hpd hstep hphys hcopy htree
  have hc3 := hc2.applyChange hinv hm2 hstep hpd hcopy
  have hroot3 : sp.virt = true → ∀ o, ((((pathOf sp db.P (parts sp al db tr).c (k + 1)).mergeSort
      (fun a b => decide (lev db.P b ≤ lev db.P a))).foldl
        (HMem.reachOnPath sp S0 db.S db.P (k + 1) (pathOf sp db.P (parts sp al db tr).c (k + 1))) m1).applyChange
        sp db.P (k + 1) (parts sp al db tr).c).obj?
      ((((pathOf sp db.P (parts sp al db tr).c (k + 1)).mergeSort
      (fun a b => decide (lev db.P b ≤ lev db.P a))).foldl
        (HMem.reachOnPath sp S0 db.S db.P (k + 1) (pathOf sp db.P (parts sp al db tr).c (k + 1))) m1).applyChange
        sp db.P (k + 1) (parts sp al db tr).c).root = some o → ∀ y p, o.ptr? y = some p →
      y ∈ pointees sp o.hist → (y ∈ pathOf sp db.P (parts sp al db tr).c (k + 1) ∨
        y ∈ (parts sp al db tr).c.new.map (·.id)) →
      ((((pathOf sp db.P (parts sp al db tr).c (k + 1)).mergeSort
      (fun a b => decide (lev db.P b ≤ lev db.P a))).foldl
        (HMem.reachOnPath sp S0 db.S db.P (k + 1) (pathOf sp db.P (parts sp al db tr).c (k + 1))) m1).applyChange
        sp db.P (k + 1) (parts sp al db tr).c).holdsCanonical p = true :=
    fun hv o ho y p hp hyp hy => hm2.rootPtrs_change hinv hls hstep hv hpr hpn hpd ho hp hyp hy
  have hpre : preWriteH sp S0 db (parts sp al db tr).c m1 =
      (((pathOf sp db.P (parts sp al db tr).c (k + 1)).mergeSort (fun a b => decide (lev db.P b ≤ lev db.P a))).foldl
        (HMem.reachOnPath sp S0 db.S db.P (k + 1) (pathOf sp db.P (parts sp al db tr).c (k + 1))) m1).applyChange
        sp db.P (k + 1) (parts sp al db tr).c := by
    unfold preWriteH; rw [hlen]; rfl
  rw [hpre, hlen]
  generalize (((pathOf sp db.P (parts sp al db tr).c (k + 1)).mergeSort
    (fun a b => decide (lev db.P b ≤ lev db.P a))).foldl
      (HMem.reachOnPath sp S0 db.S db.P (k + 1) (pathOf sp db.P (parts sp al db tr).c (k + 1))) m1).applyChange
      sp db.P (k + 1) (parts sp al db tr).c = m3 at ha hc3 hroot3 ⊢
  -- The writes.
  obtain ⟨e1, -, -, -⟩ := ha.loops_vs hsp hinv hmk hstep hinv'
  have hdata : ((parts sp al db tr).c.new.filter (·.isData)).map (·.id) = dataIds sp al db tr := rfl
  rw [hdata, e1, ← parts_D1Of, ← parts_takenOf]
  have hdnd : (dataIds sp al db tr).Nodup := (List.Sublist.map _ List.filter_sublist).nodup hstep.distinct
  have hdisj : ∀ x ∈ dataIds sp al db tr, x ∉ (parts sp al db tr).taken := by
    intro x hx hxt
    obtain ⟨d, hxd, -⟩ := step_taken_inD (al := al) (tr := tr) hinv hxt
    obtain ⟨hnone, -⟩ := step_dataIds_spec sp al db tr hinv hstep hx
    have := hinv.dIndex (x, d) hxd
    simp [isIndex, hnone] at this
  have hfr := loopsFrameH sp S0 db.D (parts sp al db tr).D1 (k + 1) (dataIds sp al db tr)
    (parts sp al db tr).taken m3 hdnd (step_taken_nodup sp al db tr hinv) ha.tbl hdisj
  exact CInvH.next hsp hinv hmk hstep hinv' ha hc3 hroot3 hfr

end Next

end SIS
