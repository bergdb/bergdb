/-
Proofs for stage 2 (bergdb item 001, WP E3), part 14: the Level 4 startup from
R(0) gives a memory with the invariant (`einv_init`), so T-CACHE holds for every
run with eviction and no restart (`TC_run_init`); and the invariant in the terms
of T-CACHE's statement (`EInv.tc_facts`).
-/
import SIS.Proof.EvictTrans

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

section Init

variable {sp : Spec V T}

theorem init_S_length (sp : Spec V T) : (init sp).S.length = 1 := rfl

theorem init_lastSp (sp : Spec V T) : lastSp (init sp).S = 0 := rfl

/-- In R(0) every version is its node's latest. -/
theorem init_versionAt_lv {r : Nat} {y : NodeId} {w : Version V} (h : (init sp).S.versionAt r y = some w) :
    r = 0 ∧ (init sp).S.lv y = some w := by
  have hr : r = 0 := by
    obtain ⟨R, hR, -, -⟩ := versionAt_spec h
    have := (List.getElem?_eq_some_iff.mp hR).1
    rw [init_S_length] at this; omega
  subst hr
  refine ⟨rfl, ?_⟩
  obtain ⟨r', u', h1, h2, h3⟩ := lv_recNo_ge h
  have hr' : r' = 0 := by
    obtain ⟨R, hR, -, -⟩ := versionAt_spec h1
    have := (List.getElem?_eq_some_iff.mp hR).1
    rw [init_S_length] at this; omega
  subst hr'
  rw [h, Option.some.injEq] at h1
  rw [h2, h1]

/-- Rule R at R(0) on a reference to a version, or on a missing one of a node
without a version: the latest version. -/
theorem init_ruleR (hsp : SpecOK sp) {y : NodeId} {r : Option Nat}
    (hr : ∀ r', r = some r' → ∃ u, (init sp).S.versionAt r' y = some u) :
    ruleRRef (init sp).S 0 y r = ((init sp).S.lv y).map (·.recNo) := by
  unfold ruleRRef
  have hn : newest (init sp).S 0 y = (init sp).S.lv y := by rw [newest_eq]; rfl
  rw [hn]
  cases hl : (init sp).S.lv y with
  | none =>
    simp only [Option.map_none]
    cases r with
    | none => rfl
    | some r' =>
      exfalso
      obtain ⟨u, hu⟩ := hr r' rfl
      rw [(init_versionAt_lv hu).2] at hl; cases hl
  | some v =>
    simp only [Option.map_some]
    cases r with
    | none => rfl
    | some r' =>
      obtain ⟨u, hu⟩ := hr r' rfl
      obtain ⟨-, hlu⟩ := init_versionAt_lv hu
      rw [hl, Option.some.injEq] at hlu
      obtain ⟨-, hrec, -⟩ := (inv_init sp hsp).version_node hu
      have hvr : v.recNo = r' := by rw [hlu]; exact hrec
      simp [hvr]

theorem init_sectionIdx (sp : Spec V T) : sectionIdx (init sp).S (lastSp (init sp).S) = [] := rfl

theorem init_lazyStartup (sp : Spec V T) : lazyStartup sp (init sp).S = lazyBase sp (init sp).S := by
  rw [lazyStartup_eq, init_sectionIdx]; rfl

theorem init_startup_D (sp : Spec V T) : (startup sp (init sp).S).D = [] := rfl

theorem secStep_tblNodup (sp : Spec V T) (S : Stream V T) (m : Mem V) (x : NodeId)
    (h : (m.table.map (·.1)).Nodup) : ((secStep sp S m x).table.map (·.1)).Nodup := by
  unfold secStep
  split
  · split
    · exact h
    · exact setTable_nodup _ _ _ h
  · exact h

theorem lazySec_tblNodup (sp : Spec V T) (S : Stream V T) : ((lazySec sp S).table.map (·.1)).Nodup := by
  unfold lazySec
  have key : ∀ (L : List NodeId) (m : Mem V), (m.table.map (·.1)).Nodup →
      ((L.foldl (secStep sp S) m).table.map (·.1)).Nodup := by
    intro L
    induction L with
    | nil => intro m h; exact h
    | cons x L ih => intro m h; exact ih _ (secStep_tblNodup sp S m x h)
  exact key _ _ List.nodup_nil

theorem lazyRoot_tblNodup (sp : Spec V T) (S : Stream V T) (m1 : Mem V) (h : (m1.table.map (·.1)).Nodup) :
    ((lazyRoot sp S m1).table.map (·.1)).Nodup := by
  unfold lazyRoot
  by_cases hv : sp.virt = true
  · simp only [hv, ↓reduceIte]
    exact setTable_nodup _ _ _ h
  · simp only [hv, Bool.false_eq_true, ↓reduceIte]
    cases hc : m1.canonicalOf root with
    | some h0 => exact h
    | none =>
      simp only
      cases ht : topVersion S (lastSp S) true with
      | none => exact h
      | some w => exact setTable_nodup _ _ _ h

/-- `sectionPos` changes no lookup when every canonical object is at its newest
version in the section already. -/
theorem Mem.sectionPos_same (m : Mem V) (S : Stream V T)
    (h : ∀ h o, m.obj? h = some o → o.canonical = true → ∀ w, newest S m.s o.node = some w →
      o.pos = some w.recNo) : m.Same (m.sectionPos S) := by
  have hobj : ∀ h', (m.sectionPos S).obj? h' = (m.obj? h').map (fun o =>
      if !o.canonical then o else match newest S m.s o.node with
        | some w => { o with pos := some w.recNo }
        | none => o) := by
    intro h'
    unfold Mem.sectionPos Mem.obj?
    simp only
    rw [lookup_map_key _ (fun q => by
      cases q.2.canonical
      · simp
      · cases newest S m.s q.2.node <;> simp) h' m.objs]
    congr 1
    funext o
    cases o.canonical
    · simp
    · cases newest S m.s o.node <;> simp
  refine ⟨fun h' => ?_, fun _ => rfl, rfl, rfl, rfl⟩
  rw [hobj]
  cases ho : m.obj? h' with
  | none => rfl
  | some o =>
    simp only [Option.map_some, Option.some.injEq]
    cases hc : o.canonical with
    | false => simp
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases hn : newest S m.s o.node with
      | none => rfl
      | some w =>
        have := h h' o ho hc w hn
        cases o; simp only at this hc; subst this hc; rfl

/-- The stage 1 contexts of the run with no transaction. -/
def al0 (sp : Spec V T) : Algo V T := { policy := fun _ _ i _ => i - 1, stillDirty := javaTest sp, mark := true }

theorem runOK_nil (hsp : SpecOK sp) : RunOK sp (al0 sp) ([] : List T) := ⟨hsp, fun j h => absurd h (by simp)⟩

theorem init_newest (sp : Spec V T) (y : NodeId) : newest (init sp).S 0 y = (init sp).S.lv y := by
  rw [newest_eq]; rfl

theorem init_inD (sp : Spec V T) (y : NodeId) : inD (init sp).D y = false := rfl

theorem Mem.sectionPos_keys (m : Mem V) (S : Stream V T) :
    (m.sectionPos S).objs.map (·.1) = m.objs.map (·.1) := by
  unfold Mem.sectionPos
  simp only [List.map_map]
  apply List.map_congr_left
  intro p _
  simp only [Function.comp]
  cases p.2.canonical
  · simp
  · cases newest S m.s p.2.node <;> simp

theorem rootVersion_times (sp : Spec V T) (s : Nat) (ws : List (Version V)) :
    ∀ e ∈ (rootVersion sp s ws).hist, e.time ≤ s := by
  intro e he
  simp only [rootVersion, List.mem_filterMap, List.mem_range] at he
  obtain ⟨t, ht, hf⟩ := he
  obtain ⟨w, -, hw⟩ := Option.map_eq_some_iff.mp hf
  rw [← hw]
  show t ≤ s
  omega

theorem lookup_refs_some {ws : List (Version V)} {y : NodeId} {r : Nat}
    (h : List.lookup y (ws.map (fun w => (w.node, w.recNo))) = some r) :
    ∃ w ∈ ws, w.node = y ∧ w.recNo = r := by
  induction ws with
  | nil => simp at h
  | cons a ws ih =>
    simp only [List.map_cons, List.lookup_cons] at h
    by_cases ha : a.node = y
    · have hb : (y == a.node) = true := by simp [ha]
      simp only [hb, Option.some.injEq] at h
      exact ⟨a, List.mem_cons_self, ha, h⟩
    · have hb : (y == a.node) = false := by simp; exact fun h => ha h.symm
      simp only [hb] at h
      obtain ⟨w, hw, h1, h2⟩ := ih h
      exact ⟨w, List.mem_cons_of_mem _ hw, h1, h2⟩

/-- A stream slot to a version that `linkCanonical` changes becomes a memory
slot to an object at that version. -/
theorem linkQ_some (m : Mem V) (y : NodeId) (r : Nat) :
    (linkQ m (y, Slot.stream (some r))).2 = Slot.stream (some r) ∨
      ∃ h0 o0, m.obj? h0 = some o0 ∧ o0.pos = some r ∧
        (linkQ m (y, Slot.stream (some r))).2 = Slot.mem h0 := by
  unfold linkQ
  simp only
  split
  · rename_i h0 ht
    split
    · rename_i o0 ho
      split
      · rename_i hc
        right
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        exact ⟨h0, o0, ho, hc.2, rfl⟩
      · left; rfl
    · left; rfl
  · left; rfl

theorem canonOfVersion_slot_eq {sp : Spec V T} {S : Stream V T} {s : Nat} {w : Version V} {y : NodeId}
    {sl : Slot} (h : (canonOfVersion sp S s w).slot? y = some sl) :
    sl = Slot.stream (ruleRRef S s y (w.ref? y)) := by
  rw [canonOfVersion_slot?] at h
  by_cases hy : y ∈ pointees sp (cutHist w (if isKeyLevel sp w.isData w.level then some s else none))
  · simp only [hy, ↓reduceIte, Option.some.injEq] at h
    exact h.symm
  · simp only [hy, ↓reduceIte] at h
    cases h

/-- At R(0), every object of the startup's memory before the memory slots has
a slot for each pointee of its history, and each of its slots is a stream slot
to the pointee's latest version. -/
theorem init_base_slot (hsp : SpecOK sp) {h : Nat} {o : Obj V}
    (ho : (lazyRoot sp (init sp).S (lazySec sp (init sp).S)).obj? h = some o) :
    (∀ y ∈ pointees sp o.hist, (o.slot? y).isSome) ∧
    ∀ y sl, o.slot? y = some sl → sl = Slot.stream (((init sp).S.lv y).map (·.recNo)) := by
  have hinv := inv_init sp hsp
  have hb := hinv.base2 (sp := sp)
  obtain ⟨-, -, hsrc⟩ := hb.obj h o ho
  rcases hsrc with ⟨w, r, hw, -, hoe, -⟩ | ⟨hv, hoe⟩ | ⟨-, u, -, hus, -, -⟩
  · subst hoe
    refine ⟨fun y hy => ?_, fun y sl hsl => ?_⟩
    · rw [(canonOfVersion_fields sp _ _ w).2.2.2.1] at hy
      rw [canonOfVersion_slot?]
      simp [hy]
    · rw [canonOfVersion_slot_eq hsl, init_lastSp, init_ruleR hsp (fun r' h' => hinv.ref_versionAt hw h')]
  · subst hoe
    have hcut : cutHist (rootVersion sp (lastSp (init sp).S) (topsRead sp (init sp).S (lastSp (init sp).S) true))
        (if isKeyLevel sp (rootVersion sp (lastSp (init sp).S) (topsRead sp (init sp).S (lastSp (init sp).S) true)).isData
          (rootVersion sp (lastSp (init sp).S) (topsRead sp (init sp).S (lastSp (init sp).S) true)).level
          then some (lastSp (init sp).S) else none) =
        (rootVersion sp (lastSp (init sp).S) (topsRead sp (init sp).S (lastSp (init sp).S) true)).hist := by
      split
      · exact upTo_of_forall _ _ (rootVersion_times sp _ _)
      · rfl
    refine ⟨fun y hy => ?_, fun y sl hsl => ?_⟩
    · show ((canonOfVersion sp (init sp).S (lastSp (init sp).S) _).slot? y).isSome
      rw [canonOfVersion_slot?, hcut]
      have hy' : y ∈ pointees sp (rootVersion sp (lastSp (init sp).S)
          (topsRead sp (init sp).S (lastSp (init sp).S) true)).hist := hy
      simp [hy']
    · have hsl' : (canonOfVersion sp (init sp).S (lastSp (init sp).S)
          (rootVersion sp (lastSp (init sp).S) (topsRead sp (init sp).S (lastSp (init sp).S) true))).slot? y =
          some sl := hsl
      have hr : ∀ r', (rootVersion sp (lastSp (init sp).S)
          (topsRead sp (init sp).S (lastSp (init sp).S) true)).ref? y = some r' →
          ∃ u, (init sp).S.versionAt r' y = some u := by
        intro r' hr'
        obtain ⟨w, hw, hwy, hwr⟩ := lookup_refs_some hr'
        obtain ⟨-, -, -, -, hlv⟩ := (hinv.topsRead_spec hv).1 w hw
        rw [← hwr, ← hwy]
        exact ⟨w, hinv.lv_at hlv⟩
      rw [canonOfVersion_slot_eq hsl']
      generalize (rootVersion sp (lastSp (init sp).S)
        (topsRead sp (init sp).S (lastSp (init sp).S) true)).ref? y = rr at hr ⊢
      rw [init_lastSp, init_ruleR hsp hr]
  · rw [init_lastSp] at hus
    omega

/-- At R(0), each pointee of an object of the memory before the rerun has a
slot that serializes its latest version. -/
theorem init_lazyBase_slot (hsp : SpecOK sp) {h : Nat} {o : Obj V}
    (ho : (lazyBase sp (init sp).S).obj? h = some o) {y : NodeId} (hy : y ∈ pointees sp o.hist) :
    ∃ sl, o.slot? y = some sl ∧
      slotRefOf (init sp).S (lazyBase sp (init sp).S) y sl = ((init sp).S.lv y).map (·.recNo) := by
  have hinv := inv_init sp hsp
  have hb := hinv.base2 (sp := sp)
  unfold lazyBase at ho ⊢
  rw [linkCanonical_obj?] at ho
  obtain ⟨o2, ho2, rfl⟩ := Option.map_eq_some_iff.mp ho
  obtain ⟨-, hc2, -⟩ := hb.obj h o2 ho2
  obtain ⟨hex, hval⟩ := init_base_slot hsp ho2
  rw [(linkObj_fields _ o2).2.2.2.1] at hy
  obtain ⟨sl2, hsl2⟩ := Option.isSome_iff_exists.mp (hex y hy)
  have hsl2' := hval y sl2 hsl2
  subst hsl2'
  rw [linkObj_slot? _ hc2, hsl2, Option.map_some]
  refine ⟨_, rfl, ?_⟩
  have hs : (lazyRoot sp (init sp).S (lazySec sp (init sp).S)).linkCanonical.s = 0 := by
    rw [linkCanonical_s, hb.s, init_lastSp]
  cases hl : (init sp).S.lv y with
  | none =>
    show ruleRRef (init sp).S (lazyRoot sp (init sp).S (lazySec sp (init sp).S)).linkCanonical.s y none = _
    rw [hs, init_ruleR hsp (fun r' h' => by cases h'), hl]
  | some v =>
    simp only [Option.map_some]
    rcases linkQ_some (lazyRoot sp (init sp).S (lazySec sp (init sp).S)) y v.recNo with he | ⟨h0, o0, ho0, hp0, he⟩
    · rw [he]
      show ruleRRef (init sp).S (lazyRoot sp (init sp).S (lazySec sp (init sp).S)).linkCanonical.s y
        (some v.recNo) = _
      rw [hs, init_ruleR hsp (fun r' h' => by cases h'; exact ⟨v, hinv.lv_at hl⟩), hl]
      rfl
    · rw [he]
      show ((lazyRoot sp (init sp).S (lazySec sp (init sp).S)).linkCanonical.obj? h0).bind (·.pos) = _
      rw [linkCanonical_obj?, ho0]
      show (linkObj _ o0).pos = _
      rw [(linkObj_fields _ o0).2.2.2.2.2, hp0]

/-- The memory before the rerun, at R(0), has the invariant. -/
theorem einv_lazyBase (hsp : SpecOK sp) : EInv sp (init sp) (init sp).S 0 (lazyBase sp (init sp).S) := by
  have hinv := inv_init sp hsp
  have hb := hinv.base2 (sp := sp)
  have hls : LiveSub sp := hsp.liveSub
  have hst : AlgOK sp (al0 sp) := algOK_of sp (al0 sp) (Or.inl rfl)
  have hctx : PCtx sp (init sp) 0 := by
    have := pctx_st (runOK_nil hsp) hst (k := 0) (Nat.zero_le _)
    rwa [st_zero] at this
  have hk : KCtx sp (init sp) (init sp) (lastSp (init sp).S) := by
    have := kctx_st sp (al0 sp) [] (runOK_nil hsp) (rfl : (al0 sp).stillDirty = javaTest sp) (Nat.le_refl 0)
      (Nat.zero_le _)
    rw [st_zero] at this
    rw [init_lastSp]; exact this
  have hm := hctx.base_ok hk
  rw [init_lastSp] at hm
  have hall : ∀ h o, (lazyBase sp (init sp).S).obj? h = some o → o.canonical = true := by
    intro h o ho
    unfold lazyBase at ho
    rw [linkCanonical_obj?] at ho
    obtain ⟨o2, ho2, rfl⟩ := Option.map_eq_some_iff.mp ho
    rw [(linkObj_fields _ o2).2.2.2.2.1]
    exact (hb.obj h o2 ho2).2.1
  refine ⟨init_S_length sp, List.prefix_refl _, hm.sEq, hm.fresh, hm.nodup, hm.root.2, ?_, hm.tbl, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact lazyRoot_tblNodup sp _ _ (lazySec_tblNodup sp _)
  · intro h o ho y h' hsl
    obtain ⟨o', ho', hn', -⟩ := hm.memSlot h o y h' ho hsl
    exact ⟨o', ho', hn'⟩
  · intro y h ht
    obtain ⟨o, ho, -⟩ := hm.tbl y h ht
    exact ⟨o, ho, hall h o ho⟩
  · intro h o ho hc
    exact (hm.canon h o ho hc).1
  · intro h o ho hc
    obtain ⟨n, hn, hh, hl, hd⟩ := (hm.canon h o ho hc).2.1
    refine ⟨n, hn, ?_, hl, hd⟩
    rw [hh]
    exact upTo_of_forall _ _ (hinv.times _ n hn)
  · intro z h o hz ho
    rw [lv_building]
    simp only [List.find?_nil, Option.none_or]
    have hzn : o.node = z := by
      obtain ⟨ht, -⟩ := (Mem.canonicalOf_eq_some _ z h).mp hz
      obtain ⟨o', ho', hn'⟩ := hm.tbl z h ht
      rw [ho, Option.some.injEq] at ho'
      rw [ho']; exact hn'
    rw [← hzn]
    unfold lazyBase at ho
    rw [linkCanonical_obj?] at ho
    obtain ⟨o2, ho2, rfl⟩ := Option.map_eq_some_iff.mp ho
    rw [(linkObj_fields _ o2).2.2.2.2.2, (linkObj_fields _ o2).1]
    obtain ⟨-, -, hsrc⟩ := hb.obj h o2 ho2
    rcases hsrc with ⟨w, r, hw, -, hoe, -⟩ | ⟨hv, hoe⟩ | ⟨-, u, -, hus, -, -⟩
    · subst hoe
      rw [(canonOfVersion_fields sp _ _ w).2.2.2.2.2, (init_versionAt_lv hw).2]
      rfl
    · subst hoe
      show none = ((init sp).S.lv SIS.root).map (·.recNo)
      cases hl : (init sp).S.lv SIS.root with
      | none => rfl
      | some v =>
        exfalso
        obtain ⟨r, hr⟩ := lv_versionAt hl
        obtain ⟨R, hR, hvR, hvn⟩ := versionAt_spec hr
        exact (hinv.vr hv).rootNV r R hR v hvR hvn
    · rw [init_lastSp] at hus
      omega
  · intro y hy
    rw [init_inD] at hy; cases hy
  · intro h o ho hc
    rw [hall h o ho] at hc; cases hc
  · intro h o ho _ y hy
    obtain ⟨sl, hsl, href⟩ := init_lazyBase_slot hsp ho hy
    refine ⟨sl, hsl, ?_⟩
    unfold SlotInv
    exact ⟨fun _ => href, fun hD => by rw [init_inD] at hD; cases hD⟩
  · intro h o ho _ _ y hy
    obtain ⟨sl, hsl, href⟩ := init_lazyBase_slot hsp ho (mem_pointees_of_live' hls hy)
    refine ⟨sl, hsl, ?_⟩
    unfold LiveInv
    exact ⟨fun hD => absurd hD (by rw [init_inD]; simp), fun _ => href⟩

/-! ### Rule 4 keeps the invariant -/

/-- A slot as rule 4 leaves it: a stream slot to a node with a canonical object
becomes a memory slot to it. -/
def linkSlot (m : Mem V) (q : NodeId × Slot) : NodeId × Slot :=
  match q.2 with
  | Slot.stream _ => match m.canonicalOf q.1 with
    | some h0 => (q.1, Slot.mem h0)
    | none => q
  | _ => q

/-- Object o at handle h as rule 4 leaves it. -/
def linkObjD (m : Mem V) (D : Dirty) (h : Nat) (o : Obj V) : Obj V :=
  if !(o.canonical && (inD D o.node || h == m.root)) then o else { o with slots := o.slots.map (linkSlot m) }

theorem Mem.linkD_obj? (m : Mem V) (D : Dirty) (h : Nat) :
    (m.linkD D).obj? h = (m.obj? h).map (linkObjD m D h) := by
  have hf : (m.linkD D).objs = m.objs.map (fun p => (p.1, linkObjD m D p.1 p.2)) := by
    unfold Mem.linkD linkObjD
    apply List.map_congr_left
    intro p _
    cases (!(p.2.canonical && (inD D p.2.node || p.1 == m.root)))
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rfl
    · simp only [↓reduceIte]
  unfold Mem.obj?
  rw [hf]
  exact lookup_map_key (fun p => (p.1, linkObjD m D p.1 p.2)) (fun _ => rfl) h m.objs

theorem linkSlot_fst (m : Mem V) (q : NodeId × Slot) : (linkSlot m q).1 = q.1 := by
  unfold linkSlot
  split
  · split <;> rfl
  · rfl

theorem linkObjD_core (m : Mem V) (D : Dirty) (h : Nat) (o : Obj V) : (linkObjD m D h o).core = o.core := by
  unfold linkObjD
  split <;> rfl

theorem linkObjD_slot (m : Mem V) (D : Dirty) (h : Nat) (o : Obj V) (y : NodeId) :
    (linkObjD m D h o).slot? y = o.slot? y ∨
      ∃ sl h0, o.slot? y = some sl ∧ (linkObjD m D h o).slot? y = some (Slot.mem h0) ∧
        m.canonicalOf y = some h0 := by
  unfold linkObjD
  split
  · exact Or.inl rfl
  · unfold Obj.slot?
    simp only
    rw [lookup_map_key (linkSlot m) (linkSlot_fst m) y o.slots]
    cases hs : List.lookup y o.slots with
    | none => exact Or.inl rfl
    | some sl =>
      simp only [Option.map_some]
      unfold linkSlot
      simp only
      cases sl with
      | stream r =>
        simp only
        cases hc : m.canonicalOf y with
        | none => exact Or.inl rfl
        | some h0 => exact Or.inr ⟨_, h0, rfl, rfl, rfl⟩
      | mem h' => exact Or.inl rfl

theorem Mem.linkD_keys (m : Mem V) (D : Dirty) : (m.linkD D).objs.map (·.1) = m.objs.map (·.1) := by
  unfold Mem.linkD
  simp only [List.map_map]
  apply List.map_congr_left
  intro p _
  simp only [Function.comp]
  split <;> rfl

end Init

/-! ## The invariant in the terms of T-CACHE's statement -/

section Facts

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

end Facts

end SIS
