/-
Proofs for stage 2 (bergdb item 001, WP E3), part 14: the Level 4 startup from
R(0) gives a memory with the invariant (`einv_init`), so T-CACHE holds for every
run with eviction and no restart (`TC_run_init`); and the invariant in the terms
of T-CACHE's statement (`EInv.tc_facts`).
-/
import SIS.Proof.EvictRun

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

theorem Mem.linkD_table (m : Mem V) (D : Dirty) : (m.linkD D).table = m.table := rfl

theorem Mem.linkD_keys (m : Mem V) (D : Dirty) : (m.linkD D).objs.map (·.1) = m.objs.map (·.1) := by
  unfold Mem.linkD
  simp only [List.map_map]
  apply List.map_congr_left
  intro p _
  simp only [Function.comp]
  split <;> rfl

/-- The invariant survives a change of slots into memory slots to the pointees'
canonical objects, the objects' cores, the node table and the rest staying. -/
theorem EInv.relink {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m m' : Mem V}
    (hm : EInv sp db S0 k m) (hfw : ∀ h o, m.obj? h = some o → ∃ o', m'.obj? h = some o')
    (hbk : ∀ h o', m'.obj? h = some o' → ∃ o, m.obj? h = some o ∧ o'.core = o.core ∧
      ∀ y, o'.slot? y = o.slot? y ∨ ∃ sl h0, o.slot? y = some sl ∧ o'.slot? y = some (Slot.mem h0) ∧
        m.canonicalOf y = some h0)
    (htab : m'.table = m.table) (hs : m'.s = m.s) (hroot : m'.root = m.root) (hnext : m'.next = m.next)
    (hnd : (m'.objs.map (·.1)).Nodup) : EInv sp db S0 k m' := by
  -- The cores, and the canonical objects, are m's.
  have hcore : ∀ h, (m'.obj? h).map Obj.core = (m.obj? h).map Obj.core := by
    intro h
    cases ho' : m'.obj? h with
    | none =>
      cases ho : m.obj? h with
      | none => rfl
      | some o => obtain ⟨o', ho''⟩ := hfw h o ho; rw [ho'] at ho''; cases ho''
    | some o' =>
      obtain ⟨o, ho, hc, -⟩ := hbk h o' ho'
      rw [ho]; simp [hc]
  have htabOf : ∀ y, m'.tableOf y = m.tableOf y := by intro y; unfold Mem.tableOf; rw [htab]
  have hcan : ∀ y, m'.canonicalOf y = m.canonicalOf y := by
    intro y
    unfold Mem.canonicalOf
    rw [htabOf]
    cases m.tableOf y with
    | none => rfl
    | some h =>
      simp only
      have := hcore h
      cases ho : m.obj? h with
      | none =>
        cases ho' : m'.obj? h with
        | none => rfl
        | some o' => rw [ho, ho'] at this; cases this
      | some o =>
        cases ho' : m'.obj? h with
        | none => rw [ho, ho'] at this; cases this
        | some o' =>
          rw [ho, ho'] at this
          simp only [Option.map_some, Option.some.injEq] at this
          have : o'.canonical = o.canonical := congrArg (fun c => c.2.2.2.2.1) this
          simp only [this]
  have hce : m.CoreEq m' := ⟨hcore, hcan, hs⟩
  -- The slots of m' that differ name canonical objects, at the latest version.
  have hnew : ∀ {h0 : Nat} {y : NodeId} {o : Obj V}, m.canonicalOf y = some h0 →
      (SlotInv S0 db m' o y (Slot.mem h0) ∧ LiveInv S0 db m' y (Slot.mem h0)) ∧
        ∃ o0, m'.obj? h0 = some o0 ∧ o0.node = y ∧ o0.canonical = true := by
    intro h0 y o hc
    obtain ⟨o0, ho0, hc0, hn0⟩ := hm.obj_of_canonicalOf hc
    have hpos := hm.pos.lv0 hc ho0
    obtain ⟨o0', ho0', e1, -, -, -, e5, e6⟩ := hce.obj ho0
    have hc' : m'.canonicalOf y = some h0 := by rw [hcan]; exact hc
    refine ⟨⟨⟨fun _ => ?_, fun _ => Or.inl ⟨h0, rfl, hc'⟩⟩, fun _ => ⟨h0, rfl, hc'⟩, fun _ => ?_⟩,
      o0', ho0', by rw [e1, hn0], by rw [e5, hc0]⟩
    · simp only [slotRefOf, ho0', Option.bind_some]; rw [e6]; exact hpos
    · simp only [slotRefOf, ho0', Option.bind_some]; rw [e6]; exact hpos
  have hbk' : ∀ h o', m'.obj? h = some o' → ∃ o, m.obj? h = some o ∧ o'.node = o.node ∧
      o'.level = o.level ∧ o'.isData = o.isData ∧ o'.hist = o.hist ∧ o'.canonical = o.canonical ∧
      o'.pos = o.pos ∧ ∀ y, o'.slot? y = o.slot? y ∨ ∃ sl h0, o.slot? y = some sl ∧
        o'.slot? y = some (Slot.mem h0) ∧ m.canonicalOf y = some h0 := by
    intro h o' ho'
    obtain ⟨o, ho, hc, hsl⟩ := hbk h o' ho'
    simp only [Obj.core, Prod.mk.injEq] at hc
    exact ⟨o, ho, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2, hsl⟩
  refine ⟨hm.len, hm.pre, by rw [hs]; exact hm.sEq, fun h hh => ?_, hnd, ?_, by rw [htab]; exact hm.tblNodup,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases ho' : m'.obj? h with
    | none => rfl
    | some o' =>
      obtain ⟨o, ho, -⟩ := hbk h o' ho'
      rw [hm.fresh h (by rw [← hnext]; exact hh)] at ho; cases ho
  · obtain ⟨o, ho, hc, hn⟩ := hm.root
    obtain ⟨o', ho', e1, -, -, -, e5, -⟩ := hce.obj ho
    exact ⟨o', by rw [hroot]; exact ho', by rw [e5, hc], by rw [e1, hn]⟩
  · intro y h ht
    rw [htabOf] at ht
    obtain ⟨o, ho, hn⟩ := hm.tbl y h ht
    obtain ⟨o', ho', e1, -⟩ := hce.obj ho
    exact ⟨o', ho', by rw [e1, hn]⟩
  · intro h o' ho' y h' hsl
    obtain ⟨o, ho, -, -, -, -, -, -, hsl'⟩ := hbk' h o' ho'
    rcases hsl' y with he | ⟨sl, h0, -, hs0, hc⟩
    · rw [he] at hsl
      obtain ⟨o2, ho2, hn2⟩ := hm.slotsNode h o ho y h' hsl
      obtain ⟨o2', ho2', e1, -⟩ := hce.obj ho2
      exact ⟨o2', ho2', by rw [e1, hn2]⟩
    · rw [hs0, Option.some.injEq, Slot.mem.injEq] at hsl
      subst hsl
      obtain ⟨-, o0, ho0, hn0, -⟩ := hnew (o := o) hc
      exact ⟨o0, ho0, hn0⟩
  · intro y h ht
    rw [htabOf] at ht
    obtain ⟨o, ho, hc⟩ := hm.tblCanon y h ht
    obtain ⟨o', ho', -, -, -, -, e5, -⟩ := hce.obj ho
    exact ⟨o', ho', by rw [e5, hc]⟩
  · intro h o' ho' hc
    obtain ⟨o, ho, e1, -, -, -, e5, -⟩ := hbk' h o' ho'
    rw [htabOf, e1]
    exact hm.canonTbl h o ho (by rw [← e5]; exact hc)
  · intro h o' ho' hc
    obtain ⟨o, ho, e1, e2, e3, e4, e5, -⟩ := hbk' h o' ho'
    rw [e1, e2, e3, e4]
    exact hm.cc h o ho (by rw [← e5]; exact hc)
  · intro z h o' hz ho'
    obtain ⟨o, ho, -, -, -, -, -, e6, -⟩ := hbk' h o' ho'
    rw [hcan] at hz
    rw [e6]
    exact hm.pos z h o hz ho
  · intro y hy
    rw [hcan]; exact hm.dCanon y hy
  · intro h o' ho' hc
    obtain ⟨o, ho, e1, e2, e3, e4, e5, e6, hsl⟩ := hbk' h o' ho'
    have hc0 : o.canonical = false := by rw [← e5]; exact hc
    obtain ⟨r, w, h1, h2, h3, h4, h5, h6, h7⟩ := hm.snap h o ho hc0
    refine ⟨r, w, by rw [e6]; exact h1, by rw [e1]; exact h2, by rw [e4]; exact h3, by rw [e2]; exact h4,
      by rw [e3]; exact h5, fun y hy => ?_, fun y sl hy => ?_⟩
    · rcases hsl y with he | ⟨sl, h0, -, hs0, -⟩
      · rw [he]; exact h6 y (by rw [← e4]; exact hy)
      · rw [hs0]; rfl
    · rcases hsl y with he | ⟨sl0, h0, -, hs0, hc'⟩
      · rw [he] at hy
        exact (h7 y sl hy).congr hce
      · rw [hs0, Option.some.injEq] at hy
        subst hy
        obtain ⟨-, o0, ho0, hn0, hc00⟩ := hnew (o := o) hc'
        exact Or.inr (Or.inr ⟨h0, o0, rfl, ho0, hn0, Or.inl hc00⟩)
  · intro h o' ho' hr y hy
    obtain ⟨o, ho, e1, -, -, e4, e5, -, hsl⟩ := hbk' h o' ho'
    obtain ⟨hrc, hrw, hrr⟩ := hr
    obtain ⟨sl, hsl0, hi⟩ := hm.slots h o ho ⟨by rw [← e5]; exact hrc, by rw [← e1]; exact hrw,
      by rw [← e1]; exact hrr⟩ y (by rw [← e4]; exact hy)
    rcases hsl y with he | ⟨sl', h0, -, hs0, hc'⟩
    · refine ⟨sl, by rw [he]; exact hsl0, ?_⟩
      have := hi.congr hce
      unfold SlotInv at this ⊢
      rw [e1]; exact this
    · exact ⟨Slot.mem h0, hs0, (hnew (o := o') hc').1.1⟩
  · intro h o' ho' hc hr y hy
    obtain ⟨o, ho, e1, -, -, e4, e5, -, hsl⟩ := hbk' h o' ho'
    obtain ⟨sl, hsl0, hi⟩ := hm.live h o ho (by rw [← e5]; exact hc) (by rw [← e1]; exact hr) y
      (by rw [← e4]; exact hy)
    rcases hsl y with he | ⟨sl', h0, -, hs0, hc'⟩
    · exact ⟨sl, by rw [he]; exact hsl0, hi.congr hce⟩
    · exact ⟨Slot.mem h0, hs0, (hnew (o := o') hc').1.2⟩

/-- Rule 4 keeps the invariant. -/
theorem EInv.linkD {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}
    (hm : EInv sp db S0 k m) (D : Dirty) : EInv sp db S0 k (m.linkD D) := by
  apply hm.relink
  · intro h o ho
    exact ⟨_, by rw [Mem.linkD_obj?, ho]; rfl⟩
  · intro h o' ho'
    rw [Mem.linkD_obj?] at ho'
    obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.mp ho'
    exact ⟨o, ho, linkObjD_core m D h o, linkObjD_slot m D h o⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rw [Mem.linkD_keys]; exact hm.objNodup

/-- The Level 4 startup from R(0) gives a memory with the invariant. -/
theorem einv_init (hsp : SpecOK sp) : EInv sp (init sp) (init sp).S 0 (evictStartup sp (init sp).S) := by
  have h0 := einv_lazyBase hsp
  have he : evictStartup sp (init sp).S =
      ((lazyBase sp (init sp).S).sectionPos (init sp).S).linkD (init sp).D := by
    unfold evictStartup
    rw [init_lazyStartup, init_startup_D]; rfl
  rw [he]
  have hs : (lazyBase sp (init sp).S).Same ((lazyBase sp (init sp).S).sectionPos (init sp).S) := by
    apply Mem.sectionPos_same
    intro h o ho hc w hw
    rw [h0.sEq, init_lastSp, init_newest] at hw
    rw [h0.pos.lv0 (h0.canonicalOf_of ho hc) ho, hw]
    rfl
  exact (h0.same hs h0.tblNodup (by rw [Mem.sectionPos_keys]; exact h0.objNodup)).linkD _

end Init

/-! ## The invariant in the terms of T-CACHE's statement -/

section Facts

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

/-- What the invariant gives, in the terms of `TC_records`: INV-CAN (the node
table's canonical object, CC, the latest position; every node of D has one),
INV-SNAP, no dangling slot, and INV-SLOT (a relevant object has a slot for
each pointee, the writer would give it the pointee's latest version, and its
second half). -/
theorem EInv.tc_facts (hm : EInv sp db S0 k m) :
    (∀ h o, m.obj? h = some o → o.canonical = true →
      m.canonicalOf o.node = some h ∧
      (∃ n, db.P.get? o.node = some n ∧ o.hist = n.hist ∧ o.level = n.level ∧ o.isData = n.isData) ∧
      o.pos = (db.S.lv o.node).map (·.recNo)) ∧
    (∀ y, inD db.D y = true → (m.canonicalOf y).isSome) ∧
    (∀ h o, m.obj? h = some o → o.canonical = false → ∃ r w, o.pos = some r ∧
      db.S.versionAt r o.node = some w ∧ o.hist = w.hist ∧ o.level = w.level ∧ o.isData = w.isData) ∧
    (∀ h o y h', m.obj? h = some o → o.slot? y = some (Slot.mem h') →
      ∃ o', m.obj? h' = some o' ∧ o'.node = y) ∧
    (∀ h o, m.obj? h = some o → o.canonical = true → written sp o.node = true →
      (reachable sp db.P k o.node = true ∨ inD db.D o.node = true) →
      ∀ y ∈ pointees sp o.hist, (o.slot? y).isSome ∧
        m.refOf S0 db.D o y = (db.S.lv y).map (·.recNo) ∧
        (inD db.D y = true → (∃ h', o.slot? y = some (Slot.mem h') ∧ m.canonicalOf y = some h') ∨
          (inD db.D o.node = true ∧ ∃ a b, (o.node, a) ∈ db.D ∧ (y, b) ∈ db.D ∧ a ≤ b))) := by
  refine ⟨fun h o ho hc => ⟨hm.canonicalOf_of ho hc, hm.cc h o ho hc,
      hm.pos.lv0 (hm.canonicalOf_of ho hc) ho⟩, hm.dCanon, ?_,
      fun h o y h' ho hsl => hm.slotsNode h o ho y h' hsl, ?_⟩
  · intro h o ho hc
    obtain ⟨r, w, hp, hv, hh, hl, hd, -, -⟩ := hm.snap h o ho hc
    exact ⟨r, w, hp, hv, hh, hl, hd⟩
  · intro h o ho hc hw hr y hy
    obtain ⟨sl, hsl, hi1, hi2⟩ := hm.slots h o ho ⟨hc, hw, hr⟩ y hy
    refine ⟨by rw [hsl]; rfl, ?_, ?_⟩
    · rw [Mem.refOf_eq]
      cases hD : inD db.D y with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [Mem.slotRef_eq, hsl, Option.bind_some]
        exact hi1 hD
      | true =>
        simp only [↓reduceIte]
        obtain ⟨h0, hc0⟩ := Option.isSome_iff_exists.mp (hm.dCanon y hD)
        rw [hc0]
        obtain ⟨o0, ho0, -, -⟩ := hm.obj_of_canonicalOf hc0
        simp only
        rw [ho0, Option.bind_some, hm.pos.lv0 hc0 ho0]
    · intro hD
      rcases hi2 hD with ⟨h', rfl, hc'⟩ | ⟨hx, a, b, ha, hb, hab⟩
      · exact Or.inl ⟨h', hsl, hc'⟩
      · exact Or.inr ⟨hx, a, b, mem_of_dOf ha, mem_of_dOf hb, hab⟩

end Facts

/-- T-CACHE, the strong form: `TC_run` from the Level 4 startup from R(0). -/
theorem TC_run_init {sp : Spec V T} {al : Algo V T} {ts : List (T × Bool × List CacheOp)}
    (hok : RunOK sp al (ts.map (·.1))) (hph : PhysRunOK sp al (ts.map (·.1)))
    (hev : EvictRunOK sp al (ts.map (·.1))) (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true)
    (hnr : ∀ p ∈ ts, p.2.1 = false) :
    ∀ j ≤ ts.length, (runEvict sp al (ts.take j)).1 = st sp al (ts.map (·.1)) j ∧
      (runEvict sp al (ts.take j)).2.2 = (init sp).S ∧
      EInv sp (st sp al (ts.map (·.1)) j) (init sp).S j (runEvict sp al (ts.take j)).2.1 :=
  TC_run hok hph hev hj hmk hnr (einv_init hok.1)

end SIS
