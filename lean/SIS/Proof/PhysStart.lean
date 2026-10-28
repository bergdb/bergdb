/-
Proofs about the lazy startup's memory (bergdb item 001, WP E5; bergdb 005-62,
for the startup with handles): the rerun of the startup from the stream after
T(k), before its positions and rule 4, keeps `RInv`:
every object is canonical; every stream slot names, after Rule R of the
stream's section, its pointee's latest version (a version of the section names
the latest version before it, which Rule R moves to the newest in the section;
a latest version written before the section, of a node current and clean in
it, names latest versions already); every memory slot names an object of its
pointee; every object has a slot for each pointee of its history. And the node
table has no repeated keys, and no object two slots for the same pointee
(`slotsND_lazyStartup`).
-/
import SIS.Proof.LogicFacts
import SIS.Proof.CutStream

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

section

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

theorem slot?_setSlot_of {o : Obj V} {y : NodeId} {sl0 : Slot} (h : o.slot? y = some sl0) (sl : Slot)
    (z : NodeId) : (o.setSlot y sl).slot? z = if z = y then some sl else o.slot? z := by
  rw [Obj.slot?_setSlot]
  split
  · rename_i hz; subst hz; rw [h]; rfl
  · rfl

end

/-- The slot of object hp for y names object h1. -/
def Mem.swz (m : Mem V) (hp : Nat) (y : NodeId) (h1 : Nat) : Mem V :=
  match m.obj? hp with
  | some op => m.setObj hp (op.setSlot y (Slot.mem h1))
  | none => m

section

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

theorem setTable_nodup (m : Mem V) (y : NodeId) (h : Nat) (hnd : (m.table.map (·.1)).Nodup) :
    ((m.setTable y h).table.map (·.1)).Nodup := by
  unfold Mem.setTable
  simp only [List.map_cons, List.nodup_cons]
  refine ⟨?_, (List.Sublist.map _ List.filter_sublist).nodup hnd⟩
  intro hm
  obtain ⟨p, hp, hpy⟩ := List.mem_map.mp hm
  have := (List.mem_filter.mp hp).2
  rw [hpy] at this
  simp at this

end

section

variable {sp : Spec V T}

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

theorem canonOfVersion_slot_eq {sp : Spec V T} {S : Stream V T} {s : Nat} {w : Version V} {y : NodeId}
    {sl : Slot} (h : (canonOfVersion sp S s w).slot? y = some sl) :
    sl = Slot.stream (ruleRRef S s y (w.ref? y)) := by
  rw [canonOfVersion_slot?] at h
  by_cases hy : y ∈ pointees sp (cutHist w (if isKeyLevel sp w.isData w.level then some s else none))
  · simp only [hy, ↓reduceIte, Option.some.injEq] at h
    exact h.symm
  · simp only [hy, ↓reduceIte] at h
    cases h

end

theorem Mem.sectionPos_obj? (m : Mem V) (S : Stream V T) (h : Nat) :
    (m.sectionPos S).obj? h = (m.obj? h).map (fun o =>
      if !o.canonical then o else match newest S m.s o.node with
        | some w => { o with pos := some w.recNo }
        | none => o) := by
  unfold Mem.sectionPos Mem.obj?
  simp only
  rw [lookup_map_key _ (fun q => by
    cases q.2.canonical
    · simp
    · cases newest S m.s q.2.node <;> simp) h m.objs]
  congr 1
  funext o
  cases o.canonical
  · simp
  · cases newest S m.s o.node <;> simp

section Fresh

variable {sp : Spec V T} {db : DB V T} {k : Nat}

/-- Rule R of the stream's own section takes a reference to a version of y to
y's latest version, if y has a version in the section; without one, it leaves
the reference, which must then name the latest version already. -/
theorem Inv.ruleR_eq_lv (hinv : Inv sp db k) (s : Nat) {y : NodeId} {ref : Option Nat}
    (hver : ∀ r'', ref = some r'' → ∃ u, db.S.versionAt r'' y = some u)
    (hnone : newest db.S s y = none → ref = (db.S.lv y).map (·.recNo)) :
    ruleRRef db.S s y ref = (db.S.lv y).map (·.recNo) := by
  unfold ruleRRef
  cases hn : newest db.S s y with
  | none => exact hnone hn
  | some u =>
    simp only
    rw [newest_lv hn, Option.map_some]
    cases ref with
    | none => rfl
    | some r'' =>
      simp only
      obtain ⟨u'', hu''⟩ := hver r'' rfl
      obtain ⟨v, hv, hle⟩ := hinv.le_lv hu''
      rw [newest_lv hn, Option.some.injEq] at hv
      subst hv
      by_cases hlt : r'' < u.recNo
      · simp [hlt]
      · simp only [hlt, ↓reduceIte, Option.some.injEq]; omega

end Fresh

section Run

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

/-- The stream after T(j) is the stream after T(k) cut after R(j). -/
theorem st_S_take (hok : RunOK sp al ts) (hst : AlgOK sp al) {j k : Nat} (hjk : j ≤ k) (hk : k ≤ ts.length) :
    (st sp al ts j).S = (st sp al ts k).S.take (j + 1) := by
  have hpre := st_S_prefix sp al ts hjk hk
  rw [← st_len sp al ts hok hst (j := j) (by omega)]
  exact (List.prefix_iff_eq_take.mp hpre)

/-- A node without a version in R(s), ..., R(k), the section of the stream after
T(k), that is current and not in D after T(j), for some j with s ≤ j ≤ k: its
latest version's reference for each pointee names, after Rule R, the pointee's
latest version (the latest version of a clean current node names the latest
versions of its pointees; none of them is written after s, or Rule R finds it). -/
theorem fresh_clean (hok : RunOK sp al ts) (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true)
    (hev : EvictRunOK sp al ts) {j k : Nat} (hjk : j ≤ k) (hk : k ≤ ts.length)
    (hsj : lastSp (st sp al ts k).S ≤ j) {x : NodeId}
    (hnew : newest (st sp al ts k).S (lastSp (st sp al ts k).S) x = none)
    (hr : reachable sp (st sp al ts j).P j x = true) (hxD : inD (st sp al ts j).D x = false)
    (hxw : written sp x = true) {v : Version V} (hv : (st sp al ts k).S.lv x = some v) :
    (∃ n, (st sp al ts j).P.get? x = some n ∧ v.hist = n.hist ∧ v.level = n.level ∧ v.isData = n.isData) ∧
    ∀ z ∈ pointees sp v.hist, ruleRRef (st sp al ts k).S (lastSp (st sp al ts k).S) z (v.ref? z) =
      ((st sp al ts k).S.lv z).map (·.recNo) := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hinvk := inv_st sp al ts hok hst k hk
  have hinvj := inv_st sp al ts hok hst j (by omega)
  have hlog := evLogic_st sp al ts hok hj hmk hev j (by omega)
  have htake := st_S_take hok hst hjk hk
  have hnone := (newest_eq_none_iff (st sp al ts k).S (lastSp (st sp al ts k).S) x).mp hnew
  -- After T(j), x's latest version is the same.
  have hvj : (st sp al ts j).S.lv x = some v := by
    rw [htake, lv_take (fun r' hr' => hnone r' (by omega))]; exact hv
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (Reach.isSome ((reachable_iff _ _ _ _).mp hr))
  obtain ⟨v', hv', hvh, hvl, hvd⟩ := hinvj.lv_whole hn hxw hxD hr
  rw [hvj, Option.some.injEq] at hv'
  subst hv'
  refine ⟨⟨n, hn, hvh, hvl, hvd⟩, fun z hz => ?_⟩
  have hz' : z ∈ pointees sp n.hist := by rw [← hvh]; exact hz
  obtain ⟨-, v'', hv'', href⟩ := hlog.clean x n hxw hr hn hxD z hz'
  rw [hvj, Option.some.injEq] at hv''
  subst hv''
  have hva := hinvk.lv_at hv
  apply hinvk.ruleR_eq_lv _ (fun r'' h => hinvk.ref_versionAt hva h)
  intro hzn
  rw [href, htake, lv_take (fun r' hr' => (newest_eq_none_iff _ _ z).mp hzn r' (by omega))]

/-- As `fresh_clean`, without Rule R: such a node's latest version names, for
each pointee, its latest version in the stream after T(j) (bergdb 005-58). -/
theorem clean_ref_lvAt (hok : RunOK sp al ts) (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true)
    (hev : EvictRunOK sp al ts) {j k : Nat} (hjk : j ≤ k) (hk : k ≤ ts.length)
    (hsj : lastSp (st sp al ts k).S ≤ j) {x : NodeId}
    (hnew : newest (st sp al ts k).S (lastSp (st sp al ts k).S) x = none)
    (hr : reachable sp (st sp al ts j).P j x = true) (hxD : inD (st sp al ts j).D x = false)
    (hxw : written sp x = true) {v : Version V} (hv : (st sp al ts k).S.lv x = some v) :
    ∀ z ∈ pointees sp v.hist, v.ref? z = ((st sp al ts j).S.lv z).map (·.recNo) := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hinvj := inv_st sp al ts hok hst j (by omega)
  have hlog := evLogic_st sp al ts hok hj hmk hev j (by omega)
  have htake := st_S_take hok hst hjk hk
  have hnone := (newest_eq_none_iff (st sp al ts k).S (lastSp (st sp al ts k).S) x).mp hnew
  have hvj : (st sp al ts j).S.lv x = some v := by
    rw [htake, lv_take (fun r' hr' => hnone r' (by omega))]; exact hv
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (Reach.isSome ((reachable_iff _ _ _ _).mp hr))
  obtain ⟨v', hv', hvh, -, -⟩ := hinvj.lv_whole hn hxw hxD hr
  rw [hvj, Option.some.injEq] at hv'
  subst hv'
  intro z hz
  have hz' : z ∈ pointees sp n.hist := by rw [← hvh]; exact hz
  obtain ⟨-, v'', hv'', href⟩ := hlog.clean x n hxw hr hn hxD z hz'
  rw [hvj, Option.some.injEq] at hv''
  subst hv''
  exact href

/-- A node whose D entry predates the section has a version in it: so a node
without a version in the section, current after T(j) for j in it, is not in D
then, but by a got-dirty entry of the section. -/
theorem notD_of_newest_none (hok : RunOK sp al ts) (hj : al.stillDirty = javaTest sp) {j k : Nat}
    (hjk : j ≤ k) (hk : k ≤ ts.length) (hsj : lastSp (st sp al ts k).S ≤ j) {x : NodeId}
    (hnew : newest (st sp al ts k).S (lastSp (st sp al ts k).S) x = none) {d : Nat}
    (hxd : (x, d) ∈ (st sp al ts j).D) :
    lastSp (st sp al ts k).S < d ∧ ∃ R, (st sp al ts k).S[d]? = some R ∧ x ∈ R.gd ∧ d ≤ j := by
  have hkk := kctx_st sp al ts hok hj hjk hk
  by_cases hds : d ≤ lastSp (st sp al ts k).S
  · exfalso
    obtain ⟨r, w, hjr, hw⟩ := hkk.dLater x d hxd hds
    have := (newest_eq_none_iff _ _ x).mp hnew r (by omega)
    rw [hw] at this; cases this
  · exact ⟨by omega, hkk.dSec x d hxd (by omega)⟩

end Run

/-! ## The rerun's invariant -/

/-- Rule R twice is Rule R once. -/
theorem ruleRRef_idem (S : Stream V T) (s : Nat) (y : NodeId) (r : Option Nat) :
    ruleRRef S s y (ruleRRef S s y r) = ruleRRef S s y r := by
  unfold ruleRRef
  cases newest S s y with
  | none => rfl
  | some w =>
    simp only
    cases r with
    | none => simp
    | some r =>
      simp only
      by_cases h : r < w.recNo
      · simp [h]
      · simp only [h, ↓reduceIte]

/-! ## Near the section (bergdb 005-58) -/

/-- No version of y is in a record strictly between r and s: a reference to
record r, for pointee y, names a version of y in R(s), ..., or y's latest
version before R(s) (bergdb 005-58). -/
def NearSec (S : Stream V T) (s : Nat) (y : NodeId) (r : Nat) : Prop :=
  ∀ r', r < r' → r' < s → S.versionAt r' y = none

section Near

variable {sp : Spec V T} {db : DB V T} {k : Nat}

/-- A reference to y's latest version is near every section. -/
theorem Inv.nearSec_of_lv (hinv : Inv sp db k) {y : NodeId} {r : Nat}
    (h : (db.S.lv y).map (·.recNo) = some r) (s : Nat) : NearSec db.S s y r := by
  intro r' hr' _
  cases hl : db.S.lv y with
  | none => rw [hl] at h; cases h
  | some u =>
    rw [hl, Option.map_some, Option.some.injEq] at h
    obtain ⟨r0, h0, hlast⟩ := (lv_eq_some_iff db.S y u).mp hl
    obtain ⟨-, hrec, -⟩ := hinv.version_node h0
    exact hlast r' (by omega)

/-- A reference of a version in record i names its pointee's latest version at
that record (the record rule), so it is near every section that starts at or
before i. -/
theorem Inv.nearSec_of_ref (hinv : Inv sp db k) {i : Nat} {x : NodeId} {v : Version V}
    (hv : db.S.versionAt i x = some v) {s : Nat} (hsi : s ≤ i) {y : NodeId} {r1 : Nat}
    (h1 : v.ref? y = some r1) : NearSec db.S s y r1 := by
  intro r' hr1 hrs
  obtain ⟨R, hR, hvR, -⟩ := versionAt_spec hv
  have hi : i < db.S.length := (List.getElem?_eq_some_iff.mp hR).1
  obtain ⟨pre, hpre, href⟩ := hinv.ref i R hR v hvR
  rw [href y] at h1
  split at h1
  · cases hl : (Stream.building (db.S.take i) pre).lv y with
    | none => rw [hl] at h1; cases h1
    | some u =>
      rw [hl] at h1
      simp only [Option.map_some, Option.some.injEq] at h1
      obtain ⟨r0, hr0, hlast⟩ := (lv_eq_some_iff _ y u).mp hl
      obtain ⟨-, hur, -⟩ := hinv.version_node ((sext_building_take hR hpre).versionAt hr0)
      have h2 := hlast r' (by omega)
      rw [versionAt_building_lt (by simp only [List.length_take]; omega), versionAt_take] at h2
      simpa [show r' < i by omega] using h2
  · cases h1

/-- A reference of a version names a pointee of its history. -/
theorem Inv.ref_mem_pointees (hinv : Inv sp db k) {i : Nat} {x : NodeId} {v : Version V}
    (hv : db.S.versionAt i x = some v) {y : NodeId} {r1 : Nat} (h1 : v.ref? y = some r1) :
    y ∈ pointees sp v.hist := by
  obtain ⟨R, hR, hvR, -⟩ := versionAt_spec hv
  obtain ⟨pre, -, href⟩ := hinv.ref i R hR v hvR
  rw [href y] at h1
  split at h1
  · assumption
  · cases h1

/-- A reference to y's latest version in R(0), ..., R(K) is near a section that
starts at or before K. -/
theorem Inv.nearSec_of_lvAt (hinv : Inv sp db k) {K s : Nat} (hsK : s ≤ K) {y : NodeId}
    {u : Version V} (hl : Stream.lv (db.S.take (K + 1)) y = some u) : NearSec db.S s y u.recNo := by
  intro r' hr' hrs
  obtain ⟨r0, h0, hlast⟩ := (lv_eq_some_iff _ y u).mp hl
  rw [versionAt_take] at h0
  split at h0
  · obtain ⟨-, hrec, -⟩ := hinv.version_node h0
    have h2 := hlast r' (by omega)
    rw [versionAt_take] at h2
    simpa [show r' < K + 1 by omega] using h2
  · cases h0

end Near

/-- The invariant of the startup's memory, against the stream S after T(k), all
through the rerun: every object is canonical; every stream slot names, after
Rule R of S's section, its pointee's latest version; every memory slot names an
object of its pointee; an object of a node without a version in the section is
at the node's latest version; every object has a slot for each pointee; every
stream slot names a version, and no version of its pointee lies between that one
and the section; and every slot is for a pointee (the last two, bergdb 005-58). -/
structure RInv (sp : Spec V T) (S : Stream V T) (m : Mem V) : Prop where
  canon : ∀ h o, m.obj? h = some o → o.canonical = true
  fresh : ∀ h o, m.obj? h = some o → ∀ y r, o.slot? y = some (Slot.stream r) →
    ruleRRef S (lastSp S) y r = (S.lv y).map (·.recNo)
  memNode : ∀ h o, m.obj? h = some o → ∀ y h', o.slot? y = some (Slot.mem h') →
    ∃ o', m.obj? h' = some o' ∧ o'.node = y
  pos : ∀ h o, m.obj? h = some o → newest S (lastSp S) o.node = none →
    o.pos = (S.lv o.node).map (·.recNo)
  /-- Every object has a slot for each pointee of its history. -/
  slotsAll : ∀ h o, m.obj? h = some o → ∀ y ∈ pointees sp o.hist, (o.slot? y).isSome
  /-- Every stream slot's reference names a version of its pointee. -/
  ver : ∀ h o, m.obj? h = some o → ∀ y r, o.slot? y = some (Slot.stream (some r)) →
    ∃ u, S.versionAt r y = some u
  /-- No version of a stream slot's pointee is in a record between the slot's and
  the section (bergdb 005-58). -/
  near : ∀ h o, m.obj? h = some o → ∀ y r, o.slot? y = some (Slot.stream (some r)) →
    NearSec S (lastSp S) y r
  /-- Every slot is for a pointee of its object's history (bergdb 005-58). -/
  keys : ∀ h o, m.obj? h = some o → ∀ y, (o.slot? y).isSome → y ∈ pointees sp o.hist

/-- The stream slot of the object startup makes from version w names, after Rule
R, what w's reference does. -/
theorem canonOfVersion_stream_eq {sp : Spec V T} {S : Stream V T} {s : Nat} {w : Version V}
    {y : NodeId} {r : Option Nat} (h : (canonOfVersion sp S s w).slot? y = some (Slot.stream r)) :
    y ∈ pointees sp w.hist ∧ ruleRRef S s y r = ruleRRef S s y (w.ref? y) := by
  have hy : y ∈ pointees sp (cutHist w (if isKeyLevel sp w.isData w.level then some s else none)) := by
    rw [canonOfVersion_slot?] at h
    by_cases hy : y ∈ pointees sp (cutHist w (if isKeyLevel sp w.isData w.level then some s else none))
    · exact hy
    · simp only [hy, ↓reduceIte] at h; cases h
  refine ⟨pointees_cutHist hy, ?_⟩
  have := canonOfVersion_slot_eq h
  simp only [Slot.stream.injEq] at this
  rw [this, ruleRRef_idem]

section Base

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

/-- The memory before the rerun meets the rerun's invariant. -/
theorem rinv_lazyBase (hok : RunOK sp al ts) (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true)
    (hev : EvictRunOK sp al ts) {k : Nat} (hk : k ≤ ts.length) :
    RInv sp (st sp al ts k).S (lazyBase sp (st sp al ts k).S) := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hinv := inv_st sp al ts hok hst k hk
  have hb := hinv.base2 (sp := sp)
  have hsk : lastSp (st sp al ts k).S ≤ k := by have := hinv.spLt; omega
  -- The stream slots of the objects before the memory slots.
  have hfresh2 : ∀ h o2, (lazyRoot sp (st sp al ts k).S (lazySec sp (st sp al ts k).S)).obj? h = some o2 →
      ∀ y r, o2.slot? y = some (Slot.stream r) →
      ruleRRef (st sp al ts k).S (lastSp (st sp al ts k).S) y r = ((st sp al ts k).S.lv y).map (·.recNo) := by
    intro h o2 ho2 y r hsl
    obtain ⟨-, -, hsrc⟩ := hb.obj h o2 ho2
    rcases hsrc with ⟨w, r0, hw, hr0, hoe, -⟩ | ⟨hv, hoe⟩ | ⟨hv, u, hu, hus, hnw, hoe⟩
    · subst hoe
      obtain ⟨hy, he⟩ := canonOfVersion_stream_eq hsl
      rw [he]
      exact hinv.ruleR_section hw hr0 hy
    · subst hoe
      have hsl' : (canonOfVersion sp (st sp al ts k).S (lastSp (st sp al ts k).S)
          (rootVersion sp (lastSp (st sp al ts k).S)
            (topsRead sp (st sp al ts k).S (lastSp (st sp al ts k).S) true))).slot? y =
          some (Slot.stream r) := hsl
      obtain ⟨hy, he⟩ := canonOfVersion_stream_eq hsl'
      rw [he]
      have hws := (hinv.topsRead_spec hv).1
      -- the reference names the version read of y, which is y's latest
      have href : ∀ r'', (rootVersion sp (lastSp (st sp al ts k).S)
          (topsRead sp (st sp al ts k).S (lastSp (st sp al ts k).S) true)).ref? y = some r'' →
          ∃ w, (st sp al ts k).S.lv y = some w ∧ w.recNo = r'' := by
        intro r'' hr''
        obtain ⟨w, hw, hwy, hwr⟩ := lookup_refs_some hr''
        obtain ⟨-, -, -, -, hlv⟩ := hws w hw
        exact ⟨w, by rw [← hwy]; exact hlv, hwr⟩
      apply hinv.ruleR_eq_lv _ (fun r'' h => by
        obtain ⟨w, hlv, hwr⟩ := href r'' h
        rw [← hwr]; exact ⟨w, hinv.lv_at hlv⟩)
      intro _
      cases hr' : (rootVersion sp (lastSp (st sp al ts k).S)
          (topsRead sp (st sp al ts k).S (lastSp (st sp al ts k).S) true)).ref? y with
      | some r'' =>
        obtain ⟨w, hlv, hwr⟩ := href r'' hr'
        rw [hlv, Option.map_some, hwr]
      | none =>
        exfalso
        -- y is the node of a version read: the root's entries are for them
        rw [mem_pointees] at hy
        obtain ⟨e, he, hye⟩ := hy
        simp only [rootVersion, List.mem_filterMap, List.mem_range] at he
        obtain ⟨t, -, hf⟩ := he
        obtain ⟨w, hwf, hwe⟩ := Option.map_eq_some_iff.mp hf
        have hwm := List.mem_of_find?_eq_some hwf
        rw [← hwe, (hinv.vr hv).rootPtrs] at hye
        simp only [List.mem_singleton] at hye
        have := lookup_isSome_of_mem (l := (topsRead sp (st sp al ts k).S (lastSp (st sp al ts k).S) true).map
          (fun w => (w.node, w.recNo))) (a := w.node) (List.mem_map.mpr ⟨(w.node, w.recNo),
            List.mem_map.mpr ⟨w, hwm, rfl⟩, rfl⟩)
        unfold Version.ref? at hr'
        simp only [rootVersion] at hr'
        rw [← hye, hr'] at this
        cases this
    · subst hoe
      obtain ⟨hy, he⟩ := canonOfVersion_stream_eq hsl
      rw [he]
      have hroot : reachable sp (st sp al ts (lastSp (st sp al ts k).S)).P (lastSp (st sp al ts k).S)
          SIS.root = true := by
        obtain ⟨n0, h0⟩ := Option.isSome_iff_exists.mp
          (inv_st sp al ts hok hst (lastSp (st sp al ts k).S) (by omega)).rootIn
        exact reachable_root h0 _
      have hrD : inD (st sp al ts (lastSp (st sp al ts k).S)).D SIS.root = false := by
        cases hd : inD (st sp al ts (lastSp (st sp al ts k).S)).D SIS.root with
        | false => rfl
        | true =>
          obtain ⟨d, hd'⟩ := (inD_iff _ _).mp hd
          obtain ⟨h1, -, -, -, h2⟩ := notD_of_newest_none hok hj hsk hk (Nat.le_refl _) hnw hd'
          omega
      have hrw : written sp SIS.root = true := by simp [written, hv]
      exact (fresh_clean hok hj hmk hev hsk hk (Nat.le_refl _) hnw hroot hrD hrw hu).2 y hy
  -- The stream slots of the objects before the memory slots name versions: Rule R of
  -- a version's reference.
  have hver2 : ∀ h o2, (lazyRoot sp (st sp al ts k).S (lazySec sp (st sp al ts k).S)).obj? h = some o2 →
      ∀ y r, o2.slot? y = some (Slot.stream (some r)) → ∃ u, (st sp al ts k).S.versionAt r y = some u := by
    intro h o2 ho2 y r hsl
    obtain ⟨-, -, hsrc⟩ := hb.obj h o2 ho2
    have hcv : ∀ w : Version V, (∀ r' y', w.ref? y' = some r' → ∃ u, (st sp al ts k).S.versionAt r' y' = some u) →
        (canonOfVersion sp (st sp al ts k).S (lastSp (st sp al ts k).S) w).slot? y = some (Slot.stream (some r)) →
        ∃ u, (st sp al ts k).S.versionAt r y = some u := by
      intro w hw hs
      have := canonOfVersion_slot_eq hs
      simp only [Slot.stream.injEq] at this
      exact (hinv.ruleR_bound (List.prefix_refl _) _ (fun r' h' => hw r' y h') this.symm).1
    rcases hsrc with ⟨w, r0, hw, -, hoe, -⟩ | ⟨hv, hoe⟩ | ⟨-, u, hu, -, -, hoe⟩
    · subst hoe
      exact hcv w (fun r' y' h' => hinv.ref_versionAt hw h') hsl
    · subst hoe
      apply hcv _ _ hsl
      intro r' y' hr'
      obtain ⟨w, hw, hwy, hwr⟩ := lookup_refs_some hr'
      obtain ⟨-, -, -, -, hlv⟩ := (hinv.topsRead_spec hv).1 w hw
      rw [← hwr, ← hwy]
      exact ⟨w, hinv.lv_at hlv⟩
    · subst hoe
      exact hcv u (fun r' y' h' => hinv.ref_versionAt (hinv.lv_at hu) h') hsl
  -- The stream slots of the objects before the memory slots are Rule R's of a
  -- reference, so Rule R leaves them (bergdb 005-58).
  have hfix2 : ∀ h o2, (lazyRoot sp (st sp al ts k).S (lazySec sp (st sp al ts k).S)).obj? h = some o2 →
      ∀ y r, o2.slot? y = some (Slot.stream r) →
      ruleRRef (st sp al ts k).S (lastSp (st sp al ts k).S) y r = r := by
    intro h o2 ho2 y r hsl
    obtain ⟨-, -, hsrc⟩ := hb.obj h o2 ho2
    have hcv : ∀ w : Version V, (canonOfVersion sp (st sp al ts k).S (lastSp (st sp al ts k).S) w).slot? y =
        some (Slot.stream r) → ruleRRef (st sp al ts k).S (lastSp (st sp al ts k).S) y r = r := by
      intro w hs
      have := canonOfVersion_slot_eq hs
      simp only [Slot.stream.injEq] at this
      rw [this, ruleRRef_idem]
    rcases hsrc with ⟨w, -, -, -, hoe, -⟩ | ⟨-, hoe⟩ | ⟨-, u, -, -, -, hoe⟩
    · subst hoe; exact hcv w hsl
    · subst hoe; exact hcv _ hsl
    · subst hoe; exact hcv u hsl
  refine ⟨fun h o ho => ?_, fun h o ho y r hsl => ?_, fun h o ho y h' hsl => ?_, fun h o ho hn => ?_,
    fun h o ho y hy => ?_, fun h o ho y r hsl => ?_, fun h o ho y r hsl => ?_, fun h o ho y hy => ?_⟩
  · unfold lazyBase at ho
    rw [linkCanonical_obj?] at ho
    obtain ⟨o2, ho2, rfl⟩ := Option.map_eq_some_iff.mp ho
    rw [(linkObj_fields _ o2).2.2.2.2.1]
    exact (hb.obj h o2 ho2).2.1
  · unfold lazyBase at ho
    rw [linkCanonical_obj?] at ho
    obtain ⟨o2, ho2, rfl⟩ := Option.map_eq_some_iff.mp ho
    obtain ⟨-, hc2, -⟩ := hb.obj h o2 ho2
    rw [linkObj_slot? _ hc2] at hsl
    obtain ⟨sl2, hsl2, hq⟩ := Option.map_eq_some_iff.mp hsl
    rcases linkQ_cases (lazyRoot sp (st sp al ts k).S (lazySec sp (st sp al ts k).S)) y sl2 with
      he | ⟨h0, o0, -, -, -, he⟩
    · rw [he] at hq
      subst hq
      exact hfresh2 h o2 ho2 y r hsl2
    · rw [he] at hq; cases hq
  · unfold lazyBase at ho ⊢
    rw [linkCanonical_obj?] at ho
    obtain ⟨o2, ho2, rfl⟩ := Option.map_eq_some_iff.mp ho
    obtain ⟨-, hc2, -⟩ := hb.obj h o2 ho2
    rw [linkObj_slot? _ hc2] at hsl
    obtain ⟨sl2, hsl2, hq⟩ := Option.map_eq_some_iff.mp hsl
    obtain ⟨r2, rfl⟩ := hb.stream_slots ho2 hsl2
    rcases linkQ_cases (lazyRoot sp (st sp al ts k).S (lazySec sp (st sp al ts k).S)) y (Slot.stream r2) with
      he | ⟨h0, o0, ht0, ho0, -, he⟩
    · rw [he] at hq; cases hq
    · rw [he, Slot.mem.injEq] at hq
      subst hq
      obtain ⟨o', ho', hn'⟩ := hb.tbl y h0 ht0
      rw [ho0, Option.some.injEq] at ho'
      subst ho'
      exact ⟨linkObj _ o0, by rw [linkCanonical_obj?, ho0]; rfl, by rw [(linkObj_fields _ o0).1, hn']⟩
  · unfold lazyBase at ho
    rw [linkCanonical_obj?] at ho
    obtain ⟨o2, ho2, rfl⟩ := Option.map_eq_some_iff.mp ho
    rw [(linkObj_fields _ o2).1] at hn
    rw [(linkObj_fields _ o2).2.2.2.2.2, (linkObj_fields _ o2).1]
    obtain ⟨-, -, hsrc⟩ := hb.obj h o2 ho2
    rcases hsrc with ⟨w, r0, hw, hr0, hoe, -⟩ | ⟨hv, hoe⟩ | ⟨-, u, hu, -, -, hoe⟩
    · exact absurd hn (newest_some_of_versionAt hw hr0)
    · subst hoe
      show none = ((st sp al ts k).S.lv SIS.root).map (·.recNo)
      cases hl : (st sp al ts k).S.lv SIS.root with
      | none => rfl
      | some v =>
        exfalso
        obtain ⟨r, hr⟩ := lv_versionAt hl
        obtain ⟨R, hR, hvR, hvn⟩ := versionAt_spec hr
        exact (hinv.vr hv).rootNV r R hR v hvR hvn
    · subst hoe
      rw [(canonOfVersion_fields sp _ _ u).2.2.2.2.2, (canonOfVersion_fields sp _ _ u).1,
        (hinv.version_node (hinv.lv_at hu)).1, hu]
      rfl
  · unfold lazyBase at ho
    rw [linkCanonical_obj?] at ho
    obtain ⟨o2, ho2, rfl⟩ := Option.map_eq_some_iff.mp ho
    obtain ⟨-, hc2, hsrc⟩ := hb.obj h o2 ho2
    rw [(linkObj_fields _ o2).2.2.2.1] at hy
    rw [linkObj_slot? _ hc2]
    suffices hs : (o2.slot? y).isSome by
      obtain ⟨sl, hsl⟩ := Option.isSome_iff_exists.mp hs
      rw [hsl]; rfl
    rcases hsrc with ⟨w, -, -, -, hoe, -⟩ | ⟨-, hoe⟩ | ⟨-, u, -, -, -, hoe⟩
    · subst hoe
      rw [(canonOfVersion_fields sp _ _ w).2.2.2.1] at hy
      rw [canonOfVersion_slot?]; simp [hy]
    · subst hoe
      have hcut : cutHist (rootVersion sp (lastSp (st sp al ts k).S)
          (topsRead sp (st sp al ts k).S (lastSp (st sp al ts k).S) true))
          (if isKeyLevel sp (rootVersion sp (lastSp (st sp al ts k).S)
            (topsRead sp (st sp al ts k).S (lastSp (st sp al ts k).S) true)).isData
            (rootVersion sp (lastSp (st sp al ts k).S)
              (topsRead sp (st sp al ts k).S (lastSp (st sp al ts k).S) true)).level
            then some (lastSp (st sp al ts k).S) else none) =
          (rootVersion sp (lastSp (st sp al ts k).S)
            (topsRead sp (st sp al ts k).S (lastSp (st sp al ts k).S) true)).hist := by
        split
        · exact upTo_of_forall _ _ (rootVersion_times sp _ _)
        · rfl
      show ((canonOfVersion sp (st sp al ts k).S (lastSp (st sp al ts k).S) _).slot? y).isSome
      rw [canonOfVersion_slot?, hcut]
      have hy' : y ∈ pointees sp (rootVersion sp (lastSp (st sp al ts k).S)
          (topsRead sp (st sp al ts k).S (lastSp (st sp al ts k).S) true)).hist := hy
      simp [hy']
    · subst hoe
      rw [(canonOfVersion_fields sp _ _ u).2.2.2.1] at hy
      rw [canonOfVersion_slot?]; simp [hy]
  · unfold lazyBase at ho
    rw [linkCanonical_obj?] at ho
    obtain ⟨o2, ho2, rfl⟩ := Option.map_eq_some_iff.mp ho
    obtain ⟨-, hc2, -⟩ := hb.obj h o2 ho2
    rw [linkObj_slot? _ hc2] at hsl
    obtain ⟨sl2, hsl2, hq⟩ := Option.map_eq_some_iff.mp hsl
    rcases linkQ_cases (lazyRoot sp (st sp al ts k).S (lazySec sp (st sp al ts k).S)) y sl2 with
      he | ⟨h0, o0, -, -, -, he⟩
    · rw [he] at hq
      subst hq
      exact hver2 h o2 ho2 y r hsl2
    · rw [he] at hq; cases hq
  · -- a stream slot names its pointee's latest version, so nothing lies between
    unfold lazyBase at ho
    rw [linkCanonical_obj?] at ho
    obtain ⟨o2, ho2, rfl⟩ := Option.map_eq_some_iff.mp ho
    obtain ⟨-, hc2, -⟩ := hb.obj h o2 ho2
    rw [linkObj_slot? _ hc2] at hsl
    obtain ⟨sl2, hsl2, hq⟩ := Option.map_eq_some_iff.mp hsl
    rcases linkQ_cases (lazyRoot sp (st sp al ts k).S (lazySec sp (st sp al ts k).S)) y sl2 with
      he | ⟨h0, o0, -, -, -, he⟩
    · rw [he] at hq
      subst hq
      have hfr := hfresh2 h o2 ho2 y (some r) hsl2
      rw [hfix2 h o2 ho2 y (some r) hsl2] at hfr
      exact hinv.nearSec_of_lv hfr.symm _
    · rw [he] at hq; cases hq
  · -- every slot is for a pointee of the history read
    unfold lazyBase at ho
    rw [linkCanonical_obj?] at ho
    obtain ⟨o2, ho2, rfl⟩ := Option.map_eq_some_iff.mp ho
    obtain ⟨-, hc2, hsrc⟩ := hb.obj h o2 ho2
    rw [linkObj_slot? _ hc2, Option.isSome_map] at hy
    rw [(linkObj_fields _ o2).2.2.2.1]
    rcases hsrc with ⟨w, -, -, -, hoe, -⟩ | ⟨-, hoe⟩ | ⟨-, u, -, -, -, hoe⟩
    · subst hoe
      rw [(canonOfVersion_fields sp _ _ w).2.2.2.1]
      rw [canonOfVersion_slot?] at hy
      by_cases hmem : y ∈ pointees sp (cutHist w (if isKeyLevel sp w.isData w.level then
          some (lastSp (st sp al ts k).S) else none))
      · exact hmem
      · simp [hmem] at hy
    · subst hoe
      have hy' : ((canonOfVersion sp (st sp al ts k).S (lastSp (st sp al ts k).S)
          (rootVersion sp (lastSp (st sp al ts k).S)
            (topsRead sp (st sp al ts k).S (lastSp (st sp al ts k).S) true))).slot? y).isSome := hy
      rw [canonOfVersion_slot?] at hy'
      generalize hrv : rootVersion sp (lastSp (st sp al ts k).S)
        (topsRead sp (st sp al ts k).S (lastSp (st sp al ts k).S) true) = rv at hy'
      show y ∈ pointees sp (rootVersion sp (lastSp (st sp al ts k).S)
        (topsRead sp (st sp al ts k).S (lastSp (st sp al ts k).S) true)).hist
      rw [hrv]
      by_cases hmem : y ∈ pointees sp (cutHist rv (if isKeyLevel sp rv.isData rv.level then
          some (lastSp (st sp al ts k).S) else none))
      · exact pointees_cutHist hmem
      · simp [hmem] at hy'
    · subst hoe
      rw [(canonOfVersion_fields sp _ _ u).2.2.2.1]
      rw [canonOfVersion_slot?] at hy
      by_cases hmem : y ∈ pointees sp (cutHist u (if isKeyLevel sp u.isData u.level then
          some (lastSp (st sp al ts k).S) else none))
      · exact hmem
      · simp [hmem] at hy

end Base

/-! ## The rerun keeps its invariant -/

theorem Obj.setSlot_twice (o : Obj V) (y : NodeId) (sl : Slot) : (o.setSlot y sl).setSlot y sl = o.setSlot y sl := by
  unfold Obj.setSlot
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro p _
  simp only [Function.comp]
  by_cases hp : p.1 == y
  · simp [hp]
  · simp [hp]

section Walk

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

/-- The writer's walk of the rerun keeps the rerun's invariant: a node it loads
has no version in the section, or its version is one; either way the slots of
its object name latest versions after Rule R. -/
theorem RInv.reachOnPath (hok : RunOK sp al ts) (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true)
    (hev : EvictRunOK sp al ts) {k K : Nat} (hk : k ≤ ts.length) (hKk : K < k)
    (hsK : lastSp (st sp al ts k).S ≤ K) {m : Mem V} (hr : RInv sp (st sp al ts k).S m)
    (hm : MemInv sp (st sp al ts k) K m) {P : Struct V} (hP : SameNodes P (st sp al ts K).P)
    {path : List NodeId} (hpath : ∀ p ∈ path, reachable sp (st sp al ts k).P K p = true) (x : NodeId) :
    RInv sp (st sp al ts k).S (m.reachOnPath sp (st sp al ts k).S P (K + 1) path x) := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hls : LiveSub sp := hok.1.liveSub
  have hinvk := inv_st sp al ts hok hst k hk
  have hinvK := inv_st sp al ts hok hst K (by omega)
  have hkK := kctx_st sp al ts hok hj (Nat.le_of_lt hKk) hk
  unfold Mem.reachOnPath
  cases hcx : m.canonicalOf x with
  | some _ => exact hr
  | none =>
    simp only
    have hK1 : K + 1 - 1 = K := by omega
    cases hf : path.find? (fun p => match P.get? p, m.canonicalOf p with
        | some n, some _ => (sp.live (n.hist.upTo (K + 1 - 1))).contains x
        | _, _ => false) with
    | none => exact hr
    | some p =>
      simp only
      have hpp := List.find?_some hf
      have hpm := List.mem_of_find?_eq_some hf
      cases hnp : P.get? p with
      | none => rw [hnp] at hpp; simp at hpp
      | some np =>
        cases hcp : m.canonicalOf p with
        | none => rw [hnp, hcp] at hpp; simp at hpp
        | some hp =>
          simp only
          rw [hnp, hcp] at hpp
          simp only [hK1, List.contains_iff_mem] at hpp
          -- x: a live child at K of p, so reachable at K, not the root
          have hnpK : (st sp al ts K).P.get? p = some np := by rw [← hP]; exact hnp
          have hrpK : reachable sp (st sp al ts K).P K p = true := by
            rw [← hkK.reachable_eq hls (Nat.le_refl K)]; exact hpath p hpm
          obtain ⟨hrx, hxr, -⟩ := hinvK.reach_child hls hnpK hrpK hpp
          have hxw : written sp x = true := written_of_ne_root sp hxr
          obtain ⟨ht0, op, hop, hco⟩ := (m.canonicalOf_eq_some p hp).mp hcp
          -- the slot followed
          cases hsl : op.slot? x with
          | none =>
            unfold Mem.follow
            simp only [hop, hsl, Option.bind_some]
            exact hr
          | some sl =>
            cases sl with
            | mem h =>
              cases ho : m.obj? h with
              | none =>
                unfold Mem.follow
                simp only [hop, hsl, Option.bind_some, ho]
                exact hr
              | some o =>
                rw [follow_mem_eval_w sp _ m hop hsl ho, hr.canon h o ho]
                exact hr
            | stream r =>
              -- No object of x in the node table: it would be canonical.
              have htx : m.tableOf x = none := by
                cases htx : m.tableOf x with
                | none => rfl
                | some h0 =>
                  exfalso
                  obtain ⟨o0, ho0, -⟩ := hm.tbl x h0 htx
                  have := (m.canonicalOf_eq_some x h0).mpr ⟨htx, o0, ho0, hr.canon h0 o0 ho0⟩
                  rw [hcx] at this; cases this
              have hrr : ruleRRef (st sp al ts k).S m.s x r = ((st sp al ts k).S.lv x).map (·.recNo) := by
                rw [hm.sEq]; exact hr.fresh hp op hop x r hsl
              cases hlv : (st sp al ts k).S.lv x with
              | none =>
                rw [hlv] at hrr
                unfold Mem.follow
                simp only [hop, hsl, Option.bind_some, htx, hrr, Option.map_none]
                exact hr
              | some w =>
                rw [hlv] at hrr
                simp only [Option.map_some] at hrr
                have hw := hinvk.lv_at hlv
                obtain ⟨hwx, -, -⟩ := hinvk.version_node hw
                -- the object loaded, entered in the table, and made canonical
                let cut := if m.s ≤ w.recNo && isKeyLevel sp w.isData w.level then some m.s else none
                have hpn : hp ≠ m.next := by
                  intro he; subst he; rw [hm.fresh _ (Nat.le_refl _)] at hop; cases hop
                have hreg : (m.addObj (Obj.ofVersion sp w cut)).1.register m.next =
                    ((m.addObj (Obj.ofVersion sp w cut)).1.setTable x m.next, m.next) := by
                  have h1 : (m.addObj (Obj.ofVersion sp w cut)).1.obj? m.next = some (Obj.ofVersion sp w cut) := by
                    rw [Mem.obj?_addObj]; simp
                  have h2 := register_none _ h1 (by
                    rw [(Obj.ofVersion_fields sp w cut).1, hwx, Mem.tableOf_addObj]; exact htx)
                  rw [(Obj.ofVersion_fields sp w cut).1, hwx] at h2
                  exact h2
                have hop1 : ((m.addObj (Obj.ofVersion sp w cut)).1.setTable x m.next).obj? hp = some op := by
                  rw [Mem.obj?_setTable, Mem.obj?_addObj]; simp only [hpn, ↓reduceIte]; exact hop
                have ho1 : ((m.addObj (Obj.ofVersion sp w cut)).1.setTable x m.next).obj? m.next =
                    some (Obj.ofVersion sp w cut) := by
                  rw [Mem.obj?_setTable, Mem.obj?_addObj]; simp
                rw [follow_load_eval_w sp _ m hop hsl (fun h0 o0 ht _ => by rw [htx] at ht; cases ht) hrr hw
                  hreg hop1 (Ne.symm hpn) ho1]
                rw [(Obj.ofVersion_fields sp w cut).2.2.2.2.1]
                simp only [Bool.false_eq_true, ↓reduceIte]
                have hmc := makeCanonical_eval (((m.addObj (Obj.ofVersion sp w cut)).1.setTable x m.next).setObj hp
                  (op.setSlot x (Slot.mem m.next))) (h := m.next) (y := x) (hp := hp)
                  (o1 := Obj.ofVersion sp w cut) (op := op.setSlot x (Slot.mem m.next))
                  (by rw [Mem.tableOf_setObj, Mem.tableOf_setTable]; simp)
                  (by rw [Mem.obj?_setObj]; simp only [Ne.symm hpn, ↓reduceIte]; exact ho1)
                  (by rw [Mem.obj?_setObj]; simp) hpn
                rw [hmc, Obj.setSlot_twice]
                -- What the memory holds now.
                have hobj : ∀ h', ((((((m.addObj (Obj.ofVersion sp w cut)).1.setTable x m.next).setObj hp
                    (op.setSlot x (Slot.mem m.next))).setObj m.next { Obj.ofVersion sp w cut with canonical := true }).setTable
                      x m.next).setObj hp (op.setSlot x (Slot.mem m.next))).obj? h' =
                    if h' = hp then some (op.setSlot x (Slot.mem m.next)) else
                      if h' = m.next then some { Obj.ofVersion sp w cut with canonical := true } else m.obj? h' := by
                  intro h'
                  rw [Mem.obj?_setObj, Mem.obj?_setTable, Mem.obj?_setObj, Mem.obj?_setObj, Mem.obj?_setTable,
                    Mem.obj?_addObj]
                  by_cases h1 : h' = hp
                  · simp [h1]
                  · by_cases h2 : h' = m.next
                    · simp [h2]
                    · simp [h1, h2]
                obtain ⟨f1, f2, f3, f4, -, f6⟩ := Obj.ofVersion_fields sp w cut
                have hslot1 : ∀ z sl, (Obj.ofVersion sp w cut).slot? z = some sl →
                    z ∈ pointees sp w.hist ∧ sl = Slot.stream (w.ref? z) := by
                  intro z sl hz
                  rw [Obj.ofVersion_slot?] at hz
                  by_cases hz' : z ∈ pointees sp (cutHist w cut)
                  · simp only [hz', ↓reduceIte, Option.some.injEq] at hz
                    exact ⟨pointees_cutHist hz', hz.symm⟩
                  · simp only [hz', ↓reduceIte] at hz; cases hz
                -- The new object's references name latest versions after Rule R.
                have hfreshw : ∀ z ∈ pointees sp w.hist, ruleRRef (st sp al ts k).S (lastSp (st sp al ts k).S) z
                    (w.ref? z) = ((st sp al ts k).S.lv z).map (·.recNo) := by
                  intro z hz
                  cases hnw : newest (st sp al ts k).S (lastSp (st sp al ts k).S) x with
                  | some u =>
                    obtain ⟨r0, hr0, hu0⟩ := newest_some hnw
                    have hu := newest_lv hnw
                    rw [hlv, Option.some.injEq] at hu
                    subst hu
                    exact hinvk.ruleR_section hu0 hr0 hz
                  | none =>
                    have hxD : inD (st sp al ts K).D x = false := by
                      cases hd : inD (st sp al ts K).D x with
                      | false => rfl
                      | true =>
                        exfalso
                        obtain ⟨d, hd'⟩ := (inD_iff _ _).mp hd
                        obtain ⟨hsd, R, hR, hxR, hdK⟩ := notD_of_newest_none hok hj (Nat.le_of_lt hKk) hk hsK hnw hd'
                        exact hm.coverGd d R x hsd hdK hR hxR hcx
                    exact (fresh_clean hok hj hmk hev (Nat.le_of_lt hKk) hk hsK hnw hrx hxD hxw hlv).2 z hz
                -- No version of a pointee lies between the new object's references and the
                -- section (bergdb 005-58): a version of the section names the latest versions
                -- at its record; x, current and clean at K, names the latest versions at K.
                have hnearw : ∀ z r', w.ref? z = some r' →
                    NearSec (st sp al ts k).S (lastSp (st sp al ts k).S) z r' := by
                  intro z r' hz
                  cases hnw : newest (st sp al ts k).S (lastSp (st sp al ts k).S) x with
                  | some u =>
                    obtain ⟨r0, hr0, hu0⟩ := newest_some hnw
                    have hu := newest_lv hnw
                    rw [hlv, Option.some.injEq] at hu
                    subst hu
                    exact hinvk.nearSec_of_ref hu0 hr0 hz
                  | none =>
                    have hxD : inD (st sp al ts K).D x = false := by
                      cases hd : inD (st sp al ts K).D x with
                      | false => rfl
                      | true =>
                        exfalso
                        obtain ⟨d, hd'⟩ := (inD_iff _ _).mp hd
                        obtain ⟨hsd, R, hR, hxR, hdK⟩ := notD_of_newest_none hok hj (Nat.le_of_lt hKk) hk hsK hnw hd'
                        exact hm.coverGd d R x hsd hdK hR hxR hcx
                    have href := clean_ref_lvAt hok hj hmk hev (Nat.le_of_lt hKk) hk hsK hnw hrx hxD hxw hlv z
                      (hinvk.ref_mem_pointees hw hz)
                    rw [hz, st_S_take hok hst (Nat.le_of_lt hKk) hk] at href
                    cases hl : Stream.lv ((st sp al ts k).S.take (K + 1)) z with
                    | none => rw [hl] at href; cases href
                    | some u =>
                      rw [hl, Option.map_some, Option.some.injEq] at href
                      rw [href]
                      exact hinvk.nearSec_of_lvAt hsK hl
                refine ⟨fun h' o' ho' => ?_, fun h' o' ho' z r' hz => ?_, fun h' o' ho' z h'' hz => ?_,
                  fun h' o' ho' hn => ?_, fun h' o' ho' z hz => ?_, fun h' o' ho' z r' hz => ?_,
                  fun h' o' ho' z r' hz => ?_, fun h' o' ho' z hz => ?_⟩
                · rw [hobj] at ho'
                  split at ho'
                  · simp only [Option.some.injEq] at ho'; subst ho'; exact hco
                  · split at ho'
                    · simp only [Option.some.injEq] at ho'; subst ho'; rfl
                    · exact hr.canon h' o' ho'
                · rw [hobj] at ho'
                  split at ho'
                  · simp only [Option.some.injEq] at ho'; subst ho'
                    rw [slot?_setSlot_of hsl] at hz
                    split at hz
                    · cases hz
                    · exact hr.fresh hp op hop z r' hz
                  · split at ho'
                    · simp only [Option.some.injEq] at ho'; subst ho'
                      obtain ⟨hzp, hze⟩ := hslot1 z _ hz
                      simp only [Slot.stream.injEq] at hze
                      rw [hze]
                      exact hfreshw z hzp
                    · exact hr.fresh h' o' ho' z r' hz
                · -- memory slots: hp's new one names the new object of x; the others are m's
                  have hold : ∀ h2 o2, m.obj? h2 = some o2 → ∃ o3, ((((((m.addObj (Obj.ofVersion sp w cut)).1.setTable
                      x m.next).setObj hp (op.setSlot x (Slot.mem m.next))).setObj m.next
                        { Obj.ofVersion sp w cut with canonical := true }).setTable x m.next).setObj hp
                          (op.setSlot x (Slot.mem m.next))).obj? h2 = some o3 ∧ o3.node = o2.node := by
                    intro h2 o2 ho2
                    rw [hobj]
                    have h2n : h2 ≠ m.next := by
                      intro he; subst he; rw [hm.fresh _ (Nat.le_refl _)] at ho2; cases ho2
                    by_cases h2p : h2 = hp
                    · subst h2p; rw [hop, Option.some.injEq] at ho2; subst ho2
                      exact ⟨op.setSlot x (Slot.mem m.next), by simp, rfl⟩
                    · exact ⟨o2, by simp [h2p, h2n, ho2], rfl⟩
                  rw [hobj] at ho'
                  split at ho'
                  · simp only [Option.some.injEq] at ho'; subst ho'
                    rw [slot?_setSlot_of hsl] at hz
                    split at hz
                    · rename_i hzx; subst hzx
                      simp only [Option.some.injEq, Slot.mem.injEq] at hz
                      subst hz
                      refine ⟨{ Obj.ofVersion sp w cut with canonical := true }, by rw [hobj]; simp [Ne.symm hpn], ?_⟩
                      show (Obj.ofVersion sp w cut).node = _
                      rw [f1, hwx]
                    · obtain ⟨o2, ho2, hn2⟩ := hr.memNode hp op hop z h'' hz
                      obtain ⟨o3, ho3, hn3⟩ := hold h'' o2 ho2
                      exact ⟨o3, ho3, by rw [hn3, hn2]⟩
                  · split at ho'
                    · simp only [Option.some.injEq] at ho'; subst ho'
                      obtain ⟨-, hze⟩ := hslot1 z _ hz
                      cases hze
                    · obtain ⟨o2, ho2, hn2⟩ := hr.memNode h' o' ho' z h'' hz
                      obtain ⟨o3, ho3, hn3⟩ := hold h'' o2 ho2
                      exact ⟨o3, ho3, by rw [hn3, hn2]⟩
                · rw [hobj] at ho'
                  split at ho'
                  · simp only [Option.some.injEq] at ho'; subst ho'
                    exact hr.pos hp op hop hn
                  · split at ho'
                    · simp only [Option.some.injEq] at ho'; subst ho'
                      show (Obj.ofVersion sp w cut).pos = _
                      rw [f6, f1, hwx, hlv]
                      rfl
                    · exact hr.pos h' o' ho' hn
                · rw [hobj] at ho'
                  split at ho'
                  · simp only [Option.some.injEq] at ho'; subst ho'
                    rw [slot?_setSlot_of hsl]
                    split
                    · rfl
                    · exact hr.slotsAll hp op hop z hz
                  · split at ho'
                    · simp only [Option.some.injEq] at ho'; subst ho'
                      show ((Obj.ofVersion sp w cut).slot? z).isSome
                      have hz' : z ∈ pointees sp (cutHist w cut) := by rw [← f4]; exact hz
                      rw [Obj.ofVersion_slot?]; simp [hz']
                    · exact hr.slotsAll h' o' ho' z hz
                · -- stream slots name versions: the new object's are the version's references
                  rw [hobj] at ho'
                  split at ho'
                  · simp only [Option.some.injEq] at ho'; subst ho'
                    rw [slot?_setSlot_of hsl] at hz
                    split at hz
                    · cases hz
                    · exact hr.ver hp op hop z r' hz
                  · split at ho'
                    · simp only [Option.some.injEq] at ho'; subst ho'
                      obtain ⟨-, hze⟩ := hslot1 z _ hz
                      simp only [Slot.stream.injEq] at hze
                      exact hinvk.ref_versionAt hw hze.symm
                    · exact hr.ver h' o' ho' z r' hz
                · -- no version between a stream slot's and the section
                  rw [hobj] at ho'
                  split at ho'
                  · simp only [Option.some.injEq] at ho'; subst ho'
                    rw [slot?_setSlot_of hsl] at hz
                    split at hz
                    · cases hz
                    · exact hr.near hp op hop z r' hz
                  · split at ho'
                    · simp only [Option.some.injEq] at ho'; subst ho'
                      obtain ⟨-, hze⟩ := hslot1 z _ hz
                      simp only [Slot.stream.injEq] at hze
                      exact hnearw z r' hze.symm
                    · exact hr.near h' o' ho' z r' hz
                · -- every slot is for a pointee
                  rw [hobj] at ho'
                  split at ho'
                  · simp only [Option.some.injEq] at ho'; subst ho'
                    rw [slot?_setSlot_of hsl] at hz
                    show z ∈ pointees sp op.hist
                    split at hz
                    · rename_i hzx; subst hzx; exact hr.keys hp op hop _ (by rw [hsl]; rfl)
                    · exact hr.keys hp op hop z hz
                  · split at ho'
                    · simp only [Option.some.injEq] at ho'; subst ho'
                      show z ∈ pointees sp (Obj.ofVersion sp w cut).hist
                      have hz' : ((Obj.ofVersion sp w cut).slot? z).isSome := hz
                      rw [Obj.ofVersion_slot?] at hz'
                      rw [f4]
                      split at hz'
                      · assumption
                      · cases hz'
                    · exact hr.keys h' o' ho' z hz

end Walk

section Apply

variable {sp : Spec V T} {S : Stream V T} {P : Struct V} {j : Time} {c : Changes V}

/-- The change applied in the rerun keeps the rerun's invariant: a new pointer's
slot names a canonical object, or copies a slot of an object, which names its
pointee's latest version after Rule R; a new node's object has no slots, and no
position, nor the node a version. -/
theorem RInv.applyChange {m : Mem V} (hr : RInv sp S m) (hfr : ∀ h, m.next ≤ h → m.obj? h = none)
    (hnd0 : (m.objs.map (·.1)).Nodup)
    (htn : ∀ y h, m.tableOf y = some h → ∃ o, m.obj? h = some o ∧ o.node = y)
    (hnd : (c.new.map (·.id)).Nodup)
    (hnew : ∀ nn ∈ c.new, newest S (lastSp S) nn.id = none → S.lv nn.id = none)
    (hcopy : ∀ a ∈ c.adds, ∀ y ∈ sp.ptrs a.2, ((c.new.foldl addNew m).canonicalOf y).isSome ∨
      ∃ q ∈ (c.new.foldl addNew m).objs, q.2.canonical = true ∧ (q.2.slot? y).isSome) :
    RInv sp S (m.applyChange sp P j c) := by
  have hf := applyFacts sp P j c m
  have hnd1 := foldl_addNew_nodup c.new m hfr hnd0
  -- The objects after the new nodes: m's, and the new nodes' (without slots).
  have hcls := foldl_addNew_obj c.new hnd m hfr
  have hold1 : ∀ h, h < m.next → (c.new.foldl addNew m).obj? h = m.obj? h :=
    fun h hh => foldl_addNew_old c.new m h hh
  -- A slot of an object after the new nodes is a slot of an object of m.
  have hsrc : ∀ q ∈ (c.new.foldl addNew m).objs, ∀ z sl, q.2.slot? z = some sl →
      ∃ h o, m.obj? h = some o ∧ o.slot? z = some sl := by
    intro q hq z sl hz
    have hq1 := obj?_of_mem_objs hnd1 hq
    rcases hcls q.1 q.2 hq1 with ⟨-, h2⟩ | ⟨-, nn, -, hon, -⟩
    · exact ⟨q.1, q.2, h2, hz⟩
    · rw [hon] at hz; simp [newObj, Obj.slot?] at hz
  -- The node table after the new nodes names objects of their node.
  have htn1 : ∀ z h, (c.new.foldl addNew m).tableOf z = some h →
      ∃ o, (c.new.foldl addNew m).obj? h = some o ∧ o.node = z := by
    intro z h ht
    by_cases hzn : z ∈ c.new.map (·.id)
    · obtain ⟨nn, hnn, rfl⟩ := List.mem_map.mp hzn
      obtain ⟨h2, -, ht2, ho2⟩ := foldl_addNew_new c.new hnd m nn hnn
      rw [ht, Option.some.injEq] at ht2
      subst ht2
      exact ⟨newObj nn, ho2, rfl⟩
    · rw [foldl_addNew_table_old c.new m z hzn] at ht
      obtain ⟨o, ho, hn⟩ := htn z h ht
      exact ⟨o, by rw [hold1 h (lt_next_of_obj? hfr ho)]; exact ho, hn⟩
  -- The objects of the result, and what they come from.
  have hobj : ∀ h o3, (m.applyChange sp P j c).obj? h = some o3 →
      ∃ o1 L, (c.new.foldl addNew m).obj? h = some o1 ∧ o3 = updAll sp P j (c.new.foldl addNew m) L o1 := by
    intro h o3 ho3
    rw [hf.obj h] at ho3
    obtain ⟨o1, ho1, rfl⟩ := Option.map_eq_some_iff.mp ho3
    exact ⟨o1, _, ho1, rfl⟩
  -- An object of m keeps its node in the result.
  have hkeep : ∀ h o, m.obj? h = some o → ∃ o3, (m.applyChange sp P j c).obj? h = some o3 ∧ o3.node = o.node := by
    intro h o ho
    rw [hf.obj h, hold1 h (lt_next_of_obj? hfr ho), ho]
    exact ⟨_, rfl, (updAll_core sp P j _ _ o).1⟩
  -- A stream slot of the result is a stream slot of an object of m.
  have hstr : ∀ h o3, (m.applyChange sp P j c).obj? h = some o3 → ∀ z r, o3.slot? z = some (Slot.stream r) →
      ∃ h2 o2, m.obj? h2 = some o2 ∧ o2.slot? z = some (Slot.stream r) := by
    intro h o3 ho3 z r hz
    obtain ⟨o1, L, ho1, rfl⟩ := hobj h o3 ho3
    rw [updAll_slot] at hz
    split at hz
    · unfold combo NS1 at hz
      cases hcz : (c.new.foldl addNew m).canonicalOf z with
      | some h0 => rw [hcz] at hz; simp at hz
      | none =>
        rw [hcz] at hz
        simp only [Option.map_none, Option.none_or] at hz
        cases hss : srcSlot sp P j (c.new.foldl addNew m) z with
        | some sl =>
          rw [hss] at hz
          simp only [Option.some_or, Option.some.injEq] at hz
          subst hz
          unfold srcSlot at hss
          cases hfd : (c.new.foldl addNew m).objs.find? (srcOK sp P j z) with
          | none => rw [hfd] at hss; cases hss
          | some q =>
            rw [hfd] at hss
            exact hsrc q (List.mem_of_find?_eq_some hfd) z _ hss
        | none =>
          rw [hss] at hz
          simp only [Option.none_or] at hz
          cases hos : o1.slot? z with
          | some sl =>
            rw [hos] at hz
            simp only [Option.some_or, Option.some.injEq] at hz
            subst hz
            exact hsrc (h, o1) (mem_objs_of_obj? ho1) z _ hos
          | none =>
            rw [hos] at hz
            simp only [Option.none_or] at hz
            unfold anySlot at hz
            cases hfd : (c.new.foldl addNew m).objs.find? (fun p => p.2.canonical && (p.2.slot? z).isSome) with
            | none => rw [hfd] at hz; cases hz
            | some q =>
              rw [hfd] at hz
              exact hsrc q (List.mem_of_find?_eq_some hfd) z _ hz
    · exact hsrc (h, o1) (mem_objs_of_obj? ho1) z _ hz
  refine ⟨fun h o3 ho3 => ?_, fun h o3 ho3 z r hz => ?_, fun h o3 ho3 z h' hz => ?_, fun h o3 ho3 hn => ?_,
    fun h o3 ho3 z hz => ?_, fun h o3 ho3 z r hz => ?_, fun h o3 ho3 z r hz => ?_, fun h o3 ho3 z hz => ?_⟩
  · obtain ⟨o1, L, ho1, rfl⟩ := hobj h o3 ho3
    rw [(updAll_core sp P j _ L o1).2.2.2.2.1]
    rcases hcls h o1 ho1 with ⟨-, h2⟩ | ⟨-, nn, -, hon, -⟩
    · exact hr.canon h o1 h2
    · rw [hon]; rfl
  · obtain ⟨h2, o2, ho2, hs2⟩ := hstr h o3 ho3 z r hz
    exact hr.fresh h2 o2 ho2 z r hs2
  · obtain ⟨o1, L, ho1, rfl⟩ := hobj h o3 ho3
    rw [updAll_slot] at hz
    -- the memory slot names the canonical object of z, or is a slot of an object of m
    have hcase : (∃ o, (c.new.foldl addNew m).obj? h' = some o ∧ o.node = z) ∨
        ∃ h2 o2, m.obj? h2 = some o2 ∧ o2.slot? z = some (Slot.mem h') := by
      split at hz
      · unfold combo NS1 at hz
        cases hcz : (c.new.foldl addNew m).canonicalOf z with
        | some h0 =>
          rw [hcz] at hz
          simp only [Option.map_some, Option.some_or, Option.some.injEq, Slot.mem.injEq] at hz
          subst hz
          obtain ⟨ht, -⟩ := ((c.new.foldl addNew m).canonicalOf_eq_some z h0).mp hcz
          exact Or.inl (htn1 z h0 ht)
        | none =>
          rw [hcz] at hz
          simp only [Option.map_none, Option.none_or] at hz
          right
          cases hss : srcSlot sp P j (c.new.foldl addNew m) z with
          | some sl =>
            rw [hss] at hz
            simp only [Option.some_or, Option.some.injEq] at hz
            subst hz
            unfold srcSlot at hss
            cases hfd : (c.new.foldl addNew m).objs.find? (srcOK sp P j z) with
            | none => rw [hfd] at hss; cases hss
            | some q =>
              rw [hfd] at hss
              exact hsrc q (List.mem_of_find?_eq_some hfd) z _ hss
          | none =>
            rw [hss] at hz
            simp only [Option.none_or] at hz
            cases hos : o1.slot? z with
            | some sl =>
              rw [hos] at hz
              simp only [Option.some_or, Option.some.injEq] at hz
              subst hz
              exact hsrc (h, o1) (mem_objs_of_obj? ho1) z _ hos
            | none =>
              rw [hos] at hz
              simp only [Option.none_or] at hz
              unfold anySlot at hz
              cases hfd : (c.new.foldl addNew m).objs.find? (fun p => p.2.canonical && (p.2.slot? z).isSome) with
              | none => rw [hfd] at hz; cases hz
              | some q =>
                rw [hfd] at hz
                exact hsrc q (List.mem_of_find?_eq_some hfd) z _ hz
      · exact Or.inr (hsrc (h, o1) (mem_objs_of_obj? ho1) z _ hz)
    rcases hcase with ⟨o, ho, hn⟩ | ⟨h2, o2, ho2, hs2⟩
    · rw [hf.obj h', ho]
      exact ⟨_, rfl, by rw [(updAll_core sp P j _ _ o).1, hn]⟩
    · obtain ⟨o', ho', hn'⟩ := hr.memNode h2 o2 ho2 z h' hs2
      obtain ⟨o3', ho3', hn3'⟩ := hkeep h' o' ho'
      exact ⟨o3', ho3', by rw [hn3', hn']⟩
  · obtain ⟨o1, L, ho1, rfl⟩ := hobj h o3 ho3
    obtain ⟨e1, -, -, -, -, e6⟩ := updAll_core sp P j (c.new.foldl addNew m) L o1
    rw [e1] at hn
    rw [e6, e1]
    rcases hcls h o1 ho1 with ⟨-, h2⟩ | ⟨-, nn, hnn, hon, -⟩
    · exact hr.pos h o1 h2 hn
    · subst hon
      show none = (S.lv nn.id).map (·.recNo)
      rw [hnew nn hnn hn]
      rfl
  · rw [hf.obj h] at ho3
    obtain ⟨o1, ho1, rfl⟩ := Option.map_eq_some_iff.mp ho3
    obtain ⟨-, -, -, e4, -, -⟩ := updAll_core sp P j (c.new.foldl addNew m)
      (c.adds.filter (fun a => (c.new.foldl addNew m).canonicalOf a.1 == some h)) o1
    rw [e4, mem_pointees] at hz
    obtain ⟨e, he, hze⟩ := hz
    rw [updAll_slot]
    -- a pointer of a new entry gets a slot, as A-COPY provides
    have hcombo : (combo sp P j (c.new.foldl addNew m) o1 z).isSome := by
      unfold combo NS1 anySlot
      cases hcz : (c.new.foldl addNew m).canonicalOf z with
      | some h0 => simp
      | none =>
        simp only [Option.map_none, Option.none_or]
        cases hss : srcSlot sp P j (c.new.foldl addNew m) z with
        | some sl => simp
        | none =>
          simp only [Option.none_or]
          cases hos : o1.slot? z with
          | some sl => simp
          | none =>
            simp only [Option.none_or]
            rcases List.mem_append.mp he with he1 | he2
            · -- an old pointee of o1: it has a slot
              rcases hcls h o1 ho1 with ⟨-, h2⟩ | ⟨-, nn, -, hon, -⟩
              · have := hr.slotsAll h o1 h2 z ((mem_pointees sp _ z).mpr ⟨e, he1, hze⟩)
                rw [hos] at this; cases this
              · rw [hon] at he1; cases he1
            · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he2
              have haL := (List.mem_filter.mp ha).1
              rcases hcopy a haL z hze with hc | ⟨q, hq, hqc, hqs⟩
              · rw [hcz] at hc; cases hc
              · cases hfd : (c.new.foldl addNew m).objs.find? (fun p => p.2.canonical && (p.2.slot? z).isSome) with
                | none =>
                  exfalso
                  rw [List.find?_eq_none] at hfd
                  exact hfd q hq (by simp [hqc, hqs])
                | some q' =>
                  have := List.find?_some hfd
                  simp only [Bool.and_eq_true] at this
                  simpa using this.2
    split
    · exact hcombo
    · rename_i hnot
      rcases List.mem_append.mp he with he1 | he2
      · rcases hcls h o1 ho1 with ⟨-, h2⟩ | ⟨-, nn, -, hon, -⟩
        · exact hr.slotsAll h o1 h2 z ((mem_pointees sp _ z).mpr ⟨e, he1, hze⟩)
        · rw [hon] at he1; cases he1
      · exfalso
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he2
        exact hnot (List.mem_flatMap.mpr ⟨a, ha, hze⟩)
  · obtain ⟨h2, o2, ho2, hs2⟩ := hstr h o3 ho3 z (some r) hz
    exact hr.ver h2 o2 ho2 z r hs2
  · obtain ⟨h2, o2, ho2, hs2⟩ := hstr h o3 ho3 z (some r) hz
    exact hr.near h2 o2 ho2 z r hs2
  · -- a slot is an old one, for a pointee of the old history, or one for a new entry
    obtain ⟨o1, L, ho1, rfl⟩ := hobj h o3 ho3
    rw [(updAll_core sp P j _ L o1).2.2.2.1]
    rw [updAll_slot] at hz
    split at hz
    · rename_i hmem
      obtain ⟨a, ha, hza⟩ := List.mem_flatMap.mp hmem
      exact (mem_pointees sp _ z).mpr ⟨⟨j, a.2⟩, List.mem_append_right _ (List.mem_map.mpr ⟨a, ha, rfl⟩), hza⟩
    · rcases hcls h o1 ho1 with ⟨-, h2⟩ | ⟨-, nn, -, hon, -⟩
      · obtain ⟨e, he, hze⟩ := (mem_pointees sp _ z).mp (hr.keys h o1 h2 z hz)
        exact (mem_pointees sp _ z).mpr ⟨e, List.mem_append_left _ he, hze⟩
      · rw [hon] at hz; simp [newObj, Obj.slot?] at hz

end Apply

section Rerun

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

/-- The writer's walk of the rerun, node after node: both invariants. -/
theorem RInv.reachPath (hok : RunOK sp al ts) (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true)
    (hev : EvictRunOK sp al ts) {k K : Nat} (hk : k ≤ ts.length) (hKk : K < k)
    (hsK : lastSp (st sp al ts k).S ≤ K) {P : Struct V} (hP : SameNodes P (st sp al ts K).P)
    {path : List NodeId} (hpath : ∀ p ∈ path, reachable sp (st sp al ts k).P K p = true) :
    ∀ (L : List NodeId) (m : Mem V), RInv sp (st sp al ts k).S m → MemInv sp (st sp al ts k) K m →
      RInv sp (st sp al ts k).S (L.foldl (Mem.reachOnPath sp (st sp al ts k).S P (K + 1) path) m) ∧
        MemInv sp (st sp al ts k) K (L.foldl (Mem.reachOnPath sp (st sp al ts k).S P (K + 1) path) m) := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hctx := pctx_st hok hst hk
  have hkK := kctx_st sp al ts hok hj (Nat.le_of_lt hKk) hk
  intro L
  induction L with
  | nil => intro m hr hm; exact ⟨hr, hm⟩
  | cons x L ih =>
    intro m hr hm
    simp only [List.foldl_cons]
    exact ih _ (hr.reachOnPath hok hj hmk hev hk hKk hsK hm hP hpath x)
      (hm.reachOnPath_ok hctx hkK hP hpath x).1

/-- One transaction of the rerun keeps the rerun's invariant. -/
theorem RInv.rerunStep (hok : RunOK sp al ts) (hph : PhysRunOK sp al ts) (hj : al.stillDirty = javaTest sp)
    (hmk : al.mark = true) (hev : EvictRunOK sp al ts) {k K : Nat} (hk : k ≤ ts.length)
    (hsK : lastSp (st sp al ts k).S ≤ K) (hKk : K < k) {acc : Mem V × Struct V}
    (hr : RInv sp (st sp al ts k).S acc.1) (hm : MemInv sp (st sp al ts k) K acc.1)
    (hP : SameNodes acc.2 (st sp al ts K).P) :
    RInv sp (st sp al ts k).S (rerunStep sp (st sp al ts k).S acc (K + 1)).1 := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hKt : K < ts.length := by omega
  have hls : LiveSub sp := hok.1.liveSub
  have hinvK := inv_st sp al ts hok hst K (by omega)
  have hkK := kctx_st sp al ts hok hj (Nat.le_of_lt hKk) hk
  have htr := st_trans sp al ts hok hst (j := K + 1) (k := k) (by omega) (by omega) hk
  simp only [Nat.add_sub_cancel] at htr
  obtain ⟨R, hR, hRt⟩ : ∃ R, (st sp al ts k).S[K + 1]? = some R ∧ R.trans = some ts[K] := by
    cases h : (st sp al ts k).S[K + 1]? with
    | none => rw [h] at htr; cases htr
    | some R => rw [h] at htr; exact ⟨R, rfl, htr⟩
  rw [rerunStep_eq sp _ acc hR hRt]
  simp only [Nat.add_sub_cancel]
  have hm2 := rerun_apply_ok hok hph hj hk hKk hm hP (tr := ts[K]) (List.getElem?_eq_getElem hKt)
  rw [foldl_canonicalNode_noop sp _ _ R.gd
    (fun x hx => hm2.coverGd (K + 1) R x (by omega) (Nat.le_refl _) hR hx)]
  -- The change, and its new nodes.
  have hlenK := st_len sp al ts hok hst (j := K) (by omega)
  have hc : sp.exec ts[K] (K + 1) (view sp acc.2 K) = (parts sp al (st sp al ts K) ts[K]).c := by
    rw [parts_c, hlenK, Nat.add_sub_cancel, hP.view K]
  have hstep : StepOK sp (st sp al ts K).P (K + 1) (parts sp al (st sp al ts K) ts[K]).c := by
    rw [parts_c, hlenK, Nat.add_sub_cancel]
    exact hok.2 K hKt
  -- The walk.
  have hpath : ∀ p ∈ pathOf sp acc.2 (sp.exec ts[K] (K + 1) (view sp acc.2 K)) (K + 1),
      reachable sp (st sp al ts k).P K p = true := by
    intro p hp
    have := (mem_pathOf hp).1
    rw [Nat.add_sub_cancel, hP.reachable] at this
    rw [hkK.reachable_eq hls (Nat.le_refl K)]
    exact this
  obtain ⟨hr1, hm1⟩ := RInv.reachPath hok hj hmk hev hk hKk hsK hP hpath
    ((pathOf sp acc.2 (sp.exec ts[K] (K + 1) (view sp acc.2 K)) (K + 1)).mergeSort
      (fun a b => decide (lev acc.2 b ≤ lev acc.2 a))) acc.1 hr hm
  -- The change applied.
  apply hr1.applyChange hm1.fresh hm1.nodup hm1.tbl
  · rw [hc]; exact hstep.distinct
  · intro nn hnn hn
    rw [hc] at hnn
    cases hl : (st sp al ts k).S.lv nn.id with
    | none => rfl
    | some v =>
      exfalso
      obtain ⟨r, hr'⟩ := lv_versionAt hl
      by_cases hrs : lastSp (st sp al ts k).S ≤ r
      · exact newest_some_of_versionAt hr' hrs hn
      · -- a version before the section is in the stream after T(K): its node was in P then
        have hrK : (st sp al ts K).S.versionAt r nn.id = some v := by
          rw [st_S_take hok hst (Nat.le_of_lt hKk) hk, versionAt_take]
          simp only [show r < K + 1 by omega, ↓reduceIte]; exact hr'
        obtain ⟨hvn, -, n, hn', -⟩ := hinvK.version_node hrK
        have := hstep.fresh nn hnn
        rw [hn'] at this; cases this
  · -- A-COPY: a new pointer names a new node, a node of the paths (canonical after the
    -- walk), or a pointee of one, whose object has a slot for it.
    have hctx := pctx_st hok hst hk
    have hparent : ∀ x ∈ pathOf sp acc.2 (sp.exec ts[K] (K + 1) (view sp acc.2 K)) (K + 1), x ≠ SIS.root →
        ∃ p ∈ pathOf sp acc.2 (sp.exec ts[K] (K + 1) (view sp acc.2 K)) (K + 1), ∃ np nx,
          acc.2.get? p = some np ∧ acc.2.get? x = some nx ∧ nx.level < np.level ∧
          x ∈ sp.live (np.hist.upTo K) := by
      intro x hx hxr
      obtain ⟨p, np, nx, hrp, hnp, hnx, hlt, hxl⟩ := reach_parent (mem_pathOf hx).1 hxr
      refine ⟨p, pathOf_parent hx hrp hnp hxl hnx hlt, np, nx, hnp, hnx, hlt, ?_⟩
      simpa using hxl
    obtain ⟨-, -, hcan1⟩ := MemInv.reachPath_ok hctx hkK hP hpath hparent
      ((pathOf sp acc.2 (sp.exec ts[K] (K + 1) (view sp acc.2 K)) (K + 1)).mergeSort
        (fun a b => decide (lev acc.2 b ≤ lev acc.2 a))) [] acc.1 hm (by simp)
      (fun x => by rw [List.nil_append]; exact (List.mergeSort_perm _ _).mem_iff)
      (by rw [List.nil_append]; exact pairwise_byLevelDesc _ _)
    have hcopyK : CopyStep sp (st sp al ts K).P (K + 1) (parts sp al (st sp al ts K) ts[K]).c := by
      rw [parts_c, hlenK, Nat.add_sub_cancel]; exact hev.2 K hKt
    have hpe : ∀ y, y ∈ pathOf sp (st sp al ts K).P (parts sp al (st sp al ts K) ts[K]).c (K + 1) →
        y ∈ pathOf sp acc.2 (sp.exec ts[K] (K + 1) (view sp acc.2 K)) (K + 1) := by
      intro y hy; rw [hc, pathOf_congr hP]; exact hy
    generalize hmw : (((pathOf sp acc.2 (sp.exec ts[K] (K + 1) (view sp acc.2 K)) (K + 1)).mergeSort
        (fun a b => decide (lev acc.2 b ≤ lev acc.2 a))).foldl
        (Mem.reachOnPath sp (st sp al ts k).S acc.2 (K + 1)
          (pathOf sp acc.2 (sp.exec ts[K] (K + 1) (view sp acc.2 K)) (K + 1))) acc.1) = mw at hr1 hm1 hcan1 ⊢
    intro a ha y hy
    rw [hc] at ha ⊢
    have hfr1 := hm1.fresh
    by_cases hyn : y ∈ (parts sp al (st sp al ts K) ts[K]).c.new.map (·.id)
    · left
      obtain ⟨nn, hnn, rfl⟩ := List.mem_map.mp hyn
      obtain ⟨h0, -, hc0, -⟩ := addNew_canonicalOf_new (V := V) mw _ hstep.distinct hnn
      rw [hc0]; rfl
    · rcases hcopyK a ha y hy hyn with hyp | ⟨z, hz, nz, hnz, hyz, -⟩
      · left
        rw [addNew_canonicalOf_old _ _ hfr1 (fun y h ht => by
          obtain ⟨o, ho, -⟩ := hm1.tbl y h ht; rw [ho]; rfl) hyn]
        exact Option.ne_none_iff_isSome.mp (hcan1 y (hpe y hyp))
      · right
        obtain ⟨hz0, hcz⟩ := Option.ne_none_iff_exists'.mp (hcan1 z (hpe z hz))
        obtain ⟨htz, oz, hoz, hcoz⟩ := (Mem.canonicalOf_eq_some _ z hz0).mp hcz
        obtain ⟨oz', hoz', hnoz⟩ := hm1.tbl z hz0 htz
        rw [hoz, Option.some.injEq] at hoz'
        subst hoz'
        obtain ⟨-, ⟨nk, hnk, hhk, -, -⟩, -⟩ := hm1.canon hz0 oz hoz hcoz
        rw [hnoz] at hnk
        obtain ⟨nk', hnk', -, -, hup⟩ := hkK.grow z nz hnz
        rw [hnk, Option.some.injEq] at hnk'
        subst hnk'
        have hzh : oz.hist = nz.hist := by
          rw [hhk, hup, upTo_of_forall _ _ (hinvK.times z nz hnz)]
        have hsl := hr1.slotsAll hz0 oz hoz y (by rw [hzh]; exact hyz)
        refine ⟨(hz0, oz), mem_objs_of_obj? ?_, hcoz, hsl⟩
        rw [foldl_addNew_old _ _ hz0 (lt_next_of_obj? hfr1 hoz)]
        exact hoz

/-- The startup's memory, after the rerun, meets the rerun's invariant. -/
theorem rinv_lazyStartup (hok : RunOK sp al ts) (hph : PhysRunOK sp al ts) (hj : al.stillDirty = javaTest sp)
    (hmk : al.mark = true) (hev : EvictRunOK sp al ts) {k : Nat} (hk : k ≤ ts.length) :
    RInv sp (st sp al ts k).S (lazyStartup sp (st sp al ts k).S) ∧
      MemInv sp (st sp al ts k) k (lazyStartup sp (st sp al ts k).S) := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hinv := inv_st sp al ts hok hst k hk
  have hctx := pctx_st hok hst hk
  have hsk : lastSp (st sp al ts k).S ≤ k := by have := hinv.spLt; omega
  have hkS := kctx_st sp al ts hok hj hsk hk
  have hm0 := hctx.base_ok hkS
  have hP0 := base_sameNodes sp al ts hok hst hk
  have hr0 := rinv_lazyBase hok hj hmk hev hk
  refine ⟨?_, lazy_ok hok hph hj hk⟩
  rw [lazyStartup_eq]
  generalize hs : lastSp (st sp al ts k).S = s at hm0 hP0 hsk hr0
  have hidx : sectionIdx (st sp al ts k).S s = List.range' (s + 1) (k - s) := by
    simp [sectionIdx, hinv.len]
  rw [hidx]
  have key : ∀ n, n ≤ k - s →
      RInv sp (st sp al ts k).S ((List.range' (s + 1) n).foldl (rerunStep sp (st sp al ts k).S)
          (lazyBase sp (st sp al ts k).S, baseStruct sp (st sp al ts k).S s true)).1 ∧
        MemInv sp (st sp al ts k) (s + n)
          ((List.range' (s + 1) n).foldl (rerunStep sp (st sp al ts k).S)
            (lazyBase sp (st sp al ts k).S, baseStruct sp (st sp al ts k).S s true)).1 ∧
        SameNodes ((List.range' (s + 1) n).foldl (rerunStep sp (st sp al ts k).S)
            (lazyBase sp (st sp al ts k).S, baseStruct sp (st sp al ts k).S s true)).2
          (st sp al ts (s + n)).P := by
    intro n
    induction n with
    | zero => intro _; exact ⟨hr0, hm0, hP0⟩
    | succ n ih =>
      intro hn
      rw [List.range'_concat, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, Nat.one_mul]
      obtain ⟨h0, h1, h2⟩ := ih (by omega)
      have hsK : lastSp (st sp al ts k).S ≤ s + n := by rw [hs]; omega
      have := rerunStep_ok hok hph hj hk (K := s + n) hsK (by omega) h1 h2
      have hr' := RInv.rerunStep hok hph hj hmk hev hk (K := s + n) hsK (by omega) h0 h1 h2
      rw [show s + 1 + n = s + n + 1 by omega, show s + (n + 1) = s + n + 1 by omega]
      exact ⟨hr', this⟩
  exact (key (k - s) (Nat.le_refl _)).1

end Rerun

/-! ## The node table has no repeated keys after the startup -/

section Table

/-- The node table's keys have no repeats. -/
def TblND (m : Mem V) : Prop := (m.table.map (·.1)).Nodup

theorem TblND.setObj {m : Mem V} (h : TblND m) (hp : Nat) (o : Obj V) : TblND (m.setObj hp o) := h

theorem TblND.addObj {m : Mem V} (h : TblND m) (o : Obj V) : TblND (m.addObj o).1 := h

theorem TblND.setTable {m : Mem V} (h : TblND m) (y : NodeId) (hp : Nat) : TblND (m.setTable y hp) :=
  setTable_nodup m y hp h

theorem TblND.register {m : Mem V} (h : TblND m) (h1 : Nat) : TblND (m.register h1).1 := by
  unfold Mem.register
  split
  · exact h
  · split
    · exact h.setTable _ _
    · split
      · exact h
      · split
        · split
          · exact h.setTable _ _
          · exact h
        · exact h.setTable _ _

theorem TblND.makeCanonical {m : Mem V} (h : TblND m) (hp : Nat) (y : NodeId) (h1 : Nat) :
    TblND (m.makeCanonical hp y h1).1 := by
  unfold Mem.makeCanonical
  simp only
  split <;> split <;>
    first | exact h | exact h.setObj _ _ | exact (h.setObj _ _).setTable _ _ |
      exact ((h.setObj _ _).setTable _ _).setObj _ _

theorem TblND.follow {m : Mem V} (h : TblND m) (sp : Spec V T) (S : Stream V T) (hp : Nat) (y : NodeId)
    (w : Bool) : TblND (m.follow sp S hp y w).1 := by
  unfold Mem.follow
  split
  · exact h
  · split
    · split
      · exact h.makeCanonical _ _ _
      · exact h
    · exact h
  · simp only
    split
    · exact h
    · rename_i m1 h1 hl
      have hm1 : TblND m1 := by
        split at hl
        · simp only [Option.some.injEq, Prod.mk.injEq] at hl
          obtain ⟨rfl, -⟩ := hl
          exact h
        · split at hl
          · cases hl
          · split at hl
            · cases hl
            · simp only [Option.some.injEq] at hl
              have key := congrArg Prod.fst hl
              simp only at key
              rw [← key]
              exact (h.addObj _).register _
      have hm2 : TblND (match m1.obj? hp with
          | some op => m1.setObj hp (op.setSlot y (Slot.mem h1))
          | none => m1) := by
        split
        · exact hm1.setObj _ _
        · exact hm1
      split
      · split
        · exact hm2.makeCanonical _ _ _
        · exact hm2
      · exact hm2

theorem TblND.reachOnPath {m : Mem V} (h : TblND m) (sp : Spec V T) (S : Stream V T) (P : Struct V)
    (j : Time) (path : List NodeId) (x : NodeId) : TblND (m.reachOnPath sp S P j path x) := by
  unfold Mem.reachOnPath
  split
  · exact h
  · simp only
    split
    · split
      · exact h.follow _ _ _ _ _
      · exact h
    · exact h

theorem TblND.applyChange {m : Mem V} (h : TblND m) (sp : Spec V T) (P : Struct V) (j : Time)
    (c : Changes V) : TblND (m.applyChange sp P j c) := by
  have hf := applyFacts sp P j c m
  have h1 : TblND (c.new.foldl addNew m) := by
    have key : ∀ (L : List NewNode) (m : Mem V), TblND m → TblND (L.foldl addNew m) := by
      intro L
      induction L with
      | nil => intro m h; exact h
      | cons nn L ih => intro m h; exact ih _ ((h.addObj _).setTable _ _)
    exact key _ _ h
  have ht : (m.applyChange sp P j c).table = (c.new.foldl addNew m).table := by
    have := applyChange_eq sp P j m c
    rw [this]
    have key : ∀ (L : List (NodeId × V)) (m' : Mem V),
        (L.foldl (addsStep sp P j (c.new.foldl addNew m)) m').table = m'.table := by
      intro L
      induction L with
      | nil => intro m'; rfl
      | cons a L ih =>
        intro m'
        simp only [List.foldl_cons]
        rw [ih]
        unfold addsStep
        split
        · rfl
        · split
          · rfl
          · rfl
    exact key _ _
  unfold TblND
  rw [ht]
  exact h1

theorem TblND.canonicalNode {m : Mem V} (h : TblND m) (sp : Spec V T) (S : Stream V T) (x : NodeId) :
    TblND (m.canonicalNode sp S x) := by
  unfold Mem.canonicalNode
  split
  · exact h
  · split
    · exact (h.addObj _).setTable _ _
    · exact h

theorem TblND.rerunStep {acc : Mem V × Struct V} (h : TblND acc.1) (sp : Spec V T) (S : Stream V T)
    (j : Nat) : TblND (SIS.rerunStep sp S acc j).1 := by
  unfold SIS.rerunStep
  split
  · split
    · simp only
      have hw : ∀ (L : List NodeId) (m : Mem V), TblND m → ∀ P path, TblND (L.foldl
          (Mem.reachOnPath sp S P j path) m) := by
        intro L
        induction L with
        | nil => intro m h _ _; exact h
        | cons x L ih => intro m h P path; exact ih _ (h.reachOnPath _ _ _ _ _ _) P path
      have hc : ∀ (L : List NodeId) (m : Mem V), TblND m → TblND (L.foldl (Mem.canonicalNode sp S) m) := by
        intro L
        induction L with
        | nil => intro m h; exact h
        | cons x L ih => intro m h; exact ih _ (h.canonicalNode _ _ _)
      exact hc _ _ ((hw _ _ h _ _).applyChange _ _ _ _)
    · exact h
  · exact h

theorem tblND_lazyStartup (sp : Spec V T) (S : Stream V T) : TblND (lazyStartup sp S) := by
  rw [lazyStartup_eq]
  have h0 : TblND (lazyBase sp S) := lazyRoot_tblNodup sp S _ (lazySec_tblNodup sp S)
  have key : ∀ (L : List Nat) (acc : Mem V × Struct V), TblND acc.1 → TblND (L.foldl (rerunStep sp S) acc).1 := by
    intro L
    induction L with
    | nil => intro acc h; exact h
    | cons j L ih => intro acc h; exact ih _ (TblND.rerunStep h _ _ _)
  exact key _ _ h0

end Table

/-- No two slots of object o are for the same pointee. -/
def Obj.KeysND (o : Obj V) : Prop := (o.slots.map (·.1)).Nodup

/-- No object in memory has two slots for the same pointee. -/
def SlotsND (m : Mem V) : Prop := ∀ p ∈ m.objs, p.2.KeysND

theorem keys_map_fst (l : List (NodeId × Slot)) {f : NodeId × Slot → NodeId × Slot}
    (hf : ∀ q, (f q).1 = q.1) : (l.map f).map (·.1) = l.map (·.1) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro q _
  exact hf q

theorem Obj.KeysND.of_slots {o o' : Obj V} (h : o.KeysND) {f : NodeId × Slot → NodeId × Slot}
    (hf : ∀ q, (f q).1 = q.1) (he : o'.slots = o.slots.map f) : o'.KeysND := by
  unfold Obj.KeysND at *
  rw [he, keys_map_fst _ hf]
  exact h

theorem Obj.KeysND.setSlot {o : Obj V} (h : o.KeysND) (y : NodeId) (sl : Slot) :
    (o.setSlot y sl).KeysND := by
  apply h.of_slots (f := fun p => if p.1 == y then (y, sl) else p) _ rfl
  intro q
  split
  · rename_i hq; exact (beq_iff_eq.mp hq).symm
  · rfl

theorem Obj.KeysND.putSlot {o : Obj V} (h : o.KeysND) (y : NodeId) (sl : Slot) :
    (o.putSlot y sl).KeysND := by
  unfold Obj.putSlot
  split
  · exact h.setSlot y sl
  · rename_i hy
    unfold Obj.KeysND at *
    simp only [List.map_append, List.map_cons, List.map_nil]
    rw [List.nodup_append]
    refine ⟨h, List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩, ?_⟩
    intro a ha b hb hab
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    subst hb
    subst hab
    exact hy (lookup_isSome_of_mem ha)

theorem Obj.KeysND.of_ofVersion (sp : Spec V T) (w : Version V) (cut : Option Nat) :
    (Obj.ofVersion sp w cut).KeysND := by
  unfold Obj.KeysND Obj.ofVersion
  simp only [List.map_map]
  have : ((·.1) ∘ fun y => (y, Slot.stream (w.ref? y))) = (id : NodeId → NodeId) := by
    funext y; rfl
  rw [this, List.map_id]
  exact nodup_eraseDups _

theorem Obj.KeysND.of_canonOfVersion (sp : Spec V T) (S : Stream V T) (s : Nat) (w : Version V) :
    (canonOfVersion sp S s w).KeysND := by
  unfold SIS.canonOfVersion
  apply (Obj.KeysND.of_ofVersion sp w _).of_slots (f := fun p => match p.2 with
    | Slot.stream r => (p.1, Slot.stream (ruleRRef S s p.1 r))
    | sl => (p.1, sl)) _ rfl
  intro q
  split <;> rfl

theorem Obj.KeysND.nil (o : Obj V) (h : o.slots = []) : o.KeysND := by
  unfold Obj.KeysND; rw [h]; exact List.nodup_nil

theorem SlotsND.obj {m : Mem V} (hm : SlotsND m) {h : Nat} {o : Obj V} (ho : m.obj? h = some o) :
    o.KeysND :=
  hm (h, o) (mem_of_lookup m.objs h o ho)

theorem SlotsND.setObj {m : Mem V} (hm : SlotsND m) (h : Nat) {o : Obj V} (ho : o.KeysND) :
    SlotsND (m.setObj h o) := by
  intro p hp
  unfold Mem.setObj at hp
  simp only [List.mem_cons, List.mem_filter] at hp
  rcases hp with rfl | ⟨hp, -⟩
  · exact ho
  · exact hm p hp

theorem SlotsND.addObj {m : Mem V} (hm : SlotsND m) {o : Obj V} (ho : o.KeysND) :
    SlotsND (m.addObj o).1 := by
  intro p hp
  unfold Mem.addObj at hp
  simp only [List.mem_cons] at hp
  rcases hp with rfl | hp
  · exact ho
  · exact hm p hp

theorem SlotsND.setTable {m : Mem V} (hm : SlotsND m) (y : NodeId) (h : Nat) : SlotsND (m.setTable y h) :=
  hm

/-- A memory whose objects are m's, each with its slots mapped pointee by
pointee. -/
theorem SlotsND.map_objs {m m' : Mem V} (hm : SlotsND m) {f : Nat × Obj V → Nat × Obj V}
    (he : m'.objs = m.objs.map f) (hf : ∀ p ∈ m.objs, (f p).2.slots.map (·.1) = p.2.slots.map (·.1)) :
    SlotsND m' := by
  intro p hp
  rw [he, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  unfold Obj.KeysND
  rw [hf q hq]
  exact hm q hq

/-- The object at h made canonical and the table's for y. -/
theorem SlotsND.canonical {m : Mem V} (hm : SlotsND m) (h : Nat) (y : NodeId) :
    SlotsND (match m.obj? h with
      | some o => (m.setObj h { o with canonical := true }).setTable y h
      | none => m) := by
  split
  · rename_i o ho
    have hk : o.KeysND := hm.obj ho
    exact (hm.setObj h (o := { o with canonical := true }) hk).setTable _ _
  · exact hm

/-- The slot of object hp for y set to a memory slot. -/
theorem SlotsND.link {m : Mem V} (hm : SlotsND m) (hp : Nat) (y : NodeId) (h : Nat) :
    SlotsND (match m.obj? hp with
      | some op => m.setObj hp (op.setSlot y (Slot.mem h))
      | none => m) := by
  split
  · rename_i op hop
    exact hm.setObj _ ((hm.obj hop).setSlot _ _)
  · exact hm

theorem SlotsND.register {m : Mem V} (hm : SlotsND m) (h1 : Nat) : SlotsND (m.register h1).1 := by
  unfold Mem.register
  split
  · exact hm
  · split
    · exact hm.setTable _ _
    · split
      · exact hm
      · split
        · split
          · exact hm.setTable _ _
          · exact hm
        · exact hm.setTable _ _

theorem SlotsND.makeCanonical {m : Mem V} (hm : SlotsND m) (hp : Nat) (y : NodeId) (h1 : Nat) :
    SlotsND (m.makeCanonical hp y h1).1 := by
  unfold Mem.makeCanonical
  exact (hm.canonical _ y).link hp y _

theorem SlotsND.follow {m : Mem V} (hm : SlotsND m) (sp : Spec V T) (S : Stream V T) (hp : Nat)
    (y : NodeId) (w : Bool) : SlotsND (m.follow sp S hp y w).1 := by
  unfold Mem.follow
  split
  · exact hm
  · split
    · split
      · exact hm.makeCanonical _ _ _
      · exact hm
    · exact hm
  · simp only
    split
    · exact hm
    · rename_i m1 h1 hl
      have hm1 : SlotsND m1 := by
        split at hl
        · simp only [Option.some.injEq, Prod.mk.injEq] at hl
          obtain ⟨rfl, -⟩ := hl
          exact hm
        · split at hl
          · cases hl
          · split at hl
            · cases hl
            · simp only [Option.some.injEq] at hl
              have key := congrArg Prod.fst hl
              simp only at key
              rw [← key]
              exact (hm.addObj (Obj.KeysND.of_ofVersion _ _ _)).register _
      have hm2 := hm1.link hp y h1
      split
      · split
        · exact hm2.makeCanonical _ _ _
        · exact hm2
      · exact hm2

theorem SlotsND.reachOnPath {m : Mem V} (hm : SlotsND m) (sp : Spec V T) (S : Stream V T) (P : Struct V)
    (j : Time) (path : List NodeId) (x : NodeId) : SlotsND (m.reachOnPath sp S P j path x) := by
  unfold Mem.reachOnPath
  split
  · exact hm
  · simp only
    split
    · split
      · exact hm.follow _ _ _ _ _
      · exact hm
    · exact hm

theorem Obj.KeysND.upd1 {o : Obj V} (h : o.KeysND) (sp : Spec V T) (P : Struct V) (j : Time) (m1 : Mem V)
    (y : NodeId) : (upd1 sp P j m1 o y).KeysND := by
  unfold SIS.upd1
  split
  · exact h.putSlot _ _
  · exact h

theorem Obj.KeysND.updObj {o : Obj V} (h : o.KeysND) (sp : Spec V T) (P : Struct V) (j : Time) (m1 : Mem V)
    (v : V) : (updObj sp P j m1 o v).KeysND := by
  unfold SIS.updObj
  have key : ∀ (L : List NodeId) (o' : Obj V), o'.KeysND → (L.foldl (SIS.upd1 sp P j m1) o').KeysND := by
    intro L
    induction L with
    | nil => intro o' h'; exact h'
    | cons y L ih => intro o' h'; exact ih _ (h'.upd1 sp P j m1 y)
  exact key _ _ h

theorem SlotsND.addNew {m : Mem V} (hm : SlotsND m) (nn : NewNode) : SlotsND (SIS.addNew m nn) :=
  (hm.addObj (Obj.KeysND.nil _ rfl)).setTable _ _

theorem SlotsND.foldl_addNew {m : Mem V} (hm : SlotsND m) (L : List NewNode) :
    SlotsND (L.foldl SIS.addNew m) := by
  induction L generalizing m with
  | nil => exact hm
  | cons nn L ih => exact ih (hm.addNew nn)

theorem SlotsND.applyChange {m : Mem V} (hm : SlotsND m) (sp : Spec V T) (P : Struct V) (j : Time)
    (c : Changes V) : SlotsND (m.applyChange sp P j c) := by
  rw [applyChange_eq]
  have key : ∀ (L : List (NodeId × V)) (m' : Mem V), SlotsND m' →
      SlotsND (L.foldl (SIS.addsStep sp P j (c.new.foldl SIS.addNew m)) m') := by
    intro L
    induction L with
    | nil => intro m' h'; exact h'
    | cons a L ih =>
      intro m' h'
      apply ih
      unfold SIS.addsStep
      split
      · exact h'
      · split
        · exact h'
        · rename_i o ho
          exact h'.setObj _ ((h'.obj ho).updObj sp P j _ a.2)
  exact key _ _ (hm.foldl_addNew _)

theorem SlotsND.canonicalNode {m : Mem V} (hm : SlotsND m) (sp : Spec V T) (S : Stream V T) (x : NodeId) :
    SlotsND (m.canonicalNode sp S x) := by
  unfold Mem.canonicalNode
  split
  · exact hm
  · split
    · exact (hm.addObj (Obj.KeysND.of_canonOfVersion _ _ _ _)).setTable _ _
    · exact hm

theorem SlotsND.rerunStep {acc : Mem V × Struct V} (h : SlotsND acc.1) (sp : Spec V T) (S : Stream V T)
    (j : Nat) : SlotsND (SIS.rerunStep sp S acc j).1 := by
  unfold SIS.rerunStep
  split
  · split
    · simp only
      have hw : ∀ (L : List NodeId) (m : Mem V), SlotsND m → ∀ P path, SlotsND (L.foldl
          (Mem.reachOnPath sp S P j path) m) := by
        intro L
        induction L with
        | nil => intro m h _ _; exact h
        | cons x L ih => intro m h P path; exact ih _ (h.reachOnPath _ _ _ _ _ _) P path
      have hc : ∀ (L : List NodeId) (m : Mem V), SlotsND m → SlotsND (L.foldl (Mem.canonicalNode sp S) m) := by
        intro L
        induction L with
        | nil => intro m h; exact h
        | cons x L ih => intro m h; exact ih _ (h.canonicalNode _ _ _)
      exact hc _ _ ((hw _ _ h _ _).applyChange _ _ _ _)
    · exact h
  · exact h

theorem slotsND_lazySec (sp : Spec V T) (S : Stream V T) : SlotsND (lazySec sp S) := by
  unfold lazySec
  have key : ∀ (L : List NodeId) (m : Mem V), SlotsND m → SlotsND (L.foldl (secStep sp S) m) := by
    intro L
    induction L with
    | nil => intro m h; exact h
    | cons x L ih =>
      intro m h
      apply ih
      unfold secStep
      split
      · split
        · exact h
        · exact (h.addObj (Obj.KeysND.of_canonOfVersion _ _ _ _)).setTable _ _
      · exact h
  exact key _ _ (fun p hp => by cases hp)

theorem SlotsND.lazyRoot {m : Mem V} (hm : SlotsND m) (sp : Spec V T) (S : Stream V T) :
    SlotsND (SIS.lazyRoot sp S m) := by
  unfold SIS.lazyRoot
  by_cases hv : sp.virt = true
  · simp only [hv, ↓reduceIte]
    exact (hm.addObj (o := { (canonOfVersion sp S (lastSp S) (rootVersion sp (lastSp S)
      (topsRead sp S (lastSp S) true))) with hist := (rootVersion sp (lastSp S)
      (topsRead sp S (lastSp S) true)).hist, pos := none })
      (Obj.KeysND.of_canonOfVersion _ _ _ _)).setTable SIS.root m.next
  · simp only [hv, Bool.false_eq_true, ↓reduceIte]
    cases hc : m.canonicalOf root with
    | some h0 => exact hm
    | none =>
      simp only
      cases ht : topVersion S (lastSp S) true with
      | none => exact hm
      | some w => exact (hm.addObj (Obj.KeysND.of_canonOfVersion sp S (lastSp S) w)).setTable SIS.root m.next

theorem SlotsND.linkCanonical {m : Mem V} (hm : SlotsND m) : SlotsND m.linkCanonical := by
  apply hm.map_objs rfl
  intro p _
  dsimp only
  split
  · rfl
  · apply keys_map_fst
    intro q
    split
    · split
      · split
        · split <;> rfl
        · rfl
      · rfl
    · rfl

/-- The positions of the section keep the slots. -/
theorem SlotsND.sectionPos {m : Mem V} (hm : SlotsND m) (S : Stream V T) : SlotsND (m.sectionPos S) := by
  apply hm.map_objs rfl
  intro p _
  dsimp only
  split
  · rfl
  · split <;> rfl

theorem slotsND_lazyStartup (sp : Spec V T) (S : Stream V T) : SlotsND (lazyStartup sp S) := by
  rw [lazyStartup_eq]
  have h0 : SlotsND (lazyBase sp S) := ((slotsND_lazySec sp S).lazyRoot sp S).linkCanonical
  have key : ∀ (L : List Nat) (acc : Mem V × Struct V), SlotsND acc.1 →
      SlotsND (L.foldl (rerunStep sp S) acc).1 := by
    intro L
    induction L with
    | nil => intro acc h; exact h
    | cons j L ih => intro acc h; exact ih _ (SlotsND.rerunStep h _ _ _)
  exact key _ _ h0

/-- Rule R on a stream cut at or before the startup pos is Rule R on the whole
stream. -/
theorem ruleRRef_cut {S0 : Stream V T} {c s : Nat} (h : c ≤ s) (y : NodeId) (r : Option Nat) :
    ruleRRef (cutStream c S0) s y r = ruleRRef S0 s y r := by
  unfold ruleRRef; rw [newest_cut h]

end SIS
