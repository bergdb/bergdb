/-
Proofs about the physical layer with handles (bergdb item 009, step 2d), part 3:
the readers' follow keeps the invariant, step by step: the raised reference
written back into the pointer (record-neutral), the live handle, the load.
-/
import SIS.Proof.HandleInv

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## The slow path's reference -/

/-- The slow path's reference for pointer p to y: its reference after Rule R,
raised to the written position of the handle it holds (`HMem.followR`). -/
def HMem.slowRef (S0 : Stream V T) (m : HMem V) (y : NodeId) (p : HPtr) : Option Nat :=
  maxRef (ruleRRef S0 m.s y p.ref) ((p.handle.bind m.handle?).bind (·.written))

/-- Writing the slow path's reference back into the pointer changes nothing
that the record rule gives (choice 1 of Handle.lean). -/
theorem HMem.ptrRef_slowRef (m : HMem V) (S0 : Stream V T) (y : NodeId) (p : HPtr) :
    m.ptrRef S0 y { p with ref := m.slowRef S0 y p } = m.ptrRef S0 y p := by
  unfold HMem.ptrRef HMem.slowRef
  simp only
  cases hh : p.handle.bind m.handle? with
  | none =>
    simp only [Option.bind_none, maxRef_none]
    exact ruleRRef_idem S0 m.s y p.ref
  | some hd =>
    simp only [Option.bind_some]
    rw [ruleRRef_maxRef, maxRef_idem]

/-- The slow path's reference is a Rule R fixed point. -/
theorem HMem.ruleR_slowRef (m : HMem V) (S0 : Stream V T) (y : NodeId) (p : HPtr) :
    ruleRRef S0 m.s y (m.slowRef S0 y p) = m.slowRef S0 y p := by
  unfold HMem.slowRef
  exact ruleRRef_maxRef S0 m.s y p.ref _

/-- The slow path's reference is at least the reference after Rule R. -/
theorem HMem.slowRef_ge (m : HMem V) (S0 : Stream V T) (y : NodeId) (p : HPtr) {r : Nat}
    (h : ruleRRef S0 m.s y p.ref = some r) : ∃ r', m.slowRef S0 y p = some r' ∧ r ≤ r' := by
  unfold HMem.slowRef
  exact maxRef_ge_left h

section WriteBack

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : HMem V}

/-- The slow path's reference names a version of y. -/
theorem HEInv.slowRef_ver (hinv : Inv sp db k) (hm : HEInv sp db S0 k m) {a : Nat} {o : HObj V}
    {y : NodeId} {p : HPtr} (ho : m.obj? a = some o) (hp : o.ptr? y = some p) {r : Nat}
    (hr : m.slowRef S0 y p = some r) : ∃ u, db.S.versionAt r y = some u := by
  unfold HMem.slowRef at hr
  rcases maxRef_cases _ _ r hr with h | h
  · exact (hinv.ruleR_bound hm.pre m.s (fun r' h' => hm.rver a o y p r' ho hp h') h).1
  · cases hpn : p.handle with
    | none => rw [hpn] at h; cases h
    | some n =>
      rw [hpn] at h
      simp only [Option.bind_some] at h
      cases hh : m.handle? n with
      | none => rw [hh] at h; cases h
      | some hd =>
        rw [hh] at h
        simp only [Option.bind_some] at h
        obtain ⟨u, hu⟩ := hm.wver n hd r hh h
        obtain ⟨hd', hh', hn'⟩ := hm.tbl.ptrNode ho hp hpn
        rw [hh, Option.some.injEq] at hh'
        subst hh'
        rw [hn'] at hu
        exact ⟨u, hu⟩

/-- Writing the slow path's reference back into the pointer keeps the
invariant. -/
theorem HEInv.writeBack (hinv : Inv sp db k) (hm : HEInv sp db S0 k m) {a : Nat} {o : HObj V}
    {y : NodeId} {p : HPtr} (ho : m.obj? a = some o) (hp : o.ptr? y = some p) :
    HEInv sp db S0 k (m.setRef a y (m.slowRef S0 y p)) := by
  rw [HMem.setRef_eq ho hp]
  have hptr := HObj.ptr?_setPtr_of hp { p with ref := m.slowRef S0 y p }
  have hneu := HMem.ptrRef_slowRef m S0 y p
  apply hm.setObj_ptrs ho (HObj.setPtr_core o y _)
  · intro z q n hq hn
    rw [hptr] at hq
    split at hq
    · rename_i hz
      subst hz
      simp only [Option.some.injEq] at hq
      subst hq
      exact hm.tbl.ptrNode ho hp hn
    · exact hm.tbl.ptrNode ho hq hn
  · intro z q r hq hr
    rw [hptr] at hq
    split at hq
    · rename_i hz
      subst hz
      simp only [Option.some.injEq] at hq
      subst hq
      exact hm.slowRef_ver hinv ho hp hr
    · exact hm.rver a o z q r ho hq hr
  · intro hc
    obtain ⟨r, w, h1, h2, h3, h4, h5, h6, h7⟩ := hm.snap a o ho hc
    refine ⟨r, w, h1, h2, h3, h4, h5, fun z hz => ?_, fun z q hq => ?_⟩
    · rw [hptr]; split
      · rfl
      · exact h6 z hz
    · rw [hptr] at hq
      split at hq
      · rename_i hz
        subst hz
        simp only [Option.some.injEq] at hq
        subst hq
        intro r0 h0
        obtain ⟨r1, hr1, hle⟩ := h7 z p hp r0 h0
        obtain ⟨r2, hr2, hle2⟩ := m.slowRef_ge S0 z p hr1
        refine ⟨r2, ?_, by omega⟩
        show ruleRRef S0 m.s z (m.slowRef S0 z p) = some r2
        rw [HMem.ruleR_slowRef]; exact hr2
      · exact h7 z q hq
  · intro hrel z hz
    obtain ⟨q, hq, h1, h2⟩ := hm.slots a o ho hrel z hz
    by_cases hzy : z = y
    · subst hzy
      rw [hp, Option.some.injEq] at hq
      subst hq
      refine ⟨{ p with ref := m.slowRef S0 z p }, by rw [hptr]; simp, fun hD => by rw [hneu]; exact h1 hD,
        fun hD => ?_⟩
      rcases h2 hD with ⟨n, hn, ht, hcan⟩ | h
      · exact Or.inl ⟨n, hn, ht, hcan⟩
      · exact Or.inr h
    · exact ⟨q, by rw [hptr]; simp [hzy]; exact hq, h1, h2⟩
  · intro hc hr z hz
    obtain ⟨q, hq, h1, h2⟩ := hm.live a o ho hc hr z hz
    by_cases hzy : z = y
    · subst hzy
      rw [hp, Option.some.injEq] at hq
      subst hq
      refine ⟨{ p with ref := m.slowRef S0 z p }, by rw [hptr]; simp, fun hD => ?_,
        fun hD => by rw [hneu]; exact h2 hD⟩
      obtain ⟨n, hn, ht, hcan⟩ := h1 hD
      exact ⟨n, hn, ht, hcan⟩
    · exact ⟨q, by rw [hptr]; simp [hzy]; exact hq, h1, h2⟩

end WriteBack

/-! ## Memories with the same lookups -/

section Congr

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : HMem V}

/-- The invariant depends on the memory only through its lookups, its counters
and that its keys do not repeat. -/
theorem HEInv.congr (hm : HEInv sp db S0 k m) {m' : HMem V}
    (hobj : ∀ a, m'.obj? a = m.obj? a) (hh : ∀ n, m'.handle? n = m.handle? n)
    (ht : ∀ y, m'.tableOf y = m.tableOf y) (hs : m'.s = m.s) (hr : m'.root = m.root)
    (hno : m'.nextObj = m.nextObj) (hnh : m'.nextHandle = m.nextHandle)
    (hnd1 : (m'.objs.map (·.1)).Nodup) (hnd2 : (m'.handles.map (·.1)).Nodup)
    (hnd3 : (m'.table.map (·.1)).Nodup) : HEInv sp db S0 k m' := by
  have hobjf : m'.obj? = m.obj? := funext hobj
  have hhf : m'.handle? = m.handle? := funext hh
  have hof : m'.objOf = m.objOf := by funext n; unfold HMem.objOf; rw [hh]
  have hcan : ∀ y, m'.canonicalOf y = m.canonicalOf y := by
    intro y; unfold HMem.canonicalOf; rw [ht, hof, hobjf]
  have href : ∀ y p, m'.ptrRef S0 y p = m.ptrRef S0 y p := by
    intro y p; unfold HMem.ptrRef; rw [hs, hhf, hobjf]
  have hhl : ∀ y p, m'.HoldsLive y p ↔ m.HoldsLive y p := by
    intro y p; unfold HMem.HoldsLive; rw [ht, hcan]
  have hsnap : ∀ o, HSnapExact sp S0 db m o → HSnapExact sp S0 db m' o := fun o h => h.of_s hs
  have hslot : ∀ o y p, HSlotInv S0 db m o y p → HSlotInv S0 db m' o y p := by
    intro o y p h
    obtain ⟨h1, h2⟩ := h
    refine ⟨fun hD => by rw [href]; exact h1 hD, fun hD => ?_⟩
    rcases h2 hD with h | h
    · exact Or.inl ((hhl y p).mpr h)
    · exact Or.inr h
  have hlive : ∀ y p, HLiveInv S0 db m y p → HLiveInv S0 db m' y p := by
    intro y p h
    obtain ⟨h1, h2⟩ := h
    exact ⟨fun hD => (hhl y p).mpr (h1 hD), fun hD => by rw [href]; exact h2 hD⟩
  refine
    { len := hm.len
      pre := hm.pre
      sEq := by rw [hs]; exact hm.sEq
      freshO := fun a ha => by rw [hobj]; exact hm.freshO a (by rw [← hno]; exact ha)
      freshH := fun n hn => by rw [hh]; exact hm.freshH n (by rw [← hnh]; exact hn)
      objNodup := hnd1
      hNodup := hnd2
      root := by rw [hr, hobj]; exact hm.root
      tbl := ?_
      liveW := fun n hd h1 h2 => hm.liveW n hd (by rw [← hh]; exact h1) h2
      cc := fun a o ho hc => hm.cc a o (by rw [← hobj]; exact ho) hc
      pos := fun a o ho hc => hm.pos a o (by rw [← hobj]; exact ho) hc
      dCanon := fun y hy => by rw [hcan]; exact hm.dCanon y hy
      snap := fun a o ho hc => hsnap o (hm.snap a o (by rw [← hobj]; exact ho) hc)
      ruleR := fun n hd b o w h1 h2 h3 h4 h5 => hm.ruleR n hd b o w (by rw [← hh]; exact h1) h2
        (by rw [← hobj]; exact h3) h4 (by rw [← hs]; exact h5)
      wver := fun n hd w h1 h2 => hm.wver n hd w (by rw [← hh]; exact h1) h2
      rver := fun a o y p r h1 h2 h3 => hm.rver a o y p r (by rw [← hobj]; exact h1) h2 h3
      slots := fun a o ho hrel y hy => by
        obtain ⟨p, hp, hi⟩ := hm.slots a o (by rw [← hobj]; exact ho) hrel y hy
        exact ⟨p, hp, hslot o y p hi⟩
      live := fun a o ho hc hr y hy => by
        obtain ⟨p, hp, hi⟩ := hm.live a o (by rw [← hobj]; exact ho) hc hr y hy
        exact ⟨p, hp, hlive y p hi⟩ }
  refine ⟨fun y n hy => ?_, hnd3, fun n hd h1 h2 => ?_, fun n hd h1 h2 => ?_, fun a o ho => ?_,
    fun a o y p n h1 h2 h3 => ?_⟩
  · rw [ht] at hy
    obtain ⟨hd, b, o, h1, h2, h3, h4, h5, h6⟩ := hm.tbl.entry hy
    exact ⟨hd, b, o, by rw [hh]; exact h1, h2, h3, h4, by rw [hobj]; exact h5, h6⟩
  · rw [hh] at h1; rw [ht]; exact hm.tbl.liveIn h1 h2
  · rw [hh] at h1; exact hm.tbl.deadNone h1 h2
  · rw [hobj] at ho
    obtain ⟨n, h1, h2⟩ := hm.tbl.held ho
    exact ⟨n, by rw [ht]; exact h1, by rw [hof]; exact h2⟩
  · rw [hobj] at h1
    obtain ⟨hd, h4, h5⟩ := hm.tbl.ptrNode h1 h2 h3
    exact ⟨hd, by rw [hh]; exact h4, h5⟩

end Congr

/-! ## The pointer takes the live handle -/

section TakeLive

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : HMem V}

/-- A pointer whose reference is a Rule R fixed point and at least the written
position of the handle it holds, a dead one or none, takes y's live handle from
the table: the record rule gives what it gave, or the canonical object's
position, which is y's latest; the invariant is kept. -/
theorem HEInv.takeLive (hm : HEInv sp db S0 k m) {a : Nat} {o : HObj V} {y : NodeId} {p : HPtr}
    (ho : m.obj? a = some o) (hp : o.ptr? y = some p) (hfix : ruleRRef S0 m.s y p.ref = p.ref)
    (hheld : ∀ hd0, p.handle.bind m.handle? = some hd0 →
      hd0.dead = true ∧ maxRef p.ref hd0.written = p.ref)
    {n : Nat} (htb : m.tableOf y = some n) :
    HEInv sp db S0 k (m.setObj a (o.setPtr y { p with handle := some n })) := by
  have hptr := HObj.ptr?_setPtr_of hp { p with handle := some n }
  obtain ⟨hd, b, ob, hh, hl, hny, hb, hob, hon⟩ := hm.tbl.entry htb
  have hw : hd.written = none := hm.liveW n hd hh hl
  -- The record rule before: the pointer's reference.
  have hold : m.ptrRef S0 y p = p.ref := by
    unfold HMem.ptrRef
    cases hph : p.handle.bind m.handle? with
    | none => exact hfix
    | some hd0 =>
      obtain ⟨hdead, hmax⟩ := hheld hd0 hph
      have hnone : hd0.obj = none := by
        cases hpn : p.handle with
        | none => rw [hpn] at hph; cases hph
        | some n0 =>
          rw [hpn] at hph
          simp only [Option.bind_some] at hph
          exact hm.tbl.deadNone hph hdead
      simp only [hnone, Option.bind_none]
      rw [hfix, hmax]
  -- After: the canonical object's position, or the pointer's reference.
  have hnew : m.ptrRef S0 y { p with handle := some n } =
      if ob.canonical then ob.pos else p.ref := by
    unfold HMem.ptrRef
    simp only [Option.bind_some, hh, hb, hob, hw, maxRef_none, hfix]
  have hgood : inD db.D y = false → m.ptrRef S0 y p = (db.S.lv y).map (·.recNo) →
      m.ptrRef S0 y { p with handle := some n } = (db.S.lv y).map (·.recNo) := by
    intro _ h
    rw [hnew]
    split
    · rename_i hc; rw [hm.pos b ob hob hc, hon]
    · rw [← hold]; exact h
  have hholds : inD db.D y = true → m.HoldsLive y { p with handle := some n } :=
    fun hD => ⟨n, rfl, htb, hm.dCanon y hD⟩
  apply hm.setObj_ptrs ho (HObj.setPtr_core o y _)
  · intro z q n' hq hn'
    rw [hptr] at hq
    split at hq
    · rename_i hz
      subst hz
      simp only [Option.some.injEq] at hq
      subst hq
      simp only [Option.some.injEq] at hn'
      subst hn'
      exact ⟨hd, hh, hny⟩
    · exact hm.tbl.ptrNode ho hq hn'
  · intro z q r hq hr
    rw [hptr] at hq
    split at hq
    · rename_i hz
      subst hz
      simp only [Option.some.injEq] at hq
      subst hq
      exact hm.rver a o z p r ho hp hr
    · exact hm.rver a o z q r ho hq hr
  · intro hc
    obtain ⟨r, w, h1, h2, h3, h4, h5, h6, h7⟩ := hm.snap a o ho hc
    refine ⟨r, w, h1, h2, h3, h4, h5, fun z hz => ?_, fun z q hq => ?_⟩
    · rw [hptr]; split
      · rfl
      · exact h6 z hz
    · rw [hptr] at hq
      split at hq
      · rename_i hz
        subst hz
        simp only [Option.some.injEq] at hq
        subst hq
        exact h7 z p hp
      · exact h7 z q hq
  · intro hrel z hz
    obtain ⟨q, hq, h1, h2⟩ := hm.slots a o ho hrel z hz
    by_cases hzy : z = y
    · subst hzy
      rw [hp, Option.some.injEq] at hq
      subst hq
      exact ⟨{ p with handle := some n }, by rw [hptr]; simp,
        fun hD => hgood hD (h1 hD), fun hD => Or.inl (hholds hD)⟩
    · exact ⟨q, by rw [hptr]; simp [hzy]; exact hq, h1, h2⟩
  · intro hc hr z hz
    obtain ⟨q, hq, h1, h2⟩ := hm.live a o ho hc hr z hz
    by_cases hzy : z = y
    · subst hzy
      rw [hp, Option.some.injEq] at hq
      subst hq
      exact ⟨{ p with handle := some n }, by rw [hptr]; simp, hholds, fun hD => hgood hD (h2 hD)⟩
    · exact ⟨q, by rw [hptr]; simp [hzy]; exact hq, h1, h2⟩

end TakeLive

/-- A key of a list of pairs is found in it. -/
theorem lookup_ne_none_of_mem {β : Type} : ∀ {l : List (Nat × β)} {q : Nat × β}, q ∈ l →
    List.lookup q.1 l ≠ none
  | [], _, h => by cases h
  | (c, x) :: l, q, h => by
    rw [lookup_cons_eq]
    split
    · simp
    · rename_i hc
      rcases List.mem_cons.mp h with rfl | h'
      · exact absurd rfl hc
      · exact lookup_ne_none_of_mem h'

/-! ## The load installs a version -/

section Install

/-- The memory after the load installs version w, read for live handle n,
whose object was at b (`HMem.load`). -/
def HMem.installed (sp : Spec V T) (m : HMem V) (n : Nat) (hd : Handle) (b : Nat) (w : Version V) :
    HMem V :=
  let m1 := m.dropObj b
  let m2 : HMem V := { m1 with objs := (m.nextObj, HObj.ofVersion sp w) :: m1.objs, nextObj := m.nextObj + 1 }
  m2.setHandle n { hd with obj := some m.nextObj }

theorem HMem.load_installed (sp : Spec V T) (S : Stream V T) {m : HMem V} {n : Nat} {hd : Handle}
    {b : Nat} {ob : HObj V} (hh : m.handle? n = some hd) (hb : hd.obj = some b) (hob : m.obj? b = some ob)
    {r : Nat} (hu : ob.usable (some r) = false) {w : Version V} (hw : S.versionAt r hd.node = some w) :
    m.load sp S n (some r) = (m.installed sp n hd b w, some m.nextObj) := by
  unfold HMem.load
  simp only [hh, hb, hob, hu, Bool.false_eq_true, ↓reduceIte, hw]
  rfl

theorem HMem.installed_obj? (sp : Spec V T) (m : HMem V) (n : Nat) (hd : Handle) (b : Nat) (w : Version V)
    (x : Nat) : (m.installed sp n hd b w).obj? x =
      if x = m.nextObj then some (HObj.ofVersion sp w) else if x = b then none else m.obj? x := by
  unfold HMem.installed
  simp only [HMem.obj?_setHandle]
  unfold HMem.obj?
  simp only
  rw [lookup_cons_eq]
  split
  · rfl
  · show (m.dropObj b).obj? x = _
    rw [HMem.obj?_dropObj]
    rfl

theorem HMem.installed_handle? (sp : Spec V T) (m : HMem V) (n : Nat) (hd : Handle) (b : Nat)
    (w : Version V) (n' : Nat) : (m.installed sp n hd b w).handle? n' =
      if n' = n then some { hd with obj := some m.nextObj } else m.handle? n' := by
  unfold HMem.installed
  simp only [HMem.handle?_setHandle]
  rfl

theorem HMem.installed_tableOf (sp : Spec V T) (m : HMem V) (n : Nat) (hd : Handle) (b : Nat)
    (w : Version V) (y : NodeId) : (m.installed sp n hd b w).tableOf y = m.tableOf y := rfl
@[simp] theorem HMem.installed_s (sp : Spec V T) (m : HMem V) (n : Nat) (hd : Handle) (b : Nat)
    (w : Version V) : (m.installed sp n hd b w).s = m.s := rfl
@[simp] theorem HMem.installed_root (sp : Spec V T) (m : HMem V) (n : Nat) (hd : Handle) (b : Nat)
    (w : Version V) : (m.installed sp n hd b w).root = m.root := rfl
@[simp] theorem HMem.installed_nextObj (sp : Spec V T) (m : HMem V) (n : Nat) (hd : Handle) (b : Nat)
    (w : Version V) : (m.installed sp n hd b w).nextObj = m.nextObj + 1 := rfl
@[simp] theorem HMem.installed_nextHandle (sp : Spec V T) (m : HMem V) (n : Nat) (hd : Handle)
    (b : Nat) (w : Version V) : (m.installed sp n hd b w).nextHandle = m.nextHandle := rfl

theorem HObj.ofVersion_ptr? (sp : Spec V T) (w : Version V) (z : NodeId) :
    (HObj.ofVersion sp w).ptr? z =
      if z ∈ pointees sp w.hist then some { ref := w.ref? z, handle := none } else none := by
  unfold HObj.ofVersion HObj.ptr?
  exact lookup_map_pair (pointees sp w.hist) (fun y => ({ ref := w.ref? y, handle := none } : HPtr)) z

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : HMem V}

/-- The snapshot of version w, read at r, as the invariant asks of a
snapshot: exactly the version, with a pointer for each pointee, each with w's
reference and no handle. -/
theorem ofVersion_snapExact (hinv : Inv sp db k) {r : Nat} {y : NodeId}
    {w : Version V} (hw : db.S.versionAt r y = some w) (m' : HMem V) :
    HSnapExact sp S0 db m' (HObj.ofVersion sp w) := by
  obtain ⟨hwn, hwr, -⟩ := hinv.version_node hw
  refine ⟨r, w, by simp [HObj.ofVersion, hwr], by simp [HObj.ofVersion, hwn]; exact hw, rfl, rfl, rfl,
    fun z hz => ?_, fun z p hp => ?_⟩
  · rw [HObj.ofVersion_ptr?]
    have : z ∈ pointees sp w.hist := hz
    simp [this]
  · rw [HObj.ofVersion_ptr?] at hp
    split at hp
    · simp only [Option.some.injEq] at hp
      subst hp
      intro r0 h0
      exact ⟨r0, h0, Nat.le_refl _⟩
    · cases hp

/-- The load installs a version in a live handle that holds a snapshot: the
version read at r, which is at least the newest version of the node in the
startup section. The invariant is kept: no record reference changes (the
handle holds a snapshot before and after), and the new snapshot is exact. -/
theorem HEInv.install (hinv : Inv sp db k) (hm : HEInv sp db S0 k m) {n : Nat} {hd : Handle} {b : Nat}
    {ob : HObj V} (hh : m.handle? n = some hd) (hb : hd.obj = some b) (hob : m.obj? b = some ob)
    (hc : ob.canonical = false) {r : Nat} {w : Version V} (hw : db.S.versionAt r hd.node = some w)
    (hnew : ∀ wn, newest S0 m.s hd.node = some wn → wn.recNo ≤ r) :
    HEInv sp db S0 k (m.installed sp n hd b w) := by
  have hl : hd.dead = false := hm.tbl.live_of_obj hh hb
  obtain ⟨htbn, ob', hob', hobn⟩ := hm.tbl.obj_of_handle hh hb
  rw [hob, Option.some.injEq] at hob'
  subst hob'
  obtain ⟨hwn, hwr, -⟩ := hinv.version_node hw
  have hblt : b < m.nextObj := Nat.lt_of_not_le (fun h => by rw [hm.freshO b h] at hob; cases hob)
  have hbb : m.nextObj ≠ b := by omega
  have hobjn : m.objOf n = some b := by simp [HMem.objOf, hh, hb]
  have huniq : ∀ n' hd', m.handle? n' = some hd' → hd'.obj = some b → n' = n :=
    fun n' hd' h1 h2 => hm.tbl.uniq h1 h2 hobjn
  have eobj := HMem.installed_obj? sp m n hd b w
  have ehd := HMem.installed_handle? sp m n hd b w
  -- A handle's object is in memory, so it is not the new address.
  have hobj_lt : ∀ n' hd' x, m.handle? n' = some hd' → hd'.obj = some x → x < m.nextObj := by
    intro n' hd' x h1 h2
    obtain ⟨-, o', ho', -⟩ := hm.tbl.obj_of_handle h1 h2
    exact Nat.lt_of_not_le (fun h => by rw [hm.freshO x h] at ho'; cases ho')
  -- The objects of other handles are as they were.
  have hother : ∀ n' hd' x, n' ≠ n → m.handle? n' = some hd' → hd'.obj = some x →
      (m.installed sp n hd b w).obj? x = m.obj? x := by
    intro n' hd' x hn h1 h2
    have hxb : x ≠ b := by intro he; subst he; exact hn (huniq n' hd' h1 h2)
    have hxn : x ≠ m.nextObj := by have := hobj_lt n' hd' x h1 h2; omega
    rw [eobj]; simp [hxb, hxn]
  -- canonicalOf is as it was: node hd.node has none, before and after.
  have hcan : ∀ z, (m.installed sp n hd b w).canonicalOf z = m.canonicalOf z := by
    intro z
    unfold HMem.canonicalOf
    rw [HMem.installed_tableOf]
    cases hz : m.tableOf z with
    | none => rfl
    | some n' =>
      simp only [Option.bind_some]
      unfold HMem.objOf
      rw [ehd n']
      by_cases hn : n' = n
      · subst hn
        simp only [↓reduceIte, hh, hb, Option.bind_some]
        rw [eobj, hob]
        simp [hc, HObj.ofVersion]
      · simp only [hn, ↓reduceIte]
        cases h1 : m.handle? n' with
        | none => rfl
        | some hd' =>
          simp only [Option.bind_some]
          cases h2 : hd'.obj with
          | none => rfl
          | some x =>
            simp only
            rw [hother n' hd' x hn h1 h2]
  -- Every record reference is as it was.
  have href : ∀ y q, (m.installed sp n hd b w).ptrRef S0 y q = m.ptrRef S0 y q := by
    intro y q
    unfold HMem.ptrRef
    rw [HMem.installed_s]
    cases hq : q.handle with
    | none => rfl
    | some n' =>
      simp only [Option.bind_some]
      rw [ehd n']
      by_cases hn : n' = n
      · subst hn
        simp only [↓reduceIte, hh, Option.bind_some, hb]
        rw [eobj, hob]
        simp [hc, HObj.ofVersion]
      · simp only [hn, ↓reduceIte]
        cases h1 : m.handle? n' with
        | none => rfl
        | some hd' =>
          simp only
          cases h2 : hd'.obj with
          | none => rfl
          | some x =>
            simp only [Option.bind_some]
            rw [hother n' hd' x hn h1 h2]
  have hhl : ∀ y q, (m.installed sp n hd b w).HoldsLive y q ↔ m.HoldsLive y q := by
    intro y q; unfold HMem.HoldsLive; rw [HMem.installed_tableOf, hcan]
  have hback : ∀ x ox, (m.installed sp n hd b w).obj? x = some ox →
      (x = m.nextObj ∧ ox = HObj.ofVersion sp w) ∨ (x ≠ m.nextObj ∧ x ≠ b ∧ m.obj? x = some ox) := by
    intro x ox hx
    rw [eobj] at hx
    split at hx
    · rename_i h; simp only [Option.some.injEq] at hx; exact Or.inl ⟨h, hx.symm⟩
    · rename_i h1
      split at hx
      · cases hx
      · rename_i h2; exact Or.inr ⟨h1, h2, hx⟩
  have hnode_new : (HObj.ofVersion sp w).node = hd.node := by simp [HObj.ofVersion, hwn]
  refine
    { len := hm.len
      pre := hm.pre
      sEq := by rw [HMem.installed_s]; exact hm.sEq
      freshO := ?_
      freshH := ?_
      objNodup := ?_
      hNodup := ?_
      root := ?_
      tbl := ?_
      liveW := ?_
      cc := ?_
      pos := ?_
      dCanon := fun y hy => by rw [hcan]; exact hm.dCanon y hy
      snap := ?_
      ruleR := ?_
      wver := ?_
      rver := ?_
      slots := ?_
      live := ?_ }
  · intro x hx
    rw [HMem.installed_nextObj] at hx
    rw [eobj]
    have h1 : x ≠ m.nextObj := by omega
    have h2 : x ≠ b := by omega
    simp only [h1, h2, ↓reduceIte]
    exact hm.freshO x (by omega)
  · intro n' hn'
    rw [HMem.installed_nextHandle] at hn'
    rw [ehd]
    have : n' ≠ n := by intro he; subst he; rw [hm.freshH n' hn'] at hh; cases hh
    simp only [this, ↓reduceIte]
    exact hm.freshH n' hn'
  · unfold HMem.installed
    simp only [HMem.setHandle_objs, HMem.dropObj, List.map_cons, List.nodup_cons]
    refine ⟨?_, (List.Sublist.map _ List.filter_sublist).nodup hm.objNodup⟩
    intro hmem
    obtain ⟨q, hq, hqn⟩ := List.mem_map.mp hmem
    have hq' := (List.mem_filter.mp hq).1
    have : m.obj? q.1 ≠ none := lookup_ne_none_of_mem hq'
    rw [hqn, hm.freshO m.nextObj (Nat.le_refl _)] at this
    exact this rfl
  · unfold HMem.installed
    exact setHandle_nodup _ n _ hm.hNodup
  · obtain ⟨or, hor, hcr, hnr⟩ := hm.root
    refine ⟨or, ?_, hcr, hnr⟩
    rw [HMem.installed_root, eobj]
    have h1 : m.root ≠ m.nextObj := by
      intro he; rw [he, hm.freshO m.nextObj (Nat.le_refl _)] at hor; cases hor
    have h2 : m.root ≠ b := by intro he; rw [he, hob, Option.some.injEq] at hor; subst hor; rw [hc] at hcr; cases hcr
    simp only [h1, h2, ↓reduceIte]
    exact hor
  · refine ⟨fun y n' hy => ?_, hm.tbl.nodup, fun n' hd' h1 h2 => ?_, fun n' hd' h1 h2 => ?_,
      fun x ox hx => ?_, fun x ox y q n' hx hq hn' => ?_⟩
    · rw [HMem.installed_tableOf] at hy
      obtain ⟨hd'', b'', o'', h1, h2, h3, h4, h5, h6⟩ := hm.tbl.entry hy
      by_cases hn : n' = n
      · subst hn
        rw [hh, Option.some.injEq] at h1
        subst h1
        refine ⟨{ hd with obj := some m.nextObj }, m.nextObj, HObj.ofVersion sp w, by rw [ehd]; simp,
          h2, h3, rfl, by rw [eobj]; simp, by rw [hnode_new, h3]⟩
      · refine ⟨hd'', b'', o'', by rw [ehd]; simp [hn]; exact h1, h2, h3, h4, ?_, h6⟩
        rw [hother n' hd'' b'' hn h1 h4]; exact h5
    · rw [ehd] at h1
      split at h1
      · rename_i hn
        subst hn
        simp only [Option.some.injEq] at h1
        subst h1
        rw [HMem.installed_tableOf]; exact htbn
      · rw [HMem.installed_tableOf]; exact hm.tbl.liveIn h1 h2
    · rw [ehd] at h1
      split at h1
      · simp only [Option.some.injEq] at h1
        subst h1
        simp only at h2
        rw [hl] at h2; cases h2
      · exact hm.tbl.deadNone h1 h2
    · rcases hback x ox hx with ⟨rfl, rfl⟩ | ⟨h1, h2, h3⟩
      · refine ⟨n, by rw [HMem.installed_tableOf, hnode_new]; exact htbn, ?_⟩
        unfold HMem.objOf; rw [ehd]; simp
      · obtain ⟨n'', ht'', hob''⟩ := hm.tbl.held h3
        have hn : n'' ≠ n := by
          intro he; subst he; rw [hobjn, Option.some.injEq] at hob''; exact h2 hob''.symm
        refine ⟨n'', by rw [HMem.installed_tableOf]; exact ht'', ?_⟩
        unfold HMem.objOf; rw [ehd]; simp only [hn, ↓reduceIte]; exact hob''
    · rcases hback x ox hx with ⟨-, rfl⟩ | ⟨-, -, h3⟩
      · rw [HObj.ofVersion_ptr?] at hq
        split at hq
        · simp only [Option.some.injEq] at hq; subst hq; cases hn'
        · cases hq
      · obtain ⟨hd'', h4, h5⟩ := hm.tbl.ptrNode h3 hq hn'
        rw [ehd]
        split
        · rename_i hn; subst hn; rw [hh, Option.some.injEq] at h4; subst h4; exact ⟨_, rfl, h5⟩
        · exact ⟨hd'', h4, h5⟩
  · intro n' hd' h1 h2
    rw [ehd] at h1
    split at h1
    · simp only [Option.some.injEq] at h1; subst h1; exact hm.liveW n hd hh hl
    · exact hm.liveW n' hd' h1 h2
  · intro x ox hx hcx
    rcases hback x ox hx with ⟨-, rfl⟩ | ⟨-, -, h3⟩
    · simp [HObj.ofVersion] at hcx
    · exact hm.cc x ox h3 hcx
  · intro x ox hx hcx
    rcases hback x ox hx with ⟨-, rfl⟩ | ⟨-, -, h3⟩
    · simp [HObj.ofVersion] at hcx
    · exact hm.pos x ox h3 hcx
  · intro x ox hx hcx
    rcases hback x ox hx with ⟨-, rfl⟩ | ⟨-, -, h3⟩
    · rw [← hwn] at hw; exact ofVersion_snapExact (S0 := S0) hinv hw _
    · exact (hm.snap x ox h3 hcx).of_s (HMem.installed_s sp m n hd b w)
  · intro n' hd' x ox wn h1 h2 h3 h4 h5
    rw [HMem.installed_s] at h5
    rw [ehd] at h1
    split at h1
    · rename_i hn
      subst hn
      simp only [Option.some.injEq] at h1
      subst h1
      simp only [Option.some.injEq] at h2
      subst h2
      rw [eobj] at h3
      simp only [↓reduceIte, Option.some.injEq] at h3
      subst h3
      exact ⟨r, by simp [HObj.ofVersion, hwr], hnew wn h5⟩
    · rw [hother n' hd' x (by assumption) h1 h2] at h3
      exact hm.ruleR n' hd' x ox wn h1 h2 h3 h4 h5
  · intro n' hd' w' h1 h2
    rw [ehd] at h1
    split at h1
    · simp only [Option.some.injEq] at h1; subst h1; exact hm.wver n hd w' hh h2
    · exact hm.wver n' hd' w' h1 h2
  · intro x ox z q r' hx hq hr'
    rcases hback x ox hx with ⟨-, rfl⟩ | ⟨-, -, h3⟩
    · rw [HObj.ofVersion_ptr?] at hq
      split at hq
      · simp only [Option.some.injEq] at hq
        subst hq
        exact hinv.ref_versionAt hw hr'
      · cases hq
    · exact hm.rver x ox z q r' h3 hq hr'
  · intro x ox hx hrel z hz
    rcases hback x ox hx with ⟨-, rfl⟩ | ⟨-, -, h3⟩
    · simp [HRelevant, HObj.ofVersion] at hrel
    · obtain ⟨q, hq, h1, h2⟩ := hm.slots x ox h3 hrel z hz
      refine ⟨q, hq, fun hD => by rw [href]; exact h1 hD, fun hD => ?_⟩
      rcases h2 hD with h | h
      · exact Or.inl ((hhl z q).mpr h)
      · exact Or.inr h
  · intro x ox hx hcx hr z hz
    rcases hback x ox hx with ⟨-, rfl⟩ | ⟨-, -, h3⟩
    · simp [HObj.ofVersion] at hcx
    · obtain ⟨q, hq, h1, h2⟩ := hm.live x ox h3 hcx hr z hz
      exact ⟨q, hq, fun hD => (hhl z q).mpr (h1 hD), fun hD => by rw [href]; exact h2 hD⟩

end Install

/-! ## A new handle with a version -/

section NewHandle

/-- The memory with a new live handle for node y, the table's, holding the
snapshot of version w at a new address. -/
def HMem.withNew (sp : Spec V T) (m : HMem V) (y : NodeId) (w : Version V) : HMem V :=
  { m with objs := (m.nextObj, HObj.ofVersion sp w) :: m.objs,
           handles := (m.nextHandle, { node := y, obj := some m.nextObj, written := none, dead := false })
             :: m.handles,
           table := (y, m.nextHandle) :: m.table,
           nextObj := m.nextObj + 1, nextHandle := m.nextHandle + 1 }

theorem HMem.withNew_obj? (sp : Spec V T) (m : HMem V) (y : NodeId) (w : Version V) (x : Nat) :
    (m.withNew sp y w).obj? x = if x = m.nextObj then some (HObj.ofVersion sp w) else m.obj? x := by
  unfold HMem.withNew HMem.obj?
  exact lookup_cons_eq _ _ _ _

theorem HMem.withNew_handle? (sp : Spec V T) (m : HMem V) (y : NodeId) (w : Version V) (n : Nat) :
    (m.withNew sp y w).handle? n = if n = m.nextHandle then
      some { node := y, obj := some m.nextObj, written := none, dead := false } else m.handle? n := by
  unfold HMem.withNew HMem.handle?
  exact lookup_cons_eq _ _ _ _

theorem HMem.withNew_tableOf (sp : Spec V T) (m : HMem V) (y : NodeId) (w : Version V) (z : NodeId) :
    (m.withNew sp y w).tableOf z = if z = y then some m.nextHandle else m.tableOf z := by
  unfold HMem.withNew HMem.tableOf
  exact lookup_cons_eq _ _ _ _

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : HMem V}

/-- A node with no live handle gets one, the table's, holding the snapshot of a
version read at r, at least the newest version in the startup section: the
invariant is kept. -/
theorem HEInv.addHandle (hinv : Inv sp db k) (hm : HEInv sp db S0 k m) {y : NodeId}
    (hty : m.tableOf y = none) {r : Nat} {w : Version V} (hw : db.S.versionAt r y = some w)
    (hnew : ∀ wn, newest S0 m.s y = some wn → wn.recNo ≤ r) :
    HEInv sp db S0 k (m.withNew sp y w) := by
  obtain ⟨hwn, hwr, -⟩ := hinv.version_node hw
  have eobj := HMem.withNew_obj? sp m y w
  have ehd := HMem.withNew_handle? sp m y w
  have etb := HMem.withNew_tableOf sp m y w
  have hnode_new : (HObj.ofVersion sp w).node = y := by simp [HObj.ofVersion, hwn]
  -- Handles and objects of m are below the counters.
  have hh_lt : ∀ n hd, m.handle? n = some hd → n < m.nextHandle := by
    intro n hd h
    exact Nat.lt_of_not_le (fun hle => by rw [hm.freshH n hle] at h; cases h)
  have ho_lt : ∀ x o, m.obj? x = some o → x < m.nextObj := by
    intro x o h
    exact Nat.lt_of_not_le (fun hle => by rw [hm.freshO x hle] at h; cases h)
  -- No object of y is in m, and no live handle of y.
  have hnoobj : ∀ x o, m.obj? x = some o → o.node ≠ y := by
    intro x o h he
    obtain ⟨n, ht, -⟩ := hm.tbl.held h
    rw [he, hty] at ht; cases ht
  have hnolive : ∀ n hd, m.handle? n = some hd → hd.dead = false → hd.node ≠ y := by
    intro n hd h hl he
    have := hm.tbl.liveIn h hl
    rw [he, hty] at this; cases this
  -- A handle's object in m is not the new address.
  have hobj_lt : ∀ n hd x, m.handle? n = some hd → hd.obj = some x → x < m.nextObj := by
    intro n hd x h1 h2
    obtain ⟨-, o, ho, -⟩ := hm.tbl.obj_of_handle h1 h2
    exact ho_lt x o ho
  have hcan : ∀ z, (m.withNew sp y w).canonicalOf z = m.canonicalOf z := by
    intro z
    unfold HMem.canonicalOf
    rw [etb]
    by_cases hz : z = y
    · subst hz
      simp only [↓reduceIte, hty, Option.bind_some, Option.bind_none]
      unfold HMem.objOf
      rw [ehd]
      simp only [↓reduceIte, Option.bind_some]
      rw [eobj]
      simp [HObj.ofVersion]
    · simp only [hz, ↓reduceIte]
      cases ht : m.tableOf z with
      | none => rfl
      | some n =>
        simp only [Option.bind_some]
        obtain ⟨hd, b, o, hh, -, -, hb, hob, -⟩ := hm.tbl.entry ht
        have hn : n ≠ m.nextHandle := by have := hh_lt n hd hh; omega
        have hb' : b ≠ m.nextObj := by have := ho_lt b o hob; omega
        unfold HMem.objOf
        rw [ehd]
        simp only [hn, ↓reduceIte, hh, hb, Option.bind_some]
        rw [eobj]
        simp only [hb', ↓reduceIte]
  -- The record rule, for pointers whose handle is one of m's, or none.
  have href : ∀ z q, (∀ n, q.handle = some n → n < m.nextHandle) →
      (m.withNew sp y w).ptrRef S0 z q = m.ptrRef S0 z q := by
    intro z q hq
    unfold HMem.ptrRef
    have hs : (m.withNew sp y w).s = m.s := rfl
    rw [hs]
    cases hqn : q.handle with
    | none => rfl
    | some n =>
      have hn : n ≠ m.nextHandle := by have := hq n hqn; omega
      simp only [Option.bind_some]
      rw [ehd]
      simp only [hn, ↓reduceIte]
      cases h1 : m.handle? n with
      | none => rfl
      | some hd =>
        simp only
        cases h2 : hd.obj with
        | none => rfl
        | some x =>
          have hx : x ≠ m.nextObj := by have := hobj_lt n hd x h1 h2; omega
          simp only [Option.bind_some]
          rw [eobj]
          simp only [hx, ↓reduceIte]
  have hptr_lt : ∀ x o z q n, m.obj? x = some o → o.ptr? z = some q → q.handle = some n →
      n < m.nextHandle := by
    intro x o z q n h1 h2 h3
    obtain ⟨hd, hh, -⟩ := hm.tbl.ptrNode h1 h2 h3
    exact hh_lt n hd hh
  have hhl : ∀ x o z q, m.obj? x = some o → o.ptr? z = some q →
      ((m.withNew sp y w).HoldsLive z q ↔ m.HoldsLive z q) := by
    intro x o z q h1 h2
    unfold HMem.HoldsLive
    rw [etb, hcan]
    by_cases hz : z = y
    · subst hz
      simp only [↓reduceIte, hty]
      constructor
      · rintro ⟨n, -, -, hc⟩
        have : m.canonicalOf z = none := by
          unfold HMem.canonicalOf; rw [hty]; rfl
        rw [this] at hc; cases hc
      · rintro ⟨n, -, h, -⟩; cases h
    · simp only [hz, ↓reduceIte]
  have hback : ∀ x ox, (m.withNew sp y w).obj? x = some ox →
      (x = m.nextObj ∧ ox = HObj.ofVersion sp w) ∨ (x ≠ m.nextObj ∧ m.obj? x = some ox) := by
    intro x ox hx
    rw [eobj] at hx
    split at hx
    · rename_i h; simp only [Option.some.injEq] at hx; exact Or.inl ⟨h, hx.symm⟩
    · rename_i h; exact Or.inr ⟨h, hx⟩
  refine
    { len := hm.len
      pre := hm.pre
      sEq := hm.sEq
      freshO := ?_
      freshH := ?_
      objNodup := ?_
      hNodup := ?_
      root := ?_
      tbl := ?_
      liveW := ?_
      cc := ?_
      pos := ?_
      dCanon := fun z hz => by rw [hcan]; exact hm.dCanon z hz
      snap := ?_
      ruleR := ?_
      wver := ?_
      rver := ?_
      slots := ?_
      live := ?_ }
  · intro x hx
    have hx' : m.nextObj + 1 ≤ x := hx
    rw [eobj]
    have : x ≠ m.nextObj := by omega
    simp only [this, ↓reduceIte]
    exact hm.freshO x (by omega)
  · intro n hn
    have hn' : m.nextHandle + 1 ≤ n := hn
    rw [ehd]
    have : n ≠ m.nextHandle := by omega
    simp only [this, ↓reduceIte]
    exact hm.freshH n (by omega)
  · show ((m.nextObj, HObj.ofVersion sp w) :: m.objs).map (·.1) |>.Nodup
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨fun hmem => ?_, hm.objNodup⟩
    obtain ⟨q, hq, hqn⟩ := List.mem_map.mp hmem
    have : m.obj? q.1 ≠ none := lookup_ne_none_of_mem hq
    rw [hqn, hm.freshO m.nextObj (Nat.le_refl _)] at this
    exact this rfl
  · show ((m.nextHandle, ({ node := y, obj := some m.nextObj, written := none, dead := false } : Handle))
      :: m.handles).map (·.1) |>.Nodup
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨fun hmem => ?_, hm.hNodup⟩
    obtain ⟨q, hq, hqn⟩ := List.mem_map.mp hmem
    have := lookup_ne_none_of_mem hq
    rw [hqn] at this
    exact this (hm.freshH m.nextHandle (Nat.le_refl _))
  · obtain ⟨or, hor, hcr, hnr⟩ := hm.root
    refine ⟨or, ?_, hcr, hnr⟩
    show (m.withNew sp y w).obj? m.root = some or
    rw [eobj]
    have : m.root ≠ m.nextObj := by have := ho_lt m.root or hor; omega
    simp only [this, ↓reduceIte]
    exact hor
  · refine ⟨fun z n hz => ?_, ?_, fun n hd h1 h2 => ?_, fun n hd h1 h2 => ?_,
      fun x ox hx => ?_, fun x ox z q n hx hq hn => ?_⟩
    · rw [etb] at hz
      split at hz
      · rename_i he
        rw [he]
        simp only [Option.some.injEq] at hz
        subst hz
        refine ⟨{ node := y, obj := some m.nextObj, written := none, dead := false }, m.nextObj,
          HObj.ofVersion sp w, by rw [ehd]; simp, rfl, rfl, rfl, by rw [eobj]; simp, hnode_new⟩
      · obtain ⟨hd, b, o, h1, h2, h3, h4, h5, h6⟩ := hm.tbl.entry hz
        have hn : n ≠ m.nextHandle := by have := hh_lt n hd h1; omega
        have hb : b ≠ m.nextObj := by have := ho_lt b o h5; omega
        exact ⟨hd, b, o, by rw [ehd]; simp [hn]; exact h1, h2, h3, h4, by rw [eobj]; simp [hb]; exact h5, h6⟩
    · show ((y, m.nextHandle) :: m.table).map (·.1) |>.Nodup
      simp only [List.map_cons, List.nodup_cons]
      refine ⟨fun hmem => ?_, hm.tbl.nodup⟩
      obtain ⟨q, hq, hqn⟩ := List.mem_map.mp hmem
      have := lookup_ne_none_of_mem hq
      rw [hqn] at this
      exact this hty
    · rw [ehd] at h1
      split at h1
      · rename_i hn
        simp only [Option.some.injEq] at h1
        subst h1
        rw [etb]; simp [hn]
      · rw [etb]
        have hny : hd.node ≠ y := hnolive n hd h1 h2
        simp only [hny, ↓reduceIte]
        exact hm.tbl.liveIn h1 h2
    · rw [ehd] at h1
      split at h1
      · simp only [Option.some.injEq] at h1; subst h1; cases h2
      · exact hm.tbl.deadNone h1 h2
    · rcases hback x ox hx with ⟨rfl, rfl⟩ | ⟨h1, h2⟩
      · refine ⟨m.nextHandle, by rw [etb, hnode_new]; simp, ?_⟩
        unfold HMem.objOf; rw [ehd]; simp
      · obtain ⟨n, ht, hob⟩ := hm.tbl.held h2
        have hny : ox.node ≠ y := hnoobj x ox h2
        refine ⟨n, by rw [etb]; simp only [hny, ↓reduceIte]; exact ht, ?_⟩
        obtain ⟨hd, -, -, hh, -, -, -, -, -⟩ := hm.tbl.entry ht
        have hn : n ≠ m.nextHandle := by have := hh_lt n hd hh; omega
        unfold HMem.objOf; rw [ehd]; simp only [hn, ↓reduceIte]; exact hob
    · rcases hback x ox hx with ⟨-, rfl⟩ | ⟨-, h2⟩
      · rw [HObj.ofVersion_ptr?] at hq
        split at hq
        · simp only [Option.some.injEq] at hq; subst hq; cases hn
        · cases hq
      · obtain ⟨hd, hh, hnd⟩ := hm.tbl.ptrNode h2 hq hn
        have hn' : n ≠ m.nextHandle := by have := hh_lt n hd hh; omega
        exact ⟨hd, by rw [ehd]; simp [hn']; exact hh, hnd⟩
  · intro n hd h1 h2
    rw [ehd] at h1
    split at h1
    · simp only [Option.some.injEq] at h1; subst h1; rfl
    · exact hm.liveW n hd h1 h2
  · intro x ox hx hcx
    rcases hback x ox hx with ⟨-, rfl⟩ | ⟨-, h2⟩
    · simp [HObj.ofVersion] at hcx
    · exact hm.cc x ox h2 hcx
  · intro x ox hx hcx
    rcases hback x ox hx with ⟨-, rfl⟩ | ⟨-, h2⟩
    · simp [HObj.ofVersion] at hcx
    · exact hm.pos x ox h2 hcx
  · intro x ox hx hcx
    rcases hback x ox hx with ⟨-, rfl⟩ | ⟨-, h2⟩
    · exact ofVersion_snapExact (S0 := S0) hinv hw _
    · exact (hm.snap x ox h2 hcx).of_s rfl
  · intro n hd x ox wn h1 h2 h3 h4 h5
    have h5' : newest S0 m.s hd.node = some wn := h5
    rw [ehd] at h1
    split at h1
    · simp only [Option.some.injEq] at h1
      subst h1
      simp only [Option.some.injEq] at h2
      subst h2
      rw [eobj] at h3
      simp only [↓reduceIte, Option.some.injEq] at h3
      subst h3
      exact ⟨r, by simp [HObj.ofVersion, hwr], hnew wn h5'⟩
    · rename_i hn
      have hx : x ≠ m.nextObj := by have := hobj_lt n hd x h1 h2; omega
      rw [eobj] at h3
      simp only [hx, ↓reduceIte] at h3
      exact hm.ruleR n hd x ox wn h1 h2 h3 h4 h5'
  · intro n hd w' h1 h2
    rw [ehd] at h1
    split at h1
    · simp only [Option.some.injEq] at h1; subst h1; cases h2
    · exact hm.wver n hd w' h1 h2
  · intro x ox z q r' hx hq hr'
    rcases hback x ox hx with ⟨-, rfl⟩ | ⟨-, h2⟩
    · rw [HObj.ofVersion_ptr?] at hq
      split at hq
      · simp only [Option.some.injEq] at hq; subst hq; exact hinv.ref_versionAt hw hr'
      · cases hq
    · exact hm.rver x ox z q r' h2 hq hr'
  · intro x ox hx hrel z hz
    rcases hback x ox hx with ⟨-, rfl⟩ | ⟨-, h2⟩
    · simp [HRelevant, HObj.ofVersion] at hrel
    · obtain ⟨q, hq, h1, h3⟩ := hm.slots x ox h2 hrel z hz
      have hql : ∀ n, q.handle = some n → n < m.nextHandle := fun n hn => hptr_lt x ox z q n h2 hq hn
      refine ⟨q, hq, fun hD => by rw [href z q hql]; exact h1 hD, fun hD => ?_⟩
      rcases h3 hD with h | h
      · exact Or.inl ((hhl x ox z q h2 hq).mpr h)
      · exact Or.inr h
  · intro x ox hx hcx hr z hz
    rcases hback x ox hx with ⟨-, rfl⟩ | ⟨-, h2⟩
    · simp [HObj.ofVersion] at hcx
    · obtain ⟨q, hq, h1, h3⟩ := hm.live x ox h2 hcx hr z hz
      have hql : ∀ n, q.handle = some n → n < m.nextHandle := fun n hn => hptr_lt x ox z q n h2 hq hn
      exact ⟨q, hq, fun hD => (hhl x ox z q h2 hq).mpr (h1 hD), fun hD => by rw [href z q hql]; exact h3 hD⟩

end NewHandle

/-! ## Resolve and load, case by case -/

section Cases

theorem HMem.resolve_live {M : HMem V} {a : Nat} {y : NodeId} {o : HObj V} {p : HPtr} {n : Nat}
    {hd : Handle} (ho : M.obj? a = some o) (hp : o.ptr? y = some p) (hn : p.handle = some n)
    (hh : M.handle? n = some hd) (hl : hd.dead = false) : M.resolve a y = (M, n) := by
  unfold HMem.resolve
  simp only [ho, Option.bind_some, hp, hn, hh, hl, Bool.false_eq_true, ↓reduceIte]

theorem HMem.resolve_table {M : HMem V} {a : Nat} {y : NodeId} {o : HObj V} {p : HPtr} {n : Nat}
    (ho : M.obj? a = some o) (hp : o.ptr? y = some p)
    (hnl : ∀ n0 hd0, p.handle = some n0 → M.handle? n0 = some hd0 → hd0.dead = true)
    (ht : M.tableOf y = some n) :
    M.resolve a y = (M.setObj a (o.setPtr y { p with handle := some n }), n) := by
  unfold HMem.resolve
  simp only [ho, Option.bind_some, hp]
  cases hpn : p.handle with
  | none => simp only [ht, ho, hp]
  | some n0 =>
    cases hh : M.handle? n0 with
    | none => simp only [hh, ht, ho, hp]
    | some hd0 =>
      have := hnl n0 hd0 hpn hh
      simp only [hh, this, ↓reduceIte, ht, ho, hp]

/-- The memory with a new live handle for y, with no object, in the table
(`HMem.resolve`). -/
def HMem.emptyHandle (M : HMem V) (y : NodeId) : HMem V :=
  { (M.setHandle M.nextHandle { node := y, obj := none, written := none, dead := false }).setTable y
      M.nextHandle with nextHandle := M.nextHandle + 1 }

theorem HMem.resolve_new {M : HMem V} {a : Nat} {y : NodeId} {o : HObj V} {p : HPtr}
    (ho : M.obj? a = some o) (hp : o.ptr? y = some p)
    (hnl : ∀ n0 hd0, p.handle = some n0 → M.handle? n0 = some hd0 → hd0.dead = true)
    (ht : M.tableOf y = none) :
    M.resolve a y = ((M.emptyHandle y).setObj a (o.setPtr y { p with handle := some M.nextHandle }),
      M.nextHandle) := by
  have ho' : (M.emptyHandle y).obj? a = some o := ho
  simp only [HMem.emptyHandle] at ho'
  unfold HMem.resolve
  simp only [ho, Option.bind_some, hp]
  cases hpn : p.handle with
  | none => simp only [ht, ho', hp]; rfl
  | some n0 =>
    cases hh : M.handle? n0 with
    | none => simp only [hh, ht, ho', hp]; rfl
    | some hd0 =>
      have := hnl n0 hd0 hpn hh
      simp only [hh, this, ↓reduceIte, ht, ho', hp]
      rfl

theorem HMem.load_usable (sp : Spec V T) (S : Stream V T) {M : HMem V} {n : Nat} {hd : Handle} {b : Nat}
    {ob : HObj V} (hh : M.handle? n = some hd) (hb : hd.obj = some b) (hob : M.obj? b = some ob)
    {r : Option Nat} (hu : ob.usable r = true) : M.load sp S n r = (M, some b) := by
  unfold HMem.load
  simp only [hh, hb, hob, hu, ↓reduceIte]

/-- The memory after the load reads version w for live handle n, which holds
no object (`HMem.load`). -/
def HMem.filled (sp : Spec V T) (M : HMem V) (n : Nat) (hd : Handle) (w : Version V) : HMem V :=
  let m2 : HMem V := { M with objs := (M.nextObj, HObj.ofVersion sp w) :: M.objs, nextObj := M.nextObj + 1 }
  m2.setHandle n { hd with obj := some M.nextObj }

theorem HMem.load_filled (sp : Spec V T) (S : Stream V T) {M : HMem V} {n : Nat} {hd : Handle}
    (hh : M.handle? n = some hd) (hb : hd.obj = none) {r : Nat} {w : Version V}
    (hw : S.versionAt r hd.node = some w) :
    M.load sp S n (some r) = (M.filled sp n hd w, some M.nextObj) := by
  unfold HMem.load
  simp only [hh, hb, hw]
  rfl

end Cases

/-! ## The readers' follow -/

section Follow

/-- Object b, of node y, can be read at the last time k: it is canonical, or the
snapshot at the latest version of a written node not in D. -/
def HReadable (sp : Spec V T) (db : DB V T) (m : HMem V) (b : Nat) (y : NodeId) : Prop :=
  ∃ o, m.obj? b = some o ∧ o.node = y ∧
    (o.canonical = true ∨ (inD db.D y = false ∧ written sp y = true ∧ o.pos = (db.S.lv y).map (·.recNo)))

/-- A pointer for y that a read at k may follow: for y in D it holds y's live
handle with y's canonical object; otherwise the record rule gives y's latest
version. -/
def HPtrGood (S0 : Stream V T) (db : DB V T) (m : HMem V) (y : NodeId) (p : HPtr) : Prop :=
  (inD db.D y = true ∧ m.HoldsLive y p) ∨
    (inD db.D y = false ∧ m.ptrRef S0 y p = (db.S.lv y).map (·.recNo))

/-- What the readers' follow of the pointer of object a for y gives, from
memory m to m', with n the live handle reached and b the object reached: the
invariant; every object of another node keeps its core; b is an object of y,
held by n, which is y's live handle; if the pointer was good, b is readable;
every object at another address that is of another node, or canonical, is as it
was; object a, if of another node, keeps its core and its other pointers, and
its pointer for y holds n; the table is as it was for the other nodes. -/
structure HFollowed (sp : Spec V T) (S0 : Stream V T) (db : DB V T) (k : Nat) (m m' : HMem V) (a : Nat)
    (y : NodeId) (n b : Nat) : Prop where
  inv : HEInv sp db S0 k m'
  frame : ∀ x o, m.obj? x = some o → o.node ≠ y → ∃ o', m'.obj? x = some o' ∧ o'.core = o.core
  obj : ∃ ob, m'.obj? b = some ob ∧ ob.node = y
  readable : ∀ o p, m.obj? a = some o → o.ptr? y = some p → HPtrGood S0 db m y p →
    written sp y = true → HReadable sp db m' b y
  objOf : m'.objOf n = some b
  tableOf : m'.tableOf y = some n
  others : ∀ x o, m.obj? x = some o → x ≠ a → (o.node ≠ y ∨ o.canonical = true) → m'.obj? x = some o
  parent : ∀ o, m.obj? a = some o → o.node ≠ y → ∃ o' p', m'.obj? a = some o' ∧ o'.core = o.core ∧
    o'.ptr? y = some p' ∧ p'.handle = some n ∧ ∀ z, z ≠ y → o'.ptr? z = o.ptr? z
  tables : ∀ z, z ≠ y → m'.tableOf z = m.tableOf z

theorem HMem.followR_fast (sp : Spec V T) (S0 S : Stream V T) {m : HMem V} {a : Nat} {y : NodeId}
    {o : HObj V} {p : HPtr} {n b : Nat} {ob : HObj V} (ho : m.obj? a = some o) (hp : o.ptr? y = some p)
    (hn : p.handle = some n) (hb : m.objOf n = some b) (hob : m.obj? b = some ob)
    (hu : ob.usable p.ref = true) : m.followR sp S0 S a y = some (m, n, b) := by
  unfold HMem.followR
  simp only [ho, Option.bind_some, hp, hn, hb, hob, hu, ↓reduceIte]

theorem HMem.followR_slow (sp : Spec V T) (S0 S : Stream V T) {m : HMem V} {a : Nat} {y : NodeId}
    {o : HObj V} {p : HPtr} (ho : m.obj? a = some o) (hp : o.ptr? y = some p)
    (hnf : ∀ n b ob, p.handle = some n → m.objOf n = some b → m.obj? b = some ob → ob.usable p.ref = false) :
    m.followR sp S0 S a y =
      match ((m.setRef a y (m.slowRef S0 y p)).resolve a y).1.load sp S
          ((m.setRef a y (m.slowRef S0 y p)).resolve a y).2 (m.slowRef S0 y p) with
      | (m2, some b) => some (m2, ((m.setRef a y (m.slowRef S0 y p)).resolve a y).2, b)
      | (_, none) => none := by
  unfold HMem.followR HMem.slowRef
  simp only [ho, Option.bind_some, hp]
  cases hn : p.handle with
  | none => rfl
  | some n =>
    simp only
    cases hb : m.objOf n with
    | none => rfl
    | some b =>
      simp only
      cases hob : m.obj? b with
      | none => rfl
      | some ob => simp only [hnf n b ob hn hb hob, Bool.false_eq_true, ↓reduceIte]; rfl

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : HMem V}

/-- A snapshot at a position at least the reference r0, and at least the newest
version in the section, is at least the reference after Rule R. -/
theorem le_of_ruleR {S0 : Stream V T} {s : Nat} {y : NodeId} {r0 q : Nat}
    (hle : r0 ≤ q) (hn : ∀ wn, newest S0 s y = some wn → wn.recNo ≤ q) {x : Nat}
    (hx : ruleRRef S0 s y (some r0) = some x) : x ≤ q := by
  unfold ruleRRef at hx
  cases hnw : newest S0 s y with
  | none => rw [hnw] at hx; simp only [Option.some.injEq] at hx; omega
  | some wn =>
    rw [hnw] at hx
    have := hn wn hnw
    simp only at hx
    split at hx
    · simp only [Option.some.injEq] at hx; omega
    · simp only [Option.some.injEq] at hx; omega

/-- A snapshot of y in memory, at least as new as y's latest version, is at it. -/
theorem HEInv.snap_eq_lv (hinv : Inv sp db k) (hm : HEInv sp db S0 k m) {b : Nat} {ob : HObj V}
    (hob : m.obj? b = some ob) (hc : ob.canonical = false) {y : NodeId} (hny : ob.node = y) {r : Nat}
    (hr : (db.S.lv y).map (·.recNo) = some r) {q : Nat} (hq : ob.pos = some q) (hle : r ≤ q) :
    ob.pos = (db.S.lv y).map (·.recNo) := by
  obtain ⟨r1, w1, h1, h2, -⟩ := hm.snap b ob hob hc
  rw [hq, Option.some.injEq] at h1
  subst h1
  rw [hny] at h2
  obtain ⟨v, hv, hle2⟩ := hinv.le_lv h2
  rw [hv] at hr
  simp only [Option.map_some, Option.some.injEq] at hr
  rw [hq, hv]
  simp only [Option.map_some, Option.some.injEq]
  omega

end Follow

/-! ## The load on a live handle -/

section LoadOk

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {M : HMem V}

/-- The load on a live handle that holds an object, with a reference r at least
the newest version in the section: the invariant is kept; every object of
another node keeps its core; the handle then holds an object of its node,
usable for r; the table is the same. -/
theorem HEInv.load_ok (hinv : Inv sp db k) (hM : HEInv sp db S0 k M) {n : Nat} {hd : Handle}
    (hh : M.handle? n = some hd) {b0 : Nat} (hb0 : hd.obj = some b0) {r : Option Nat}
    (hr : ∀ x, r = some x → ∀ wn, newest S0 M.s hd.node = some wn → wn.recNo ≤ x)
    {M' : HMem V} {b : Nat} (hload : M.load sp db.S n r = (M', some b)) :
    HEInv sp db S0 k M' ∧
      (∀ x o, M.obj? x = some o → (o.node ≠ hd.node ∨ o.canonical = true) → M'.obj? x = some o) ∧
      (∃ ob, M'.obj? b = some ob ∧ ob.node = hd.node ∧ ob.usable r = true) ∧
      M'.objOf n = some b ∧ (∀ z, M'.tableOf z = M.tableOf z) ∧ M'.s = M.s := by
  obtain ⟨-, ob0, hob0, hon0⟩ := hM.tbl.obj_of_handle hh hb0
  cases hu : ob0.usable r with
  | true =>
    rw [HMem.load_usable sp db.S hh hb0 hob0 hu] at hload
    simp only [Prod.mk.injEq, Option.some.injEq] at hload
    obtain ⟨rfl, rfl⟩ := hload
    exact ⟨hM, fun x o ho _ => ho, ⟨ob0, hob0, hon0, hu⟩,
      by simp [HMem.objOf, hh, hb0], fun z => rfl, rfl⟩
  | false =>
    have hc : ob0.canonical = false := by
      cases hc0 : ob0.canonical with
      | false => rfl
      | true => simp [HObj.usable, hc0] at hu
    cases r with
    | none =>
      unfold HMem.load at hload
      simp only [hh, hb0, hob0, hu, Bool.false_eq_true, ↓reduceIte] at hload
      cases hload
    | some x =>
      cases hw : db.S.versionAt x hd.node with
      | none =>
        unfold HMem.load at hload
        simp only [hh, hb0, hob0, hu, Bool.false_eq_true, ↓reduceIte, hw] at hload
        cases hload
      | some w =>
        rw [HMem.load_installed sp db.S hh hb0 hob0 hu hw] at hload
        simp only [Prod.mk.injEq, Option.some.injEq] at hload
        obtain ⟨rfl, rfl⟩ := hload
        obtain ⟨hwn, hwr, -⟩ := hinv.version_node hw
        refine ⟨hM.install hinv hh hb0 hob0 hc hw (hr x rfl), ?_, ?_, ?_, fun z => rfl, rfl⟩
        · intro x' o ho hon
          have hx1 : x' ≠ M.nextObj := by
            intro he; rw [he, hM.freshO _ (Nat.le_refl _)] at ho; cases ho
          have hx2 : x' ≠ b0 := by
            intro he; rw [he, hob0, Option.some.injEq] at ho; subst ho
            rcases hon with hon | hon
            · exact hon hon0
            · rw [hc] at hon; cases hon
          rw [HMem.installed_obj?]; simp [hx1, hx2]; exact ho
        · refine ⟨HObj.ofVersion sp w, by rw [HMem.installed_obj?]; simp, by simp [HObj.ofVersion, hwn], ?_⟩
          simp [HObj.usable, HObj.ofVersion, hwr]
        · unfold HMem.objOf; rw [HMem.installed_handle?]; simp

end LoadOk

/-! ## The follow to a node with no live handle -/

section NewLoad

theorem HMem.emptyHandle_obj? (M : HMem V) (y : NodeId) (x : Nat) : (M.emptyHandle y).obj? x = M.obj? x := rfl

theorem HMem.emptyHandle_handle? (M : HMem V) (y : NodeId) (n : Nat) :
    (M.emptyHandle y).handle? n = if n = M.nextHandle then
      some { node := y, obj := none, written := none, dead := false } else M.handle? n := by
  show (M.setHandle M.nextHandle _).handle? n = _
  rw [HMem.handle?_setHandle]

theorem HMem.emptyHandle_tableOf (M : HMem V) (y z : NodeId) :
    (M.emptyHandle y).tableOf z = if z = y then some M.nextHandle else M.tableOf z := by
  show ((M.setHandle M.nextHandle _).setTable y M.nextHandle).tableOf z = _
  rw [HMem.tableOf_setTable]
  rfl

theorem HMem.filled_obj? (sp : Spec V T) (M : HMem V) (n : Nat) (hd : Handle) (w : Version V) (x : Nat) :
    (M.filled sp n hd w).obj? x = if x = M.nextObj then some (HObj.ofVersion sp w) else M.obj? x := by
  unfold HMem.filled
  simp only [HMem.obj?_setHandle]
  unfold HMem.obj?
  exact lookup_cons_eq _ _ _ _

theorem HMem.filled_handle? (sp : Spec V T) (M : HMem V) (n : Nat) (hd : Handle) (w : Version V) (n' : Nat) :
    (M.filled sp n hd w).handle? n' = if n' = n then some { hd with obj := some M.nextObj } else
      M.handle? n' := by
  unfold HMem.filled
  simp only [HMem.handle?_setHandle]
  rfl

theorem HMem.filled_tableOf (sp : Spec V T) (M : HMem V) (n : Nat) (hd : Handle) (w : Version V)
    (z : NodeId) : (M.filled sp n hd w).tableOf z = M.tableOf z := rfl

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {M : HMem V}

/-- The follow's slow path to a node y with no live handle (`HMem.resolve`,
`HMem.load`): a new live handle, holding the version read at r, and the pointer
holds it. The invariant is kept, every object keeps its core, and the object
reached is the new snapshot, of y, at r. -/
theorem HEInv.newLoad_ok (hinv : Inv sp db k) (hM : HEInv sp db S0 k M) {a : Nat} {o : HObj V}
    {y : NodeId} {p : HPtr} (ho : M.obj? a = some o) (hp : o.ptr? y = some p)
    (hfix : ruleRRef S0 M.s y p.ref = p.ref)
    (hheld : ∀ hd0, p.handle.bind M.handle? = some hd0 →
      hd0.dead = true ∧ maxRef p.ref hd0.written = p.ref)
    (hty : M.tableOf y = none) {r : Nat} {w : Version V}
    (hw : db.S.versionAt r y = some w) (hnew : ∀ wn, newest S0 M.s y = some wn → wn.recNo ≤ r) :
    HEInv sp db S0 k (((M.emptyHandle y).setObj a (o.setPtr y { p with handle := some M.nextHandle })).filled
      sp M.nextHandle { node := y, obj := none, written := none, dead := false } w) := by
  have hW := hM.addHandle hinv hty hw hnew
  have halt : a < M.nextObj := Nat.lt_of_not_le (fun h => by rw [hM.freshO a h] at ho; cases ho)
  have hoW : (M.withNew sp y w).obj? a = some o := by
    rw [HMem.withNew_obj?]; simp [show a ≠ M.nextObj by omega]; exact ho
  have hh_lt : ∀ n hd, M.handle? n = some hd → n < M.nextHandle := by
    intro n hd h
    exact Nat.lt_of_not_le (fun hle => by rw [hM.freshH n hle] at h; cases h)
  have hheldW : ∀ hd0, p.handle.bind (M.withNew sp y w).handle? = some hd0 →
      hd0.dead = true ∧ maxRef p.ref hd0.written = p.ref := by
    intro hd0 h
    cases hpn : p.handle with
    | none => rw [hpn] at h; cases h
    | some n =>
      rw [hpn] at h
      simp only [Option.bind_some] at h
      rw [HMem.withNew_handle?] at h
      split at h
      · rename_i hn
        obtain ⟨hdq, hhq, -⟩ := hM.tbl.ptrNode ho hp hpn
        have := hh_lt n hdq hhq
        omega
      · exact hheld hd0 (by rw [hpn]; simp only [Option.bind_some]; exact h)
  have hX := hW.takeLive hoW hp hfix hheldW (n := M.nextHandle) (by rw [HMem.withNew_tableOf]; simp)
  apply hX.congr
  · intro x
    rw [HMem.filled_obj?, HMem.obj?_setObj, HMem.obj?_setObj, HMem.emptyHandle_obj?, HMem.withNew_obj?]
    simp only [HMem.setObj_nextObj]
    show (if x = M.nextObj then _ else _) = _
    by_cases h1 : x = M.nextObj
    · subst h1
      have h2 : M.nextObj ≠ a := by omega
      simp [h2]
    · simp [h1]
  · intro n
    rw [HMem.filled_handle?, HMem.handle?_setObj, HMem.handle?_setObj, HMem.emptyHandle_handle?,
      HMem.withNew_handle?]
    by_cases h : n = M.nextHandle
    · simp [h]; rfl
    · simp [h]
  · intro z
    rw [HMem.filled_tableOf, HMem.tableOf_setObj, HMem.tableOf_setObj, HMem.emptyHandle_tableOf,
      HMem.withNew_tableOf]
  · rfl
  · rfl
  · rfl
  · rfl
  · -- the objects' keys
    show (((M.emptyHandle y).setObj a _).nextObj, HObj.ofVersion sp w) :: ((M.emptyHandle y).setObj a _).objs
      |>.map (·.1) |>.Nodup
    simp only [List.map_cons, List.nodup_cons]
    have hnd : (((M.emptyHandle y).setObj a (o.setPtr y { p with handle := some M.nextHandle })).objs.map
        (·.1)).Nodup := by
      unfold HMem.setObj
      simp only [List.map_cons, List.nodup_cons]
      refine ⟨?_, (List.Sublist.map _ List.filter_sublist).nodup hM.objNodup⟩
      intro hmem
      obtain ⟨q, hq, hqa⟩ := List.mem_map.mp hmem
      have := (List.mem_filter.mp hq).2
      rw [hqa] at this
      simp at this
    refine ⟨fun hmem => ?_, hnd⟩
    obtain ⟨q, hq, hqn⟩ := List.mem_map.mp hmem
    have := lookup_ne_none_of_mem hq
    change ((M.emptyHandle y).setObj a (o.setPtr y { p with handle := some M.nextHandle })).obj? q.1 ≠ none
      at this
    rw [hqn, HMem.obj?_setObj] at this
    simp only [HMem.setObj_nextObj] at this
    have h1 : (M.emptyHandle y).nextObj ≠ a := by show M.nextObj ≠ a; omega
    simp only [h1, ↓reduceIte, HMem.emptyHandle_obj?] at this
    exact this (hM.freshO _ (Nat.le_refl _))
  · -- the handles' keys
    unfold HMem.filled
    simp only
    apply setHandle_nodup
    show ((M.emptyHandle y).handles.map (·.1)).Nodup
    unfold HMem.emptyHandle
    exact setHandle_nodup M _ _ hM.hNodup
  · -- the table's keys
    show ((M.setHandle M.nextHandle _).setTable y M.nextHandle).table.map (·.1) |>.Nodup
    unfold HMem.setTable
    simp only [HMem.setHandle_table, List.map_cons, List.nodup_cons]
    refine ⟨?_, (List.Sublist.map _ List.filter_sublist).nodup hM.tbl.nodup⟩
    intro hmem
    obtain ⟨q, hq, hqy⟩ := List.mem_map.mp hmem
    have := (List.mem_filter.mp hq).2
    rw [hqy] at this
    simp at this

end NewLoad

/-! ## The readers' follow keeps the invariant -/

section FollowOk

/-- When the handle a pointer holds holds no canonical object, the record rule
gives the slow path's reference. -/
theorem HMem.ptrRef_eq_slowRef (m : HMem V) (S0 : Stream V T) (y : NodeId) (p : HPtr)
    (h : ∀ hd b ob, p.handle.bind m.handle? = some hd → hd.obj = some b → m.obj? b = some ob →
      ob.canonical = false) : m.ptrRef S0 y p = m.slowRef S0 y p := by
  unfold HMem.ptrRef HMem.slowRef
  cases hh : p.handle.bind m.handle? with
  | none => simp [maxRef_none]
  | some hd =>
    simp only [Option.bind_some]
    cases hb : hd.obj with
    | none => rfl
    | some b =>
      simp only [Option.bind_some]
      cases hob : m.obj? b with
      | none => rfl
      | some ob =>
        simp only
        rw [h hd b ob hh hb hob]
        rfl

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : HMem V}

/-- An object of y usable for the reference that gives y's latest version, y not
in D and written, is readable. -/
theorem HEInv.readable_of_usable (hinv : Inv sp db k) (hm : HEInv sp db S0 k m) {b : Nat} {ob : HObj V}
    {y : NodeId} (hob : m.obj? b = some ob) (hon : ob.node = y) (hD : inD db.D y = false)
    (hw : written sp y = true) {r : Option Nat} (hu : ob.usable r = true)
    (hr : r = (db.S.lv y).map (·.recNo)) : HReadable sp db m b y := by
  refine ⟨ob, hob, hon, ?_⟩
  cases hc : ob.canonical with
  | true => exact Or.inl rfl
  | false =>
    right
    refine ⟨hD, hw, ?_⟩
    unfold HObj.usable at hu
    rw [hc, Bool.false_or] at hu
    cases hrx : r with
    | none => rw [hrx] at hu; simp at hu
    | some x =>
      rw [hrx] at hu
      cases hq : ob.pos with
      | none => rw [hq] at hu; simp at hu
      | some q =>
        rw [hq] at hu
        simp only [decide_eq_true_eq] at hu
        rw [hrx] at hr
        have := hm.snap_eq_lv hinv hob hc hon hr.symm hq hu
        rw [hq] at this
        exact this

/-- The objects of the memory after the follow to a node with no live handle:
the new snapshot, object a with the same core, every other object as it was. -/
theorem HMem.filled_frame (sp : Spec V T) {M : HMem V} {a : Nat} {o1 o1' : HObj V} (y : NodeId)
    (ho1 : M.obj? a = some o1) (hc : o1'.core = o1.core) (hfresh : M.obj? M.nextObj = none)
    (n : Nat) (hd : Handle) (w : Version V) :
    ∀ x o', M.obj? x = some o' →
      ∃ o'', (((M.emptyHandle y).setObj a o1').filled sp n hd w).obj? x = some o'' ∧ o''.core = o'.core := by
  intro x o' hx
  have hxn : x ≠ M.nextObj := by intro he; rw [he, hfresh] at hx; cases hx
  rw [HMem.filled_obj?]
  have hxn' : x ≠ ((M.emptyHandle y).setObj a o1').nextObj := hxn
  simp only [hxn', ↓reduceIte]
  rw [HMem.obj?_setObj, HMem.emptyHandle_obj?]
  by_cases hxa : x = a
  · subst hxa
    rw [ho1, Option.some.injEq] at hx
    subst hx
    exact ⟨o1', by simp, hc⟩
  · simp only [hxa, ↓reduceIte]
    exact ⟨o', hx, rfl⟩

theorem HMem.filled_new (sp : Spec V T) (M : HMem V) (n : Nat) (hd : Handle) (w : Version V) :
    (M.filled sp n hd w).obj? M.nextObj = some (HObj.ofVersion sp w) := by
  rw [HMem.filled_obj?]; simp

/-- The readers' follow of the pointer of object a for a node y keeps the
invariant, and leaves what `HFollowed` says. -/
theorem HEInv.followR_ok (hinv : Inv sp db k) (hm : HEInv sp db S0 k m) {a : Nat} {o : HObj V}
    {y : NodeId} (ho : m.obj? a = some o) {m' : HMem V} {n b : Nat}
    (hf : m.followR sp S0 db.S a y = some (m', n, b)) : HFollowed sp S0 db k m m' a y n b := by
  cases hp : o.ptr? y with
  | none => unfold HMem.followR at hf; simp [ho, hp] at hf
  | some p =>
  have hgoodp : ∀ o2 p2, m.obj? a = some o2 → o2.ptr? y = some p2 → o = o2 ∧ p = p2 := by
    intro o2 p2 h1 h2
    rw [ho, Option.some.injEq] at h1
    subst h1
    rw [hp, Option.some.injEq] at h2
    exact ⟨rfl, h2⟩
  by_cases hfast : ∃ n0 b0 ob0, p.handle = some n0 ∧ m.objOf n0 = some b0 ∧ m.obj? b0 = some ob0 ∧
      ob0.usable p.ref = true
  · -- The fast path: nothing changes.
    obtain ⟨n0, b0, ob0, hn0, hb0, hob0, hu0⟩ := hfast
    rw [HMem.followR_fast sp S0 db.S ho hp hn0 hb0 hob0 hu0] at hf
    simp only [Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl, rfl⟩ := hf
    obtain ⟨hd0, hh0, hny0⟩ := hm.tbl.ptrNode ho hp hn0
    have hb0' : hd0.obj = some b0 := by simpa [HMem.objOf, hh0] using hb0
    obtain ⟨-, ob0', hob0', hon0⟩ := hm.tbl.obj_of_handle hh0 hb0'
    rw [hob0, Option.some.injEq] at hob0'
    subst hob0'
    have hony : ob0.node = y := by rw [hon0, hny0]
    have htb0 : m.tableOf y = some n0 := by
      rw [← hny0]; exact hm.tbl.liveIn hh0 (hm.tbl.live_of_obj hh0 hb0')
    refine ⟨hm, fun x o' hx _ => ⟨o', hx, rfl⟩, ⟨ob0, hob0, hony⟩, ?_, hb0, htb0, fun x o' hx _ _ => hx,
      ?_, fun _ _ => rfl⟩
    · intro o2 p2 ho2 hp2 hgood hw
      obtain ⟨h1, h2⟩ := hgoodp o2 p2 ho2 hp2
      subst h1; subst h2
      rcases hgood with ⟨hD, n', hn', ht', hc'⟩ | ⟨hD, hr⟩
      · -- y in D: the handle holds y's canonical object.
        rw [hn0, Option.some.injEq] at hn'
        subst hn'
        obtain ⟨c, hcy⟩ := Option.isSome_iff_exists.mp hc'
        obtain ⟨n'', oc, ht'', hoc, hocx, hcc⟩ := (m.canonicalOf_eq_some y c).mp hcy
        rw [ht', Option.some.injEq] at ht''
        subst ht''
        rw [hb0, Option.some.injEq] at hoc
        subst hoc
        rw [hob0, Option.some.injEq] at hocx
        subst hocx
        exact ⟨ob0, hob0, hony, Or.inl hcc⟩
      · -- y not in D: the record rule gives y's latest version, which the object serves.
        cases hc0 : ob0.canonical with
        | true => exact ⟨ob0, hob0, hony, Or.inl hc0⟩
        | false =>
          have hl0 := hm.tbl.live_of_obj hh0 hb0'
          have hpr : m.ptrRef S0 y p = ruleRRef S0 m.s y p.ref := by
            unfold HMem.ptrRef
            simp only [hn0, Option.bind_some, hh0, hb0', hob0, hc0, Bool.false_eq_true, ↓reduceIte,
              hm.liveW n0 hd0 hh0 hl0, maxRef_none]
          rw [hpr] at hr
          cases hpref : p.ref with
          | none => simp [HObj.usable, hc0, hpref] at hu0
          | some r0 =>
            cases hq : ob0.pos with
            | none => simp [HObj.usable, hc0, hpref, hq] at hu0
            | some q =>
              have hle : r0 ≤ q := by simpa [HObj.usable, hc0, hpref, hq] using hu0
              have hnw : ∀ wn, newest S0 m.s y = some wn → wn.recNo ≤ q := by
                intro wn hwn
                obtain ⟨q', hq', hle'⟩ := hm.ruleR n0 hd0 b0 ob0 wn hh0 hb0' hob0 hc0
                  (by rw [hny0]; exact hwn)
                rw [hq, Option.some.injEq] at hq'
                omega
              rw [hpref] at hr
              obtain ⟨x, hx, -⟩ := ruleRRef_ge (S0 := S0) (s := m.s) (y := y) (rfl : some r0 = some r0)
              rw [hx] at hr
              have hlr := le_of_ruleR hle hnw hx
              have := hm.snap_eq_lv hinv hob0 hc0 hony hr.symm hq hlr
              exact ⟨ob0, hob0, hony, Or.inr ⟨hD, hw, this⟩⟩
    · intro o2 ho2 _
      rw [ho, Option.some.injEq] at ho2
      subst ho2
      exact ⟨o, p, ho, rfl, hp, hn0, fun _ _ => rfl⟩
  · -- The slow path.
    have hnf : ∀ n0 b0 ob0, p.handle = some n0 → m.objOf n0 = some b0 → m.obj? b0 = some ob0 →
        ob0.usable p.ref = false := by
      intro n0 b0 ob0 h1 h2 h3
      cases hu : ob0.usable p.ref with
      | false => rfl
      | true => exact absurd ⟨n0, b0, ob0, h1, h2, h3, hu⟩ hfast
    rw [HMem.followR_slow sp S0 db.S ho hp hnf] at hf
    have hm1 := hm.writeBack hinv ho hp
    rw [HMem.setRef_eq ho hp] at hf hm1
    have ho1 := HMem.obj?_setObj_self m a (o.setPtr y { p with ref := m.slowRef S0 y p })
    have hp1 : (o.setPtr y { p with ref := m.slowRef S0 y p }).ptr? y =
        some { p with ref := m.slowRef S0 y p } := by
      rw [HObj.ptr?_setPtr_of hp]; simp
    have hgoodD : HPtrGood S0 db m y p →
        inD db.D y = false ∧ m.ptrRef S0 y p = (db.S.lv y).map (·.recNo) := by
      intro hg
      rcases hg with ⟨hD, n', hn', ht', hc'⟩ | h
      · exfalso
        obtain ⟨c, hcy⟩ := Option.isSome_iff_exists.mp hc'
        obtain ⟨n'', oc, ht'', hoc, hocx, hcc⟩ := (m.canonicalOf_eq_some y c).mp hcy
        rw [ht', Option.some.injEq] at ht''
        subst ht''
        have := hnf n' c oc hn' hoc hocx
        simp [HObj.usable, hcc] at this
      · exact h
    have hrefeq : m.ptrRef S0 y p = m.slowRef S0 y p := by
      apply HMem.ptrRef_eq_slowRef
      intro hd' b' ob' h1 h2 h3
      cases hpn : p.handle with
      | none => rw [hpn] at h1; cases h1
      | some n' =>
        rw [hpn] at h1
        simp only [Option.bind_some] at h1
        cases hc : ob'.canonical with
        | false => rfl
        | true =>
          have := hnf n' b' ob' hpn (by simp [HMem.objOf, h1, h2]) h3
          simp [HObj.usable, hc] at this
    have hsec : ∀ x, m.slowRef S0 y p = some x → ∀ wn, newest S0 m.s y = some wn → wn.recNo ≤ x := by
      intro x hx wn hwn
      obtain ⟨x', hx', hle⟩ := ruleRRef_ge_newest hwn p.ref
      obtain ⟨x'', hx'', hle'⟩ := m.slowRef_ge S0 y p hx'
      rw [hx, Option.some.injEq] at hx''
      omega
    have hfr1 : ∀ x o', m.obj? x = some o' →
        ∃ o'', (m.setObj a (o.setPtr y { p with ref := m.slowRef S0 y p })).obj? x = some o'' ∧
          o''.core = o'.core := by
      intro x o' hx
      rw [HMem.obj?_setObj]
      split
      · rename_i hxa; rw [hxa, ho, Option.some.injEq] at hx; subst hx
        exact ⟨_, rfl, HObj.setPtr_core _ _ _⟩
      · exact ⟨o', hx, rfl⟩
    -- Objects at other addresses are as they were after the write-back.
    have hne1 : ∀ x o', m.obj? x = some o' → x ≠ a →
        (m.setObj a (o.setPtr y { p with ref := m.slowRef S0 y p })).obj? x = some o' := by
      intro x o' hx hxa
      rw [HMem.obj?_setObj_ne _ _ hxa]; exact hx
    -- Object a's pointers, after one or two changes of its pointer for y.
    have hptrs1 : ∀ (q : HPtr) z, z ≠ y → ((o.setPtr y { p with ref := m.slowRef S0 y p }).setPtr y q).ptr? z =
        o.ptr? z := by
      intro q z hz
      simp [HObj.ptr?_setPtr, hz]
    have hptrs0 : ∀ z, z ≠ y → (o.setPtr y { p with ref := m.slowRef S0 y p }).ptr? z = o.ptr? z := by
      intro z hz
      rw [HObj.ptr?_setPtr]
      simp [hz]
    by_cases hlive : ∃ n0 hd0, p.handle = some n0 ∧ m.handle? n0 = some hd0 ∧ hd0.dead = false
    · -- The pointer holds a live handle.
      obtain ⟨n0, hd0, hn0, hh0, hl0⟩ := hlive
      obtain ⟨hdq, hhq, hy0⟩ := hm.tbl.ptrNode ho hp hn0
      rw [hh0, Option.some.injEq] at hhq
      subst hhq
      rw [HMem.resolve_live ho1 hp1 hn0 (by rw [HMem.handle?_setObj]; exact hh0) hl0] at hf
      obtain ⟨hd', b0, ob0, hh', -, -, hb0, hob0, hon0⟩ := hm.tbl.entry (hm.tbl.liveIn hh0 hl0)
      rw [hh0, Option.some.injEq] at hh'
      subst hh'
      have htb0 : m.tableOf y = some n0 := by rw [← hy0]; exact hm.tbl.liveIn hh0 hl0
      cases hload : (m.setObj a (o.setPtr y { p with ref := m.slowRef S0 y p })).load sp db.S n0
          (m.slowRef S0 y p) with
      | mk M' ob =>
        cases ob with
        | none => rw [hload] at hf; cases hf
        | some b' =>
          rw [hload] at hf
          simp only [Option.some.injEq, Prod.mk.injEq] at hf
          obtain ⟨rfl, rfl, rfl⟩ := hf
          obtain ⟨hi, hfr, ⟨ob, hob, hon, hu⟩, hobn, htbl, -⟩ :=
            hm1.load_ok hinv (by rw [HMem.handle?_setObj]; exact hh0) hb0
              (fun x hx wn hwn => hsec x hx wn (by rw [hy0] at hwn; exact hwn)) hload
          refine ⟨hi, fun x o' hx hxn => ?_, ⟨ob, hob, by rw [hon, hy0]⟩, ?_, hobn,
            by rw [htbl, HMem.tableOf_setObj]; exact htb0, ?_, ?_, ?_⟩
          · obtain ⟨o'', hx'', hc''⟩ := hfr1 x o' hx
            have hxn' : o''.node ≠ hd0.node := by
              rw [show o''.node = o'.node from congrArg (fun c => c.1) hc'', hy0]; exact hxn
            exact ⟨o'', hfr x o'' hx'' (Or.inl hxn'), hc''⟩
          · intro o2 p2 ho2 hp2 hgood hw
            obtain ⟨h1, h2⟩ := hgoodp o2 p2 ho2 hp2
            subst h1; subst h2
            obtain ⟨hD, hr⟩ := hgoodD hgood
            exact hi.readable_of_usable hinv hob (by rw [hon, hy0]) hD hw hu (by rw [← hrefeq]; exact hr)
          · intro x o' hx hxa hcase
            exact hfr x o' (hne1 x o' hx hxa) (by rw [hy0]; exact hcase)
          · intro o2 ho2 hny
            rw [ho, Option.some.injEq] at ho2
            subst ho2
            refine ⟨_, { p with ref := m.slowRef S0 y p }, hfr a _ ho1 (Or.inl (by
              rw [HObj.setPtr_node, hy0]; exact hny)), HObj.setPtr_core _ _ _, hp1, hn0, hptrs0⟩
          · intro z hz
            rw [htbl, HMem.tableOf_setObj]
    · -- The pointer holds no live handle.
      have hnl : ∀ n0 hd0, ({ p with ref := m.slowRef S0 y p } : HPtr).handle = some n0 →
          (m.setObj a (o.setPtr y { p with ref := m.slowRef S0 y p })).handle? n0 = some hd0 →
          hd0.dead = true := by
        intro n0 hd0 h1 h2
        rw [HMem.handle?_setObj] at h2
        cases hd : hd0.dead with
        | true => rfl
        | false => exact absurd ⟨n0, hd0, h1, h2, hd⟩ hlive
      have hfix : ruleRRef S0 (m.setObj a (o.setPtr y { p with ref := m.slowRef S0 y p })).s y
          ({ p with ref := m.slowRef S0 y p } : HPtr).ref = ({ p with ref := m.slowRef S0 y p } : HPtr).ref := by
        rw [HMem.setObj_s]; exact HMem.ruleR_slowRef m S0 y p
      have hheld : ∀ hd0, ({ p with ref := m.slowRef S0 y p } : HPtr).handle.bind
          (m.setObj a (o.setPtr y { p with ref := m.slowRef S0 y p })).handle? = some hd0 →
          hd0.dead = true ∧ maxRef ({ p with ref := m.slowRef S0 y p } : HPtr).ref hd0.written =
            ({ p with ref := m.slowRef S0 y p } : HPtr).ref := by
        intro hd0 h
        rw [HMem.handle?_setObj_fun] at h
        have h' : p.handle.bind m.handle? = some hd0 := h
        refine ⟨?_, ?_⟩
        · cases hpn : p.handle with
          | none => rw [hpn] at h'; cases h'
          | some n0 =>
            rw [hpn] at h'
            simp only [Option.bind_some] at h'
            exact hnl n0 hd0 hpn (by rw [HMem.handle?_setObj]; exact h')
        · show maxRef (m.slowRef S0 y p) hd0.written = m.slowRef S0 y p
          unfold HMem.slowRef
          rw [h']
          exact maxRef_idem _ _
      cases htb : m.tableOf y with
      | some n1 =>
        rw [HMem.resolve_table ho1 hp1 hnl (by rw [HMem.tableOf_setObj]; exact htb)] at hf
        have hm2 := hm1.takeLive ho1 hp1 hfix hheld (by rw [HMem.tableOf_setObj]; exact htb)
        obtain ⟨hd1, b1, ob1, hh1, hl1, hny1, hb1, hob1, hon1⟩ := hm.tbl.entry htb
        cases hload : ((m.setObj a (o.setPtr y { p with ref := m.slowRef S0 y p })).setObj a
            ((o.setPtr y { p with ref := m.slowRef S0 y p }).setPtr y
              { ({ p with ref := m.slowRef S0 y p } : HPtr) with handle := some n1 })).load sp db.S n1
            (m.slowRef S0 y p) with
        | mk M' ob =>
          cases ob with
          | none => rw [hload] at hf; cases hf
          | some b' =>
            rw [hload] at hf
            simp only [Option.some.injEq, Prod.mk.injEq] at hf
            obtain ⟨rfl, rfl, rfl⟩ := hf
            obtain ⟨hi, hfr, ⟨ob, hob, hon, hu⟩, hobn, htbl, -⟩ :=
              hm2.load_ok hinv (by rw [HMem.handle?_setObj, HMem.handle?_setObj]; exact hh1) hb1
                (fun x hx wn hwn => hsec x hx wn (by rw [hny1] at hwn; exact hwn)) hload
            have hx2 : ∀ x o'', (m.setObj a (o.setPtr y { p with ref := m.slowRef S0 y p })).obj? x = some o'' →
                ∃ o2, ((m.setObj a (o.setPtr y { p with ref := m.slowRef S0 y p })).setObj a
                  ((o.setPtr y { p with ref := m.slowRef S0 y p }).setPtr y
                    { ({ p with ref := m.slowRef S0 y p } : HPtr) with handle := some n1 })).obj? x = some o2 ∧
                  o2.core = o''.core := by
              intro x o'' hx''
              rw [HMem.obj?_setObj]
              split
              · rename_i hxa
                rw [hxa, ho1, Option.some.injEq] at hx''
                subst hx''
                exact ⟨_, rfl, HObj.setPtr_core _ _ _⟩
              · exact ⟨o'', hx'', rfl⟩
            refine ⟨hi, fun x o' hx hxn => ?_, ⟨ob, hob, by rw [hon, hny1]⟩, ?_, hobn,
              by rw [htbl, HMem.tableOf_setObj, HMem.tableOf_setObj]; exact htb, ?_, ?_, ?_⟩
            · obtain ⟨o'', hx'', hc''⟩ := hfr1 x o' hx
              obtain ⟨o2, hx2', hc2⟩ := hx2 x o'' hx''
              have hxn' : o2.node ≠ hd1.node := by
                rw [show o2.node = o'.node from (congrArg (fun c => c.1) hc2).trans
                  (congrArg (fun c => c.1) hc''), hny1]; exact hxn
              exact ⟨o2, hfr x o2 hx2' (Or.inl hxn'), by rw [hc2, hc'']⟩
            · intro o2 p2 ho2 hp2 hgood hw
              obtain ⟨h1, h2⟩ := hgoodp o2 p2 ho2 hp2
              subst h1; subst h2
              obtain ⟨hD, hr⟩ := hgoodD hgood
              exact hi.readable_of_usable hinv hob (by rw [hon, hny1]) hD hw hu (by rw [← hrefeq]; exact hr)
            · intro x o' hx hxa hcase
              refine hfr x o' ?_ (by rw [hny1]; exact hcase)
              rw [HMem.obj?_setObj_ne _ _ hxa]
              exact hne1 x o' hx hxa
            · intro o2 ho2 hny
              rw [ho, Option.some.injEq] at ho2
              subst ho2
              refine ⟨_, { ({ p with ref := m.slowRef S0 y p } : HPtr) with handle := some n1 },
                hfr a _ (HMem.obj?_setObj_self _ _ _) (Or.inl (by
                  rw [HObj.setPtr_node, HObj.setPtr_node, hny1]; exact hny)),
                by rw [HObj.setPtr_core, HObj.setPtr_core], ?_, rfl, hptrs1 _⟩
              rw [HObj.ptr?_setPtr_of hp1]; simp
            · intro z hz
              rw [htbl, HMem.tableOf_setObj, HMem.tableOf_setObj]
      | none =>
        rw [HMem.resolve_new ho1 hp1 hnl (by rw [HMem.tableOf_setObj]; exact htb)] at hf
        have hhn : HMem.handle? (((m.setObj a (o.setPtr y { p with ref := m.slowRef S0 y p })).emptyHandle y).setObj
            a ((o.setPtr y { p with ref := m.slowRef S0 y p }).setPtr y
              { ({ p with ref := m.slowRef S0 y p } : HPtr) with
                handle := some (m.setObj a (o.setPtr y { p with ref := m.slowRef S0 y p })).nextHandle }))
            (m.setObj a (o.setPtr y { p with ref := m.slowRef S0 y p })).nextHandle =
            some { node := y, obj := none, written := none, dead := false } := by
          rw [HMem.handle?_setObj, HMem.emptyHandle_handle?]; simp
        -- The frame and the new object, before the reference is known.
        have hfreshM1 : (m.setObj a (o.setPtr y { p with ref := m.slowRef S0 y p })).obj?
            (m.setObj a (o.setPtr y { p with ref := m.slowRef S0 y p })).nextObj = none := by
          rw [HMem.setObj_nextObj, HMem.obj?_setObj]
          have hna : m.nextObj ≠ a := by
            intro he; rw [← he, hm.freshO _ (Nat.le_refl _)] at ho; cases ho
          simp only [hna, ↓reduceIte]
          exact hm.freshO _ (Nat.le_refl _)
        have hfr2 := HMem.filled_frame sp y ho1 (o1' := (o.setPtr y { p with ref := m.slowRef S0 y p }).setPtr y
            { ({ p with ref := m.slowRef S0 y p } : HPtr) with
              handle := some (m.setObj a (o.setPtr y { p with ref := m.slowRef S0 y p })).nextHandle })
          (HObj.setPtr_core _ _ _) hfreshM1
        -- The objects after the load, at the addresses that were in use.
        have hfill : ∀ (hd : Handle) (w : Version V) x,
            (m.setObj a (o.setPtr y { p with ref := m.slowRef S0 y p })).obj? x ≠ none →
            ((((m.setObj a (o.setPtr y { p with ref := m.slowRef S0 y p })).emptyHandle y).setObj a
              ((o.setPtr y { p with ref := m.slowRef S0 y p }).setPtr y
                { ({ p with ref := m.slowRef S0 y p } : HPtr) with
                  handle := some (m.setObj a (o.setPtr y { p with ref := m.slowRef S0 y p })).nextHandle })).filled
              sp (m.setObj a (o.setPtr y { p with ref := m.slowRef S0 y p })).nextHandle hd w).obj? x =
            if x = a then some ((o.setPtr y { p with ref := m.slowRef S0 y p }).setPtr y
                { ({ p with ref := m.slowRef S0 y p } : HPtr) with
                  handle := some (m.setObj a (o.setPtr y { p with ref := m.slowRef S0 y p })).nextHandle })
            else (m.setObj a (o.setPtr y { p with ref := m.slowRef S0 y p })).obj? x := by
          intro hd w x hx
          rw [HMem.filled_obj?]
          have hxn : x ≠ (((m.setObj a (o.setPtr y { p with ref := m.slowRef S0 y p })).emptyHandle y).setObj a
              ((o.setPtr y { p with ref := m.slowRef S0 y p }).setPtr y
                { ({ p with ref := m.slowRef S0 y p } : HPtr) with
                  handle := some (m.setObj a (o.setPtr y { p with ref := m.slowRef S0 y p })).nextHandle })).nextObj := by
            intro he
            apply hx
            rw [he]
            exact hfreshM1
          simp only [hxn, ↓reduceIte]
          rw [HMem.obj?_setObj, HMem.emptyHandle_obj?]
        cases hsr : m.slowRef S0 y p with
        | none =>
          rw [hsr] at hf hhn
          unfold HMem.load at hf
          rw [hhn] at hf
          simp at hf
        | some r =>
          cases hw : db.S.versionAt r y with
          | none =>
            rw [hsr] at hf hhn
            unfold HMem.load at hf
            rw [hhn] at hf
            simp [hw] at hf
          | some w =>
            have hm4 := hm1.newLoad_ok hinv ho1 hp1 hfix hheld (by rw [HMem.tableOf_setObj]; exact htb)
              (r := r) (w := w) hw (fun wn hwn => hsec r hsr wn hwn)
            have hfr3 := hfr2 (m.setObj a (o.setPtr y { p with ref := m.slowRef S0 y p })).nextHandle
              { node := y, obj := none, written := none, dead := false } w
            have hfill' := hfill { node := y, obj := none, written := none, dead := false } w
            have hne1' := hne1
            rw [hsr] at hf hhn hm4 hfr3 hfill' hne1' hptrs1
            rw [HMem.load_filled sp db.S hhn rfl hw] at hf
            simp only [Option.some.injEq, Prod.mk.injEq] at hf
            obtain ⟨rfl, rfl, rfl⟩ := hf
            obtain ⟨hwn, hwr, -⟩ := hinv.version_node hw
            refine ⟨hm4, fun x o' hx _ => ?_, ⟨HObj.ofVersion sp w, HMem.filled_new sp _ _ _ w,
              by simp [HObj.ofVersion, hwn]⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
            · obtain ⟨o'', hx'', hc''⟩ := hfr1 x o' hx
              rw [hsr] at hx''
              obtain ⟨o3, h3, hc3⟩ := hfr3 x o'' hx''
              exact ⟨o3, h3, by rw [hc3, hc'']⟩
            · intro o2 p2 ho2 hp2 hgood hwy
              obtain ⟨h1, h2⟩ := hgoodp o2 p2 ho2 hp2
              subst h1; subst h2
              obtain ⟨hD, hr⟩ := hgoodD hgood
              rw [hrefeq, hsr] at hr
              refine ⟨HObj.ofVersion sp w, HMem.filled_new sp _ _ _ w, by simp [HObj.ofVersion, hwn],
                Or.inr ⟨hD, hwy, ?_⟩⟩
              rw [← hr]
              simp [HObj.ofVersion, hwr]
            · unfold HMem.objOf
              rw [HMem.filled_handle?]
              simp
            · rw [HMem.filled_tableOf, HMem.tableOf_setObj, HMem.emptyHandle_tableOf]
              simp
            · intro x o' hx hxa hcase
              have hx1 := hne1' x o' hx hxa
              rw [hfill' x (by rw [hx1]; simp)]
              simp only [hxa, ↓reduceIte]
              exact hx1
            · intro o2 ho2 hny
              rw [ho, Option.some.injEq] at ho2
              subst ho2
              refine ⟨(o.setPtr y { p with ref := some r }).setPtr y
                  { ({ p with ref := some r } : HPtr) with
                    handle := some (m.setObj a (o.setPtr y { p with ref := some r })).nextHandle },
                { ({ p with ref := some r } : HPtr) with
                    handle := some (m.setObj a (o.setPtr y { p with ref := some r })).nextHandle },
                by rw [hfill' a (by rw [HMem.obj?_setObj_self]; simp)]; simp only [↓reduceIte],
                by rw [HObj.setPtr_core, HObj.setPtr_core], ?_, rfl, hptrs1 _⟩
              rw [HObj.ptr?_setPtr, HObj.ptr?_setPtr_of hp]
              simp
            · intro z hz
              rw [HMem.filled_tableOf, HMem.tableOf_setObj, HMem.emptyHandle_tableOf, HMem.tableOf_setObj]
              simp [hz]

end FollowOk

end SIS
