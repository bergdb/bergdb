/-
Proofs about the physical layer with handles (bergdb item 009, step 2d), part 2:
the invariant of the memory with handles (`HEInv`): INV-CAN, INV-SNAP,
INV-SLOT for the record rule, the live pointers of current canonical objects,
and the table and the handles; and that an eviction keeps it.
-/
import SIS.Proof.HandleMem

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## The invariant -/

/-- An object whose pointers matter for records: a canonical object of a
written node that is current at k or in D. -/
def HRelevant (sp : Spec V T) (db : DB V T) (k : Nat) (o : HObj V) : Prop :=
  o.canonical = true ∧ written sp o.node = true ∧
    (reachable sp db.P k o.node = true ∨ inD db.D o.node = true)

/-- What a snapshot of version w asks of its pointer p for pointee y: its
reference after Rule R is at least w's reference after Rule R (a follow only
raises a pointer's reference). -/
def HSnapPtr (S0 : Stream V T) (m : HMem V) (w : Version V) (y : NodeId) (p : HPtr) : Prop :=
  ∀ r0, ruleRRef S0 m.s y (w.ref? y) = some r0 → ∃ r1, ruleRRef S0 m.s y p.ref = some r1 ∧ r0 ≤ r1

/-- A snapshot o: exactly the version w of its node at its position, with a
pointer for each pointee of its history, each as `HSnapPtr` asks. -/
def HSnapExact (sp : Spec V T) (S0 : Stream V T) (db : DB V T) (m : HMem V) (o : HObj V) : Prop :=
  ∃ r w, o.pos = some r ∧ db.S.versionAt r o.node = some w ∧ o.hist = w.hist ∧
    o.level = w.level ∧ o.isData = w.isData ∧
    (∀ y ∈ pointees sp o.hist, (o.ptr? y).isSome) ∧
    ∀ y p, o.ptr? y = some p → HSnapPtr S0 m w y p

/-- Pointer p holds y's live handle, which holds y's canonical object. -/
def HMem.HoldsLive (m : HMem V) (y : NodeId) (p : HPtr) : Prop :=
  ∃ n, p.handle = some n ∧ m.tableOf y = some n ∧ (m.canonicalOf y).isSome

/-- INV-SLOT for pointer p of a relevant object o for pointee y: for y not in D,
the record rule gives y's latest version; for y in D, the pointer holds y's
live handle with y's canonical object, or o's node is in D with an index at
most y's (it is written no later than y). -/
def HSlotInv (S0 : Stream V T) (db : DB V T) (m : HMem V) (o : HObj V) (y : NodeId) (p : HPtr) :
    Prop :=
  (inD db.D y = false → m.ptrRef S0 y p = (db.S.lv y).map (·.recNo)) ∧
  (inD db.D y = true → m.HoldsLive y p ∨
    (inD db.D o.node = true ∧ ∃ a b, dOf db.D o.node = some a ∧ dOf db.D y = some b ∧ a ≤ b))

/-- The pointer p of a canonical object of a node current at k for a live child
y: for y in D, it holds y's live handle with y's canonical object; otherwise the
record rule gives y's latest version (what reads at k and the writer's walk
rely on). -/
def HLiveInv (S0 : Stream V T) (db : DB V T) (m : HMem V) (y : NodeId) (p : HPtr) : Prop :=
  (inD db.D y = true → m.HoldsLive y p) ∧
  (inD db.D y = false → m.ptrRef S0 y p = (db.S.lv y).map (·.recNo))

/-- The invariant of the memory m with handles, for state db at time k, after a
startup from S0. -/
structure HEInv (sp : Spec V T) (db : DB V T) (S0 : Stream V T) (k : Nat) (m : HMem V) : Prop where
  len : db.S.length = k + 1
  pre : S0 <+: db.S
  sEq : m.s = lastSp S0
  freshO : ∀ a, m.nextObj ≤ a → m.obj? a = none
  freshH : ∀ n, m.nextHandle ≤ n → m.handle? n = none
  objNodup : (m.objs.map (·.1)).Nodup
  hNodup : (m.handles.map (·.1)).Nodup
  root : ∃ o, m.obj? m.root = some o ∧ o.canonical = true ∧ o.node = root
  /-- The table and the handles. -/
  tbl : HTableOK m
  /-- Live handles have no written position. -/
  liveW : HLiveWrittenOK m
  /-- A canonical object holds its node's whole history (CC), and its latest
  position. -/
  cc : ∀ a o, m.obj? a = some o → o.canonical = true →
    ∃ n, db.P.get? o.node = some n ∧ o.hist = n.hist ∧ o.level = n.level ∧ o.isData = n.isData
  pos : ∀ a o, m.obj? a = some o → o.canonical = true → o.pos = (db.S.lv o.node).map (·.recNo)
  /-- Every node of D has a canonical object. -/
  dCanon : ∀ y, inD db.D y = true → (m.canonicalOf y).isSome
  /-- Snapshots are exact versions (INV-SNAP). -/
  snap : ∀ a o, m.obj? a = some o → o.canonical = false → HSnapExact sp S0 db m o
  /-- Snapshots in handles are at least the newest version in the section. -/
  ruleR : HRuleROK S0 m
  /-- Written positions and references name versions. -/
  wver : ∀ n hd w, m.handle? n = some hd → hd.written = some w →
    ∃ u, db.S.versionAt w hd.node = some u
  rver : ∀ a o y p r, m.obj? a = some o → o.ptr? y = some p → p.ref = some r →
    ∃ u, db.S.versionAt r y = some u
  /-- INV-SLOT: a relevant object has a pointer for each pointee, as
  `HSlotInv` asks. -/
  slots : ∀ a o, m.obj? a = some o → HRelevant sp db k o → ∀ y ∈ pointees sp o.hist,
    ∃ p, o.ptr? y = some p ∧ HSlotInv S0 db m o y p
  /-- A canonical object of a node current at k (a virtual root too) has a
  pointer for each live child, as `HLiveInv` asks. -/
  live : ∀ a o, m.obj? a = some o → o.canonical = true → reachable sp db.P k o.node = true →
    ∀ y ∈ sp.live o.hist, ∃ p, o.ptr? y = some p ∧ HLiveInv S0 db m y p

/-! ## The parts of `HTableOK` -/

section Table

variable {m : HMem V}

theorem HTableOK.entry (ht : HTableOK m) {y : NodeId} {n : Nat} (h : m.tableOf y = some n) :
    ∃ hd a o, m.handle? n = some hd ∧ hd.dead = false ∧ hd.node = y ∧ hd.obj = some a ∧
      m.obj? a = some o ∧ o.node = y := ht.1 y n h

theorem HTableOK.nodup (ht : HTableOK m) : (m.table.map (·.1)).Nodup := ht.2.1

theorem HTableOK.liveIn (ht : HTableOK m) {n : Nat} {hd : Handle} (h : m.handle? n = some hd)
    (hl : hd.dead = false) : m.tableOf hd.node = some n := ht.2.2.1 n hd h hl

theorem HTableOK.deadNone (ht : HTableOK m) {n : Nat} {hd : Handle} (h : m.handle? n = some hd)
    (hd' : hd.dead = true) : hd.obj = none := ht.2.2.2.1 n hd h hd'

theorem HTableOK.held (ht : HTableOK m) {a : Nat} {o : HObj V} (h : m.obj? a = some o) :
    ∃ n, m.tableOf o.node = some n ∧ m.objOf n = some a := ht.2.2.2.2.1 a o h

theorem HTableOK.ptrNode (ht : HTableOK m) {a : Nat} {o : HObj V} {y : NodeId} {p : HPtr} {n : Nat}
    (ho : m.obj? a = some o) (hp : o.ptr? y = some p) (hn : p.handle = some n) :
    ∃ hd, m.handle? n = some hd ∧ hd.node = y := ht.2.2.2.2.2 a o y p n ho hp hn

/-- A handle that holds an object is live. -/
theorem HTableOK.live_of_obj (ht : HTableOK m) {n : Nat} {hd : Handle} (h : m.handle? n = some hd)
    {a : Nat} (ha : hd.obj = some a) : hd.dead = false := by
  cases hdk : hd.dead with
  | false => rfl
  | true => rw [ht.deadNone h hdk] at ha; cases ha

/-- A handle that holds an object is its node's live handle, and the object is
in memory, of that node. -/
theorem HTableOK.obj_of_handle (ht : HTableOK m) {n : Nat} {hd : Handle} (h : m.handle? n = some hd)
    {a : Nat} (ha : hd.obj = some a) :
    m.tableOf hd.node = some n ∧ ∃ o, m.obj? a = some o ∧ o.node = hd.node := by
  have hl := ht.live_of_obj h ha
  have htb := ht.liveIn h hl
  obtain ⟨hd', a', o, hh', -, hn', ha', ho, hon⟩ := ht.entry htb
  rw [h, Option.some.injEq] at hh'
  subst hh'
  rw [ha, Option.some.injEq] at ha'
  subst ha'
  exact ⟨htb, o, ho, hon⟩

end Table

/-! ## Canonical objects -/

theorem HMem.canonicalOf_eq_some (m : HMem V) (y : NodeId) (a : Nat) :
    m.canonicalOf y = some a ↔
      ∃ n o, m.tableOf y = some n ∧ m.objOf n = some a ∧ m.obj? a = some o ∧ o.canonical = true := by
  unfold HMem.canonicalOf
  constructor
  · intro h
    cases ht : m.tableOf y with
    | none => rw [ht] at h; simp at h
    | some n =>
      rw [ht] at h
      simp only [Option.bind_some] at h
      cases hob : m.objOf n with
      | none => rw [hob] at h; simp at h
      | some b =>
        rw [hob] at h
        simp only at h
        cases ho : m.obj? b with
        | none => rw [ho] at h; simp at h
        | some o =>
          rw [ho] at h
          simp only at h
          split at h
          · rename_i hc
            simp only [Option.some.injEq] at h
            subst h
            exact ⟨n, o, rfl, hob, ho, hc⟩
          · simp at h
  · rintro ⟨n, o, ht, hob, ho, hc⟩
    rw [ht]
    simp only [Option.bind_some]
    rw [hob]
    simp only
    rw [ho]
    simp [hc]

section Facts

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : HMem V}

/-- A canonical object is its node's canonical object. -/
theorem HEInv.canonicalOf_of (hm : HEInv sp db S0 k m) {a : Nat} {o : HObj V} (ho : m.obj? a = some o)
    (hc : o.canonical = true) : m.canonicalOf o.node = some a := by
  obtain ⟨n, htb, hob⟩ := hm.tbl.held ho
  exact (m.canonicalOf_eq_some o.node a).mpr ⟨n, o, htb, hob, ho, hc⟩

/-- A node's canonical object is in memory, canonical, of that node. -/
theorem HEInv.obj_of_canonicalOf (hm : HEInv sp db S0 k m) {y : NodeId} {a : Nat}
    (h : m.canonicalOf y = some a) : ∃ o, m.obj? a = some o ∧ o.canonical = true ∧ o.node = y := by
  obtain ⟨n, o, htb, hob, ho, hc⟩ := (m.canonicalOf_eq_some y a).mp h
  obtain ⟨hd, b, o', hh, -, hny, hb, ho', hon⟩ := hm.tbl.entry htb
  have : m.objOf n = some b := by simp [HMem.objOf, hh, hb]
  rw [hob, Option.some.injEq] at this
  subst this
  rw [ho, Option.some.injEq] at ho'
  subst ho'
  exact ⟨o, ho, hc, hon⟩

/-- INV-CAN in the terms of HandleTheorems.lean. -/
theorem HEInv.hcan (hm : HEInv sp db S0 k m) : HCanOK db m :=
  ⟨fun a o ho hc => ⟨hm.canonicalOf_of ho hc, hm.cc a o ho hc, hm.pos a o ho hc⟩, hm.dCanon⟩

/-- References and written positions in the terms of HandleTheorems.lean. -/
theorem HEInv.hwritten (hm : HEInv sp db S0 k m) : HWrittenOK db m := by
  refine ⟨fun n hd w hh hw => ?_, fun a o y p r ho hp hr => ?_⟩
  · obtain ⟨u, hu⟩ := hm.wver n hd w hh hw
    rw [hu]; rfl
  · obtain ⟨u, hu⟩ := hm.rver a o y p r ho hp hr
    rw [hu]; rfl

/-- The record rule names a version of y, at most y's latest, for every pointer
of an object in memory (references and written positions name versions, Rule R
gives versions). -/
theorem HEInv.ptrRef_le (hinv : Inv sp db k) (hm : HEInv sp db S0 k m) {a : Nat} {o : HObj V}
    {y : NodeId} {p : HPtr} (ho : m.obj? a = some o) (hp : o.ptr? y = some p) {r : Nat}
    (hr : m.ptrRef S0 y p = some r) :
    (∃ u, db.S.versionAt r y = some u) ∧ ∃ v, db.S.lv y = some v ∧ r ≤ v.recNo := by
  have hrr : ∀ r0, ruleRRef S0 m.s y p.ref = some r0 →
      (∃ u, db.S.versionAt r0 y = some u) ∧ ∃ v, db.S.lv y = some v ∧ r0 ≤ v.recNo :=
    fun r0 h0 => hinv.ruleR_bound hm.pre m.s (fun r' h' => hm.rver a o y p r' ho hp h') h0
  unfold HMem.ptrRef at hr
  cases hph : p.handle.bind m.handle? with
  | none => rw [hph] at hr; exact hrr r hr
  | some hd =>
    rw [hph] at hr
    simp only at hr
    -- The handle is y's.
    have hnode : hd.node = y := by
      cases hpn : p.handle with
      | none => rw [hpn] at hph; cases hph
      | some n =>
        rw [hpn] at hph
        obtain ⟨hd', hh', hn'⟩ := hm.tbl.ptrNode ho hp hpn
        simp only [Option.bind_some] at hph
        rw [hph, Option.some.injEq] at hh'
        subst hh'
        exact hn'
    have hw : ∀ w, hd.written = some w →
        (∃ u, db.S.versionAt w y = some u) ∧ ∃ v, db.S.lv y = some v ∧ w ≤ v.recNo := by
      intro w hw
      cases hpn : p.handle with
      | none => rw [hpn] at hph; cases hph
      | some n =>
        rw [hpn] at hph
        simp only [Option.bind_some] at hph
        obtain ⟨u, hu⟩ := hm.wver n hd w hph hw
        rw [hnode] at hu
        exact ⟨⟨u, hu⟩, hinv.le_lv hu⟩
    have hmax : ∀ r1, maxRef (ruleRRef S0 m.s y p.ref) hd.written = some r1 →
        (∃ u, db.S.versionAt r1 y = some u) ∧ ∃ v, db.S.lv y = some v ∧ r1 ≤ v.recNo := by
      intro r1 h1
      rcases maxRef_cases _ _ r1 h1 with h | h
      · exact hrr r1 h
      · exact hw r1 h
    cases hob : hd.obj.bind m.obj? with
    | none => rw [hob] at hr; exact hmax r hr
    | some ob =>
      rw [hob] at hr
      simp only at hr
      split at hr
      · rename_i hc
        -- A canonical object's position.
        cases hb : hd.obj with
        | none => rw [hb] at hob; cases hob
        | some b =>
          rw [hb] at hob
          simp only [Option.bind_some] at hob
          have hpos := hm.pos b ob hob hc
          rw [hr] at hpos
          cases hpn : p.handle with
          | none => rw [hpn] at hph; cases hph
          | some n =>
            rw [hpn] at hph
            simp only [Option.bind_some] at hph
            obtain ⟨-, o', ho', hon'⟩ := hm.tbl.obj_of_handle hph hb
            rw [hob, Option.some.injEq] at ho'
            subst ho'
            rw [hon', hnode] at hpos
            cases hl : db.S.lv y with
            | none => rw [hl] at hpos; cases hpos
            | some v =>
              rw [hl] at hpos
              simp only [Option.map_some, Option.some.injEq] at hpos
              subst hpos
              exact ⟨⟨v, hinv.lv_at hl⟩, v, rfl, Nat.le_refl _⟩
      · exact hmax r hr

end Facts

/-! ## Eviction keeps the invariant -/

section Evict

theorem HMem.evict_tableOf {m : HMem V} {D : Dirty} {n : Nat} {hd : Handle} {a : Nat}
    (hnd : (m.table.map (·.1)).Nodup) (hev : m.evictable D n = true) (hh : m.handle? n = some hd)
    (ha : hd.obj = some a) (y : NodeId) :
    (m.evict D n).tableOf y = if m.tableOf y = some n then none else m.tableOf y := by
  unfold HMem.evict
  simp only [hev, ↓reduceIte, hh, ha]
  unfold HMem.tableOf
  simp only [HMem.setHandle_table]
  exact lookup_filter_snd m.table hnd y n

theorem HMem.evict_root (m : HMem V) (D : Dirty) (n : Nat) : (m.evict D n).root = m.root := by
  unfold HMem.evict
  split
  · split
    · split <;> rfl
    · rfl
  · rfl

theorem HMem.evict_nextObj (m : HMem V) (D : Dirty) (n : Nat) : (m.evict D n).nextObj = m.nextObj := by
  unfold HMem.evict
  split
  · split
    · split <;> rfl
    · rfl
  · rfl

theorem HMem.evict_nextHandle (m : HMem V) (D : Dirty) (n : Nat) :
    (m.evict D n).nextHandle = m.nextHandle := by
  unfold HMem.evict
  split
  · split
    · split <;> rfl
    · rfl
  · rfl

theorem HMem.evict_handles {m : HMem V} {D : Dirty} {n : Nat} {hd : Handle} {a : Nat}
    (hev : m.evictable D n = true) (hh : m.handle? n = some hd) (ha : hd.obj = some a) :
    (m.evict D n).handles =
      (n, { hd with obj := none, written := m.evictWritten hd a, dead := true }) ::
        m.handles.filter (fun p => p.1 != n) := by
  unfold HMem.evict
  simp only [hev, ↓reduceIte, hh, ha]
  rfl

theorem HMem.evict_objs {m : HMem V} {D : Dirty} {n : Nat} {hd : Handle} {a : Nat}
    (hev : m.evictable D n = true) (hh : m.handle? n = some hd) (ha : hd.obj = some a) :
    (m.evict D n).objs = m.objs.filter (fun p => p.1 != a) := by
  unfold HMem.evict
  simp only [hev, ↓reduceIte, hh, ha]
  rfl

theorem HMem.evict_not (m : HMem V) (D : Dirty) (n : Nat) (hev : m.evictable D n = false) :
    m.evict D n = m := by
  unfold HMem.evict
  simp [hev]

/-- What an evictable handle is: live, with an object in memory that is not
pinned and has a position. -/
theorem HMem.evictable_some {m : HMem V} {D : Dirty} {n : Nat} (hev : m.evictable D n = true) :
    ∃ hd b ob, m.handle? n = some hd ∧ hd.dead = false ∧ hd.obj = some b ∧ m.obj? b = some ob ∧
      m.pinned D b = false ∧ ob.pos.isSome = true := by
  unfold HMem.evictable at hev
  cases hh : m.handle? n with
  | none => rw [hh] at hev; cases hev
  | some hd =>
    rw [hh] at hev
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hev
    obtain ⟨hdead, hrest⟩ := hev
    cases hb : hd.obj with
    | none => rw [hb] at hrest; cases hrest
    | some b =>
      rw [hb] at hrest
      simp only at hrest
      cases hob : m.obj? b with
      | none => rw [hob] at hrest; cases hrest
      | some ob =>
        rw [hob] at hrest
        simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hrest
        exact ⟨hd, b, ob, rfl, hdead, hb, hob, hrest.1, hrest.2⟩

theorem setHandle_nodup (m : HMem V) (n : Nat) (hd : Handle) (hnd : (m.handles.map (·.1)).Nodup) :
    ((m.setHandle n hd).handles.map (·.1)).Nodup := by
  unfold HMem.setHandle
  simp only [List.map_cons, List.nodup_cons]
  refine ⟨?_, (List.Sublist.map _ List.filter_sublist).nodup hnd⟩
  intro hmem
  obtain ⟨p, hp, hpy⟩ := List.mem_map.mp hmem
  have := (List.mem_filter.mp hp).2
  rw [hpy] at this
  simp at this

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : HMem V}

/-- An eviction keeps the invariant: it removes one object that is not pinned,
kills its handle, and changes no pointer's record reference. -/
theorem HEInv.evict (hinv : Inv sp db k) (hm : HEInv sp db S0 k m) (n : Nat) :
    HEInv sp db S0 k (m.evict db.D n) := by
  cases hev : m.evictable db.D n with
  | false => rw [HMem.evict_not m db.D n hev]; exact hm
  | true =>
  obtain ⟨hd, b, ob, hh, hlive, hb, hob, hpin, hpos⟩ := HMem.evictable_some hev
  have hobjn : m.objOf n = some b := by simp [HMem.objOf, hh, hb]
  have huniq : ∀ n' hd', m.handle? n' = some hd' → hd'.obj = some b → n' = n :=
    fun n' hd' h1 h2 => hm.tbl.uniq h1 h2 hobjn
  obtain ⟨htbn, ob', hob', hobnode⟩ := hm.tbl.obj_of_handle hh hb
  rw [hob, Option.some.injEq] at hob'
  subst hob'
  have htbn_iff : ∀ y, m.tableOf y = some n → y = hd.node := by
    intro y hy
    obtain ⟨hd', -, -, hh', -, hny, -⟩ := hm.tbl.entry hy
    rw [hh, Option.some.injEq] at hh'
    subst hh'
    exact hny.symm
  have eobj := HMem.evict_obj? hev hh hb
  have ehd := HMem.evict_handle? hev hh hb
  have etb := HMem.evict_tableOf hm.tbl.nodup hev hh hb
  have es := HMem.evict_s m db.D n
  -- The evicted object is not the root's, nor a canonical object of D.
  have hroot : m.root ≠ b := by
    intro he; unfold HMem.pinned at hpin; rw [he] at hpin; simp at hpin
  have hnotD : ob.canonical = true → inD db.D ob.node = false := by
    intro hc
    unfold HMem.pinned at hpin
    rw [hob] at hpin
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq, Bool.and_eq_false_iff] at hpin
    rcases hpin.2 with h | h
    · rw [hc] at h; cases h
    · exact h
  -- Other objects stay, and the other handles and table entries.
  have hobj_ne : ∀ a, a ≠ b → (m.evict db.D n).obj? a = m.obj? a := by
    intro a ha; rw [eobj a]; simp [ha]
  have hhd_ne : ∀ n', n' ≠ n → (m.evict db.D n).handle? n' = m.handle? n' := by
    intro n' hn; rw [ehd n']; simp [hn]
  -- canonicalOf: the same for every node but the evicted one's.
  have ecan : ∀ y, y ≠ hd.node → (m.evict db.D n).canonicalOf y = m.canonicalOf y := by
    intro y hy
    have htb : (m.evict db.D n).tableOf y = m.tableOf y := by
      rw [etb y]
      split
      · rename_i h; exact absurd (htbn_iff y h) hy
      · rfl
    unfold HMem.canonicalOf
    rw [htb]
    cases hty : m.tableOf y with
    | none => rfl
    | some n' =>
      have hn' : n' ≠ n := by intro he; subst he; exact hy (htbn_iff y hty)
      simp only [Option.bind_some]
      have hobjof : (m.evict db.D n).objOf n' = m.objOf n' := by
        unfold HMem.objOf; rw [hhd_ne n' hn']
      rw [hobjof]
      cases hb' : m.objOf n' with
      | none => rfl
      | some b' =>
        have hbb : b' ≠ b := by
          intro he; subst he
          unfold HMem.objOf at hb'
          cases hh' : m.handle? n' with
          | none => rw [hh'] at hb'; cases hb'
          | some hd' =>
            rw [hh'] at hb'
            exact hn' (huniq n' hd' hh' hb')
        simp only
        rw [hobj_ne b' hbb]
  -- canonicalOf of a node of D is the same.
  have ecanD : ∀ y, inD db.D y = true → (m.evict db.D n).canonicalOf y = m.canonicalOf y := by
    intro y hy
    apply ecan
    intro he
    subst he
    -- The evicted object would be y's canonical object, pinned.
    obtain ⟨a0, ha0⟩ := Option.isSome_iff_exists.mp (hm.dCanon _ hy)
    obtain ⟨n0, o0, ht0, hob0, ho0, hc0⟩ := (m.canonicalOf_eq_some _ a0).mp ha0
    rw [htbn, Option.some.injEq] at ht0
    subst ht0
    rw [hobjn, Option.some.injEq] at hob0
    subst hob0
    rw [hob, Option.some.injEq] at ho0
    subst ho0
    have h1 := hnotD hc0
    rw [hobnode] at h1
    rw [h1] at hy
    cases hy
  -- HoldsLive for a node of D is the same.
  have eholds : ∀ y p, inD db.D y = true → ((m.evict db.D n).HoldsLive y p ↔ m.HoldsLive y p) := by
    intro y p hy
    have hyn : y ≠ hd.node := by
      intro he
      have := ecanD y hy
      subst he
      -- as above: the canonical object of a node of D is pinned
      obtain ⟨a0, ha0⟩ := Option.isSome_iff_exists.mp (hm.dCanon _ hy)
      obtain ⟨n0, o0, ht0, hob0, ho0, hc0⟩ := (m.canonicalOf_eq_some _ a0).mp ha0
      rw [htbn, Option.some.injEq] at ht0
      subst ht0
      rw [hobjn, Option.some.injEq] at hob0
      subst hob0
      rw [hob, Option.some.injEq] at ho0
      subst ho0
      have h1 := hnotD hc0
      rw [hobnode] at h1
      rw [h1] at hy
      cases hy
    have htb : (m.evict db.D n).tableOf y = m.tableOf y := by
      rw [etb y]
      split
      · rename_i h; exact absurd (htbn_iff y h) hyn
      · rfl
    unfold HMem.HoldsLive
    rw [htb, ecan y hyn]
  -- The record rule, for every pointer of an object of the evicted memory.
  have eref : ∀ a o y p, m.obj? a = some o → o.ptr? y = some p →
      (m.evict db.D n).ptrRef S0 y p = m.ptrRef S0 y p := by
    intro a o y p ho hp
    exact HMem.ptrRef_evict_of hm.tbl hm.hcan hm.hwritten hm.pre
      (fun r y w h => (hinv.version_node h).2.1) (fun r y w h => hinv.le_lv h) ho hp
  -- An object of the evicted memory is an object of m, not b.
  have hback : ∀ a o, (m.evict db.D n).obj? a = some o → a ≠ b ∧ m.obj? a = some o := by
    intro a o ha
    rw [eobj a] at ha
    split at ha
    · cases ha
    · rename_i hab; exact ⟨hab, ha⟩
  refine
    { len := hm.len
      pre := hm.pre
      sEq := by rw [es]; exact hm.sEq
      freshO := ?_
      freshH := ?_
      objNodup := ?_
      hNodup := ?_
      root := ?_
      tbl := ?_
      liveW := ?_
      cc := ?_
      pos := ?_
      dCanon := ?_
      snap := ?_
      ruleR := ?_
      wver := ?_
      rver := ?_
      slots := ?_
      live := ?_ }
  · intro a ha
    rw [HMem.evict_nextObj] at ha
    rw [eobj a]
    split
    · rfl
    · exact hm.freshO a ha
  · intro n' hn'
    rw [HMem.evict_nextHandle] at hn'
    have hne : n' ≠ n := by
      intro he; subst he; rw [hm.freshH n' hn'] at hh; cases hh
    rw [hhd_ne n' hne]
    exact hm.freshH n' hn'
  · rw [HMem.evict_objs hev hh hb]
    exact (List.Sublist.map _ List.filter_sublist).nodup hm.objNodup
  · rw [HMem.evict_handles hev hh hb]
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, (List.Sublist.map _ List.filter_sublist).nodup hm.hNodup⟩
    intro hmem
    obtain ⟨q, hq, hqn⟩ := List.mem_map.mp hmem
    have := (List.mem_filter.mp hq).2
    rw [hqn] at this
    simp at this
  · obtain ⟨o, ho, hc, hn⟩ := hm.root
    refine ⟨o, ?_, hc, hn⟩
    rw [HMem.evict_root, hobj_ne _ hroot]; exact ho
  · -- The table and the handles.
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro y n' hy
      rw [etb y] at hy
      split at hy
      · cases hy
      · rename_i hyn
        have hn' : n' ≠ n := by intro he; subst he; exact hyn hy
        obtain ⟨hd', a', o', hh', hl', hny', ha', ho', hon'⟩ := hm.tbl.entry hy
        have hab : a' ≠ b := by intro he; subst he; exact hn' (huniq n' hd' hh' ha')
        exact ⟨hd', a', o', by rw [hhd_ne n' hn']; exact hh', hl', hny', ha',
          by rw [hobj_ne a' hab]; exact ho', hon'⟩
    · unfold HMem.evict
      simp only [hev, ↓reduceIte, hh, hb]
      exact (List.Sublist.map _ List.filter_sublist).nodup hm.tbl.nodup
    · intro n' hd' hh' hl'
      rw [ehd n'] at hh'
      split at hh'
      · simp only [Option.some.injEq] at hh'
        subst hh'
        cases hl'
      · rename_i hn'
        have := hm.tbl.liveIn hh' hl'
        rw [etb, this]
        simp [hn']
    · intro n' hd' hh' hdd
      rw [ehd n'] at hh'
      split at hh'
      · simp only [Option.some.injEq] at hh'
        subst hh'
        rfl
      · exact hm.tbl.deadNone hh' hdd
    · intro a o ha
      obtain ⟨hab, ha'⟩ := hback a o ha
      obtain ⟨n', ht', hob'⟩ := hm.tbl.held ha'
      have hn' : n' ≠ n := by
        intro he; subst he; rw [hobjn, Option.some.injEq] at hob'; exact hab hob'.symm
      refine ⟨n', ?_, ?_⟩
      · rw [etb, ht']; simp [hn']
      · unfold HMem.objOf; rw [hhd_ne n' hn']; exact hob'
    · intro a o y p n' ha hp hn'
      obtain ⟨-, ha'⟩ := hback a o ha
      obtain ⟨hd', hh', hny⟩ := hm.tbl.ptrNode ha' hp hn'
      rw [ehd n']
      split
      · rename_i he
        subst he
        rw [hh, Option.some.injEq] at hh'
        subst hh'
        exact ⟨_, rfl, hny⟩
      · exact ⟨hd', hh', hny⟩
  · intro n' hd' hh' hl'
    rw [ehd n'] at hh'
    split at hh'
    · simp only [Option.some.injEq] at hh'
      subst hh'
      cases hl'
    · exact hm.liveW n' hd' hh' hl'
  · intro a o ha hc
    exact hm.cc a o (hback a o ha).2 hc
  · intro a o ha hc
    exact hm.pos a o (hback a o ha).2 hc
  · intro y hy
    rw [ecanD y hy]; exact hm.dCanon y hy
  · intro a o ha hc
    obtain ⟨r, w, h1, h2, h3, h4, h5, h6, h7⟩ := hm.snap a o (hback a o ha).2 hc
    refine ⟨r, w, h1, h2, h3, h4, h5, h6, fun y p hp => ?_⟩
    intro r0 h0
    rw [es] at h0 ⊢
    exact h7 y p hp r0 h0
  · intro n' hd' b' o w hh' hb' hob' hc hw
    rw [ehd n'] at hh'
    split at hh'
    · simp only [Option.some.injEq] at hh'
      subst hh'
      cases hb'
    · rename_i hn'
      have hbb : b' ≠ b := by intro he; subst he; exact hn' (huniq n' hd' hh' hb')
      rw [hobj_ne b' hbb] at hob'
      rw [es] at hw
      exact hm.ruleR n' hd' b' o w hh' hb' hob' hc hw
  · intro n' hd' w hh' hw
    rw [ehd n'] at hh'
    split at hh'
    · simp only [Option.some.injEq] at hh'
      subst hh'
      simp only at hw ⊢
      unfold HMem.evictWritten at hw
      rw [hob] at hw
      simp only at hw
      split at hw
      · rename_i hc
        have hp := hm.pos b ob hob hc
        rw [hw] at hp
        cases hl : db.S.lv ob.node with
        | none => rw [hl] at hp; cases hp
        | some v =>
          rw [hl] at hp
          simp only [Option.map_some, Option.some.injEq] at hp
          subst hp
          rw [← hobnode]
          exact ⟨v, hinv.lv_at hl⟩
      · exact hm.wver n hd w hh hw
    · exact hm.wver n' hd' w hh' hw
  · intro a o y p r ha hp hr
    exact hm.rver a o y p r (hback a o ha).2 hp hr
  · intro a o ha hrel y hy
    obtain ⟨hab, ha'⟩ := hback a o ha
    obtain ⟨p, hp, h1, h2⟩ := hm.slots a o ha' hrel y hy
    refine ⟨p, hp, fun hD => ?_, fun hD => ?_⟩
    · rw [eref a o y p ha' hp]; exact h1 hD
    · rcases h2 hD with h | h
      · exact Or.inl ((eholds y p hD).mpr h)
      · exact Or.inr h
  · intro a o ha hc hr y hy
    obtain ⟨hab, ha'⟩ := hback a o ha
    obtain ⟨p, hp, h1, h2⟩ := hm.live a o ha' hc hr y hy
    refine ⟨p, hp, fun hD => (eholds y p hD).mpr (h1 hD), fun hD => ?_⟩
    rw [eref a o y p ha' hp]; exact h2 hD

end Evict

/-! ## Changing one object's pointers -/

section SetObj

theorem HMem.handle?_setObj_fun (m : HMem V) (a : Nat) (o : HObj V) :
    (m.setObj a o).handle? = m.handle? := rfl
theorem HMem.objOf_setObj_fun (m : HMem V) (a : Nat) (o : HObj V) :
    (m.setObj a o).objOf = m.objOf := rfl

/-- The canonical objects after an object is replaced by one with the same core. -/
theorem HMem.canonicalOf_setObj_core {m : HMem V} {a : Nat} {o o' : HObj V} (ho : m.obj? a = some o)
    (hc : o'.core = o.core) (y : NodeId) : (m.setObj a o').canonicalOf y = m.canonicalOf y := by
  have hcan : o'.canonical = o.canonical := congrArg (fun c => c.2.2.2.2.1) hc
  unfold HMem.canonicalOf
  rw [HMem.tableOf_setObj, HMem.objOf_setObj_fun]
  cases (m.tableOf y).bind m.objOf with
  | none => rfl
  | some b =>
    simp only
    rw [HMem.obj?_setObj]
    by_cases hba : b = a
    · subst hba; simp only [↓reduceIte]; rw [ho]; simp only [hcan]
    · simp only [hba, ↓reduceIte]

/-- The record rule after an object is replaced by one with the same core. -/
theorem HMem.ptrRef_setObj_core {m : HMem V} {a : Nat} {o o' : HObj V} (ho : m.obj? a = some o)
    (hc : o'.core = o.core) (S0 : Stream V T) (y : NodeId) (p : HPtr) :
    (m.setObj a o').ptrRef S0 y p = m.ptrRef S0 y p := by
  have hcan : o'.canonical = o.canonical := congrArg (fun c => c.2.2.2.2.1) hc
  have hpos : o'.pos = o.pos := congrArg (fun c => c.2.2.2.2.2) hc
  unfold HMem.ptrRef
  rw [HMem.handle?_setObj_fun, HMem.setObj_s]
  cases p.handle.bind m.handle? with
  | none => rfl
  | some hd =>
    simp only
    cases hb : hd.obj with
    | none => rfl
    | some b =>
      simp only [Option.bind_some]
      rw [HMem.obj?_setObj]
      by_cases hba : b = a
      · subst hba; simp only [↓reduceIte]; rw [ho]; simp only [hcan, hpos]
      · simp only [hba, ↓reduceIte]

theorem HMem.holdsLive_setObj_core {m : HMem V} {a : Nat} {o o' : HObj V} (ho : m.obj? a = some o)
    (hc : o'.core = o.core) (y : NodeId) (p : HPtr) :
    (m.setObj a o').HoldsLive y p ↔ m.HoldsLive y p := by
  unfold HMem.HoldsLive
  rw [HMem.tableOf_setObj, HMem.canonicalOf_setObj_core ho hc]

/-- Whether a pointer holds a canonical object, after an object is replaced by
one with the same flag. -/
theorem HMem.holdsCanonical_setObj_flag {m : HMem V} {a : Nat} {o o' : HObj V} (ho : m.obj? a = some o)
    (hc : o'.canonical = o.canonical) (p : HPtr) : (m.setObj a o').holdsCanonical p = m.holdsCanonical p := by
  unfold HMem.holdsCanonical
  rw [HMem.objOf_setObj_fun]
  cases p.handle.bind m.objOf with
  | none => rfl
  | some b =>
    simp only [Option.bind_some]
    rw [HMem.obj?_setObj]
    by_cases hba : b = a
    · subst hba; simp [ho, hc]
    · simp only [hba, ↓reduceIte]

theorem HSnapExact.of_s {sp : Spec V T} {S0 : Stream V T} {db : DB V T} {m m' : HMem V} {o : HObj V}
    (hs : m'.s = m.s) (h : HSnapExact sp S0 db m o) : HSnapExact sp S0 db m' o := by
  obtain ⟨r, w, h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨r, w, h1, h2, h3, h4, h5, h6, fun y p hp r0 h0 => ?_⟩
  rw [hs] at h0 ⊢
  exact h7 y p hp r0 h0

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : HMem V}

/-- Replacing object a by an object with the same core and other pointers keeps
the invariant, if its pointers meet what the invariant asks of them. -/
theorem HEInv.setObj_ptrs (hm : HEInv sp db S0 k m) {a : Nat} {o o' : HObj V} (ho : m.obj? a = some o)
    (hc : o'.core = o.core)
    (hnode : ∀ y q n, o'.ptr? y = some q → q.handle = some n → ∃ hd, m.handle? n = some hd ∧ hd.node = y)
    (hver : ∀ y q r, o'.ptr? y = some q → q.ref = some r → ∃ u, db.S.versionAt r y = some u)
    (hsnap : o.canonical = false → HSnapExact sp S0 db m o')
    (hslot : HRelevant sp db k o → ∀ y ∈ pointees sp o.hist,
      ∃ q, o'.ptr? y = some q ∧ HSlotInv S0 db m o y q)
    (hlive : o.canonical = true → reachable sp db.P k o.node = true → ∀ y ∈ sp.live o.hist,
      ∃ q, o'.ptr? y = some q ∧ HLiveInv S0 db m y q) :
    HEInv sp db S0 k (m.setObj a o') := by
  have e1 : o'.node = o.node := congrArg (fun c => c.1) hc
  have e2 : o'.level = o.level := congrArg (fun c => c.2.1) hc
  have e3 : o'.isData = o.isData := congrArg (fun c => c.2.2.1) hc
  have e4 : o'.hist = o.hist := congrArg (fun c => c.2.2.2.1) hc
  have e5 : o'.canonical = o.canonical := congrArg (fun c => c.2.2.2.2.1) hc
  have e6 : o'.pos = o.pos := congrArg (fun c => c.2.2.2.2.2) hc
  have hlt : a < m.nextObj := Nat.lt_of_not_le (fun h => by rw [hm.freshO a h] at ho; cases ho)
  have hobj : ∀ x, (m.setObj a o').obj? x = if x = a then some o' else m.obj? x :=
    fun x => HMem.obj?_setObj m a x o'
  have href : ∀ y p, (m.setObj a o').ptrRef S0 y p = m.ptrRef S0 y p := HMem.ptrRef_setObj_core ho hc S0
  have hcan : ∀ y, (m.setObj a o').canonicalOf y = m.canonicalOf y := HMem.canonicalOf_setObj_core ho hc
  have hhl : ∀ y p, (m.setObj a o').HoldsLive y p ↔ m.HoldsLive y p := HMem.holdsLive_setObj_core ho hc
  have hslotc : ∀ x y q, HSlotInv S0 db m x y q → HSlotInv S0 db (m.setObj a o') x y q := by
    intro x y q h
    obtain ⟨h1, h2⟩ := h
    refine ⟨fun hD => by rw [href]; exact h1 hD, fun hD => ?_⟩
    rcases h2 hD with h | h
    · exact Or.inl ((hhl y q).mpr h)
    · exact Or.inr h
  have hlivec : ∀ y q, HLiveInv S0 db m y q → HLiveInv S0 db (m.setObj a o') y q := by
    intro y q h
    obtain ⟨h1, h2⟩ := h
    exact ⟨fun hD => (hhl y q).mpr (h1 hD), fun hD => by rw [href]; exact h2 hD⟩
  have hback : ∀ x ox, (m.setObj a o').obj? x = some ox →
      (x = a ∧ ox = o') ∨ (x ≠ a ∧ m.obj? x = some ox) := by
    intro x ox hx
    rw [hobj] at hx
    split at hx
    · rename_i h; simp only [Option.some.injEq] at hx; exact Or.inl ⟨h, hx.symm⟩
    · rename_i h; exact Or.inr ⟨h, hx⟩
  refine
    { len := hm.len
      pre := hm.pre
      sEq := by rw [HMem.setObj_s]; exact hm.sEq
      freshO := ?_
      freshH := fun n hn => hm.freshH n hn
      objNodup := ?_
      hNodup := hm.hNodup
      root := ?_
      tbl := ?_
      liveW := hm.liveW
      cc := ?_
      pos := ?_
      dCanon := fun y hy => by rw [hcan]; exact hm.dCanon y hy
      snap := ?_
      ruleR := ?_
      wver := hm.wver
      rver := ?_
      slots := ?_
      live := ?_ }
  · intro x hx
    rw [HMem.setObj_nextObj] at hx
    rw [hobj]
    have : x ≠ a := by omega
    simp only [this, ↓reduceIte]
    exact hm.freshO x hx
  · unfold HMem.setObj
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, (List.Sublist.map _ List.filter_sublist).nodup hm.objNodup⟩
    intro hmem
    obtain ⟨q, hq, hqa⟩ := List.mem_map.mp hmem
    have := (List.mem_filter.mp hq).2
    rw [hqa] at this
    simp at this
  · obtain ⟨or, hor, hc', hn'⟩ := hm.root
    rw [HMem.setObj_root, hobj]
    split
    · rename_i h
      rw [h, ho, Option.some.injEq] at hor
      subst hor
      exact ⟨o', rfl, by rw [e5]; exact hc', by rw [e1]; exact hn'⟩
    · exact ⟨or, hor, hc', hn'⟩
  · refine ⟨?_, hm.tbl.nodup, fun n hd hh hl => hm.tbl.liveIn hh hl,
      fun n hd hh hdd => hm.tbl.deadNone hh hdd, ?_, ?_⟩
    · intro y n hy
      obtain ⟨hd, b, ob, hh, hl, hny, hb, hob, hon⟩ := hm.tbl.entry hy
      by_cases hba : b = a
      · subst hba
        rw [ho, Option.some.injEq] at hob
        subst hob
        exact ⟨hd, b, o', hh, hl, hny, hb, by rw [hobj]; simp, by rw [e1]; exact hon⟩
      · exact ⟨hd, b, ob, hh, hl, hny, hb, by rw [hobj]; simp [hba]; exact hob, hon⟩
    · intro x ox hx
      rcases hback x ox hx with ⟨hxa, hox⟩ | ⟨-, hx'⟩
      · subst hox
        obtain ⟨n, ht, hob⟩ := hm.tbl.held ho
        exact ⟨n, by rw [HMem.tableOf_setObj, e1]; exact ht, by rw [hxa]; exact hob⟩
      · exact hm.tbl.held hx'
    · intro x ox y q n hx hq hn
      rcases hback x ox hx with ⟨-, hox⟩ | ⟨-, hx'⟩
      · subst hox; exact hnode y q n hq hn
      · exact hm.tbl.ptrNode hx' hq hn
  · intro x ox hx hcx
    rcases hback x ox hx with ⟨-, hox⟩ | ⟨-, hx'⟩
    · subst hox
      obtain ⟨n, hn, h1, h2, h3⟩ := hm.cc a o ho (by rw [← e5]; exact hcx)
      exact ⟨n, by rw [e1]; exact hn, by rw [e4]; exact h1, by rw [e2]; exact h2, by rw [e3]; exact h3⟩
    · exact hm.cc x ox hx' hcx
  · intro x ox hx hcx
    rcases hback x ox hx with ⟨-, hox⟩ | ⟨-, hx'⟩
    · subst hox; rw [e6, e1]; exact hm.pos a o ho (by rw [← e5]; exact hcx)
    · exact hm.pos x ox hx' hcx
  · intro x ox hx hcx
    rcases hback x ox hx with ⟨-, hox⟩ | ⟨-, hx'⟩
    · subst hox; exact (hsnap (by rw [← e5]; exact hcx)).of_s (HMem.setObj_s _ _ _)
    · exact (hm.snap x ox hx' hcx).of_s (HMem.setObj_s _ _ _)
  · intro n hd b ob w hh hb hob hcb hw
    rw [HMem.setObj_s] at hw
    rw [hobj] at hob
    split at hob
    · rename_i hba
      simp only [Option.some.injEq] at hob
      subst hob
      rw [e6]
      exact hm.ruleR n hd b o w hh hb (by rw [hba]; exact ho) (by rw [← e5]; exact hcb) hw
    · exact hm.ruleR n hd b ob w hh hb hob hcb hw
  · intro x ox y q r hx hq hr
    rcases hback x ox hx with ⟨-, hox⟩ | ⟨-, hx'⟩
    · subst hox; exact hver y q r hq hr
    · exact hm.rver x ox y q r hx' hq hr
  · intro x ox hx hrelx y hy
    rcases hback x ox hx with ⟨-, hox⟩ | ⟨-, hx'⟩
    · subst hox
      have hrel0 : HRelevant sp db k o := by
        obtain ⟨h1, h2, h3⟩ := hrelx
        exact ⟨by rw [← e5]; exact h1, by rw [← e1]; exact h2, by rw [← e1]; exact h3⟩
      obtain ⟨q, hq, hi⟩ := hslot hrel0 y (by rw [← e4]; exact hy)
      refine ⟨q, hq, ?_⟩
      have := hslotc o y q hi
      unfold HSlotInv at this ⊢
      rw [e1]; exact this
    · obtain ⟨q, hq, hi⟩ := hm.slots x ox hx' hrelx y hy
      exact ⟨q, hq, hslotc ox y q hi⟩
  · intro x ox hx hcx hrx y hy
    rcases hback x ox hx with ⟨-, hox⟩ | ⟨-, hx'⟩
    · subst hox
      obtain ⟨q, hq, hi⟩ := hlive (by rw [← e5]; exact hcx) (by rw [← e1]; exact hrx) y
        (by rw [← e4]; exact hy)
      exact ⟨q, hq, hlivec y q hi⟩
    · obtain ⟨q, hq, hi⟩ := hm.live x ox hx' hcx hrx y hy
      exact ⟨q, hq, hlivec y q hi⟩

end SetObj

end SIS
