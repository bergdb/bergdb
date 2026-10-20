/-
Proofs about reclaim, part 13 (bergdb item 001, WP R4, T9): reads in the
running process after a cut. A physical read at a time t from f on, through
the Level 4 loader, reads only versions that `ReadsPhys` covers, so a safe cut
(`CutOK`'s part 2) changes nothing it reads. What it needs of the memory
(`CInv`): a canonical object of a clean node names, for each pointee, a
canonical object or a record at or after the one that the node's latest
version names; one of a node of D names, by a memory slot to a snapshot, a
pointee of D at its latest version; a virtual root's object names its root
children of D by memory slots to their canonical objects and the others at
their latest versions; and no snapshot is of a version that Rule A put back
and that is still in D.
-/
import SIS.Proof.EvictReadT
import SIS.Proof.CutStream

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## The invariant -/

/-- Slot sl for y names a canonical object, or (`slotRefOf`) a record at or
after r0. -/
def SlotAtLeast (S0 : Stream V T) (m : Mem V) (y : NodeId) (sl : Slot) (r0 : Nat) : Prop :=
  (∃ h' o', sl = Slot.mem h' ∧ m.obj? h' = some o' ∧ o'.canonical = true) ∨
    ∃ r, slotRefOf S0 m y sl = some r ∧ r0 ≤ r

/-- T9's invariant on the memory, for state db, after a startup from S0. -/
structure CInv (sp : Spec V T) (db : DB V T) (S0 : Stream V T) (m : Mem V) : Prop where
  /-- A canonical object of a written node not in D: each slot names a
  canonical object, or a record at or after the one that the node's latest
  version names for that pointee. -/
  mono : ∀ h o, m.obj? h = some o → o.canonical = true → written sp o.node = true →
    inD db.D o.node = false → ∀ v, db.S.lv o.node = some v → ∀ y sl r0, o.slot? y = some sl →
      v.ref? y = some r0 → SlotAtLeast S0 m y sl r0
  /-- A canonical object of a node of D: a memory slot to a snapshot, for a
  pointee of D in its history, names the pointee's latest version. -/
  pinSnap : ∀ h o, m.obj? h = some o → o.canonical = true → inD db.D o.node = true →
    ∀ y h' o', o.slot? y = some (Slot.mem h') → inD db.D y = true → m.obj? h' = some o' →
      o'.canonical = false → y ∈ pointees sp o.hist → o'.pos = (db.S.lv y).map (·.recNo)
  /-- With a virtual root: the root's object names a root child of D by a
  memory slot to its canonical object, -/
  rootD : sp.virt = true → ∀ o, m.obj? m.root = some o → ∀ y sl, o.slot? y = some sl →
    y ∈ pointees sp o.hist → inD db.D y = true → ∃ h', sl = Slot.mem h' ∧ m.canonicalOf y = some h'
  /-- and every other root child at its latest version. -/
  rootClean : sp.virt = true → ∀ o, m.obj? m.root = some o → ∀ y sl, o.slot? y = some sl →
    y ∈ pointees sp o.hist → inD db.D y = false → slotRefOf S0 m y sl = (db.S.lv y).map (·.recNo)
  /-- No snapshot is of a version that Rule A put back and that is still in D. -/
  snapND : ∀ h o r, m.obj? h = some o → o.canonical = false → o.pos = some r → (o.node, r) ∉ db.D

/-- Object h, of node y, can be read at t from a stream cut safely: it is
canonical, or the snapshot of a version that a physical read at t may follow. -/
def CutSafeT (sp : Spec V T) (db : DB V T) (m : Mem V) (t : Time) (h : Nat) (y : NodeId) : Prop :=
  ∃ o, m.obj? h = some o ∧ o.node = y ∧
    (o.canonical = true ∨ ∃ r w, o.pos = some r ∧ db.S.versionAt r y = some w ∧
      ReadsPhys sp db.S db.P db.D t w)

/-- A slot for y that a read at t may follow, on a stream cut safely: to an
object that can be read so; or a stream slot that the loader turns into y's
canonical object, or into a version that a physical read at t may follow. -/
def SlotCutT (sp : Spec V T) (S0 : Stream V T) (db : DB V T) (m : Mem V) (t : Time) (y : NodeId) :
    Slot → Prop
  | Slot.mem h' => CutSafeT sp db m t h' y
  | Slot.stream r => m.canonicalOf y ≠ none ∨
      ∀ r' w, ruleRRef S0 m.s y r = some r' → db.S.versionAt r' y = some w →
        ReadsPhys sp db.S db.P db.D t w

/-! ## The loader on a stream cut safely -/

section Load

variable {sp : Spec V T} {S0 S : Stream V T}

/-- The loader's first touch gives the same on a stream cut at c when the
version it would read, if any, is at the cut or later. -/
theorem reached4_cut {c : Nat} (m : Mem V) (hp : Nat) (y : NodeId)
    (h : ∀ r r', (m.obj? hp).bind (·.slot? y) = some (Slot.stream r) → m.canonicalOf y = none →
      ruleRRef S0 m.s y r = some r' → (S.versionAt r' y).isSome → c ≤ r') :
    m.reached4 sp S0 (cutStream c S) hp y = m.reached4 sp S0 S hp y := by
  unfold Mem.reached4
  cases hsl : (m.obj? hp).bind (·.slot? y) with
  | none => rfl
  | some sl =>
    cases sl with
    | mem h1 => rfl
    | stream r =>
      simp only
      cases hc : m.canonicalOf y with
      | some h0 => rfl
      | none =>
        simp only
        cases hr : ruleRRef S0 m.s y r with
        | none => rfl
        | some r' =>
          simp only
          rcases Nat.lt_or_ge r' c with hlt | hge
          · rw [versionAt_cut_lt hlt]
            cases hw : S.versionAt r' y with
            | none => rfl
            | some w =>
              have := h r r' hsl hc hr (by rw [hw]; rfl)
              omega
          · rw [versionAt_cut_ge hge]

theorem follow4_cut {c : Nat} (m : Mem V) (hp : Nat) (y : NodeId) (wr : Bool)
    (h : ∀ r r', (m.obj? hp).bind (·.slot? y) = some (Slot.stream r) → m.canonicalOf y = none →
      ruleRRef S0 m.s y r = some r' → (S.versionAt r' y).isSome → c ≤ r') :
    m.follow4 sp S0 (cutStream c S) hp y wr = m.follow4 sp S0 S hp y wr := by
  rw [follow4_eq, follow4_eq, reached4_cut m hp y h]

end Load

/-! ## The slots that a read at t follows -/

section Slots

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

/-- An object of node z whose snapshot, if it is one, is of a version that a
physical read at t may follow, can be read at t on a stream cut safely. -/
theorem EInv.cutSafe_of (hm : EInv sp db S0 k m) {h' : Nat} {o' : Obj V} (ho' : m.obj? h' = some o')
    {z : NodeId} (hn : o'.node = z) {t : Time}
    (hrp : o'.canonical = false → ∀ p w, o'.pos = some p → db.S.versionAt p z = some w →
      ReadsPhys sp db.S db.P db.D t w) :
    CutSafeT sp db m t h' z := by
  cases hc : o'.canonical with
  | true => exact ⟨o', ho', hn, Or.inl hc⟩
  | false =>
    obtain ⟨r, w, hp, hw, -⟩ := hm.snap h' o' ho' hc
    rw [hn] at hw
    exact ⟨o', ho', hn, Or.inr ⟨r, w, hp, hw, hrp hc r w hp hw⟩⟩

/-- A slot that names the latest version of a pointee reachable at t is as a
read at t on a stream cut safely needs it. -/
theorem EInv.slotCut_latest (hinv : Inv sp db k) (hm : EInv sp db S0 k m) {h : Nat} {o : Obj V}
    (ho : m.obj? h = some o) {z : NodeId} {sl : Slot} (hsl : o.slot? z = some sl)
    (href : slotRefOf S0 m z sl = (db.S.lv z).map (·.recNo)) {t : Time}
    (hrz : reachable sp db.P t z = true) : SlotCutT sp S0 db m t z sl := by
  have hlat : ∀ p w, (db.S.lv z).map (·.recNo) = some p → db.S.versionAt p z = some w →
      ReadsPhys sp db.S db.P db.D t w := by
    intro p w hp hw
    cases hl : db.S.lv z with
    | none => rw [hl] at hp; cases hp
    | some u =>
      rw [hl, Option.map_some, Option.some.injEq] at hp
      subst hp
      rw [hinv.lv_at hl, Option.some.injEq] at hw
      subst hw
      exact ReadsPhys.latest z _ hrz hl
  cases sl with
  | mem h' =>
    obtain ⟨o', ho', hn'⟩ := hm.slotsNode h o ho z h' hsl
    simp only [slotRefOf, ho', Option.bind_some] at href
    exact hm.cutSafe_of ho' hn' (fun _ p w hp hw => hlat p w (by rw [← href, hp]) hw)
  | stream r =>
    simp only [slotRefOf] at href
    exact Or.inr (fun r' w hr hw => hlat r' w (by rw [← href, hr]) hw)

/-- The slots of an object that can be read at t on a stream cut safely, for
its live children at t: as a read at t there needs them. -/
theorem CInv.slotCut (hinv : Inv sp db k) (hls : LiveSub sp) (hm : EInv sp db S0 k m)
    (hh : HInv sp db S0 k m) (hc : CInv sp db S0 m) {t : Time} (ht : t ≤ k) {h : Nat} {y : NodeId}
    (hrd : ReadableT sp db m t h y) (hcs : CutSafeT sp db m t h y) (hr : reachable sp db.P t y = true)
    {o : Obj V} (ho : m.obj? h = some o) {z : NodeId} (hz : z ∈ sp.live (o.hist.upTo t)) :
    ∃ sl, o.slot? z = some sl ∧ SlotCutT sp S0 db m t z sl := by
  obtain ⟨o1, ho1, hoy, hcase⟩ := hcs
  rw [ho, Option.some.injEq] at ho1
  subst ho1
  cases hco : o.canonical with
  | true =>
    obtain ⟨hrz, hzr, hzw⟩ := hm.reach_child hinv hls ho hco (by rw [hoy]; exact hr) hz
    obtain ⟨sl, hsl, -⟩ := hh h o ho hco t ht (by rw [hoy]; exact hr) z hz
    refine ⟨sl, hsl, ?_⟩
    have hzp : z ∈ pointees sp o.hist := mem_pointees_of_live hls hz
    by_cases hyw : written sp y = true
    · cases hyD : inD db.D y with
      | false =>
        -- A clean node: its latest version, good for t, and the slots at least as new.
        obtain ⟨v, hv, hg⟩ := hinv.clean_good hls hyD hyw ht hr
        obtain ⟨n, hn, hoh, -, -⟩ := hm.cc h o ho hco
        rw [hoy] at hn
        have hvh : v.hist.upTo t = o.hist.upTo t := by
          obtain ⟨⟨n', hn', hh'⟩, -⟩ := (good_iff sp db.S db.P t v).mp hg
          obtain ⟨hvn, -⟩ := hinv.version_node (hinv.lv_at hv)
          rw [hvn, hn, Option.some.injEq] at hn'
          subst hn'
          rw [hh', hoh]
        have hzv : z ∈ sp.live (v.hist.upTo t) := by rw [hvh]; exact hz
        have hvr : ReadsPhys sp db.S db.P db.D t v := ReadsPhys.latest y v hr hv
        have hvD : (v.node, v.recNo) ∉ db.D := by
          intro hm'
          have hvn := (hinv.version_node (hinv.lv_at hv)).1
          rw [hvn] at hm'
          have := (inD_iff _ _).mpr ⟨_, hm'⟩
          rw [hyD] at this; cases this
        have hmono := hc.mono h o ho hco (by rw [hoy]; exact hyw) (by rw [hoy]; exact hyD) v
          (by rw [hoy]; exact hv) z sl
        -- Any version of z at or after what v names may be followed.
        have hchild : ∀ p w, db.S.versionAt p z = some w → (∀ r0, v.ref? z = some r0 → r0 ≤ p) →
            ReadsPhys sp db.S db.P db.D t w :=
          fun p w hw hle => ReadsPhys.child v z w hvr hzv (Or.inr ⟨hvD, p, hw, hle⟩)
        cases sl with
        | mem h' =>
          obtain ⟨o', ho', hn'⟩ := hm.slotsNode h o ho z h' hsl
          refine hm.cutSafe_of ho' hn' (fun hc' p w hp hw => hchild p w hw (fun r0 hr0 => ?_))
          rcases hmono r0 hsl hr0 with ⟨h2, o2, he, ho2, hc2⟩ | ⟨r, hr', hle⟩
          · simp only [Slot.mem.injEq] at he
            subst he
            rw [ho', Option.some.injEq] at ho2
            subst ho2
            rw [hc'] at hc2; cases hc2
          · simp only [slotRefOf, ho', Option.bind_some, hp, Option.some.injEq] at hr'
            omega
        | stream r =>
          refine Or.inr (fun r' w hr' hw => hchild r' w hw (fun r0 hr0 => ?_))
          rcases hmono r0 hsl hr0 with ⟨h2, o2, he, -, -⟩ | ⟨r1, hr1, hle⟩
          · cases he
          · simp only [slotRefOf, hr', Option.some.injEq] at hr1
            omega
      | true =>
        -- A node of D: INV-SLOT, and for a pointee of D its canonical object or
        -- a snapshot of its latest version.
        obtain ⟨sl', hsl', hsi⟩ := hm.slots h o ho ⟨hco, by rw [hoy]; exact hyw, Or.inr (by rw [hoy]; exact hyD)⟩
          z hzp
        rw [hsl, Option.some.injEq] at hsl'
        subst hsl'
        cases hzD : inD db.D z with
        | false => exact hm.slotCut_latest hinv ho hsl (hsi.1 hzD) hrz
        | true =>
          cases sl with
          | mem h' =>
            obtain ⟨o', ho', hn'⟩ := hm.slotsNode h o ho z h' hsl
            refine hm.cutSafe_of ho' hn' (fun hc' p w hp hw => ?_)
            have hpos := hc.pinSnap h o ho hco (by rw [hoy]; exact hyD) z h' o' hsl hzD ho' hc' hzp
            rw [hp] at hpos
            cases hl : db.S.lv z with
            | none => rw [hl] at hpos; cases hpos
            | some u =>
              rw [hl, Option.map_some, Option.some.injEq] at hpos
              subst hpos
              rw [hinv.lv_at hl, Option.some.injEq] at hw
              subst hw
              exact ReadsPhys.latest z _ hrz hl
          | stream r =>
            left
            have := hm.dCanon z hzD
            intro he; rw [he] at this; cases this
    · -- A virtual root: its root children of D by their canonical objects, the
      -- others at their latest versions.
      have hv : sp.virt = true := by
        cases hv : sp.virt
        · simp [written, hv] at hyw
        · rfl
      have hyr : y = SIS.root := by
        rcases Classical.em (y = SIS.root) with hy | hne
        · exact hy
        · exact absurd (written_of_ne_root sp hne) hyw
      obtain ⟨o0, ho0, hc0, hn0⟩ := hm.root
      have hhr : h = m.root := by
        have e1 := hm.canonTbl h o ho hco
        have e2 := hm.canonTbl m.root o0 ho0 hc0
        rw [hoy, hyr] at e1
        rw [hn0] at e2
        rw [e1] at e2
        exact Option.some.inj e2
      subst hhr
      cases hzD : inD db.D z with
      | false => exact hm.slotCut_latest hinv ho hsl (hc.rootClean hv o ho z sl hsl hzp hzD) hrz
      | true =>
        obtain ⟨h', rfl, hcz⟩ := hc.rootD hv o ho z sl hsl hzp hzD
        obtain ⟨o', ho', hc', hn'⟩ := hm.obj_of_canonicalOf hcz
        exact ⟨o', ho', hn', Or.inl hc'⟩
  | false =>
    -- A snapshot of a version that a physical read at t may follow, good for t.
    rcases hcase with hcase | ⟨r, w, hp, hw, hrp⟩
    · rw [hco] at hcase; cases hcase
    obtain ⟨r0, w0, hp0, hw0, hh0, -, -, hex, hss⟩ := hm.snap h o ho hco
    rw [hp, Option.some.injEq] at hp0
    subst hp0
    rw [hoy, hw, Option.some.injEq] at hw0
    subst hw0
    have hrdw : ∃ r2 w2, o.pos = some r2 ∧ db.S.versionAt r2 y = some w2 ∧
        good sp db.S db.P t w2 = true := by
      obtain ⟨o2, ho2, hn2, hc2⟩ := hrd
      rw [ho, Option.some.injEq] at ho2
      subst ho2
      rcases hc2 with hc2 | hc2
      · rw [hco] at hc2; cases hc2
      · exact hc2
    obtain ⟨r2, w2, hp2, hw2, hg⟩ := hrdw
    rw [hp, Option.some.injEq] at hp2
    subst hp2
    rw [hw, Option.some.injEq] at hw2
    subst hw2
    rw [hh0] at hz
    obtain ⟨hwn, hwr, -⟩ := hinv.version_node hw
    -- z is reachable at t: the version is good for t.
    obtain ⟨⟨ny, hny, hwh⟩, -⟩ := (good_iff sp db.S db.P t w).mp hg
    rw [hwn] at hny
    obtain ⟨hrz, -, -⟩ := hinv.reach_child hls hny hr (by rw [← hwh]; exact hz)
    have hwD : (w.node, w.recNo) ∉ db.D := by
      rw [hwn, hwr, ← hoy]; exact hc.snapND h o r ho hco hp
    have hchild : ∀ p w', db.S.versionAt p z = some w' → (∀ r0, w.ref? z = some r0 → r0 ≤ p) →
        ReadsPhys sp db.S db.P db.D t w' :=
      fun p w' hw' hle => ReadsPhys.child w z w' hrp hz (Or.inr ⟨hwD, p, hw', hle⟩)
    -- What Rule R gives for w's reference is at least as new.
    have hRR : ∀ r0, w.ref? z = some r0 → ∃ q, ruleRRef S0 m.s z (w.ref? z) = some q ∧ r0 ≤ q := by
      intro r0 hr0
      rw [hr0]
      obtain ⟨q, hq⟩ := ruleRRef_some_some S0 m.s z r0
      exact ⟨q, hq, ruleRRef_some_ge hq⟩
    obtain ⟨sl, hsl⟩ := Option.isSome_iff_exists.mp
      (hex z (by rw [hh0]; exact mem_pointees_of_live hls (by rw [← hh0] at hz ⊢; exact hz)))
    refine ⟨sl, hsl, ?_⟩
    rcases hss z sl hsl with h1 | ⟨p, u, h1, -, h3⟩ | ⟨h', o', h1, ho', hn', hc'⟩
    · subst h1
      refine Or.inr (fun r' w' hr' hw' => hchild r' w' hw' (fun r0 hr0 => ?_))
      rw [hr0] at hr'
      exact ruleRRef_some_ge hr'
    · subst h1
      refine Or.inr (fun r' w' hr' hw' => hchild r' w' hw' (fun r0 hr0 => ?_))
      obtain ⟨q, hq, hle⟩ := hRR r0 hr0
      have := h3 q hq
      have := ruleRRef_some_ge hr'
      omega
    · subst h1
      refine hm.cutSafe_of ho' hn' (fun hc2 p w' hpp hw' => hchild p w' hw' (fun r0 hr0 => ?_))
      rcases hc' with hc' | ⟨p', hp', hle⟩
      · rw [hc2] at hc'; cases hc'
      · rw [hpp, Option.some.injEq] at hp'
        subst hp'
        obtain ⟨q, hq, hle'⟩ := hRR r0 hr0
        have := hle q hq
        omega

end Slots

/-! ## The reader's follow -/

section Reader

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

theorem CutSafeT.keepCore {t : Time} {h : Nat} {y : NodeId} {m' : Mem V}
    (hc : CutSafeT sp db m t h y) (hk : m.KeepCore m') : CutSafeT sp db m' t h y := by
  obtain ⟨o, ho, hn, hcase⟩ := hc
  obtain ⟨o', ho', hcore⟩ := hk h o ho
  have e1 : o'.node = o.node := congrArg (fun c => c.1) hcore
  have e5 : o'.canonical = o.canonical := congrArg (fun c => c.2.2.2.2.1) hcore
  have e6 : o'.pos = o.pos := congrArg (fun c => c.2.2.2.2.2) hcore
  exact ⟨o', ho', by rw [e1, hn], by rw [e5, e6]; exact hcase⟩

/-- A slot to an object of m, or a stream slot, names the same record in a
memory that keeps m's objects' cores and Rule R. -/
theorem slotRefOf_keep {m' : Mem V} (hk : m.KeepCore m') (hs : m'.s = m.s) {y : NodeId}
    {sl : Slot} (hsl : ∀ h', sl = Slot.mem h' → (m.obj? h').isSome) :
    slotRefOf S0 m' y sl = slotRefOf S0 m y sl := by
  cases sl with
  | mem h' =>
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp (hsl h' rfl)
    obtain ⟨o', ho', hcore⟩ := hk h' o ho
    have e6 : o'.pos = o.pos := congrArg (fun c => c.2.2.2.2.2) hcore
    simp only [slotRefOf, ho, ho', Option.bind_some, e6]
  | stream r => simp only [slotRefOf, hs]

theorem SlotAtLeast.keep {m' : Mem V} (hk : m.KeepCore m') (hs : m'.s = m.s) {y : NodeId}
    {sl : Slot} {r0 : Nat} (ha : SlotAtLeast S0 m y sl r0)
    (hsl : ∀ h', sl = Slot.mem h' → (m.obj? h').isSome) : SlotAtLeast S0 m' y sl r0 := by
  rcases ha with ⟨h', o', he, ho', hc'⟩ | ⟨r, hr, hle⟩
  · obtain ⟨o'', ho'', hcore⟩ := hk h' o' ho'
    have e5 : o''.canonical = o'.canonical := congrArg (fun c => c.2.2.2.2.1) hcore
    exact Or.inl ⟨h', o'', he, ho'', by rw [e5, hc']⟩
  · exact Or.inr ⟨r, by rw [slotRefOf_keep hk hs hsl]; exact hr, hle⟩

theorem Mem.swz_obj?_ne (m : Mem V) (hp : Nat) (y : NodeId) (h1 : Nat) {h' : Nat} (hne : h' ≠ hp) :
    (m.swz hp y h1).obj? h' = m.obj? h' := by
  unfold Mem.swz
  split
  · rw [Mem.obj?_setObj]; simp [hne]
  · rfl

/-- The reader's follow keeps T9's invariant: the slot then names the object it
names, the canonical object, or the snapshot of the version that Rule R gives,
which a node without a canonical object, so not in D, has. -/
theorem CInv.reached4 (hinv : Inv sp db k) (hm : EInv sp db S0 k m) (hc : CInv sp db S0 m)
    {hp : Nat} {y : NodeId} {m1 : Mem V} {h1 : Nat} (h : m.reached4 sp S0 db.S hp y = some (m1, h1)) :
    CInv sp db S0 (m1.swz hp y h1) := by
  obtain ⟨op, sl, hop, hsl, hcase⟩ := reached4_cases h
  have hk := hm.reached4_keepCore h
  obtain ⟨hset, hcan, -⟩ := hm.reached4_frame hop h
  have hs : (m1.swz hp y h1).s = m.s := by
    rw [swz_s]
    rcases hcase with ⟨-, rfl, -⟩ | ⟨r, -, -, rfl⟩ | ⟨r, r', w, -, -, -, -, rfl, -⟩
    · rfl
    · rfl
    · rfl
  -- Every memory slot of m names an object of m.
  have hold : ∀ h0 o0 z sl0, m.obj? h0 = some o0 → o0.slot? z = some sl0 →
      ∀ h', sl0 = Slot.mem h' → (m.obj? h').isSome := by
    intro h0 o0 z sl0 ho0 hsl0 h' he
    subst he
    obtain ⟨o', ho', -⟩ := hm.slotsNode h0 o0 ho0 z h' hsl0
    rw [ho']; rfl
  -- The slot for y after: it names what the reached object is.
  have hnew : ∀ r0, SlotAtLeast S0 m y sl r0 → SlotAtLeast S0 (m1.swz hp y h1) y (Slot.mem h1) r0 := by
    intro r0 ha
    rcases hcase with ⟨rfl, rfl, -⟩ | ⟨r, rfl, hcy, rfl⟩ | ⟨r, r', w, rfl, hcy, hr, hw, rfl, rfl⟩
    · exact ha.keep hk hs (hold hp op y _ hop hsl)
    · obtain ⟨o0, ho0, hc0, -⟩ := hm.obj_of_canonicalOf hcy
      obtain ⟨o0', ho0', hcore⟩ := hk h1 o0 ho0
      have e5 : o0'.canonical = o0.canonical := congrArg (fun c => c.2.2.2.2.1) hcore
      exact Or.inl ⟨h1, o0', rfl, ho0', by rw [e5, hc0]⟩
    · rcases ha with ⟨h', o', he, -, -⟩ | ⟨r1, hr1, hle⟩
      · cases he
      · simp only [slotRefOf, hr, Option.some.injEq] at hr1
        subst hr1
        have hpn : hp ≠ m.next := by
          intro he; subst he; rw [hm.fresh _ (Nat.le_refl _)] at hop; cases hop
        have hobj : ((m.addObj (Obj.ofVersion sp w none)).1.swz hp y m.next).obj? m.next =
            some (Obj.ofVersion sp w none) := by
          unfold Mem.swz
          rw [Mem.obj?_addObj]
          simp only [hpn, ↓reduceIte, hop]
          rw [Mem.obj?_setObj]
          simp only [Ne.symm hpn, ↓reduceIte, Mem.obj?_addObj]
        obtain ⟨-, -, -, -, -, f6⟩ := Obj.ofVersion_fields sp w none
        obtain ⟨-, hwr, -⟩ := hinv.version_node hw
        exact Or.inr ⟨r', by simp only [slotRefOf, hobj, Option.bind_some, f6, hwr], hle⟩
  -- What the reached object is, when y is in D: its canonical object.
  have hreachD : inD db.D y = true → (∃ h0, sl = Slot.mem h0) ∨ m.canonicalOf y = some h1 := by
    intro hyD
    rcases hcase with ⟨rfl, -, -⟩ | ⟨r, -, hcy, -⟩ | ⟨r, r', w, -, hcy, -, -, -, -⟩
    · exact Or.inl ⟨h1, rfl⟩
    · exact Or.inr hcy
    · have := hm.dCanon y hyD; rw [hcy] at this; cases this
  constructor
  · -- mono
    intro h' o' ho' hco hw hD v hv z sl' r0 hsl' hr0
    rcases reached4_back hm h hop ho' with ⟨rfl, rfl⟩ | ⟨-, h2⟩ | ⟨-, -, h3⟩
    · have hco0 : op.canonical = true := hco
      by_cases hzy : z = y
      · subst hzy
        rw [slot?_setSlot_of hsl] at hsl'
        simp only [↓reduceIte, Option.some.injEq] at hsl'
        subst hsl'
        exact hnew _ (hc.mono h' op hop hco0 hw hD v hv z sl r0 hsl hr0)
      · rw [slot?_setSlot_of hsl] at hsl'
        simp only [hzy, ↓reduceIte] at hsl'
        exact (hc.mono h' op hop hco0 hw hD v hv z sl' r0 hsl' hr0).keep hk hs (hold h' op z sl' hop hsl')
    · exact (hc.mono h' o' h2 hco hw hD v hv z sl' r0 hsl' hr0).keep hk hs (hold h' o' z sl' h2 hsl')
    · rw [hco] at h3; cases h3
  · -- pinSnap
    intro h' o' ho' hco hD z h2 o2 hsl' hzD ho2 hc2 hzp
    -- The snapshot named was in m, with its position.
    have hback : ∀ o0, m.obj? h2 = some o0 → o2.pos = o0.pos ∧ o0.canonical = false := by
      intro o0 ho0
      obtain ⟨o0', ho0', hcore⟩ := hk h2 o0 ho0
      rw [ho2, Option.some.injEq] at ho0'
      subst ho0'
      exact ⟨congrArg (fun c => c.2.2.2.2.2) hcore, by rw [← hc2]; exact (congrArg (fun c => c.2.2.2.2.1) hcore).symm⟩
    rcases reached4_back hm h hop ho' with ⟨rfl, rfl⟩ | ⟨-, h3⟩ | ⟨-, -, h3⟩
    · have hco0 : op.canonical = true := hco
      by_cases hzy : z = y
      · subst hzy
        rw [slot?_setSlot_of hsl] at hsl'
        simp only [↓reduceIte, Option.some.injEq, Slot.mem.injEq] at hsl'
        subst hsl'
        rcases hreachD hzD with ⟨h0, rfl⟩ | hcy
        · rcases hcase with ⟨he, -, -⟩ | ⟨r, he, -, -⟩ | ⟨r, r', w, he, -⟩
          · simp only [Slot.mem.injEq] at he
            subst he
            obtain ⟨o0, ho0⟩ := Option.isSome_iff_exists.mp (hold h' op z _ hop hsl _ rfl)
            obtain ⟨e1, e2⟩ := hback o0 ho0
            rw [e1]
            exact hc.pinSnap h' op hop hco0 hD z _ o0 hsl hzD ho0 e2 hzp
          · cases he
          · cases he
        · obtain ⟨o0, ho0, hc0, -⟩ := hm.obj_of_canonicalOf hcy
          obtain ⟨-, e2⟩ := hback o0 ho0
          rw [hc0] at e2; cases e2
      · rw [slot?_setSlot_of hsl] at hsl'
        simp only [hzy, ↓reduceIte] at hsl'
        obtain ⟨o0, ho0⟩ := Option.isSome_iff_exists.mp (hold h' op z _ hop hsl' h2 rfl)
        obtain ⟨e1, e2⟩ := hback o0 ho0
        rw [e1]
        exact hc.pinSnap h' op hop hco0 hD z h2 o0 hsl' hzD ho0 e2 hzp
    · obtain ⟨o0, ho0⟩ := Option.isSome_iff_exists.mp (hold h' o' z _ h3 hsl' h2 rfl)
      obtain ⟨e1, e2⟩ := hback o0 ho0
      rw [e1]
      exact hc.pinSnap h' o' h3 hco hD z h2 o0 hsl' hzD ho0 e2 hzp
    · rw [hco] at h3; cases h3
  · -- rootD
    intro hv o' ho' z sl' hsl' hzp hzD
    have hroot : (m1.swz hp y h1).root = m.root := by
      unfold Mem.swz
      rcases hcase with ⟨-, rfl, -⟩ | ⟨r, -, -, rfl⟩ | ⟨r, r', w, -, -, -, -, rfl, -⟩
      · split <;> rfl
      · split <;> rfl
      · split <;> rfl
    rw [hroot] at ho'
    obtain ⟨o0, ho0, -, -⟩ := hm.root
    rcases reached4_back hm h hop ho' with ⟨he, rfl⟩ | ⟨-, h3⟩ | ⟨hne, hnx, h3⟩
    · subst he
      by_cases hzy : z = y
      · subst hzy
        rw [slot?_setSlot_of hsl] at hsl'
        simp only [↓reduceIte, Option.some.injEq] at hsl'
        subst hsl'
        obtain ⟨h0, hsl0, hc0⟩ := hc.rootD hv op hop z sl hsl hzp hzD
        subst hsl0
        rcases hcase with ⟨he, -, -⟩ | ⟨r, he, -, -⟩ | ⟨r, r', w, he, -⟩
        · simp only [Slot.mem.injEq] at he
          subst he
          exact ⟨h0, rfl, by rw [hcan]; exact hc0⟩
        · cases he
        · cases he
      · rw [slot?_setSlot_of hsl] at hsl'
        simp only [hzy, ↓reduceIte] at hsl'
        obtain ⟨h0, hsl0, hc0⟩ := hc.rootD hv op hop z sl' hsl' hzp hzD
        exact ⟨h0, hsl0, by rw [hcan]; exact hc0⟩
    · obtain ⟨h0, hsl0, hc0⟩ := hc.rootD hv o' h3 z sl' hsl' hzp hzD
      exact ⟨h0, hsl0, by rw [hcan]; exact hc0⟩
    · exfalso
      rw [hnx, hm.fresh _ (Nat.le_refl _)] at ho0
      cases ho0
  · -- rootClean
    intro hv o' ho' z sl' hsl' hzp hzD
    have hroot : (m1.swz hp y h1).root = m.root := by
      unfold Mem.swz
      rcases hcase with ⟨-, rfl, -⟩ | ⟨r, -, -, rfl⟩ | ⟨r, r', w, -, -, -, -, rfl, -⟩
      · split <;> rfl
      · split <;> rfl
      · split <;> rfl
    rw [hroot] at ho'
    obtain ⟨o0, ho0, -, -⟩ := hm.root
    have hlat : ∀ o0 sl0, m.obj? m.root = some o0 → o0.slot? z = some sl0 → z ∈ pointees sp o0.hist →
        slotRefOf S0 (m1.swz hp y h1) z sl0 = (db.S.lv z).map (·.recNo) := by
      intro o0 sl0 ho0 hsl0 hzp0
      rw [slotRefOf_keep hk hs (hold _ o0 z sl0 ho0 hsl0)]
      exact hc.rootClean hv o0 ho0 z sl0 hsl0 hzp0 hzD
    rcases reached4_back hm h hop ho' with ⟨he, rfl⟩ | ⟨-, h3⟩ | ⟨hne, hnx, h3⟩
    · subst he
      by_cases hzy : z = y
      · subst hzy
        rw [slot?_setSlot_of hsl] at hsl'
        simp only [↓reduceIte, Option.some.injEq] at hsl'
        subst hsl'
        have hold0 := hc.rootClean hv op hop z sl hsl hzp hzD
        rcases hcase with ⟨rfl, rfl, -⟩ | ⟨r, rfl, hcy, rfl⟩ | ⟨r, r', w, rfl, hcy, hr, hw, rfl, rfl⟩
        · exact hlat op _ hop hsl hzp
        · obtain ⟨o0, ho0, hc0, hn0⟩ := hm.obj_of_canonicalOf hcy
          obtain ⟨o0', ho0', hcore⟩ := hk h1 o0 ho0
          have e6 : o0'.pos = o0.pos := congrArg (fun c => c.2.2.2.2.2) hcore
          have hpos := hm.pos z h1 o0 hcy ho0
          rw [lv_building] at hpos
          simp only [List.find?_nil, Option.none_or] at hpos
          simp only [slotRefOf, ho0', Option.bind_some, e6, hpos]
        · simp only [slotRefOf] at hold0
          rw [hr] at hold0
          have hpn : m.root ≠ m.next := by
            intro he; rw [he, hm.fresh _ (Nat.le_refl _)] at hop; cases hop
          have hobj : ((m.addObj (Obj.ofVersion sp w none)).1.swz m.root z m.next).obj? m.next =
              some (Obj.ofVersion sp w none) := by
            unfold Mem.swz
            rw [Mem.obj?_addObj]
            simp only [hpn, ↓reduceIte, hop]
            rw [Mem.obj?_setObj]
            simp only [Ne.symm hpn, ↓reduceIte, Mem.obj?_addObj]
          obtain ⟨-, -, -, -, -, f6⟩ := Obj.ofVersion_fields sp w none
          obtain ⟨-, hwr, -⟩ := hinv.version_node hw
          simp only [slotRefOf, hobj, Option.bind_some, f6, hwr]
          exact hold0
      · rw [slot?_setSlot_of hsl] at hsl'
        simp only [hzy, ↓reduceIte] at hsl'
        exact hlat op sl' hop hsl' hzp
    · exact hlat o' sl' h3 hsl' hzp
    · exfalso
      rw [hnx, hm.fresh _ (Nat.le_refl _)] at ho0
      cases ho0
  · -- snapND
    intro h' o' r ho' hco hp'
    rcases reached4_back hm h hop ho' with ⟨rfl, rfl⟩ | ⟨-, h3⟩ | ⟨hne, hnx, h3⟩
    · exact hc.snapND h' op r hop hco hp'
    · exact hc.snapND h' o' r h3 hco hp'
    · -- the new snapshot: of a node without a canonical object, so not in D
      rcases hcase with ⟨-, rfl, -⟩ | ⟨r0, -, -, rfl⟩ | ⟨r0, r', w, rfl, hcy, hr, hw, rfl, rfl⟩
      · exfalso
        rw [Mem.swz_obj?_ne _ _ _ _ hne, hnx, hm.fresh _ (Nat.le_refl _)] at ho'
        cases ho'
      · exfalso
        rw [Mem.swz_obj?_ne _ _ _ _ hne, hnx, hm.fresh _ (Nat.le_refl _)] at ho'
        cases ho'
      · have hpn : hp ≠ m.next := by
          intro he; subst he; rw [hm.fresh _ (Nat.le_refl _)] at hop; cases hop
        have hobj : ((m.addObj (Obj.ofVersion sp w none)).1.swz hp y m.next).obj? m.next =
            some (Obj.ofVersion sp w none) := by
          unfold Mem.swz
          rw [Mem.obj?_addObj]
          simp only [hpn, ↓reduceIte, hop]
          rw [Mem.obj?_setObj]
          simp only [Ne.symm hpn, ↓reduceIte, Mem.obj?_addObj]
        subst hnx
        rw [hobj, Option.some.injEq] at ho'
        subst ho'
        obtain ⟨f1, -, -, -, -, -⟩ := Obj.ofVersion_fields sp w none
        obtain ⟨hwn, -⟩ := hinv.version_node hw
        rw [f1, hwn]
        intro hmem
        have hyD : inD db.D y = true := (inD_iff _ _).mpr ⟨r, hmem⟩
        have := hm.dCanon y hyD
        rw [hcy] at this; cases this

theorem CInv.follow4_reader (hinv : Inv sp db k) (hm : EInv sp db S0 k m) (hc : CInv sp db S0 m)
    (hp : Nat) (y : NodeId) : CInv sp db S0 (m.follow4 sp S0 db.S hp y false).1 := by
  rw [follow4_eq]
  cases h : m.reached4 sp S0 db.S hp y with
  | none => exact hc
  | some p =>
    obtain ⟨m1, h1⟩ := p
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact hc.reached4 hinv hm h

/-- A read at any time, from any object, keeps T9's invariant. -/
theorem CInv.readAt4 (hinv : Inv sp db k) :
    ∀ (fuel : Nat) (m : Mem V) (t : Time) (h : Nat), EInv sp db S0 k m → CInv sp db S0 m →
      EInv sp db S0 k (m.readAt4 sp S0 db.S fuel t h).1 ∧ CInv sp db S0 (m.readAt4 sp S0 db.S fuel t h).1 := by
  intro fuel
  induction fuel with
  | zero => intro m t h hm hc; exact ⟨hm, hc⟩
  | succ fuel ih =>
    intro m t h hm hc
    unfold Mem.readAt4
    cases ho : m.obj? h with
    | none => exact ⟨hm, hc⟩
    | some o =>
      simp only
      apply foldl_inv1 _ (fun m => EInv sp db S0 k m ∧ CInv sp db S0 m) _ _ _ ⟨hm, hc⟩
      intro acc z ⟨hacc, hcacc⟩
      have hf := hacc.follow4_reader hinv h z
      have hfc := hcacc.follow4_reader hinv hacc h z
      generalize acc.1.follow4 sp S0 db.S h z false = res at hf hfc ⊢
      obtain ⟨m1, oh⟩ := res
      cases oh with
      | none => exact ⟨hf, hfc⟩
      | some h1 =>
        simp only
        cases ho1 : m1.obj? h1 with
        | none => exact ⟨hf, hfc⟩
        | some o1 =>
          simp only
          split
          · exact ih m1 t h1 hf hfc
          · exact ⟨hf, hfc⟩

theorem CInv.read4 (hinv : Inv sp db k) (hm : EInv sp db S0 k m) (hc : CInv sp db S0 m) (t : Time) :
    CInv sp db S0 (m.read4 sp S0 db.S t).1 := by
  unfold Mem.read4
  cases m.obj? m.root with
  | none => exact hc
  | some o => exact (CInv.readAt4 hinv _ m t _ hm hc).2

/-- The reader's follow of a slot that a read at t may follow on a stream cut
safely: the same on the cut stream, and it reaches an object that can be read
so. -/
theorem EInv.follow_cut (hinv : Inv sp db k) (hm : EInv sp db S0 k m) {c : Nat}
    (hcut : CutOK sp c db k) {t : Time} (hft : lastFa db.S ≤ t) (htk : t ≤ k) {hp : Nat} {op : Obj V}
    (hop : m.obj? hp = some op) {z : NodeId} {sl : Slot} (hsl : op.slot? z = some sl)
    (hg : SlotCutT sp S0 db m t z sl) :
    m.follow4 sp S0 (cutStream c db.S) hp z false = m.follow4 sp S0 db.S hp z false ∧
      ∀ m1 h1, m.reached4 sp S0 db.S hp z = some (m1, h1) → CutSafeT sp db (m1.swz hp z h1) t h1 z := by
  refine ⟨follow4_cut m hp z false (fun r r' he hcz hr hw => ?_), fun m1 h1 hrc => ?_⟩
  · rw [hop, Option.bind_some, hsl, Option.some.injEq] at he
    subst he
    rcases hg with hg | hg
    · exact absurd hcz hg
    · obtain ⟨w, hw'⟩ := Option.isSome_iff_exists.mp hw
      have hrp := hg r' w hr hw'
      have := hcut.2.1 t w hft htk hrp
      rw [(hinv.version_node hw').2.1] at this
      exact this
  · have hk := hm.reached4_keepCore hrc
    obtain ⟨op', sl', hop', hsl', hcase⟩ := reached4_cases hrc
    rw [hop, Option.some.injEq] at hop'
    subst hop'
    rw [hsl, Option.some.injEq] at hsl'
    subst hsl'
    rcases hcase with ⟨rfl, rfl, -⟩ | ⟨r, rfl, hcz, rfl⟩ | ⟨r, r', w, rfl, hcz, hr, hw, rfl, rfl⟩
    · exact CutSafeT.keepCore hg hk
    · obtain ⟨o0, ho0, hc0, hn0⟩ := hm.obj_of_canonicalOf hcz
      exact CutSafeT.keepCore ⟨o0, ho0, hn0, Or.inl hc0⟩ hk
    · rcases hg with hg | hg
      · exact absurd hcz hg
      have hrp := hg r' w hr hw
      have hpn : hp ≠ m.next := by
        intro he; subst he; rw [hm.fresh _ (Nat.le_refl _)] at hop; cases hop
      have hobj : ((m.addObj (Obj.ofVersion sp w none)).1.swz hp z m.next).obj? m.next =
          some (Obj.ofVersion sp w none) := by
        unfold Mem.swz
        rw [Mem.obj?_addObj]
        simp only [hpn, ↓reduceIte, hop]
        rw [Mem.obj?_setObj]
        simp only [Ne.symm hpn, ↓reduceIte, Mem.obj?_addObj]
      obtain ⟨f1, -, -, -, f5, f6⟩ := Obj.ofVersion_fields sp w none
      obtain ⟨hwn, hwr, -⟩ := hinv.version_node hw
      refine ⟨_, hobj, by rw [f1, hwn], Or.inr ⟨w.recNo, w, f6, by rw [hwr]; exact hw, hrp⟩⟩

end Reader

/-! ## Reads in the running process after a safe cut (T9) -/

section ReadCut

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

theorem foldl_eq_inv {α β : Type} (f g : α → β → α) (I : α → Prop) :
    ∀ (l : List β), (∀ a z, z ∈ l → I a → f a z = g a z ∧ I (g a z)) →
      ∀ a, I a → l.foldl f a = l.foldl g a ∧ I (l.foldl g a) := by
  intro l
  induction l with
  | nil => intro _ a h; exact ⟨rfl, h⟩
  | cons z l ih =>
    intro hstep a ha
    simp only [List.foldl_cons]
    obtain ⟨e, h2⟩ := hstep a z List.mem_cons_self ha
    rw [e]
    exact ih (fun a' z' hz' ha' => hstep a' z' (List.mem_cons_of_mem z hz') ha') _ h2

/-- A read at t from f on, from an object that can be read at t on a stream cut
safely, of a node reachable at t: the same on the cut stream as on the whole
stream; the invariants are kept. -/
theorem CInv.readAt4_cut (hinv : Inv sp db k) (hls : LiveSub sp) {c : Nat} (hcut : CutOK sp c db k)
    {t : Time} (hft : lastFa db.S ≤ t) (htk : t ≤ k) :
    ∀ (fuel : Nat) (m : Mem V) (h : Nat) (y : NodeId) (n : Node V), EInv sp db S0 k m → HInv sp db S0 k m →
      CInv sp db S0 m → ReadableT sp db m t h y → CutSafeT sp db m t h y → db.P.get? y = some n →
      reachable sp db.P t y = true → n.level < fuel →
      m.readAt4 sp S0 (cutStream c db.S) fuel t h = m.readAt4 sp S0 db.S fuel t h ∧
        EInv sp db S0 k (m.readAt4 sp S0 db.S fuel t h).1 ∧ HInv sp db S0 k (m.readAt4 sp S0 db.S fuel t h).1 ∧
        CInv sp db S0 (m.readAt4 sp S0 db.S fuel t h).1 ∧ m.KeepCore (m.readAt4 sp S0 db.S fuel t h).1 := by
  intro fuel
  induction fuel with
  | zero => intro m h y n _ _ _ _ _ _ _ hlt; omega
  | succ fuel ih =>
    intro m h y n hm hh hc hrd hcs hn hr hlt
    obtain ⟨o, ho, hoy, hoh, hol, hod⟩ := hm.readableT_facts hinv hrd hn
    rw [readAt4_succ_eq sp S0 (cutStream c db.S) fuel m t h ho, readAt4_succ_eq sp S0 db.S fuel m t h ho]
    have hlive : sp.live (o.hist.upTo t) = sp.live (n.hist.upTo t) := by rw [hoh]
    have hstep : ∀ (acc : Mem V × List (NodeId × Node V)) z, z ∈ sp.live (o.hist.upTo t) →
        (EInv sp db S0 k acc.1 ∧ HInv sp db S0 k acc.1 ∧ CInv sp db S0 acc.1 ∧ m.KeepCore acc.1) →
        readStep4 sp S0 (cutStream c db.S) fuel t h o acc z = readStep4 sp S0 db.S fuel t h o acc z ∧
          (EInv sp db S0 k (readStep4 sp S0 db.S fuel t h o acc z).1 ∧
            HInv sp db S0 k (readStep4 sp S0 db.S fuel t h o acc z).1 ∧
            CInv sp db S0 (readStep4 sp S0 db.S fuel t h o acc z).1 ∧
            m.KeepCore (readStep4 sp S0 db.S fuel t h o acc z).1) := by
      intro acc z hz ⟨hmA, hhA, hcA, hkA⟩
      obtain ⟨o', ho', hcore⟩ := hkA h o ho
      have e4 : o'.hist = o.hist := congrArg (fun c => c.2.2.2.1) hcore
      have hz' : z ∈ sp.live (o'.hist.upTo t) := by rw [e4]; exact hz
      obtain ⟨sl, hsl, hg⟩ := hmA.readableT_slot hinv hls hhA htk (hrd.keepCore hkA) hr ho' hz'
      obtain ⟨sl', hsl', hgc⟩ := hcA.slotCut hinv hls hmA hhA htk (hrd.keepCore hkA) (hcs.keepCore hkA) hr ho' hz'
      rw [hsl, Option.some.injEq] at hsl'
      subst hsl'
      obtain ⟨hfeq, hcsafe⟩ := hmA.follow_cut hinv hcut hft htk ho' hsl hgc
      obtain ⟨m1, h1, hev1, hm1, hh1, hkc1, hrd1⟩ := hmA.follow_goodT hinv hhA ho' hsl hg
      have hc1 : CInv sp db S0 m1 := by
        have := hcA.follow4_reader hinv hmA h z
        rw [hev1] at this; exact this
      have hcs1 : CutSafeT sp db m1 t h1 z := by
        rw [follow4_eq] at hev1
        cases hrc : acc.1.reached4 sp S0 db.S h z with
        | none => rw [hrc] at hev1; simp at hev1
        | some p =>
          obtain ⟨m2, h2⟩ := p
          rw [hrc] at hev1
          simp only [Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq, Option.some.injEq] at hev1
          obtain ⟨rfl, rfl⟩ := hev1
          exact hcsafe m2 h2 hrc
      have hz2 : z ∈ sp.live (n.hist.upTo t) := by rw [← hlive]; exact hz
      obtain ⟨hrz, -, nz, hnz, hlvl⟩ := hinv.reach_child hls hn hr hz2
      obtain ⟨o1, ho1, -, -, hol1, -⟩ := hm1.readableT_facts hinv hrd1 hnz
      obtain ⟨heq, hI2, hH2, hC2, hkc2⟩ := ih m1 h1 z nz hm1 hh1 hc1 hrd1 hcs1 hnz hrz (by omega)
      have hst : ∀ S' : Stream V T, acc.1.follow4 sp S0 S' h z false = (m1, some h1) →
          readStep4 sp S0 S' fuel t h o acc z =
            ((Mem.readAt4 sp S0 S' fuel m1 t h1).1, acc.2 ++ (Mem.readAt4 sp S0 S' fuel m1 t h1).2) := by
        intro S' hS'
        unfold readStep4
        rw [hS']
        simp only [ho1, hol1, hol, hlvl, ↓reduceIte]
      rw [hst db.S hev1, hst (cutStream c db.S) (by rw [hfeq]; exact hev1), heq]
      exact ⟨rfl, hI2, hH2, hC2, (hkA.trans hkc1).trans hkc2⟩
    obtain ⟨heq, hI⟩ := foldl_eq_inv (readStep4 sp S0 (cutStream c db.S) fuel t h o) (readStep4 sp S0 db.S fuel t h o)
      (fun acc => EInv sp db S0 k acc.1 ∧ HInv sp db S0 k acc.1 ∧ CInv sp db S0 acc.1 ∧ m.KeepCore acc.1)
      (sp.live (o.hist.upTo t)) hstep (m, [(o.node, o.nodeAt t)]) ⟨hm, hh, hc, Mem.KeepCore.refl m⟩
    exact ⟨heq, hI.1, hI.2.1, hI.2.2.1, hI.2.2.2⟩

/-- T9 for one read: after a safe cut, a read at a time from f on from the
running memory gives the same on the cut stream as on the whole stream. -/
theorem CInv.read4_cut (hinv : Inv sp db k) (hls : LiveSub sp) (hm : EInv sp db S0 k m)
    (hh : HInv sp db S0 k m) (hc : CInv sp db S0 m) {c : Nat} (hcut : CutOK sp c db k) {t : Time}
    (hft : lastFa db.S ≤ t) (htk : t ≤ k) :
    m.read4 sp S0 (cutStream c db.S) t = m.read4 sp S0 db.S t := by
  obtain ⟨o, ho, hco, hn⟩ := hm.root
  obtain ⟨n0, hn0⟩ := Option.isSome_iff_exists.mp hinv.rootIn
  have hrd : ReadableT sp db m t m.root SIS.root := ⟨o, ho, hn, Or.inl hco⟩
  have hcs : CutSafeT sp db m t m.root SIS.root := ⟨o, ho, hn, Or.inl hco⟩
  obtain ⟨o', ho', -, -, hol, -⟩ := hm.readableT_facts hinv hrd hn0
  rw [ho, Option.some.injEq] at ho'
  subst ho'
  unfold Mem.read4
  rw [ho]
  exact (CInv.readAt4_cut hinv hls hcut hft htk (o.level + 1) m m.root SIS.root n0 hm hh hc hrd hcs hn0
    (reachable_root hn0 t) (by omega)).1

end ReadCut

/-! ## Unswizzle and release -/

section Cache

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

/-- A reference of the latest version of a node is at or before the latest
version of the pointee. -/
theorem Inv.ref_le_lv (hinv : Inv sp db k) {x : NodeId} {v : Version V} (hv : db.S.lv x = some v)
    {y : NodeId} {r0 : Nat} (hr0 : v.ref? y = some r0) :
    ∃ u, db.S.lv y = some u ∧ r0 ≤ u.recNo := by
  obtain ⟨u0, hu0⟩ := hinv.ref_versionAt (hinv.lv_at hv) hr0
  obtain ⟨r', u', h1, h2, hle⟩ := lv_recNo_ge hu0
  rw [(hinv.version_node h1).2.1.symm] at hle
  exact ⟨u', h2, hle⟩

/-- Unswizzling keeps T9's invariant: the stream slot names the object's
position, which is the latest version of a node not in D, or a snapshot's. -/
theorem CInv.unswizzle (hinv : Inv sp db k) (hm : EInv sp db S0 k m) (hc : CInv sp db S0 m)
    (hp : Nat) (y : NodeId) : CInv sp db S0 (m.unswizzle db.D hp y) := by
  unfold Mem.unswizzle
  cases hop : m.obj? hp with
  | none => exact hc
  | some op =>
    simp only
    cases hsl : op.slot? y with
    | none => exact hc
    | some sl =>
      cases sl with
      | stream r => exact hc
      | mem h =>
        simp only
        cases ho : m.obj? h with
        | none => exact hc
        | some o =>
          simp only
          split
          · rename_i hdet
            obtain ⟨o0, ho0, -, hnp, p, hpos⟩ := Mem.detachable_some hdet
            rw [ho, Option.some.injEq] at ho0
            subst ho0
            obtain ⟨o1, ho1, hny⟩ := hm.slotsNode hp op hop y h hsl
            rw [ho, Option.some.injEq] at ho1
            subst ho1
            rw [hpos]
            -- The memory after: hp's object with the stream slot; the same cores.
            generalize hm' : m.setObj hp (op.setSlot y (Slot.stream (some p))) = m'
            have hobj : ∀ h'', m'.obj? h'' = if h'' = hp then some (op.setSlot y (Slot.stream (some p)))
                else m.obj? h'' := by
              intro h''; rw [← hm', Mem.obj?_setObj]
            have hk : m.KeepCore m' := by
              intro h'' o'' ho''
              rw [hobj h'']
              split
              · rename_i he; subst he; rw [hop, Option.some.injEq] at ho''; subst ho''
                exact ⟨_, rfl, setSlot_core op y _⟩
              · exact ⟨o'', ho'', rfl⟩
            have hs : m'.s = m.s := by rw [← hm']; rfl
            have hroot : m'.root = m.root := by rw [← hm']; rfl
            have hcan : ∀ z, m'.canonicalOf z = m.canonicalOf z := by
              intro z
              unfold Mem.canonicalOf
              have htb : m'.tableOf z = m.tableOf z := by rw [← hm']; rfl
              rw [htb]
              cases m.tableOf z with
              | none => rfl
              | some h0 =>
                simp only
                rw [hobj h0]
                by_cases he : h0 = hp
                · subst he
                  simp only [↓reduceIte, hop, Obj.setSlot]
                · simp only [he, ↓reduceIte]
            have hslot' : ∀ z, (op.setSlot y (Slot.stream (some p))).slot? z =
                if z = y then some (Slot.stream (some p)) else op.slot? z := by
              intro z
              rw [Obj.slot?_setSlot]
              split
              · rename_i hz; subst hz; rw [hsl]; rfl
              · rfl
            -- Every memory slot of m names an object of m.
            have hold : ∀ h0 o0 z sl0, m.obj? h0 = some o0 → o0.slot? z = some sl0 →
                ∀ h', sl0 = Slot.mem h' → (m.obj? h').isSome := by
              intro h0 o0 z sl0 ho0 hsl0 h' he
              subst he
              obtain ⟨o', ho', -⟩ := hm.slotsNode h0 o0 ho0 z h' hsl0
              rw [ho']; rfl
            -- The objects of m', from m.
            have hback : ∀ h'' o'', m'.obj? h'' = some o'' →
                (h'' = hp ∧ o'' = op.setSlot y (Slot.stream (some p))) ∨ (h'' ≠ hp ∧ m.obj? h'' = some o'') := by
              intro h'' o'' ho''
              rw [hobj h''] at ho''
              split at ho''
              · rename_i he; exact Or.inl ⟨he, (Option.some.inj ho'').symm⟩
              · rename_i he; exact Or.inr ⟨he, ho''⟩
            -- What the new slot names: at least the object's position, which is
            -- y's latest version if the object is canonical.
            have hver : ∃ q, ruleRRef S0 m.s y (some p) = some q ∧ p ≤ q := by
              obtain ⟨q, hq⟩ := ruleRRef_some_some S0 m.s y p
              exact ⟨q, hq, ruleRRef_some_ge hq⟩
            constructor
            · intro h'' o'' ho'' hco hw hD v hv z sl'' r0 hsl'' hr0
              rcases hback h'' o'' ho'' with ⟨rfl, rfl⟩ | ⟨-, h2⟩
              · have hco0 : op.canonical = true := hco
                rw [hslot' z] at hsl''
                split at hsl''
                · rename_i hzy
                  subst hzy
                  simp only [Option.some.injEq] at hsl''
                  subst hsl''
                  obtain ⟨q, hq, hpq⟩ := hver
                  refine Or.inr ⟨q, by simp only [slotRefOf, hs, hq], ?_⟩
                  rcases hc.mono h'' op hop hco0 hw hD v hv z (Slot.mem h) r0 hsl hr0 with
                    ⟨h2, o2, he, ho2, hc2⟩ | ⟨r1, hr1, hle⟩
                  · simp only [Slot.mem.injEq] at he
                    subst he
                    rw [ho, Option.some.injEq] at ho2
                    subst ho2
                    have hcz := hm.canonicalOf_of ho hc2
                    rw [hny] at hcz
                    have hpl := hm.pos.lv0 hcz ho
                    rw [hpos] at hpl
                    obtain ⟨u, hu, hle⟩ := hinv.ref_le_lv hv hr0
                    rw [hu, Option.map_some, Option.some.injEq] at hpl
                    omega
                  · simp only [slotRefOf, ho, Option.bind_some, hpos, Option.some.injEq] at hr1
                    omega
                · exact (hc.mono h'' op hop hco0 hw hD v hv z sl'' r0 hsl'' hr0).keep hk hs
                    (hold h'' op z sl'' hop hsl'')
              · exact (hc.mono h'' o'' h2 hco hw hD v hv z sl'' r0 hsl'' hr0).keep hk hs
                  (hold h'' o'' z sl'' h2 hsl'')
            · intro h'' o'' ho'' hco hD z h2 o2 hsl'' hzD ho2 hc2 hzp
              have hcore2 : ∃ o0, m.obj? h2 = some o0 ∧ o2.pos = o0.pos ∧ o0.canonical = false := by
                rw [hobj h2] at ho2
                split at ho2
                · rename_i he; subst he
                  rw [Option.some.injEq] at ho2
                  subst ho2
                  exact ⟨op, hop, rfl, hc2⟩
                · exact ⟨o2, ho2, rfl, hc2⟩
              obtain ⟨o0, ho0, e1, e2⟩ := hcore2
              rw [e1]
              rcases hback h'' o'' ho'' with ⟨rfl, rfl⟩ | ⟨-, h3⟩
              · rw [hslot' z] at hsl''
                split at hsl''
                · cases hsl''
                · exact hc.pinSnap h'' op hop hco hD z h2 o0 hsl'' hzD ho0 e2 hzp
              · exact hc.pinSnap h'' o'' h3 hco hD z h2 o0 hsl'' hzD ho0 e2 hzp
            · intro hv o'' ho'' z sl'' hsl'' hzp hzD
              rw [hroot] at ho''
              rcases hback _ o'' ho'' with ⟨he, rfl⟩ | ⟨-, h3⟩
              · rw [hslot' z] at hsl''
                split at hsl''
                · rename_i hzy
                  subst hzy
                  exfalso
                  rw [← he] at hop
                  obtain ⟨h0, hsl0, hc0⟩ := hc.rootD hv op hop z (Slot.mem h) hsl hzp hzD
                  simp only [Slot.mem.injEq] at hsl0
                  subst hsl0
                  obtain ⟨o3, ho3, hc3, hn3⟩ := hm.obj_of_canonicalOf hc0
                  rw [ho, Option.some.injEq] at ho3
                  subst ho3
                  exact hnp ⟨hc3, by rw [hn3]; exact hzD⟩
                · rw [← he] at hop
                  obtain ⟨h0, hsl0, hc0⟩ := hc.rootD hv op hop z sl'' hsl'' hzp hzD
                  exact ⟨h0, hsl0, by rw [hcan]; exact hc0⟩
              · obtain ⟨h0, hsl0, hc0⟩ := hc.rootD hv o'' h3 z sl'' hsl'' hzp hzD
                exact ⟨h0, hsl0, by rw [hcan]; exact hc0⟩
            · intro hv o'' ho'' z sl'' hsl'' hzp hzD
              rw [hroot] at ho''
              rcases hback _ o'' ho'' with ⟨he, rfl⟩ | ⟨-, h3⟩
              · rw [← he] at hop
                rw [hslot' z] at hsl''
                split at hsl''
                · rename_i hzy
                  subst hzy
                  simp only [Option.some.injEq] at hsl''
                  subst hsl''
                  have h1 := hc.rootClean hv op hop z (Slot.mem h) hsl hzp hzD
                  simp only [slotRefOf, ho, Option.bind_some, hpos] at h1
                  simp only [slotRefOf, hs]
                  rw [h1]
                  exact hinv.ruleR_lv0 hm.pre m.s z
                · rw [slotRefOf_keep hk hs (hold _ op z sl'' hop hsl'')]
                  exact hc.rootClean hv op hop z sl'' hsl'' hzp hzD
              · rw [slotRefOf_keep hk hs (hold _ o'' z sl'' h3 hsl'')]
                exact hc.rootClean hv o'' h3 z sl'' hsl'' hzp hzD
            · intro h'' o'' r'' ho'' hco hp''
              rcases hback h'' o'' ho'' with ⟨rfl, rfl⟩ | ⟨-, h3⟩
              · exact hc.snapND h'' op r'' hop hco hp''
              · exact hc.snapND h'' o'' r'' h3 hco hp''
          · exact hc

/-- Release keeps T9's invariant: an eligible object is not pinned, and no
memory slot names it. -/
theorem CInv.release (hm : EInv sp db S0 k m) (hc : CInv sp db S0 m) (h : Nat) :
    CInv sp db S0 (m.release db.D h) := by
  cases he : m.eligible db.D h with
  | false =>
    have : m.release db.D h = m := by unfold Mem.release; simp [he]
    rw [this]; exact hc
  | true =>
  have hdet : m.detachable db.D h = true := by
    unfold Mem.eligible at he; simp only [Bool.and_eq_true] at he; exact he.1
  have hinc : m.incoming h = false := by
    unfold Mem.eligible at he; simp only [Bool.and_eq_true, Bool.not_eq_true'] at he; exact he.2
  obtain ⟨o, ho, hroot, hnp, -⟩ := Mem.detachable_some hdet
  have hobj := release_obj? db.D he
  have hcan := release_canonicalOf hm.tblNodup db.D he
  have hs' : (m.release db.D h).s = m.s := by unfold Mem.release; simp only [he, ↓reduceIte]
  have hroot' : (m.release db.D h).root = m.root := by unfold Mem.release; simp only [he, ↓reduceIte]
  have hstay : ∀ h2 o2, (m.release db.D h).obj? h2 = some o2 → h2 ≠ h ∧ m.obj? h2 = some o2 := by
    intro h2 o2 ho2
    rw [hobj h2] at ho2
    split at ho2
    · cases ho2
    · rename_i hne; exact ⟨hne, ho2⟩
  have hsame : ∀ h', h' ≠ h → (m.release db.D h).obj? h' = m.obj? h' := by
    intro h' hne; rw [hobj h']; simp only [hne, ↓reduceIte]
  have hslotRef : ∀ h2 o2, m.obj? h2 = some o2 → ∀ z sl, o2.slot? z = some sl →
      slotRefOf S0 (m.release db.D h) z sl = slotRefOf S0 m z sl := by
    intro h2 o2 ho2 z sl hz
    cases sl with
    | mem h' =>
      have hne := Mem.incoming_false hinc ho2 hz
      simp only [slotRefOf]
      rw [hsame h' hne]
    | stream r => simp only [slotRefOf, hs']
  have hAtLeast : ∀ h2 o2, m.obj? h2 = some o2 → ∀ z sl r0, o2.slot? z = some sl →
      SlotAtLeast S0 m z sl r0 → SlotAtLeast S0 (m.release db.D h) z sl r0 := by
    intro h2 o2 ho2 z sl r0 hz ha
    rcases ha with ⟨h', o', he', ho', hc'⟩ | ⟨r, hr, hle⟩
    · subst he'
      have hne := Mem.incoming_false hinc ho2 hz
      exact Or.inl ⟨h', o', rfl, by rw [hsame h' hne]; exact ho', hc'⟩
    · exact Or.inr ⟨r, by rw [hslotRef h2 o2 ho2 z sl hz]; exact hr, hle⟩
  constructor
  · intro h2 o2 ho2 hco hw hD v hv z sl r0 hsl hr0
    obtain ⟨-, ho2'⟩ := hstay h2 o2 ho2
    exact hAtLeast h2 o2 ho2' z sl r0 hsl (hc.mono h2 o2 ho2' hco hw hD v hv z sl r0 hsl hr0)
  · intro h2 o2 ho2 hco hD z h' o' hsl hzD ho' hc' hzp
    obtain ⟨-, ho2'⟩ := hstay h2 o2 ho2
    have hne := Mem.incoming_false hinc ho2' hsl
    rw [hsame h' hne] at ho'
    exact hc.pinSnap h2 o2 ho2' hco hD z h' o' hsl hzD ho' hc' hzp
  · intro hv o2 ho2 z sl hsl hzp hzD
    rw [hroot'] at ho2
    obtain ⟨-, ho2'⟩ := hstay _ o2 ho2
    obtain ⟨h0, hsl0, hc0⟩ := hc.rootD hv o2 ho2' z sl hsl hzp hzD
    subst hsl0
    have hne := Mem.incoming_false hinc ho2' hsl
    refine ⟨h0, rfl, ?_⟩
    rw [hcan z, hc0]
    simp [hne]
  · intro hv o2 ho2 z sl hsl hzp hzD
    rw [hroot'] at ho2
    obtain ⟨-, ho2'⟩ := hstay _ o2 ho2
    rw [hslotRef _ o2 ho2' z sl hsl]
    exact hc.rootClean hv o2 ho2' z sl hsl hzp hzD
  · intro h2 o2 r ho2 hco hp
    obtain ⟨-, ho2'⟩ := hstay h2 o2 ho2
    exact hc.snapND h2 o2 r ho2' hco hp

/-- Every cache operation keeps T9's invariant. -/
theorem CInv.cacheOp (hinv : Inv sp db k) (hm : EInv sp db S0 k m) (hc : CInv sp db S0 m) (op : CacheOp) :
    CInv sp db S0 (m.cacheOp sp S0 db.S db.D op) := by
  cases op with
  | read t => exact hc.read4 hinv hm t
  | unswizzle h y => exact hc.unswizzle hinv hm h y
  | release h => exact hc.release hm h

theorem CInv.cacheOps (hinv : Inv sp db k) (ops : List CacheOp) :
    ∀ m, EInv sp db S0 k m → CInv sp db S0 m → CInv sp db S0 (ops.foldl (Mem.cacheOp sp S0 db.S db.D) m) := by
  induction ops with
  | nil => intro m _ hc; exact hc
  | cons op ops ih => intro m hm hc; exact ih _ (hm.cacheOp hinv op) (hc.cacheOp hinv hm op)

end Cache

/-! ## The writer's walk -/

section Walk

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

/-- m' keeps every object of m with its node and position, still canonical if
it was. -/
def Mem.KeepPos (m m' : Mem V) : Prop :=
  ∀ h o, m.obj? h = some o → ∃ o', m'.obj? h = some o' ∧ o'.node = o.node ∧ o'.pos = o.pos ∧
    (o.canonical = true → o'.canonical = true)

theorem slotRefOf_keepPos {m' : Mem V} (hk : m.KeepPos m') (hs : m'.s = m.s) {y : NodeId}
    {sl : Slot} (hsl : ∀ h', sl = Slot.mem h' → (m.obj? h').isSome) :
    slotRefOf S0 m' y sl = slotRefOf S0 m y sl := by
  cases sl with
  | mem h' =>
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp (hsl h' rfl)
    obtain ⟨o', ho', -, e6, -⟩ := hk h' o ho
    simp only [slotRefOf, ho, ho', Option.bind_some, e6]
  | stream r => simp only [slotRefOf, hs]

theorem SlotAtLeast.keepPos {m' : Mem V} (hk : m.KeepPos m') (hs : m'.s = m.s) {y : NodeId}
    {sl : Slot} {r0 : Nat} (ha : SlotAtLeast S0 m y sl r0)
    (hsl : ∀ h', sl = Slot.mem h' → (m.obj? h').isSome) : SlotAtLeast S0 m' y sl r0 := by
  rcases ha with ⟨h', o', he, ho', hc'⟩ | ⟨r, hr, hle⟩
  · obtain ⟨o'', ho'', -, -, hc''⟩ := hk h' o' ho'
    exact Or.inl ⟨h', o'', he, ho'', hc'' hc'⟩
  · exact Or.inr ⟨r, by rw [slotRefOf_keepPos hk hs hsl]; exact hr, hle⟩

/-- A snapshot's slot names what the snapshot's version names, or newer. -/
theorem SnapSlot.atLeast {w : Version V} {z : NodeId} {sl : Slot} (hss : SnapSlot S0 db m w z sl)
    {r0 : Nat} (hr0 : w.ref? z = some r0) : SlotAtLeast S0 m z sl r0 := by
  obtain ⟨q, hq⟩ := ruleRRef_some_some S0 m.s z r0
  have hqle := ruleRRef_some_ge hq
  rcases hss with rfl | ⟨p, u, rfl, -, hle⟩ | ⟨h', o', rfl, ho', -, hc'⟩
  · exact Or.inr ⟨q, by simp only [slotRefOf, hr0, hq], hqle⟩
  · rw [hr0] at hle
    have hqp := hle q hq
    obtain ⟨q', hq'⟩ := ruleRRef_some_some S0 m.s z p
    have := ruleRRef_some_ge hq'
    exact Or.inr ⟨q', by simp only [slotRefOf, hq'], by omega⟩
  · rcases hc' with hc' | ⟨p, hp, hle⟩
    · exact Or.inl ⟨h', o', rfl, ho', hc'⟩
    · rw [hr0] at hle
      have := hle q hq
      exact Or.inr ⟨p, by simp only [slotRefOf, ho', Option.bind_some, hp], by omega⟩

/-- Promotion after the writer's follow keeps T9's invariant: the slot names a
canonical object, and a snapshot promoted is of the latest version of a clean
node, with slots at least as new as that version's references. -/
theorem CInv.promote_step (hinv : Inv sp db k) (hm : EInv sp db S0 k m)
    (hc : CInv sp db S0 m) {hp : Nat} {op : Obj V} (hop : m.obj? hp = some op)
    (hco : op.canonical = true) (hr : reachable sp db.P k op.node = true) {y : NodeId}
    (hy : y ∈ sp.live op.hist) (hyw : written sp y = true) (hyne : y ≠ op.node) {h1 : Nat}
    (hsl : op.slot? y = some (Slot.mem h1)) :
    CInv sp db S0 (m.promote hp y h1).1 := by
  obtain ⟨o1, ho1, hn1⟩ := hm.slotsNode hp op hop y h1 hsl
  have hp1 : hp ≠ h1 := by
    intro he; subst he; rw [hop, Option.some.injEq] at ho1; subst ho1; exact hyne hn1.symm
  have hold : ∀ h0 o0 z sl0, m.obj? h0 = some o0 → o0.slot? z = some sl0 →
      ∀ h', sl0 = Slot.mem h' → (m.obj? h').isSome := by
    intro h0 o0 z sl0 ho0 hsl0 h' he
    subst he
    obtain ⟨o', ho', -⟩ := hm.slotsNode h0 o0 ho0 z h' hsl0
    rw [ho']; rfl
  have hss : ∀ z, z ≠ y → (op.setSlot y (Slot.mem h1)).slot? z = op.slot? z := by
    intro z hz; rw [slot?_setSlot_of hsl]; simp [hz]
  cases hcy : m.canonicalOf y with
  | some h0 =>
    obtain ⟨o0, ho0, hc0, hn0⟩ := hm.obj_of_canonicalOf hcy
    have hp0 : hp ≠ h0 := by
      intro he; subst he; rw [hop, Option.some.injEq] at ho0; subst ho0; exact hyne hn0.symm
    have hpe : m.promote hp y h1 = (match ((m.setObj h0 { o0 with canonical := true }).setTable y h0).obj? hp with
        | some op3 => ((m.setObj h0 { o0 with canonical := true }).setTable y h0).setObj hp
            (op3.setSlot y (Slot.mem h0))
        | none => (m.setObj h0 { o0 with canonical := true }).setTable y h0, h0) := by
      unfold Mem.promote; simp only [hcy, Option.getD_some, ho0]; rfl
    rw [hpe, obj_with_canonical_true hc0]
    have hop3 : ((m.setObj h0 o0).setTable y h0).obj? hp = some op := by
      rw [Mem.obj?_setTable, Mem.obj?_setObj]; simp only [hp0, ↓reduceIte]; exact hop
    simp only [hop3]
    generalize hm' : ((m.setObj h0 o0).setTable y h0).setObj hp (op.setSlot y (Slot.mem h0)) = m'
    have hobj : ∀ h, m'.obj? h = if h = hp then some (op.setSlot y (Slot.mem h0)) else m.obj? h := by
      intro h
      rw [← hm', Mem.obj?_setObj, Mem.obj?_setTable, Mem.obj?_setObj]
      split
      · rfl
      · split
        · rename_i _ he; subst he; exact ho0.symm
        · rfl
    have hk : m.KeepPos m' := by
      intro h o ho
      rw [hobj]
      split
      · rename_i he; subst he; rw [hop, Option.some.injEq] at ho; subst ho
        exact ⟨_, rfl, rfl, rfl, id⟩
      · exact ⟨o, ho, rfl, rfl, id⟩
    have hs : m'.s = m.s := by rw [← hm']; rfl
    have hroot : m'.root = m.root := by rw [← hm']; rfl
    have hcan : ∀ z, m'.canonicalOf z = m.canonicalOf z := by
      intro z
      have ht : m'.tableOf z = m.tableOf z := by
        rw [← hm']
        show ((m.setObj h0 o0).setTable y h0).tableOf z = m.tableOf z
        rw [Mem.tableOf_setTable, Mem.tableOf_setObj]
        split
        · rename_i he; subst he
          obtain ⟨ht0, -⟩ := (m.canonicalOf_eq_some _ h0).mp hcy
          exact ht0.symm
        · rfl
      unfold Mem.canonicalOf
      rw [ht]
      cases m.tableOf z with
      | none => rfl
      | some h2 =>
        simp only
        rw [hobj h2]
        by_cases he : h2 = hp
        · subst he; simp only [↓reduceIte, hop, Obj.setSlot]
        · simp only [he, ↓reduceIte]
    have hback : ∀ h o', m'.obj? h = some o' →
        (h = hp ∧ o' = op.setSlot y (Slot.mem h0)) ∨ (h ≠ hp ∧ m.obj? h = some o') := by
      intro h o' ho'
      rw [hobj h] at ho'
      split at ho'
      · rename_i he; exact Or.inl ⟨he, (Option.some.inj ho').symm⟩
      · rename_i he; exact Or.inr ⟨he, ho'⟩
    have hnewSlot : ∀ z sl', (op.setSlot y (Slot.mem h0)).slot? z = some sl' →
        (z = y ∧ sl' = Slot.mem h0) ∨ (z ≠ y ∧ op.slot? z = some sl') := by
      intro z sl' hz
      rw [slot?_setSlot_of hsl] at hz
      split at hz
      · rename_i hzy; exact Or.inl ⟨hzy, (Option.some.inj hz).symm⟩
      · rename_i hzy; exact Or.inr ⟨hzy, hz⟩
    have ho0' : m'.obj? h0 = some o0 := by rw [hobj]; simp only [Ne.symm hp0, ↓reduceIte]; exact ho0
    constructor
    · intro h o' ho' hco' hw hD v hv z sl' r0 hsl' hr0
      rcases hback h o' ho' with ⟨rfl, rfl⟩ | ⟨-, h2⟩
      · rcases hnewSlot z sl' hsl' with ⟨rfl, rfl⟩ | ⟨hzy, h3⟩
        · exact Or.inl ⟨h0, o0, rfl, ho0', hc0⟩
        · exact (hc.mono h op hop hco hw hD v hv z sl' r0 h3 hr0).keepPos hk hs (hold h op z sl' hop h3)
      · exact (hc.mono h o' h2 hco' hw hD v hv z sl' r0 hsl' hr0).keepPos hk hs (hold h o' z sl' h2 hsl')
    · intro h o' ho' hco' hD z h2 o2 hsl' hzD ho2 hc2 hzp
      have hpos2 : ∃ o0', m.obj? h2 = some o0' ∧ o2.pos = o0'.pos ∧ o0'.canonical = false := by
        rw [hobj] at ho2
        split at ho2
        · rename_i he; subst he; rw [Option.some.injEq] at ho2; subst ho2
          exact ⟨op, hop, rfl, hc2⟩
        · exact ⟨o2, ho2, rfl, hc2⟩
      obtain ⟨o3, ho3, e1, e2⟩ := hpos2
      rw [e1]
      rcases hback h o' ho' with ⟨rfl, rfl⟩ | ⟨-, h4⟩
      · rcases hnewSlot z _ hsl' with ⟨rfl, he⟩ | ⟨-, h5⟩
        · simp only [Slot.mem.injEq] at he
          subst he
          rw [ho0, Option.some.injEq] at ho3
          subst ho3
          rw [hc0] at e2; cases e2
        · exact hc.pinSnap h op hop hco hD z h2 o3 h5 hzD ho3 e2 hzp
      · exact hc.pinSnap h o' h4 hco' hD z h2 o3 hsl' hzD ho3 e2 hzp
    · intro hv o' ho' z sl' hsl' hzp hzD
      rw [hroot] at ho'
      rcases hback _ o' ho' with ⟨he, rfl⟩ | ⟨-, h4⟩
      · rw [← he] at hop
        rcases hnewSlot z sl' hsl' with ⟨rfl, rfl⟩ | ⟨-, h5⟩
        · exact ⟨h0, rfl, by rw [hcan]; exact hcy⟩
        · obtain ⟨h6, hsl6, hc6⟩ := hc.rootD hv op hop z sl' h5 hzp hzD
          exact ⟨h6, hsl6, by rw [hcan]; exact hc6⟩
      · obtain ⟨h6, hsl6, hc6⟩ := hc.rootD hv o' h4 z sl' hsl' hzp hzD
        exact ⟨h6, hsl6, by rw [hcan]; exact hc6⟩
    · intro hv o' ho' z sl' hsl' hzp hzD
      rw [hroot] at ho'
      rcases hback _ o' ho' with ⟨he, rfl⟩ | ⟨-, h4⟩
      · rw [← he] at hop
        rcases hnewSlot z sl' hsl' with ⟨rfl, rfl⟩ | ⟨-, h5⟩
        · have hpl := hm.pos.lv0 hcy ho0
          simp only [slotRefOf, ho0', Option.bind_some, hpl]
        · rw [slotRefOf_keepPos hk hs (hold _ op z sl' hop h5)]
          exact hc.rootClean hv op hop z sl' h5 hzp hzD
      · rw [slotRefOf_keepPos hk hs (hold _ o' z sl' h4 hsl')]
        exact hc.rootClean hv o' h4 z sl' hsl' hzp hzD
    · intro h o' r ho' hco' hp'
      rcases hback h o' ho' with ⟨rfl, rfl⟩ | ⟨-, h4⟩
      · exact hc.snapND h op r hop hco' hp'
      · exact hc.snapND h o' r h4 hco' hp'
  | none =>
    have hnc : o1.canonical = false := by
      cases hc1 : o1.canonical with
      | false => rfl
      | true =>
        have := hm.canonicalOf_of ho1 hc1
        rw [hn1, hcy] at this; cases this
    have hyD : inD db.D y = false := by
      cases hyd : inD db.D y with
      | false => rfl
      | true => have := hm.dCanon y hyd; rw [hcy] at this; cases this
    -- The snapshot reached: of y's latest version.
    obtain ⟨sl', hsl', hli⟩ := hm.live hp op hop hco hr y hy
    rw [hsl, Option.some.injEq] at hsl'
    subst hsl'
    have hpos1 : o1.pos = (db.S.lv y).map (·.recNo) := by
      have := hli.2 hyD
      simp only [slotRefOf, ho1, Option.bind_some] at this
      exact this
    obtain ⟨r1, w1, e1, e2, -, -, -, -, hsnap⟩ := hm.snap h1 o1 ho1 hnc
    have hw1 : db.S.lv y = some w1 := by
      cases hl : db.S.lv y with
      | none => rw [hl] at hpos1; rw [hpos1] at e1; cases e1
      | some v =>
        rw [hl] at hpos1
        rw [hpos1, Option.map_some, Option.some.injEq] at e1
        rw [← e1, hn1, hinv.lv_at hl, Option.some.injEq] at e2
        rw [e2]
    have hpe : m.promote hp y h1 = (match ((m.setObj h1 { o1 with canonical := true }).setTable y h1).obj? hp with
        | some op3 => ((m.setObj h1 { o1 with canonical := true }).setTable y h1).setObj hp
            (op3.setSlot y (Slot.mem h1))
        | none => (m.setObj h1 { o1 with canonical := true }).setTable y h1, h1) := by
      unfold Mem.promote; simp only [hcy, Option.getD_none, ho1]; rfl
    rw [hpe]
    have hop3 : ((m.setObj h1 { o1 with canonical := true }).setTable y h1).obj? hp = some op := by
      rw [Mem.obj?_setTable, Mem.obj?_setObj]; simp only [hp1, ↓reduceIte]; exact hop
    simp only [hop3]
    generalize hm' : ((m.setObj h1 { o1 with canonical := true }).setTable y h1).setObj hp
      (op.setSlot y (Slot.mem h1)) = m'
    have hobj : ∀ h, m'.obj? h = if h = hp then some (op.setSlot y (Slot.mem h1)) else
        if h = h1 then some { o1 with canonical := true } else m.obj? h := by
      intro h
      rw [← hm', Mem.obj?_setObj, Mem.obj?_setTable, Mem.obj?_setObj]
    have hk : m.KeepPos m' := by
      intro h o ho
      rw [hobj]
      split
      · rename_i he; subst he; rw [hop, Option.some.injEq] at ho; subst ho
        exact ⟨_, rfl, rfl, rfl, id⟩
      · split
        · rename_i _ he; subst he; rw [ho1, Option.some.injEq] at ho; subst ho
          exact ⟨_, rfl, rfl, rfl, fun _ => rfl⟩
        · exact ⟨o, ho, rfl, rfl, id⟩
    have hs : m'.s = m.s := by rw [← hm']; rfl
    have hroot : m'.root = m.root := by rw [← hm']; rfl
    have hcan : ∀ z, z ≠ y → m'.canonicalOf z = m.canonicalOf z := by
      intro z hzy
      have ht : m'.tableOf z = m.tableOf z := by
        rw [← hm']
        show ((m.setObj h1 { o1 with canonical := true }).setTable y h1).tableOf z = m.tableOf z
        rw [Mem.tableOf_setTable, Mem.tableOf_setObj]
        simp only [hzy, ↓reduceIte]
      unfold Mem.canonicalOf
      rw [ht]
      cases htz : m.tableOf z with
      | none => rfl
      | some h2 =>
        simp only
        rw [hobj h2]
        by_cases he : h2 = hp
        · subst he; simp only [↓reduceIte, hop, Obj.setSlot]
        · simp only [he, ↓reduceIte]
          by_cases he1 : h2 = h1
          · subst he1
            exfalso
            obtain ⟨o', ho', hn'⟩ := hm.tbl z h2 htz
            rw [ho1, Option.some.injEq] at ho'
            subst ho'
            exact hzy (hn'.symm.trans hn1)
          · simp only [he1, ↓reduceIte]
    have hback : ∀ h o', m'.obj? h = some o' →
        (h = hp ∧ o' = op.setSlot y (Slot.mem h1)) ∨ (h ≠ hp ∧ h = h1 ∧ o' = { o1 with canonical := true }) ∨
          (h ≠ hp ∧ h ≠ h1 ∧ m.obj? h = some o') := by
      intro h o' ho'
      rw [hobj h] at ho'
      split at ho'
      · rename_i he; exact Or.inl ⟨he, (Option.some.inj ho').symm⟩
      · split at ho'
        · rename_i he he1; exact Or.inr (Or.inl ⟨he, he1, (Option.some.inj ho').symm⟩)
        · rename_i he he1; exact Or.inr (Or.inr ⟨he, he1, ho'⟩)
    have hnewSlot : ∀ z sl', (op.setSlot y (Slot.mem h1)).slot? z = some sl' →
        (z = y ∧ sl' = Slot.mem h1) ∨ (z ≠ y ∧ op.slot? z = some sl') := by
      intro z sl' hz
      rw [slot?_setSlot_of hsl] at hz
      split at hz
      · rename_i hzy; exact Or.inl ⟨hzy, (Option.some.inj hz).symm⟩
      · rename_i hzy; exact Or.inr ⟨hzy, hz⟩
    have ho1' : m'.obj? h1 = some { o1 with canonical := true } := by
      rw [hobj]; simp only [Ne.symm hp1, ↓reduceIte]
    constructor
    · intro h o' ho' hco' hw hD v hv z sl'' r0 hsl'' hr0
      rcases hback h o' ho' with ⟨rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨-, -, h2⟩
      · rcases hnewSlot z sl'' hsl'' with ⟨rfl, rfl⟩ | ⟨hzy, h3⟩
        · exact Or.inl ⟨h1, _, rfl, ho1', rfl⟩
        · exact (hc.mono h op hop hco hw hD v hv z sl'' r0 h3 hr0).keepPos hk hs (hold h op z sl'' hop h3)
      · -- the snapshot promoted, of y's latest version
        simp only at hv hsl'' ⊢
        rw [hn1, hw1, Option.some.injEq] at hv
        subst hv
        exact (SnapSlot.atLeast (hsnap z sl'' hsl'') hr0).keepPos hk hs (hold _ o1 z sl'' ho1 hsl'')
      · exact (hc.mono h o' h2 hco' hw hD v hv z sl'' r0 hsl'' hr0).keepPos hk hs (hold h o' z sl'' h2 hsl'')
    · intro h o' ho' hco' hD z h2 o2 hsl'' hzD ho2 hc2 hzp
      have hpos2 : ∃ o0', m.obj? h2 = some o0' ∧ o2.pos = o0'.pos ∧ o0'.canonical = false := by
        rw [hobj] at ho2
        split at ho2
        · rename_i he; subst he; rw [Option.some.injEq] at ho2; subst ho2
          exact ⟨op, hop, rfl, hc2⟩
        · split at ho2
          · rw [Option.some.injEq] at ho2; subst ho2; cases hc2
          · exact ⟨o2, ho2, rfl, hc2⟩
      obtain ⟨o3, ho3, e3, e4⟩ := hpos2
      rw [e3]
      rcases hback h o' ho' with ⟨rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨-, -, h4⟩
      · rcases hnewSlot z _ hsl'' with ⟨rfl, he⟩ | ⟨-, h5⟩
        · rw [hyD] at hzD; cases hzD
        · exact hc.pinSnap h op hop hco hD z h2 o3 h5 hzD ho3 e4 hzp
      · simp only at hD
        rw [hn1, hyD] at hD; cases hD
      · exact hc.pinSnap h o' h4 hco' hD z h2 o3 hsl'' hzD ho3 e4 hzp
    · intro hv o' ho' z sl'' hsl'' hzp hzD
      rw [hroot] at ho'
      have hzy : z ≠ y := by intro he; rw [he, hyD] at hzD; cases hzD
      rcases hback _ o' ho' with ⟨he, rfl⟩ | ⟨-, he, rfl⟩ | ⟨-, -, h4⟩
      · rw [← he] at hop
        rcases hnewSlot z sl'' hsl'' with ⟨rfl, -⟩ | ⟨-, h5⟩
        · exact absurd rfl hzy
        · obtain ⟨h6, hsl6, hc6⟩ := hc.rootD hv op hop z sl'' h5 hzp hzD
          exact ⟨h6, hsl6, by rw [hcan z hzy]; exact hc6⟩
      · exfalso
        obtain ⟨o0, ho0, hc0, hn0⟩ := hm.root
        rw [he, ho1, Option.some.injEq] at ho0
        subst ho0
        rw [hnc] at hc0; cases hc0
      · obtain ⟨h6, hsl6, hc6⟩ := hc.rootD hv o' h4 z sl'' hsl'' hzp hzD
        exact ⟨h6, hsl6, by rw [hcan z hzy]; exact hc6⟩
    · intro hv o' ho' z sl'' hsl'' hzp hzD
      rw [hroot] at ho'
      rcases hback _ o' ho' with ⟨he, rfl⟩ | ⟨-, he, rfl⟩ | ⟨-, -, h4⟩
      · rw [← he] at hop
        rcases hnewSlot z sl'' hsl'' with ⟨rfl, rfl⟩ | ⟨-, h5⟩
        · simp only [slotRefOf, ho1', Option.bind_some]
          exact hpos1
        · rw [slotRefOf_keepPos hk hs (hold _ op z sl'' hop h5)]
          exact hc.rootClean hv op hop z sl'' h5 hzp hzD
      · exfalso
        obtain ⟨o0, ho0, hc0, hn0⟩ := hm.root
        rw [he, ho1, Option.some.injEq] at ho0
        subst ho0
        rw [hnc] at hc0; cases hc0
      · rw [slotRefOf_keepPos hk hs (hold _ o' z sl'' h4 hsl'')]
        exact hc.rootClean hv o' h4 z sl'' hsl'' hzp hzD
    · intro h o' r ho' hco' hp'
      rcases hback h o' ho' with ⟨rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨-, -, h4⟩
      · exact hc.snapND h op r hop hco' hp'
      · cases hco'
      · exact hc.snapND h o' r h4 hco' hp'

/-- The writer's follow of a live slot of the canonical object of a current node
keeps T9's invariant. -/
theorem CInv.follow4_writer (hinv : Inv sp db k) (hls : LiveSub sp) (hm : EInv sp db S0 k m)
    (hc : CInv sp db S0 m) {hp : Nat} {op : Obj V} (hop : m.obj? hp = some op)
    (hco : op.canonical = true) (hr : reachable sp db.P k op.node = true) {y : NodeId}
    (hy : y ∈ sp.live op.hist) : CInv sp db S0 (m.follow4 sp S0 db.S hp y true).1 := by
  obtain ⟨n, hn, hhist, -, -⟩ := hm.cc hp op hop hco
  have hy' : y ∈ sp.live (n.hist.upTo k) := by
    rw [upTo_of_forall _ _ (hinv.times _ n hn), ← hhist]; exact hy
  obtain ⟨-, hyroot, ny, hny, hlt⟩ := hinv.reach_child hls hn hr hy'
  have hyw : written sp y = true := written_of_ne_root sp hyroot
  have hyne : y ≠ op.node := by
    intro he; rw [he, hn, Option.some.injEq] at hny; subst hny; omega
  rw [follow4_eq]
  cases hrc : m.reached4 sp S0 db.S hp y with
  | none => exact hc
  | some p =>
    obtain ⟨m1, h1⟩ := p
    simp only [↓reduceIte]
    obtain ⟨hop2, -, -⟩ := hm.reached4_frame hop hrc
    have hm2 := hm.reached4 hinv hrc
    have hc2 := hc.reached4 hinv hm hrc
    have hsl2 : (op.setSlot y (Slot.mem h1)).slot? y = some (Slot.mem h1) := by
      obtain ⟨op0, sl, hop0, hsl0, -⟩ := reached4_cases hrc
      rw [hop, Option.some.injEq] at hop0; subst hop0
      rw [slot?_setSlot_of hsl0]; simp
    exact hc2.promote_step hinv hm2 hop2 hco hr hy hyw hyne hsl2

/-- The writer reaches one node of a path. -/
theorem CInv.reachOnPath4 (hinv : Inv sp db k) (hls : LiveSub sp) (hm : EInv sp db S0 k m)
    (hc : CInv sp db S0 m) {path : List NodeId} (hpath : ∀ p ∈ path, reachable sp db.P k p = true)
    (x : NodeId) : CInv sp db S0 (m.reachOnPath4 sp S0 db.S db.P (k + 1) path x) := by
  unfold Mem.reachOnPath4
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
      | some hp =>
        simp only
        rw [hnp, hcp] at hpp
        simp only [hK1, List.contains_iff_mem] at hpp
        obtain ⟨op, hop, hco, hnode⟩ := hm.obj_of_canonicalOf hcp
        obtain ⟨nf, hnf, hh', -, -⟩ := hm.cc hp op hop hco
        rw [hnode, hnp, Option.some.injEq] at hnf
        subst hnf
        have hxop : x ∈ sp.live op.hist := by
          rw [hh', ← upTo_of_forall _ _ (hinv.times p np hnp)]; exact hpp
        exact hc.follow4_writer hinv hls hm hop hco (by rw [hnode]; exact hpath p hpm) hxop

/-- The writer reaches the nodes of its paths: T9's invariant is kept. -/
theorem CInv.reachPath4 (hinv : Inv sp db k) (hls : LiveSub sp) (hev : EvLogic sp db k)
    {path : List NodeId} (hpath : ∀ p ∈ path, reachable sp db.P k p = true) :
    ∀ (L : List NodeId) (m : Mem V), EInv sp db S0 k m → CInv sp db S0 m →
      CInv sp db S0 (L.foldl (Mem.reachOnPath4 sp S0 db.S db.P (k + 1) path) m) := by
  intro L
  induction L with
  | nil => intro m _ hc; exact hc
  | cons x L ih =>
    intro m hm hc
    simp only [List.foldl_cons]
    exact ih _ (hm.reachOnPath4_ok hinv hls hev hpath x).1 (hc.reachOnPath4 hinv hls hm hpath x)

end Walk

end SIS
