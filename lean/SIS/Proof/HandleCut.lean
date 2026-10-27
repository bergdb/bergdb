/-
Proofs about reclaim with handles (bergdb 005-62), part 1 of T9 over handles:
reads in the running process after a cut. A read through the handles at a time
t from f on reads the stream only in a load, at the slow path's reference of a
pointer whose pointee has no canonical object; it reads only versions that
`ReadsPhys` covers, so a safe cut (`CutOK`'s part 2) changes nothing it reads.
What it needs of the memory (`CInvH`, as `CInv` of SIS/Proof/CutPhys.lean is
for Evict.lean's memory): a canonical object of a clean node has, for each
pointee, a pointer that holds a canonical object or whose slow path's
reference is at or after the one that the node's latest version names; with a
virtual root, the root's object holds the live handle of each root child of D
and names each other root child at its latest version. CInv's other parts hold
by themselves with handles: a node has at most one object in memory, held by
its live handle, and every node of D has a canonical object, which every follow
of a pointer to it reaches without a load.
-/
import SIS.Proof.HandleRestart
import SIS.Proof.CutPhys

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## The invariant -/

/-- Pointer p for y holds a handle that holds a canonical object, or its slow
path's reference is r0 or later. -/
def HMem.PtrAtLeast (S0 : Stream V T) (m : HMem V) (y : NodeId) (p : HPtr) (r0 : Nat) : Prop :=
  m.holdsCanonical p = true ∨ ∃ r, m.slowRef S0 y p = some r ∧ r0 ≤ r

/-- T9's invariant over handles, for state db, after a startup from S0. -/
structure CInvH (sp : Spec V T) (db : DB V T) (S0 : Stream V T) (m : HMem V) : Prop where
  /-- A canonical object of a written node not in D: each pointer holds a
  canonical object, or its slow path's reference is at or after the record that
  the node's latest version names for that pointee. -/
  mono : ∀ a o, m.obj? a = some o → o.canonical = true → written sp o.node = true →
    inD db.D o.node = false → ∀ v, db.S.lv o.node = some v → ∀ y p r0, o.ptr? y = some p →
      v.ref? y = some r0 → m.PtrAtLeast S0 y p r0
  /-- With a virtual root: the root's object's pointer for a root child of D
  holds a canonical object (its live handle, with its canonical object), -/
  rootD : sp.virt = true → ∀ o, m.obj? m.root = some o → ∀ y p, o.ptr? y = some p →
    y ∈ pointees sp o.hist → inD db.D y = true → m.holdsCanonical p = true
  /-- and its pointer for every other root child holds a canonical object or has
  a slow path's reference at or after that child's latest version. -/
  rootClean : sp.virt = true → ∀ o, m.obj? m.root = some o → ∀ y p, o.ptr? y = some p →
    y ∈ pointees sp o.hist → inD db.D y = false → ∀ u, db.S.lv y = some u →
      m.PtrAtLeast S0 y p u.recNo

/-- Object b, of node y, can be read at t from a stream cut safely: it is
canonical, or the snapshot of a version that a physical read at t may
follow. -/
def HCutSafeT (sp : Spec V T) (db : DB V T) (m : HMem V) (t : Time) (b : Nat) (y : NodeId) : Prop :=
  ∃ o, m.obj? b = some o ∧ o.node = y ∧
    (o.canonical = true ∨ ∃ r w, o.pos = some r ∧ db.S.versionAt r y = some w ∧
      ReadsPhys sp db.S db.P db.D t w)

/-- A pointer for y that a read at t may follow on a stream cut safely: y has a
canonical object, which every follow of a pointer to y reaches; or every version
of y at or after the slow path's reference is one that a physical read at t may
follow. -/
def HPtrCutT (sp : Spec V T) (S0 : Stream V T) (db : DB V T) (m : HMem V) (t : Time) (y : NodeId)
    (p : HPtr) : Prop :=
  (m.canonicalOf y).isSome = true ∨
    ∀ r, m.slowRef S0 y p = some r → ∀ q w, r ≤ q → db.S.versionAt q y = some w →
      ReadsPhys sp db.S db.P db.D t w

/-! ## The load and the follow on a stream cut safely -/

section Load

variable {sp : Spec V T} {S0 S : Stream V T}

/-- The load depends on the stream only through the version it reads, when the
handle's object cannot serve the reference. -/
theorem HMem.load_congr {S1 S2 : Stream V T} (M : HMem V) (n : Nat) (r : Option Nat)
    (h : ∀ hd q, M.handle? n = some hd → r = some q →
      (∀ b ob, hd.obj = some b → M.obj? b = some ob → ob.usable r = false) →
      S1.versionAt q hd.node = S2.versionAt q hd.node) :
    M.load sp S1 n r = M.load sp S2 n r := by
  unfold HMem.load
  cases hh : M.handle? n with
  | none => rfl
  | some hd =>
    simp only
    cases hb : hd.obj with
    | none =>
      simp only
      cases r with
      | none => rfl
      | some q =>
        simp only
        rw [h hd q hh rfl (fun b ob hb' _ => by rw [hb] at hb'; cases hb')]
    | some b =>
      simp only
      cases hob : M.obj? b with
      | none =>
        simp only
        cases r with
        | none => rfl
        | some q =>
          simp only
          rw [h hd q hh rfl (fun b' ob hb' hob' => by
            rw [hb, Option.some.injEq] at hb'; subst hb'; rw [hob] at hob'; cases hob')]
      | some ob =>
        simp only
        cases hu : ob.usable r with
        | true => simp
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          cases r with
          | none => rfl
          | some q =>
            simp only
            rw [h hd q hh rfl (fun b' ob' hb' hob' => by
              rw [hb, Option.some.injEq] at hb'; subst hb'; rw [hob, Option.some.injEq] at hob'
              subst hob'; exact hu)]

/-- The load gives the same on a stream cut at c when the version it would read,
if any, is at the cut or later. -/
theorem HMem.load_cut {c : Nat} (M : HMem V) (n : Nat) (r : Option Nat)
    (h : ∀ hd q w, M.handle? n = some hd → r = some q → S.versionAt q hd.node = some w →
      (∀ b ob, hd.obj = some b → M.obj? b = some ob → ob.usable r = false) → c ≤ q) :
    M.load sp (cutStream c S) n r = M.load sp S n r := by
  apply HMem.load_congr
  intro hd q hh hq hnu
  rcases Nat.lt_or_ge q c with hlt | hge
  · rw [versionAt_cut_lt hlt]
    cases hw : S.versionAt q hd.node with
    | none => rfl
    | some w =>
      have := h hd q w hh hq hw hnu
      omega
  · rw [versionAt_cut_ge hge]

end Load

section Follow

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : HMem V}

/-- The readers' follow of a pointer that a read at t may follow on a stream cut
safely gives the same on the cut stream as on the whole stream. -/
theorem HEInv.followR_cut (hinv : Inv sp db k) (hm : HEInv sp db S0 k m) {c : Nat}
    (hcut : CutOK sp c db k) {t : Time} (hft : lastFa db.S ≤ t) (htk : t ≤ k) {a : Nat}
    {o : HObj V} (ho : m.obj? a = some o) {y : NodeId} {p : HPtr} (hp : o.ptr? y = some p)
    (hg : HPtrCutT sp S0 db m t y p) :
    m.followR sp S0 (cutStream c db.S) a y = m.followR sp S0 db.S a y := by
  by_cases hfast : ∃ n0 b0 ob0, p.handle = some n0 ∧ m.objOf n0 = some b0 ∧ m.obj? b0 = some ob0 ∧
      ob0.usable p.ref = true
  · obtain ⟨n0, b0, ob0, hn0, hb0, hob0, hu0⟩ := hfast
    rw [HMem.followR_fast sp S0 (cutStream c db.S) ho hp hn0 hb0 hob0 hu0,
      HMem.followR_fast sp S0 db.S ho hp hn0 hb0 hob0 hu0]
  · have hnf : ∀ n0 b0 ob0, p.handle = some n0 → m.objOf n0 = some b0 → m.obj? b0 = some ob0 →
        ob0.usable p.ref = false := by
      intro n0 b0 ob0 h1 h2 h3
      cases hu : ob0.usable p.ref with
      | false => rfl
      | true => exact absurd ⟨n0, b0, ob0, h1, h2, h3, hu⟩ hfast
    rw [HMem.followR_slow sp S0 (cutStream c db.S) ho hp hnf, HMem.followR_slow sp S0 db.S ho hp hnf]
    have hm1 := hm.writeBack hinv ho hp
    rw [HMem.setRef_eq ho hp] at hm1 ⊢
    have ho1 := HMem.obj?_setObj_self m a (o.setPtr y { p with ref := m.slowRef S0 y p })
    have hp1 : (o.setPtr y { p with ref := m.slowRef S0 y p }).ptr? y =
        some { p with ref := m.slowRef S0 y p } := by
      rw [HObj.ptr?_setPtr_of hp]; simp
    have hc1 : (m.setObj a (o.setPtr y { p with ref := m.slowRef S0 y p })).canonicalOf y =
        m.canonicalOf y := HMem.canonicalOf_setObj_core ho (HObj.setPtr_core _ _ _) y
    have hl : ((m.setObj a (o.setPtr y { p with ref := m.slowRef S0 y p })).resolve a y).1.load sp
        (cutStream c db.S) ((m.setObj a (o.setPtr y { p with ref := m.slowRef S0 y p })).resolve a y).2
        (m.slowRef S0 y p) =
        ((m.setObj a (o.setPtr y { p with ref := m.slowRef S0 y p })).resolve a y).1.load sp db.S
        ((m.setObj a (o.setPtr y { p with ref := m.slowRef S0 y p })).resolve a y).2
        (m.slowRef S0 y p) := by
      generalize m.setObj a (o.setPtr y { p with ref := m.slowRef S0 y p }) = M1 at ho1 hm1 hc1 ⊢
      obtain ⟨hd1, hh1, hhn1⟩ := HMem.resolve_handle hm1.tbl ho1 hp1
      apply HMem.load_cut
      intro hd q w hh hq hw hnu
      rw [hh1, Option.some.injEq] at hh
      subst hh
      rw [hhn1] at hw
      rcases hg with hcs | hg
      · -- y's canonical object is the live handle's object, which can serve any
        -- reference.
        obtain ⟨cc, hcc⟩ := Option.isSome_iff_exists.mp hcs
        rw [← hc1] at hcc
        obtain ⟨hd', hh', hhc', oc, hoc, hcan⟩ := HMem.resolve_canonical hm1.tbl ho1 hp1 hcc
        rw [hh1, Option.some.injEq] at hh'
        subst hh'
        have := hnu cc oc hhc' hoc
        simp [HObj.usable, hcan] at this
      · have hrp := hg q hq q w (Nat.le_refl _) hw
        have := hcut.2.1 t w hft htk hrp
        rw [(hinv.version_node hw).2.1] at this
        exact this
    rw [hl]

end Follow

/-! ## What a follow keeps -/

section Keep

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : HMem V}

theorem HMem.resolve_root (m : HMem V) (a : Nat) (y : NodeId) : (m.resolve a y).1.root = m.root := by
  unfold HMem.resolve
  simp only
  split
  · rfl
  · split <;> split <;> (try split) <;> simp_all

theorem HMem.load_root (sp : Spec V T) (S : Stream V T) (m : HMem V) (n : Nat) (r : Option Nat) :
    (m.load sp S n r).1.root = m.root := by
  unfold HMem.load
  split
  · rfl
  · simp only
    split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · split <;> simp

theorem HMem.followR_root (sp : Spec V T) (S0 S : Stream V T) {m m' : HMem V} {a : Nat} {y : NodeId}
    {n b : Nat} (h : m.followR sp S0 S a y = some (m', n, b)) : m'.root = m.root := by
  unfold HMem.followR at h
  split at h
  · cases h
  · simp only at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.1]
    · split at h
      · rename_i m2 b' hl
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1]
        have e := congrArg (fun q => q.1.root) hl
        simp only at e
        rw [← e, HMem.load_root, HMem.resolve_root, HMem.setRef_root]
      · cases h

theorem HMem.follow_root (sp : Spec V T) (S0 S : Stream V T) {m m1 : HMem V} {a : Nat} {y : NodeId}
    {b : Nat} (h : m.follow sp S0 S a y false = (m1, some b)) : m1.root = m.root := by
  unfold HMem.follow at h
  cases hf : m.followR sp S0 S a y with
  | none => rw [hf] at h; simp at h
  | some r =>
    obtain ⟨m2, n, b2⟩ := r
    rw [hf] at h
    simp only [Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at h
    rw [← h.1]
    exact HMem.followR_root sp S0 S hf

/-- What `PtrAtLeast` asks of a pointer that does not change is kept by a memory
that keeps what the pointers give. -/
theorem HMem.PtrAtLeast.keep {m1 : HMem V} (ht : HTableOK m) (hk : m.KeepPtrs m1) {a : Nat}
    {o : HObj V} (ho : m.obj? a = some o) {y : NodeId} {p : HPtr} (hp : o.ptr? y = some p) {r0 : Nat}
    (h : m.PtrAtLeast S0 y p r0) : m1.PtrAtLeast S0 y p r0 := by
  rcases h with h | ⟨r, hr, hle⟩
  · exact Or.inl (hk.canon p h)
  · exact Or.inr ⟨r, by rw [hk.slowRef S0 y (ht.ptr_handle ho hp)]; exact hr, hle⟩

/-- The followed pointer, after a follow that changed it: its slow path's
reference is the one before (written back, and the live handle it now holds has
no written position). -/
theorem HFollowed.slowRef_new {m1 : HMem V} {a : Nat} {y : NodeId} {n b : Nat}
    (hF : HFollowed sp S0 db k m m1 a y n b) {p p' : HPtr} (hr : p'.ref = m.slowRef S0 y p)
    (hn : p'.handle = some n) : m1.slowRef S0 y p' = m.slowRef S0 y p := by
  obtain ⟨hd, a1, o1, hh, hl, -, -, -, -⟩ := hF.inv.tbl.entry hF.tableOf
  have hw := hF.inv.liveW n hd hh hl
  unfold HMem.slowRef
  rw [hr, hn, hF.keep.s]
  simp only [Option.bind_some, hh, hw, maxRef_none]
  exact HMem.ruleR_slowRef m S0 y p

end Keep

/-! ## Objects and pointers that a read at t may follow on a cut stream -/

section Cut

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : HMem V}

/-- The object that a follow of a pointer that a read at t may follow on a cut
stream reaches can be read at t on a cut stream. -/
theorem HFollowed.cutSafe (hm : HEInv sp db S0 k m) {m1 : HMem V} {a : Nat} {o : HObj V}
    (ho : m.obj? a = some o) {z : NodeId} {p : HPtr} (hp : o.ptr? z = some p) {n b : Nat}
    (hF : HFollowed sp S0 db k m m1 a z n b) (hne : o.node ≠ z) {t : Time}
    (hg : HPtrCutT sp S0 db m t z p) : HCutSafeT sp db m1 t b z := by
  rcases hg with hcs | hg
  · obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hcs
    obtain ⟨oc, hoc, hcc, hcn⟩ := hm.obj_of_canonicalOf hc
    have hca : c ≠ a := by
      intro he; rw [he, ho, Option.some.injEq] at hoc; rw [← hoc] at hcn; exact hne hcn
    have hoc1 := hF.others c oc hoc hca (Or.inr hcc)
    have hc1 := hF.inv.canonicalOf_of hoc1 hcc
    rw [hcn] at hc1
    obtain ⟨n', oc', htn', hcn', -, -⟩ := (m1.canonicalOf_eq_some z c).mp hc1
    rw [hF.tableOf, Option.some.injEq] at htn'
    rw [← htn', hF.objOf, Option.some.injEq] at hcn'
    rw [hcn']
    exact ⟨oc, hoc1, hcn, Or.inl hcc⟩
  · obtain ⟨ob, hob, hu⟩ := hF.usable o p ho hp
    obtain ⟨ob', hob', hony⟩ := hF.obj
    rw [hob, Option.some.injEq] at hob'
    rw [← hob'] at hony
    refine ⟨ob, hob, hony, ?_⟩
    cases hcb : ob.canonical with
    | true => exact Or.inl rfl
    | false =>
      right
      unfold HObj.usable at hu
      rw [hcb, Bool.false_or] at hu
      cases hsr : m.slowRef S0 z p with
      | none => rw [hsr] at hu; simp at hu
      | some r =>
        rw [hsr] at hu
        cases hq : ob.pos with
        | none => rw [hq] at hu; simp at hu
        | some q =>
          rw [hq] at hu
          simp only [decide_eq_true_eq] at hu
          obtain ⟨r1, w1, e1, e2, -⟩ := hF.inv.snap b ob hob hcb
          rw [hq, Option.some.injEq] at e1
          rw [← e1, hony] at e2
          exact ⟨q, w1, rfl, e2, hg r hsr q w1 hu e2⟩

/-- Every version of y at or after y's latest version is that version, which a
physical read at t follows if y is reachable at t. -/
theorem Inv.covered_from_lv (hinv : Inv sp db k) {z : NodeId} {u : Version V} (hl : db.S.lv z = some u)
    {t : Time} (hrz : reachable sp db.P t z = true) :
    ∀ q w, u.recNo ≤ q → db.S.versionAt q z = some w → ReadsPhys sp db.S db.P db.D t w := by
  intro q w hle hw
  obtain ⟨r', u', h1, h2, hqr⟩ := lv_recNo_ge hw
  rw [hl, Option.some.injEq] at h2
  subst h2
  have hr' := (hinv.version_node h1).2.1
  have hq : q = u.recNo := by omega
  subst hq
  rw [hinv.lv_at hl, Option.some.injEq] at hw
  subst hw
  exact ReadsPhys.latest z _ hrz hl

/-- A pointer that holds no canonical object has the record rule's reference as
its slow path's reference. -/
theorem HMem.slowRef_of_not_holds {p : HPtr} (h : m.holdsCanonical p = false) :
    m.ptrRef S0 y p = m.slowRef S0 y p := by
  apply HMem.ptrRef_eq_slowRef
  intro hd b ob hhd hb hob
  unfold HMem.holdsCanonical at h
  cases hn : p.handle with
  | none => rw [hn] at hhd; cases hhd
  | some n =>
    rw [hn, Option.bind_some] at hhd
    rw [hn, Option.bind_some] at h
    simp only [HMem.objOf, hhd, Option.bind_some, hb, hob] at h
    exact h

/-- The pointers of an object that can be read at t, also on a cut stream, of a
node reachable at t, for its live children at t: as a read at t on a cut stream
needs them. -/
theorem HEInv.cutPtr (hinv : Inv sp db k) (hls : LiveSub sp) (hm : HEInv sp db S0 k m)
    (hc : CInvH sp db S0 m) {t : Time} (ht : t ≤ k) {b : Nat} {y : NodeId}
    (hrd : HReadableT sp db m t b y) (hcs : HCutSafeT sp db m t b y) (hr : reachable sp db.P t y = true)
    {o : HObj V} (ho : m.obj? b = some o) {z : NodeId} (hz : z ∈ sp.live (o.hist.upTo t)) {p : HPtr}
    (hp : o.ptr? z = some p) : HPtrCutT sp S0 db m t z p := by
  obtain ⟨o1, ho1, hoy, hcase⟩ := hcs
  rw [ho, Option.some.injEq] at ho1
  subst ho1
  -- A pointer to a node with a canonical object, or one that the record rule
  -- gives z's latest version, is as needed.
  have hlatest : reachable sp db.P t z = true → (m.holdsCanonical p = true ∨
      ∃ u r, db.S.lv z = some u ∧ m.slowRef S0 z p = some r ∧ u.recNo ≤ r) → HPtrCutT sp S0 db m t z p := by
    intro hrz h
    rcases h with h | ⟨u, r, hl, hsr, hle⟩
    · obtain ⟨-, -, -, hcs⟩ := HMem.holdsLive_of_holdsCanonical hm.tbl (hm.tbl.ptr_nodes ho hp) h
      exact Or.inl hcs
    · right
      intro r' hr' q w hq hw
      rw [hsr, Option.some.injEq] at hr'
      subst hr'
      exact hinv.covered_from_lv hl hrz q w (by omega) hw
  cases hco : o.canonical with
  | true =>
    obtain ⟨hrz, hzr, hzw⟩ := hm.reach_child hinv hls ho hco (by rw [hoy]; exact hr) hz
    have hzp : z ∈ pointees sp o.hist := mem_pointees_of_live hls hz
    by_cases hyw : written sp y = true
    · cases hyD : inD db.D y with
      | false =>
        -- A clean node: its latest version, good for t, and the pointers at
        -- least as new.
        obtain ⟨v, hv, hg⟩ := hinv.clean_good hls hyD hyw ht hr
        obtain ⟨n, hn, hoh, -, -⟩ := hm.cc b o ho hco
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
        obtain ⟨r0, w0, hr0, -, -, -⟩ := ((good_iff sp db.S db.P t v).mp hg).2 z hzv
        rcases hc.mono b o ho hco (by rw [hoy]; exact hyw) (by rw [hoy]; exact hyD) v
          (by rw [hoy]; exact hv) z p r0 hp hr0 with h | ⟨r, hsr, hle⟩
        · obtain ⟨-, -, -, hcs⟩ := HMem.holdsLive_of_holdsCanonical hm.tbl (hm.tbl.ptr_nodes ho hp) h
          exact Or.inl hcs
        · right
          intro r' hr' q w hq hw
          rw [hsr, Option.some.injEq] at hr'
          subst hr'
          refine ReadsPhys.child v z w hvr hzv (Or.inr ⟨hvD, q, hw, fun r1 hr1 => ?_⟩)
          rw [hr0, Option.some.injEq] at hr1
          omega
      | true =>
        -- A node of D: INV-SLOT.
        obtain ⟨p', hp', hsi⟩ := hm.slots b o ho ⟨hco, by rw [hoy]; exact hyw, Or.inr (by rw [hoy]; exact hyD)⟩
          z hzp
        rw [hp, Option.some.injEq] at hp'
        subst hp'
        cases hzD : inD db.D z with
        | true => exact Or.inl (hm.dCanon z hzD)
        | false =>
          apply hlatest hrz
          cases hhc : m.holdsCanonical p with
          | true => exact Or.inl rfl
          | false =>
            right
            have he := hsi.1 hzD
            rw [HMem.slowRef_of_not_holds hhc] at he
            obtain ⟨u, hu, -⟩ := hinv.clean_good hls hzD hzw ht hrz
            rw [hu] at he
            exact ⟨u, u.recNo, hu, he, Nat.le_refl _⟩
    · -- A virtual root.
      have hv : sp.virt = true := by
        cases hv : sp.virt
        · simp [written, hv] at hyw
        · rfl
      have hyr : y = SIS.root := by
        rcases Classical.em (y = SIS.root) with hy | hne
        · exact hy
        · exact absurd (written_of_ne_root sp hne) hyw
      obtain ⟨o0, ho0, hc0, hn0⟩ := hm.root
      have hbr : b = m.root := by
        have e1 := hm.canonicalOf_of ho hco
        have e2 := hm.canonicalOf_of ho0 hc0
        rw [hoy, hyr] at e1
        rw [hn0] at e2
        rw [e1] at e2
        exact Option.some.inj e2
      subst hbr
      cases hzD : inD db.D z with
      | true => exact Or.inl (hm.dCanon z hzD)
      | false =>
        apply hlatest hrz
        obtain ⟨u, hu, -⟩ := hinv.clean_good hls hzD hzw ht hrz
        rcases hc.rootClean hv o ho z p hp hzp hzD u hu with h | ⟨r, hsr, hle⟩
        · exact Or.inl h
        · exact Or.inr ⟨u, r, hu, hsr, hle⟩
  | false =>
    -- A snapshot of a version that a physical read at t may follow.
    rcases hcase with hcase | ⟨r, w, hpos, hw, hrp⟩
    · rw [hco] at hcase; cases hcase
    obtain ⟨r0, w0, hp0, hw0, hh0, -, -, -, hss⟩ := hm.snap b o ho hco
    rw [hpos, Option.some.injEq] at hp0
    subst hp0
    rw [hoy, hw, Option.some.injEq] at hw0
    subst hw0
    rw [hh0] at hz
    obtain ⟨hwn, hwr, -⟩ := hinv.version_node hw
    -- y has no canonical object: its one object in memory is this snapshot.
    have hyD : inD db.D y = false := by
      cases hyD : inD db.D y with
      | false => rfl
      | true =>
        obtain ⟨c, hcc⟩ := Option.isSome_iff_exists.mp (hm.dCanon y hyD)
        obtain ⟨oc, hoc, hcan, hcn⟩ := hm.obj_of_canonicalOf hcc
        obtain ⟨n1, ht1, hb1⟩ := hm.tbl.held ho
        obtain ⟨n2, ht2, hb2⟩ := hm.tbl.held hoc
        rw [hoy] at ht1
        rw [hcn, ht1, Option.some.injEq] at ht2
        subst ht2
        rw [hb1, Option.some.injEq] at hb2
        subst hb2
        rw [ho, Option.some.injEq] at hoc
        subst hoc
        rw [hco] at hcan; cases hcan
    have hwD : (w.node, w.recNo) ∉ db.D := by
      intro hm'
      rw [hwn] at hm'
      have := (inD_iff _ _).mpr ⟨_, hm'⟩
      rw [hyD] at this; cases this
    right
    intro r' hr' q w' hq hw'
    refine ReadsPhys.child w z w' hrp hz (Or.inr ⟨hwD, q, hw', fun r1 hr1 => ?_⟩)
    obtain ⟨q1, hq1⟩ := ruleRRef_some_some S0 m.s z r1
    have h1 := ruleRRef_some_ge hq1
    obtain ⟨r2, hr2, hle2⟩ := hss z p hp q1 (by rw [hr1]; exact hq1)
    obtain ⟨r3, hr3, hle3⟩ := HMem.slowRef_ge m S0 z p hr2
    rw [hr', Option.some.injEq] at hr3
    omega

/-- A follow keeps T9's invariant. -/
theorem CInvH.followed (hm : HEInv sp db S0 k m) (hc : CInvH sp db S0 m) {m1 : HMem V} {a : Nat}
    {oa : HObj V} (ho : m.obj? a = some oa) {y : NodeId} {pa : HPtr} (hpa : oa.ptr? y = some pa)
    {n b : Nat} (hF : HFollowed sp S0 db k m m1 a y n b) (hroot : m1.root = m.root) :
    CInvH sp db S0 m1 := by
  -- A pointer of an object of m1 that was canonical in m.
  have hptr : ∀ x o' p' r0, m1.obj? x = some o' → o'.canonical = true → ∀ z, o'.ptr? z = some p' →
      (∀ o p, m.obj? x = some o → o.ptr? z = some p → m.PtrAtLeast S0 z p r0) →
      m1.PtrAtLeast S0 z p' r0 := by
    intro x o' p' r0 ho' hc' z hp' hold
    obtain ⟨o, hox, hcore, hxa, hptrs⟩ := hF.back x o' ho' hc'
    by_cases hzy : z = y
    · subst hzy
      by_cases hx : x = a
      · subst hx
        rw [ho, Option.some.injEq] at hox
        subst hox
        rcases hF.ptrA oa pa o' ho hpa ho' with he | ⟨hnc, p'', hp'', hr'', hn''⟩
        · subst he
          rw [ho, Option.some.injEq] at ho'
          subst ho'
          rw [hpa, Option.some.injEq] at hp'
          subst hp'
          exact hold oa pa ho hpa
        · rw [hp', Option.some.injEq] at hp''
          subst hp''
          rcases hold oa pa ho hpa with h | ⟨r, hr, hle⟩
          · rw [hnc] at h; cases h
          · exact Or.inr ⟨r, by rw [hF.slowRef_new hr'' hn'', hr], hle⟩
      · rw [hxa hx] at hp'
        exact (hold o p' hox hp').keep hm.tbl hF.keep hox hp'
    · rw [hptrs z hzy] at hp'
      exact (hold o p' hox hp').keep hm.tbl hF.keep hox hp'
  refine ⟨?_, ?_, ?_⟩
  · intro x o' ho' hc' hw hD v hv z p' r0 hp' hr0
    refine hptr x o' p' r0 ho' hc' z hp' (fun o p hox hp => ?_)
    obtain ⟨o2, hox2, hcore, -, -⟩ := hF.back x o' ho' hc'
    rw [hox, Option.some.injEq] at hox2
    subst hox2
    have e1 : o'.node = o.node := congrArg (fun c => c.1) hcore
    have e5 : o'.canonical = o.canonical := congrArg (fun c => c.2.2.2.2.1) hcore
    rw [e1] at hw hD hv
    exact hc.mono x o hox (by rw [← e5]; exact hc') hw hD v hv z p r0 hp hr0
  · intro hv o' ho' z p' hp' hzp hzD
    rw [hroot] at ho'
    obtain ⟨or1, hor1, hcr1, -⟩ := hF.inv.root
    rw [hroot, ho', Option.some.injEq] at hor1
    subst hor1
    obtain ⟨o, hox, hcore, hxa, hptrs⟩ := hF.back m.root o' ho' hcr1
    have e4 : o'.hist = o.hist := congrArg (fun c => c.2.2.2.1) hcore
    rw [e4] at hzp
    have hold : ∀ p, o.ptr? z = some p → m.holdsCanonical p = true :=
      fun p hp => hc.rootD hv o hox z p hp hzp hzD
    by_cases hzy : z = y
    · subst hzy
      by_cases hx : m.root = a
      · rw [hx] at hox ho'
        rw [ho, Option.some.injEq] at hox
        subst hox
        rcases hF.ptrA oa pa o' ho hpa ho' with he | ⟨hnc, -, -, -, -⟩
        · subst he
          rw [ho, Option.some.injEq] at ho'
          subst ho'
          rw [hpa, Option.some.injEq] at hp'
          subst hp'
          exact hold pa hpa
        · rw [hold pa hpa] at hnc; cases hnc
      · rw [hxa hx] at hp'
        exact hF.keep.canon p' (hold p' hp')
    · rw [hptrs z hzy] at hp'
      exact hF.keep.canon p' (hold p' hp')
  · intro hv o' ho' z p' hp' hzp hzD u hu
    rw [hroot] at ho'
    obtain ⟨or1, hor1, hcr1, -⟩ := hF.inv.root
    rw [hroot, ho', Option.some.injEq] at hor1
    subst hor1
    refine hptr m.root o' p' u.recNo ho' hcr1 z hp' (fun o p hox hp => ?_)
    obtain ⟨o2, hox2, hcore, -, -⟩ := hF.back m.root o' ho' hcr1
    rw [hox, Option.some.injEq] at hox2
    subst hox2
    have e4 : o'.hist = o.hist := congrArg (fun c => c.2.2.2.1) hcore
    rw [e4] at hzp
    exact hc.rootClean hv o hox z p hp hzp hzD u hu

end Cut

/-! ## Reads keep the invariant; a read after a safe cut -/

section Read

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : HMem V}

theorem CInvH.followR (hinv : Inv sp db k) (hm : HEInv sp db S0 k m) (hc : CInvH sp db S0 m)
    {a : Nat} {o : HObj V} (ho : m.obj? a = some o) {y : NodeId} {m' : HMem V} {n b : Nat}
    (hf : m.followR sp S0 db.S a y = some (m', n, b)) : CInvH sp db S0 m' := by
  obtain ⟨p, hp⟩ : ∃ p, o.ptr? y = some p := by
    cases hp : o.ptr? y with
    | none => unfold HMem.followR at hf; rw [ho, Option.bind_some, hp] at hf; cases hf
    | some p => exact ⟨p, rfl⟩
  exact hc.followed hm ho hp (hm.followR_ok hinv ho hf) (HMem.followR_root sp S0 db.S hf)

theorem CInvH.follow_reader (hinv : Inv sp db k) (hm : HEInv sp db S0 k m) (hc : CInvH sp db S0 m)
    (a : Nat) (y : NodeId) : CInvH sp db S0 (m.follow sp S0 db.S a y false).1 := by
  unfold HMem.follow
  cases hf : m.followR sp S0 db.S a y with
  | none => exact hc
  | some r =>
    obtain ⟨m', n, b⟩ := r
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases ho : m.obj? a with
    | none => unfold HMem.followR at hf; rw [ho] at hf; cases hf
    | some o => exact hc.followR hinv hm ho hf

/-- A read at any time, from any object, keeps T9's invariant. -/
theorem CInvH.readAt (hinv : Inv sp db k) :
    ∀ (fuel : Nat) (m : HMem V) (t : Time) (a : Nat), HEInv sp db S0 k m → CInvH sp db S0 m →
      HEInv sp db S0 k (m.readAt sp S0 db.S fuel t a).1 ∧
        CInvH sp db S0 (m.readAt sp S0 db.S fuel t a).1 := by
  intro fuel
  induction fuel with
  | zero => intro m t a hm hc; exact ⟨hm, hc⟩
  | succ fuel ih =>
    intro m t a hm hc
    unfold HMem.readAt
    cases ho : m.obj? a with
    | none => exact ⟨hm, hc⟩
    | some o =>
      simp only
      apply foldl_invH _ (fun m => HEInv sp db S0 k m ∧ CInvH sp db S0 m) _ _ _ ⟨hm, hc⟩
      intro acc z ⟨hacc, hcacc⟩
      have hf := hacc.follow_reader hinv a z
      have hfc := hcacc.follow_reader hinv hacc a z
      generalize acc.1.follow sp S0 db.S a z false = res at hf hfc ⊢
      obtain ⟨m1, ob⟩ := res
      cases ob with
      | none => exact ⟨hf, hfc⟩
      | some b =>
        simp only
        cases ho1 : m1.obj? b with
        | none => exact ⟨hf, hfc⟩
        | some o1 =>
          simp only
          split
          · exact ih m1 t b hf hfc
          · exact ⟨hf, hfc⟩

theorem CInvH.read (hinv : Inv sp db k) (hm : HEInv sp db S0 k m) (hc : CInvH sp db S0 m) (t : Time) :
    CInvH sp db S0 (m.read sp S0 db.S t).1 := by
  unfold HMem.read
  cases m.obj? m.root with
  | none => exact hc
  | some o => exact (CInvH.readAt hinv _ m t _ hm hc).2

theorem HCutSafeT.keep {t : Time} {b : Nat} {y : NodeId} {m' : HMem V} (hr : HCutSafeT sp db m t b y)
    {o o' : HObj V} (ho : m.obj? b = some o) (ho' : m'.obj? b = some o') (hc : o'.core = o.core) :
    HCutSafeT sp db m' t b y := by
  obtain ⟨o1, ho1, hn, hcs⟩ := hr
  rw [ho, Option.some.injEq] at ho1
  subst ho1
  have e1 : o'.node = o.node := congrArg (fun c => c.1) hc
  have e5 : o'.canonical = o.canonical := congrArg (fun c => c.2.2.2.2.1) hc
  have e6 : o'.pos = o.pos := congrArg (fun c => c.2.2.2.2.2) hc
  exact ⟨o', ho', by rw [e1, hn], by rw [e5, e6]; exact hcs⟩

/-- A read at t from f on, from an object that can be read at t (also on a cut
stream), of a node reachable at t: the same on the stream cut safely as on the
whole stream; the invariants, the core of every object of a node at the object's
level or higher, and the root are kept. -/
theorem CInvH.readAtT_cut (hinv : Inv sp db k) (hls : LiveSub sp) {c : Nat} (hcut : CutOK sp c db k)
    {t : Time} (hft : lastFa db.S ≤ t) (htk : t ≤ k) :
    ∀ (fuel : Nat) (m : HMem V) (b : Nat) (y : NodeId) (n : Node V), HEInv sp db S0 k m →
      HInvH sp db S0 k m → CInvH sp db S0 m → HReadableT sp db m t b y → HCutSafeT sp db m t b y →
      db.P.get? y = some n → reachable sp db.P t y = true → n.level < fuel →
      m.readAt sp S0 (cutStream c db.S) fuel t b = m.readAt sp S0 db.S fuel t b ∧
        HEInv sp db S0 k (m.readAt sp S0 db.S fuel t b).1 ∧
        HInvH sp db S0 k (m.readAt sp S0 db.S fuel t b).1 ∧
        CInvH sp db S0 (m.readAt sp S0 db.S fuel t b).1 ∧
        HKeepFrom db.P n.level m (m.readAt sp S0 db.S fuel t b).1 ∧
        (m.readAt sp S0 db.S fuel t b).1.root = m.root := by
  intro fuel
  induction fuel with
  | zero => intro m b y n _ _ _ _ _ _ _ hlt; omega
  | succ fuel ih =>
    intro m b y n hm hh hc hrd hcs hn hr hlt
    obtain ⟨o, ho, hoy, hoh, hol, hod⟩ := hm.readableT_facts hinv hrd hn
    rw [readAt_succ_eqH sp S0 (cutStream c db.S) fuel m t b ho, readAt_succ_eqH sp S0 db.S fuel m t b ho]
    have hkeepB : ∀ m', HKeepFrom db.P n.level m m' → ∃ o', m'.obj? b = some o' ∧ o'.core = o.core := by
      intro m' hk
      exact hk b o ho (fun nn hnn => by
        rw [hoy, hn, Option.some.injEq] at hnn; subst hnn; exact Nat.le_refl _)
    have hlive : sp.live (o.hist.upTo t) = sp.live (n.hist.upTo t) := by rw [hoh]
    have hstep : ∀ (acc : HMem V × List (NodeId × Node V)) z, z ∈ sp.live (o.hist.upTo t) →
        (HEInv sp db S0 k acc.1 ∧ HInvH sp db S0 k acc.1 ∧ CInvH sp db S0 acc.1 ∧
          HKeepFrom db.P n.level m acc.1 ∧ acc.1.root = m.root) →
        readStepH sp S0 (cutStream c db.S) fuel t b o acc z = readStepH sp S0 db.S fuel t b o acc z ∧
          (HEInv sp db S0 k (readStepH sp S0 db.S fuel t b o acc z).1 ∧
            HInvH sp db S0 k (readStepH sp S0 db.S fuel t b o acc z).1 ∧
            CInvH sp db S0 (readStepH sp S0 db.S fuel t b o acc z).1 ∧
            HKeepFrom db.P n.level m (readStepH sp S0 db.S fuel t b o acc z).1 ∧
            (readStepH sp S0 db.S fuel t b o acc z).1.root = m.root) := by
      intro acc z hz ⟨hmA, hhA, hcA, hkcA, hrA⟩
      obtain ⟨o', ho', hc'⟩ := hkeepB acc.1 hkcA
      have e4 : o'.hist = o.hist := congrArg (fun c => c.2.2.2.1) hc'
      have hz' : z ∈ sp.live (o'.hist.upTo t) := by rw [e4]; exact hz
      have hrdA := hrd.keep ho ho' hc'
      have hcsA := hcs.keep ho ho' hc'
      obtain ⟨p, hp, hg⟩ := hmA.readableT_ptr hinv hls hhA htk hrdA hr ho' hz'
      have hgc := hmA.cutPtr hinv hls hcA htk hrdA hcsA hr ho' hz' hp
      have hz2 : z ∈ sp.live (n.hist.upTo t) := by rw [← hlive]; exact hz
      obtain ⟨hrz, -, nz, hnz, hlvl⟩ := hinv.reach_child hls hn hr hz2
      have hne : o'.node ≠ z := by
        have e1 : o'.node = o.node := congrArg (fun c => c.1) hc'
        intro he
        rw [e1, hoy] at he
        rw [← he, hn, Option.some.injEq] at hnz
        rw [← hnz] at hlvl
        omega
      obtain ⟨m1, n1, b1, hf1, hF1, hrd1⟩ := hmA.follow_goodT hinv hls ho' hp hg hne
      have hfeq : acc.1.follow sp S0 (cutStream c db.S) b z false = acc.1.follow sp S0 db.S b z false := by
        unfold HMem.follow
        rw [hmA.followR_cut hinv hcut hft htk ho' hp hgc]
      have hh1 : HInvH sp db S0 k m1 := by
        have := hhA.follow_reader hinv hmA b z
        rw [hf1] at this
        exact this
      have hroot1 : m1.root = acc.1.root := HMem.follow_root sp S0 db.S hf1
      have hc1 : CInvH sp db S0 m1 := hcA.followed hmA ho' hp hF1 hroot1
      have hcs1 : HCutSafeT sp db m1 t b1 z := hF1.cutSafe hmA ho' hp hne hgc
      obtain ⟨o1, ho1, -, -, hol1, -⟩ := hF1.inv.readableT_facts hinv hrd1 hnz
      obtain ⟨heq, hI2, hH2, hC2, hkc2, hr2⟩ := ih m1 b1 z nz hF1.inv hh1 hc1 hrd1 hcs1 hnz hrz (by omega)
      have hst : ∀ S' : Stream V T, acc.1.follow sp S0 S' b z false = (m1, some b1) →
          readStepH sp S0 S' fuel t b o acc z =
            ((HMem.readAt sp S0 S' fuel m1 t b1).1, acc.2 ++ (HMem.readAt sp S0 S' fuel m1 t b1).2) := by
        intro S' hS'
        unfold readStepH
        rw [hS']
        simp only [ho1, hol1, hol, hlvl, ↓reduceIte]
      rw [hst db.S hf1, hst (cutStream c db.S) (by rw [hfeq]; exact hf1), heq]
      refine ⟨rfl, hI2, hH2, hC2, ?_, by rw [hr2, hroot1, hrA]⟩
      refine hkcA.trans (HKeepFrom.trans ?_ (hkc2.mono (Nat.le_of_lt hlvl)))
      intro x ox hx hlev
      apply hF1.frame x ox hx
      intro hxz
      have := hlev nz (by rw [hxz]; exact hnz)
      omega
    obtain ⟨heq, hI⟩ := foldl_eq_inv (readStepH sp S0 (cutStream c db.S) fuel t b o)
      (readStepH sp S0 db.S fuel t b o)
      (fun acc => HEInv sp db S0 k acc.1 ∧ HInvH sp db S0 k acc.1 ∧ CInvH sp db S0 acc.1 ∧
        HKeepFrom db.P n.level m acc.1 ∧ acc.1.root = m.root)
      (sp.live (o.hist.upTo t)) hstep (m, [(o.node, o.nodeAt t)]) ⟨hm, hh, hc, HKeepFrom.refl _ _ m, rfl⟩
    exact ⟨heq, hI.1, hI.2.1, hI.2.2.1, hI.2.2.2.1, hI.2.2.2.2⟩

/-- T9 for one read: after a safe cut, a read at a time from f on from the
running memory gives the same on the cut stream as on the whole stream. -/
theorem CInvH.read_cut (hinv : Inv sp db k) (hls : LiveSub sp) (hm : HEInv sp db S0 k m)
    (hh : HInvH sp db S0 k m) (hc : CInvH sp db S0 m) {c : Nat} (hcut : CutOK sp c db k) {t : Time}
    (hft : lastFa db.S ≤ t) (htk : t ≤ k) :
    m.read sp S0 (cutStream c db.S) t = m.read sp S0 db.S t := by
  obtain ⟨o, ho, hco, hn⟩ := hm.root
  obtain ⟨n0, hn0⟩ := Option.isSome_iff_exists.mp hinv.rootIn
  have hrd : HReadableT sp db m t m.root SIS.root := ⟨o, ho, hn, Or.inl hco⟩
  have hcs : HCutSafeT sp db m t m.root SIS.root := ⟨o, ho, hn, Or.inl hco⟩
  obtain ⟨o', ho', -, -, hol, -⟩ := hm.readableT_facts hinv hrd hn0
  rw [ho, Option.some.injEq] at ho'
  subst ho'
  unfold HMem.read
  rw [ho]
  exact (CInvH.readAtT_cut hinv hls hcut hft htk (o.level + 1) m m.root SIS.root n0 hm hh hc hrd hcs hn0
    (reachable_root hn0 t) (by omega)).1

end Read

/-! ## Evictions keep the invariant -/

section Evict

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : HMem V}

/-- An eviction keeps T9's invariant. A pointer that held the evicted handle and
its canonical object now has the object's position, its node's latest version,
as its slow path's reference, at least what the invariant asks; any other
pointer gives what it gave. -/
theorem CInvH.evict (hinv : Inv sp db k) (hm : HEInv sp db S0 k m) (hc : CInvH sp db S0 m) (n : Nat) :
    CInvH sp db S0 (m.evict db.D n) := by
  cases hev : m.evictable db.D n with
  | false => rw [HMem.evict_not m db.D n hev]; exact hc
  | true =>
  obtain ⟨hd, b, ob, hh0, -, hb, hob, hpin, -⟩ := HMem.evictable_some hev
  have hobjn : m.objOf n = some b := by simp [HMem.objOf, hh0, hb]
  have eobj := HMem.evict_obj? hev hh0 hb
  have ehd := HMem.evict_handle? hev hh0 hb
  have es := HMem.evict_s m db.D n
  have eroot := HMem.evict_root m db.D n
  obtain ⟨-, ob', hob', hon⟩ := hm.tbl.obj_of_handle hh0 hb
  rw [hob, Option.some.injEq] at hob'
  subst hob'
  -- A pointer that does not hold handle n gives what it gave.
  have hslow : ∀ (z : NodeId) (q : HPtr), q.handle ≠ some n →
      (m.evict db.D n).slowRef S0 z q = m.slowRef S0 z q := by
    intro z q hq
    unfold HMem.slowRef
    rw [es]
    cases hqn : q.handle with
    | none => rfl
    | some n' =>
      have hne : n' ≠ n := fun h => hq (by rw [hqn, h])
      simp only [Option.bind_some, ehd n', hne, ↓reduceIte]
  have hcanq : ∀ q : HPtr, q.handle ≠ some n → m.holdsCanonical q = true →
      (m.evict db.D n).holdsCanonical q = true := by
    intro q hq h
    obtain ⟨n', c, oc, hqn, hc, hoc, hcc⟩ := (m.holdsCanonical_iff q).mp h
    have hne : n' ≠ n := fun h => hq (by rw [hqn, h])
    have hcb : c ≠ b := by
      intro he
      rw [he] at hc
      apply hne
      unfold HMem.objOf at hc
      cases hq' : m.handle? n' with
      | none => rw [hq'] at hc; cases hc
      | some hd'' =>
        rw [hq'] at hc
        simp only [Option.bind_some] at hc
        exact hm.tbl.uniq hq' hc hobjn
    refine ((m.evict db.D n).holdsCanonical_iff q).mpr ⟨n', c, oc, hqn, ?_, ?_, hcc⟩
    · unfold HMem.objOf; rw [ehd n']; simp only [hne, ↓reduceIte]; exact hc
    · rw [eobj]; simp only [hcb, ↓reduceIte]; exact hoc
  -- A pointer to z of an object that stays: what `PtrAtLeast` asks, for a
  -- record at most z's latest version's.
  have hptr : ∀ x o z p r0, m.obj? x = some o → o.ptr? z = some p →
      (∀ u, db.S.lv z = some u → r0 ≤ u.recNo) → m.PtrAtLeast S0 z p r0 →
      (m.evict db.D n).PtrAtLeast S0 z p r0 := by
    intro x o z p r0 hx hp hle hpa
    by_cases hpn : p.handle = some n
    · obtain ⟨hd', hh', hnode⟩ := hm.tbl.ptrNode hx hp hpn
      rw [hh0, Option.some.injEq] at hh'
      rw [← hh'] at hnode
      have hslowE : (m.evict db.D n).slowRef S0 z p =
          maxRef (ruleRRef S0 m.s z p.ref) (m.evictWritten hd b) := by
        unfold HMem.slowRef
        rw [es, hpn]
        simp only [Option.bind_some, ehd n, ↓reduceIte]
      cases hcb : ob.canonical with
      | true =>
        right
        have hwr : m.evictWritten hd b = ob.pos := by
          unfold HMem.evictWritten
          rw [hob]
          simp only [hcb, ↓reduceIte]
        have hpos := hm.pos b ob hob hcb
        rw [hon, hnode] at hpos
        cases hl : db.S.lv z with
        | none =>
          -- An evicted object has a position.
          exfalso
          obtain ⟨hd2, b2, ob2, hh2, -, hb2, hob2, -, hps⟩ := HMem.evictable_some hev
          rw [hh0, Option.some.injEq] at hh2
          subst hh2
          rw [hb, Option.some.injEq] at hb2
          subst hb2
          rw [hob, Option.some.injEq] at hob2
          subst hob2
          rw [hpos, hl] at hps
          simp at hps
        | some u =>
          rw [hl] at hpos
          obtain ⟨r, hr, hle'⟩ := maxRef_ge_right (r := ruleRRef S0 m.s z p.ref)
            (by rw [hwr, hpos]; rfl : m.evictWritten hd b = some u.recNo)
          exact ⟨r, by rw [hslowE]; exact hr, Nat.le_trans (hle u hl) hle'⟩
      | false =>
        have hwr : m.evictWritten hd b = hd.written := by
          unfold HMem.evictWritten; rw [hob]; simp only [hcb, Bool.false_eq_true, ↓reduceIte]
        have hsl : (m.evict db.D n).slowRef S0 z p = m.slowRef S0 z p := by
          rw [hslowE, hwr]
          unfold HMem.slowRef
          rw [hpn]
          simp only [Option.bind_some, hh0]
        have hnc : m.holdsCanonical p = false := by
          cases h : m.holdsCanonical p with
          | false => rfl
          | true =>
            obtain ⟨n', c, oc, hn', hc', hoc, hcc⟩ := (m.holdsCanonical_iff p).mp h
            rw [hpn, Option.some.injEq] at hn'
            rw [← hn', hobjn, Option.some.injEq] at hc'
            rw [← hc', hob, Option.some.injEq] at hoc
            rw [← hoc, hcb] at hcc
            cases hcc
        rcases hpa with h1 | ⟨r, h1, h2⟩
        · rw [hnc] at h1; cases h1
        · exact Or.inr ⟨r, by rw [hsl]; exact h1, h2⟩
    · rcases hpa with h1 | ⟨r, h1, h2⟩
      · exact Or.inl (hcanq p hpn h1)
      · exact Or.inr ⟨r, by rw [hslow z p hpn]; exact h1, h2⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x o hx hco hw hD v hv z p r0 hp hr0
    rw [eobj] at hx
    split at hx
    · cases hx
    · refine hptr x o z p r0 hx hp (fun u hu => ?_) (hc.mono x o hx hco hw hD v hv z p r0 hp hr0)
      obtain ⟨u', hu', hle⟩ := hinv.ref_le_lv hv hr0
      rw [hu, Option.some.injEq] at hu'
      subst hu'
      exact hle
  · intro hv o hx z p hp hzp hzD
    rw [eroot, eobj] at hx
    split at hx
    · cases hx
    · have h0 := hc.rootD hv o hx z p hp hzp hzD
      by_cases hpn : p.handle = some n
      · -- The root's pointer held z's canonical object, which is pinned.
        exfalso
        obtain ⟨n', c, oc, hn', hc', hoc, hcc⟩ := (m.holdsCanonical_iff p).mp h0
        rw [hpn, Option.some.injEq] at hn'
        rw [← hn', hobjn, Option.some.injEq] at hc'
        subst hc'
        rw [hob, Option.some.injEq] at hoc
        subst hoc
        obtain ⟨hd', hh', hnode⟩ := hm.tbl.ptrNode hx hp hpn
        rw [hh0, Option.some.injEq] at hh'
        rw [← hh'] at hnode
        unfold HMem.pinned at hpin
        simp only [Bool.or_eq_false_iff, hob, hcc, Bool.true_and] at hpin
        rw [hon, hnode, hzD] at hpin
        cases hpin.2
      · exact hcanq p hpn h0
  · intro hv o hx z p hp hzp hzD u hu
    rw [eroot, eobj] at hx
    split at hx
    · cases hx
    · refine hptr m.root o z p u.recNo hx hp (fun u' hu' => ?_) (hc.rootClean hv o hx z p hp hzp hzD u hu)
      rw [hu, Option.some.injEq] at hu'
      subst hu'
      exact Nat.le_refl _

/-- Every operation between transactions keeps the invariant. -/
theorem CInvH.cacheOp (hinv : Inv sp db k) (hm : HEInv sp db S0 k m) (hc : CInvH sp db S0 m)
    (op : HCacheOp) : CInvH sp db S0 (m.cacheOp sp S0 db.S db.D op) := by
  cases op with
  | read t => exact hc.read hinv hm t
  | evict n => exact hc.evict hinv hm n

theorem CInvH.cacheOps (hinv : Inv sp db k) (ops : List HCacheOp) :
    ∀ m, HEInv sp db S0 k m → CInvH sp db S0 m →
      CInvH sp db S0 (ops.foldl (HMem.cacheOp sp S0 db.S db.D) m) := by
  induction ops with
  | nil => intro m _ hc; exact hc
  | cons op ops ih =>
    intro m hm hc
    exact ih _ (hm.cacheOp hinv op) (hc.cacheOp hinv hm op)

end Evict

end SIS
