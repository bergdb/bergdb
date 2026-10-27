/-
Proofs about reclaim with handles (bergdb 005-62), part 1 of T12 over handles:
reads in a state later than a restart from a stream on which a cut at c is
safe. A read through the handles at a time from the first available time of
the restart's state on gives the same on the streams cut at c (the stream now,
and the restart's stream for Rule R) as on the whole streams: its loads are of
versions at least as new as one that `LaterOK` allows (`ReadsPhys` in the
restart's state at the earlier of t and the restart, or a version written after
it), so at c or later. T9's invariant (`CInvH`) is all it needs of the memory:
the readers' slow path may take the live handle's snapshot when it is at least
as new as the pointer's reference, and such a snapshot names its live children
at versions at least as new as those that the older version names (lemma M,
`Inv.ref_mono`; Rule R is monotone), which `LaterOK` allows.
-/
import SIS.Proof.HandleCut
import SIS.Proof.CutLaterRead

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## Rule R of a cut stream, and its order -/

section RuleR

variable {S0 : Stream V T}

/-- The slow path's reference is the same with Rule R of the stream cut at c,
when c is at or before the startup pos. -/
theorem HMem.slowRef_cutS0 {c : Nat} (m : HMem V) (h : c ≤ m.s) (y : NodeId) (p : HPtr) :
    m.slowRef (cutStream c S0) y p = m.slowRef S0 y p := by
  unfold HMem.slowRef
  rw [ruleRRef_cut h]

/-- Rule R keeps the order of references. -/
theorem ruleRRef_mono {s : Nat} {y : NodeId} {r1 r2 a b : Nat} (hle : r1 ≤ r2)
    (ha : ruleRRef S0 s y (some r1) = some a) (hb : ruleRRef S0 s y (some r2) = some b) : a ≤ b := by
  unfold ruleRRef at ha hb
  cases hn : newest S0 s y with
  | none =>
    rw [hn] at ha hb
    simp only [Option.some.injEq] at ha hb
    omega
  | some w =>
    rw [hn] at ha hb
    simp only at ha hb
    split at ha <;> split at hb <;> simp only [Option.some.injEq] at ha hb <;> omega

end RuleR

/-! ## Objects and pointers that a read at t may follow after a later restart -/

/-- Object b, of node y, can be read at t on the cut streams: it is canonical,
or the snapshot of a version at least as new as one that `LaterOK` allows and
that is good for t. -/
def HLaterSafeT (sp : Spec V T) (db1 : DB V T) (j1 : Nat) (db : DB V T) (m : HMem V) (t : Time)
    (b : Nat) (y : NodeId) : Prop :=
  ∃ o, m.obj? b = some o ∧ o.node = y ∧
    (o.canonical = true ∨ ∃ r w r1 u, o.pos = some r ∧ db.S.versionAt r y = some w ∧
      db.S.versionAt r1 y = some u ∧ r1 ≤ r ∧ LaterOK sp db1 j1 t u ∧ good sp db.S db.P t u = true)

/-- A pointer for y that a read at t may follow on the cut streams: y has a
canonical object, which every follow of a pointer to y reaches; or the slow
path's reference is at least the record of a version of y that `LaterOK`
allows and that is good for t. -/
def HPtrLaterT (sp : Spec V T) (S0 : Stream V T) (db1 : DB V T) (j1 : Nat) (db : DB V T) (m : HMem V)
    (t : Time) (y : NodeId) (p : HPtr) : Prop :=
  (m.canonicalOf y).isSome = true ∨
    ∃ r1 u, db.S.versionAt r1 y = some u ∧ LaterOK sp db1 j1 t u ∧ good sp db.S db.P t u = true ∧
      ∀ r, m.slowRef S0 y p = some r → r1 ≤ r

section Later

variable {sp : Spec V T} {db1 db : DB V T} {j1 j : Nat} {m : HMem V}

theorem HLaterSafeT.keep {t : Time} {b : Nat} {y : NodeId} {m' : HMem V}
    (hr : HLaterSafeT sp db1 j1 db m t b y) {o o' : HObj V} (ho : m.obj? b = some o)
    (ho' : m'.obj? b = some o') (hc : o'.core = o.core) : HLaterSafeT sp db1 j1 db m' t b y := by
  obtain ⟨o1, ho1, hn, hcs⟩ := hr
  rw [ho, Option.some.injEq] at ho1
  subst ho1
  have e1 : o'.node = o.node := congrArg (fun c => c.1) hc
  have e5 : o'.canonical = o.canonical := congrArg (fun c => c.2.2.2.2.1) hc
  have e6 : o'.pos = o.pos := congrArg (fun c => c.2.2.2.2.2) hc
  exact ⟨o', ho', by rw [e1, hn], by rw [e5, e6]; exact hcs⟩

/-- The readers' follow of a pointer that a read at t may follow gives the same
on the cut streams as on the whole streams. -/
theorem HEInv.followR_later (hL : Later sp db1 db j1 j) (hm : HEInv sp db db1.S j m) {c : Nat}
    (hcut : CutOK sp c db1 j1) {t : Time} (hft : lastFa db1.S ≤ t) {a : Nat}
    {o : HObj V} (ho : m.obj? a = some o) {y : NodeId} {p : HPtr} (hp : o.ptr? y = some p)
    (hg : HPtrLaterT sp db1.S db1 j1 db m t y p) :
    m.followR sp (cutStream c db1.S) (cutStream c db.S) a y = m.followR sp db1.S db.S a y := by
  have hinv := hL.inv
  have hcs : c ≤ m.s := by
    rw [hm.sEq]
    have h1 := hcut.1
    have h2 := hL.fa1
    omega
  by_cases hfast : ∃ n0 b0 ob0, p.handle = some n0 ∧ m.objOf n0 = some b0 ∧ m.obj? b0 = some ob0 ∧
      ob0.usable p.ref = true
  · obtain ⟨n0, b0, ob0, hn0, hb0, hob0, hu0⟩ := hfast
    rw [HMem.followR_fast sp (cutStream c db1.S) (cutStream c db.S) ho hp hn0 hb0 hob0 hu0,
      HMem.followR_fast sp db1.S db.S ho hp hn0 hb0 hob0 hu0]
  · have hnf : ∀ n0 b0 ob0, p.handle = some n0 → m.objOf n0 = some b0 → m.obj? b0 = some ob0 →
        ob0.usable p.ref = false := by
      intro n0 b0 ob0 h1 h2 h3
      cases hu : ob0.usable p.ref with
      | false => rfl
      | true => exact absurd ⟨n0, b0, ob0, h1, h2, h3, hu⟩ hfast
    rw [HMem.followR_slow sp (cutStream c db1.S) (cutStream c db.S) ho hp hnf,
      HMem.followR_slow sp db1.S db.S ho hp hnf, HMem.slowRef_cutS0 m hcs]
    have hm1 := hm.writeBack hinv ho hp
    rw [HMem.setRef_eq ho hp] at hm1 ⊢
    have ho1 := HMem.obj?_setObj_self m a (o.setPtr y { p with ref := m.slowRef db1.S y p })
    have hp1 : (o.setPtr y { p with ref := m.slowRef db1.S y p }).ptr? y =
        some { p with ref := m.slowRef db1.S y p } := by
      rw [HObj.ptr?_setPtr_of hp]; simp
    have hc1 : (m.setObj a (o.setPtr y { p with ref := m.slowRef db1.S y p })).canonicalOf y =
        m.canonicalOf y := HMem.canonicalOf_setObj_core ho (HObj.setPtr_core _ _ _) y
    have hl : ((m.setObj a (o.setPtr y { p with ref := m.slowRef db1.S y p })).resolve a y).1.load sp
        (cutStream c db.S) ((m.setObj a (o.setPtr y { p with ref := m.slowRef db1.S y p })).resolve a y).2
        (m.slowRef db1.S y p) =
        ((m.setObj a (o.setPtr y { p with ref := m.slowRef db1.S y p })).resolve a y).1.load sp db.S
        ((m.setObj a (o.setPtr y { p with ref := m.slowRef db1.S y p })).resolve a y).2
        (m.slowRef db1.S y p) := by
      generalize m.setObj a (o.setPtr y { p with ref := m.slowRef db1.S y p }) = M1 at ho1 hm1 hc1 ⊢
      obtain ⟨hd1, hh1, hhn1⟩ := HMem.resolve_handle hm1.tbl ho1 hp1
      apply HMem.load_cut
      intro hd q w hh hq hw hnu
      rw [hh1, Option.some.injEq] at hh
      subst hh
      rw [hhn1] at hw
      rcases hg with hcan | ⟨r1, u, hu, hok, -, hle⟩
      · obtain ⟨cc, hcc⟩ := Option.isSome_iff_exists.mp hcan
        rw [← hc1] at hcc
        obtain ⟨hd', hh', hhc', oc, hoc, hcan'⟩ := HMem.resolve_canonical hm1.tbl ho1 hp1 hcc
        rw [hh1, Option.some.injEq] at hh'
        subst hh'
        have := hnu cc oc hhc' hoc
        simp [HObj.usable, hcan'] at this
      · have h1 := hle q hq
        have h2 := hok.ge hL hcut hft
        rw [(hinv.version_node hu).2.1] at h2
        omega
    rw [hl]

/-- The object that a follow of such a pointer reaches can be read at t on the
cut streams. -/
theorem HFollowed.laterSafe (hm : HEInv sp db db1.S j m) {m1 : HMem V} {a : Nat} {o : HObj V}
    (ho : m.obj? a = some o) {z : NodeId} {p : HPtr} (hp : o.ptr? z = some p) {n b : Nat}
    (hF : HFollowed sp db1.S db j m m1 a z n b) (hne : o.node ≠ z) {t : Time}
    (hg : HPtrLaterT sp db1.S db1 j1 db m t z p) : HLaterSafeT sp db1 j1 db m1 t b z := by
  rcases hg with hcs | ⟨r1, u, hu, hok, hgu, hle⟩
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
  · obtain ⟨ob, hob, husable⟩ := hF.usable o p ho hp
    obtain ⟨ob', hob', hony⟩ := hF.obj
    rw [hob, Option.some.injEq] at hob'
    rw [← hob'] at hony
    refine ⟨ob, hob, hony, ?_⟩
    cases hcb : ob.canonical with
    | true => exact Or.inl rfl
    | false =>
      right
      unfold HObj.usable at husable
      rw [hcb, Bool.false_or] at husable
      cases hsr : m.slowRef db1.S z p with
      | none => rw [hsr] at husable; simp at husable
      | some r =>
        rw [hsr] at husable
        cases hq : ob.pos with
        | none => rw [hq] at husable; simp at husable
        | some q =>
          rw [hq] at husable
          simp only [decide_eq_true_eq] at husable
          obtain ⟨r2, w2, e1, e2, -⟩ := hF.inv.snap b ob hob hcb
          rw [hq, Option.some.injEq] at e1
          rw [← e1, hony] at e2
          exact ⟨q, w2, r1, u, rfl, e2, hu, by have := hle r hsr; omega, hok, hgu⟩

/-- The pointers of an object that can be read at t (also on the cut streams), of
a node reachable at t, for its live children at t: as a read at t on the cut
streams needs them. -/
theorem HEInv.laterPtr (hL : Later sp db1 db j1 j) (hls : LiveSub sp) (hm : HEInv sp db db1.S j m)
    (hc : CInvH sp db db1.S m) {t : Time} (ht : t ≤ j) {b : Nat} {y : NodeId}
    (hrd : HReadableT sp db m t b y) (hcs : HLaterSafeT sp db1 j1 db m t b y)
    (hr : reachable sp db.P t y = true) {o : HObj V} (ho : m.obj? b = some o) {z : NodeId}
    (hz : z ∈ sp.live (o.hist.upTo t)) {p : HPtr} (hp : o.ptr? z = some p) :
    HPtrLaterT sp db1.S db1 j1 db m t z p := by
  have hinv := hL.inv
  obtain ⟨o1, ho1, hoy, hcase⟩ := hcs
  rw [ho, Option.some.injEq] at ho1
  subst ho1
  -- A pointer to a node with a canonical object, or whose slow path's reference
  -- is at least the latest version of a clean written pointee reachable at t.
  have hlatest : reachable sp db.P t z = true → inD db.D z = false → written sp z = true →
      (m.holdsCanonical p = true ∨
        ∃ u r, db.S.lv z = some u ∧ m.slowRef db1.S z p = some r ∧ u.recNo ≤ r) →
      HPtrLaterT sp db1.S db1 j1 db m t z p := by
    intro hrz hzD hzw h
    rcases h with h | ⟨u, r, hl, hsr, hle⟩
    · obtain ⟨-, -, -, hcs⟩ := HMem.holdsLive_of_holdsCanonical hm.tbl (hm.tbl.ptr_nodes ho hp) h
      exact Or.inl hcs
    · right
      obtain ⟨u', hu', hg'⟩ := hinv.clean_good hls hzD hzw ht hrz
      rw [hl, Option.some.injEq] at hu'
      subst hu'
      refine ⟨u.recNo, u, hinv.lv_at hl, ?_, hg', fun r' hr' => ?_⟩
      · exact hL.VOK_ok ht hrz (hinv.VOK_lv hL.pre hl) (hinv.lv_at hl)
      · rw [hsr, Option.some.injEq] at hr'
        subst hr'
        exact hle
  -- A version that `LaterOK` allows and that is good for t, of node x: the version
  -- of z that Rule R gives for its reference is one too, and the slow path's
  -- reference of a pointer at least that reference is at least it.
  have hchild : ∀ (x : NodeId) (r0 : Nat) (u0 : Version V), db.S.versionAt r0 x = some u0 →
      LaterOK sp db1 j1 t u0 → good sp db.S db.P t u0 = true → z ∈ sp.live (u0.hist.upTo t) →
      reachable sp db.P t z = true →
      (∀ q0, u0.ref? z = some q0 → ∀ q1, ruleRRef db1.S m.s z (some q0) = some q1 →
        ∀ r, m.slowRef db1.S z p = some r → q1 ≤ r) →
      HPtrLaterT sp db1.S db1 j1 db m t z p := by
    intro x r0 u0 hu0 hok0 hg0 hz0 hrz hge
    right
    obtain ⟨q0, wq, hq0, hwq, -, hgq⟩ := ((good_iff sp db.S db.P t u0).mp hg0).2 z hz0
    obtain ⟨q1, hq1⟩ := ruleRRef_some_some db1.S m.s z q0
    have hpre : db1.S <+: db.S := hL.pre
    obtain ⟨⟨u1, hu1⟩, -⟩ := hinv.ruleR_bound hpre m.s
      (fun r' h' => by rw [Option.some.injEq] at h'; subst h'; exact ⟨wq, hwq⟩) hq1
    have hsEq : m.s = lastSp db1.S := hm.sEq
    refine ⟨q1, u1, hu1, ?_, ?_, fun r hr => hge q0 hq0 q1 hq1 r hr⟩
    · rw [hsEq] at hq1
      exact hL.own_ok ht hu0 hok0 hz0 hrz (by rw [hq0]; exact hq1) hu1
    · exact hinv.good_of_le hls hwq hu1 (ruleRRef_some_ge hq1) hgq
  cases hco : o.canonical with
  | true =>
    obtain ⟨hrz, hzr, hzw⟩ := hm.reach_child hinv hls ho hco (by rw [hoy]; exact hr) hz
    have hzp : z ∈ pointees sp o.hist := mem_pointees_of_live hls hz
    by_cases hyw : written sp y = true
    · cases hyD : inD db.D y with
      | false =>
        -- A clean node: its latest version, good for t, which `LaterOK` allows.
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
        have hokv : LaterOK sp db1 j1 t v := hL.VOK_ok ht hr (hinv.VOK_lv hL.pre hv) (hinv.lv_at hv)
        rcases hc.mono b o ho hco (by rw [hoy]; exact hyw) (by rw [hoy]; exact hyD) v (by rw [hoy]; exact hv)
          z p with hmono
        cases hvz : v.ref? z with
        | none =>
          exfalso
          obtain ⟨q0, -, hq0, -⟩ := ((good_iff sp db.S db.P t v).mp hg).2 z hzv
          rw [hvz] at hq0; cases hq0
        | some r0 =>
          rcases hmono r0 hp hvz with h | ⟨r, hsr, hle⟩
          · obtain ⟨-, -, -, hcs⟩ := HMem.holdsLive_of_holdsCanonical hm.tbl (hm.tbl.ptr_nodes ho hp) h
            exact Or.inl hcs
          · refine hchild y v.recNo v (hinv.lv_at hv) hokv hg hzv hrz (fun q0 hq0 q1 hq1 r' hr' => ?_)
            rw [hvz, Option.some.injEq] at hq0
            subst hq0
            rw [hsr, Option.some.injEq] at hr'
            subst hr'
            -- the slow path's reference is a fixed point of Rule R
            have hfix := HMem.ruleR_slowRef m db1.S z p
            rw [hsr] at hfix
            exact ruleRRef_mono hle hq1 hfix
      | true =>
        -- A node of D: INV-SLOT.
        obtain ⟨p', hp', hsi⟩ := hm.slots b o ho ⟨hco, by rw [hoy]; exact hyw, Or.inr (by rw [hoy]; exact hyD)⟩
          z hzp
        rw [hp, Option.some.injEq] at hp'
        subst hp'
        cases hzD : inD db.D z with
        | true => exact Or.inl (hm.dCanon z hzD)
        | false =>
          apply hlatest hrz hzD hzw
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
        apply hlatest hrz hzD hzw
        obtain ⟨u, hu, -⟩ := hinv.clean_good hls hzD hzw ht hrz
        rcases hc.rootClean hv o ho z p hp hzp hzD u hu with h | ⟨r, hsr, hle⟩
        · exact Or.inl h
        · exact Or.inr ⟨u, r, hu, hsr, hle⟩
  | false =>
    -- A snapshot of a version at least as new as one that `LaterOK` allows.
    rcases hcase with hcase | ⟨r, w, r1, u0, hpos, hw, hu0, hr1, hok0, hg0⟩
    · rw [hco] at hcase; cases hcase
    obtain ⟨r2, w2, hp2, hw2, hh2, -, -, -, hss⟩ := hm.snap b o ho hco
    rw [hpos, Option.some.injEq] at hp2
    subst hp2
    rw [hoy, hw, Option.some.injEq] at hw2
    subst hw2
    -- The snapshot's version is good for t.
    have hgw : good sp db.S db.P t w = true := by
      obtain ⟨o2, ho2, hn2, hc2⟩ := hrd
      rw [ho, Option.some.injEq] at ho2
      subst ho2
      rcases hc2 with hc2 | ⟨r3, w3, hp3, hw3, hg3⟩
      · rw [hco] at hc2; cases hc2
      · rw [hpos, Option.some.injEq] at hp3
        subst hp3
        rw [hw, Option.some.injEq] at hw3
        subst hw3
        exact hg3
    rw [hh2] at hz
    -- Both versions are good for t, so they have the same live children at t.
    have hsame : u0.hist.upTo t = w.hist.upTo t := by
      obtain ⟨⟨n1, hn1, hh1⟩, -⟩ := (good_iff sp db.S db.P t u0).mp hg0
      obtain ⟨⟨n2, hn2, hh2'⟩, -⟩ := (good_iff sp db.S db.P t w).mp hgw
      rw [(hinv.version_node hu0).1] at hn1
      rw [(hinv.version_node hw).1, hn1, Option.some.injEq] at hn2
      subst hn2
      rw [hh1, hh2']
    have hz0 : z ∈ sp.live (u0.hist.upTo t) := by rw [hsame]; exact hz
    have hrz : reachable sp db.P t z = true := by
      obtain ⟨⟨ny, hny, hwh⟩, -⟩ := (good_iff sp db.S db.P t w).mp hgw
      rw [(hinv.version_node hw).1] at hny
      exact (hinv.reach_child hls hny hr (by rw [← hwh]; exact hz)).1
    refine hchild y r1 u0 hu0 hok0 hg0 hz0 hrz (fun q0 hq0 q1 hq1 r' hr' => ?_)
    -- w names z at least where u0 does (lemma M), and the pointer at least where w does.
    obtain ⟨qw, wq, hqw, hwq, -, -⟩ := ((good_iff sp db.S db.P t w).mp hgw).2 z hz
    have hle0 : q0 ≤ qw := by
      rcases Nat.lt_or_ge r1 r with hlt | hge
      · obtain ⟨r2', u', h2, -, hle'⟩ := hinv.ref_mono hu0 hw hlt (mem_pointees_of_live hls hz0)
          (mem_pointees_of_live hls hz) hq0
        rw [hqw, Option.some.injEq] at h2
        subst h2
        exact hle'
      · have hrr : r1 = r := by omega
        subst hrr
        rw [hu0, Option.some.injEq] at hw
        subst hw
        rw [hq0, Option.some.injEq] at hqw
        omega
    obtain ⟨qw1, hqw1⟩ := ruleRRef_some_some db1.S m.s z qw
    have h1 := ruleRRef_mono hle0 hq1 hqw1
    obtain ⟨r3, hr3, hle3⟩ := hss z p hp qw1 (by rw [hqw]; exact hqw1)
    obtain ⟨r4, hr4, hle4⟩ := HMem.slowRef_ge m db1.S z p hr3
    rw [hr', Option.some.injEq] at hr4
    omega

/-- A read at t from the first available time of the restart's state on, from an
object that can be read at t (also on the cut streams), of a node reachable at
t: the same on the cut streams as on the whole streams; the invariants, the core
of every object of a node at the object's level or higher, and the root are
kept. -/
theorem CInvH.readAtT_later (hL : Later sp db1 db j1 j) (hls : LiveSub sp) {c : Nat}
    (hcut : CutOK sp c db1 j1) {t : Time} (hft : lastFa db1.S ≤ t) (htj : t ≤ j) :
    ∀ (fuel : Nat) (m : HMem V) (b : Nat) (y : NodeId) (n : Node V), HEInv sp db db1.S j m →
      HInvH sp db db1.S j m → CInvH sp db db1.S m → HReadableT sp db m t b y →
      HLaterSafeT sp db1 j1 db m t b y →
      db.P.get? y = some n → reachable sp db.P t y = true → n.level < fuel →
      m.readAt sp (cutStream c db1.S) (cutStream c db.S) fuel t b = m.readAt sp db1.S db.S fuel t b ∧
        HEInv sp db db1.S j (m.readAt sp db1.S db.S fuel t b).1 ∧
        HInvH sp db db1.S j (m.readAt sp db1.S db.S fuel t b).1 ∧
        CInvH sp db db1.S (m.readAt sp db1.S db.S fuel t b).1 ∧
        HKeepFrom db.P n.level m (m.readAt sp db1.S db.S fuel t b).1 ∧
        (m.readAt sp db1.S db.S fuel t b).1.root = m.root := by
  have hinv := hL.inv
  intro fuel
  induction fuel with
  | zero => intro m b y n _ _ _ _ _ _ _ hlt; omega
  | succ fuel ih =>
    intro m b y n hm hh hc hrd hcs hn hr hlt
    obtain ⟨o, ho, hoy, hoh, hol, hod⟩ := hm.readableT_facts hinv hrd hn
    rw [readAt_succ_eqH sp (cutStream c db1.S) (cutStream c db.S) fuel m t b ho,
      readAt_succ_eqH sp db1.S db.S fuel m t b ho]
    have hkeepB : ∀ m', HKeepFrom db.P n.level m m' → ∃ o', m'.obj? b = some o' ∧ o'.core = o.core := by
      intro m' hk
      exact hk b o ho (fun nn hnn => by
        rw [hoy, hn, Option.some.injEq] at hnn; subst hnn; exact Nat.le_refl _)
    have hlive : sp.live (o.hist.upTo t) = sp.live (n.hist.upTo t) := by rw [hoh]
    have hstep : ∀ (acc : HMem V × List (NodeId × Node V)) z, z ∈ sp.live (o.hist.upTo t) →
        (HEInv sp db db1.S j acc.1 ∧ HInvH sp db db1.S j acc.1 ∧ CInvH sp db db1.S acc.1 ∧
          HKeepFrom db.P n.level m acc.1 ∧ acc.1.root = m.root) →
        readStepH sp (cutStream c db1.S) (cutStream c db.S) fuel t b o acc z =
            readStepH sp db1.S db.S fuel t b o acc z ∧
          (HEInv sp db db1.S j (readStepH sp db1.S db.S fuel t b o acc z).1 ∧
            HInvH sp db db1.S j (readStepH sp db1.S db.S fuel t b o acc z).1 ∧
            CInvH sp db db1.S (readStepH sp db1.S db.S fuel t b o acc z).1 ∧
            HKeepFrom db.P n.level m (readStepH sp db1.S db.S fuel t b o acc z).1 ∧
            (readStepH sp db1.S db.S fuel t b o acc z).1.root = m.root) := by
      intro acc z hz ⟨hmA, hhA, hcA, hkcA, hrA⟩
      obtain ⟨o', ho', hc'⟩ := hkeepB acc.1 hkcA
      have e4 : o'.hist = o.hist := congrArg (fun c => c.2.2.2.1) hc'
      have hz' : z ∈ sp.live (o'.hist.upTo t) := by rw [e4]; exact hz
      have hrdA := hrd.keep ho ho' hc'
      have hcsA := hcs.keep ho ho' hc'
      obtain ⟨p, hp, hg⟩ := hmA.readableT_ptr hinv hls hhA htj hrdA hr ho' hz'
      have hgc := hmA.laterPtr hL hls hcA htj hrdA hcsA hr ho' hz' hp
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
      have hfeq : acc.1.follow sp (cutStream c db1.S) (cutStream c db.S) b z false =
          acc.1.follow sp db1.S db.S b z false := by
        unfold HMem.follow
        rw [hmA.followR_later hL hcut hft ho' hp hgc]
      have hh1 : HInvH sp db db1.S j m1 := by
        have := hhA.follow_reader hinv hmA b z
        rw [hf1] at this
        exact this
      have hroot1 : m1.root = acc.1.root := HMem.follow_root sp db1.S db.S hf1
      have hc1 : CInvH sp db db1.S m1 := hcA.followed hmA ho' hp hF1 hroot1
      have hcs1 : HLaterSafeT sp db1 j1 db m1 t b1 z := hF1.laterSafe hmA ho' hp hne hgc
      obtain ⟨o1, ho1, -, -, hol1, -⟩ := hF1.inv.readableT_facts hinv hrd1 hnz
      obtain ⟨heq, hI2, hH2, hC2, hkc2, hr2⟩ := ih m1 b1 z nz hF1.inv hh1 hc1 hrd1 hcs1 hnz hrz (by omega)
      have hst : ∀ S0' S' : Stream V T, acc.1.follow sp S0' S' b z false = (m1, some b1) →
          readStepH sp S0' S' fuel t b o acc z =
            ((HMem.readAt sp S0' S' fuel m1 t b1).1, acc.2 ++ (HMem.readAt sp S0' S' fuel m1 t b1).2) := by
        intro S0' S' hS'
        unfold readStepH
        rw [hS']
        simp only [ho1, hol1, hol, hlvl, ↓reduceIte]
      rw [hst db1.S db.S hf1, hst (cutStream c db1.S) (cutStream c db.S) (by rw [hfeq]; exact hf1), heq]
      refine ⟨rfl, hI2, hH2, hC2, ?_, by rw [hr2, hroot1, hrA]⟩
      refine hkcA.trans (HKeepFrom.trans ?_ (hkc2.mono (Nat.le_of_lt hlvl)))
      intro x ox hx hlev
      apply hF1.frame x ox hx
      intro hxz
      have := hlev nz (by rw [hxz]; exact hnz)
      omega
    obtain ⟨heq, hI⟩ := foldl_eq_inv (readStepH sp (cutStream c db1.S) (cutStream c db.S) fuel t b o)
      (readStepH sp db1.S db.S fuel t b o)
      (fun acc => HEInv sp db db1.S j acc.1 ∧ HInvH sp db db1.S j acc.1 ∧ CInvH sp db db1.S acc.1 ∧
        HKeepFrom db.P n.level m acc.1 ∧ acc.1.root = m.root)
      (sp.live (o.hist.upTo t)) hstep (m, [(o.node, o.nodeAt t)]) ⟨hm, hh, hc, HKeepFrom.refl _ _ m, rfl⟩
    exact ⟨heq, hI.1, hI.2.1, hI.2.2.1, hI.2.2.2.1, hI.2.2.2.2⟩

/-- A read in a state later than a restart from a stream on which a cut at c is
safe, at a time from that state's first available time on: the same on the cut
streams (the stream now, and the restart's stream for Rule R) as on the whole
streams. -/
theorem CInvH.read_later (hL : Later sp db1 db j1 j) (hls : LiveSub sp) (hm : HEInv sp db db1.S j m)
    (hh : HInvH sp db db1.S j m) (hc : CInvH sp db db1.S m) {c : Nat} (hcut : CutOK sp c db1 j1) {t : Time}
    (hft : lastFa db1.S ≤ t) (htj : t ≤ j) :
    m.read sp (cutStream c db1.S) (cutStream c db.S) t = m.read sp db1.S db.S t := by
  have hinv := hL.inv
  obtain ⟨o, ho, hco, hn⟩ := hm.root
  obtain ⟨n0, hn0⟩ := Option.isSome_iff_exists.mp hinv.rootIn
  have hrd : HReadableT sp db m t m.root SIS.root := ⟨o, ho, hn, Or.inl hco⟩
  have hcs : HLaterSafeT sp db1 j1 db m t m.root SIS.root := ⟨o, ho, hn, Or.inl hco⟩
  obtain ⟨o', ho', -, -, hol, -⟩ := hm.readableT_facts hinv hrd hn0
  rw [ho, Option.some.injEq] at ho'
  subst ho'
  unfold HMem.read
  rw [ho]
  exact (CInvH.readAtT_later hL hls hcut hft htj (o.level + 1) m m.root SIS.root n0 hm hh hc hrd hcs hn0
    (reachable_root hn0 t) (by omega)).1

/-! ## The writer's walk after a later restart -/

/-- The writer's follow of a live pointer of the canonical object of a current
node gives the same on the cut streams: the pointer holds its pointee's live
handle with its canonical object, or the record rule gives the pointee's latest
version, which `LaterOK` allows. -/
theorem HEInv.followW_later (hL : Later sp db1 db j1 j) (hls : LiveSub sp) (hm : HEInv sp db db1.S j m)
    {c : Nat} (hcut : CutOK sp c db1 j1) {a : Nat} {op : HObj V} (hop : m.obj? a = some op)
    (hco : op.canonical = true) (hr : reachable sp db.P j op.node = true) {x : NodeId}
    (hx : x ∈ sp.live op.hist) :
    m.follow sp (cutStream c db1.S) (cutStream c db.S) a x true = m.follow sp db1.S db.S a x true := by
  have hinv := hL.inv
  have hfj : lastFa db1.S ≤ j := by
    have h1 := hL.fa1
    have h2 := hL.inv1.spLt
    have h3 := hL.le
    have h4 := hL.inv1.len
    omega
  obtain ⟨n, hn, hhist, -, -⟩ := hm.cc a op hop hco
  have hx' : x ∈ sp.live (n.hist.upTo j) := by
    rw [upTo_of_forall _ _ (hinv.times _ n hn), ← hhist]; exact hx
  obtain ⟨e, he, hxe⟩ := hls _ _ hx'
  obtain ⟨nx, hnx, hlt⟩ := hinv.ptrs op.node n hn e (mem_upTo.mp he).1 x hxe
  have hxroot : x ≠ SIS.root := hinv.ptr_ne_root hn (mem_upTo.mp he).1 hxe
  have hxw : written sp x = true := written_of_ne_root sp hxroot
  have hrx : reachable sp db.P j x = true := by
    rw [reachable_iff] at hr ⊢; exact Reach.child hr hn hx' hnx hlt
  obtain ⟨p, hp, hli1, hli2⟩ := hm.live a op hop hco hr x hx
  have hg : HPtrLaterT sp db1.S db1 j1 db m j x p := by
    cases hxD : inD db.D x with
    | true =>
      obtain ⟨-, -, -, hcs⟩ := hli1 hxD
      exact Or.inl hcs
    | false =>
      cases hhc : m.holdsCanonical p with
      | true =>
        obtain ⟨-, -, -, hcs⟩ := HMem.holdsLive_of_holdsCanonical hm.tbl (hm.tbl.ptr_nodes hop hp) hhc
        exact Or.inl hcs
      | false =>
        right
        have he := hli2 hxD
        rw [HMem.slowRef_of_not_holds hhc] at he
        obtain ⟨u, hu, hgu⟩ := hinv.clean_good hls hxD hxw (Nat.le_refl _) hrx
        rw [hu] at he
        refine ⟨u.recNo, u, hinv.lv_at hu, hL.VOK_ok (Nat.le_refl _) hrx (hinv.VOK_lv hL.pre hu)
          (hinv.lv_at hu), hgu, fun r hr' => ?_⟩
        rw [he, Option.map_some, Option.some.injEq] at hr'
        omega
  unfold HMem.follow
  rw [hm.followR_later hL hcut hfj hop hp hg]

/-- The writer reaches one node of a path: the same on the cut streams. -/
theorem HEInv.reachOnPath_later (hL : Later sp db1 db j1 j) (hls : LiveSub sp) (hm : HEInv sp db db1.S j m)
    {c : Nat} (hcut : CutOK sp c db1 j1) {path : List NodeId}
    (hpath : ∀ p ∈ path, reachable sp db.P j p = true) (x : NodeId) :
    m.reachOnPath sp (cutStream c db1.S) (cutStream c db.S) db.P (j + 1) path x =
      m.reachOnPath sp db1.S db.S db.P (j + 1) path x := by
  have hinv := hL.inv
  unfold HMem.reachOnPath
  have hK1 : j + 1 - 1 = j := by omega
  cases hf : path.find? (fun p => match db.P.get? p, m.canonicalOf p with
      | some n, some _ => (sp.live (n.hist.upTo (j + 1 - 1))).contains x
      | _, _ => false) with
  | none => rfl
  | some p =>
    simp only
    have hpp := List.find?_some hf
    have hpm := List.mem_of_find?_eq_some hf
    cases hnp : db.P.get? p with
    | none => rw [hnp] at hpp; simp at hpp
    | some np =>
      cases hcp : m.canonicalOf p with
      | none => rfl
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
        rw [hm.followW_later hL hls hcut hop hco (by rw [hnode]; exact hpath p hpm) hxop]

/-- The writer reaches the nodes of its paths: the same on the cut streams. -/
theorem HEInv.reachPath_later (hL : Later sp db1 db j1 j) (hls : LiveSub sp) (hev : EvLogic sp db j)
    {c : Nat} (hcut : CutOK sp c db1 j1) {path : List NodeId}
    (hpath : ∀ p ∈ path, reachable sp db.P j p = true) :
    ∀ (L : List NodeId) (m : HMem V), HEInv sp db db1.S j m →
      L.foldl (HMem.reachOnPath sp (cutStream c db1.S) (cutStream c db.S) db.P (j + 1) path) m =
        L.foldl (HMem.reachOnPath sp db1.S db.S db.P (j + 1) path) m := by
  have hinv := hL.inv
  intro L
  induction L with
  | nil => intro m _; rfl
  | cons x L ih =>
    intro m hm
    simp only [List.foldl_cons]
    rw [hm.reachOnPath_later hL hls hcut hpath x]
    exact ih _ (hm.reachOnPath_ok hinv hls hev hpath x).1

end Later

end SIS
