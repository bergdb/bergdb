/-
Proofs about the physical layer, part 3: the invariant of the memory (bergdb
item 001, WP L3).

The memory m after a lazy startup from the stream S of a run state db, while
the rerun has reached time K (S and P are db's, the final ones). `memInvB` in PhysExample.lean checks it by running.
-/
import SIS.Proof.PhysMem
import SIS.Proof.Fresh
import SIS.Proof.Newer

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

section Defs

variable (sp : Spec V T) (db : DB V T)

/-- Node y's history at time t in P, empty if y is not in P. -/
def histAt (P : Struct V) (y : NodeId) (t : Time) : History V :=
  ((P.get? y).map (·.hist.upTo t)).getD []

/-- Node y at time t in P: its level and kind, its history at t (an empty node
if y is not in P). -/
def nodeAt (P : Struct V) (y : NodeId) (t : Time) : Node V :=
  match P.get? y with
  | some n => { n with hist := n.hist.upTo t }
  | none => { level := 0, isData := false, hist := [] }

/-- Object o holds all of version w, whose entries are up to K. -/
def Uncut (K : Nat) (o : Obj V) (w : Version V) : Prop :=
  o.hist = w.hist ∧ ∀ e ∈ w.hist, e.time ≤ K

/-- Object o at handle h, not canonical, holds version w of its node: all of
it, with entries up to K; or (read at runtime from the startup section) cut
back to s; then w is the node's latest version, o is the node table's object,
and the node has no entries up to K. -/
def SnapOK (m : Mem V) (K : Nat) (h : Nat) (o : Obj V) (w : Version V) : Prop :=
  ∃ r, o.pos = some r ∧ db.S.versionAt r o.node = some w ∧ o.level = w.level ∧
    o.isData = w.isData ∧
    (Uncut K o w ∨ (o.hist = w.hist.upTo (lastSp db.S) ∧ db.S.lv o.node = some w ∧
      m.tableOf o.node = some h ∧ histAt db.P o.node K = []))

/-- Object h of node y holds at least the version of record r' (or y's
canonical object, or a data node's version). -/
def AtLeast (m : Mem V) (y : NodeId) (h : Nat) (r' : Option Nat) : Prop :=
  ∃ o, m.obj? h = some o ∧ o.node = y ∧
    (o.canonical = true ∨ o.isData = true ∨ ∃ p, o.pos = some p ∧ ∀ r, r' = some r → r ≤ p)

/-- The slots of a snapshot o of version w: one for each pointee of its
history; a stream slot names w's reference, a memory slot an object at least
as new as that reference leads to with Rule R. -/
def SnapSlots (m : Mem V) (o : Obj V) (w : Version V) : Prop :=
  (∀ y ∈ pointees sp o.hist, (o.slot? y).isSome) ∧
  ∀ y sl, o.slot? y = some sl →
    sl = Slot.stream (w.ref? y) ∨
    ∃ h', sl = Slot.mem h' ∧ AtLeast m y h' (ruleRRef db.S (lastSp db.S) y (w.ref? y))

/-- Object h, of node y, can be read at time t: it is canonical, or a version
that is good for t (or cut back and empty). -/
def Readable (m : Mem V) (K : Nat) (t : Time) (h : Nat) (y : NodeId) : Prop :=
  ∃ o, m.obj? h = some o ∧ o.node = y ∧
    (o.canonical = true ∨ ∃ w, SnapOK db m K h o w ∧ (o.hist = w.hist → good sp db.S db.P t w = true))

/-- A slot for y that a read at time t may follow: to a readable object; or a
stream slot to y's canonical object, or to a version good for t. -/
def SlotGood (m : Mem V) (K : Nat) (t : Time) (y : NodeId) : Slot → Prop
  | Slot.mem h' => Readable sp db m K t h' y
  | Slot.stream r => m.canonicalOf y ≠ none ∨
      ∃ r' w, ruleRRef db.S (lastSp db.S) y r = some r' ∧ db.S.versionAt r' y = some w ∧
        good sp db.S db.P t w = true

/-- A slot for y that the writer may follow at time K: to an object that is
canonical, or a version of a data node, or y's latest version (with
`MemSlotOK`, the node table's object); or a stream slot to y's canonical
object, or leading to a version of a data node, or to y's latest version. -/
def SlotFresh (m : Mem V) (y : NodeId) : Slot → Prop
  | Slot.mem h' => ∃ o, m.obj? h' = some o ∧
      (o.canonical = true ∨ o.isData = true ∨ o.pos = (db.S.lv y).map (·.recNo))
  | Slot.stream r => m.canonicalOf y ≠ none ∨
      (∃ n r' w, db.P.get? y = some n ∧ n.isData = true ∧
        ruleRRef db.S (lastSp db.S) y r = some r' ∧ db.S.versionAt r' y = some w) ∨
      (ruleRRef db.S (lastSp db.S) y r = (db.S.lv y).map (·.recNo) ∧ (db.S.lv y).isSome)

/-- A memory slot to object h' of node y: the node table's object, or an
older version than the table's. -/
def MemSlotOK (m : Mem V) (y : NodeId) (h' : Nat) : Prop :=
  ∃ o, m.obj? h' = some o ∧ o.node = y ∧
    (m.tableOf y = some h' ∨
      (o.canonical = false ∧ ∃ h0 o0 p p0, m.tableOf y = some h0 ∧ m.obj? h0 = some o0 ∧
        o.pos = some p ∧ o0.pos = some p0 ∧ p < p0))

/-- A canonical object o at handle h, at time K: the node table's object for
its node, with the node's whole history (up to K); its record, if any, holds a
version of its node; its slots are good at every time up to K at which its
node is reachable, and fresh at K. -/
def CanonOK (m : Mem V) (K : Nat) (h : Nat) (o : Obj V) : Prop :=
  m.tableOf o.node = some h ∧
  (∃ n, db.P.get? o.node = some n ∧ o.hist = n.hist.upTo K ∧ o.level = n.level ∧
    o.isData = n.isData) ∧
  (∀ p, o.pos = some p → (db.S.versionAt p o.node).isSome) ∧
  (∀ t ≤ K, reachable sp db.P t o.node = true → ∀ y ∈ sp.live (o.hist.upTo t),
    ∃ sl, o.slot? y = some sl ∧ SlotGood sp db m K t y sl) ∧
  (reachable sp db.P K o.node = true → ∀ y ∈ sp.live o.hist,
    ∃ sl, o.slot? y = some sl ∧ SlotFresh db m y sl)

/-- The invariant of the memory m at time K. -/
structure MemInv (K : Nat) (m : Mem V) : Prop where
  sEq : m.s = lastSp db.S
  sK : lastSp db.S ≤ K
  fresh : ∀ h, m.next ≤ h → m.obj? h = none
  nodup : (m.objs.map (·.1)).Nodup
  root : m.tableOf root = some m.root ∧
    ∃ o, m.obj? m.root = some o ∧ o.canonical = true ∧ o.node = root
  tbl : ∀ y h, m.tableOf y = some h → ∃ o, m.obj? h = some o ∧ o.node = y
  born : ∀ h o, m.obj? h = some o → ∃ t ≤ K, reachable sp db.P t o.node = true
  canon : ∀ h o, m.obj? h = some o → o.canonical = true → CanonOK sp db m K h o
  snap : ∀ h o, m.obj? h = some o → o.canonical = false →
    ∃ w, SnapOK db m K h o w ∧ SnapSlots sp db m o w
  memSlot : ∀ h o y h', m.obj? h = some o → o.slot? y = some (Slot.mem h') → MemSlotOK m y h'
  coverGd : ∀ d R x, lastSp db.S < d → d ≤ K → db.S[d]? = some R → x ∈ R.gd →
    m.canonicalOf x ≠ none
  coverSec : ∀ x w, newest db.S (lastSp db.S) x = some w → w.isData = false →
    w.hist.upTo (lastSp db.S) ≠ [] → m.canonicalOf x ≠ none
  coverNew : ∀ x n e, db.P.get? x = some n → e ∈ n.hist → lastSp db.S < e.time → e.time ≤ K →
    m.canonicalOf x ≠ none

end Defs

/-! ### Memories that keep what they hold -/

/-- m' keeps what m holds: each object of m is in m' with the same node,
level, kind and record; a canonical object stays canonical; an object that is
not canonical in m' has the same history; the canonical objects of nodes stay
theirs. -/
structure Mem.Le (m m' : Mem V) : Prop where
  obj : ∀ h o, m.obj? h = some o → ∃ o', m'.obj? h = some o' ∧ o'.node = o.node ∧
    o'.level = o.level ∧ o'.isData = o.isData ∧ o'.pos = o.pos ∧
    (o.canonical = true → o'.canonical = true) ∧ (o'.canonical = false → o'.hist = o.hist)
  canon : ∀ y h, m.canonicalOf y = some h → m'.canonicalOf y = some h

theorem Mem.Le.refl (m : Mem V) : m.Le m :=
  ⟨fun _ o ho => ⟨o, ho, rfl, rfl, rfl, rfl, id, fun _ => rfl⟩, fun _ _ h => h⟩

theorem Mem.Le.trans {m m' m'' : Mem V} (h1 : m.Le m') (h2 : m'.Le m'') : m.Le m'' := by
  refine ⟨fun h o ho => ?_, fun y h hc => h2.canon y h (h1.canon y h hc)⟩
  obtain ⟨o', ho', e1, e2, e3, e4, e5, e6⟩ := h1.obj h o ho
  obtain ⟨o'', ho'', f1, f2, f3, f4, f5, f6⟩ := h2.obj h o' ho'
  refine ⟨o'', ho'', by rw [f1, e1], by rw [f2, e2], by rw [f3, e3], by rw [f4, e4],
    fun h => f5 (e5 h), fun h => ?_⟩
  rw [f6 h]
  apply e6
  cases hc : o'.canonical
  · rfl
  · have := f5 hc; rw [h] at this; cases this

/-! ### Rule R on references -/

section RuleR

variable {sp : Spec V T} {db : DB V T} {k : Nat}

/-- Rule R leads a reference to a version of y to a version of y at least as new. -/
theorem Inv.ruleR_ge (hinv : Inv sp db k) {y : NodeId} {r : Nat} {u : Version V}
    (hu : db.S.versionAt r y = some u) (s : Nat) :
    ∃ r' u', ruleRRef db.S s y (some r) = some r' ∧ db.S.versionAt r' y = some u' ∧ r ≤ r' := by
  unfold ruleRRef
  cases hn : newest db.S s y with
  | none => exact ⟨r, u, rfl, hu, Nat.le_refl _⟩
  | some w =>
    simp only
    obtain ⟨r0, -, hr0⟩ := newest_some hn
    obtain ⟨-, hrec, -⟩ := hinv.version_node hr0
    by_cases hlt : r < w.recNo
    · simp only [hlt, ↓reduceIte]
      exact ⟨w.recNo, w, rfl, by rw [hrec]; exact hr0, Nat.le_of_lt hlt⟩
    · simp only [hlt, ↓reduceIte]
      exact ⟨r, u, rfl, hu, Nat.le_refl _⟩

/-- Rule R on the reference to y's latest version gives it. -/
theorem ruleR_lv (S : Stream V T) (s : Nat) (y : NodeId) :
    ruleRRef S s y ((S.lv y).map (·.recNo)) = (S.lv y).map (·.recNo) := by
  unfold ruleRRef
  cases hn : newest S s y with
  | none => rfl
  | some w =>
    simp only
    rw [newest_lv hn]
    simp

/-- A version of y is at most y's latest version. -/
theorem Inv.le_lv (hinv : Inv sp db k) {y : NodeId} {r' : Nat} {u : Version V}
    (hu : db.S.versionAt r' y = some u) : ∃ v, db.S.lv y = some v ∧ r' ≤ v.recNo := by
  obtain ⟨r2, u2, h2, hlv, hle⟩ := lv_recNo_ge hu
  obtain ⟨-, hrec, -⟩ := hinv.version_node h2
  exact ⟨u2, hlv, by rw [hrec]; exact hle⟩

/-- L-SEC for references: a version written in R(s), ..., R(k) names, with
Rule R, the latest version of each of its pointees. -/
theorem Inv.ruleR_section (hinv : Inv sp db k) {r : Nat} {x : NodeId} {w : Version V}
    (hw : db.S.versionAt r x = some w) (hr : lastSp db.S ≤ r) {y : NodeId}
    (hy : y ∈ pointees sp w.hist) :
    ruleRRef db.S (lastSp db.S) y (w.ref? y) = (db.S.lv y).map (·.recNo) := by
  cases hnw : newest db.S (lastSp db.S) y with
  | some w' =>
    have hlv := newest_lv hnw
    obtain ⟨r0, hr0s, hr0⟩ := newest_some hnw
    obtain ⟨-, hrec0, -⟩ := hinv.version_node hr0
    unfold ruleRRef
    rw [hnw, hlv]
    simp only [Option.map_some]
    cases href : w.ref? y with
    | none => rfl
    | some ry =>
      simp only
      by_cases hlt : ry < w'.recNo
      · simp [hlt]
      · simp only [hlt, ↓reduceIte, Option.some.injEq]
        -- The reference names a version of y, which is at most the newest.
        obtain ⟨R, hR, hwR, -⟩ := versionAt_spec hw
        obtain ⟨pre, hpre, hrefw⟩ := hinv.ref r R hR w hwR
        rw [hrefw y] at href
        simp only [hy, ↓reduceIte] at href
        cases hl : (Stream.building (db.S.take r) pre).lv y with
        | none => rw [hl] at href; cases href
        | some u =>
          rw [hl] at href
          simp only [Option.map_some, Option.some.injEq] at href
          -- u is a version of y in the stream: in R(r) (pre) or before r.
          rw [lv_building] at hl
          cases hf : pre.find? (fun v => v.node == y) with
          | some u1 =>
            rw [hf] at hl
            simp only [Option.some_or, Option.some.injEq] at hl
            subst hl
            have hu1R : u1 ∈ R.vers := hpre.subset (List.mem_of_find?_eq_some hf)
            have hu1n : u1.node = y := by have := List.find?_some hf; simpa using this
            have := hinv.recNo r R hR u1 hu1R
            have hva : db.S.versionAt r y = some u1 := by
              rw [← hu1n]; exact versionAt_of_mem hR (hinv.versNodup r R hR) hu1R
            obtain ⟨r2, hr2s, hr2, hle⟩ := newest_ge hnw hva
            obtain ⟨-, hrec2, -⟩ := hinv.version_node hr2
            omega
          | none =>
            rw [hf, Option.none_or] at hl
            obtain ⟨r1, hr1⟩ := lv_versionAt hl
            rw [versionAt_take] at hr1
            split at hr1
            · obtain ⟨-, hrec1, -⟩ := hinv.version_node hr1
              obtain ⟨r2, hr2s, hr2, hle⟩ := newest_ge hnw hr1
              obtain ⟨-, hrec2, -⟩ := hinv.version_node hr2
              omega
            · cases hr1
  | none =>
    unfold ruleRRef
    rw [hnw]
    simp only
    have hnone := (newest_eq_none_iff db.S (lastSp db.S) y).mp hnw
    obtain ⟨R, hR, hvR, -⟩ := versionAt_spec hw
    obtain ⟨pre, hpre, href⟩ := hinv.ref r R hR w hvR
    have hpre_none : pre.find? (fun w => w.node == y) = none := by
      rw [List.find?_eq_none]
      intro w' hw' hw'y
      have hw'R : w' ∈ R.vers := hpre.subset hw'
      have := hnone r hr
      rw [← (show w'.node = y by simpa using hw'y)] at this
      rw [versionAt_of_mem hR (hinv.versNodup r R hR) hw'R] at this
      simp at this
    have hlvy : Stream.lv (Stream.building (db.S.take r) pre) y = db.S.lv y := by
      rw [lv_building, hpre_none, Option.none_or]
      exact lv_take (fun r' hr' => hnone r' (by omega))
    rw [href y]
    simp only [hy, ↓reduceIte]
    rw [hlvy]

end RuleR

/-! ### The facts of the run that the physical layer's proofs use -/

/-- A node that Java never cuts back (a data node, or a root child of a
virtual root), reachable by K, has its entries up to K: it gets entries only
when it is created. -/
def FixedLe (sp : Spec V T) (db : DB V T) (K : Nat) : Prop :=
  ∀ y n, db.P.get? y = some n → isKeyLevel sp n.isData n.level = false →
    (n.isData = true ∨ y ≠ root) →
    (∃ t ≤ K, reachable sp db.P t y = true) → ∀ e ∈ n.hist, e.time ≤ K

/-- The final state db of a run, after T(k): the invariant, LiveSub, and that a
data node has one version. -/
structure PCtx (sp : Spec V T) (db : DB V T) (k : Nat) : Prop where
  inv : Inv sp db k
  ls : LiveSub sp
  dataOnce : ∀ x n r w, db.P.get? x = some n → n.isData = true → db.S.versionAt r x = some w →
    db.S.lv x = some w

/-! ### Memories that differ only in slots -/

/-- An object without its slots. -/
def Obj.core (o : Obj V) : NodeId × Nat × Bool × History V × Bool × Option Nat :=
  (o.node, o.level, o.isData, o.hist, o.canonical, o.pos)

/-- m and m' have the same node table, and the same objects but for slots. -/
def Mem.SameCore (m m' : Mem V) : Prop :=
  m'.table = m.table ∧ ∀ h, (m'.obj? h).map Obj.core = (m.obj? h).map Obj.core

theorem Mem.SameCore.symm {m m' : Mem V} (h : m.SameCore m') : m'.SameCore m :=
  ⟨h.1.symm, fun x => (h.2 x).symm⟩

theorem Mem.SameCore.obj {m m' : Mem V} (hs : m.SameCore m') {h : Nat} {o : Obj V}
    (ho : m.obj? h = some o) : ∃ o', m'.obj? h = some o' ∧ o'.node = o.node ∧ o'.level = o.level ∧
      o'.isData = o.isData ∧ o'.hist = o.hist ∧ o'.canonical = o.canonical ∧ o'.pos = o.pos := by
  have := hs.2 h
  rw [ho] at this
  cases h' : m'.obj? h with
  | none => rw [h'] at this; cases this
  | some o' =>
    rw [h'] at this
    simp only [Option.map_some, Option.some.injEq, Obj.core, Prod.mk.injEq] at this
    exact ⟨o', rfl, this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2⟩

theorem Mem.SameCore.tableOf {m m' : Mem V} (hs : m.SameCore m') (y : NodeId) :
    m'.tableOf y = m.tableOf y := by
  unfold Mem.tableOf; rw [hs.1]

theorem Mem.SameCore.canonicalOf {m m' : Mem V} (hs : m.SameCore m') (y : NodeId) :
    m'.canonicalOf y = m.canonicalOf y := by
  cases hc : m.canonicalOf y with
  | some h =>
    obtain ⟨ht, o, ho, hcan⟩ := (m.canonicalOf_eq_some y h).mp hc
    obtain ⟨o', ho', -, -, -, -, hc', -⟩ := hs.obj ho
    exact (m'.canonicalOf_eq_some y h).mpr ⟨by rw [hs.tableOf]; exact ht, o', ho', by rw [hc', hcan]⟩
  | none =>
    rw [Mem.canonicalOf_eq_none] at hc ⊢
    intro h o' ht ho'
    obtain ⟨o, ho, -, -, -, -, hc', -⟩ := hs.symm.obj ho'
    have := hc h o (by rw [← hs.tableOf]; exact ht) ho
    rw [← hc', this]

section Congr

variable {sp : Spec V T} {db : DB V T} {m m' : Mem V} (hs : m.SameCore m')
include hs

theorem SnapOK.congr {K h : Nat} {o o' : Obj V} {w : Version V} (h1 : SnapOK db m K h o w)
    (e1 : o'.node = o.node) (e2 : o'.level = o.level) (e3 : o'.isData = o.isData)
    (e4 : o'.hist = o.hist) (e6 : o'.pos = o.pos) : SnapOK db m' K h o' w := by
  obtain ⟨r, hr1, hr2, hr3, hr4, hr5⟩ := h1
  refine ⟨r, by rw [e6]; exact hr1, by rw [e1]; exact hr2, by rw [e2]; exact hr3,
    by rw [e3]; exact hr4, ?_⟩
  unfold Uncut at hr5 ⊢
  rw [e4, e1, hs.tableOf]
  exact hr5

theorem Readable.congr {K : Nat} {t : Time} {h : Nat} {y : NodeId}
    (h1 : Readable sp db m K t h y) : Readable sp db m' K t h y := by
  obtain ⟨o, ho, hy, hc⟩ := h1
  obtain ⟨o', ho', e1, e2, e3, e4, e5, e6⟩ := hs.obj ho
  refine ⟨o', ho', by rw [e1, hy], ?_⟩
  rcases hc with hc | ⟨w, hw, hg⟩
  · exact Or.inl (by rw [e5, hc])
  · exact Or.inr ⟨w, SnapOK.congr hs hw e1 e2 e3 e4 e6, by rw [e4]; exact hg⟩

theorem AtLeast.congr {y : NodeId} {h : Nat} {r' : Option Nat} (h1 : AtLeast m y h r') :
    AtLeast m' y h r' := by
  obtain ⟨o, ho, hy, hc⟩ := h1
  obtain ⟨o', ho', e1, -, e3, -, e5, e6⟩ := hs.obj ho
  exact ⟨o', ho', by rw [e1, hy], by rw [e5, e3, e6]; exact hc⟩

theorem SlotGood.congr {K : Nat} {t : Time} {y : NodeId} {sl : Slot}
    (h1 : SlotGood sp db m K t y sl) : SlotGood sp db m' K t y sl := by
  cases sl with
  | mem h' => exact Readable.congr hs h1
  | stream r =>
    rcases h1 with h1 | h1
    · left; rw [hs.canonicalOf]; exact h1
    · exact Or.inr h1

theorem SlotFresh.congr {y : NodeId} {sl : Slot} (h1 : SlotFresh db m y sl) :
    SlotFresh db m' y sl := by
  cases sl with
  | mem h' =>
    obtain ⟨o, ho, hc⟩ := h1
    obtain ⟨o', ho', -, -, e3, -, e5, e6⟩ := hs.obj ho
    exact ⟨o', ho', by rw [e5, e3, e6]; exact hc⟩
  | stream r =>
    rcases h1 with h1 | h1
    · left; rw [hs.canonicalOf]; exact h1
    · exact Or.inr h1

theorem MemSlotOK.congr {y : NodeId} {h' : Nat} (h1 : MemSlotOK m y h') : MemSlotOK m' y h' := by
  obtain ⟨o, ho, hy, hc⟩ := h1
  obtain ⟨o', ho', e1, -, -, -, e5, e6⟩ := hs.obj ho
  refine ⟨o', ho', by rw [e1, hy], ?_⟩
  rcases hc with hc | ⟨hcan, h0, o0, p, p0, ht, ho0, hp, hp0, hlt⟩
  · left; rw [hs.tableOf]; exact hc
  · right
    obtain ⟨o0', ho0', -, -, -, -, -, f6⟩ := hs.obj ho0
    exact ⟨by rw [e5, hcan], h0, o0', p, p0, by rw [hs.tableOf]; exact ht, ho0', by rw [e6]; exact hp,
      by rw [f6]; exact hp0, hlt⟩

end Congr

end SIS
