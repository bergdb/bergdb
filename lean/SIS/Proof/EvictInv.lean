/-
Proofs for stage 2 (bergdb item 001, WP E3), part 3: the invariant of the memory
with eviction (bergdb 001-08, 5.3 and 5.4), and that unswizzling and
release keep it.
-/
import SIS.Proof.EvictWrite
import SIS.Proof.PhysT2

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## The invariant -/

/-- The got-dirty index of x in D, if x is in D. -/
def dOf (D : Dirty) (x : NodeId) : Option Nat := (D.find? (fun e => e.1 == x)).map (·.2)

/-- An object whose slots matter for records: a canonical object of a node that
is current at time k or in D, but a virtual root (never written). -/
def Relevant (sp : Spec V T) (db : DB V T) (k : Nat) (o : Obj V) : Prop :=
  o.canonical = true ∧ written sp o.node = true ∧
    (reachable sp db.P k o.node = true ∨ inD db.D o.node = true)

/-- The reference that slot sl for y serializes (a stream slot's after Rule R). -/
def slotRefOf (S0 : Stream V T) (m : Mem V) (y : NodeId) : Slot → Option Nat
  | Slot.mem h => (m.obj? h).bind (·.pos)
  | Slot.stream r => ruleRRef S0 m.s y r

/-- What a snapshot of version w asks of its slot sl for pointee y: a stream slot
names w's reference, or (after an unswizzle) a version at least as new as the
one that Rule R gives for that reference; a memory slot names an object of the
pointee, canonical or at least as new. -/
def SnapSlot (S0 : Stream V T) (db : DB V T) (m : Mem V) (w : Version V) (y : NodeId) (sl : Slot) :
    Prop :=
  sl = Slot.stream (w.ref? y) ∨
  (∃ p u, sl = Slot.stream (some p) ∧ db.S.versionAt p y = some u ∧
    ∀ r0, ruleRRef S0 m.s y (w.ref? y) = some r0 → r0 ≤ p) ∨
  (∃ h' o', sl = Slot.mem h' ∧ m.obj? h' = some o' ∧ o'.node = y ∧
    (o'.canonical = true ∨
      ∃ p, o'.pos = some p ∧ ∀ r0, ruleRRef S0 m.s y (w.ref? y) = some r0 → r0 ≤ p))

/-- A snapshot o: the version w of its node at its position, exactly, with a slot
for each pointee of its history, each as `SnapSlot` asks. -/
def SnapExact (sp : Spec V T) (S0 : Stream V T) (db : DB V T) (m : Mem V) (o : Obj V) : Prop :=
  ∃ r w, o.pos = some r ∧ db.S.versionAt r o.node = some w ∧ o.hist = w.hist ∧
    o.level = w.level ∧ o.isData = w.isData ∧
    (∀ y ∈ pointees sp o.hist, (o.slot? y).isSome) ∧
    ∀ y sl, o.slot? y = some sl → SnapSlot S0 db m w y sl

/-- INV-SLOT for slot sl of a relevant object o for pointee y: for y not in D it
serializes y's latest version; for y in D it is a memory slot to y's canonical
object, or o's node is in D with an index at most y's (it is written no later
than y). -/
def SlotInv (S0 : Stream V T) (db : DB V T) (m : Mem V) (o : Obj V) (y : NodeId) (sl : Slot) :
    Prop :=
  (inD db.D y = false → slotRefOf S0 m y sl = (db.S.lv y).map (·.recNo)) ∧
  (inD db.D y = true → (∃ h', sl = Slot.mem h' ∧ m.canonicalOf y = some h') ∨
    (inD db.D o.node = true ∧ ∃ a b, dOf db.D o.node = some a ∧ dOf db.D y = some b ∧ a ≤ b))

/-- The slot sl of a canonical object of a node current at k for a live child y:
for y in D a memory slot to y's canonical object; otherwise it serializes y's
latest version (what reads at k and the writer's walk rely on). -/
def LiveInv (S0 : Stream V T) (db : DB V T) (m : Mem V) (y : NodeId) (sl : Slot) : Prop :=
  (inD db.D y = true → ∃ h', sl = Slot.mem h' ∧ m.canonicalOf y = some h') ∧
  (inD db.D y = false → slotRefOf S0 m y sl = (db.S.lv y).map (·.recNo))

/-- The invariant of the memory m with eviction, for state db at time k, after a
startup from S0. -/
structure EInv (sp : Spec V T) (db : DB V T) (S0 : Stream V T) (k : Nat) (m : Mem V) : Prop where
  len : db.S.length = k + 1
  pre : S0 <+: db.S
  sEq : m.s = lastSp S0
  fresh : ∀ h, m.next ≤ h → m.obj? h = none
  objNodup : (m.objs.map (·.1)).Nodup
  root : ∃ o, m.obj? m.root = some o ∧ o.canonical = true ∧ o.node = root
  tblNodup : (m.table.map (·.1)).Nodup
  tbl : TableNode m
  slotsNode : SlotsNode m
  /-- The node table names canonical objects, and every canonical object is the
  table's (INV-CAN). -/
  tblCanon : ∀ y h, m.tableOf y = some h → ∃ o, m.obj? h = some o ∧ o.canonical = true
  canonTbl : ∀ h o, m.obj? h = some o → o.canonical = true → m.tableOf o.node = some h
  /-- A canonical object holds its node's whole history (CC) and its latest
  position. -/
  cc : ∀ h o, m.obj? h = some o → o.canonical = true →
    ∃ n, db.P.get? o.node = some n ∧ o.hist = n.hist ∧ o.level = n.level ∧ o.isData = n.isData
  pos : PosOK db.S [] m
  /-- Every node of D has a canonical object. -/
  dCanon : ∀ y, inD db.D y = true → (m.canonicalOf y).isSome
  /-- Snapshots are exact versions (INV-SNAP). -/
  snap : ∀ h o, m.obj? h = some o → o.canonical = false → SnapExact sp S0 db m o
  /-- INV-SLOT: a relevant object has a slot for each pointee, as `SlotInv` asks. -/
  slots : ∀ h o, m.obj? h = some o → Relevant sp db k o → ∀ y ∈ pointees sp o.hist,
    ∃ sl, o.slot? y = some sl ∧ SlotInv S0 db m o y sl
  /-- A canonical object of a node current at k (a virtual root too) has a slot
  for each live child, as `LiveInv` asks. -/
  live : ∀ h o, m.obj? h = some o → o.canonical = true → reachable sp db.P k o.node = true →
    ∀ y ∈ sp.live o.hist, ∃ sl, o.slot? y = some sl ∧ LiveInv S0 db m y sl

/-! ## Basic facts -/

theorem ruleRRef_some_ge {S0 : Stream V T} {s : Nat} {y : NodeId} {r r0 : Nat}
    (h : ruleRRef S0 s y (some r) = some r0) : r ≤ r0 := by
  unfold ruleRRef at h
  cases hn : newest S0 s y with
  | none => rw [hn] at h; simp at h; omega
  | some w =>
    rw [hn] at h
    simp only at h
    split at h
    · simp at h; omega
    · simp at h; omega

section Facts

variable {sp : Spec V T} {db : DB V T} {k : Nat}

/-- The reference of a version names a version of the pointee. -/
theorem Inv.ref_versionAt (hinv : Inv sp db k) {r : Nat} {x : NodeId} {v : Version V}
    (hv : db.S.versionAt r x = some v) {y : NodeId} {r1 : Nat} (h1 : v.ref? y = some r1) :
    ∃ u, db.S.versionAt r1 y = some u := by
  obtain ⟨R, hR, hvR, -⟩ := versionAt_spec hv
  obtain ⟨pre, hpre, href⟩ := hinv.ref r R hR v hvR
  rw [href y] at h1
  split at h1
  · cases hl : (Stream.building (db.S.take r) pre).lv y with
    | none => rw [hl] at h1; cases h1
    | some u =>
      rw [hl] at h1
      simp only [Option.map_some, Option.some.injEq] at h1
      obtain ⟨r0, hr0⟩ := lv_versionAt hl
      have hu0 := (sext_building_take hR hpre).versionAt hr0
      obtain ⟨-, hur, -⟩ := hinv.version_node hu0
      rw [← h1, hur]
      exact ⟨u, hu0⟩
  · cases h1

/-- Rule R of the stream of the last startup, a prefix of the stream, leaves the
reference to the latest version. -/
theorem Inv.ruleR_lv0 (hinv : Inv sp db k) {S0 : Stream V T} (hpre : S0 <+: db.S) (s : Nat)
    (y : NodeId) : ruleRRef S0 s y ((db.S.lv y).map (·.recNo)) = (db.S.lv y).map (·.recNo) := by
  unfold ruleRRef
  cases hn : newest S0 s y with
  | none => rfl
  | some w =>
    simp only
    obtain ⟨r0, -, hr0⟩ := newest_some hn
    have hr0' := versionAt_prefix hpre hr0
    obtain ⟨-, hrec, -⟩ := hinv.version_node hr0'
    obtain ⟨v, hv, hle⟩ := hinv.le_lv hr0'
    rw [hv]
    simp only [Option.map_some]
    have : ¬ v.recNo < w.recNo := by omega
    simp [this]

/-- Rule R of the stream of the last startup on a reference to a version gives a
version, at most the latest. -/
theorem Inv.ruleR_bound (hinv : Inv sp db k) {S0 : Stream V T} (hpre : S0 <+: db.S) (s : Nat)
    {y : NodeId} {r : Option Nat} (hr : ∀ r', r = some r' → ∃ u, db.S.versionAt r' y = some u)
    {r0 : Nat} (h : ruleRRef S0 s y r = some r0) :
    (∃ u, db.S.versionAt r0 y = some u) ∧ ∃ v, db.S.lv y = some v ∧ r0 ≤ v.recNo := by
  have hver : ∃ u, db.S.versionAt r0 y = some u := by
    unfold ruleRRef at h
    cases hn : newest S0 s y with
    | none => rw [hn] at h; exact hr r0 h
    | some w =>
      rw [hn] at h
      obtain ⟨r1, -, hr1⟩ := newest_some hn
      have hr1' := versionAt_prefix hpre hr1
      obtain ⟨-, hrec, -⟩ := hinv.version_node hr1'
      simp only at h
      cases r with
      | none =>
        simp only [Option.some.injEq] at h
        rw [← h, hrec]; exact ⟨w, hr1'⟩
      | some r' =>
        simp only at h
        split at h
        · simp only [Option.some.injEq] at h
          rw [← h, hrec]; exact ⟨w, hr1'⟩
        · simp only [Option.some.injEq] at h
          rw [← h]; exact hr r' rfl
  obtain ⟨u, hu⟩ := hver
  exact ⟨⟨u, hu⟩, hinv.le_lv hu⟩

/-- A clean node's latest version holds its whole history. -/
theorem Inv.lv_whole (hinv : Inv sp db k) {y : NodeId} {n : Node V} (hn : db.P.get? y = some n)
    (hw : written sp y = true) (hD : inD db.D y = false) (hr : reachable sp db.P k y = true) :
    ∃ v, db.S.lv y = some v ∧ v.hist = n.hist ∧ v.level = n.level ∧ v.isData = n.isData := by
  have hwhole : ∀ v, db.S.lv y = some v → v.hist.upTo k = n.hist.upTo k →
      v.hist = n.hist ∧ v.level = n.level ∧ v.isData = n.isData := by
    intro v hv hup
    have hva := hinv.lv_at hv
    obtain ⟨-, hrec, n', hn', hh, hl, hd⟩ := hinv.version_node hva
    rw [hn, Option.some.injEq] at hn'
    subst hn'
    have hrk : v.recNo ≤ k := by
      obtain ⟨R, hR, -, -⟩ := versionAt_spec hva
      have := (List.getElem?_eq_some_iff.mp hR).1
      rw [hinv.len] at this; omega
    refine ⟨?_, hl, hd⟩
    have h1 : v.hist.upTo k = v.hist := by rw [hh, upTo_upTo' _ hrk]
    have h2 : n.hist.upTo k = n.hist := upTo_of_forall _ _ (hinv.times y n hn)
    rw [← h1, hup, h2]
  by_cases hd : n.isData = true
  · obtain ⟨v, hv, hvh⟩ := hinv.dataV y n hn hd
    obtain ⟨h1, h2, h3⟩ := hwhole v hv (by rw [hvh])
    exact ⟨v, hv, h1, h2, h3⟩
  · have hix : isIndex db.P y = true := by simp [isIndex, hn, hd]
    have hdirty : dirty sp db.S db.P k y = false := by
      cases hdy : dirty sp db.S db.P k y with
      | false => rfl
      | true => rw [hinv.inv2 y hix hw hdy] at hD; cases hD
    obtain ⟨v, hv, hgood⟩ := (dirty_false_iff sp db.S db.P k y).mp hdirty
    have hg := hgood k (Nat.le_refl k) hr
    rw [good_eq] at hg
    simp only [Bool.and_eq_true] at hg
    have hup : v.hist.upTo k = n.hist.upTo k := by
      have h1 := hg.1
      have hvn : v.node = y := by
        obtain ⟨-, -, -⟩ := hinv.version_node (hinv.lv_at hv)
        exact (hinv.version_node (hinv.lv_at hv)).1
      rw [hvn, hn] at h1
      simpa using h1
    obtain ⟨h1, h2, h3⟩ := hwhole v hv hup
    exact ⟨v, hv, h1, h2, h3⟩

end Facts

/-! ## Memories with the same cores -/

/-- m' has m's objects but for slots, m's canonical objects, and m's startup
pos. -/
def Mem.CoreEq (m m' : Mem V) : Prop :=
  (∀ h, (m'.obj? h).map Obj.core = (m.obj? h).map Obj.core) ∧
    (∀ y, m'.canonicalOf y = m.canonicalOf y) ∧ m'.s = m.s

section Core

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m m' : Mem V}

theorem Mem.CoreEq.obj (hce : m.CoreEq m') {h : Nat} {o : Obj V}
    (ho : m.obj? h = some o) : ∃ o', m'.obj? h = some o' ∧ o'.node = o.node ∧ o'.level = o.level ∧
      o'.isData = o.isData ∧ o'.hist = o.hist ∧ o'.canonical = o.canonical ∧ o'.pos = o.pos := by
  have := hce.1 h
  rw [ho] at this
  cases h' : m'.obj? h with
  | none => rw [h'] at this; cases this
  | some o' =>
    rw [h'] at this
    simp only [Option.map_some, Option.some.injEq, Obj.core, Prod.mk.injEq] at this
    exact ⟨o', rfl, this.1, this.2.1, this.2.2.1, this.2.2.2.1, this.2.2.2.2.1, this.2.2.2.2.2⟩

theorem Mem.CoreEq.pos_eq (hce : m.CoreEq m') (h : Nat) :
    (m'.obj? h).bind (·.pos) = (m.obj? h).bind (·.pos) := by
  cases ho : m.obj? h with
  | none =>
    cases ho' : m'.obj? h with
    | none => rfl
    | some o' =>
      have := hce.1 h
      rw [ho, ho'] at this; cases this
  | some o =>
    obtain ⟨o', ho', -, -, -, -, -, hp⟩ := hce.obj ho
    rw [ho']; simp [hp]

theorem slotRefOf_congr (hce : m.CoreEq m') (y : NodeId) (sl : Slot) :
    slotRefOf S0 m' y sl = slotRefOf S0 m y sl := by
  cases sl with
  | mem h => exact hce.pos_eq h
  | stream r => simp only [slotRefOf, hce.2.2]

theorem SnapSlot.congr (hce : m.CoreEq m') {w : Version V} {y : NodeId} {sl : Slot}
    (h : SnapSlot S0 db m w y sl) : SnapSlot S0 db m' w y sl := by
  unfold SnapSlot at h ⊢
  rw [hce.2.2]
  rcases h with h | h | ⟨h', o', hsl, ho', hn, hc⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · obtain ⟨o'', ho'', e1, -, -, -, e5, e6⟩ := hce.obj ho'
    refine Or.inr (Or.inr ⟨h', o'', hsl, ho'', by rw [e1, hn], ?_⟩)
    rw [e5, e6]; exact hc

theorem SnapExact.congr (hce : m.CoreEq m') {o : Obj V} (h : SnapExact sp S0 db m o) :
    SnapExact sp S0 db m' o := by
  obtain ⟨r, w, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨r, w, h1, h2, h3, h4, h5, h6, fun y sl hsl => (h7 y sl hsl).congr hce⟩

theorem SlotInv.congr (hce : m.CoreEq m') {o : Obj V} {y : NodeId} {sl : Slot}
    (h : SlotInv S0 db m o y sl) : SlotInv S0 db m' o y sl := by
  refine ⟨fun hy => by rw [slotRefOf_congr hce]; exact h.1 hy, fun hy => ?_⟩
  rcases h.2 hy with ⟨h', hsl, hc⟩ | h2
  · exact Or.inl ⟨h', hsl, by rw [hce.2.1]; exact hc⟩
  · exact Or.inr h2

theorem LiveInv.congr (hce : m.CoreEq m') {y : NodeId} {sl : Slot}
    (h : LiveInv S0 db m y sl) : LiveInv S0 db m' y sl := by
  refine ⟨fun hy => ?_, fun hy => by rw [slotRefOf_congr hce]; exact h.2 hy⟩
  obtain ⟨h', hsl, hc⟩ := h.1 hy
  exact ⟨h', hsl, by rw [hce.2.1]; exact hc⟩

end Core

/-! ## Changing the slots of one object -/

section SetObj

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

end SetObj

/-! ## Unswizzle and release -/

section Evict

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

theorem PosOK.lv0 {S : Stream V T} (hp : PosOK S [] m) {z : NodeId} {h : Nat} {o : Obj V}
    (hz : m.canonicalOf z = some h) (ho : m.obj? h = some o) : o.pos = (S.lv z).map (·.recNo) := by
  rw [hp z h o hz ho, lv_building]; rfl

theorem EInv.canonicalOf_of (hm : EInv sp db S0 k m) {h : Nat} {o : Obj V} (ho : m.obj? h = some o)
    (hc : o.canonical = true) : m.canonicalOf o.node = some h :=
  (m.canonicalOf_eq_some o.node h).mpr ⟨hm.canonTbl h o ho hc, o, ho, hc⟩

theorem lookup_filter_self {β : Type} (l : List (Nat × β)) (h : Nat) :
    List.lookup h (l.filter (fun p => p.1 != h)) = none := by
  apply lookup_none_of_not_mem
  intro hm
  obtain ⟨p, hp, hph⟩ := List.mem_map.mp hm
  have := (List.mem_filter.mp hp).2
  rw [hph] at this
  simp at this

theorem lookup_filter_snd (l : List (NodeId × Nat)) (hnd : (l.map (·.1)).Nodup) (a : NodeId)
    (h : Nat) :
    List.lookup a (l.filter (fun p => p.2 != h)) =
      if List.lookup a l = some h then none else List.lookup a l := by
  induction l with
  | nil => rfl
  | cons q l ih =>
    obtain ⟨b, c⟩ := q
    simp only [List.map_cons, List.nodup_cons] at hnd
    rw [List.filter_cons, lookup_cons_eq]
    by_cases hab : a = b
    · subst hab
      have hl : List.lookup a l = none := lookup_none_of_not_mem hnd.1
      by_cases hc : c = h
      · subst hc
        simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        rw [ih hnd.2, hl]; simp
      · have : (c != h) = true := by simp [hc]
        simp only [this, ↓reduceIte, lookup_cons_eq, Option.some.injEq, hc]
    · simp only [hab, ↓reduceIte]
      split
      · rw [lookup_cons_eq]; simp only [hab, ↓reduceIte]; exact ih hnd.2
      · exact ih hnd.2

end Evict

end SIS
