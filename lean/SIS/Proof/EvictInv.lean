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

theorem Mem.slotRef_eq (S0 : Stream V T) (m : Mem V) (o : Obj V) (y : NodeId) :
    m.slotRef S0 o y = (o.slot? y).bind (slotRefOf S0 m y) := by
  unfold Mem.slotRef
  cases o.slot? y with
  | none => rfl
  | some sl => cases sl <;> rfl

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

theorem Mem.SameCore.coreEq (hs : m.SameCore m') (he : m'.s = m.s) : m.CoreEq m' :=
  ⟨hs.2, hs.canonicalOf, he⟩

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

/-- Changing the slots of one object, keeping its core, keeps the invariant if
the object's new slots are as the invariant asks (in the memory before, which
has the same cores). -/
theorem EInv.setObj_core (hm : EInv sp db S0 k m) {hp : Nat} {op op' : Obj V}
    (hop : m.obj? hp = some op) (hc : op'.core = op.core)
    (hnode : ∀ y h', op'.slot? y = some (Slot.mem h') → ∃ o', m.obj? h' = some o' ∧ o'.node = y)
    (hsnap : op.canonical = false → SnapExact sp S0 db m op')
    (hslots : Relevant sp db k op → ∀ y ∈ pointees sp op.hist,
      ∃ sl, op'.slot? y = some sl ∧ SlotInv S0 db m op y sl)
    (hlive : op.canonical = true → reachable sp db.P k op.node = true →
      ∀ y ∈ sp.live op.hist, ∃ sl, op'.slot? y = some sl ∧ LiveInv S0 db m y sl) :
    EInv sp db S0 k (m.setObj hp op') := by
  have hsc : m.SameCore (m.setObj hp op') := setObj_sameCore m hop hc
  have hce : m.CoreEq (m.setObj hp op') := hsc.coreEq rfl
  have e1 : op'.node = op.node := congrArg (fun c => c.1) hc
  have e4 : op'.hist = op.hist := congrArg (fun c => c.2.2.2.1) hc
  have e5 : op'.canonical = op.canonical := congrArg (fun c => c.2.2.2.2.1) hc
  have e2 : op'.level = op.level := congrArg (fun c => c.2.1) hc
  have e3 : op'.isData = op.isData := congrArg (fun c => c.2.2.1) hc
  have e6 : op'.pos = op.pos := congrArg (fun c => c.2.2.2.2.2) hc
  -- An object of m.setObj hp op': op' at hp, else m's.
  have hobj : ∀ h o, (m.setObj hp op').obj? h = some o →
      (h = hp ∧ o = op') ∨ (h ≠ hp ∧ m.obj? h = some o) := by
    intro h o ho
    rw [Mem.obj?_setObj] at ho
    split at ho
    · rename_i hh; exact Or.inl ⟨hh, (Option.some.injEq _ _ ▸ ho).symm⟩
    · rename_i hh; exact Or.inr ⟨hh, ho⟩
  have hrelop : Relevant sp db k op' ↔ Relevant sp db k op := by
    unfold Relevant; rw [e1, e5]
  refine ⟨hm.len, hm.pre, by rw [Mem.setObj_s]; exact hm.sEq, ?_, nodup_setObj_keys m hp op' hm.objNodup,
    ?_, hm.tblNodup, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h hh
    rw [Mem.setObj_next] at hh
    have hne : h ≠ hp := by
      intro he; subst he
      rw [hm.fresh h hh] at hop; cases hop
    rw [Mem.obj?_setObj_ne _ _ hne]; exact hm.fresh h hh
  · obtain ⟨o, ho, hc1, hn1⟩ := hm.root
    obtain ⟨o', ho', f1, -, -, -, f5, -⟩ := hsc.obj ho
    exact ⟨o', by rw [Mem.setObj_root]; exact ho', by rw [f5, hc1], by rw [f1, hn1]⟩
  · intro y h ht
    rw [hsc.tableOf] at ht
    obtain ⟨o, ho, hn⟩ := hm.tbl y h ht
    obtain ⟨o', ho', f1, -⟩ := hsc.obj ho
    exact ⟨o', ho', by rw [f1, hn]⟩
  · intro h o ho y h' hs
    rcases hobj h o ho with ⟨-, rfl⟩ | ⟨-, ho⟩
    · obtain ⟨o1, ho1, hn1⟩ := hnode y h' hs
      obtain ⟨o2, ho2, f1, -⟩ := hsc.obj ho1
      exact ⟨o2, ho2, by rw [f1, hn1]⟩
    · obtain ⟨o1, ho1, hn1⟩ := hm.slotsNode h o ho y h' hs
      obtain ⟨o2, ho2, f1, -⟩ := hsc.obj ho1
      exact ⟨o2, ho2, by rw [f1, hn1]⟩
  · intro y h ht
    rw [hsc.tableOf] at ht
    obtain ⟨o, ho, hc1⟩ := hm.tblCanon y h ht
    obtain ⟨o', ho', -, -, -, -, f5, -⟩ := hsc.obj ho
    exact ⟨o', ho', by rw [f5, hc1]⟩
  · intro h o ho hc1
    rw [hsc.tableOf]
    rcases hobj h o ho with ⟨rfl, rfl⟩ | ⟨-, ho⟩
    · rw [e1]; exact hm.canonTbl h op hop (by rw [← e5]; exact hc1)
    · exact hm.canonTbl h o ho hc1
  · intro h o ho hc1
    rcases hobj h o ho with ⟨rfl, rfl⟩ | ⟨-, ho⟩
    · obtain ⟨n, hn, h1, h2, h3⟩ := hm.cc h op hop (by rw [← e5]; exact hc1)
      exact ⟨n, by rw [e1]; exact hn, by rw [e4]; exact h1, by rw [e2]; exact h2, by rw [e3]; exact h3⟩
    · exact hm.cc h o ho hc1
  · intro z h o hz ho
    rw [hsc.canonicalOf] at hz
    rcases hobj h o ho with ⟨rfl, rfl⟩ | ⟨-, ho⟩
    · rw [e6]; exact hm.pos z h op hz hop
    · exact hm.pos z h o hz ho
  · intro y hy
    rw [hsc.canonicalOf]; exact hm.dCanon y hy
  · intro h o ho hc1
    rcases hobj h o ho with ⟨rfl, rfl⟩ | ⟨-, ho⟩
    · exact (hsnap (by rw [← e5]; exact hc1)).congr hce
    · exact (hm.snap h o ho hc1).congr hce
  · intro h o ho hr y hy
    rcases hobj h o ho with ⟨rfl, rfl⟩ | ⟨-, ho⟩
    · obtain ⟨sl, hsl, hinv⟩ := hslots (hrelop.mp hr) y (by rw [← e4]; exact hy)
      refine ⟨sl, hsl, ?_⟩
      have := hinv.congr hce
      unfold SlotInv at this ⊢
      rw [e1]; exact this
    · obtain ⟨sl, hsl, hinv⟩ := hm.slots h o ho hr y hy
      exact ⟨sl, hsl, hinv.congr hce⟩
  · intro h o ho hc1 hr y hy
    rcases hobj h o ho with ⟨rfl, rfl⟩ | ⟨-, ho⟩
    · obtain ⟨sl, hsl, hinv⟩ := hlive (by rw [← e5]; exact hc1) (by rw [← e1]; exact hr) y
        (by rw [← e4]; exact hy)
      exact ⟨sl, hsl, hinv.congr hce⟩
    · obtain ⟨sl, hsl, hinv⟩ := hm.live h o ho hc1 hr y hy
      exact ⟨sl, hsl, hinv.congr hce⟩

end SetObj

/-! ## Unswizzle and release -/

section Evict

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

theorem Mem.detachable_some {D : Dirty} {h : Nat} (hd : m.detachable D h = true) :
    ∃ o, m.obj? h = some o ∧ h ≠ m.root ∧ ¬ (o.canonical = true ∧ inD D o.node = true) ∧
      ∃ p, o.pos = some p := by
  unfold Mem.detachable at hd
  cases ho : m.obj? h with
  | none => rw [ho] at hd; cases hd
  | some o =>
    rw [ho] at hd
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hd
    obtain ⟨hpin, hpos⟩ := hd
    unfold Mem.pinned at hpin
    rw [ho] at hpin
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, Bool.and_eq_false_iff] at hpin
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hpos
    refine ⟨o, rfl, hpin.1, ?_, p, hp⟩
    rintro ⟨h1, h2⟩
    rcases hpin.2 with h3 | h3
    · rw [h1] at h3; cases h3
    · rw [h2] at h3; cases h3

theorem PosOK.lv0 {S : Stream V T} (hp : PosOK S [] m) {z : NodeId} {h : Nat} {o : Obj V}
    (hz : m.canonicalOf z = some h) (ho : m.obj? h = some o) : o.pos = (S.lv z).map (·.recNo) := by
  rw [hp z h o hz ho, lv_building]; rfl

theorem EInv.canonicalOf_of (hm : EInv sp db S0 k m) {h : Nat} {o : Obj V} (ho : m.obj? h = some o)
    (hc : o.canonical = true) : m.canonicalOf o.node = some h :=
  (m.canonicalOf_eq_some o.node h).mpr ⟨hm.canonTbl h o ho hc, o, ho, hc⟩

theorem EInv.obj_of_canonicalOf (hm : EInv sp db S0 k m) {y : NodeId} {h : Nat}
    (hc : m.canonicalOf y = some h) : ∃ o, m.obj? h = some o ∧ o.canonical = true ∧ o.node = y := by
  obtain ⟨ht, o, ho, hco⟩ := (m.canonicalOf_eq_some y h).mp hc
  obtain ⟨o', ho', hn⟩ := hm.tbl y h ht
  rw [ho, Option.some.injEq] at ho'
  subst ho'
  exact ⟨o, ho, hco, hn⟩

/-- Unswizzling keeps the invariant: the slot names the position of the object
it named, which serializes as before (Rule R of a prefix leaves the latest
version), and a snapshot's slot still names a version at least as new. -/
theorem EInv.unswizzle (hinv : Inv sp db k) (hm : EInv sp db S0 k m) (hp : Nat) (y : NodeId) :
    EInv sp db S0 k (m.unswizzle db.D hp y) := by
  unfold Mem.unswizzle
  cases hop : m.obj? hp with
  | none => exact hm
  | some op =>
    simp only
    cases hsl : op.slot? y with
    | none => exact hm
    | some sl =>
      cases sl with
      | stream r => exact hm
      | mem h =>
        simp only
        cases ho : m.obj? h with
        | none => exact hm
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
            -- What the new slot names.
            have hslot' : ∀ z, (op.setSlot y (Slot.stream (some p))).slot? z =
                if z = y then some (Slot.stream (some p)) else op.slot? z := by
              intro z
              rw [Obj.slot?_setSlot]
              split
              · rename_i hz; subst hz; rw [hsl]; rfl
              · rfl
            -- The object named: y's canonical object, not pinned so y is not in D, at
            -- y's latest version; or a snapshot, at an exact version.
            have hval : (inD db.D y = true → ¬ ∃ h', h = h' ∧ m.canonicalOf y = some h') := by
              rintro hyD ⟨h', rfl, hc⟩
              obtain ⟨o2, ho2, hc2, -⟩ := hm.obj_of_canonicalOf hc
              rw [ho, Option.some.injEq] at ho2
              subst ho2
              exact hnp ⟨hc2, by rw [hny]; exact hyD⟩
            have hlvp : inD db.D y = false → (db.S.lv y).map (·.recNo) = some p →
                ruleRRef S0 m.s y (some p) = some p := by
              intro _ hl
              rw [← hl]; exact hinv.ruleR_lv0 hm.pre m.s y
            have hver : ∃ u, db.S.versionAt p y = some u := by
              cases hco : o.canonical with
              | true =>
                have hcy := hm.canonicalOf_of ho hco
                rw [hny] at hcy
                have := hm.pos.lv0 hcy ho
                rw [hpos] at this
                cases hl : db.S.lv y with
                | none => rw [hl] at this; cases this
                | some v =>
                  rw [hl] at this
                  simp only [Option.map_some, Option.some.injEq] at this
                  rw [this]; exact ⟨v, hinv.lv_at hl⟩
              | false =>
                obtain ⟨r1, w1, h1, h2, -⟩ := hm.snap h o ho hco
                rw [hpos, Option.some.injEq] at h1
                subst h1
                rw [hny] at h2
                exact ⟨w1, h2⟩
            apply hm.setObj_core hop (setSlot_core op y _)
            · intro z h' hz
              rw [hslot' z] at hz
              split at hz
              · cases hz
              · exact hm.slotsNode hp op hop z h' hz
            · intro hco
              obtain ⟨r, w, h1, h2, h3, h4, h5, h6, h7⟩ := hm.snap hp op hop hco
              refine ⟨r, w, h1, h2, h3, h4, h5, fun z hz => ?_, fun z sl hz => ?_⟩
              · rw [hslot' z]; split
                · rfl
                · exact h6 z hz
              · rw [hslot' z] at hz
                split at hz
                · rename_i hzy
                  subst hzy
                  simp only [Option.some.injEq] at hz
                  subst hz
                  -- The old slot named an object at least as new.
                  have hold := h7 z (Slot.mem h) hsl
                  obtain ⟨u, hu⟩ := hver
                  refine Or.inr (Or.inl ⟨p, u, rfl, hu, fun r0 hr0 => ?_⟩)
                  rcases hold with hold | ⟨p1, u1, hold, -⟩ | ⟨h', o', hold, ho', -, hc'⟩
                  · cases hold
                  · cases hold
                  · simp only [Slot.mem.injEq] at hold
                    subst hold
                    rw [ho, Option.some.injEq] at ho'
                    subst ho'
                    rcases hc' with hc' | ⟨p', hp', hle⟩
                    · -- y's canonical object, at y's latest version
                      have hcy := hm.canonicalOf_of ho hc'
                      rw [hny] at hcy
                      have hpl := hm.pos.lv0 hcy ho
                      rw [hpos] at hpl
                      obtain ⟨-, v, hv, hle⟩ := hinv.ruleR_bound hm.pre m.s
                        (fun r' hr' => hinv.ref_versionAt h2 hr') hr0
                      rw [hv] at hpl
                      simp only [Option.map_some, Option.some.injEq] at hpl
                      omega
                    · rw [hpos, Option.some.injEq] at hp'
                      subst hp'
                      exact hle r0 hr0
                · exact h7 z sl hz
            · intro hrel z hz
              obtain ⟨sl, hsl1, hinv1⟩ := hm.slots hp op hop hrel z hz
              rw [hslot' z]
              split
              · rename_i hzy
                subst hzy
                rw [hsl, Option.some.injEq] at hsl1
                subst hsl1
                refine ⟨_, rfl, fun hyD => ?_, fun hyD => ?_⟩
                · have h1 := hinv1.1 hyD
                  simp only [slotRefOf, ho, Option.bind_some, hpos] at h1
                  simp only [slotRefOf]
                  rw [hlvp hyD h1.symm, h1]
                · rcases hinv1.2 hyD with ⟨h', hh', hc⟩ | h2
                  · simp only [Slot.mem.injEq] at hh'
                    exact absurd ⟨h', hh', hc⟩ (hval hyD)
                  · exact Or.inr h2
              · exact ⟨sl, hsl1, hinv1⟩
            · intro hco hr z hz
              obtain ⟨sl, hsl1, hinv1⟩ := hm.live hp op hop hco hr z hz
              rw [hslot' z]
              split
              · rename_i hzy
                subst hzy
                rw [hsl, Option.some.injEq] at hsl1
                subst hsl1
                refine ⟨_, rfl, fun hyD => ?_, fun hyD => ?_⟩
                · obtain ⟨h', hh', hc⟩ := hinv1.1 hyD
                  simp only [Slot.mem.injEq] at hh'
                  exact absurd ⟨h', hh', hc⟩ (hval hyD)
                · have h1 := hinv1.2 hyD
                  simp only [slotRefOf, ho, Option.bind_some, hpos] at h1
                  simp only [slotRefOf]
                  rw [hlvp hyD h1.symm, h1]
              · exact ⟨sl, hsl1, hinv1⟩
          · exact hm

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

theorem Mem.incoming_false {h : Nat} (hi : m.incoming h = false) {h2 : Nat} {o2 : Obj V}
    (ho2 : m.obj? h2 = some o2) {z : NodeId} {h' : Nat} (hz : o2.slot? z = some (Slot.mem h')) :
    h' ≠ h := by
  intro he
  subst he
  unfold Mem.incoming at hi
  have hm1 := mem_of_lookup _ _ _ ho2
  have hm2 := mem_of_lookup _ _ _ hz
  have : m.objs.any (fun p => p.2.slots.any (fun q => q.2 == Slot.mem h')) = true :=
    List.any_eq_true.mpr ⟨(h2, o2), hm1, List.any_eq_true.mpr ⟨(z, Slot.mem h'), hm2, by simp⟩⟩
  rw [hi] at this; cases this

theorem release_obj? (D : Dirty) {h : Nat} (he : m.eligible D h = true) (h' : Nat) :
    (m.release D h).obj? h' = if h' = h then none else m.obj? h' := by
  unfold Mem.release Mem.obj?
  simp only [he, ↓reduceIte]
  split
  · rename_i hh; subst hh; exact lookup_filter_self _ _
  · rename_i hh; exact lookup_filter_ne h h' m.objs hh

theorem release_tableOf (hnd : (m.table.map (·.1)).Nodup) (D : Dirty) {h : Nat}
    (he : m.eligible D h = true) (y : NodeId) :
    (m.release D h).tableOf y = if m.tableOf y = some h then none else m.tableOf y := by
  unfold Mem.release Mem.tableOf
  simp only [he, ↓reduceIte]
  exact lookup_filter_snd _ hnd y h

theorem release_canonicalOf (hnd : (m.table.map (·.1)).Nodup) (D : Dirty) {h : Nat}
    (he : m.eligible D h = true) (y : NodeId) :
    (m.release D h).canonicalOf y = if m.canonicalOf y = some h then none else m.canonicalOf y := by
  unfold Mem.canonicalOf
  rw [release_tableOf hnd D he y]
  cases ht : m.tableOf y with
  | none => simp
  | some h1 =>
    by_cases h1h : h1 = h
    · subst h1h
      simp only [↓reduceIte]
      cases m.obj? h1 with
      | none => simp
      | some o => cases o.canonical <;> simp
    · have : (some h1 = some h) = False := by simp [h1h]
      simp only [Option.some.injEq, h1h, ↓reduceIte]
      rw [release_obj? D he h1]
      simp only [h1h, ↓reduceIte]
      cases ho : m.obj? h1 with
      | none => simp
      | some o =>
        cases hc : o.canonical
        · simp [hc]
        · simp [h1h]

/-- Release keeps the invariant: an eligible object is not pinned, and no memory
slot names it, so every slot serializes as before. -/
theorem EInv.release (hm : EInv sp db S0 k m) (h : Nat) : EInv sp db S0 k (m.release db.D h) := by
  cases he : m.eligible db.D h with
  | false =>
    have : m.release db.D h = m := by unfold Mem.release; simp [he]
    rw [this]; exact hm
  | true =>
  have hdet : m.detachable db.D h = true := by
    unfold Mem.eligible at he; simp only [Bool.and_eq_true] at he; exact he.1
  have hinc : m.incoming h = false := by
    unfold Mem.eligible at he; simp only [Bool.and_eq_true, Bool.not_eq_true'] at he; exact he.2
  obtain ⟨o, ho, hroot, hnp, -⟩ := Mem.detachable_some hdet
  have hobj := release_obj? db.D he
  have hcan := release_canonicalOf hm.tblNodup db.D he
  have hts := release_tableOf hm.tblNodup db.D he
  have hs' : (m.release db.D h).s = m.s := by unfold Mem.release; simp only [he, ↓reduceIte]
  -- The objects that stay, and what their memory slots name.
  have hstay : ∀ h2 o2, (m.release db.D h).obj? h2 = some o2 → h2 ≠ h ∧ m.obj? h2 = some o2 := by
    intro h2 o2 ho2
    rw [hobj h2] at ho2
    split at ho2
    · cases ho2
    · rename_i hne; exact ⟨hne, ho2⟩
  have hsame : ∀ h', h' ≠ h → (m.release db.D h).obj? h' = m.obj? h' := by
    intro h' hne; rw [hobj h']; simp only [hne, ↓reduceIte]
  -- A canonical object of a node in D is pinned, so it stays.
  have hcanD : ∀ y h1, inD db.D y = true → m.canonicalOf y = some h1 → h1 ≠ h := by
    intro y h1 hy hc he1
    subst he1
    obtain ⟨o1, ho1, hc1, hn1⟩ := hm.obj_of_canonicalOf hc
    rw [ho, Option.some.injEq] at ho1
    subst ho1
    exact hnp ⟨hc1, by rw [hn1]; exact hy⟩
  have hcanS : ∀ y h1, m.canonicalOf y = some h1 → h1 ≠ h →
      (m.release db.D h).canonicalOf y = some h1 := by
    intro y h1 hc hne
    rw [hcan y, hc]
    simp [hne]
  have hslotRef : ∀ h2 o2, m.obj? h2 = some o2 → ∀ z sl, o2.slot? z = some sl →
      slotRefOf S0 (m.release db.D h) z sl = slotRefOf S0 m z sl := by
    intro h2 o2 ho2 z sl hz
    cases sl with
    | mem h' =>
      have hne := Mem.incoming_false hinc ho2 hz
      simp only [slotRefOf]
      rw [hsame h' hne]
    | stream r => simp only [slotRefOf, hs']
  have hsnapSlot : ∀ h2 o2, m.obj? h2 = some o2 → ∀ w z sl, o2.slot? z = some sl →
      SnapSlot S0 db m w z sl → SnapSlot S0 db (m.release db.D h) w z sl := by
    intro h2 o2 ho2 w z sl hz hs
    unfold SnapSlot at hs ⊢
    rw [hs']
    rcases hs with hs | hs | ⟨h', o', hsl, ho', hn, hc⟩
    · exact Or.inl hs
    · exact Or.inr (Or.inl hs)
    · subst hsl
      have hne := Mem.incoming_false hinc ho2 hz
      exact Or.inr (Or.inr ⟨h', o', rfl, by rw [hsame h' hne]; exact ho', hn, hc⟩)
  have hrelS : ∀ h2 o2, m.obj? h2 = some o2 → ∀ z sl, o2.slot? z = some sl →
      SlotInv S0 db m o2 z sl → SlotInv S0 db (m.release db.D h) o2 z sl := by
    intro h2 o2 ho2 z sl hz hs
    refine ⟨fun hzD => by rw [hslotRef h2 o2 ho2 z sl hz]; exact hs.1 hzD, fun hzD => ?_⟩
    rcases hs.2 hzD with ⟨h', hsl, hc⟩ | h3
    · subst hsl
      exact Or.inl ⟨h', rfl, hcanS z h' hc (Mem.incoming_false hinc ho2 hz)⟩
    · exact Or.inr h3
  have hliveS : ∀ h2 o2, m.obj? h2 = some o2 → ∀ z sl, o2.slot? z = some sl →
      LiveInv S0 db m z sl → LiveInv S0 db (m.release db.D h) z sl := by
    intro h2 o2 ho2 z sl hz hs
    refine ⟨fun hzD => ?_, fun hzD => by rw [hslotRef h2 o2 ho2 z sl hz]; exact hs.2 hzD⟩
    obtain ⟨h', hsl, hc⟩ := hs.1 hzD
    subst hsl
    exact ⟨h', rfl, hcanS z h' hc (Mem.incoming_false hinc ho2 hz)⟩
  have hroot' : (m.release db.D h).root = m.root := by unfold Mem.release; simp only [he, ↓reduceIte]
  have hnext' : (m.release db.D h).next = m.next := by unfold Mem.release; simp only [he, ↓reduceIte]
  refine ⟨hm.len, hm.pre, by rw [hs']; exact hm.sEq, ?_,
    (by unfold Mem.release; simp only [he, ↓reduceIte]
        exact (List.Sublist.map _ List.filter_sublist).nodup hm.objNodup),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h2 hh
    rw [hnext'] at hh
    rw [hobj h2]; split
    · rfl
    · exact hm.fresh h2 hh
  · obtain ⟨o1, ho1, hc1, hn1⟩ := hm.root
    exact ⟨o1, by rw [hroot', hsame _ (Ne.symm hroot)]; exact ho1, hc1, hn1⟩
  · unfold Mem.release; simp only [he, ↓reduceIte]
    exact (List.Sublist.map _ List.filter_sublist).nodup hm.tblNodup
  · intro y h1 ht
    rw [hts y] at ht
    split at ht
    · cases ht
    · rename_i hne
      obtain ⟨o1, ho1, hn1⟩ := hm.tbl y h1 ht
      have : h1 ≠ h := by intro e; subst e; exact hne ht
      exact ⟨o1, by rw [hsame h1 this]; exact ho1, hn1⟩
  · intro h2 o2 ho2 z h' hz
    obtain ⟨hne, ho2⟩ := hstay h2 o2 ho2
    obtain ⟨o3, ho3, hn3⟩ := hm.slotsNode h2 o2 ho2 z h' hz
    exact ⟨o3, by rw [hsame h' (Mem.incoming_false hinc ho2 hz)]; exact ho3, hn3⟩
  · intro y h1 ht
    rw [hts y] at ht
    split at ht
    · cases ht
    · rename_i hne
      obtain ⟨o1, ho1, hc1⟩ := hm.tblCanon y h1 ht
      have : h1 ≠ h := by intro e; subst e; exact hne ht
      exact ⟨o1, by rw [hsame h1 this]; exact ho1, hc1⟩
  · intro h2 o2 ho2 hc2
    obtain ⟨hne, ho2⟩ := hstay h2 o2 ho2
    rw [hts, hm.canonTbl h2 o2 ho2 hc2]
    simp [hne]
  · intro h2 o2 ho2 hc2
    exact hm.cc h2 o2 (hstay h2 o2 ho2).2 hc2
  · intro z h1 o1 hz ho1
    obtain ⟨hne, ho1⟩ := hstay h1 o1 ho1
    rw [hcan z] at hz
    split at hz
    · cases hz
    · exact hm.pos z h1 o1 hz ho1
  · intro y hy
    obtain ⟨h1, hc⟩ := Option.isSome_iff_exists.mp (hm.dCanon y hy)
    rw [hcanS y h1 hc (hcanD y h1 hy hc)]; rfl
  · intro h2 o2 ho2 hc2
    obtain ⟨-, ho2⟩ := hstay h2 o2 ho2
    obtain ⟨r, w, h1, h2', h3, h4, h5, h6, h7⟩ := hm.snap h2 o2 ho2 hc2
    exact ⟨r, w, h1, h2', h3, h4, h5, h6, fun z sl hz => hsnapSlot h2 o2 ho2 w z sl hz (h7 z sl hz)⟩
  · intro h2 o2 ho2 hr z hz
    obtain ⟨-, ho2⟩ := hstay h2 o2 ho2
    obtain ⟨sl, hsl, hs⟩ := hm.slots h2 o2 ho2 hr z hz
    exact ⟨sl, hsl, hrelS h2 o2 ho2 z sl hsl hs⟩
  · intro h2 o2 ho2 hc2 hr z hz
    obtain ⟨-, ho2⟩ := hstay h2 o2 ho2
    obtain ⟨sl, hsl, hs⟩ := hm.live h2 o2 ho2 hc2 hr z hz
    exact ⟨sl, hsl, hliveS h2 o2 ho2 z sl hsl hs⟩

end Evict

end SIS
