/-
Proofs about reclaim, part 16 (bergdb item 001, WP R5, T12 with eviction): an
invariant on the slots for the states after a restart (`NInv`). Every slot of
a canonical object names a canonical object, or a record that is its
pointee's latest version in the stream of the last startup (S0), or one
written after S0; every slot of a snapshot does so too, or names what the
snapshot's version's reference names after Rule R. The startup gives it, and
the cache operations and the transactions keep it. A read from the first
available time on then follows only versions that the state of the last
startup may read, or versions written after it.
-/
import SIS.Proof.CutPhysRun

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## The invariant -/

/-- Record r of node y is y's latest version in S0, or a record after S0. -/
def VOK (S0 : Stream V T) (y : NodeId) (r : Nat) : Prop :=
  (S0.lv y).map (·.recNo) = some r ∨ S0.length ≤ r

/-- Slot sl for y names a canonical object, or (`slotRefOf`) a record that
`VOK` allows. -/
def SlotVOK (S0 : Stream V T) (m : Mem V) (y : NodeId) (sl : Slot) : Prop :=
  (∃ h' o', sl = Slot.mem h' ∧ m.obj? h' = some o' ∧ o'.canonical = true) ∨
    ∀ r, slotRefOf S0 m y sl = some r → VOK S0 y r

/-- Slot sl for y names (`slotRefOf`) what version v's reference for y names
after Rule R of the last startup. -/
def SlotOwn (S0 : Stream V T) (m : Mem V) (v : Version V) (y : NodeId) (sl : Slot) : Prop :=
  ∀ r, slotRefOf S0 m y sl = some r → ruleRRef S0 m.s y (v.ref? y) = some r

/-- The invariant on the slots after a restart from S0, for state db. -/
structure NInv (db : DB V T) (S0 : Stream V T) (m : Mem V) : Prop where
  canon : ∀ h o, m.obj? h = some o → o.canonical = true → ∀ y sl, o.slot? y = some sl →
    SlotVOK S0 m y sl
  snap : ∀ h o, m.obj? h = some o → o.canonical = false → ∀ r v, o.pos = some r →
    db.S.versionAt r o.node = some v → ∀ y sl, o.slot? y = some sl →
      SlotVOK S0 m y sl ∨ SlotOwn S0 m v y sl

/-! ## Basic facts -/

section Basic

variable {S0 : Stream V T} {m m' : Mem V}

theorem SlotVOK.keep (hk : m.KeepCore m') (hs : m'.s = m.s) {y : NodeId} {sl : Slot}
    (ha : SlotVOK S0 m y sl) (hsl : ∀ h', sl = Slot.mem h' → (m.obj? h').isSome) :
    SlotVOK S0 m' y sl := by
  rcases ha with ⟨h', o', he, ho', hc'⟩ | ha
  · obtain ⟨o'', ho'', hcore⟩ := hk h' o' ho'
    have e5 : o''.canonical = o'.canonical := congrArg (fun c => c.2.2.2.2.1) hcore
    exact Or.inl ⟨h', o'', he, ho'', by rw [e5, hc']⟩
  · exact Or.inr (fun r hr => ha r (by rw [← slotRefOf_keep hk hs hsl]; exact hr))

theorem SlotOwn.keep (hk : m.KeepCore m') (hs : m'.s = m.s) {v : Version V} {y : NodeId}
    {sl : Slot} (ha : SlotOwn S0 m v y sl) (hsl : ∀ h', sl = Slot.mem h' → (m.obj? h').isSome) :
    SlotOwn S0 m' v y sl := by
  intro r hr
  rw [hs]
  exact ha r (by rw [← slotRefOf_keep hk hs hsl]; exact hr)

/-- Rule R of the stream's section takes nothing to y's latest version. -/
theorem ruleRRef_none_VOK {s : Nat} {y : NodeId} {r : Nat} (h : ruleRRef S0 s y none = some r) :
    VOK S0 y r := by
  unfold ruleRRef at h
  cases hn : newest S0 s y with
  | none => rw [hn] at h; cases h
  | some w =>
    rw [hn] at h
    simp only [Option.some.injEq] at h
    subst h
    left
    rw [newest_lv hn]
    rfl

end Basic

section Stream

variable {sp : Spec V T} {db : DB V T} {k : Nat} {S0 : Stream V T}

theorem versionAt_lt_length {S : Stream V T} {r : Nat} {y : NodeId} {w : Version V}
    (h : S.versionAt r y = some w) : r < S.length := by
  obtain ⟨R, hR, -, -⟩ := versionAt_spec h
  exact (List.getElem?_eq_some_iff.mp hR).1

/-- Rule R of S0's section leaves a record that `VOK` allows as it is (S0 a
prefix of the stream of a state with the invariant). -/
theorem Inv.ruleRRef_VOK (hinv : Inv sp db k) (hpre : S0 <+: db.S) (s : Nat) {y : NodeId} {r : Nat}
    (h : VOK S0 y r) : ruleRRef S0 s y (some r) = some r := by
  unfold ruleRRef
  cases hn : newest S0 s y with
  | none => rfl
  | some u =>
    simp only
    have hlv := newest_lv hn
    have hlt : ¬ r < u.recNo := by
      intro hlt
      rcases h with h | h
      · rw [hlv, Option.map_some, Option.some.injEq] at h; omega
      · obtain ⟨r0, -, hr0⟩ := newest_some hn
        have h1 := versionAt_lt_length hr0
        have h2 := (hinv.version_node (versionAt_prefix hpre hr0)).2.1
        omega
    simp [hlt]

/-- A node's latest version in a state with S0 as a prefix of its stream: its
latest version in S0, or one after S0. -/
theorem Inv.VOK_lv (hinv : Inv sp db k) (hpre : S0 <+: db.S) {y : NodeId} {u : Version V}
    (hu : db.S.lv y = some u) : VOK S0 y u.recNo := by
  by_cases hlt : u.recNo < S0.length
  · left
    have htake : S0 = db.S.take S0.length := List.prefix_iff_eq_take.mp hpre
    have hnone : ∀ r', S0.length ≤ r' → db.S.versionAt r' y = none := by
      intro r' hr'
      obtain ⟨r0, hr0, hlast⟩ := (lv_eq_some_iff db.S y u).mp hu
      have := (hinv.version_node hr0).2.1
      exact hlast r' (by omega)
    rw [htake, lv_take hnone, hu]
    rfl
  · right; omega

end Stream

/-! ## The startup and the cache operations -/

section Startup

variable {sp : Spec V T} {al : Algo V T}

/-- The Level 4 startup from the stream after T(k) gives the invariant: every
object is canonical, and every slot names its pointee's latest version. -/
theorem ninv_startup {ts : List T} (hok : RunOK sp al ts) (hph : PhysRunOK sp al ts)
    (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) (hev : EvictRunOK sp al ts) {k : Nat}
    (hk : k ≤ ts.length) :
    NInv (st sp al ts k) (st sp al ts k).S (evictStartup sp (st sp al ts k).S) := by
  obtain ⟨-, -, hcan, hser, -, -⟩ := einv_hinv_startup_facts hok hph hj hmk hev hk
  constructor
  · intro h o ho _ y sl hsl
    right
    intro r hr
    rw [hser h o y sl ho hsl] at hr
    exact Or.inl hr
  · intro h o ho hco
    rw [hcan h o ho] at hco; cases hco

end Startup

section Cache

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

/-- The reader's follow keeps the invariant: the slot then names what it
named, or the canonical object; a new snapshot's slots name what its
version's references name. -/
theorem NInv.reached4 (hinv : Inv sp db k) (hm : EInv sp db S0 k m) (hn : NInv db S0 m)
    {hp : Nat} {y : NodeId} {m1 : Mem V} {h1 : Nat} (h : m.reached4 sp S0 db.S hp y = some (m1, h1)) :
    NInv db S0 (m1.swz hp y h1) := by
  obtain ⟨op, sl, hop, hsl, hcase⟩ := reached4_cases h
  have hk := hm.reached4_keepCore h
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
  -- The slot for y after names the canonical object, or what the slot named.
  have hnew : (∃ o', (m1.swz hp y h1).obj? h1 = some o' ∧ o'.canonical = true) ∨
      (sl = Slot.mem h1) ∨
      ((∃ r0, sl = Slot.stream r0) ∧
        ∀ r, slotRefOf S0 (m1.swz hp y h1) y (Slot.mem h1) = some r → slotRefOf S0 m y sl = some r) := by
    rcases hcase with ⟨rfl, rfl, -⟩ | ⟨r, rfl, hcy, rfl⟩ | ⟨r, r', w, rfl, hcy, hr, hw, rfl, rfl⟩
    · exact Or.inr (Or.inl rfl)
    · obtain ⟨o0, ho0, hc0, -⟩ := hm.obj_of_canonicalOf hcy
      obtain ⟨o0', ho0', hcore⟩ := hk h1 o0 ho0
      have e5 : o0'.canonical = o0.canonical := congrArg (fun c => c.2.2.2.2.1) hcore
      exact Or.inl ⟨o0', ho0', by rw [e5, hc0]⟩
    · right; right
      refine ⟨⟨r, rfl⟩, ?_⟩
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
      intro r1 hr1
      simp only [slotRefOf, hobj, Option.bind_some, f6, hwr] at hr1
      simp only [slotRefOf]
      rw [hr]; exact hr1
  have hV : SlotVOK S0 m y sl → SlotVOK S0 (m1.swz hp y h1) y (Slot.mem h1) := by
    intro ha
    rcases hnew with ⟨o', ho', hc'⟩ | he | hsame
    · exact Or.inl ⟨h1, o', rfl, ho', hc'⟩
    · subst he; exact ha.keep hk hs (hold hp op y _ hop hsl)
    · obtain ⟨⟨r0, hr0⟩, hsame⟩ := hsame
      rcases ha with ⟨h', o', he, -, -⟩ | ha
      · rw [hr0] at he; cases he
      · exact Or.inr (fun r hr => ha r (hsame r hr))
  have hO : ∀ v, SlotOwn S0 m v y sl →
      SlotVOK S0 (m1.swz hp y h1) y (Slot.mem h1) ∨ SlotOwn S0 (m1.swz hp y h1) v y (Slot.mem h1) := by
    intro v ha
    rcases hnew with ⟨o', ho', hc'⟩ | he | hsame
    · exact Or.inl (Or.inl ⟨h1, o', rfl, ho', hc'⟩)
    · subst he; exact Or.inr (ha.keep hk hs (hold hp op y _ hop hsl))
    · exact Or.inr (fun r hr => by rw [hs]; exact ha r (hsame.2 r hr))
  constructor
  · -- canonical objects
    intro h' o' ho' hco z sl' hsl'
    rcases reached4_back hm h hop ho' with ⟨rfl, rfl⟩ | ⟨-, h2⟩ | ⟨-, -, h3⟩
    · have hco0 : op.canonical = true := hco
      by_cases hzy : z = y
      · subst hzy
        rw [slot?_setSlot_of hsl] at hsl'
        simp only [↓reduceIte, Option.some.injEq] at hsl'
        subst hsl'
        exact hV (hn.canon h' op hop hco0 z sl hsl)
      · rw [slot?_setSlot_of hsl] at hsl'
        simp only [hzy, ↓reduceIte] at hsl'
        exact (hn.canon h' op hop hco0 z sl' hsl').keep hk hs (hold h' op z sl' hop hsl')
    · exact (hn.canon h' o' h2 hco z sl' hsl').keep hk hs (hold h' o' z sl' h2 hsl')
    · rw [hco] at h3; cases h3
  · -- snapshots
    intro h' o' ho' hco r v hp' hv z sl' hsl'
    rcases reached4_back hm h hop ho' with ⟨rfl, rfl⟩ | ⟨-, h2⟩ | ⟨hne, hnx, -⟩
    · have hco0 : op.canonical = false := hco
      have hv0 : db.S.versionAt r op.node = some v := hv
      by_cases hzy : z = y
      · subst hzy
        rw [slot?_setSlot_of hsl] at hsl'
        simp only [↓reduceIte, Option.some.injEq] at hsl'
        subst hsl'
        rcases hn.snap h' op hop hco0 r v hp' hv0 z sl hsl with ha | ha
        · exact Or.inl (hV ha)
        · exact hO v ha
      · rw [slot?_setSlot_of hsl] at hsl'
        simp only [hzy, ↓reduceIte] at hsl'
        rcases hn.snap h' op hop hco0 r v hp' hv0 z sl' hsl' with ha | ha
        · exact Or.inl (ha.keep hk hs (hold h' op z sl' hop hsl'))
        · exact Or.inr (ha.keep hk hs (hold h' op z sl' hop hsl'))
    · rcases hn.snap h' o' h2 hco r v hp' hv z sl' hsl' with ha | ha
      · exact Or.inl (ha.keep hk hs (hold h' o' z sl' h2 hsl'))
      · exact Or.inr (ha.keep hk hs (hold h' o' z sl' h2 hsl'))
    · -- the new snapshot: its slots are its version's references
      right
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
        obtain ⟨f1, -, -, -, -, f6⟩ := Obj.ofVersion_fields sp w none
        obtain ⟨hwn, hwr, -⟩ := hinv.version_node hw
        rw [f6, Option.some.injEq] at hp'
        subst hp'
        rw [f1, hwn, hwr, hw, Option.some.injEq] at hv
        subst hv
        rw [Obj.ofVersion_slot?] at hsl'
        split at hsl'
        · simp only [Option.some.injEq] at hsl'
          subst hsl'
          intro r1 hr1
          simp only [slotRefOf] at hr1
          exact hr1
        · cases hsl'

theorem NInv.follow4_reader (hinv : Inv sp db k) (hm : EInv sp db S0 k m) (hn : NInv db S0 m)
    (hp : Nat) (y : NodeId) : NInv db S0 (m.follow4 sp S0 db.S hp y false).1 := by
  rw [follow4_eq]
  cases h : m.reached4 sp S0 db.S hp y with
  | none => exact hn
  | some p =>
    obtain ⟨m1, h1⟩ := p
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact hn.reached4 hinv hm h

/-- A read at any time, from any object, keeps the invariant. -/
theorem NInv.readAt4 (hinv : Inv sp db k) :
    ∀ (fuel : Nat) (m : Mem V) (t : Time) (h : Nat), EInv sp db S0 k m → NInv db S0 m →
      EInv sp db S0 k (m.readAt4 sp S0 db.S fuel t h).1 ∧ NInv db S0 (m.readAt4 sp S0 db.S fuel t h).1 := by
  intro fuel
  induction fuel with
  | zero => intro m t h hm hn; exact ⟨hm, hn⟩
  | succ fuel ih =>
    intro m t h hm hn
    unfold Mem.readAt4
    cases ho : m.obj? h with
    | none => exact ⟨hm, hn⟩
    | some o =>
      simp only
      apply foldl_inv1 _ (fun m => EInv sp db S0 k m ∧ NInv db S0 m) _ _ _ ⟨hm, hn⟩
      intro acc z ⟨hacc, hnacc⟩
      have hf := hacc.follow4_reader hinv h z
      have hfn := hnacc.follow4_reader hinv hacc h z
      generalize acc.1.follow4 sp S0 db.S h z false = res at hf hfn ⊢
      obtain ⟨m1, oh⟩ := res
      cases oh with
      | none => exact ⟨hf, hfn⟩
      | some h1 =>
        simp only
        cases ho1 : m1.obj? h1 with
        | none => exact ⟨hf, hfn⟩
        | some o1 =>
          simp only
          split
          · exact ih m1 t h1 hf hfn
          · exact ⟨hf, hfn⟩

theorem NInv.read4 (hinv : Inv sp db k) (hm : EInv sp db S0 k m) (hn : NInv db S0 m) (t : Time) :
    NInv db S0 (m.read4 sp S0 db.S t).1 := by
  unfold Mem.read4
  cases m.obj? m.root with
  | none => exact hn
  | some o => exact (NInv.readAt4 hinv _ m t _ hm hn).2


/-- Unswizzling keeps the invariant: the stream slot names the object's
position, which is the latest version for a canonical object, and Rule R
leaves it so. -/
theorem NInv.unswizzle (hinv : Inv sp db k) (hm : EInv sp db S0 k m) (hn : NInv db S0 m)
    (hp : Nat) (y : NodeId) : NInv db S0 (m.unswizzle db.D hp y) := by
  unfold Mem.unswizzle
  cases hop : m.obj? hp with
  | none => exact hn
  | some op =>
    simp only
    cases hsl : op.slot? y with
    | none => exact hn
    | some sl =>
      cases sl with
      | stream r => exact hn
      | mem h =>
        simp only
        cases ho : m.obj? h with
        | none => exact hn
        | some o =>
          simp only
          split
          · rename_i hdet
            obtain ⟨o0, ho0, -, -, p, hpos⟩ := Mem.detachable_some hdet
            rw [ho, Option.some.injEq] at ho0
            subst ho0
            obtain ⟨o1, ho1, hny⟩ := hm.slotsNode hp op hop y h hsl
            rw [ho, Option.some.injEq] at ho1
            subst ho1
            rw [hpos]
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
            have hslot' : ∀ z, (op.setSlot y (Slot.stream (some p))).slot? z =
                if z = y then some (Slot.stream (some p)) else op.slot? z := by
              intro z
              rw [Obj.slot?_setSlot]
              split
              · rename_i hz; subst hz; rw [hsl]; rfl
              · rfl
            have hold : ∀ h0 o0 z sl0, m.obj? h0 = some o0 → o0.slot? z = some sl0 →
                ∀ h', sl0 = Slot.mem h' → (m.obj? h').isSome := by
              intro h0 o0 z sl0 ho0 hsl0 h' he
              subst he
              obtain ⟨o', ho', -⟩ := hm.slotsNode h0 o0 ho0 z h' hsl0
              rw [ho']; rfl
            have hback : ∀ h'' o'', m'.obj? h'' = some o'' →
                (h'' = hp ∧ o'' = op.setSlot y (Slot.stream (some p))) ∨ (h'' ≠ hp ∧ m.obj? h'' = some o'') := by
              intro h'' o'' ho''
              rw [hobj h''] at ho''
              split at ho''
              · rename_i he; exact Or.inl ⟨he, (Option.some.inj ho'').symm⟩
              · rename_i he; exact Or.inr ⟨he, ho''⟩
            -- The new slot names the object's position, after Rule R.
            have hnewV : SlotVOK S0 m y (Slot.mem h) → SlotVOK S0 m' y (Slot.stream (some p)) := by
              intro ha
              right
              have hVp : VOK S0 y p := by
                rcases ha with ⟨h2, o2, he, ho2, hc2⟩ | ha
                · simp only [Slot.mem.injEq] at he
                  subst he
                  rw [ho, Option.some.injEq] at ho2
                  subst ho2
                  have hcz := hm.canonicalOf_of ho hc2
                  rw [hny] at hcz
                  have hpl := hm.pos.lv0 hcz ho
                  rw [hpos] at hpl
                  cases hu : db.S.lv y with
                  | none => rw [hu] at hpl; cases hpl
                  | some u =>
                    rw [hu, Option.map_some, Option.some.injEq] at hpl
                    rw [hpl]
                    exact hinv.VOK_lv hm.pre hu
                · exact ha p (by simp only [slotRefOf, ho, Option.bind_some, hpos])
              intro r hr
              simp only [slotRefOf, hs] at hr
              rw [hinv.ruleRRef_VOK hm.pre _ hVp, Option.some.injEq] at hr
              subst hr
              exact hVp
            have hnewO : ∀ v, SlotOwn S0 m v y (Slot.mem h) → SlotOwn S0 m' v y (Slot.stream (some p)) := by
              intro v ha r hr
              have h1 := ha p (by simp only [slotRefOf, ho, Option.bind_some, hpos])
              simp only [slotRefOf, hs] at hr
              rw [hs, h1]
              rw [← h1, ruleRRef_idem, h1] at hr
              exact hr
            constructor
            · intro h'' o'' ho'' hco z sl'' hsl''
              rcases hback h'' o'' ho'' with ⟨rfl, rfl⟩ | ⟨-, h2⟩
              · have hco0 : op.canonical = true := hco
                rw [hslot' z] at hsl''
                split at hsl''
                · rename_i hzy
                  subst hzy
                  simp only [Option.some.injEq] at hsl''
                  subst hsl''
                  exact hnewV (hn.canon h'' op hop hco0 z _ hsl)
                · exact (hn.canon h'' op hop hco0 z sl'' hsl'').keep hk hs (hold h'' op z sl'' hop hsl'')
              · exact (hn.canon h'' o'' h2 hco z sl'' hsl'').keep hk hs (hold h'' o'' z sl'' h2 hsl'')
            · intro h'' o'' ho'' hco r v hp'' hv z sl'' hsl''
              rcases hback h'' o'' ho'' with ⟨rfl, rfl⟩ | ⟨-, h2⟩
              · have hco0 : op.canonical = false := hco
                have hv0 : db.S.versionAt r op.node = some v := hv
                rw [hslot' z] at hsl''
                split at hsl''
                · rename_i hzy
                  subst hzy
                  simp only [Option.some.injEq] at hsl''
                  subst hsl''
                  rcases hn.snap h'' op hop hco0 r v hp'' hv0 z _ hsl with ha | ha
                  · exact Or.inl (hnewV ha)
                  · exact Or.inr (hnewO v ha)
                · rcases hn.snap h'' op hop hco0 r v hp'' hv0 z sl'' hsl'' with ha | ha
                  · exact Or.inl (ha.keep hk hs (hold h'' op z sl'' hop hsl''))
                  · exact Or.inr (ha.keep hk hs (hold h'' op z sl'' hop hsl''))
              · rcases hn.snap h'' o'' h2 hco r v hp'' hv z sl'' hsl'' with ha | ha
                · exact Or.inl (ha.keep hk hs (hold h'' o'' z sl'' h2 hsl''))
                · exact Or.inr (ha.keep hk hs (hold h'' o'' z sl'' h2 hsl''))
          · exact hn

/-- Release keeps the invariant: no memory slot names the object released. -/
theorem NInv.release (hn : NInv db S0 m) (h : Nat) :
    NInv db S0 (m.release db.D h) := by
  cases he : m.eligible db.D h with
  | false =>
    have : m.release db.D h = m := by unfold Mem.release; simp [he]
    rw [this]; exact hn
  | true =>
  have hinc : m.incoming h = false := by
    unfold Mem.eligible at he; simp only [Bool.and_eq_true, Bool.not_eq_true'] at he; exact he.2
  have hobj := release_obj? db.D he
  have hs' : (m.release db.D h).s = m.s := by unfold Mem.release; simp only [he, ↓reduceIte]
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
  have hV : ∀ h2 o2, m.obj? h2 = some o2 → ∀ z sl, o2.slot? z = some sl →
      SlotVOK S0 m z sl → SlotVOK S0 (m.release db.D h) z sl := by
    intro h2 o2 ho2 z sl hz ha
    rcases ha with ⟨h', o', he', ho', hc'⟩ | ha
    · subst he'
      have hne := Mem.incoming_false hinc ho2 hz
      exact Or.inl ⟨h', o', rfl, by rw [hsame h' hne]; exact ho', hc'⟩
    · exact Or.inr (fun r hr => ha r (by rw [← hslotRef h2 o2 ho2 z sl hz]; exact hr))
  have hO : ∀ h2 o2, m.obj? h2 = some o2 → ∀ v z sl, o2.slot? z = some sl →
      SlotOwn S0 m v z sl → SlotOwn S0 (m.release db.D h) v z sl := by
    intro h2 o2 ho2 v z sl hz ha r hr
    rw [hs']
    exact ha r (by rw [← hslotRef h2 o2 ho2 z sl hz]; exact hr)
  constructor
  · intro h2 o2 ho2 hco z sl hsl
    obtain ⟨-, ho2'⟩ := hstay h2 o2 ho2
    exact hV h2 o2 ho2' z sl hsl (hn.canon h2 o2 ho2' hco z sl hsl)
  · intro h2 o2 ho2 hco r v hp hv z sl hsl
    obtain ⟨-, ho2'⟩ := hstay h2 o2 ho2
    rcases hn.snap h2 o2 ho2' hco r v hp hv z sl hsl with ha | ha
    · exact Or.inl (hV h2 o2 ho2' z sl hsl ha)
    · exact Or.inr (hO h2 o2 ho2' v z sl hsl ha)

/-- Every cache operation keeps the invariant. -/
theorem NInv.cacheOp (hinv : Inv sp db k) (hm : EInv sp db S0 k m) (hn : NInv db S0 m) (op : CacheOp) :
    NInv db S0 (m.cacheOp sp S0 db.S db.D op) := by
  cases op with
  | read t => exact hn.read4 hinv hm t
  | unswizzle h y => exact hn.unswizzle hinv hm h y
  | release h => exact hn.release h

theorem NInv.cacheOps (hinv : Inv sp db k) (ops : List CacheOp) :
    ∀ m, EInv sp db S0 k m → NInv db S0 m → NInv db S0 (ops.foldl (Mem.cacheOp sp S0 db.S db.D) m) := by
  induction ops with
  | nil => intro m _ hn; exact hn
  | cons op ops ih => intro m hm hn; exact ih _ (hm.cacheOp hinv op) (hn.cacheOp hinv hm op)

end Cache


/-! ## The writer's walk -/

section Walk

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

theorem SlotVOK.keepPos {m' : Mem V} (hk : m.KeepPos m') (hs : m'.s = m.s) {y : NodeId} {sl : Slot}
    (ha : SlotVOK S0 m y sl) (hsl : ∀ h', sl = Slot.mem h' → (m.obj? h').isSome) :
    SlotVOK S0 m' y sl := by
  rcases ha with ⟨h', o', he, ho', hc'⟩ | ha
  · obtain ⟨o'', ho'', -, -, hc''⟩ := hk h' o' ho'
    exact Or.inl ⟨h', o'', he, ho'', hc'' hc'⟩
  · exact Or.inr (fun r hr => ha r (by rw [← slotRefOf_keepPos hk hs hsl]; exact hr))

theorem SlotOwn.keepPos {m' : Mem V} (hk : m.KeepPos m') (hs : m'.s = m.s) {v : Version V} {y : NodeId}
    {sl : Slot} (ha : SlotOwn S0 m v y sl) (hsl : ∀ h', sl = Slot.mem h' → (m.obj? h').isSome) :
    SlotOwn S0 m' v y sl := by
  intro r hr
  rw [hs]
  exact ha r (by rw [← slotRefOf_keepPos hk hs hsl]; exact hr)

/-- A snapshot of the latest version of a clean current node: what its
version's references name after Rule R is the pointees' latest version in S0,
or one after it. -/
theorem EvLogic.own_VOK (hinv : Inv sp db k) (hev : EvLogic sp db k) (hpre : S0 <+: db.S) {y : NodeId}
    {ny : Node V} (hny : db.P.get? y = some ny) (hyw : written sp y = true) (hr : reachable sp db.P k y = true)
    (hyD : inD db.D y = false) {w : Version V} (hw : db.S.lv y = some w) (s : Nat) (z : NodeId) {r : Nat}
    (h : ruleRRef S0 s z (w.ref? z) = some r) : VOK S0 z r := by
  cases hz : w.ref? z with
  | none => rw [hz] at h; exact ruleRRef_none_VOK h
  | some r0 =>
    rw [hz] at h
    have hzp : z ∈ pointees sp w.hist := hinv.ref_pointees hw hz
    obtain ⟨-, -, n', hn', hvh, -⟩ := hinv.version_node (hinv.lv_at hw)
    rw [hny, Option.some.injEq] at hn'
    subst hn'
    have hzn : z ∈ pointees sp ny.hist := by
      obtain ⟨e, he, hze⟩ := (mem_pointees sp _ _).mp hzp
      rw [hvh] at he
      exact (mem_pointees sp _ _).mpr ⟨e, (mem_upTo.mp he).1, hze⟩
    obtain ⟨-, v, hv, href⟩ := hev.clean y ny hyw hr hny hyD z hzn
    rw [hw, Option.some.injEq] at hv
    subst hv
    rw [hz] at href
    cases hl : db.S.lv z with
    | none => rw [hl] at href; cases href
    | some u =>
      rw [hl, Option.map_some, Option.some.injEq] at href
      subst href
      have hV := hinv.VOK_lv hpre hl
      rw [hinv.ruleRRef_VOK hpre s hV, Option.some.injEq] at h
      subst h
      exact hV

/-- Promotion after the writer's follow keeps the invariant: the slot names a
canonical object, and a snapshot promoted is of the latest version of a clean
current node, whose references name the pointees' latest versions. -/
theorem NInv.promote_step (hinv : Inv sp db k) (hev : EvLogic sp db k) (hm : EInv sp db S0 k m)
    (hn : NInv db S0 m) {hp : Nat} {op : Obj V} (hop : m.obj? hp = some op)
    (hco : op.canonical = true) (hr : reachable sp db.P k op.node = true) {y : NodeId}
    (hy : y ∈ sp.live op.hist) (hyw : written sp y = true) (hyne : y ≠ op.node) {h1 : Nat}
    (hsl : op.slot? y = some (Slot.mem h1)) (hry : reachable sp db.P k y = true) :
    NInv db S0 (m.promote hp y h1).1 := by
  obtain ⟨o1, ho1, hn1⟩ := hm.slotsNode hp op hop y h1 hsl
  have hp1 : hp ≠ h1 := by
    intro he; subst he; rw [hop, Option.some.injEq] at ho1; subst ho1; exact hyne hn1.symm
  have hold : ∀ h0 o0 z sl0, m.obj? h0 = some o0 → o0.slot? z = some sl0 →
      ∀ h', sl0 = Slot.mem h' → (m.obj? h').isSome := by
    intro h0 o0 z sl0 ho0 hsl0 h' he
    subst he
    obtain ⟨o', ho', -⟩ := hm.slotsNode h0 o0 ho0 z h' hsl0
    rw [ho']; rfl
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
    · intro h o' ho' hco' z sl' hsl'
      rcases hback h o' ho' with ⟨rfl, rfl⟩ | ⟨-, h2⟩
      · rcases hnewSlot z sl' hsl' with ⟨rfl, rfl⟩ | ⟨-, h3⟩
        · exact Or.inl ⟨h0, o0, rfl, ho0', hc0⟩
        · exact (hn.canon h op hop hco z sl' h3).keepPos hk hs (hold h op z sl' hop h3)
      · exact (hn.canon h o' h2 hco' z sl' hsl').keepPos hk hs (hold h o' z sl' h2 hsl')
    · intro h o' ho' hco' r v hp' hv z sl' hsl'
      rcases hback h o' ho' with ⟨rfl, rfl⟩ | ⟨-, h2⟩
      · exfalso
        have he : (op.setSlot y (Slot.mem h0)).canonical = op.canonical := rfl
        rw [he, hco] at hco'
        cases hco'
      · rcases hn.snap h o' h2 hco' r v hp' hv z sl' hsl' with ha | ha
        · exact Or.inl (ha.keepPos hk hs (hold h o' z sl' h2 hsl'))
        · exact Or.inr (ha.keepPos hk hs (hold h o' z sl' h2 hsl'))
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
    obtain ⟨r1, w1, e1, e2, -⟩ := hm.snap h1 o1 ho1 hnc
    have hw1 : db.S.lv y = some w1 := by
      cases hl : db.S.lv y with
      | none => rw [hl] at hpos1; rw [hpos1] at e1; cases e1
      | some v =>
        rw [hl] at hpos1
        rw [hpos1, Option.map_some, Option.some.injEq] at e1
        rw [← e1, hn1, hinv.lv_at hl, Option.some.injEq] at e2
        rw [e2]
    obtain ⟨ny, hny⟩ := Option.isSome_iff_exists.mp (Reach.isSome ((reachable_iff _ _ _ _).mp hry))
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
    -- The promoted object's slots name what the latest version's references
    -- name, its pointees' latest versions.
    have hprom : ∀ z sl'', o1.slot? z = some sl'' → SlotVOK S0 m' z sl'' := by
      intro z sl'' hz
      rcases hn.snap h1 o1 ho1 hnc r1 w1 e1 e2 z sl'' hz with ha | ha
      · exact ha.keepPos hk hs (hold h1 o1 z sl'' ho1 hz)
      · right
        intro r hr
        have hr' := (ha.keepPos hk hs (hold h1 o1 z sl'' ho1 hz)) r hr
        rw [hs] at hr'
        exact hev.own_VOK hinv hm.pre hny hyw hry hyD hw1 m.s z hr'
    constructor
    · intro h o' ho' hco' z sl'' hsl''
      rcases hback h o' ho' with ⟨rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨-, -, h2⟩
      · rcases hnewSlot z sl'' hsl'' with ⟨rfl, rfl⟩ | ⟨-, h3⟩
        · exact Or.inl ⟨h1, _, rfl, ho1', rfl⟩
        · exact (hn.canon h op hop hco z sl'' h3).keepPos hk hs (hold h op z sl'' hop h3)
      · exact hprom z sl'' hsl''
      · exact (hn.canon h o' h2 hco' z sl'' hsl'').keepPos hk hs (hold h o' z sl'' h2 hsl'')
    · intro h o' ho' hco' r v hp' hv z sl'' hsl''
      rcases hback h o' ho' with ⟨rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨-, -, h2⟩
      · exfalso
        have he : (op.setSlot y (Slot.mem h1)).canonical = op.canonical := rfl
        rw [he, hco] at hco'
        cases hco'
      · cases hco'
      · rcases hn.snap h o' h2 hco' r v hp' hv z sl'' hsl'' with ha | ha
        · exact Or.inl (ha.keepPos hk hs (hold h o' z sl'' h2 hsl''))
        · exact Or.inr (ha.keepPos hk hs (hold h o' z sl'' h2 hsl''))


/-- The writer's follow of a live slot of the canonical object of a current node
keeps the invariant. -/
theorem NInv.follow4_writer (hinv : Inv sp db k) (hls : LiveSub sp) (hev : EvLogic sp db k)
    (hm : EInv sp db S0 k m) (hn : NInv db S0 m) {hp : Nat} {op : Obj V} (hop : m.obj? hp = some op)
    (hco : op.canonical = true) (hr : reachable sp db.P k op.node = true) {y : NodeId}
    (hy : y ∈ sp.live op.hist) : NInv db S0 (m.follow4 sp S0 db.S hp y true).1 := by
  obtain ⟨n, hn', hhist, -, -⟩ := hm.cc hp op hop hco
  have hy' : y ∈ sp.live (n.hist.upTo k) := by
    rw [upTo_of_forall _ _ (hinv.times _ n hn'), ← hhist]; exact hy
  obtain ⟨hry, hyroot, ny, hny, hlt⟩ := hinv.reach_child hls hn' hr hy'
  have hyw : written sp y = true := written_of_ne_root sp hyroot
  have hyne : y ≠ op.node := by
    intro he; rw [he, hn', Option.some.injEq] at hny; subst hny; omega
  rw [follow4_eq]
  cases hrc : m.reached4 sp S0 db.S hp y with
  | none => exact hn
  | some p =>
    obtain ⟨m1, h1⟩ := p
    simp only [↓reduceIte]
    obtain ⟨hop2, -, -⟩ := hm.reached4_frame hop hrc
    have hm2 := hm.reached4 hinv hrc
    have hn2 := hn.reached4 hinv hm hrc
    have hsl2 : (op.setSlot y (Slot.mem h1)).slot? y = some (Slot.mem h1) := by
      obtain ⟨op0, sl, hop0, hsl0, -⟩ := reached4_cases hrc
      rw [hop, Option.some.injEq] at hop0; subst hop0
      rw [slot?_setSlot_of hsl0]; simp
    exact hn2.promote_step hinv hev hm2 hop2 hco hr hy hyw hyne hsl2 hry

/-- The writer reaches one node of a path. -/
theorem NInv.reachOnPath4 (hinv : Inv sp db k) (hls : LiveSub sp) (hev : EvLogic sp db k)
    (hm : EInv sp db S0 k m) (hn : NInv db S0 m) {path : List NodeId}
    (hpath : ∀ p ∈ path, reachable sp db.P k p = true) (x : NodeId) :
    NInv db S0 (m.reachOnPath4 sp S0 db.S db.P (k + 1) path x) := by
  unfold Mem.reachOnPath4
  have hK1 : k + 1 - 1 = k := by omega
  cases hf : path.find? (fun p => match db.P.get? p, m.canonicalOf p with
      | some n, some _ => (sp.live (n.hist.upTo (k + 1 - 1))).contains x
      | _, _ => false) with
  | none => exact hn
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
        exact hn.follow4_writer hinv hls hev hm hop hco (by rw [hnode]; exact hpath p hpm) hxop

/-- The writer reaches the nodes of its paths: the invariant is kept. -/
theorem NInv.reachPath4 (hinv : Inv sp db k) (hls : LiveSub sp) (hev : EvLogic sp db k)
    {path : List NodeId} (hpath : ∀ p ∈ path, reachable sp db.P k p = true) :
    ∀ (L : List NodeId) (m : Mem V), EInv sp db S0 k m → NInv db S0 m →
      NInv db S0 (L.foldl (Mem.reachOnPath4 sp S0 db.S db.P (k + 1) path) m) := by
  intro L
  induction L with
  | nil => intro m _ hn; exact hn
  | cons x L ih =>
    intro m hm hn
    simp only [List.foldl_cons]
    exact ih _ (hm.reachOnPath4_ok hinv hls hev hpath x).1 (hn.reachOnPath4 hinv hls hev hm hpath x)

end Walk


/-! ## The change and the writes -/

section Change

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V} {c : Changes V}

/-- The change keeps the invariant: a new slot names a canonical object, or
copies a slot that names its pointee's latest version. -/
theorem NInv.applyChange4 (hinv : Inv sp db k) (hm : EInv sp db S0 k m) (hn : NInv db S0 m)
    (hstep : StepOK sp db.P (k + 1) c) : NInv db S0 (m.applyChange4 sp db.P (k + 1) c) := by
  have haf := hm.addFacts hstep.distinct
  have hcf := changeFacts sp db.P (k + 1) c m
  have hobj : ∀ h o3, (m.applyChange4 sp db.P (k + 1) c).obj? h = some o3 → ∃ o1,
      (c.new.foldl addNew m).obj? h = some o1 ∧
      o3 = updAll4 sp db.P (k + 1) (c.new.foldl addNew m)
        (c.adds.filter (fun a => (c.new.foldl addNew m).canonicalOf a.1 == some h)) o1 := by
    intro h o3 ho3
    rw [hcf.obj h] at ho3
    obtain ⟨o1, ho1, rfl⟩ := Option.map_eq_some_iff.mp ho3
    exact ⟨o1, ho1, rfl⟩
  have hk : m.KeepPos (m.applyChange4 sp db.P (k + 1) c) := by
    intro h o ho
    have hlt := lt_next_of_obj? hm.fresh ho
    rw [hcf.obj h, haf.old h hlt, ho, Option.map_some]
    obtain ⟨e1, -, -, -, e5, e6⟩ := updAll4_core sp db.P (k + 1) (c.new.foldl addNew m)
      (c.adds.filter (fun a => (c.new.foldl addNew m).canonicalOf a.1 == some h)) o
    exact ⟨_, rfl, e1, e6, fun hc => by rw [e5]; exact hc⟩
  have hs : (m.applyChange4 sp db.P (k + 1) c).s = m.s := by rw [hcf.s, haf.s]
  have hcan3 : ∀ y, (m.applyChange4 sp db.P (k + 1) c).canonicalOf y = (c.new.foldl addNew m).canonicalOf y :=
    hcf.canonicalOf
  have hcanObj : ∀ y h', (c.new.foldl addNew m).canonicalOf y = some h' →
      ∃ o', (m.applyChange4 sp db.P (k + 1) c).obj? h' = some o' ∧ o'.canonical = true := by
    intro y h' hc'
    obtain ⟨o'', ho'', -, hco''⟩ := hm.addNew_canon haf hc'
    obtain ⟨-, -, -, -, f5, -⟩ := updAll4_core sp db.P (k + 1) (c.new.foldl addNew m)
      (c.adds.filter (fun a => (c.new.foldl addNew m).canonicalOf a.1 == some h')) o''
    exact ⟨_, by rw [hcf.obj h', ho'']; rfl, by rw [f5, hco'']⟩
  have hold : ∀ h0 o0 z sl0, m.obj? h0 = some o0 → o0.slot? z = some sl0 →
      ∀ h', sl0 = Slot.mem h' → (m.obj? h').isSome := by
    intro h0 o0 z sl0 ho0 hsl0 h' he
    subst he
    obtain ⟨o', ho', -⟩ := hm.slotsNode h0 o0 ho0 z h' hsl0
    rw [ho']; rfl
  have hslot : ∀ h o3, (m.applyChange4 sp db.P (k + 1) c).obj? h = some o3 → ∀ z sl, o3.slot? z = some sl →
      ∃ o1, (c.new.foldl addNew m).obj? h = some o1 ∧
        (o1.slot? z = some sl ∨ NS4 sp db.P (k + 1) (c.new.foldl addNew m) z = some sl) := by
    intro h o3 ho3 z sl hz
    obtain ⟨o1, ho1, rfl⟩ := hobj h o3 ho3
    refine ⟨o1, ho1, ?_⟩
    rw [updAll4_slot] at hz
    split at hz
    · unfold combo4 at hz
      cases hns : NS4 sp db.P (k + 1) (c.new.foldl addNew m) z with
      | none => rw [hns, Option.none_or] at hz; exact Or.inl hz
      | some sl' =>
        rw [hns, Option.some_or] at hz
        exact Or.inr hz
    · exact Or.inl hz
  -- A new slot names a canonical object, or what a slot naming the pointee's
  -- latest version names.
  have hNS : ∀ z sl, NS4 sp db.P (k + 1) (c.new.foldl addNew m) z = some sl →
      SlotVOK S0 (m.applyChange4 sp db.P (k + 1) c) z sl := by
    intro z sl hns
    rcases hm.NS4_good hinv hstep hns with ⟨h', rfl, hc'⟩ | ⟨-, -, -, href, h0, o0, ho0, hsl0⟩
    · obtain ⟨o', ho', hco'⟩ := hcanObj z h' hc'
      exact Or.inl ⟨h', o', rfl, ho', hco'⟩
    · right
      intro r hr
      rw [slotRefOf_keepPos hk hs (hold h0 o0 z sl ho0 hsl0), href] at hr
      cases hl : db.S.lv z with
      | none => rw [hl] at hr; cases hr
      | some u =>
        rw [hl, Option.map_some, Option.some.injEq] at hr
        subst hr
        exact hinv.VOK_lv hm.pre hl
  have hm1 : ∀ h o1, (c.new.foldl addNew m).obj? h = some o1 →
      m.obj? h = some o1 ∨ (∃ nn ∈ c.new, o1 = newObj nn) := by
    intro h o1 ho1
    rcases haf.cls h o1 ho1 with ⟨-, h2⟩ | ⟨-, nn, hnn, hon, -⟩
    · exact Or.inl h2
    · exact Or.inr ⟨nn, hnn, hon⟩
  constructor
  · intro h o3 ho3 hco z sl hsl
    obtain ⟨o1, ho1, hcase⟩ := hslot h o3 ho3 z sl hsl
    obtain ⟨o1', ho1', rfl⟩ := hobj h o3 ho3
    rw [ho1, Option.some.injEq] at ho1'
    subst ho1'
    obtain ⟨-, -, -, -, e5, -⟩ := updAll4_core sp db.P (k + 1) (c.new.foldl addNew m)
      (c.adds.filter (fun a => (c.new.foldl addNew m).canonicalOf a.1 == some h)) o1
    rcases hcase with hcase | hcase
    · rcases hm1 h o1 ho1 with ho | ⟨nn, -, rfl⟩
      · exact (hn.canon h o1 ho (by rw [← e5]; exact hco) z sl hcase).keepPos hk hs (hold h o1 z sl ho hcase)
      · simp [newObj, Obj.slot?] at hcase
    · exact hNS z sl hcase
  · intro h o3 ho3 hco r v hp hv z sl hsl
    obtain ⟨o1, ho1, hcase⟩ := hslot h o3 ho3 z sl hsl
    obtain ⟨o1', ho1', rfl⟩ := hobj h o3 ho3
    rw [ho1, Option.some.injEq] at ho1'
    subst ho1'
    obtain ⟨e1, -, -, -, e5, e6⟩ := updAll4_core sp db.P (k + 1) (c.new.foldl addNew m)
      (c.adds.filter (fun a => (c.new.foldl addNew m).canonicalOf a.1 == some h)) o1
    rcases hcase with hcase | hcase
    · rcases hm1 h o1 ho1 with ho | ⟨nn, -, rfl⟩
      · rcases hn.snap h o1 ho (by rw [← e5]; exact hco) r v (by rw [← e6]; exact hp)
          (by rw [← e1]; exact hv) z sl hcase with ha | ha
        · exact Or.inl (ha.keepPos hk hs (hold h o1 z sl ho hcase))
        · exact Or.inr (ha.keepPos hk hs (hold h o1 z sl ho hcase))
      · simp [newObj, Obj.slot?] at hcase
    · exact Or.inl (hNS z sl hcase)


/-- After the writes: a slot is as before, or a memory slot to its pointee's
canonical object; a snapshot keeps its position, a canonical object stays
canonical. So the invariant holds for the next state too. -/
theorem NInv.loops {db' : DB V T} (hS : db.S <+: db'.S) {m3 m6 : Mem V} (hsn : SlotsNode m3)
    (hsnap : ∀ h o, m3.obj? h = some o → o.canonical = false → ∀ r, o.pos = some r →
      ∃ w, db.S.versionAt r o.node = some w)
    (hn3 : NInv db S0 m3) {D0 D1 : Dirty} {xs1 xs2 : List NodeId} {i : Nat}
    (hfr : LoopsFrame D0 D1 xs1 xs2 i m3 m6) : NInv db' S0 m6 := by
  have hobj : ∀ h o6, m6.obj? h = some o6 → ∃ o3, m3.obj? h = some o3 := by
    intro h o6 ho6
    cases h3 : m3.obj? h with
    | none => rw [hfr.none h h3] at ho6; cases ho6
    | some o3 => exact ⟨o3, rfl⟩
  -- A snapshot stays as it is; a canonical object stays canonical.
  have hsnap6 : ∀ h o3, m3.obj? h = some o3 → o3.canonical = false → ∃ o6, m6.obj? h = some o6 ∧
      o6.node = o3.node ∧ o6.canonical = false ∧ o6.pos = o3.pos ∧ ∀ z, o6.slot? z = o3.slot? z := by
    intro h o3 ho3 hc3'
    obtain ⟨o6, ho6, e1, -, -, -, e5, -, -, e8⟩ := hfr.obj h o3 ho3
    have hnc : ¬ ((o3.node ∈ xs1 ∨ o3.node ∈ xs2) ∧ m3.canonicalOf o3.node = some h) := by
      rintro ⟨-, hc⟩
      obtain ⟨-, o', ho', hco⟩ := (m3.canonicalOf_eq_some _ h).mp hc
      rw [ho3, Option.some.injEq] at ho'; subst ho'
      rw [hc3'] at hco; cases hco
    exact ⟨o6, ho6, e1, by rw [e5]; exact hc3', (e8 hnc).1, (e8 hnc).2⟩
  have hcan6 : ∀ h o3, m3.obj? h = some o3 → o3.canonical = true → ∃ o6, m6.obj? h = some o6 ∧
      o6.canonical = true := by
    intro h o3 ho3 hc3'
    obtain ⟨o6, ho6, -, -, -, -, e5, -⟩ := hfr.obj h o3 ho3
    exact ⟨o6, ho6, by rw [e5]; exact hc3'⟩
  -- What a slot of m3 names, in m6.
  have hsame : ∀ y sl, (∀ h', sl = Slot.mem h' → (m3.obj? h').isSome) →
      (∃ h' o', sl = Slot.mem h' ∧ m6.obj? h' = some o' ∧ o'.canonical = true) ∨
        slotRefOf S0 m6 y sl = slotRefOf S0 m3 y sl := by
    intro y sl hsl
    cases sl with
    | stream r => right; simp only [slotRefOf, hfr.s]
    | mem h' =>
      obtain ⟨o', ho'⟩ := Option.isSome_iff_exists.mp (hsl h' rfl)
      cases hco : o'.canonical with
      | true =>
        obtain ⟨o6, ho6, hc6⟩ := hcan6 h' o' ho' hco
        exact Or.inl ⟨h', o6, rfl, ho6, hc6⟩
      | false =>
        obtain ⟨o6, ho6, -, -, hp6, -⟩ := hsnap6 h' o' ho' hco
        right
        simp only [slotRefOf, ho6, ho', Option.bind_some, hp6]
  have hV : ∀ y sl, (∀ h', sl = Slot.mem h' → (m3.obj? h').isSome) → SlotVOK S0 m3 y sl →
      SlotVOK S0 m6 y sl := by
    intro y sl hsl ha
    rcases ha with ⟨h', o', he, ho', hc'⟩ | ha
    · obtain ⟨o6, ho6, hc6⟩ := hcan6 h' o' ho' hc'
      exact Or.inl ⟨h', o6, he, ho6, hc6⟩
    · rcases hsame y sl hsl with hc | he
      · exact Or.inl hc
      · exact Or.inr (fun r hr => ha r (by rw [← he]; exact hr))
  have hO : ∀ v y sl, (∀ h', sl = Slot.mem h' → (m3.obj? h').isSome) → SlotOwn S0 m3 v y sl →
      SlotVOK S0 m6 y sl ∨ SlotOwn S0 m6 v y sl := by
    intro v y sl hsl ha
    rcases hsame y sl hsl with hc | he
    · exact Or.inl (Or.inl hc)
    · exact Or.inr (fun r hr => by rw [hfr.s]; exact ha r (by rw [← he]; exact hr))
  have hold : ∀ h0 o0 z sl0, m3.obj? h0 = some o0 → o0.slot? z = some sl0 →
      ∀ h', sl0 = Slot.mem h' → (m3.obj? h').isSome := by
    intro h0 o0 z sl0 ho0 hsl0 h' he
    subst he
    obtain ⟨o', ho', -⟩ := hsn h0 o0 ho0 z h' hsl0
    rw [ho']; rfl
  constructor
  · intro h o6 ho6 hco z sl hsl
    obtain ⟨o3, ho3⟩ := hobj h o6 ho6
    obtain ⟨o6', ho6', -, -, -, -, e5, hsl6, -, -⟩ := hfr.obj h o3 ho3
    rw [ho6, Option.some.injEq] at ho6'
    subst ho6'
    have hc3' : o3.canonical = true := by rw [← e5]; exact hco
    rcases hsl6 z with hs | ⟨-, sl', h0, -, hc0, hs⟩
    · rw [hs] at hsl
      exact hV z sl (hold h o3 z sl ho3 hsl) (hn3.canon h o3 ho3 hc3' z sl hsl)
    · rw [hs, Option.some.injEq] at hsl
      subst hsl
      obtain ⟨-, o0, ho0, hco0⟩ := (m3.canonicalOf_eq_some z h0).mp hc0
      obtain ⟨o6', ho6', hc6'⟩ := hcan6 h0 o0 ho0 hco0
      exact Or.inl ⟨h0, o6', rfl, ho6', hc6'⟩
  · intro h o6 ho6 hco r v hp hv z sl hsl
    obtain ⟨o3, ho3⟩ := hobj h o6 ho6
    have hc3' : o3.canonical = false := by
      obtain ⟨o6', ho6', -, -, -, -, e5, -⟩ := hfr.obj h o3 ho3
      rw [ho6, Option.some.injEq] at ho6'
      subst ho6'
      rw [← e5]; exact hco
    obtain ⟨o6', ho6', e1, -, hp6, hsl6⟩ := hsnap6 h o3 ho3 hc3'
    rw [ho6, Option.some.injEq] at ho6'
    subst ho6'
    rw [hsl6 z] at hsl
    rw [hp6] at hp
    rw [e1] at hv
    -- The snapshot's version, in db's stream.
    have hv0 : db.S.versionAt r o3.node = some v := by
      obtain ⟨w, hw⟩ := hsnap h o3 ho3 hc3' r hp
      rw [versionAt_prefix hS hw, Option.some.injEq] at hv
      rw [hw, hv]
    rcases hn3.snap h o3 ho3 hc3' r v hp hv0 z sl hsl with ha | ha
    · exact Or.inl (hV z sl (hold h o3 z sl ho3 hsl) ha)
    · exact hO v z sl (hold h o3 z sl ho3 hsl) ha


end Change

/-! ## One transaction, and runs -/

section Next

variable {sp : Spec V T} {al : Algo V T} {db : DB V T} {tr : T} {S0 : Stream V T} {k : Nat}

/-- One transaction of the physical writer keeps the invariant: its reads, its
walk to the paths, the change, and the writes. -/
theorem NInv.evictTrans_ok (hsp : SpecOK sp) (hinv : Inv sp db k) (hmk : al.mark = true)
    {m : Mem V} (hm : EInv sp db S0 k m) (hn : NInv db S0 m) (hev : EvLogic sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) (hphys : PhysStep sp db.P (k + 1) (parts sp al db tr).c)
    (hcopy : CopyStep sp db.P (k + 1) (parts sp al db tr).c) (htree : treeAt sp db.P k)
    (hinv' : Inv sp (step sp al db tr) (k + 1)) :
    NInv (step sp al db tr) S0 (evictTrans sp al S0 db m tr).2 := by
  have hls : LiveSub sp := hsp.liveSub
  have hlen := hinv.len
  have hK1 : k + 1 - 1 = k := by omega
  obtain ⟨hm1, hv⟩ := hm.view4_ok hinv hls hev
  have hn1 : NInv db S0 (m.view4 sp S0 db.S k).1 := hn.read4 hinv hm k
  have hcx : sp.exec tr db.S.length (m.view4 sp S0 db.S (db.S.length - 1)).2 = (parts sp al db tr).c := by
    rw [hlen, hK1, hv, parts_c, hlen, hK1]
  rw [evictTrans_eq, hcx, evictAfter_eq]
  have hm1' : EInv sp db S0 k (m.view4 sp S0 db.S (db.S.length - 1)).1 := by rw [hlen, hK1]; exact hm1
  have hn1' : NInv db S0 (m.view4 sp S0 db.S (db.S.length - 1)).1 := by rw [hlen, hK1]; exact hn1
  generalize (m.view4 sp S0 db.S (db.S.length - 1)).1 = m1 at hm1' hn1' ⊢
  have hpr : ∀ p ∈ pathOf sp db.P (parts sp al db tr).c (k + 1), reachable sp db.P k p = true := by
    intro p hp; have := (mem_pathOf hp).1; rw [hK1] at this; exact this
  have hparent : ∀ x ∈ pathOf sp db.P (parts sp al db tr).c (k + 1), x ≠ SIS.root →
      ∃ p ∈ pathOf sp db.P (parts sp al db tr).c (k + 1), ∃ np nx, db.P.get? p = some np ∧
        db.P.get? x = some nx ∧ nx.level < np.level ∧ x ∈ sp.live (np.hist.upTo k) := by
    intro x hx hxr
    have hrx := (mem_pathOf hx).1
    rw [hK1] at hrx
    obtain ⟨p, np, nx, hrp, hnp, hnx, hlt, hxl⟩ := reach_parent hrx hxr
    refine ⟨p, pathOf_parent hx (by rw [hK1]; exact hrp) hnp (by rw [hK1]; exact hxl) hnx hlt, np, nx, hnp, hnx,
      hlt, hxl⟩
  have hpnd : (pathOf sp db.P (parts sp al db tr).c (k + 1)).Nodup := by
    unfold pathOf; exact nodup_filter (nodup_eraseDups _) _
  have hsorted := pairwise_byLevelDesc db.P (pathOf sp db.P (parts sp al db tr).c (k + 1))
  obtain ⟨hm2, hpd⟩ := EInv.reachPath4_ok (S0 := S0) hinv hls hev hpr hparent
    ((pathOf sp db.P (parts sp al db tr).c (k + 1)).mergeSort (fun a b => decide (lev db.P b ≤ lev db.P a))) []
    m1 hm1' (fun a ha => by cases ha)
    (fun x => by rw [List.nil_append]; exact (List.mergeSort_perm _ _).mem_iff)
    (by rw [List.nil_append]; exact (List.mergeSort_perm _ _).nodup_iff.mpr hpnd)
    (by rw [List.nil_append]; exact hsorted)
  have hn2 := NInv.reachPath4 (S0 := S0) hinv hls hev hpr
    ((pathOf sp db.P (parts sp al db tr).c (k + 1)).mergeSort (fun a b => decide (lev db.P b ≤ lev db.P a)))
    m1 hm1' hn1'
  have ha := hm2.applyChange4_ok hinv hls hpd hstep hphys hcopy htree
  have hn3 := hn2.applyChange4 hinv hm2 hstep
  have hpre : preWrite sp S0 db (parts sp al db tr).c m1 =
      (((pathOf sp db.P (parts sp al db tr).c (k + 1)).mergeSort (fun a b => decide (lev db.P b ≤ lev db.P a))).foldl
        (Mem.reachOnPath4 sp S0 db.S db.P (k + 1) (pathOf sp db.P (parts sp al db tr).c (k + 1))) m1).applyChange4
        sp db.P (k + 1) (parts sp al db tr).c := by
    unfold preWrite; rw [hlen]; rfl
  rw [hpre, hlen]
  generalize (((pathOf sp db.P (parts sp al db tr).c (k + 1)).mergeSort
    (fun a b => decide (lev db.P b ≤ lev db.P a))).foldl
      (Mem.reachOnPath4 sp S0 db.S db.P (k + 1) (pathOf sp db.P (parts sp al db tr).c (k + 1))) m1).applyChange4
      sp db.P (k + 1) (parts sp al db tr).c = m3 at ha hn3 ⊢
  obtain ⟨e1, -, -, -⟩ := ha.loops_vs hsp hinv hmk hstep hinv'
  have hdata : ((parts sp al db tr).c.new.filter (·.isData)).map (·.id) = dataIds sp al db tr := rfl
  rw [hdata, e1, ← parts_D1Of, ← parts_takenOf]
  have hdnd : (dataIds sp al db tr).Nodup := (List.Sublist.map _ List.filter_sublist).nodup hstep.distinct
  have hdisj : ∀ x ∈ dataIds sp al db tr, x ∉ (parts sp al db tr).taken := by
    intro x hx hxt
    obtain ⟨d, hxd, -⟩ := step_taken_inD (al := al) (tr := tr) hinv hxt
    obtain ⟨hnone, -⟩ := step_dataIds_spec sp al db tr hinv hstep hx
    have := hinv.dIndex (x, d) hxd
    simp [isIndex, hnone] at this
  have hfr := loopsFrame sp S0 db.D (parts sp al db tr).D1 (k + 1) (dataIds sp al db tr) (parts sp al db tr).taken
    m3 hdnd (step_taken_nodup sp al db tr hinv) ha.tbl hdisj
  have hS : db.S <+: (step sp al db tr).S := List.prefix_append _ _
  have hsnap : ∀ h o, m3.obj? h = some o → o.canonical = false → ∀ r, o.pos = some r →
      ∃ w, db.S.versionAt r o.node = some w := by
    intro h o ho hc r hr
    obtain ⟨r', w, s1, s2, -⟩ := ha.snap h o ho hc
    rw [hr, Option.some.injEq] at s1
    subst s1
    exact ⟨w, s2⟩
  exact NInv.loops hS ha.slotsNode hsnap hn3 hfr

end Next

section Run

variable {sp : Spec V T} {al : Algo V T}

/-- One transaction of a run with eviction, and its cache operations, keep the
invariant. -/
theorem NInv.run_step {ts : List T} (hok : RunOK sp al ts) (hph : PhysRunOK sp al ts)
    (hev : EvictRunOK sp al ts) (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) {j : Nat}
    (hjt : j < ts.length) {S0 : Stream V T} {m : Mem V} (hm : EInv sp (st sp al ts j) S0 j m)
    (hn : NInv (st sp al ts j) S0 m) (ops : List CacheOp) :
    NInv (st sp al ts (j + 1)) S0
      (ops.foldl (Mem.cacheOp sp S0 (evictTrans sp al S0 (st sp al ts j) m ts[j]).1.S
        (evictTrans sp al S0 (st sp al ts j) m ts[j]).1.D) (evictTrans sp al S0 (st sp al ts j) m ts[j]).2) := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hsp := hok.1
  have hinv := inv_st sp al ts hok hst j (by omega)
  have hinv' := inv_st sp al ts hok hst (j + 1) (by omega)
  have hlog := evLogic_st sp al ts hok hj hmk hev j (by omega)
  have hlog' := evLogic_st sp al ts hok hj hmk hev (j + 1) (by omega)
  have hcx : (parts sp al (st sp al ts j) ts[j]).c = sp.exec ts[j] (j + 1) (view sp (st sp al ts j).P j) := by
    rw [parts_c, hinv.len, Nat.add_sub_cancel]
  have hstep : StepOK sp (st sp al ts j).P (j + 1) (parts sp al (st sp al ts j) ts[j]).c := by
    rw [hcx]; exact hok.2 j hjt
  have hphys : PhysStep sp (st sp al ts j).P (j + 1) (parts sp al (st sp al ts j) ts[j]).c := by
    rw [hcx]; exact hph j hjt
  have hcopy : CopyStep sp (st sp al ts j).P (j + 1) (parts sp al (st sp al ts j) ts[j]).c := by
    rw [hcx]; exact hev.2 j hjt
  have htree : treeAt sp (st sp al ts j).P j := (hev.1 j (by omega)).tree
  rw [st_succ sp al ts hjt] at hinv' hlog' ⊢
  obtain ⟨h1, h2⟩ := hm.evictTrans_ok hsp hinv hmk hlog hstep hphys hcopy htree hinv' hlog'
  have h3 := NInv.evictTrans_ok hsp hinv hmk hm hn hlog hstep hphys hcopy htree hinv'
  rw [h1]
  exact NInv.cacheOps hinv' ops _ h2 h3

/-- The run invariants with `NInv`, for the stream of the last startup. -/
def EvictInvN (sp : Spec V T) (al : Algo V T) (ts : List (T × Bool × List CacheOp)) (j : Nat)
    (r : DB V T × Mem V × Stream V T) : Prop :=
  EvictInvC sp al ts j r ∧ NInv (st sp al (ts.map (·.1)) j) r.2.2 r.2.1

/-- One transaction of a run with eviction and restarts, and its cache
operations or its restart, keeps `EvictInvN`. -/
theorem evictInvN_step {ts : List (T × Bool × List CacheOp)} (hok : RunOK sp al (ts.map (·.1)))
    (hph : PhysRunOK sp al (ts.map (·.1))) (hev : EvictRunOK sp al (ts.map (·.1)))
    (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) {j : Nat} (hjt : j < ts.length)
    {acc : DB V T × Mem V × Stream V T} (hI : EvictInvN sp al ts j acc) :
    EvictInvN sp al ts (j + 1)
      (if ts[j].2.1 then
        (startup sp (evictTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S,
          evictStartup sp (evictTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S,
          (evictTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S)
      else
        ((evictTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1,
          ts[j].2.2.foldl (Mem.cacheOp sp acc.2.2 (evictTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S
            (evictTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.D) (evictTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).2,
          acc.2.2)) := by
  obtain ⟨hC, hN⟩ := hI
  refine ⟨evictInvC_step hok hph hev hj hmk hjt hC, ?_⟩
  obtain ⟨⟨k1, -, hS0, hrel, hm, -⟩, -⟩ := hC
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hjm : j < (ts.map (·.1)).length := by simp; omega
  have htr : (ts.map (·.1))[j] = ts[j].1 := by simp
  obtain ⟨hrel1, hmem1⟩ := evictTrans_congr sp al hst acc.2.2 hrel acc.2.1 ts[j].1
  rw [← hS0] at hm
  have hrunN := NInv.run_step hok hph hev hj hmk hjm hm hN ts[j].2.2
  have hrun := EInv.run_step hok hph hev hj hmk hjm hm ts[j].2.2
  rw [htr] at hrunN hrun
  obtain ⟨f1, -⟩ := hrun
  have hrel' : Rel (evictTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1 (st sp al (ts.map (·.1)) (j + 1)) := by
    rw [← f1]; exact hrel1
  split
  · show NInv _ (evictTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S
      (evictStartup sp (evictTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S)
    rw [hrel'.1]
    exact ninv_startup hok hph hj hmk hev (by simp; omega)
  · show NInv _ acc.2.2 (ts[j].2.2.foldl (Mem.cacheOp sp acc.2.2 (evictTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S
      (evictTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.D) (evictTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).2)
    rw [hrel1.1, hrel1.2.1, hmem1]
    exact hrunN

/-- `EvictInvN` holds after every prefix of a run with eviction and restarts. -/
theorem evictInvN_all {ts : List (T × Bool × List CacheOp)} (hok : RunOK sp al (ts.map (·.1)))
    (hph : PhysRunOK sp al (ts.map (·.1))) (hev : EvictRunOK sp al (ts.map (·.1)))
    (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) :
    ∀ j ≤ ts.length, EvictInvN sp al ts j (runEvict sp al (ts.take j)) := by
  intro j
  induction j with
  | zero =>
    intro _
    have h0 : runEvict sp al (ts.take 0) = (init sp, evictStartup sp (init sp).S, (init sp).S) := by
      simp [runEvict]
    refine ⟨evictInvC_all hok hph hev hj hmk 0 (Nat.zero_le _), ?_⟩
    rw [h0]
    have := ninv_startup hok hph hj hmk hev (k := 0) (Nat.zero_le _)
    rw [st_zero] at this
    rw [st_zero]
    exact this
  | succ j ih =>
    intro hjt
    rw [runEvict_succ sp al ts (by omega)]
    exact evictInvN_step hok hph hev hj hmk (by omega) (ih (by omega))

end Run

end SIS
