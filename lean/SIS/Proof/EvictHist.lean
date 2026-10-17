/-
Proofs for stage 2 (bergdb item 001, WP E4), part 1: the invariant for reads at
earlier times (`HInv`). For every canonical object, every time t at which its
node is reachable, and every live child at t: a memory slot to an object that a
read at t may use (canonical, or the snapshot of a version good for t); or a
stream slot that names, after Rule R, a version good for t, or a node of D, the
object's node being in D and no later (INV-SLOT's second half). The cache
operations keep it.
-/
import SIS.Proof.EvictInit

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## The invariant -/

/-- Object h, of node y, can be read at time t: it is canonical, or the
snapshot of a version of y good for t. -/
def ReadableT (sp : Spec V T) (db : DB V T) (m : Mem V) (t : Time) (h : Nat) (y : NodeId) : Prop :=
  ∃ o, m.obj? h = some o ∧ o.node = y ∧
    (o.canonical = true ∨ ∃ r w, o.pos = some r ∧ db.S.versionAt r y = some w ∧
      good sp db.S db.P t w = true)

/-- A stream slot's reference that names, after Rule R, a version of y good
for t. -/
def GoodRef (sp : Spec V T) (S0 : Stream V T) (db : DB V T) (m : Mem V) (t : Time) (y : NodeId)
    (r : Option Nat) : Prop :=
  ∃ r' w, ruleRRef S0 m.s y r = some r' ∧ db.S.versionAt r' y = some w ∧ good sp db.S db.P t w = true

/-- INV-SLOT's second half: y and x are in D, x got dirty no later. -/
def DLater (D : Dirty) (x y : NodeId) : Prop :=
  inD D y = true ∧ inD D x = true ∧ ∃ a b, dOf D x = some a ∧ dOf D y = some b ∧ a ≤ b

/-- The slot of an object of node x for y, a live child of it at t, as a read at
t needs it. -/
def SlotHist (sp : Spec V T) (S0 : Stream V T) (db : DB V T) (m : Mem V) (t : Time) (x y : NodeId) :
    Slot → Prop
  | Slot.mem h' => ReadableT sp db m t h' y
  | Slot.stream r => GoodRef sp S0 db m t y r ∨ DLater db.D x y

/-- E4's invariant: the slots of canonical objects for reads at every time up
to k. -/
def HInv (sp : Spec V T) (db : DB V T) (S0 : Stream V T) (k : Nat) (m : Mem V) : Prop :=
  ∀ h o, m.obj? h = some o → o.canonical = true → ∀ t ≤ k, reachable sp db.P t o.node = true →
    ∀ y ∈ sp.live (o.hist.upTo t), ∃ sl, o.slot? y = some sl ∧ SlotHist sp S0 db m t o.node y sl

/-! ## Memories that keep what reads need -/

/-- m' keeps what reads need of m's objects: each is in m', of the same node,
still canonical if it was, and at the same position if it is not canonical. -/
def Mem.KeepRead (m m' : Mem V) : Prop :=
  ∀ h o, m.obj? h = some o → ∃ o', m'.obj? h = some o' ∧ o'.node = o.node ∧
    (o.canonical = true → o'.canonical = true) ∧ (o'.canonical = false → o'.pos = o.pos)

section Keep

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m m' m'' : Mem V}

theorem Mem.KeepRead.refl (m : Mem V) : m.KeepRead m := fun _ o ho => ⟨o, ho, rfl, id, fun _ => rfl⟩

theorem Mem.KeepRead.trans (h1 : m.KeepRead m') (h2 : m'.KeepRead m'') : m.KeepRead m'' := by
  intro h o ho
  obtain ⟨o', ho', e1, e2, e3⟩ := h1 h o ho
  obtain ⟨o'', ho'', f1, f2, f3⟩ := h2 h o' ho'
  refine ⟨o'', ho'', by rw [f1, e1], fun hc => f2 (e2 hc), fun hc => ?_⟩
  rw [f3 hc]
  apply e3
  cases hc' : o'.canonical
  · rfl
  · have := f2 hc'; rw [hc] at this; cases this

theorem ReadableT.keep {t : Time} {h : Nat} {y : NodeId} (hr : ReadableT sp db m t h y)
    (hk : m.KeepRead m') : ReadableT sp db m' t h y := by
  obtain ⟨o, ho, hn, hc⟩ := hr
  obtain ⟨o', ho', e1, e2, e3⟩ := hk h o ho
  refine ⟨o', ho', by rw [e1, hn], ?_⟩
  cases hc' : o'.canonical with
  | true => exact Or.inl rfl
  | false =>
    rcases hc with hc | ⟨r, w, hp, hw, hg⟩
    · rw [e2 hc] at hc'; cases hc'
    · exact Or.inr ⟨r, w, by rw [e3 hc', hp], hw, hg⟩

theorem SlotHist.keep {t : Time} {x y : NodeId} {sl : Slot} (hs : SlotHist sp S0 db m t x y sl)
    (hk : m.KeepRead m') (he : m'.s = m.s) : SlotHist sp S0 db m' t x y sl := by
  cases sl with
  | mem h' => exact ReadableT.keep (sp := sp) (db := db) hs hk
  | stream r =>
    rcases hs with ⟨r', w, h1, h2, h3⟩ | hd
    · exact Or.inl ⟨r', w, by rw [he]; exact h1, h2, h3⟩
    · exact Or.inr hd

/-- The invariant carries over to a memory that keeps what reads need, if every
canonical object of the new memory either was canonical with the same slot, or
has a slot as the invariant asks. -/
theorem HInv.transfer (hh : HInv sp db S0 k m) (hk : m.KeepRead m') (he : m'.s = m.s)
    (hcan : ∀ h o', m'.obj? h = some o' → o'.canonical = true → ∀ t ≤ k,
      reachable sp db.P t o'.node = true → ∀ y ∈ sp.live (o'.hist.upTo t),
        (∃ o, m.obj? h = some o ∧ o.canonical = true ∧ o.node = o'.node ∧
          o.hist.upTo t = o'.hist.upTo t ∧ o'.slot? y = o.slot? y) ∨
        ∃ sl, o'.slot? y = some sl ∧ SlotHist sp S0 db m' t o'.node y sl) :
    HInv sp db S0 k m' := by
  intro h o' ho' hc t ht hr y hy
  rcases hcan h o' ho' hc t ht hr y hy with ⟨o, ho, hco, hn, hup, hsl⟩ | h2
  · obtain ⟨sl, hsl0, hsh⟩ := hh h o ho hco t ht (by rw [hn]; exact hr) y (by rw [hup]; exact hy)
    refine ⟨sl, by rw [hsl]; exact hsl0, ?_⟩
    rw [← hn]
    exact hsh.keep hk he
  · exact h2

end Keep

/-! ## Good versions -/

section Good

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

/-- A written node not in D, reachable at t ≤ k, has a latest version, good for
t: it is clean (INV-2). -/
theorem Inv.clean_good (hinv : Inv sp db k) (hls : LiveSub sp) {y : NodeId} (hyD : inD db.D y = false)
    (hyw : written sp y = true) {t : Time} (ht : t ≤ k) (hr : reachable sp db.P t y = true) :
    ∃ v, db.S.lv y = some v ∧ good sp db.S db.P t v = true := by
  obtain ⟨ny, hny⟩ := Option.isSome_iff_exists.mp (Reach.isSome ((reachable_iff _ _ _ _).mp hr))
  cases hd : ny.isData with
  | true =>
    obtain ⟨v, hv, -⟩ := hinv.dataV y ny hny hd
    exact ⟨v, hv, hinv.good_data hls hny hd hv t⟩
  | false =>
    have hidx : isIndex db.P y = true := by simp [isIndex, hny, hd]
    have hcl : dirty sp db.S db.P k y = false := by
      cases hdy : dirty sp db.S db.P k y with
      | false => rfl
      | true => have := hinv.inv2 y hidx hyw hdy; rw [hyD] at this; cases this
    unfold dirty at hcl
    cases hl : db.S.lv y with
    | none => rw [hl] at hcl; cases hcl
    | some v =>
      rw [hl] at hcl
      simp only [List.any_eq_false, List.mem_range] at hcl
      refine ⟨v, rfl, ?_⟩
      have := hcl t (by omega)
      simp only [hr, Bool.true_and, Bool.not_eq_true'] at this
      cases hg : good sp db.S db.P t v
      · rw [hg] at this; exact absurd rfl this
      · rfl

theorem ruleRRef_some_some (S0 : Stream V T) (s : Nat) (y : NodeId) (r : Nat) :
    ∃ r', ruleRRef S0 s y (some r) = some r' := by
  unfold ruleRRef
  cases newest S0 s y with
  | none => exact ⟨r, rfl⟩
  | some w =>
    simp only
    split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

/-- A reference to a version of y good for t names, after Rule R, a version good
for t (lemma M). -/
theorem Inv.goodRef_of (hinv : Inv sp db k) (hls : LiveSub sp) (hpre : S0 <+: db.S) (s : Nat)
    {y : NodeId} {r1 : Nat} {u : Version V} (hu : db.S.versionAt r1 y = some u) {t : Time}
    (hg : good sp db.S db.P t u = true) {p : Nat} (hp : r1 ≤ p) {u' : Version V}
    (hu' : db.S.versionAt p y = some u') :
    ∃ r' w, ruleRRef S0 s y (some p) = some r' ∧ db.S.versionAt r' y = some w ∧
      good sp db.S db.P t w = true := by
  obtain ⟨r', hr'⟩ := ruleRRef_some_some S0 s y p
  obtain ⟨⟨w, hw⟩, -⟩ := hinv.ruleR_bound hpre s (r := some p)
    (fun r'' h => by simp only [Option.some.injEq] at h; subst h; exact ⟨u', hu'⟩) hr'
  have hle := ruleRRef_some_ge hr'
  exact ⟨r', w, hr', hw, hinv.newer hls (u.level + 1) r1 r' y u w (by omega) hu hw (by omega) t hg⟩

/-- A slot that serializes y's latest version, good for t, is as a read at t
needs it. -/
theorem EInv.slotHist_of_ref (hinv : Inv sp db k) (hm : EInv sp db S0 k m) {h : Nat} {o : Obj V}
    (ho : m.obj? h = some o) {y : NodeId} {sl : Slot} (hsl : o.slot? y = some sl) {v : Version V}
    (hv : db.S.lv y = some v) {t : Time} (hg : good sp db.S db.P t v = true)
    (href : slotRefOf S0 m y sl = some v.recNo) (x : NodeId) : SlotHist sp S0 db m t x y sl := by
  have hva := hinv.lv_at hv
  cases sl with
  | mem h' =>
    obtain ⟨o', ho', hn'⟩ := hm.slotsNode h o ho y h' hsl
    simp only [slotRefOf, ho', Option.bind_some] at href
    refine ⟨o', ho', hn', ?_⟩
    cases hc : o'.canonical with
    | true => exact Or.inl rfl
    | false =>
      obtain ⟨r, w, hp, hw, -⟩ := hm.snap h' o' ho' hc
      rw [hp, Option.some.injEq] at href
      subst href
      rw [hn', hva, Option.some.injEq] at hw
      subst hw
      exact Or.inr ⟨v.recNo, v, hp, hva, hg⟩
  | stream r =>
    simp only [slotRefOf] at href
    exact Or.inl ⟨v.recNo, v, href, hva, hg⟩

/-- The slot of a canonical object that serializes the pointee's latest version,
for a pointee not in D, reachable at t: as a read at t needs it. -/
theorem EInv.slotHist_clean (hinv : Inv sp db k) (hls : LiveSub sp) (hm : EInv sp db S0 k m) {h : Nat}
    {o : Obj V} (ho : m.obj? h = some o) {y : NodeId} {sl : Slot} (hsl : o.slot? y = some sl)
    (hyD : inD db.D y = false) (hyw : written sp y = true) {t : Time} (ht : t ≤ k)
    (hry : reachable sp db.P t y = true) (href : slotRefOf S0 m y sl = (db.S.lv y).map (·.recNo))
    (x : NodeId) : SlotHist sp S0 db m t x y sl := by
  obtain ⟨v, hv, hg⟩ := hinv.clean_good hls hyD hyw ht hry
  rw [hv] at href
  exact hm.slotHist_of_ref hinv ho hsl hv hg href x

/-- A snapshot of a version good for t: its slots for the live children at t are
as a read at t needs them, without INV-SLOT's second half. -/
theorem EInv.snap_hist (hinv : Inv sp db k) (hls : LiveSub sp) (hm : EInv sp db S0 k m) {h : Nat}
    {o : Obj V} (ho : m.obj? h = some o) (hc : o.canonical = false) {r : Nat} {w : Version V}
    (hp : o.pos = some r) (hw : db.S.versionAt r o.node = some w) {t : Time}
    (hg : good sp db.S db.P t w = true) {y : NodeId} (hy : y ∈ sp.live (o.hist.upTo t)) :
    ∃ sl, o.slot? y = some sl ∧ (∀ x, SlotHist sp S0 db m t x y sl) ∧
      (∀ r0, sl = Slot.stream r0 → GoodRef sp S0 db m t y r0) := by
  obtain ⟨r0, w0, hp0, hw0, hh, -, -, hex, hss⟩ := hm.snap h o ho hc
  rw [hp, Option.some.injEq] at hp0
  subst hp0
  rw [hw, Option.some.injEq] at hw0
  subst hw0
  rw [hh] at hy
  rw [good_iff] at hg
  obtain ⟨-, hch⟩ := hg
  obtain ⟨r1, u, hr1, hu, -, hgu⟩ := hch y hy
  obtain ⟨sl, hsl⟩ := Option.isSome_iff_exists.mp (hex y (by rw [hh]; exact mem_pointees_of_live hls hy))
  -- What Rule R gives for w's reference.
  obtain ⟨q0, hq0⟩ := ruleRRef_some_some S0 m.s y r1
  have hq0le := ruleRRef_some_ge hq0
  have hgood : ∀ p, q0 ≤ p → ∀ u', db.S.versionAt p y = some u' →
      ∃ r' w', ruleRRef S0 m.s y (some p) = some r' ∧ db.S.versionAt r' y = some w' ∧
        good sp db.S db.P t w' = true :=
    fun p hp u' hu' => hinv.goodRef_of hls hm.pre m.s hu hgu (by omega) hu'
  obtain ⟨⟨uq, huq⟩, -⟩ := hinv.ruleR_bound hm.pre m.s (r := some r1)
    (fun r'' h => by simp only [Option.some.injEq] at h; subst h; exact ⟨u, hu⟩) hq0
  have hstr : ∀ r0, sl = Slot.stream r0 → GoodRef sp S0 db m t y r0 := by
    intro r0 hr0
    subst hr0
    rcases hss y _ hsl with h1 | ⟨p, u', h1, h2, h3⟩ | ⟨h', o', h1, -⟩
    · simp only [Slot.stream.injEq] at h1
      rw [h1, hr1]
      exact ⟨q0, uq, hq0, huq, hinv.newer hls (u.level + 1) r1 q0 y u uq (by omega) hu huq hq0le t hgu⟩
    · simp only [Slot.stream.injEq] at h1
      subst h1
      rw [hr1] at h3
      exact hgood p (h3 q0 hq0) u' h2
    · cases h1
  refine ⟨sl, hsl, fun x => ?_, hstr⟩
  cases sl with
  | stream r0 => exact Or.inl (hstr r0 rfl)
  | mem h' =>
    rcases hss y _ hsl with h1 | ⟨p, u', h1, -⟩ | ⟨hq, o', h1, ho', hn', hc'⟩
    · cases h1
    · cases h1
    · simp only [Slot.mem.injEq] at h1
      subst h1
      refine ⟨o', ho', hn', ?_⟩
      cases hco : o'.canonical with
      | true => exact Or.inl rfl
      | false =>
        rcases hc' with hc' | ⟨p, hp', hle⟩
        · rw [hco] at hc'; cases hc'
        obtain ⟨p2, w2, hp2, hw2, -⟩ := hm.snap h' o' ho' hco
        rw [hp', Option.some.injEq] at hp2
        subst hp2
        rw [hn'] at hw2
        rw [hr1] at hle
        have hle' := hle q0 hq0
        exact Or.inr ⟨p, w2, hp', hw2,
          hinv.newer hls (u.level + 1) r1 p y u w2 (by omega) hu hw2 (by omega) t hgu⟩

/-- A live child at t of a node reachable at t is reachable at t, below it, and
not the root. -/
theorem Inv.reach_child (hinv : Inv sp db k) (hls : LiveSub sp) {x : NodeId} {n : Node V}
    (hn : db.P.get? x = some n) {t : Time} (hr : reachable sp db.P t x = true) {y : NodeId}
    (hy : y ∈ sp.live (n.hist.upTo t)) :
    reachable sp db.P t y = true ∧ y ≠ root ∧ ∃ ny, db.P.get? y = some ny ∧ ny.level < n.level := by
  obtain ⟨e, he, hye⟩ := hls _ _ hy
  obtain ⟨ny, hny, hlt⟩ := hinv.ptrs x n hn e (mem_upTo.mp he).1 y hye
  refine ⟨?_, hinv.ptr_ne_root hn (mem_upTo.mp he).1 hye, ny, hny, hlt⟩
  rw [reachable_iff] at hr ⊢
  exact Reach.child hr hn hy hny hlt

/-- The same, for a live child at t of a canonical object. -/
theorem EInv.reach_child (hinv : Inv sp db k) (hls : LiveSub sp) (hm : EInv sp db S0 k m) {h : Nat}
    {o : Obj V} (ho : m.obj? h = some o) (hc : o.canonical = true) {t : Time}
    (hr : reachable sp db.P t o.node = true) {y : NodeId} (hy : y ∈ sp.live (o.hist.upTo t)) :
    reachable sp db.P t y = true ∧ y ≠ SIS.root ∧ written sp y = true := by
  obtain ⟨n, hn, hh, -, -⟩ := hm.cc h o ho hc
  rw [hh] at hy
  obtain ⟨h1, h2, -⟩ := hinv.reach_child hls hn hr hy
  exact ⟨h1, h2, written_of_ne_root sp h2⟩

end Good

/-! ## The cache operations -/

section Cache

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

/-- What the memory after the reader's follow holds: hp's object with the slot
for y naming h1, m's other objects, and maybe a new snapshot. -/
theorem reached4_back (hm : EInv sp db S0 k m) {hp : Nat} {y : NodeId} {m1 : Mem V} {h1 : Nat}
    (h : m.reached4 sp S0 db.S hp y = some (m1, h1)) {op : Obj V} (hop : m.obj? hp = some op)
    {h' : Nat} {o' : Obj V} (ho' : (m1.swz hp y h1).obj? h' = some o') :
    (h' = hp ∧ o' = op.setSlot y (Slot.mem h1)) ∨ (h' ≠ hp ∧ m.obj? h' = some o') ∨
      (h' ≠ hp ∧ h' = m.next ∧ o'.canonical = false) := by
  obtain ⟨op0, sl, hop0, hsl, hcase⟩ := reached4_cases h
  rw [hop, Option.some.injEq] at hop0
  subst hop0
  have hm1 : m1.obj? hp = some op ∧ ∀ h'', m1.obj? h'' = some o' → h'' ≠ hp →
      m.obj? h'' = some o' ∨ (h'' = m.next ∧ o'.canonical = false) := by
    rcases hcase with ⟨-, rfl, -⟩ | ⟨r, -, -, rfl⟩ | ⟨r, r', w, -, -, -, -, rfl, -⟩
    · exact ⟨hop, fun _ h2 _ => Or.inl h2⟩
    · exact ⟨hop, fun _ h2 _ => Or.inl h2⟩
    · have hpn : hp ≠ m.next := by
        intro he; subst he; rw [hm.fresh _ (Nat.le_refl _)] at hop; cases hop
      refine ⟨by rw [Mem.obj?_addObj]; simp only [hpn, ↓reduceIte]; exact hop, fun h'' h2 _ => ?_⟩
      rw [Mem.obj?_addObj] at h2
      split at h2
      · rename_i he
        simp only [Option.some.injEq] at h2
        subst h2
        exact Or.inr ⟨he, (Obj.ofVersion_fields sp w none).2.2.2.2.1⟩
      · exact Or.inl h2
  unfold Mem.swz at ho'
  rw [hm1.1, Mem.obj?_setObj] at ho'
  split at ho'
  · rename_i he
    simp only [Option.some.injEq] at ho'
    exact Or.inl ⟨he, ho'.symm⟩
  · rename_i he
    rcases hm1.2 h' ho' he with h2 | ⟨h2, h3⟩
    · exact Or.inr (Or.inl ⟨he, h2⟩)
    · exact Or.inr (Or.inr ⟨he, h2, h3⟩)

theorem swz_s {m1 : Mem V} {hp : Nat} {y : NodeId} {h1 : Nat} : (m1.swz hp y h1).s = m1.s := by
  unfold Mem.swz
  split
  · rfl
  · rfl

/-- The reader's follow of any slot, before the writer's promotion, keeps the
invariant; and the object reached can be read at every time at which the slot
was as a read needs it. -/
theorem HInv.reached4 (hinv : Inv sp db k) (hm : EInv sp db S0 k m) (hh : HInv sp db S0 k m)
    {hp : Nat} {y : NodeId} {m1 : Mem V} {h1 : Nat} (h : m.reached4 sp S0 db.S hp y = some (m1, h1)) :
    HInv sp db S0 k (m1.swz hp y h1) ∧ m.KeepRead (m1.swz hp y h1) ∧ (m1.swz hp y h1).s = m.s ∧
      ∃ op sl, m.obj? hp = some op ∧ op.slot? y = some sl ∧
        ∀ t x, SlotHist sp S0 db m t x y sl → ReadableT sp db (m1.swz hp y h1) t h1 y := by
  obtain ⟨op, sl, hop, hsl, hcase⟩ := reached4_cases h
  obtain ⟨-, -, hfr2⟩ := hm.reached4_frame hop h
  have hs : (m1.swz hp y h1).s = m.s := by
    rw [swz_s]
    rcases hcase with ⟨-, rfl, -⟩ | ⟨r, -, -, rfl⟩ | ⟨r, r', w, -, -, -, -, rfl, -⟩
    · rfl
    · rfl
    · rfl
  have hk : m.KeepRead (m1.swz hp y h1) := fun h o ho => by
    obtain ⟨o', ho', e1, -, -, -, e5, e6, -⟩ := hfr2 h o ho
    exact ⟨o', ho', e1, e6, fun _ => e5⟩
  have hreach : ∀ t x, SlotHist sp S0 db m t x y sl → ReadableT sp db (m1.swz hp y h1) t h1 y := by
    intro t x hsh
    rcases hcase with ⟨rfl, rfl, -⟩ | ⟨r, rfl, hc, rfl⟩ | ⟨r, r', w, rfl, hc, hr, hw, rfl, rfl⟩
    · exact ReadableT.keep (sp := sp) (db := db) hsh hk
    · obtain ⟨o0, ho0, hc0, hn0⟩ := hm.obj_of_canonicalOf hc
      exact ReadableT.keep ⟨o0, ho0, hn0, Or.inl hc0⟩ hk
    · rcases hsh with ⟨r'', w'', e1, e2, e3⟩ | ⟨hyD, -⟩
      · rw [hr, Option.some.injEq] at e1
        subst e1
        rw [hw, Option.some.injEq] at e2
        subst e2
        have hpn : hp ≠ m.next := by
          intro he; subst he; rw [hm.fresh _ (Nat.le_refl _)] at hop; cases hop
        have hnew : ((m.addObj (Obj.ofVersion sp w none)).1.swz hp y m.next).obj? m.next =
            some (Obj.ofVersion sp w none) := by
          unfold Mem.swz
          rw [Mem.obj?_addObj]
          simp only [hpn, ↓reduceIte, hop]
          rw [Mem.obj?_setObj]
          simp only [Ne.symm hpn, ↓reduceIte, Mem.obj?_addObj]
        obtain ⟨f1, -, -, -, -, f6⟩ := Obj.ofVersion_fields sp w none
        obtain ⟨hwn, hwr, -⟩ := hinv.version_node hw
        refine ⟨_, hnew, by rw [f1, hwn], Or.inr ⟨r', w, by rw [f6, hwr], hw, e3⟩⟩
      · have := hm.dCanon y hyD
        rw [hc] at this; cases this
  refine ⟨hh.transfer hk hs ?_, hk, hs, op, sl, hop, hsl, hreach⟩
  intro h' o' ho' hc t ht hr z hz
  rcases reached4_back hm h hop ho' with ⟨rfl, rfl⟩ | ⟨-, h2⟩ | ⟨-, -, h3⟩
  · have hco : op.canonical = true := hc
    by_cases hzy : z = y
    · subst hzy
      right
      refine ⟨Slot.mem h1, by rw [slot?_setSlot_of hsl]; simp, ?_⟩
      obtain ⟨sl', hsl', hsh⟩ := hh h' op hop hco t ht hr z hz
      rw [hsl, Option.some.injEq] at hsl'
      subst hsl'
      exact hreach t _ hsh
    · left
      exact ⟨op, hop, hco, rfl, rfl, by rw [slot?_setSlot_of hsl]; simp [hzy]⟩
  · exact Or.inl ⟨o', h2, hc, rfl, rfl, rfl⟩
  · rw [hc] at h3; cases h3

/-- A reader's follow of any slot keeps the invariant. -/
theorem HInv.follow4_reader (hinv : Inv sp db k) (hm : EInv sp db S0 k m) (hh : HInv sp db S0 k m)
    (hp : Nat) (y : NodeId) : HInv sp db S0 k (m.follow4 sp S0 db.S hp y false).1 := by
  rw [follow4_eq]
  cases h : m.reached4 sp S0 db.S hp y with
  | none => exact hh
  | some p =>
    obtain ⟨m1, h1⟩ := p
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact (hh.reached4 hinv hm h).1

/-- A read at any time, from any object, keeps both invariants. -/
theorem HInv.readAt4 (hinv : Inv sp db k) :
    ∀ (fuel : Nat) (m : Mem V) (t : Time) (h : Nat), EInv sp db S0 k m → HInv sp db S0 k m →
      EInv sp db S0 k (m.readAt4 sp S0 db.S fuel t h).1 ∧ HInv sp db S0 k (m.readAt4 sp S0 db.S fuel t h).1 := by
  intro fuel
  induction fuel with
  | zero => intro m t h hm hh; exact ⟨hm, hh⟩
  | succ fuel ih =>
    intro m t h hm hh
    unfold Mem.readAt4
    cases ho : m.obj? h with
    | none => exact ⟨hm, hh⟩
    | some o =>
      simp only
      apply foldl_inv1 _ (fun m => EInv sp db S0 k m ∧ HInv sp db S0 k m) _ _ _ ⟨hm, hh⟩
      intro acc z ⟨hacc, hhacc⟩
      have hf := hacc.follow4_reader hinv h z
      have hfh := hhacc.follow4_reader hinv hacc h z
      generalize acc.1.follow4 sp S0 db.S h z false = res at hf hfh ⊢
      obtain ⟨m1, oh⟩ := res
      cases oh with
      | none => exact ⟨hf, hfh⟩
      | some h1 =>
        simp only
        cases ho1 : m1.obj? h1 with
        | none => exact ⟨hf, hfh⟩
        | some o1 =>
          simp only
          split
          · exact ih m1 t h1 hf hfh
          · exact ⟨hf, hfh⟩

theorem HInv.read4 (hinv : Inv sp db k) (hm : EInv sp db S0 k m) (hh : HInv sp db S0 k m) (t : Time) :
    HInv sp db S0 k (m.read4 sp S0 db.S t).1 := by
  unfold Mem.read4
  cases m.obj? m.root with
  | none => exact hh
  | some o => exact (HInv.readAt4 hinv _ m t _ hm hh).2

/-- Unswizzling keeps the invariant: the stream slot names the position of the
object, which is y's latest version, clean, or a snapshot's version. -/
theorem HInv.unswizzle (hinv : Inv sp db k) (hls : LiveSub sp) (hm : EInv sp db S0 k m)
    (hh : HInv sp db S0 k m) (hp : Nat) (y : NodeId) : HInv sp db S0 k (m.unswizzle db.D hp y) := by
  unfold Mem.unswizzle
  cases hop : m.obj? hp with
  | none => exact hh
  | some op =>
    simp only
    cases hsl : op.slot? y with
    | none => exact hh
    | some sl =>
      cases sl with
      | stream r => exact hh
      | mem h =>
        simp only
        cases ho : m.obj? h with
        | none => exact hh
        | some o =>
          simp only
          split
          · rename_i hdet
            obtain ⟨o0, ho0, hroot, hnp, p, hpos⟩ := Mem.detachable_some hdet
            rw [ho, Option.some.injEq] at ho0
            subst ho0
            obtain ⟨o1, ho1, hny⟩ := hm.slotsNode hp op hop y h hsl
            rw [ho, Option.some.injEq] at ho1
            subst ho1
            rw [hpos]
            have hk : m.KeepRead (m.setObj hp (op.setSlot y (Slot.stream (some p)))) := by
              intro h' o' ho'
              rw [Mem.obj?_setObj]
              split
              · rename_i he; subst he
                rw [hop, Option.some.injEq] at ho'; subst ho'
                exact ⟨_, rfl, rfl, id, fun _ => rfl⟩
              · exact ⟨o', ho', rfl, id, fun _ => rfl⟩
            apply hh.transfer hk rfl
            intro h' o' ho' hc t ht hr z hz
            rw [Mem.obj?_setObj] at ho'
            split at ho'
            · rename_i he; subst he
              simp only [Option.some.injEq] at ho'
              subst ho'
              have hco : op.canonical = true := hc
              by_cases hzy : z = y
              · subst hzy
                right
                refine ⟨Slot.stream (some p), by rw [slot?_setSlot_of hsl]; simp, Or.inl ?_⟩
                obtain ⟨sl', hsl', hsh⟩ := hh h' op hop hco t ht hr z hz
                rw [hsl, Option.some.injEq] at hsl'
                subst hsl'
                obtain ⟨o2, ho2, -, hc2⟩ := hsh
                rw [ho, Option.some.injEq] at ho2
                subst ho2
                rw [← hny]
                show ∃ r' w, ruleRRef S0 m.s o.node (some p) = some r' ∧ db.S.versionAt r' o.node = some w ∧
                  good sp db.S db.P t w = true
                rw [← hny] at hz
                rcases hc2 with hc2 | ⟨r1, w1, hp1, hw1, hg1⟩
                · -- y's canonical object: not pinned, so y is not in D; at y's latest version
                  have hyD : inD db.D o.node = false := by
                    cases hyd : inD db.D o.node with
                    | false => rfl
                    | true => exact absurd ⟨hc2, hyd⟩ hnp
                  have hcy := hm.canonicalOf_of ho hc2
                  have hposl := hm.pos.lv0 hcy ho
                  obtain ⟨hry, -, hyw⟩ := hm.reach_child hinv hls hop hco hr hz
                  obtain ⟨v, hv, hg⟩ := hinv.clean_good hls hyD hyw ht hry
                  rw [hpos, hv] at hposl
                  simp only [Option.map_some, Option.some.injEq] at hposl
                  subst hposl
                  refine ⟨v.recNo, v, ?_, hinv.lv_at hv, hg⟩
                  have := hinv.ruleR_lv0 hm.pre m.s o.node
                  rw [hv] at this
                  exact this
                · rw [hpos, Option.some.injEq] at hp1
                  subst hp1
                  rw [hny]
                  exact hinv.goodRef_of hls hm.pre _ hw1 hg1 (Nat.le_refl _) hw1
              · left
                exact ⟨op, hop, hco, rfl, rfl, by rw [slot?_setSlot_of hsl]; simp [hzy]⟩
            · exact Or.inl ⟨o', ho', hc, rfl, rfl, rfl⟩
          · exact hh

/-- Release keeps the invariant: no memory slot names the object released. -/
theorem HInv.release (hh : HInv sp db S0 k m) (h : Nat) :
    HInv sp db S0 k (m.release db.D h) := by
  by_cases he : m.eligible db.D h = true
  · have hs : (m.release db.D h).s = m.s := by unfold Mem.release; simp only [he, ↓reduceIte]
    have hinc : m.incoming h = false := by
      unfold Mem.eligible at he
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at he
      exact he.2
    intro h' o' ho' hc t ht hr y hy
    rw [release_obj? db.D he] at ho'
    split at ho'
    · cases ho'
    · rename_i hne
      obtain ⟨sl, hsl, hsh⟩ := hh h' o' ho' hc t ht hr y hy
      refine ⟨sl, hsl, ?_⟩
      cases sl with
      | mem h2 =>
        have h2h : h2 ≠ h := Mem.incoming_false hinc ho' hsl
        obtain ⟨o2, ho2, hn2, hc2⟩ := hsh
        exact ⟨o2, by rw [release_obj? db.D he]; simp only [h2h, ↓reduceIte]; exact ho2, hn2, hc2⟩
      | stream r =>
        rcases hsh with ⟨r', w, e1, e2, e3⟩ | hd
        · exact Or.inl ⟨r', w, by rw [hs]; exact e1, e2, e3⟩
        · exact Or.inr hd
  · have : m.release db.D h = m := by unfold Mem.release; simp only [he, Bool.false_eq_true, ↓reduceIte]
    rw [this]; exact hh

/-- Every cache operation keeps both invariants. -/
theorem HInv.cacheOp (hinv : Inv sp db k) (hls : LiveSub sp) (hm : EInv sp db S0 k m)
    (hh : HInv sp db S0 k m) (op : CacheOp) : HInv sp db S0 k (m.cacheOp sp S0 db.S db.D op) := by
  cases op with
  | read t => exact hh.read4 hinv hm t
  | unswizzle h y => exact hh.unswizzle hinv hls hm h y
  | release h => exact hh.release h

theorem HInv.cacheOps (hinv : Inv sp db k) (hls : LiveSub sp) (ops : List CacheOp) :
    ∀ m, EInv sp db S0 k m → HInv sp db S0 k m →
      HInv sp db S0 k (ops.foldl (Mem.cacheOp sp S0 db.S db.D) m) := by
  induction ops with
  | nil => intro m _ hh; exact hh
  | cons op ops ih =>
    intro m hm hh
    exact ih _ (hm.cacheOp hinv op) (hh.cacheOp hinv hls hm op)

end Cache

end SIS
