/-
Proofs for stage 2 (bergdb item 001, WP E3), part 7: a read at the last time k
through the Level 4 loader gives P@k (the writer's view, which the change of the
next transaction comes from). Every object it reaches is its node's canonical
object, or the snapshot of the latest version of a node not in D.
-/
import SIS.Proof.EvictPath

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

section Read

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

/-- Object h, of node y, can be read at the last time k: it is canonical, or the
snapshot at the latest version of a written node not in D. -/
def Readable4 (sp : Spec V T) (db : DB V T) (m : Mem V) (h : Nat) (y : NodeId) : Prop :=
  ∃ o, m.obj? h = some o ∧ o.node = y ∧
    (o.canonical = true ∨
      (inD db.D y = false ∧ written sp y = true ∧ o.pos = (db.S.lv y).map (·.recNo)))

/-- A slot for y that a read at k may follow: a memory slot to y's canonical
object, for y in D; otherwise one that serializes y's latest version. -/
def SlotGood4 (S0 : Stream V T) (db : DB V T) (m : Mem V) (y : NodeId) (sl : Slot) : Prop :=
  (inD db.D y = true ∧ ∃ h', sl = Slot.mem h' ∧ m.canonicalOf y = some h') ∨
    (inD db.D y = false ∧ slotRefOf S0 m y sl = (db.S.lv y).map (·.recNo))

theorem Readable4.keepCore {m m' : Mem V} {h : Nat} {y : NodeId} (hr : Readable4 sp db m h y)
    (hk : m.KeepCore m') : Readable4 sp db m' h y := by
  obtain ⟨o, ho, hn, hc⟩ := hr
  obtain ⟨o', ho', hcore⟩ := hk h o ho
  have e1 : o'.node = o.node := congrArg (fun c => c.1) hcore
  have e5 : o'.canonical = o.canonical := congrArg (fun c => c.2.2.2.2.1) hcore
  have e6 : o'.pos = o.pos := congrArg (fun c => c.2.2.2.2.2) hcore
  exact ⟨o', ho', by rw [e1, hn], by rw [e5, e6]; exact hc⟩

/-- What a readable object holds: its node's whole history, level and kind. -/
theorem EInv.readable_facts (hinv : Inv sp db k) (hm : EInv sp db S0 k m) {h : Nat} {y : NodeId}
    (hrd : Readable4 sp db m h y) {n : Node V} (hn : db.P.get? y = some n)
    (hr : reachable sp db.P k y = true) :
    ∃ o, m.obj? h = some o ∧ o.node = y ∧ o.hist = n.hist ∧ o.level = n.level ∧ o.isData = n.isData := by
  obtain ⟨o, ho, hoy, hc⟩ := hrd
  refine ⟨o, ho, hoy, ?_⟩
  rcases hc with hc | ⟨hyD, hyw, hpos⟩
  · obtain ⟨n', hn', h1, h2, h3⟩ := hm.cc h o ho hc
    rw [hoy, hn, Option.some.injEq] at hn'
    subst hn'
    exact ⟨h1, h2, h3⟩
  · cases hco : o.canonical with
    | true =>
      obtain ⟨n', hn', h1, h2, h3⟩ := hm.cc h o ho hco
      rw [hoy, hn, Option.some.injEq] at hn'
      subst hn'
      exact ⟨h1, h2, h3⟩
    | false =>
      obtain ⟨v, hv, hvh, hvl, hvd⟩ := hinv.lv_whole hn hyw hyD hr
      obtain ⟨r1, w1, e1, e2, e3, e4, e5, -⟩ := hm.snap h o ho hco
      rw [hpos, hv] at e1
      simp only [Option.map_some, Option.some.injEq] at e1
      rw [← e1, hoy, hinv.lv_at hv, Option.some.injEq] at e2
      subst e2
      exact ⟨by rw [e3, hvh], by rw [e4, hvl], by rw [e5, hvd]⟩

/-- The slots of a readable object of a node current at k, for its live children:
good for a read at k. -/
theorem EInv.readable_slot (hinv : Inv sp db k) (hev : EvLogic sp db k) (hm : EInv sp db S0 k m)
    {h : Nat} {y : NodeId} (hrd : Readable4 sp db m h y) (hr : reachable sp db.P k y = true)
    {o : Obj V} (ho : m.obj? h = some o) {z : NodeId} (hz : z ∈ sp.live o.hist) (hls : LiveSub sp) :
    ∃ sl, o.slot? z = some sl ∧ SlotGood4 S0 db m z sl := by
  obtain ⟨o1, ho1, hoy, hc⟩ := hrd
  rw [ho, Option.some.injEq] at ho1
  subst ho1
  cases hco : o.canonical with
  | true =>
    obtain ⟨sl, hsl, hli⟩ := hm.live h o ho hco (by rw [hoy]; exact hr) z hz
    refine ⟨sl, hsl, ?_⟩
    cases hzD : inD db.D z with
    | true => exact Or.inl ⟨hzD, hli.1 hzD⟩
    | false => exact Or.inr ⟨hzD, hli.2 hzD⟩
  | false =>
    rcases hc with hc | ⟨hyD, hyw, hpos⟩
    · rw [hco] at hc; cases hc
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (Reach.isSome ((reachable_iff _ _ _ _).mp hr))
    obtain ⟨v, hv, hvh, -, -⟩ := hinv.lv_whole hn hyw hyD hr
    obtain ⟨r1, w1, e1, e2, e3, -, -, e6, e7⟩ := hm.snap h o ho hco
    rw [hpos, hv] at e1
    simp only [Option.map_some, Option.some.injEq] at e1
    rw [← e1, hoy, hinv.lv_at hv, Option.some.injEq] at e2
    subst e2
    have hzp : z ∈ pointees sp n.hist := by
      rw [← hvh, ← e3]; exact mem_pointees_of_live' hls hz
    obtain ⟨hzD, v', hv', href⟩ := hev.clean y n hyw hr hn hyD z hzp
    rw [hv, Option.some.injEq] at hv'
    subst hv'
    obtain ⟨sl, hsl⟩ := Option.isSome_iff_exists.mp (e6 z (by rw [e3, hvh]; exact hzp))
    exact ⟨sl, hsl, Or.inr ⟨hzD, hm.snapSlot_clean hinv (e7 z sl hsl) href⟩⟩

/-- A reader's follow of a good slot reaches a readable object; the invariant and
every object's core are kept. -/
theorem EInv.follow_good (hinv : Inv sp db k) (hm : EInv sp db S0 k m) {hp : Nat} {op : Obj V}
    (hop : m.obj? hp = some op) {z : NodeId} {sl : Slot} (hsl : op.slot? z = some sl)
    (hg : SlotGood4 S0 db m z sl) (hzw : written sp z = true) (hzne : z ≠ op.node)
    (hzr : reachable sp db.P k z = true) :
    ∃ m1 h1, m.follow4 sp S0 db.S hp z false = (m1, some h1) ∧ EInv sp db S0 k m1 ∧
      m.KeepCore m1 ∧ Readable4 sp db m1 h1 z := by
  -- The object reached, and that it is not hp's.
  have hne : ∀ h' o', m.obj? h' = some o' → o'.node = z → h' ≠ hp := by
    intro h' o' ho' hn' he
    subst he
    rw [hop, Option.some.injEq] at ho'
    subst ho'
    exact hzne hn'.symm
  have hkeep : ∀ (m1 : Mem V) h1, m.reached4 sp S0 db.S hp z = some (m1, h1) →
      m.KeepCore (m1.swz hp z h1) := by
    intro m1 h1 hrc
    obtain ⟨-, -, hfr⟩ := hm.reached4_frame hop hrc
    intro h o ho
    obtain ⟨o', ho', e1, e2, e3, e4, e5, -, -⟩ := hfr h o ho
    refine ⟨o', ho', ?_⟩
    -- the reader's follow does not promote: the canonical flags stay too
    obtain ⟨op0, sl0, hop0, hsl0, hcase⟩ := reached4_cases hrc
    have hc' : o'.canonical = o.canonical := by
      unfold Mem.swz at ho'
      rcases hcase with ⟨-, rfl, -⟩ | ⟨r, -, -, rfl⟩ | ⟨r, r', w, -, -, -, -, rfl, -⟩
      · rw [hop] at ho'
        rw [Mem.obj?_setObj] at ho'
        split at ho'
        · rename_i he; subst he; rw [hop, Option.some.injEq] at ho; subst ho
          simp only [Option.some.injEq] at ho'; subst ho'; rfl
        · rw [ho, Option.some.injEq] at ho'; subst ho'; rfl
      · rw [hop] at ho'
        rw [Mem.obj?_setObj] at ho'
        split at ho'
        · rename_i he; subst he; rw [hop, Option.some.injEq] at ho; subst ho
          simp only [Option.some.injEq] at ho'; subst ho'; rfl
        · rw [ho, Option.some.injEq] at ho'; subst ho'; rfl
      · have hpn : hp ≠ m.next := by
          intro he; subst he; rw [hm.fresh _ (Nat.le_refl _)] at hop; cases hop
        have hop1 : (m.addObj (Obj.ofVersion sp w none)).1.obj? hp = some op := by
          rw [Mem.obj?_addObj]; simp only [hpn, ↓reduceIte]; exact hop
        rw [hop1, Mem.obj?_setObj] at ho'
        split at ho'
        · rename_i he; subst he; rw [hop, Option.some.injEq] at ho; subst ho
          simp only [Option.some.injEq] at ho'; subst ho'; rfl
        · have hn : h ≠ m.next := by
            intro he; subst he; rw [hm.fresh _ (Nat.le_refl _)] at ho; cases ho
          rw [Mem.obj?_addObj] at ho'
          simp only [hn, ↓reduceIte, ho, Option.some.injEq] at ho'
          subst ho'; rfl
    simp only [Obj.core, e1, e3, e4, e2, hc', e5]
  cases sl with
  | mem h' =>
    obtain ⟨o', ho', hn'⟩ := hm.slotsNode hp op hop z h' hsl
    have hrc : m.reached4 sp S0 db.S hp z = some (m, h') := by
      unfold Mem.reached4; rw [hop]; simp only [Option.bind_some, hsl, ho', Option.isSome_some, ↓reduceIte]
    refine ⟨m.swz hp z h', h', by rw [follow4_eq, hrc]; rfl, hm.reached4 hinv hrc, hkeep m h' hrc, ?_⟩
    have ho'' : (m.swz hp z h').obj? h' = some o' := by
      unfold Mem.swz; rw [hop, Mem.obj?_setObj]
      simp only [hne h' o' ho' hn', ↓reduceIte]; exact ho'
    refine ⟨o', ho'', hn', ?_⟩
    rcases hg with ⟨-, h0, hh0, hc0⟩ | ⟨hzD, hval⟩
    · simp only [Slot.mem.injEq] at hh0
      subst hh0
      obtain ⟨o0, ho0, hc0', -⟩ := hm.obj_of_canonicalOf hc0
      rw [ho', Option.some.injEq] at ho0; subst ho0
      exact Or.inl hc0'
    · simp only [slotRefOf, ho', Option.bind_some] at hval
      cases hco : o'.canonical with
      | true => exact Or.inl rfl
      | false => exact Or.inr ⟨hzD, hzw, hval⟩
  | stream r =>
    cases hc : m.canonicalOf z with
    | some h0 =>
      have hrc : m.reached4 sp S0 db.S hp z = some (m, h0) := by
        unfold Mem.reached4; rw [hop]; simp only [Option.bind_some, hsl, hc]
      obtain ⟨o0, ho0, hc0, hn0⟩ := hm.obj_of_canonicalOf hc
      refine ⟨m.swz hp z h0, h0, by rw [follow4_eq, hrc]; rfl, hm.reached4 hinv hrc, hkeep m h0 hrc, ?_⟩
      have ho0' : (m.swz hp z h0).obj? h0 = some o0 := by
        unfold Mem.swz; rw [hop, Mem.obj?_setObj]
        simp only [hne h0 o0 ho0 hn0, ↓reduceIte]; exact ho0
      exact ⟨o0, ho0', hn0, Or.inl hc0⟩
    | none =>
      rcases hg with ⟨hzD, -⟩ | ⟨hzD, hval⟩
      · have := hm.dCanon z hzD; rw [hc] at this; cases this
      simp only [slotRefOf] at hval
      cases hl : db.S.lv z with
      | none =>
        exfalso
        obtain ⟨nz, hnz⟩ := Option.isSome_iff_exists.mp (Reach.isSome ((reachable_iff _ _ _ _).mp hzr))
        obtain ⟨v, hv, -⟩ := hinv.lv_whole hnz hzw hzD hzr
        rw [hl] at hv; cases hv
      | some v =>
        rw [hl] at hval
        simp only [Option.map_some] at hval
        have hva := hinv.lv_at hl
        have hrc : m.reached4 sp S0 db.S hp z =
            some ((m.addObj (Obj.ofVersion sp v none)).1, m.next) := by
          unfold Mem.reached4; rw [hop]; simp only [Option.bind_some, hsl, hc, hval, hva]; rfl
        refine ⟨((m.addObj (Obj.ofVersion sp v none)).1).swz hp z m.next, m.next,
          by rw [follow4_eq, hrc]; rfl, hm.reached4 hinv hrc, hkeep _ _ hrc, ?_⟩
        obtain ⟨f1, -, -, -, f5, f6⟩ := Obj.ofVersion_fields sp v none
        obtain ⟨hvn, -, -⟩ := hinv.version_node hva
        have hpn : hp ≠ m.next := by
          intro he; subst he; rw [hm.fresh _ (Nat.le_refl _)] at hop; cases hop
        have hop1 : (m.addObj (Obj.ofVersion sp v none)).1.obj? hp = some op := by
          rw [Mem.obj?_addObj]; simp only [hpn, ↓reduceIte]; exact hop
        have hnew : (((m.addObj (Obj.ofVersion sp v none)).1).swz hp z m.next).obj? m.next =
            some (Obj.ofVersion sp v none) := by
          unfold Mem.swz; rw [hop1, Mem.obj?_setObj]
          simp only [Ne.symm hpn, ↓reduceIte, Mem.obj?_addObj]
        refine ⟨_, hnew, by rw [f1, hvn], Or.inr ⟨hzD, hzw, ?_⟩⟩
        rw [f6, hl]; rfl

/-- One step of a read's fold over the live children of object o at handle h,
Level 4. -/
def readStep4 (sp : Spec V T) (S0 S : Stream V T) (fuel : Nat) (t : Time) (h : Nat) (o : Obj V)
    (acc : Mem V × List (NodeId × Node V)) (y : NodeId) : Mem V × List (NodeId × Node V) :=
  match acc.1.follow4 sp S0 S h y false with
  | (m1, some h1) =>
    match m1.obj? h1 with
    | some o1 =>
      if o1.level < o.level then
        let r := Mem.readAt4 sp S0 S fuel m1 t h1
        (r.1, acc.2 ++ r.2)
      else (m1, acc.2)
    | none => (m1, acc.2)
  | (m1, none) => (m1, acc.2)

theorem readAt4_succ_eq (sp : Spec V T) (S0 S : Stream V T) (fuel : Nat) (m : Mem V) (t : Time)
    (h : Nat) {o : Obj V} (ho : m.obj? h = some o) :
    m.readAt4 sp S0 S (fuel + 1) t h =
      (sp.live (o.hist.upTo t)).foldl (readStep4 sp S0 S fuel t h o) (m, [(o.node, o.nodeAt t)]) := by
  rw [Mem.readAt4]; simp only [ho]; rfl

/-- A read at k from a readable object of a node reachable at k gives the nodes
reachable from it at k, each with its node at k; the invariant and the objects'
cores are kept. -/
theorem EInv.readAt4_ok (hinv : Inv sp db k) (hls : LiveSub sp) (hev : EvLogic sp db k) :
    ∀ (fuel : Nat) (m : Mem V) (h : Nat) (y : NodeId) (n : Node V), EInv sp db S0 k m →
      Readable4 sp db m h y → db.P.get? y = some n → reachable sp db.P k y = true →
      n.level < fuel →
      EInv sp db S0 k (m.readAt4 sp S0 db.S fuel k h).1 ∧ m.KeepCore (m.readAt4 sp S0 db.S fuel k h).1 ∧
        (m.readAt4 sp S0 db.S fuel k h).2 = (reachFrom sp db.P k y n).map (fun z => (z, nodeAt db.P z k)) := by
  intro fuel
  induction fuel with
  | zero => intro m h y n _ _ _ _ hlt; omega
  | succ fuel ih =>
    intro m h y n hm hrd hn hr hlt
    obtain ⟨o, ho, hoy, hoh, hol, hod⟩ := hm.readable_facts hinv hrd hn hr
    rw [readAt4_succ_eq sp S0 db.S fuel m k h ho]
    have hupk : o.hist.upTo k = o.hist := by rw [hoh]; exact upTo_of_forall _ _ (hinv.times y n hn)
    -- The parent's slots, in every memory that keeps the invariant and the cores.
    have hpar : ∀ (m' : Mem V), EInv sp db S0 k m' → m.KeepCore m' →
        ∀ z ∈ sp.live (o.hist.upTo k), ∃ o' sl, m'.obj? h = some o' ∧ o'.core = o.core ∧
          o'.slot? z = some sl ∧ SlotGood4 S0 db m' z sl := by
      intro m' hm' hkc z hz
      obtain ⟨o', ho', hc'⟩ := hkc h o ho
      have e4 : o'.hist = o.hist := congrArg (fun c => c.2.2.2.1) hc'
      obtain ⟨sl, hsl, hg⟩ := hm'.readable_slot hinv hev (hrd.keepCore hkc) hr ho'
        (by rw [e4, ← hupk]; exact hz) hls
      exact ⟨o', sl, ho', hc', hsl, hg⟩
    have hlive : sp.live (o.hist.upTo k) = sp.live (n.hist.upTo k) := by rw [hoh]
    obtain ⟨hI, hL⟩ := fold_inv (V := V) (readStep4 sp S0 db.S fuel k h o)
      (fun m' => EInv sp db S0 k m' ∧ m.KeepCore m')
      (fun z => match db.P.get? z with
        | some nz => if nz.level < n.level then (reachFrom sp db.P k z nz).map
            (fun z => (z, nodeAt db.P z k)) else []
        | none => []) (sp.live (o.hist.upTo k)) (by
        intro acc z hz ⟨hmA, hkcA⟩
        obtain ⟨o', sl, ho', hc', hsl, hg⟩ := hpar acc.1 hmA hkcA z hz
        have hz' : z ∈ sp.live (n.hist.upTo k) := by rw [← hlive]; exact hz
        obtain ⟨e, he, hze⟩ := hls _ _ hz'
        obtain ⟨nz, hnz, hlvl⟩ := hinv.ptrs y n hn e (mem_upTo.mp he).1 z hze
        have hrz : reachable sp db.P k z = true := by
          rw [reachable_iff] at hr ⊢
          exact Reach.child hr hn hz' hnz hlvl
        have e1 : o'.node = o.node := congrArg (fun c => c.1) hc'
        have hzne : z ≠ o'.node := by
          rw [e1, hoy]
          intro hzy
          rw [hzy, hn, Option.some.injEq] at hnz
          subst hnz
          omega
        have hzw : written sp z = true :=
          written_of_ne_root sp (hinv.ptr_ne_root hn (mem_upTo.mp he).1 hze)
        obtain ⟨m1, h1, hev1, hm1, hkc1, hrd1⟩ := hmA.follow_good hinv ho' hsl hg hzw hzne hrz
        obtain ⟨o1, ho1, -, -, hol1, -⟩ := hm1.readable_facts hinv hrd1 hnz hrz
        obtain ⟨hI2, hkc2, hL2⟩ := ih m1 h1 z nz hm1 hrd1 hnz hrz (by omega)
        have hst : readStep4 sp S0 db.S fuel k h o acc z =
            ((Mem.readAt4 sp S0 db.S fuel m1 k h1).1, acc.2 ++ (Mem.readAt4 sp S0 db.S fuel m1 k h1).2) := by
          unfold readStep4
          rw [hev1]
          simp only [ho1, hol1, hol, hlvl, ↓reduceIte]
        rw [hst]
        refine ⟨⟨hI2, (hkcA.trans hkc1).trans hkc2⟩, ?_⟩
        simp only [hnz, hlvl, ↓reduceIte]
        rw [hL2]) (m, [(o.node, o.nodeAt k)]) ⟨hm, Mem.KeepCore.refl m⟩
    refine ⟨hI.1, hI.2, ?_⟩
    have hnode : o.nodeAt k = nodeAt db.P y k := by
      unfold Obj.nodeAt nodeAt
      rw [hn]
      simp only [hol, hod, hoh]
    rw [hL, reachFrom_eq, List.map_cons, List.map_flatMap, hoy, hnode, hoh]
    simp only [List.singleton_append, List.cons.injEq, true_and]
    apply flatMap_congr_mem
    intro z _
    cases hnz : db.P.get? z with
    | none => rfl
    | some nz =>
      simp only
      split <;> rfl

/-- A read at k from the root's object gives P@k, and keeps the invariant. -/
theorem EInv.read4_ok (hinv : Inv sp db k) (hls : LiveSub sp) (hev : EvLogic sp db k)
    (hm : EInv sp db S0 k m) :
    EInv sp db S0 k (m.read4 sp S0 db.S k).1 ∧
      (m.read4 sp S0 db.S k).2 = (reachList sp db.P k).map (fun z => (z, nodeAt db.P z k)) := by
  obtain ⟨o, ho, hc, hn⟩ := hm.root
  obtain ⟨n0, hn0⟩ := Option.isSome_iff_exists.mp hinv.rootIn
  have hrd : Readable4 sp db m m.root SIS.root := ⟨o, ho, hn, Or.inl hc⟩
  obtain ⟨o', ho', -, -, hol, -⟩ := hm.readable_facts hinv hrd hn0 (reachable_root hn0 k)
  rw [ho, Option.some.injEq] at ho'
  subst ho'
  have := EInv.readAt4_ok hinv hls hev (o.level + 1) m m.root SIS.root n0 hm hrd hn0
    (reachable_root hn0 k) (by omega)
  unfold Mem.read4
  rw [ho]
  simp only
  refine ⟨this.1, ?_⟩
  rw [this.2.2]
  unfold reachList
  rw [hn0]

/-- The writer's view at k through the Level 4 loader is P's. -/
theorem EInv.view4_ok (hinv : Inv sp db k) (hls : LiveSub sp) (hev : EvLogic sp db k)
    (hm : EInv sp db S0 k m) :
    EInv sp db S0 k (m.view4 sp S0 db.S k).1 ∧ (m.view4 sp S0 db.S k).2 = view sp db.P k := by
  obtain ⟨h1, h2⟩ := hm.read4_ok hinv hls hev
  refine ⟨h1, ?_⟩
  funext x
  show ((m.read4 sp S0 db.S k).2).lookup x = _
  rw [h2, lookup_reach_view]

end Read

end SIS
