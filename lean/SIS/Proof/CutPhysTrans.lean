/-
Proofs about reclaim, part 14 (bergdb item 001, WP R4, T9): one transaction of
the physical writer keeps T9's invariant (`CInv`). The change gives a new
pointer the canonical object of its pointee, or a copy of a slot that names the
pointee's latest version; the writes make the slots of a taken node for the
pointees of D memory slots to their canonical objects, and give the taken node a
version that names its pointees' latest versions; Rule A's order keeps a node
of D written no later than a pointee of D that a stale slot names.
-/
import SIS.Proof.CutPhys

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## The change -/

section Change

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V} {c : Changes V}

/-- With a virtual root, the root's new pointees are new root children. -/
theorem EInv.rootNew (hinv : Inv sp db k) (hm : EInv sp db S0 k m) (hstep : StepOK sp db.P (k + 1) c)
    (hv : sp.virt = true) {y : NodeId}
    (hy : y ∈ (c.adds.filter (fun a => (c.new.foldl addNew m).canonicalOf a.1 == some m.root)).flatMap
      (fun a => sp.ptrs a.2)) :
    y ∈ c.new.map (·.id) := by
  have haf := hm.addFacts hstep.distinct
  obtain ⟨a, ha, hya⟩ := List.mem_flatMap.mp hy
  obtain ⟨o0, ho0, hc0, hn0⟩ := hm.root
  have hcr : m.canonicalOf SIS.root = some m.root := by rw [← hn0]; exact hm.canonicalOf_of ho0 hc0
  have hrn : SIS.root ∉ c.new.map (·.id) := by
    intro hr
    obtain ⟨nn, hnn, he⟩ := List.mem_map.mp hr
    have := hstep.fresh nn hnn
    rw [he] at this
    obtain ⟨n0, h0⟩ := Option.isSome_iff_exists.mp hinv.rootIn
    rw [h0] at this; cases this
  have hcr' : (c.new.foldl addNew m).canonicalOf SIS.root = some m.root := by
    rw [haf.canOld _ hrn]; exact hcr
  rw [hm.adds_filter_node hstep.distinct hcr'] at ha
  have ha' : a ∈ c.adds.filter (fun a => a.1 == SIS.root) := ha
  rw [(hstep.virt hv).rootAdds] at ha'
  obtain ⟨nn, hnn, rfl⟩ := List.mem_map.mp ha'
  simp only [(hinv.vr hv).rootPtrs, List.mem_singleton] at hya
  subst hya
  exact List.mem_map.mpr ⟨nn, (List.mem_filter.mp hnn).1, rfl⟩

/-- The change keeps T9's invariant, for the state before it: the new slots
name canonical objects, or copy slots that name the pointees' latest versions;
the new nodes' objects are canonical. -/
theorem CInv.applyChange4 (hinv : Inv sp db k) (hm : EInv sp db S0 k m) (hc : CInv sp db S0 m)
    (hstep : StepOK sp db.P (k + 1) c) : CInv sp db S0 (m.applyChange4 sp db.P (k + 1) c) := by
  have haf := hm.addFacts hstep.distinct
  have hcf := changeFacts sp db.P (k + 1) c m
  -- Every object after: an object of m with entries and new slots, or a new node's.
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
  have hroot : (m.applyChange4 sp db.P (k + 1) c).root = m.root := by rw [hcf.root, haf.root]
  have hcan3 : ∀ y, (m.applyChange4 sp db.P (k + 1) c).canonicalOf y = (c.new.foldl addNew m).canonicalOf y :=
    hcf.canonicalOf
  -- A canonical object of m1 is canonical after.
  have hcanObj : ∀ y h', (c.new.foldl addNew m).canonicalOf y = some h' →
      ∃ o', (m.applyChange4 sp db.P (k + 1) c).obj? h' = some o' ∧ o'.canonical = true := by
    intro y h' hc'
    obtain ⟨o'', ho'', -, hco''⟩ := hm.addNew_canon haf hc'
    obtain ⟨-, -, -, -, f5, -⟩ := updAll4_core sp db.P (k + 1) (c.new.foldl addNew m)
      (c.adds.filter (fun a => (c.new.foldl addNew m).canonicalOf a.1 == some h')) o''
    exact ⟨_, by rw [hcf.obj h', ho'']; rfl, by rw [f5, hco'']⟩
  -- Every memory slot of m names an object of m.
  have hold : ∀ h0 o0 z sl0, m.obj? h0 = some o0 → o0.slot? z = some sl0 →
      ∀ h', sl0 = Slot.mem h' → (m.obj? h').isSome := by
    intro h0 o0 z sl0 ho0 hsl0 h' he
    subst he
    obtain ⟨o', ho', -⟩ := hm.slotsNode h0 o0 ho0 z h' hsl0
    rw [ho']; rfl
  -- The slot of an object after, for a pointee: its own, or the new one (NS4).
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
      (∃ h', sl = Slot.mem h' ∧ (m.applyChange4 sp db.P (k + 1) c).canonicalOf z = some h' ∧
        ∃ o', (m.applyChange4 sp db.P (k + 1) c).obj? h' = some o' ∧ o'.canonical = true) ∨
      (inD db.D z = false ∧ (c.new.foldl addNew m).canonicalOf z = none ∧
        slotRefOf S0 (m.applyChange4 sp db.P (k + 1) c) z sl = (db.S.lv z).map (·.recNo)) := by
    intro z sl hns
    rcases hm.NS4_good hinv hstep hns with ⟨h', rfl, hc'⟩ | ⟨hcz, hzD, -, href, h0, o0, ho0, hsl0⟩
    · exact Or.inl ⟨h', rfl, by rw [hcan3]; exact hc', hcanObj z h' hc'⟩
    · refine Or.inr ⟨hzD, hcz, ?_⟩
      rw [slotRefOf_keepPos hk hs (hold h0 o0 z sl ho0 hsl0)]
      exact href
  -- An object of m1 is an object of m, or a new node's (canonical, of a node with no
  -- version and not in D).
  have hm1 : ∀ h o1, (c.new.foldl addNew m).obj? h = some o1 →
      m.obj? h = some o1 ∨ (∃ nn ∈ c.new, o1 = newObj nn) := by
    intro h o1 ho1
    rcases haf.cls h o1 ho1 with ⟨-, h2⟩ | ⟨-, nn, hnn, hon, -⟩
    · exact Or.inl h2
    · exact Or.inr ⟨nn, hnn, hon⟩
  have hnewNoV : ∀ nn ∈ c.new, db.S.lv nn.id = none := by
    intro nn hnn
    cases hl : db.S.lv nn.id with
    | none => rfl
    | some v =>
      exfalso
      obtain ⟨-, -, n, hn, -⟩ := hinv.version_node (hinv.lv_at hl)
      rw [hstep.fresh nn hnn] at hn; cases hn
  have hnewND : ∀ nn ∈ c.new, inD db.D nn.id = false := by
    intro nn hnn
    cases hd : inD db.D nn.id with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨d, hdd⟩ := (inD_iff _ _).mp hd
      have := isSome_of_isIndex (hinv.dIndex _ hdd)
      rw [hstep.fresh nn hnn] at this; cases this
  -- With a virtual root, the root's new pointees are new root children.
  have hrootNew : sp.virt = true → ∀ y, y ∈ (c.adds.filter (fun a =>
      (c.new.foldl addNew m).canonicalOf a.1 == some m.root)).flatMap (fun a => sp.ptrs a.2) →
      y ∈ c.new.map (·.id) :=
    fun hv _ hy => hm.rootNew hinv hstep hv hy
  constructor
  · -- mono
    intro h o3 ho3 hco hw hD v hv y sl r0 hsl hr0
    obtain ⟨o1, ho1, hcase⟩ := hslot h o3 ho3 y sl hsl
    obtain ⟨o1', ho1', rfl⟩ := hobj h o3 ho3
    rw [ho1, Option.some.injEq] at ho1'
    subst ho1'
    obtain ⟨e1, -, -, -, e5, -⟩ := updAll4_core sp db.P (k + 1) (c.new.foldl addNew m)
      (c.adds.filter (fun a => (c.new.foldl addNew m).canonicalOf a.1 == some h)) o1
    rcases hm1 h o1 ho1 with ho | ⟨nn, hnn, rfl⟩
    · rcases hcase with hcase | hcase
      · exact (hc.mono h o1 ho (by rw [← e5]; exact hco) (by rw [← e1]; exact hw) (by rw [← e1]; exact hD)
          v (by rw [← e1]; exact hv) y sl r0 hcase hr0).keepPos hk hs (hold h o1 y sl ho hcase)
      · rcases hNS y sl hcase with ⟨h', rfl, -, o', ho', hco'⟩ | ⟨-, -, href⟩
        · exact Or.inl ⟨h', o', rfl, ho', hco'⟩
        · have hv1 : db.S.lv o1.node = some v := by rw [← e1]; exact hv
          obtain ⟨u, hu, hle⟩ := hinv.ref_le_lv hv1 hr0
          exact Or.inr ⟨u.recNo, by rw [href, hu]; rfl, hle⟩
    · exfalso
      rw [e1] at hv
      simp only [newObj] at hv
      rw [hnewNoV nn hnn] at hv; cases hv
  · -- pinSnap
    intro h o3 ho3 hco hD y h2 o2 hsl hyD ho2 hc2 hzp
    obtain ⟨o1, ho1, rfl⟩ := hobj h o3 ho3
    obtain ⟨e1, -, -, e4, e5, -⟩ := updAll4_core sp db.P (k + 1) (c.new.foldl addNew m)
      (c.adds.filter (fun a => (c.new.foldl addNew m).canonicalOf a.1 == some h)) o1
    -- the snapshot named: in m, at the same position
    obtain ⟨o0, ho0, hp0, hc0⟩ : ∃ o0, m.obj? h2 = some o0 ∧ o2.pos = o0.pos ∧ o0.canonical = false := by
      obtain ⟨o0, ho0⟩ : ∃ o0, (c.new.foldl addNew m).obj? h2 = some o0 := by
        rw [hcf.obj h2] at ho2
        obtain ⟨o0, ho0, -⟩ := Option.map_eq_some_iff.mp ho2
        exact ⟨o0, ho0⟩
      obtain ⟨o0', ho0', rfl⟩ := hobj h2 o2 ho2
      rw [ho0, Option.some.injEq] at ho0'
      subst ho0'
      obtain ⟨-, -, -, -, f5, f6⟩ := updAll4_core sp db.P (k + 1) (c.new.foldl addNew m)
        (c.adds.filter (fun a => (c.new.foldl addNew m).canonicalOf a.1 == some h2)) o0
      rcases hm1 h2 o0 ho0 with h3 | ⟨nn, -, rfl⟩
      · exact ⟨o0, h3, f6, by rw [← f5]; exact hc2⟩
      · rw [f5] at hc2; simp [newObj] at hc2
    rw [hp0]
    have hyn : y ∉ c.new.map (·.id) := by
      intro hy'
      obtain ⟨nn, hnn, rfl⟩ := List.mem_map.mp hy'
      rw [hnewND nn hnn] at hyD; cases hyD
    rcases hm1 h o1 ho1 with ho | ⟨nn, hnn, rfl⟩
    · rw [updAll4_slot] at hsl
      split at hsl
      · -- a new pointer: y, in D, has a canonical object, which the new slot names
        exfalso
        obtain ⟨h', hc'⟩ : ∃ h', (c.new.foldl addNew m).canonicalOf y = some h' := by
          rw [haf.canOld y hyn]; exact Option.isSome_iff_exists.mp (hm.dCanon y hyD)
        unfold combo4 NS4 at hsl
        rw [hc'] at hsl
        simp only [Option.map_some, Option.some_or, Option.some.injEq, Slot.mem.injEq] at hsl
        subst hsl
        obtain ⟨o', ho', hco'⟩ := hcanObj y h' hc'
        rw [ho2, Option.some.injEq] at ho'
        subst ho'
        rw [hco'] at hc2; cases hc2
      · rename_i hy
        have hzp1 : y ∈ pointees sp o1.hist := by
          rw [e4] at hzp
          rcases pointees_append_mem hzp with h | h
          · exact h
          · exfalso
            obtain ⟨a, ha, hya⟩ := pointees_adds_mem h
            exact hy (List.mem_flatMap.mpr ⟨a, ha, hya⟩)
        exact hc.pinSnap h o1 ho (by rw [← e5]; exact hco) (by rw [← e1]; exact hD) y h2 o0 hsl hyD ho0 hc0
          hzp1
    · exfalso
      rw [e1] at hD
      simp only [newObj] at hD
      rw [hnewND nn hnn] at hD; cases hD
  · -- rootD
    intro hv o3 ho3 y sl hsl hzp hyD
    rw [hroot] at ho3
    obtain ⟨o1, ho1, rfl⟩ := hobj _ o3 ho3
    obtain ⟨e1, -, -, e4, -, -⟩ := updAll4_core sp db.P (k + 1) (c.new.foldl addNew m)
      (c.adds.filter (fun a => (c.new.foldl addNew m).canonicalOf a.1 == some m.root)) o1
    rw [updAll4_slot] at hsl
    split at hsl
    · -- a new root child: not in D
      exfalso
      rename_i hy
      obtain ⟨nn, hnn, rfl⟩ := List.mem_map.mp (hrootNew hv y hy)
      rw [hnewND nn hnn] at hyD
      cases hyD
    · rename_i hy
      rcases hm1 _ o1 ho1 with ho | ⟨nn, hnn, rfl⟩
      · have hzp1 : y ∈ pointees sp o1.hist := by
          rw [e4] at hzp
          rcases pointees_append_mem hzp with h | h
          · exact h
          · exfalso
            obtain ⟨a, ha, hya⟩ := pointees_adds_mem h
            exact hy (List.mem_flatMap.mpr ⟨a, ha, hya⟩)
        have hyn : y ∉ c.new.map (·.id) := by
          intro hy'
          obtain ⟨nn, hnn, rfl⟩ := List.mem_map.mp hy'
          rw [hnewND nn hnn] at hyD; cases hyD
        obtain ⟨h', hsl', hc'⟩ := hc.rootD hv o1 ho y sl hsl hzp1 hyD
        exact ⟨h', hsl', by rw [hcan3, haf.canOld y hyn]; exact hc'⟩
      · simp [newObj, Obj.slot?] at hsl
  · -- rootClean
    intro hv o3 ho3 y sl hsl hzp hyD
    rw [hroot] at ho3
    obtain ⟨o1, ho1, rfl⟩ := hobj _ o3 ho3
    obtain ⟨e1, -, -, e4, -, -⟩ := updAll4_core sp db.P (k + 1) (c.new.foldl addNew m)
      (c.adds.filter (fun a => (c.new.foldl addNew m).canonicalOf a.1 == some m.root)) o1
    rw [updAll4_slot] at hsl
    split at hsl
    · -- a new root child: its new object, with no version
      rename_i hy
      have hyn := hrootNew hv y hy
      obtain ⟨nn, hnn, rfl⟩ := List.mem_map.mp hyn
      obtain ⟨h2, -, hc2, ho2⟩ := haf.canNew nn hnn
      unfold combo4 NS4 at hsl
      rw [hc2] at hsl
      simp only [Option.map_some, Option.some_or, Option.some.injEq] at hsl
      subst hsl
      have ho2' : (m.applyChange4 sp db.P (k + 1) c).obj? h2 = some (updAll4 sp db.P (k + 1)
          (c.new.foldl addNew m) (c.adds.filter (fun a => (c.new.foldl addNew m).canonicalOf a.1 == some h2))
          (newObj nn)) := by rw [hcf.obj h2, ho2]; rfl
      obtain ⟨-, -, -, -, -, f6⟩ := updAll4_core sp db.P (k + 1) (c.new.foldl addNew m)
        (c.adds.filter (fun a => (c.new.foldl addNew m).canonicalOf a.1 == some h2)) (newObj nn)
      simp only [slotRefOf, ho2', Option.bind_some, f6, hnewNoV nn hnn]
      rfl
    · rename_i hy
      rcases hm1 _ o1 ho1 with ho | ⟨nn, hnn, rfl⟩
      · have hzp1 : y ∈ pointees sp o1.hist := by
          rw [e4] at hzp
          rcases pointees_append_mem hzp with h | h
          · exact h
          · exfalso
            obtain ⟨a, ha, hya⟩ := pointees_adds_mem h
            exact hy (List.mem_flatMap.mpr ⟨a, ha, hya⟩)
        rw [slotRefOf_keepPos hk hs (hold _ o1 y sl ho hsl)]
        exact hc.rootClean hv o1 ho y sl hsl hzp1 hyD
      · simp [newObj, Obj.slot?] at hsl
  · -- snapND
    intro h o3 r ho3 hco hp
    obtain ⟨o1, ho1, rfl⟩ := hobj h o3 ho3
    obtain ⟨e1, -, -, -, e5, e6⟩ := updAll4_core sp db.P (k + 1) (c.new.foldl addNew m)
      (c.adds.filter (fun a => (c.new.foldl addNew m).canonicalOf a.1 == some h)) o1
    rw [e1]
    rcases hm1 h o1 ho1 with ho | ⟨nn, -, rfl⟩
    · exact hc.snapND h o1 r ho (by rw [← e5]; exact hco) (by rw [← e6]; exact hp)
    · rw [e5] at hco; simp [newObj] at hco

end Change


/-! ## Root children -/

section Root

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V} {c : Changes V}

/-- With a virtual root, a pointee of the root is a root child. -/
theorem VInv.top_of_pointee (hvi : VInv sp db k) {n : Node V} (hn : db.P.get? root = some n)
    {y : NodeId} (hy : y ∈ pointees sp n.hist) : ∃ m c, TopAt sp db.P y m c := by
  obtain ⟨e, he, hye⟩ := (mem_pointees sp _ _).mp hy
  obtain ⟨z, m, htop, hval⟩ := hvi.rootEntry n hn e he
  rw [hval, hvi.rootPtrs, List.mem_singleton] at hye
  subst hye
  exact ⟨m, e.time, htop⟩

/-- With a virtual root, a node reachable at k with a root child as a live child
at k is the root: a node above a root child is one too, and a root child that a
root child points to is not reachable (`VInv.deadTops`). -/
theorem Inv.parent_of_top (hinv : Inv sp db k) (hls : LiveSub sp) (hv : sp.virt = true) {p y : NodeId}
    {np : Node V} (hrp : reachable sp db.P k p = true) (hnp : db.P.get? p = some np)
    (hy : y ∈ sp.live (np.hist.upTo k)) (hty : isTop sp db.P y = true) : p = root := by
  rcases Classical.em (p = root) with h | hne
  · exact h
  · exfalso
    obtain ⟨e, he, hye⟩ := hls _ _ hy
    have he' := (mem_upTo.mp he).1
    obtain ⟨my, hmy, hlt⟩ := hinv.ptrs p np hnp e he' y hye
    have hyp : y ∈ pointees sp np.hist := (mem_pointees sp _ _).mpr ⟨e, he', hye⟩
    have htp : isTop sp db.P p = true := by
      unfold isTop at hty ⊢
      rw [hmy] at hty
      rw [hnp]
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hty ⊢
      exact ⟨hne, by omega⟩
    have hdead := (hinv.vr hv).deadTops p np hnp htp y hyp hty
    have hry : reachable sp db.P k y = true := by
      rw [reachable_iff] at hrp ⊢
      exact Reach.child hrp hnp hy hmy hlt
    rw [hry] at hdead; cases hdead

/-- A version's references are for its pointees. -/
theorem Inv.ref_pointees (hinv : Inv sp db k) {x : NodeId} {v : Version V} (hv : db.S.lv x = some v)
    {y : NodeId} {r : Nat} (hr : v.ref? y = some r) : y ∈ pointees sp v.hist := by
  obtain ⟨r0, hr0⟩ := lv_versionAt hv
  obtain ⟨R, hR, hvR, -⟩ := versionAt_spec hr0
  obtain ⟨pre, -, href⟩ := hinv.ref r0 R hR v hvR
  rw [href y] at hr
  split at hr
  · assumption
  · cases hr

/-- With a virtual root, after the change: the root's object names a root child
on the writer's paths, or a new one, by a memory slot to its canonical object
(the walk reached it from the root; the change gave the new one its new
canonical object). -/
theorem EInv.rootSlots_change (hinv : Inv sp db k) (hls : LiveSub sp) (hm : EInv sp db S0 k m)
    (hstep : StepOK sp db.P (k + 1) c) (hv : sp.virt = true) {path : List NodeId}
    (hpr : ∀ p ∈ path, reachable sp db.P k p = true) (hpd : ∀ x ∈ path, PathDone sp db.P k path m x)
    {o : Obj V}
    (ho : (m.applyChange4 sp db.P (k + 1) c).obj? (m.applyChange4 sp db.P (k + 1) c).root = some o)
    {y : NodeId} {sl : Slot} (hsl : o.slot? y = some sl) (hyp : y ∈ pointees sp o.hist)
    (hy : y ∈ path ∨ y ∈ c.new.map (·.id)) :
    ∃ h', sl = Slot.mem h' ∧ (m.applyChange4 sp db.P (k + 1) c).canonicalOf y = some h' := by
  have haf := hm.addFacts hstep.distinct
  have hcf := changeFacts sp db.P (k + 1) c m
  have hroot : (m.applyChange4 sp db.P (k + 1) c).root = m.root := by rw [hcf.root, haf.root]
  rw [hroot, hcf.obj] at ho
  obtain ⟨o1, ho1, rfl⟩ := Option.map_eq_some_iff.mp ho
  obtain ⟨o0, ho0, hc0, hn0⟩ := hm.root
  have hlt := lt_next_of_obj? hm.fresh ho0
  rw [haf.old _ hlt, ho0, Option.some.injEq] at ho1
  subst ho1
  obtain ⟨-, -, -, e4, -, -⟩ := updAll4_core sp db.P (k + 1) (c.new.foldl addNew m)
    (c.adds.filter (fun a => (c.new.foldl addNew m).canonicalOf a.1 == some m.root)) o0
  rw [updAll4_slot] at hsl
  split at hsl
  · -- a new root child: the new slot names its new canonical object
    rename_i hya
    obtain ⟨nn, hnn, rfl⟩ := List.mem_map.mp (hm.rootNew hinv hstep hv hya)
    obtain ⟨h2, -, hc2, -⟩ := haf.canNew nn hnn
    unfold combo4 NS4 at hsl
    rw [hc2] at hsl
    simp only [Option.map_some, Option.some_or, Option.some.injEq] at hsl
    exact ⟨h2, hsl.symm, by rw [hcf.canonicalOf]; exact hc2⟩
  · rename_i hya
    have hyp0 : y ∈ pointees sp o0.hist := by
      rw [e4] at hyp
      rcases pointees_append_mem hyp with h | h
      · exact h
      · exfalso
        obtain ⟨a, ha, hya'⟩ := pointees_adds_mem h
        exact hya (List.mem_flatMap.mpr ⟨a, ha, hya'⟩)
    obtain ⟨n0, hn0', hh0, -, -⟩ := hm.cc m.root o0 ho0 hc0
    rw [hn0] at hn0'
    rw [hh0] at hyp0
    obtain ⟨my, cy, htop⟩ := (hinv.vr hv).top_of_pointee hn0' hyp0
    have hyn : y ∉ c.new.map (·.id) := by
      intro hy'
      obtain ⟨nn, hnn, he⟩ := List.mem_map.mp hy'
      have := hstep.fresh nn hnn
      rw [he, htop.1] at this; cases this
    have hyp' : y ∈ path := by
      rcases hy with h | h
      · exact h
      · exact absurd h hyn
    obtain ⟨-, hpd2⟩ := hpd y hyp'
    obtain ⟨p, hpp, np, hp, op, ha, hnp, hyl, hcp, hop, hsla, hca⟩ := hpd2 htop.2.1
    have hpr' : p = SIS.root := hinv.parent_of_top hls hv (hpr p hpp) hnp hyl htop.isTop
    subst hpr'
    have hcr : m.canonicalOf SIS.root = some m.root := by rw [← hn0]; exact hm.canonicalOf_of ho0 hc0
    rw [hcr, Option.some.injEq] at hcp
    subst hcp
    rw [ho0, Option.some.injEq] at hop
    subst hop
    rw [hsla, Option.some.injEq] at hsl
    refine ⟨ha, hsl.symm, ?_⟩
    rw [hcf.canonicalOf, haf.canOld y hyn]
    exact hca

end Root


/-! ## The next state -/

section Next

variable {sp : Spec V T} {al : Algo V T} {db : DB V T} {tr : T} {S0 : Stream V T} {k : Nat}

/-- After the writes, T9's invariant of the next state. A written node's new
version names its pointees' latest versions; its slots name these, or canonical
objects (pinned, for D1). A node not written keeps its slots and its version;
a snapshot that one of D names stays of its pointee's latest version, as Rule
A's order writes that pointee no earlier than the node. -/
theorem CInv.next (hsp : SpecOK sp) (hinv : Inv sp db k) (hmk : al.mark = true)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) (hinv' : Inv sp (step sp al db tr) (k + 1))
    {m3 m6 : Mem V}
    (ha : AInv sp db S0 k (parts sp al db tr).c (pathOf sp db.P (parts sp al db tr).c (k + 1)) m3)
    (hc3 : CInv sp db S0 m3)
    (hroot3 : sp.virt = true → ∀ o, m3.obj? m3.root = some o → ∀ y sl, o.slot? y = some sl →
      y ∈ pointees sp o.hist → (y ∈ pathOf sp db.P (parts sp al db tr).c (k + 1) ∨
        y ∈ (parts sp al db tr).c.new.map (·.id)) → ∃ h', sl = Slot.mem h' ∧ m3.canonicalOf y = some h')
    (hfr : LoopsFrame db.D (parts sp al db tr).D1 (dataIds sp al db tr) (parts sp al db tr).taken (k + 1)
      m3 m6)
    (hm6 : EInv sp (step sp al db tr) S0 (k + 1) m6) :
    CInv sp (step sp al db tr) S0 m6 := by
  have hP : (parts sp al db tr).P = db.P.apply (k + 1) (parts sp al db tr).c := parts_P' sp al db tr hinv.len
  have hP' : (step sp al db tr).P = (parts sp al db tr).P := rfl
  have hS' : (step sp al db tr).S = Snew sp al db tr := rfl
  have hD' : (step sp al db tr).D = (parts sp al db tr).r7.1 := rfl
  -- Objects of m6 come from m3.
  have hobj : ∀ h o6, m6.obj? h = some o6 → ∃ o3, m3.obj? h = some o3 ∧ o6.node = o3.node ∧
      o6.level = o3.level ∧ o6.isData = o3.isData ∧ o6.hist = o3.hist ∧ o6.canonical = o3.canonical ∧
      (∀ z, o6.slot? z = o3.slot? z ∨ ((inD db.D z = true ∨ inD (parts sp al db tr).D1 z = true) ∧
        ∃ sl h0, o3.slot? z = some sl ∧ m3.canonicalOf z = some h0 ∧ o6.slot? z = some (Slot.mem h0))) ∧
      ((o3.node ∈ (parts sp al db tr).taken ∧ m3.canonicalOf o3.node = some h) → ∀ z sl h0,
        o3.slot? z = some sl → inD (parts sp al db tr).D1 z = true → m3.canonicalOf z = some h0 →
        o6.slot? z = some (Slot.mem h0)) ∧
      (¬ ((o3.node ∈ dataIds sp al db tr ∨ o3.node ∈ (parts sp al db tr).taken) ∧
        m3.canonicalOf o3.node = some h) → o6.pos = o3.pos ∧ ∀ z, o6.slot? z = o3.slot? z) := by
    intro h o6 ho6
    obtain ⟨o3, ho3⟩ : ∃ o3, m3.obj? h = some o3 := by
      cases h3 : m3.obj? h with
      | none => rw [hfr.none h h3] at ho6; cases ho6
      | some o3 => exact ⟨o3, rfl⟩
    obtain ⟨o6', ho6', rest⟩ := hfr.obj h o3 ho3
    rw [ho6, Option.some.injEq] at ho6'
    subst ho6'
    exact ⟨o3, ho3, rest⟩
  -- A snapshot stays as it is; a canonical object stays canonical.
  have hsnap6 : ∀ h o3, m3.obj? h = some o3 → o3.canonical = false → ∃ o6, m6.obj? h = some o6 ∧
      o6.node = o3.node ∧ o6.canonical = false ∧ o6.pos = o3.pos ∧ ∀ z, o6.slot? z = o3.slot? z := by
    intro h o3 ho3 hc3'
    obtain ⟨o6, ho6, e1, -, -, -, e5, -, -, e8⟩ := hfr.obj h o3 ho3
    have hnc : ¬ ((o3.node ∈ dataIds sp al db tr ∨ o3.node ∈ (parts sp al db tr).taken) ∧
        m3.canonicalOf o3.node = some h) := by
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
  have hcanObj : ∀ y h0, m3.canonicalOf y = some h0 → ∃ o6, m6.obj? h0 = some o6 ∧ o6.canonical = true := by
    intro y h0 hc0
    obtain ⟨-, o0, ho0, hco0⟩ := (m3.canonicalOf_eq_some y h0).mp hc0
    exact hcan6 h0 o0 ho0 hco0
  -- A slot that names a canonical object, or a record at or after r0, still does.
  have hAL : ∀ y sl r0, SlotAtLeast S0 m3 y sl r0 → SlotAtLeast S0 m6 y sl r0 := by
    intro y sl r0 hal
    rcases hal with ⟨h', o', rfl, ho', hco'⟩ | ⟨r, hr, hle⟩
    · obtain ⟨o6, ho6, hc6⟩ := hcan6 h' o' ho' hco'
      exact Or.inl ⟨h', o6, rfl, ho6, hc6⟩
    · cases sl with
      | stream p =>
        refine Or.inr ⟨r, ?_, hle⟩
        simp only [slotRefOf, hfr.s] at hr ⊢
        exact hr
      | mem h' =>
        cases ho' : m3.obj? h' with
        | none => simp only [slotRefOf, ho', Option.bind_none] at hr; cases hr
        | some o' =>
          cases hco : o'.canonical with
          | true =>
            obtain ⟨o6, ho6, hc6⟩ := hcan6 h' o' ho' hco
            exact Or.inl ⟨h', o6, rfl, ho6, hc6⟩
          | false =>
            obtain ⟨o6, ho6, -, -, hp6, -⟩ := hsnap6 h' o' ho' hco
            refine Or.inr ⟨r, ?_, hle⟩
            simp only [slotRefOf, ho', Option.bind_some] at hr
            simp only [slotRefOf, ho6, Option.bind_some, hp6]
            exact hr
  -- D after the transaction.
  have hD1D : ∀ y, inD db.D y = true → inD (parts sp al db tr).D1 y = true := by
    intro y hy
    obtain ⟨d, hd⟩ := (inD_iff _ _).mp hy
    exact (inD_iff _ _).mpr ⟨d, (step_D1_mem sp al db tr hinv.len _).mpr (Or.inl hd)⟩
  have hD'D1 : ∀ y, inD (parts sp al db tr).r7.1 y = true → inD (parts sp al db tr).D1 y = true :=
    fun y hy => step_r7_D1 sp al db tr hinv hy
  have hD1cases : ∀ y, inD (parts sp al db tr).D1 y = true →
      inD db.D y = true ∨ y ∈ pathOf sp db.P (parts sp al db tr).c (k + 1) ∨
        y ∈ (parts sp al db tr).c.new.map (·.id) := by
    intro y hy
    rcases step_D1_cases sp al db tr hmk hinv hy with h | h | h
    · exact Or.inl h
    · by_cases hn : y ∈ (parts sp al db tr).c.new.map (·.id)
      · exact Or.inr (Or.inr hn)
      · rw [hP] at h
        exact Or.inr (Or.inl (step_marked_path sp al db tr hsp hinv hstep h hn))
    · exact Or.inr (Or.inl (step_touched_path sp al db tr hstep h))
  have hD1rel : ∀ y, inD (parts sp al db tr).D1 y = true →
      reachable sp (db.P.apply (k + 1) (parts sp al db tr).c) (k + 1) y = true ∨ inD db.D y = true ∨
        reachable sp db.P k y = true := by
    intro y hy
    rcases step_D1_cases sp al db tr hmk hinv hy with h | h | h
    · exact Or.inr (Or.inl h)
    · left; rw [hP] at h; unfold marked at h; simp only [Bool.and_eq_true] at h; exact h.1
    · right; right; have := hstep.touchReach y h; simpa using this
  have hnotw : ∀ z, z ∉ dataIds sp al db tr → z ∉ (parts sp al db tr).taken →
      (Snew sp al db tr).lv z = db.S.lv z := by
    intro z h1 h2
    apply lv_Snew_not_written
    intro w hw hwz
    have := (step_written_iff sp al db tr hinv hstep z).mp ⟨w, hw, hwz⟩
    rcases this with h | h
    · exact h1 h
    · exact h2 h
  have htakenD : ∀ x ∈ (parts sp al db tr).taken, ∃ d, (x, d) ∈ db.D ∧ d ≤ (parts sp al db tr).s :=
    fun x hx => step_taken_inD (al := al) (tr := tr) hinv hx
  have hdnew : ∀ x ∈ dataIds sp al db tr, x ∈ (parts sp al db tr).c.new.map (·.id) := by
    intro x hx
    simp only [dataIds, List.mem_map, List.mem_filter] at hx
    obtain ⟨nn, ⟨hnn, -⟩, rfl⟩ := hx
    exact List.mem_map.mpr ⟨nn, hnn, rfl⟩
  have hdataND : ∀ z ∈ dataIds sp al db tr, inD db.D z = false := by
    intro z hzd
    cases hzd' : inD db.D z with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨d, hd⟩ := (inD_iff _ _).mp hzd'
      have hix := hinv.dIndex (z, d) hd
      obtain ⟨hnone, -⟩ := step_dataIds_spec sp al db tr hinv hstep hzd
      simp [isIndex, hnone] at hix
  have htakenND : ∀ z, inD db.D z = false → z ∉ (parts sp al db tr).taken := by
    intro z hz hzt
    obtain ⟨d, hd, -⟩ := htakenD z hzt
    rw [(inD_iff _ _).mpr ⟨d, hd⟩] at hz; cases hz
  have hD2 : ∀ z, inD (parts sp al db tr).D1 z = true → z ∉ (parts sp al db tr).taken →
      inD (parts sp al db tr).r7.1 z = true := by
    intro z hz hzt
    obtain ⟨d, hd⟩ := (inD_iff _ _).mp hz
    have h2 := step_D2_of_not_taken sp al db tr hd hzt
    obtain ⟨d2, hd2⟩ := (inD_iff _ _).mp h2
    rw [(step_r7_shape sp al db tr hinv.len).1]
    exact (inD_iff _ _).mpr ⟨d2, List.mem_append_left _ hd2⟩
  -- The serialized reference of a slot of an object of m3, after the record.
  have hsref : ∀ h3 o3, m3.obj? h3 = some o3 → ∀ z sl, o3.slot? z = some sl →
      z ∉ dataIds sp al db tr → z ∉ (parts sp al db tr).taken →
      slotRefOf S0 m6 z sl = slotRefOf S0 m3 z sl := by
    intro h3 o3 ho3 z sl hz hzd hzt
    cases sl with
    | mem h' =>
      obtain ⟨o', ho', hn'⟩ := ha.slotsNode h3 o3 ho3 z h' hz
      obtain ⟨o6, ho6, e1, -, -, -, -, -, -, e9⟩ := hfr.obj h' o' ho'
      have hp : o6.pos = o'.pos := by
        refine (e9 ?_).1
        rintro ⟨h1, -⟩
        rw [hn'] at h1
        rcases h1 with h1 | h1
        · exact hzd h1
        · exact hzt h1
      simp only [slotRefOf, ho6, ho', Option.bind_some, hp]
    | stream r => simp only [slotRefOf, hfr.s]
  -- The position of the canonical object of a node, after the record: its latest
  -- version then.
  have hcanpos : ∀ z h0, m3.canonicalOf z = some h0 →
      slotRefOf S0 m6 z (Slot.mem h0) = ((step sp al db tr).S.lv z).map (·.recNo) := by
    intro z h0 hc
    rw [← hfr.canon] at hc
    obtain ⟨-, o, ho, -⟩ := (m6.canonicalOf_eq_some z h0).mp hc
    simp only [slotRefOf, ho, Option.bind_some]
    exact hm6.pos.lv0 hc ho
  -- The root is not written.
  have hroot6 : sp.virt = true → ∀ o6, m6.obj? m6.root = some o6 → ∃ o3, m3.obj? m3.root = some o3 ∧
      o6.hist = o3.hist ∧ ∀ z, o6.slot? z = o3.slot? z := by
    intro hv o6 ho6
    rw [hfr.root] at ho6
    obtain ⟨o3, ho3, -, -, -, e4, -, -, -, hun⟩ := hobj _ o6 ho6
    obtain ⟨o0, ho0, -, hn0⟩ := ha.root
    rw [ho3, Option.some.injEq] at ho0
    subst ho0
    refine ⟨o3, ho3, e4, (hun ?_).2⟩
    rintro ⟨h1 | h1, -⟩
    · rw [hn0] at h1
      obtain ⟨hnone, -⟩ := step_dataIds_spec sp al db tr hinv hstep h1
      have := hinv.rootIn
      rw [hnone] at this; cases this
    · rw [hn0] at h1
      exact htakenND _ (hinv.vr hv).rootND h1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- mono
    intro h o6 ho6 hco hw hD v hv y sl r0 hsl hr0
    obtain ⟨o3, ho3, e1, -, -, e4, e5, hsl6, hpin, hun⟩ := hobj h o6 ho6
    have hc3' : o3.canonical = true := by rw [← e5]; exact hco
    have hcx : m3.canonicalOf o3.node = some h := ha.canonicalOf_of' ho3 hc3'
    by_cases hxw : o3.node ∈ dataIds sp al db tr ∨ o3.node ∈ (parts sp al db tr).taken
    · -- written in the record: v is its new version, of its node in the new structure
      obtain ⟨n, hn, hh, -, -⟩ := ha.cc h o3 ho3 hc3'
      have hn' : (parts sp al db tr).P.get? o3.node = some n := by rw [hP]; exact hn
      have hyv : y ∈ pointees sp v.hist := hinv'.ref_pointees hv hr0
      obtain ⟨-, -, n', hn'', hvh, -⟩ := hinv'.version_node (hinv'.lv_at hv)
      rw [hP', e1, hn', Option.some.injEq] at hn''
      subst hn''
      have hyn : y ∈ pointees sp n.hist := by
        obtain ⟨e, he, hye⟩ := (mem_pointees sp _ _).mp hyv
        rw [hvh] at he
        exact (mem_pointees sp _ _).mpr ⟨e, (mem_upTo.mp he).1, hye⟩
      rcases hxw with hxd | hxt
      · -- a data node has no pointers
        exfalso
        obtain ⟨-, n2, hn2, hd2⟩ := step_dataIds_spec sp al db tr hinv hstep hxd
        rw [hn', Option.some.injEq] at hn2
        subst hn2
        obtain ⟨e, he, hye⟩ := (mem_pointees sp _ _).mp hyn
        have := hinv'.data o3.node n (by rw [hP']; exact hn') hd2 e he
        rw [this] at hye; cases hye
      · obtain ⟨v', hv', hrefs⟩ := step_taken_refs sp al db tr hsp hinv hstep hxt hn'
        have hv2 : (Snew sp al db tr).lv o3.node = some v := by rw [← e1]; exact hv
        rw [hv2, Option.some.injEq] at hv'
        subst hv'
        have hr0' := hrefs y hyn
        rw [hr0] at hr0'
        obtain ⟨d, hd, -⟩ := htakenD _ hxt
        obtain ⟨sl3, hsl3, hA1, -⟩ := ha.slots h o3 ho3 hc3' (by rw [← e1]; exact hw)
          (Or.inr (Or.inl ((inD_iff _ _).mpr ⟨d, hd⟩))) y (by rw [hh]; exact hyn)
        by_cases hyD1 : inD (parts sp al db tr).D1 y = true
        · -- pinned: the slot names y's canonical object
          obtain ⟨h0, hc0⟩ := Option.isSome_iff_exists.mp (ha.canon_D1 hsp hinv hmk hstep hyD1)
          have := hpin ⟨hxt, hcx⟩ y sl3 h0 hsl3 hyD1 hc0
          rw [hsl, Option.some.injEq] at this
          subst this
          obtain ⟨o6', ho6', hc6'⟩ := hcanObj y h0 hc0
          exact Or.inl ⟨h0, o6', rfl, ho6', hc6'⟩
        · have hyD : inD db.D y = false := by
            cases hy : inD db.D y with
            | false => rfl
            | true => exact absurd (hD1D y hy) hyD1
          have hyt := htakenND y hyD
          have hsame : sl = sl3 := by
            rcases hsl6 y with hs | ⟨hyin, -⟩
            · rw [hs, hsl3, Option.some.injEq] at hsl; exact hsl.symm
            · exfalso
              rcases hyin with h1 | h1
              · rw [hyD] at h1; cases h1
              · exact hyD1 h1
          subst hsame
          by_cases hyd : y ∈ dataIds sp al db tr
          · obtain ⟨h', rfl, hc'⟩ := (hA1 hyD).2 (hdnew y hyd)
            obtain ⟨o6', ho6', hc6'⟩ := hcanObj y h' hc'
            exact Or.inl ⟨h', o6', rfl, ho6', hc6'⟩
          · refine Or.inr ⟨r0, ?_, Nat.le_refl _⟩
            rw [hsref h o3 ho3 y sl hsl3 hyd hyt, (hA1 hyD).1, ← hnotw y hyd hyt]
            exact hr0'.symm
    · -- not written: its slots and its version as before, and its node not in D
      rw [not_or] at hxw
      have hxD : inD db.D o3.node = false := by
        cases hx : inD db.D o3.node with
        | false => rfl
        | true =>
          exfalso
          have := hD2 _ (hD1D _ hx) hxw.2
          have hD6 : inD (parts sp al db tr).r7.1 o3.node = false := by rw [← e1]; exact hD
          rw [this] at hD6; cases hD6
      have hv3 : db.S.lv o3.node = some v := by rw [← hnotw _ hxw.1 hxw.2, ← e1]; exact hv
      obtain ⟨-, hsame⟩ := hun (fun ⟨h1, _⟩ => by
        rcases h1 with h1 | h1
        · exact hxw.1 h1
        · exact hxw.2 h1)
      rw [hsame y] at hsl
      exact hAL y sl r0 (hc3.mono h o3 ho3 hc3' (by rw [← e1]; exact hw) hxD v hv3 y sl r0 hsl hr0)
  · -- pinSnap
    intro h o6 ho6 hco hD y h' o' hsl hyD ho' hco' hyp
    have hD6 : inD (parts sp al db tr).r7.1 o6.node = true := hD
    have hyD6 : inD (parts sp al db tr).r7.1 y = true := hyD
    obtain ⟨o3, ho3, e1, -, -, e4, e5, hsl6, hpin, -⟩ := hobj h o6 ho6
    have hc3' : o3.canonical = true := by rw [← e5]; exact hco
    have hcx : m3.canonicalOf o3.node = some h := ha.canonicalOf_of' ho3 hc3'
    -- The snapshot, in m3.
    obtain ⟨o3', ho3', -, -, -, -, e5', -⟩ := hobj h' o' ho'
    have hc3'' : o3'.canonical = false := by rw [← e5']; exact hco'
    obtain ⟨o6', ho6', -, -, hp6', -⟩ := hsnap6 h' o3' ho3' hc3''
    rw [ho', Option.some.injEq] at ho6'
    subst ho6'
    rw [hp6']
    -- h' is not y's canonical object.
    have hnc : ∀ h0, m3.canonicalOf y = some h0 → h' ≠ h0 := by
      intro h0 hc0 he
      subst he
      obtain ⟨-, o0, ho0, hco0⟩ := (m3.canonicalOf_eq_some y h').mp hc0
      rw [ho3', Option.some.injEq] at ho0
      subst ho0
      rw [hc3''] at hco0; cases hco0
    have hyD1 : inD (parts sp al db tr).D1 y = true := hD'D1 y hyD6
    obtain ⟨h0, hc0⟩ := Option.isSome_iff_exists.mp (ha.canon_D1 hsp hinv hmk hstep hyD1)
    -- The slot is o3's: a pinned one names y's canonical object.
    have hsl3 : o3.slot? y = some (Slot.mem h') := by
      rcases hsl6 y with hs | ⟨-, sl, h1, -, hc1, hs⟩
      · rw [← hs]; exact hsl
      · exfalso
        rw [hs, Option.some.injEq, Slot.mem.injEq] at hsl
        exact hnc h1 hc1 hsl.symm
    -- o's node is not taken: its slot for y would be pinned.
    have hxt : o3.node ∉ (parts sp al db tr).taken := by
      intro hxt
      have := hpin ⟨hxt, hcx⟩ y _ h0 hsl3 hyD1 hc0
      rw [hsl, Option.some.injEq, Slot.mem.injEq] at this
      exact hnc h0 hc0 this
    have hxD1 : inD (parts sp al db tr).D1 o3.node = true := by rw [← e1]; exact hD'D1 _ hD6
    have hw3 : written sp o3.node = true := by rw [← e1]; exact hinv'.written_of_D hD
    obtain ⟨sl3, hsl3', hA1, hA2⟩ := ha.slots h o3 ho3 hc3' hw3 (hD1rel _ hxD1) y (by rw [← e4]; exact hyp)
    rw [hsl3, Option.some.injEq] at hsl3'
    subst hsl3'
    cases hyDb : inD db.D y with
    | true =>
      rcases hA2 hyDb with ⟨h1, he, hc1⟩ | ⟨hxD, a, b, hda, hdb, hab⟩
      · simp only [Slot.mem.injEq] at he; exact absurd he (hnc h1 hc1)
      · -- y is not taken: else o's node, dirty no later, would be taken too
        have hyt : y ∉ (parts sp al db tr).taken := by
          intro hyt
          obtain ⟨d, hd, hds⟩ := htakenD y hyt
          have hb : b = d := by rw [dOf_of_mem hinv.dNodup hd, Option.some.injEq] at hdb; exact hdb.symm
          apply hxt
          exact (step_taken_mem sp al db tr _).mpr ⟨a, (step_D1_mem sp al db tr hinv.len _).mpr
            (Or.inl (mem_of_dOf hda)), by omega⟩
        have hyd : y ∉ dataIds sp al db tr := by
          intro hyd; rw [hdataND y hyd] at hyDb; cases hyDb
        rw [hS', hnotw y hyd hyt]
        exact hc3.pinSnap h o3 ho3 hc3' hxD y h' o3' hsl3 hyDb ho3' hc3'' (by rw [← e4]; exact hyp)
    | false =>
      obtain ⟨href, hnew⟩ := hA1 hyDb
      have hyt := htakenND y hyDb
      have hyd : y ∉ dataIds sp al db tr := by
        intro hyd
        obtain ⟨h1, he, hc1⟩ := hnew (hdnew y hyd)
        simp only [Slot.mem.injEq] at he
        exact hnc h1 hc1 he
      rw [hS', hnotw y hyd hyt]
      simp only [slotRefOf, ho3', Option.bind_some] at href
      exact href
  · -- rootD
    intro hv o6 ho6 y sl hsl hyp hyD
    have hyD6 : inD (parts sp al db tr).r7.1 y = true := hyD
    obtain ⟨o3, ho3, e4, hsame⟩ := hroot6 hv o6 ho6
    rw [hsame y] at hsl
    have hyp3 : y ∈ pointees sp o3.hist := by rw [← e4]; exact hyp
    cases hyDb : inD db.D y with
    | true =>
      obtain ⟨h', rfl, hc'⟩ := hc3.rootD hv o3 ho3 y sl hsl hyp3 hyDb
      exact ⟨h', rfl, by rw [hfr.canon]; exact hc'⟩
    | false =>
      have hy3 : y ∈ pathOf sp db.P (parts sp al db tr).c (k + 1) ∨
          y ∈ (parts sp al db tr).c.new.map (·.id) := by
        rcases hD1cases y (hD'D1 y hyD6) with h1 | h1
        · rw [hyDb] at h1; cases h1
        · exact h1
      obtain ⟨h', rfl, hc'⟩ := hroot3 hv o3 ho3 y sl hsl hyp3 hy3
      exact ⟨h', rfl, by rw [hfr.canon]; exact hc'⟩
  · -- rootClean
    intro hv o6 ho6 y sl hsl hyp hyD
    obtain ⟨o3, ho3, e4, hsame⟩ := hroot6 hv o6 ho6
    rw [hsame y] at hsl
    have hyp3 : y ∈ pointees sp o3.hist := by rw [← e4]; exact hyp
    cases hyDb : inD db.D y with
    | true =>
      -- taken, so written: the slot names its canonical object
      obtain ⟨h', rfl, hc'⟩ := hc3.rootD hv o3 ho3 y sl hsl hyp3 hyDb
      exact hcanpos y h' hc'
    | false =>
      have hyt := htakenND y hyDb
      -- a root child is an index node
      have hyd : y ∉ dataIds sp al db tr := by
        intro hyd
        obtain ⟨o0, ho0, hc0, hn0⟩ := ha.root
        rw [ho3, Option.some.injEq] at ho0
        subst ho0
        obtain ⟨n, hn, hh, -, -⟩ := ha.cc _ o3 ho3 hc0
        rw [hn0, ← hP] at hn
        rw [hh] at hyp3
        obtain ⟨my, cy, htop⟩ := (hinv'.vr hv).top_of_pointee (by rw [hP']; exact hn) hyp3
        obtain ⟨-, n2, hn2, hd2⟩ := step_dataIds_spec sp al db tr hinv hstep hyd
        have := htop.1
        rw [hP', hn2, Option.some.injEq] at this
        subst this
        rw [htop.2.2.2.1] at hd2; cases hd2
      rw [hsref _ o3 ho3 y sl hsl hyd hyt, hc3.rootClean hv o3 ho3 y sl hsl hyp3 hyDb, hS', hnotw y hyd hyt]
  · -- snapND
    intro h o6 r ho6 hco hp hrD
    obtain ⟨o3, ho3, e1, -, -, -, e5, -⟩ := hobj h o6 ho6
    have hc3' : o3.canonical = false := by rw [← e5]; exact hco
    obtain ⟨o6', ho6', -, -, hp6, -⟩ := hsnap6 h o3 ho3 hc3'
    rw [ho6, Option.some.injEq] at ho6'
    subst ho6'
    rw [hp6] at hp
    have hrD' : (o3.node, r) ∈ (parts sp al db tr).r7.1 := by rw [← e1]; exact hrD
    rcases step_D'_entry (al := al) (tr := tr) hinv hrD' with hk | ⟨hdb, -⟩
    · -- a snapshot's position is a record of db.S
      obtain ⟨r', w, hp', hw, -⟩ := ha.snap h o3 ho3 hc3'
      rw [hp, Option.some.injEq] at hp'
      subst hp'
      obtain ⟨R, hR, -, -⟩ := versionAt_spec hw
      have := (List.getElem?_eq_some_iff.mp hR).1
      rw [hinv.len] at this
      omega
    · exact hc3.snapND h o3 r ho3 hc3' hp hdb


/-- One transaction of the physical writer keeps T9's invariant: its reads, its
walk to the paths, the change, and the writes. -/
theorem CInv.evictTrans_ok (hsp : SpecOK sp) (hinv : Inv sp db k) (hmk : al.mark = true)
    {m : Mem V} (hm : EInv sp db S0 k m) (hc : CInv sp db S0 m) (hev : EvLogic sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) (hphys : PhysStep sp db.P (k + 1) (parts sp al db tr).c)
    (hcopy : CopyStep sp db.P (k + 1) (parts sp al db tr).c) (htree : treeAt sp db.P k)
    (hinv' : Inv sp (step sp al db tr) (k + 1)) (hev' : EvLogic sp (step sp al db tr) (k + 1)) :
    CInv sp (step sp al db tr) S0 (evictTrans sp al S0 db m tr).2 := by
  have hls : LiveSub sp := hsp.liveSub
  have hlen := hinv.len
  have hK1 : k + 1 - 1 = k := by omega
  obtain ⟨hm1, hv⟩ := hm.view4_ok hinv hls hev
  have hc1 : CInv sp db S0 (m.view4 sp S0 db.S k).1 := hc.read4 hinv hm k
  have hcx : sp.exec tr db.S.length (m.view4 sp S0 db.S (db.S.length - 1)).2 = (parts sp al db tr).c := by
    rw [hlen, hK1, hv, parts_c, hlen, hK1]
  rw [evictTrans_eq, hcx, evictAfter_eq]
  have hm1' : EInv sp db S0 k (m.view4 sp S0 db.S (db.S.length - 1)).1 := by rw [hlen, hK1]; exact hm1
  have hc1' : CInv sp db S0 (m.view4 sp S0 db.S (db.S.length - 1)).1 := by rw [hlen, hK1]; exact hc1
  generalize (m.view4 sp S0 db.S (db.S.length - 1)).1 = m1 at hm1' hc1' ⊢
  -- The writer's paths.
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
  have hc2 := CInv.reachPath4 (S0 := S0) hinv hls hev hpr
    ((pathOf sp db.P (parts sp al db tr).c (k + 1)).mergeSort (fun a b => decide (lev db.P b ≤ lev db.P a)))
    m1 hm1' hc1'
  -- The change.
  have ha := hm2.applyChange4_ok hinv hls hpd hstep hphys hcopy htree
  have hc3 := hc2.applyChange4 hinv hm2 hstep
  generalize hm2def : ((pathOf sp db.P (parts sp al db tr).c (k + 1)).mergeSort
    (fun a b => decide (lev db.P b ≤ lev db.P a))).foldl
      (Mem.reachOnPath4 sp S0 db.S db.P (k + 1) (pathOf sp db.P (parts sp al db tr).c (k + 1))) m1 = m2
    at hm2 hpd hc2 ha hc3
  have hroot3 : sp.virt = true → ∀ o, (m2.applyChange4 sp db.P (k + 1) (parts sp al db tr).c).obj?
      (m2.applyChange4 sp db.P (k + 1) (parts sp al db tr).c).root = some o → ∀ y sl, o.slot? y = some sl →
      y ∈ pointees sp o.hist → (y ∈ pathOf sp db.P (parts sp al db tr).c (k + 1) ∨
        y ∈ (parts sp al db tr).c.new.map (·.id)) →
      ∃ h', sl = Slot.mem h' ∧ (m2.applyChange4 sp db.P (k + 1) (parts sp al db tr).c).canonicalOf y = some h' :=
    fun hv _ ho _ _ hsl hyp hy => hm2.rootSlots_change hinv hls hstep hv hpr hpd ho hsl hyp hy
  have hpre : preWrite sp S0 db (parts sp al db tr).c m1 =
      m2.applyChange4 sp db.P (k + 1) (parts sp al db tr).c := by
    unfold preWrite; rw [hlen, ← hm2def]; rfl
  rw [hpre, hlen]
  generalize m2.applyChange4 sp db.P (k + 1) (parts sp al db tr).c = m3 at ha hc3 hroot3 ⊢
  -- The writes.
  obtain ⟨e1, -, -, e4⟩ := ha.loops_vs hsp hinv hmk hstep hinv'
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
  have hm6 := ha.final_ok hsp hinv hmk hstep hinv' hev' hfr e4
  exact CInv.next hsp hinv hmk hstep hinv' ha hc3 hroot3 hfr hm6

end Next

end SIS
