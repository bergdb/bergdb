/-
Proofs about the physical layer, part 6: a read through the physical layer
gives P (bergdb item 001, WP L3).
-/
import SIS.Proof.PhysLogic

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

section Read

variable {sp : Spec V T} {db : DB V T} {K k : Nat} {m : Mem V}

/-- A data node's version, any of them, is good. -/
theorem PCtx.good_dataVer (hctx : PCtx sp db k) {y : NodeId} {n : Node V}
    (hn : db.P.get? y = some n) (hd : n.isData = true) {r : Nat} {w : Version V}
    (hw : db.S.versionAt r y = some w) (t : Time) : good sp db.S db.P t w = true :=
  hctx.inv.good_data hctx.ls hn hd (hctx.dataOnce y n r w hn hd hw) t

/-- An object at least as new as a version good for t can be read at t. -/
theorem MemInv.atLeast_readable (hm : MemInv sp db K m) (hctx : PCtx sp db k) {y : NodeId}
    {h' : Nat} {r' : Nat} (hal : AtLeast m y h' (some r')) {u : Version V}
    (hu : db.S.versionAt r' y = some u) {t : Time} (hg : good sp db.S db.P t u = true) :
    Readable sp db m K t h' y := by
  obtain ⟨o', ho', hy', hc'⟩ := hal
  refine ⟨o', ho', hy', ?_⟩
  cases hcan : o'.canonical
  · right
    obtain ⟨w0, hw0, -⟩ := hm.snap h' o' ho' hcan
    refine ⟨w0, hw0, fun _ => ?_⟩
    obtain ⟨p0, hp0, hv0, -, hd0, -⟩ := hw0
    rw [hy'] at hv0
    rcases hc' with hc' | hc' | ⟨p, hp, hle⟩
    · rw [hcan] at hc'; cases hc'
    · obtain ⟨-, -, n0, hn0, -, -, hd0'⟩ := hctx.inv.version_node hv0
      exact hctx.good_dataVer hn0 (by rw [← hd0', ← hd0, hc']) hv0 t
    · rw [hp0, Option.some.injEq] at hp
      subst hp
      exact hctx.inv.newer hctx.ls (u.level + 1) r' p0 y u w0 (by omega) hu hv0 (hle r' rfl) t hg
  · exact Or.inl rfl

/-- The slots of a snapshot of a version that is good for t are good for t. -/
theorem MemInv.snap_slotGood (hm : MemInv sp db K m) (hctx : PCtx sp db k) {o : Obj V}
    {w : Version V} (hss : SnapSlots sp db m o w) (hhw : o.hist = w.hist) {t : Time}
    (hg : good sp db.S db.P t w = true) {y : NodeId} (hy : y ∈ sp.live (o.hist.upTo t)) :
    ∃ sl, o.slot? y = some sl ∧ SlotGood sp db m K t y sl := by
  obtain ⟨e, he, hye⟩ := hctx.ls _ _ hy
  have hyp : y ∈ pointees sp o.hist := (mem_pointees sp _ y).mpr ⟨e, (mem_upTo.mp he).1, hye⟩
  obtain ⟨sl, hsl⟩ := Option.isSome_iff_exists.mp (hss.1 y hyp)
  refine ⟨sl, hsl, ?_⟩
  rw [good_iff] at hg
  obtain ⟨-, hch⟩ := hg
  obtain ⟨r, u, hr, hu, -, hgu⟩ := hch y (by rw [← hhw]; exact hy)
  obtain ⟨r', u', hr', hu', hle⟩ := hctx.inv.ruleR_ge hu (lastSp db.S)
  have hgu' := hctx.inv.newer hctx.ls (u.level + 1) r r' y u u' (by omega) hu hu' hle t hgu
  rcases hss.2 y sl hsl with h1 | ⟨h', h1, hal⟩
  · subst h1
    right
    rw [hr]
    exact ⟨r', u', hr', hu', hgu'⟩
  · subst h1
    rw [hr, hr'] at hal
    exact hm.atLeast_readable hctx hal hu' hgu'

/-- What a readable object holds at t: the node's history at t, and its level. -/
theorem MemInv.readable_facts (hm : MemInv sp db K m) (hctx : PCtx sp db k) {t : Time}
    (ht : t ≤ K) {h : Nat} {y : NodeId} (hrd : Readable sp db m K t h y) {n : Node V}
    (hn : db.P.get? y = some n) :
    ∃ o, m.obj? h = some o ∧ o.node = y ∧ o.hist.upTo t = n.hist.upTo t ∧ o.level = n.level := by
  obtain ⟨o, ho, hy, hc⟩ := hrd
  refine ⟨o, ho, hy, ?_⟩
  rcases hc with hc | ⟨w, hw, hg⟩
  · obtain ⟨-, ⟨n', hn', hh, hl, -⟩, -⟩ := hm.canon h o ho hc
    rw [hy, hn, Option.some.injEq] at hn'
    subst hn'
    exact ⟨by rw [hh, upTo_upTo _ ht], hl⟩
  · obtain ⟨r, -, hv, hl, -, h5⟩ := hw
    rw [hy] at hv
    obtain ⟨-, -, n', hn', hwh, hwl, -⟩ := hctx.inv.version_node hv
    rw [hn, Option.some.injEq] at hn'
    subst hn'
    refine ⟨?_, by rw [hl, hwl]⟩
    rcases h5 with ⟨h6, -⟩ | ⟨h6, -, -, h9⟩
    · have := hg h6
      rw [good_iff] at this
      obtain ⟨⟨n'', hn'', hc'⟩, -⟩ := this
      rw [(hctx.inv.version_node hv).1, hn, Option.some.injEq] at hn''
      subst hn''
      rw [h6]; exact hc'
    · unfold histAt at h9
      rw [hy, hn] at h9
      simp only [Option.map_some, Option.getD_some] at h9
      have h10 : n.hist.upTo t = [] := by rw [← upTo_upTo _ ht, h9]; rfl
      have h11 : o.hist = [] := by
        rw [h6]
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro e he
        rw [hwh] at he
        have he1 := mem_upTo.mp he
        have he2 := mem_upTo.mp he1.1
        have : e ∈ n.hist.upTo K := mem_upTo.mpr ⟨he2.1, by have := hm.sK; omega⟩
        rw [h9] at this; cases this
      rw [h11, h10]; rfl

/-- A fold that keeps an invariant of the memory and appends a list per element. -/
theorem fold_inv {α : Type} (f : Mem V × List α → NodeId → Mem V × List α) (I : Mem V → Prop)
    (g : NodeId → List α) :
    ∀ (L : List NodeId), (∀ acc z, z ∈ L → I acc.1 → I (f acc z).1 ∧ (f acc z).2 = acc.2 ++ g z) →
      ∀ acc, I acc.1 → I (L.foldl f acc).1 ∧ (L.foldl f acc).2 = acc.2 ++ L.flatMap g := by
  intro L
  induction L with
  | nil => intro _ acc hI; exact ⟨hI, by simp⟩
  | cons z L ih =>
    intro hstep acc hI
    simp only [List.foldl_cons, List.flatMap_cons]
    obtain ⟨h1, h2⟩ := hstep acc z (List.mem_cons_self) hI
    obtain ⟨h3, h4⟩ := ih (fun acc' z' hz' hI' => hstep acc' z' (List.mem_cons_of_mem z hz') hI') _ h1
    exact ⟨h3, by rw [h4, h2, List.append_assoc]⟩

/-- One step of a read's fold over the live children of object o at handle h. -/
def readStep (sp : Spec V T) (S : Stream V T) (fuel : Nat) (t : Time) (h : Nat) (o : Obj V)
    (acc : Mem V × List (NodeId × History V)) (y : NodeId) : Mem V × List (NodeId × History V) :=
  match acc.1.follow sp S h y false with
  | (m1, some h1) =>
    match m1.obj? h1 with
    | some o1 =>
      if o1.level < o.level then
        let r := Mem.readAt sp S fuel m1 t h1
        (r.1, acc.2 ++ r.2)
      else (m1, acc.2)
    | none => (m1, acc.2)
  | (m1, none) => (m1, acc.2)

theorem readAt_succ_eq (sp : Spec V T) (S : Stream V T) (fuel : Nat) (m : Mem V) (t : Time)
    (h : Nat) {o : Obj V} (ho : m.obj? h = some o) :
    m.readAt sp S (fuel + 1) t h =
      (sp.live (o.hist.upTo t)).foldl (readStep sp S fuel t h o) (m, [(o.node, o.hist.upTo t)]) := by
  rw [Mem.readAt]; simp only [ho]; rfl

/-- A read at time t from a readable object of a node y reachable at t gives
the nodes reachable from y at t, each with its history at t; the invariant is
kept. -/
theorem MemInv.readAt_ok (hctx : PCtx sp db k) (hfix : FixedLe sp db K) {t : Time} (ht : t ≤ K) :
    ∀ (fuel : Nat) (m : Mem V) (h : Nat) (y : NodeId) (n : Node V), MemInv sp db K m →
      Readable sp db m K t h y → db.P.get? y = some n → reachable sp db.P t y = true →
      n.level < fuel →
      MemInv sp db K (m.readAt sp db.S fuel t h).1 ∧ m.Le (m.readAt sp db.S fuel t h).1 ∧
        m.KeepCore (m.readAt sp db.S fuel t h).1 ∧
        (m.readAt sp db.S fuel t h).2 =
          (reachFrom sp db.P t y n).map (fun z => (z, histAt db.P z t)) := by
  intro fuel
  induction fuel with
  | zero => intro m h y n _ _ _ _ hlt; omega
  | succ fuel ih =>
    intro m h y n hm hrd hn hr hlt
    obtain ⟨o, ho, hoy, hoh, hol⟩ := hm.readable_facts hctx ht hrd hn
    rw [readAt_succ_eq sp db.S fuel m t h ho]
    -- The parent: canonical, or a snapshot of a version good for t.
    have hpar : ∀ (m' : Mem V), MemInv sp db K m' → m.KeepCore m' → m.Le m' →
        ∀ z ∈ sp.live (o.hist.upTo t), ∃ o' sl, m'.obj? h = some o' ∧ o'.core = o.core ∧
          o'.slot? z = some sl ∧ SlotGood sp db m' K t z sl := by
      intro m' hm' hkc hle z hz
      obtain ⟨o', ho', hc'⟩ := hkc h o ho
      have e4 : o'.hist = o.hist := by
        have := congrArg (fun c => c.2.2.2.1) hc'; simpa [Obj.core] using this
      have e5 : o'.canonical = o.canonical := by
        have := congrArg (fun c => c.2.2.2.2.1) hc'; simpa [Obj.core] using this
      have e1 : o'.node = o.node := by
        have := congrArg (fun c => c.1) hc'; simpa [Obj.core] using this
      have e6 : o'.pos = o.pos := by
        have := congrArg (fun c => c.2.2.2.2.2) hc'; simpa [Obj.core] using this
      obtain ⟨o0, ho0, -, hc⟩ := hrd
      rw [ho, Option.some.injEq] at ho0
      subst ho0
      cases hcan : o.canonical
      · -- a snapshot
        have hco' : o'.canonical = false := by rw [e5, hcan]
        obtain ⟨w', hw', hss'⟩ := hm'.snap h o' ho' hco'
        rcases hc with hc | ⟨w, hw, hg⟩
        · rw [hc] at hcan; cases hcan
        · -- the version is the same; o is uncut, or cut back and empty
          have hww : w' = w := by
            obtain ⟨r1, hp1, hv1, -⟩ := hw
            obtain ⟨r2, hp2, hv2, -⟩ := hw'
            rw [e6, hp1, Option.some.injEq] at hp2; subst hp2
            rw [e1, hv1, Option.some.injEq] at hv2; exact hv2.symm
          subst hww
          obtain ⟨r1, -, hv1, -, -, h5⟩ := hw
          rcases h5 with ⟨h6, -⟩ | ⟨h6, -, -, h9⟩
          · obtain ⟨sl, hsl, hg'⟩ := hm'.snap_slotGood hctx hss' (by rw [e4, h6]) (hg h6)
              (by rw [e4]; exact hz)
            exact ⟨o', sl, ho', hc', hsl, hg'⟩
          · -- cut back: empty, so no live children
            exfalso
            have hnil : o.hist.upTo t = [] := by
              rw [hoh]
              unfold histAt at h9
              rw [hoy, hn] at h9
              simp only [Option.map_some, Option.getD_some] at h9
              rw [← upTo_upTo _ ht, h9]; rfl
            rw [hnil, live_nil hctx.ls] at hz
            cases hz
      · -- canonical
        have hco' : o'.canonical = true := by rw [e5, hcan]
        obtain ⟨-, -, -, c4, -⟩ := hm'.canon h o' ho' hco'
        obtain ⟨sl, hsl, hg'⟩ := c4 t ht (by rw [e1, hoy]; exact hr) z (by rw [e4]; exact hz)
        exact ⟨o', sl, ho', hc', hsl, hg'⟩
    -- The fold over the live children.
    have hlive : sp.live (o.hist.upTo t) = sp.live (n.hist.upTo t) := by rw [hoh]
    obtain ⟨hI, hL⟩ := fold_inv (V := V) (readStep sp db.S fuel t h o)
      (fun m' => MemInv sp db K m' ∧ m.Le m' ∧ m.KeepCore m')
      (fun z => match db.P.get? z with
        | some nz => if nz.level < n.level then (reachFrom sp db.P t z nz).map
            (fun z => (z, histAt db.P z t)) else []
        | none => []) (sp.live (o.hist.upTo t)) (by
        intro acc z hz ⟨hmA, hleA, hkcA⟩
        obtain ⟨o', sl, ho', hc', hsl, hg⟩ := hpar acc.1 hmA hkcA hleA z hz
        -- z is a node, on a lower level, reachable at t
        have hz' : z ∈ sp.live (n.hist.upTo t) := by rw [← hlive]; exact hz
        obtain ⟨e, he, hze⟩ := hctx.ls _ _ hz'
        obtain ⟨nz, hnz, hlvl⟩ := hctx.inv.ptrs y n hn e (mem_upTo.mp he).1 z hze
        have hrz : reachable sp db.P t z = true := by
          rw [reachable_iff] at hr ⊢
          exact Reach.child hr hn hz' hnz hlvl
        have hzne : z ≠ o'.node := by
          have e1 : o'.node = o.node := by
            have := congrArg (fun c => c.1) hc'; simpa [Obj.core] using this
          rw [e1, hoy]
          intro hzy
          rw [hzy, hn, Option.some.injEq] at hnz
          subst hnz
          omega
        obtain ⟨m1, h1, hev, hm1, hle1, hkc1, hrd1, -, -⟩ :=
          hmA.follow_reader hctx hfix ho' hsl hzne ht hrz hg
        have hfol : acc.1.follow sp db.S h z false = (m1, some h1) := hev
        obtain ⟨o1, ho1, -, -, hol1⟩ := hm1.readable_facts hctx ht hrd1 hnz
        obtain ⟨hI2, hle2, hkc2, hL2⟩ := ih m1 h1 z nz hm1 hrd1 hnz hrz (by omega)
        have hst : readStep sp db.S fuel t h o acc z =
            ((Mem.readAt sp db.S fuel m1 t h1).1, acc.2 ++ (Mem.readAt sp db.S fuel m1 t h1).2) := by
          unfold readStep
          rw [hfol]
          simp only [ho1, hol1, hol, hlvl, ↓reduceIte]
        rw [hst]
        refine ⟨⟨hI2, (hleA.trans hle1).trans hle2, (hkcA.trans hkc1).trans hkc2⟩, ?_⟩
        simp only [hnz, hlvl, ↓reduceIte]
        rw [hL2]) (m, [(o.node, o.hist.upTo t)]) ⟨hm, Mem.Le.refl m, Mem.KeepCore.refl m⟩
    refine ⟨hI.1, hI.2.1, hI.2.2, ?_⟩
    rw [hL, reachFrom_eq, List.map_cons, List.map_flatMap, hoy, hoh]
    unfold histAt
    rw [hn]
    simp only [Option.map_some, Option.getD_some, List.singleton_append, List.cons.injEq, true_and]
    apply flatMap_congr_mem
    intro z _
    cases hnz : db.P.get? z with
    | none => rfl
    | some nz =>
      simp only
      split <;> rfl

/-- A read at time t from the root's object gives P@t: each node reachable at t,
with its history at t. The invariant is kept. -/
theorem MemInv.read_ok (hm : MemInv sp db K m) (hctx : PCtx sp db k) (hfix : FixedLe sp db K)
    {t : Time} (ht : t ≤ K) :
    MemInv sp db K (m.read sp db.S t).1 ∧ m.Le (m.read sp db.S t).1 ∧
      (m.read sp db.S t).2 = (reachList sp db.P t).map (fun z => (z, histAt db.P z t)) := by
  obtain ⟨-, o, ho, hc, hn⟩ := hm.root
  obtain ⟨n0, hn0⟩ := Option.isSome_iff_exists.mp hctx.inv.rootIn
  have hrd : Readable sp db m K t m.root SIS.root := ⟨o, ho, hn, Or.inl hc⟩
  obtain ⟨o', ho', -, -, hol⟩ := hm.readable_facts hctx ht hrd hn0
  rw [ho, Option.some.injEq] at ho'
  subst ho'
  have := MemInv.readAt_ok hctx hfix ht (o.level + 1) m m.root SIS.root n0 hm hrd hn0
    (reachable_root hn0 t) (by omega)
  unfold Mem.read
  rw [ho]
  simp only
  refine ⟨this.1, this.2.1, ?_⟩
  rw [this.2.2.2]
  unfold reachList
  rw [hn0]

end Read

end SIS
