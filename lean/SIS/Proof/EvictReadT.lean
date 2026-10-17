/-
Proofs for stage 2 (bergdb item 001, WP E4), part 3: a read at any time t up to
the last record, through the Level 4 loader, gives P at t (T-READ). Every
object it reaches is canonical, or the snapshot of a version good for t; the
invariant for earlier times (`HInv`) gives the slots it follows.
-/
import SIS.Proof.EvictHistTrans

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

section ReadT

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : Mem V}

/-- What an object that can be read at t holds: its node's level and kind, and
its history up to t. -/
theorem EInv.readableT_facts (hinv : Inv sp db k) (hm : EInv sp db S0 k m) {t : Time} {h : Nat}
    {y : NodeId} (hrd : ReadableT sp db m t h y) {n : Node V} (hn : db.P.get? y = some n) :
    ∃ o, m.obj? h = some o ∧ o.node = y ∧ o.hist.upTo t = n.hist.upTo t ∧ o.level = n.level ∧
      o.isData = n.isData := by
  obtain ⟨o, ho, hoy, hc⟩ := hrd
  refine ⟨o, ho, hoy, ?_⟩
  cases hco : o.canonical with
  | true =>
    obtain ⟨n', hn', h1, h2, h3⟩ := hm.cc h o ho hco
    rw [hoy, hn, Option.some.injEq] at hn'
    subst hn'
    exact ⟨by rw [h1], h2, h3⟩
  | false =>
    rcases hc with hc | ⟨r, w, hp, hw, hg⟩
    · rw [hco] at hc; cases hc
    obtain ⟨r1, w1, e1, e2, e3, e4, e5, -⟩ := hm.snap h o ho hco
    rw [hp, Option.some.injEq] at e1
    subst e1
    rw [hoy, hw, Option.some.injEq] at e2
    subst e2
    obtain ⟨hwy, -, n', hn', -, hvl, hvd⟩ := hinv.version_node hw
    rw [hn, Option.some.injEq] at hn'
    subst hn'
    rw [good_iff] at hg
    obtain ⟨⟨n'', hn'', hh⟩, -⟩ := hg
    rw [hwy, hn, Option.some.injEq] at hn''
    subst hn''
    exact ⟨by rw [e3, hh], by rw [e4, hvl], by rw [e5, hvd]⟩

theorem ReadableT.keepCore {t : Time} {h : Nat} {y : NodeId} {m' : Mem V} (hr : ReadableT sp db m t h y)
    (hk : m.KeepCore m') : ReadableT sp db m' t h y := by
  obtain ⟨o, ho, hn, hc⟩ := hr
  obtain ⟨o', ho', hcore⟩ := hk h o ho
  have e1 : o'.node = o.node := congrArg (fun c => c.1) hcore
  have e5 : o'.canonical = o.canonical := congrArg (fun c => c.2.2.2.2.1) hcore
  have e6 : o'.pos = o.pos := congrArg (fun c => c.2.2.2.2.2) hcore
  exact ⟨o', ho', by rw [e1, hn], by rw [e5, e6]; exact hc⟩

/-- A slot for y that a read at t may follow: to an object that can be read at
t; or a stream slot that the loader turns into y's canonical object, or into a
version good for t. -/
def SlotGoodT (sp : Spec V T) (S0 : Stream V T) (db : DB V T) (m : Mem V) (t : Time) (y : NodeId) :
    Slot → Prop
  | Slot.mem h' => ReadableT sp db m t h' y
  | Slot.stream r => m.canonicalOf y ≠ none ∨ GoodRef sp S0 db m t y r

/-- The slots of an object that can be read at t, for the live children at t:
as a read at t may follow them. -/
theorem EInv.readableT_slot (hinv : Inv sp db k) (hls : LiveSub sp) (hm : EInv sp db S0 k m)
    (hh : HInv sp db S0 k m) {t : Time} (ht : t ≤ k) {h : Nat} {y : NodeId} (hrd : ReadableT sp db m t h y)
    (hr : reachable sp db.P t y = true) {o : Obj V} (ho : m.obj? h = some o) {z : NodeId}
    (hz : z ∈ sp.live (o.hist.upTo t)) :
    ∃ sl, o.slot? z = some sl ∧ SlotGoodT sp S0 db m t z sl := by
  obtain ⟨o1, ho1, hoy, hc⟩ := hrd
  rw [ho, Option.some.injEq] at ho1
  subst ho1
  cases hco : o.canonical with
  | true =>
    obtain ⟨sl, hsl, hsh⟩ := hh h o ho hco t ht (by rw [hoy]; exact hr) z hz
    refine ⟨sl, hsl, ?_⟩
    cases sl with
    | mem h' => exact hsh
    | stream r =>
      rcases hsh with hg | ⟨hzD, -⟩
      · exact Or.inr hg
      · left
        have := hm.dCanon z hzD
        intro he; rw [he] at this; cases this
  | false =>
    rcases hc with hc | ⟨r, w, hp, hw, hg⟩
    · rw [hco] at hc; cases hc
    obtain ⟨sl, hsl, hsh, hstr⟩ := hm.snap_hist hinv hls ho hco hp (by rw [hoy]; exact hw) hg hz
    refine ⟨sl, hsl, ?_⟩
    cases sl with
    | mem h' => exact hsh o.node
    | stream r0 => exact Or.inr (hstr r0 rfl)

/-- The reader's follow keeps the objects' cores. -/
theorem EInv.reached4_keepCore (hm : EInv sp db S0 k m) {hp : Nat} {y : NodeId} {m1 : Mem V} {h1 : Nat}
    (h : m.reached4 sp S0 db.S hp y = some (m1, h1)) : m.KeepCore (m1.swz hp y h1) := by
  obtain ⟨op, sl, hop, hsl, hcase⟩ := reached4_cases h
  obtain ⟨-, -, hfr⟩ := hm.reached4_frame hop h
  intro h' o ho
  obtain ⟨o', ho', e1, e2, e3, e4, e5, e6, -⟩ := hfr h' o ho
  refine ⟨o', ho', ?_⟩
  rcases reached4_back hm h hop ho' with ⟨rfl, rfl⟩ | ⟨-, h2⟩ | ⟨-, hn, -⟩
  · rw [hop, Option.some.injEq] at ho; subst ho; rfl
  · rw [ho, Option.some.injEq] at h2; subst h2; rfl
  · subst hn; rw [hm.fresh _ (Nat.le_refl _)] at ho; cases ho

/-- A reader's follow of a slot that a read at t may follow reaches an object
that can be read at t; both invariants and the objects' cores are kept. -/
theorem EInv.follow_goodT (hinv : Inv sp db k) (hm : EInv sp db S0 k m) (hh : HInv sp db S0 k m)
    {t : Time} {hp : Nat} {op : Obj V} (hop : m.obj? hp = some op) {z : NodeId} {sl : Slot}
    (hsl : op.slot? z = some sl) (hg : SlotGoodT sp S0 db m t z sl) :
    ∃ m1 h1, m.follow4 sp S0 db.S hp z false = (m1, some h1) ∧ EInv sp db S0 k m1 ∧
      HInv sp db S0 k m1 ∧ m.KeepCore m1 ∧ ReadableT sp db m1 t h1 z := by
  have hfin : ∀ (m1 : Mem V) h1, m.reached4 sp S0 db.S hp z = some (m1, h1) →
      ReadableT sp db (m1.swz hp z h1) t h1 z →
      ∃ m1' h1', m.follow4 sp S0 db.S hp z false = (m1', some h1') ∧ EInv sp db S0 k m1' ∧
        HInv sp db S0 k m1' ∧ m.KeepCore m1' ∧ ReadableT sp db m1' t h1' z := by
    intro m1 h1 hrc hrd
    refine ⟨m1.swz hp z h1, h1, by rw [follow4_eq, hrc]; rfl, hm.reached4 hinv hrc,
      (hh.reached4 hinv hm hrc).1, hm.reached4_keepCore hrc, hrd⟩
  cases sl with
  | mem h' =>
    obtain ⟨o', ho', hn'⟩ := hm.slotsNode hp op hop z h' hsl
    have hrc : m.reached4 sp S0 db.S hp z = some (m, h') := by
      unfold Mem.reached4; rw [hop]; simp only [Option.bind_some, hsl, ho', Option.isSome_some, ↓reduceIte]
    exact hfin m h' hrc (ReadableT.keepCore hg (hm.reached4_keepCore hrc))
  | stream r =>
    cases hc : m.canonicalOf z with
    | some h0 =>
      have hrc : m.reached4 sp S0 db.S hp z = some (m, h0) := by
        unfold Mem.reached4; rw [hop]; simp only [Option.bind_some, hsl, hc]
      obtain ⟨o0, ho0, hc0, hn0⟩ := hm.obj_of_canonicalOf hc
      exact hfin m h0 hrc (ReadableT.keepCore ⟨o0, ho0, hn0, Or.inl hc0⟩ (hm.reached4_keepCore hrc))
    | none =>
      rcases hg with hg | ⟨r', w, e1, e2, e3⟩
      · exact absurd hc hg
      have hrc : m.reached4 sp S0 db.S hp z =
          some ((m.addObj (Obj.ofVersion sp w none)).1, m.next) := by
        unfold Mem.reached4; rw [hop]; simp only [Option.bind_some, hsl, hc, e1, e2]; rfl
      obtain ⟨-, -, -, hreach⟩ := hh.reached4 hinv hm hrc
      obtain ⟨op', sl', hop', hsl', hrd⟩ := hreach
      rw [hop, Option.some.injEq] at hop'
      subst hop'
      rw [hsl, Option.some.injEq] at hsl'
      subst hsl'
      exact hfin _ _ hrc (hrd t z (Or.inl ⟨r', w, e1, e2, e3⟩))

/-- A read at t from an object that can be read at t, of a node reachable at t,
gives the nodes reachable from it at t, each with its node at t; both
invariants and the objects' cores are kept. -/
theorem EInv.readAt4T_ok (hinv : Inv sp db k) (hls : LiveSub sp) {t : Time} (ht : t ≤ k) :
    ∀ (fuel : Nat) (m : Mem V) (h : Nat) (y : NodeId) (n : Node V), EInv sp db S0 k m → HInv sp db S0 k m →
      ReadableT sp db m t h y → db.P.get? y = some n → reachable sp db.P t y = true → n.level < fuel →
      EInv sp db S0 k (m.readAt4 sp S0 db.S fuel t h).1 ∧ HInv sp db S0 k (m.readAt4 sp S0 db.S fuel t h).1 ∧
        m.KeepCore (m.readAt4 sp S0 db.S fuel t h).1 ∧
        (m.readAt4 sp S0 db.S fuel t h).2 = (reachFrom sp db.P t y n).map (fun z => (z, nodeAt db.P z t)) := by
  intro fuel
  induction fuel with
  | zero => intro m h y n _ _ _ _ _ hlt; omega
  | succ fuel ih =>
    intro m h y n hm hh hrd hn hr hlt
    obtain ⟨o, ho, hoy, hoh, hol, hod⟩ := hm.readableT_facts hinv hrd hn
    rw [readAt4_succ_eq sp S0 db.S fuel m t h ho]
    have hpar : ∀ (m' : Mem V), EInv sp db S0 k m' → HInv sp db S0 k m' → m.KeepCore m' →
        ∀ z ∈ sp.live (o.hist.upTo t), ∃ o' sl, m'.obj? h = some o' ∧ o'.core = o.core ∧
          o'.slot? z = some sl ∧ SlotGoodT sp S0 db m' t z sl := by
      intro m' hm' hh' hkc z hz
      obtain ⟨o', ho', hc'⟩ := hkc h o ho
      have e4 : o'.hist = o.hist := congrArg (fun c => c.2.2.2.1) hc'
      obtain ⟨sl, hsl, hg⟩ := hm'.readableT_slot hinv hls hh' ht (hrd.keepCore hkc) hr ho'
        (by rw [e4]; exact hz)
      exact ⟨o', sl, ho', hc', hsl, hg⟩
    have hlive : sp.live (o.hist.upTo t) = sp.live (n.hist.upTo t) := by rw [hoh]
    obtain ⟨hI, hL⟩ := fold_inv (V := V) (readStep4 sp S0 db.S fuel t h o)
      (fun m' => EInv sp db S0 k m' ∧ HInv sp db S0 k m' ∧ m.KeepCore m')
      (fun z => match db.P.get? z with
        | some nz => if nz.level < n.level then (reachFrom sp db.P t z nz).map
            (fun z => (z, nodeAt db.P z t)) else []
        | none => []) (sp.live (o.hist.upTo t)) (by
        intro acc z hz ⟨hmA, hhA, hkcA⟩
        obtain ⟨o', sl, ho', hc', hsl, hg⟩ := hpar acc.1 hmA hhA hkcA z hz
        have hz' : z ∈ sp.live (n.hist.upTo t) := by rw [← hlive]; exact hz
        obtain ⟨hrz, -, nz, hnz, hlvl⟩ := hinv.reach_child hls hn hr hz'
        obtain ⟨m1, h1, hev1, hm1, hh1, hkc1, hrd1⟩ := hmA.follow_goodT hinv hhA ho' hsl hg
        obtain ⟨o1, ho1, -, -, hol1, -⟩ := hm1.readableT_facts hinv hrd1 hnz
        obtain ⟨hI2, hH2, hkc2, hL2⟩ := ih m1 h1 z nz hm1 hh1 hrd1 hnz hrz (by omega)
        have hst : readStep4 sp S0 db.S fuel t h o acc z =
            ((Mem.readAt4 sp S0 db.S fuel m1 t h1).1, acc.2 ++ (Mem.readAt4 sp S0 db.S fuel m1 t h1).2) := by
          unfold readStep4
          rw [hev1]
          simp only [ho1, hol1, hol, hlvl, ↓reduceIte]
        rw [hst]
        refine ⟨⟨hI2, hH2, (hkcA.trans hkc1).trans hkc2⟩, ?_⟩
        simp only [hnz, hlvl, ↓reduceIte]
        rw [hL2]) (m, [(o.node, o.nodeAt t)]) ⟨hm, hh, Mem.KeepCore.refl m⟩
    refine ⟨hI.1, hI.2.1, hI.2.2, ?_⟩
    have hnode : o.nodeAt t = nodeAt db.P y t := by
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

/-- A read at any time t ≤ k from the root's object gives P at t, and keeps both
invariants. -/
theorem EInv.read4T_ok (hinv : Inv sp db k) (hls : LiveSub sp) (hm : EInv sp db S0 k m)
    (hh : HInv sp db S0 k m) {t : Time} (ht : t ≤ k) :
    EInv sp db S0 k (m.read4 sp S0 db.S t).1 ∧ HInv sp db S0 k (m.read4 sp S0 db.S t).1 ∧
      (m.read4 sp S0 db.S t).2 = (reachList sp db.P t).map (fun z => (z, nodeAt db.P z t)) := by
  obtain ⟨o, ho, hc, hn⟩ := hm.root
  obtain ⟨n0, hn0⟩ := Option.isSome_iff_exists.mp hinv.rootIn
  have hrd : ReadableT sp db m t m.root SIS.root := ⟨o, ho, hn, Or.inl hc⟩
  obtain ⟨o', ho', -, -, hol, -⟩ := hm.readableT_facts hinv hrd hn0
  rw [ho, Option.some.injEq] at ho'
  subst ho'
  have := EInv.readAt4T_ok hinv hls ht (o.level + 1) m m.root SIS.root n0 hm hh hrd hn0
    (reachable_root hn0 t) (by omega)
  unfold Mem.read4
  rw [ho]
  simp only
  refine ⟨this.1, this.2.1, ?_⟩
  rw [this.2.2.2]
  unfold reachList
  rw [hn0]

end ReadT

/-! ## The invariant at R(0) and along runs -/

section Run

variable {sp : Spec V T} {al : Algo V T}

/-- At any state, the invariant at the last time follows from INV-SLOT's live
part: so it holds after the startup from R(0), where k is 0. -/
theorem HInv.of_live {db : DB V T} {S0 : Stream V T} {m : Mem V} (hinv : Inv sp db 0) (hls : LiveSub sp)
    (hm : EInv sp db S0 0 m) : HInv sp db S0 0 m := by
  intro h o ho hc t ht hr z hz
  have ht0 : t = 0 := by omega
  subst ht0
  obtain ⟨n, hn, hhist, -, -⟩ := hm.cc h o ho hc
  have hz' : z ∈ sp.live o.hist := by
    rw [hhist] at hz ⊢
    rw [upTo_of_forall _ _ (hinv.times _ n hn)] at hz
    exact hz
  obtain ⟨sl, hsl, hli⟩ := hm.live h o ho hc hr z hz'
  refine ⟨sl, hsl, ?_⟩
  cases hzD : inD db.D z with
  | true =>
    obtain ⟨h', rfl, hc'⟩ := hli.1 hzD
    obtain ⟨o', ho', hco', hn'⟩ := hm.obj_of_canonicalOf hc'
    exact ⟨o', ho', hn', Or.inl hco'⟩
  | false =>
    obtain ⟨hrz, -, hzw⟩ := hm.reach_child hinv hls ho hc hr hz
    exact hm.slotHist_clean hinv hls ho hsl hzD hzw (Nat.le_refl _) hrz (hli.2 hzD) o.node

/-- One transaction of a run with eviction, and its cache operations: the
invariant for reads at earlier times. -/
theorem HInv.run_step {ts : List T} (hok : RunOK sp al ts) (hph : PhysRunOK sp al ts)
    (hev : EvictRunOK sp al ts) (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) {j : Nat}
    (hjt : j < ts.length) {S0 : Stream V T} {m : Mem V} (hm : EInv sp (st sp al ts j) S0 j m)
    (hh : HInv sp (st sp al ts j) S0 j m) (ops : List CacheOp) :
    HInv sp (st sp al ts (j + 1)) S0 (j + 1)
      (ops.foldl (Mem.cacheOp sp S0 (evictTrans sp al S0 (st sp al ts j) m ts[j]).1.S
        (evictTrans sp al S0 (st sp al ts j) m ts[j]).1.D) (evictTrans sp al S0 (st sp al ts j) m ts[j]).2) := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hsp := hok.1
  have hinv := inv_st sp al ts hok hst j (by omega)
  have hinv' := inv_st sp al ts hok hst (j + 1) (by omega)
  have hlog := evLogic_st sp al ts hok hj hmk hev j (by omega)
  have hlog' := evLogic_st sp al ts hok hj hmk hev (j + 1) (by omega)
  have hc : (parts sp al (st sp al ts j) ts[j]).c = sp.exec ts[j] (j + 1) (view sp (st sp al ts j).P j) := by
    rw [parts_c, hinv.len, Nat.add_sub_cancel]
  have hstep : StepOK sp (st sp al ts j).P (j + 1) (parts sp al (st sp al ts j) ts[j]).c := by
    rw [hc]; exact hok.2 j hjt
  have hphys : PhysStep sp (st sp al ts j).P (j + 1) (parts sp al (st sp al ts j) ts[j]).c := by
    rw [hc]; exact hph j hjt
  have hcopy : CopyStep sp (st sp al ts j).P (j + 1) (parts sp al (st sp al ts j) ts[j]).c := by
    rw [hc]; exact hev.2 j hjt
  have htree : treeAt sp (st sp al ts j).P j := (hev.1 j (by omega)).tree
  rw [st_succ sp al ts hjt] at hinv' hlog' ⊢
  obtain ⟨h1, h2⟩ := hm.evictTrans_ok hsp hinv hmk hlog hstep hphys hcopy htree hinv' hlog'
  have h3 := HInv.evictTrans_ok hsp hinv hmk hm hh hlog hstep hphys hcopy htree hinv' hlog'
  rw [h1]
  exact HInv.cacheOps hinv' hsp.liveSub ops _ h2 h3

/-- The invariant for reads at earlier times, in every run with eviction and no
restart, from the Level 4 startup from R(0). -/
theorem HInv.run {ts : List (T × Bool × List CacheOp)} (hok : RunOK sp al (ts.map (·.1)))
    (hph : PhysRunOK sp al (ts.map (·.1))) (hev : EvictRunOK sp al (ts.map (·.1)))
    (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) (hnr : ∀ p ∈ ts, p.2.1 = false) :
    ∀ j ≤ ts.length, HInv sp (st sp al (ts.map (·.1)) j) (init sp).S j (runEvict sp al (ts.take j)).2.1 := by
  intro j
  induction j with
  | zero =>
    intro _
    have : runEvict sp al (ts.take 0) = (init sp, evictStartup sp (init sp).S, (init sp).S) := by
      simp [runEvict]
    rw [this, st_zero]
    exact HInv.of_live (inv_init sp hok.1) hok.1.liveSub (einv_init hok.1)
  | succ j ih =>
    intro hjt
    have hh := ih (by omega)
    obtain ⟨e1, e2, e3⟩ := TC_run_init hok hph hev hj hmk hnr j (by omega)
    have hjt' : j < ts.length := by omega
    have hjm : j < (ts.map (·.1)).length := by simp; omega
    rw [runEvict_succ sp al ts hjt']
    have hnrj : ts[j].2.1 = false := hnr _ (List.getElem_mem hjt')
    simp only [hnrj, Bool.false_eq_true, ↓reduceIte]
    rw [e1, e2]
    have htr : (ts.map (·.1))[j] = ts[j].1 := by simp
    have := HInv.run_step hok hph hev hj hmk hjm e3 hh ts[j].2.2
    rw [htr] at this
    exact this

end Run

end SIS
