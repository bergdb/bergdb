/-
Proofs about the physical layer with handles (bergdb item 009, phase 4a), part
3 of T-READ: a read through the handles at any time t up to the last record
gives P at t (`tr_handles`, `TR_handles` of SIS/HandleTheorems.lean). Every
object the read reaches
is canonical, or the snapshot of a version good for t; the invariant for
earlier times (`HInvH`) gives the pointers it follows: a follow of a pointer to
a node with a canonical object reaches that object, and any other follow
reaches an object that serves the slow path's reference, which names a version
good for t, so by lemma M the object is canonical or a snapshot of a version
good for t.
-/
import SIS.Proof.HandleHistTrans

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## Objects that can be read at t -/

section ReadableT

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : HMem V}

/-- What an object that can be read at t holds: its node's level and kind, and
its history up to t. -/
theorem HEInv.readableT_facts (hinv : Inv sp db k) (hm : HEInv sp db S0 k m) {t : Time} {b : Nat}
    {y : NodeId} (hrd : HReadableT sp db m t b y) {n : Node V} (hn : db.P.get? y = some n) :
    ∃ o, m.obj? b = some o ∧ o.node = y ∧ o.hist.upTo t = n.hist.upTo t ∧ o.level = n.level ∧
      o.isData = n.isData := by
  obtain ⟨o, ho, hoy, hc⟩ := hrd
  refine ⟨o, ho, hoy, ?_⟩
  cases hco : o.canonical with
  | true =>
    obtain ⟨n', hn', h1, h2, h3⟩ := hm.cc b o ho hco
    rw [hoy, hn, Option.some.injEq] at hn'
    subst hn'
    exact ⟨by rw [h1], h2, h3⟩
  | false =>
    rcases hc with hc | ⟨r, w, hp, hw, hg⟩
    · rw [hco] at hc; cases hc
    obtain ⟨r1, w1, e1, e2, e3, e4, e5, -, -⟩ := hm.snap b o ho hco
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

theorem HReadableT.keep {t : Time} {b : Nat} {y : NodeId} {m' : HMem V} (hr : HReadableT sp db m t b y)
    {o o' : HObj V} (ho : m.obj? b = some o) (ho' : m'.obj? b = some o') (hc : o'.core = o.core) :
    HReadableT sp db m' t b y := by
  obtain ⟨o1, ho1, hn, hcs⟩ := hr
  rw [ho, Option.some.injEq] at ho1
  subst ho1
  have e1 : o'.node = o.node := congrArg (fun c => c.1) hc
  have e5 : o'.canonical = o.canonical := congrArg (fun c => c.2.2.2.2.1) hc
  have e6 : o'.pos = o.pos := congrArg (fun c => c.2.2.2.2.2) hc
  exact ⟨o', ho', by rw [e1, hn], by rw [e5, e6]; exact hcs⟩

/-- A pointer for y that a read at t may follow: y has a canonical object, which
every follow of a pointer to y reaches; or the slow path's reference names a
version good for t. -/
def HPtrGoodT (sp : Spec V T) (S0 : Stream V T) (db : DB V T) (m : HMem V) (t : Time) (y : NodeId)
    (p : HPtr) : Prop :=
  (m.canonicalOf y).isSome = true ∨ HGoodRef sp S0 db m t y p

/-- A pointer's handle, if any, is of the pointer's pointee. -/
theorem HTableOK.ptr_nodes (ht : HTableOK m) {a : Nat} {o : HObj V} (ho : m.obj? a = some o)
    {y : NodeId} {p : HPtr} (hp : o.ptr? y = some p) :
    ∀ n hd, p.handle = some n → m.handle? n = some hd → hd.node = y := by
  intro n hd hn hh
  obtain ⟨hd', hh', hnd⟩ := ht.ptrNode ho hp hn
  rw [hh, Option.some.injEq] at hh'
  rw [hh']; exact hnd

/-- The pointers of an object that can be read at t, of a node reachable at t,
for its live children at t: as a read at t may follow them. -/
theorem HEInv.readableT_ptr (hinv : Inv sp db k) (hls : LiveSub sp) (hm : HEInv sp db S0 k m)
    (hh : HInvH sp db S0 k m) {t : Time} (ht : t ≤ k) {b : Nat} {y : NodeId}
    (hrd : HReadableT sp db m t b y) (hr : reachable sp db.P t y = true) {o : HObj V}
    (ho : m.obj? b = some o) {z : NodeId} (hz : z ∈ sp.live (o.hist.upTo t)) :
    ∃ p, o.ptr? z = some p ∧ HPtrGoodT sp S0 db m t z p := by
  obtain ⟨o1, ho1, hoy, hc⟩ := hrd
  rw [ho, Option.some.injEq] at ho1
  subst ho1
  cases hco : o.canonical with
  | true =>
    obtain ⟨p, hp, hph⟩ := hh b o ho hco t ht (by rw [hoy]; exact hr) z hz
    refine ⟨p, hp, ?_⟩
    rcases hph with h1 | h1 | ⟨hzD, -⟩
    · obtain ⟨-, -, -, hcs⟩ := HMem.holdsLive_of_holdsCanonical hm.tbl (hm.tbl.ptr_nodes ho hp) h1
      exact Or.inl hcs
    · exact Or.inr h1
    · exact Or.inl (hm.dCanon z hzD)
  | false =>
    rcases hc with hc | ⟨r, w, hp, hw, hg⟩
    · rw [hco] at hc; cases hc
    obtain ⟨q, hq, hgq⟩ := hm.snap_goodRef hinv hls ho hco hp (by rw [hoy]; exact hw) hg hz
    exact ⟨q, hq, Or.inr hgq⟩

end ReadableT

/-! ## The follow of a pointer that a read at t may follow -/

/-- The slow path's live handle for a pointee with a canonical object is the
pointee's live handle, which holds that object, still canonical. -/
theorem HMem.resolve_canonical {M : HMem V} (ht : HTableOK M) {a : Nat} {y : NodeId} {o : HObj V}
    {p : HPtr} (ho : M.obj? a = some o) (hp : o.ptr? y = some p) {c : Nat} (hc : M.canonicalOf y = some c) :
    ∃ hd, (M.resolve a y).1.handle? (M.resolve a y).2 = some hd ∧ hd.obj = some c ∧
      ∃ oc, (M.resolve a y).1.obj? c = some oc ∧ oc.canonical = true := by
  obtain ⟨n, oc, htn, hcn, hoc, hcc⟩ := (M.canonicalOf_eq_some y c).mp hc
  obtain ⟨hd, hh, hhc⟩ : ∃ hd, M.handle? n = some hd ∧ hd.obj = some c := by
    unfold HMem.objOf at hcn
    cases hq : M.handle? n with
    | none => rw [hq] at hcn; cases hcn
    | some hd => rw [hq] at hcn; exact ⟨hd, rfl, hcn⟩
  by_cases hlive : ∃ n0 hd0, p.handle = some n0 ∧ M.handle? n0 = some hd0 ∧ hd0.dead = false
  · obtain ⟨n0, hd0, hn0, hh0, hl0⟩ := hlive
    rw [HMem.resolve_live ho hp hn0 hh0 hl0]
    -- The live handle the pointer holds is y's live handle.
    obtain ⟨hd', hh', hy0⟩ := ht.ptrNode ho hp hn0
    rw [hh0, Option.some.injEq] at hh'
    have h1 := ht.liveIn hh0 hl0
    rw [hh', hy0, htn, Option.some.injEq] at h1
    rw [← h1]
    exact ⟨hd, hh, hhc, oc, hoc, hcc⟩
  · have hnl : ∀ n0 hd0, p.handle = some n0 → M.handle? n0 = some hd0 → hd0.dead = true := by
      intro n0 hd0 h1 h2
      cases hd : hd0.dead with
      | true => rfl
      | false => exact absurd ⟨n0, hd0, h1, h2, hd⟩ hlive
    rw [HMem.resolve_table ho hp hnl htn]
    refine ⟨hd, by rw [HMem.handle?_setObj]; exact hh, hhc, ?_⟩
    rw [HMem.obj?_setObj]
    split
    · rename_i hca
      rw [hca, ho, Option.some.injEq] at hoc
      rw [← hoc] at hcc
      exact ⟨_, rfl, hcc⟩
    · exact ⟨oc, hoc, hcc⟩

section FollowT

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : HMem V}

/-- The readers' follow reaches an object, if the pointee has a canonical
object or the slow path's reference names a version. -/
theorem HEInv.followR_someT (hinv : Inv sp db k) (hm : HEInv sp db S0 k m) {a : Nat} {o : HObj V}
    {z : NodeId} {p : HPtr} (ho : m.obj? a = some o) (hp : o.ptr? z = some p)
    (hg : (m.canonicalOf z).isSome = true ∨
      ∃ r u, m.slowRef S0 z p = some r ∧ db.S.versionAt r z = some u) :
    ∃ m' n b, m.followR sp S0 db.S a z = some (m', n, b) := by
  by_cases hfast : ∃ n0 b0 ob0, p.handle = some n0 ∧ m.objOf n0 = some b0 ∧ m.obj? b0 = some ob0 ∧
      ob0.usable p.ref = true
  · obtain ⟨n0, b0, ob0, hn0, hb0, hob0, hu0⟩ := hfast
    exact ⟨m, n0, b0, HMem.followR_fast sp S0 db.S ho hp hn0 hb0 hob0 hu0⟩
  · have hnf : ∀ n0 b0 ob0, p.handle = some n0 → m.objOf n0 = some b0 → m.obj? b0 = some ob0 →
        ob0.usable p.ref = false := by
      intro n0 b0 ob0 h1 h2 h3
      cases hu : ob0.usable p.ref with
      | false => rfl
      | true => exact absurd ⟨n0, b0, ob0, h1, h2, h3, hu⟩ hfast
    rw [HMem.followR_slow sp S0 db.S ho hp hnf]
    have hm1 := hm.writeBack hinv ho hp
    rw [HMem.setRef_eq ho hp] at hm1 ⊢
    have ho1 := HMem.obj?_setObj_self m a (o.setPtr z { p with ref := m.slowRef S0 z p })
    have hp1 : (o.setPtr z { p with ref := m.slowRef S0 z p }).ptr? z =
        some { p with ref := m.slowRef S0 z p } := by
      rw [HObj.ptr?_setPtr_of hp]; simp
    rcases hg with hcs | ⟨r, u, hsr, hu⟩
    · -- z's canonical object, held by z's live handle, which the follow resolves to.
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hcs
      have hc1 : (m.setObj a (o.setPtr z { p with ref := m.slowRef S0 z p })).canonicalOf z = some c := by
        rw [HMem.canonicalOf_setObj_core ho (HObj.setPtr_core _ _ _)]; exact hc
      generalize m.setObj a (o.setPtr z { p with ref := m.slowRef S0 z p }) = M1 at ho1 hm1 hc1 ⊢
      obtain ⟨hd, hh, hhc, oc, hoc, hcc⟩ := HMem.resolve_canonical hm1.tbl ho1 hp1 hc1
      rw [HMem.load_usable sp db.S hh hhc hoc (by simp [HObj.usable, hcc])]
      exact ⟨_, _, _, rfl⟩
    · generalize m.setObj a (o.setPtr z { p with ref := m.slowRef S0 z p }) = M1 at ho1 hm1 ⊢
      obtain ⟨hd, hh, hhn⟩ := HMem.resolve_handle hm1.tbl ho1 hp1
      obtain ⟨M', b, hl⟩ := HMem.load_some sp db.S hh (x := r) (by rw [hhn]; exact hu)
      rw [hsr, hl]
      exact ⟨_, _, _, rfl⟩

/-- The readers' follow of a pointer that a read at t may follow, of an object
of another node, reaches an object that can be read at t, as
`HEInv.followR_ok` says. -/
theorem HEInv.follow_goodT (hinv : Inv sp db k) (hls : LiveSub sp) (hm : HEInv sp db S0 k m)
    {t : Time} {a : Nat} {o : HObj V} (ho : m.obj? a = some o) {z : NodeId} {p : HPtr}
    (hp : o.ptr? z = some p) (hg : HPtrGoodT sp S0 db m t z p) (hne : o.node ≠ z) :
    ∃ m1 n b, m.follow sp S0 db.S a z false = (m1, some b) ∧ HFollowed sp S0 db k m m1 a z n b ∧
      HReadableT sp db m1 t b z := by
  have hg' : (m.canonicalOf z).isSome = true ∨
      ∃ r u, m.slowRef S0 z p = some r ∧ db.S.versionAt r z = some u := by
    rcases hg with h | ⟨r, w, h1, h2, -⟩
    · exact Or.inl h
    · exact Or.inr ⟨r, w, h1, h2⟩
  obtain ⟨m1, n, b, hf⟩ := hm.followR_someT hinv ho hp hg'
  have hF := hm.followR_ok hinv ho hf
  have hfe : m.follow sp S0 db.S a z false = (m1, some b) := by unfold HMem.follow; rw [hf]; rfl
  refine ⟨m1, n, b, hfe, hF, ?_⟩
  rcases hg with hcs | ⟨r, w, hsr, hw, hgw⟩
  · -- z's canonical object stays, and it is the object reached.
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hcs
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
  · -- The object reached serves the slow path's reference, which names a version
    -- good for t: it is canonical, or a snapshot at least as new (lemma M).
    obtain ⟨ob, hob, hu⟩ := hF.usable o p ho hp
    obtain ⟨ob', hob', hony⟩ := hF.obj
    rw [hob, Option.some.injEq] at hob'
    rw [← hob'] at hony
    refine ⟨ob, hob, hony, ?_⟩
    cases hcb : ob.canonical with
    | true => exact Or.inl rfl
    | false =>
      right
      rw [hsr] at hu
      unfold HObj.usable at hu
      rw [hcb, Bool.false_or] at hu
      cases hq : ob.pos with
      | none => rw [hq] at hu; simp at hu
      | some q =>
        rw [hq] at hu
        simp only [decide_eq_true_eq] at hu
        obtain ⟨r1, w1, e1, e2, -⟩ := hF.inv.snap b ob hob hcb
        rw [hq, Option.some.injEq] at e1
        rw [← e1, hony] at e2
        exact ⟨q, w1, rfl, e2, hinv.good_of_le hls hw e2 hu hgw⟩

end FollowT

/-! ## A read at an earlier time -/

section ReadT

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : HMem V}

/-- A read at t ≤ k from an object that can be read at t, of a node reachable
at t, gives the nodes reachable from it at t, each with its node at t; both
invariants are kept, and so is the core of every object of a node at the
object's level or higher. -/
theorem HEInv.readAtT_ok (hinv : Inv sp db k) (hls : LiveSub sp) {t : Time} (ht : t ≤ k) :
    ∀ (fuel : Nat) (m : HMem V) (b : Nat) (y : NodeId) (n : Node V), HEInv sp db S0 k m →
      HInvH sp db S0 k m → HReadableT sp db m t b y → db.P.get? y = some n →
      reachable sp db.P t y = true → n.level < fuel →
      HEInv sp db S0 k (m.readAt sp S0 db.S fuel t b).1 ∧ HInvH sp db S0 k (m.readAt sp S0 db.S fuel t b).1 ∧
        HKeepFrom db.P n.level m (m.readAt sp S0 db.S fuel t b).1 ∧
        (m.readAt sp S0 db.S fuel t b).2 = (reachFrom sp db.P t y n).map (fun z => (z, nodeAt db.P z t)) := by
  intro fuel
  induction fuel with
  | zero => intro m b y n _ _ _ _ _ hlt; omega
  | succ fuel ih =>
    intro m b y n hm hh hrd hn hr hlt
    obtain ⟨o, ho, hoy, hoh, hol, hod⟩ := hm.readableT_facts hinv hrd hn
    rw [readAt_succ_eqH sp S0 db.S fuel m t b ho]
    have hkeepB : ∀ m', HKeepFrom db.P n.level m m' → ∃ o', m'.obj? b = some o' ∧ o'.core = o.core := by
      intro m' hk
      exact hk b o ho (fun nn hnn => by
        rw [hoy, hn, Option.some.injEq] at hnn; subst hnn; exact Nat.le_refl _)
    -- The parent's pointers, in every memory that keeps both invariants and the
    -- parent's core.
    have hpar : ∀ (m' : HMem V), HEInv sp db S0 k m' → HInvH sp db S0 k m' → HKeepFrom db.P n.level m m' →
        ∀ z ∈ sp.live (o.hist.upTo t), ∃ o' p, m'.obj? b = some o' ∧ o'.core = o.core ∧
          o'.ptr? z = some p ∧ HPtrGoodT sp S0 db m' t z p := by
      intro m' hm' hh' hkc z hz
      obtain ⟨o', ho', hc'⟩ := hkeepB m' hkc
      have e4 : o'.hist = o.hist := congrArg (fun c => c.2.2.2.1) hc'
      obtain ⟨p, hp, hg⟩ := hm'.readableT_ptr hinv hls hh' ht (hrd.keep ho ho' hc') hr ho'
        (by rw [e4]; exact hz)
      exact ⟨o', p, ho', hc', hp, hg⟩
    have hlive : sp.live (o.hist.upTo t) = sp.live (n.hist.upTo t) := by rw [hoh]
    obtain ⟨hI, hL⟩ := fold_invH (readStepH sp S0 db.S fuel t b o)
      (fun m' => HEInv sp db S0 k m' ∧ HInvH sp db S0 k m' ∧ HKeepFrom db.P n.level m m')
      (fun z => match db.P.get? z with
        | some nz => if nz.level < n.level then (reachFrom sp db.P t z nz).map
            (fun z => (z, nodeAt db.P z t)) else []
        | none => []) (sp.live (o.hist.upTo t)) (by
        intro acc z hz ⟨hmA, hhA, hkcA⟩
        obtain ⟨o', p, ho', hc', hp, hg⟩ := hpar acc.1 hmA hhA hkcA z hz
        have hz' : z ∈ sp.live (n.hist.upTo t) := by rw [← hlive]; exact hz
        obtain ⟨hrz, -, nz, hnz, hlvl⟩ := hinv.reach_child hls hn hr hz'
        have hne : o'.node ≠ z := by
          have e1 : o'.node = o.node := congrArg (fun c => c.1) hc'
          intro he
          rw [e1, hoy] at he
          rw [← he, hn, Option.some.injEq] at hnz
          rw [← hnz] at hlvl
          omega
        obtain ⟨m1, n1, b1, hf1, hF1, hrd1⟩ := hmA.follow_goodT hinv hls ho' hp hg hne
        have hh1 : HInvH sp db S0 k m1 := by
          have := hhA.follow_reader hinv hmA b z
          rw [hf1] at this
          exact this
        obtain ⟨o1, ho1, -, -, hol1, -⟩ := hF1.inv.readableT_facts hinv hrd1 hnz
        obtain ⟨hI2, hH2, hkc2, hL2⟩ := ih m1 b1 z nz hF1.inv hh1 hrd1 hnz hrz (by omega)
        have hst : readStepH sp S0 db.S fuel t b o acc z =
            ((HMem.readAt sp S0 db.S fuel m1 t b1).1, acc.2 ++ (HMem.readAt sp S0 db.S fuel m1 t b1).2) := by
          unfold readStepH
          rw [hf1]
          simp only [ho1, hol1, hol, hlvl, ↓reduceIte]
        rw [hst]
        refine ⟨⟨hI2, hH2, ?_⟩, ?_⟩
        · -- The follow keeps every object of a node other than z, the read below every
          -- object of a node at z's level or higher.
          refine hkcA.trans (HKeepFrom.trans ?_ (hkc2.mono (Nat.le_of_lt hlvl)))
          intro x ox hx hlev
          apply hF1.frame x ox hx
          intro hxz
          have := hlev nz (by rw [hxz]; exact hnz)
          omega
        · simp only [hnz, hlvl, ↓reduceIte]
          rw [hL2]) (m, [(o.node, o.nodeAt t)]) ⟨hm, hh, HKeepFrom.refl _ _ m⟩
    refine ⟨hI.1, hI.2.1, hI.2.2, ?_⟩
    have hnode : o.nodeAt t = nodeAt db.P y t := by
      unfold HObj.nodeAt nodeAt
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
theorem HEInv.readT_ok (hinv : Inv sp db k) (hls : LiveSub sp) (hm : HEInv sp db S0 k m)
    (hh : HInvH sp db S0 k m) {t : Time} (ht : t ≤ k) :
    HEInv sp db S0 k (m.read sp S0 db.S t).1 ∧ HInvH sp db S0 k (m.read sp S0 db.S t).1 ∧
      (m.read sp S0 db.S t).2 = (reachList sp db.P t).map (fun z => (z, nodeAt db.P z t)) := by
  obtain ⟨o, ho, hc, hn⟩ := hm.root
  obtain ⟨n0, hn0⟩ := Option.isSome_iff_exists.mp hinv.rootIn
  have hrd : HReadableT sp db m t m.root SIS.root := ⟨o, ho, hn, Or.inl hc⟩
  obtain ⟨o', ho', -, -, hol, -⟩ := hm.readableT_facts hinv hrd hn0
  rw [ho, Option.some.injEq] at ho'
  subst ho'
  have := HEInv.readAtT_ok hinv hls ht (o.level + 1) m m.root SIS.root n0 hm hh hrd hn0
    (reachable_root hn0 t) (by omega)
  unfold HMem.read
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

/-- At any state, the invariant at the last time follows from the live pointers
of `HEInv`: so it holds after the startup from R(0), where k is 0. -/
theorem HInvH.of_live {db : DB V T} {S0 : Stream V T} {m : HMem V} (hinv : Inv sp db 0) (hls : LiveSub sp)
    (hm : HEInv sp db S0 0 m) : HInvH sp db S0 0 m := by
  intro a o ho hc t ht hr z hz
  have ht0 : t = 0 := by omega
  subst ht0
  obtain ⟨n, hn, hhist, -, -⟩ := hm.cc a o ho hc
  have hz' : z ∈ sp.live o.hist := by
    rw [hhist] at hz ⊢
    rw [upTo_of_forall _ _ (hinv.times _ n hn)] at hz
    exact hz
  obtain ⟨p, hp, hli1, hli2⟩ := hm.live a o ho hc hr z hz'
  refine ⟨p, hp, ?_⟩
  cases hzD : inD db.D z with
  | true => exact Or.inl (HMem.holdsCanonical_of_holdsLive (hli1 hzD))
  | false =>
    obtain ⟨hrz, -, hzw⟩ := hm.reach_child hinv hls ho hc hr hz
    exact HPtrHist.clean hinv hls hzD hzw (Nat.le_refl _) hrz (hli2 hzD) o.node

/-- One transaction of a run with handles, and its reads and evictions: the
invariant for reads at earlier times. -/
theorem HInvH.run_step {ts : List T} (hok : RunOK sp al ts) (hph : PhysRunOK sp al ts)
    (hev : EvictRunOK sp al ts) (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) {j : Nat}
    (hjt : j < ts.length) {S0 : Stream V T} {m : HMem V} (hm : HEInv sp (st sp al ts j) S0 j m)
    (hh : HInvH sp (st sp al ts j) S0 j m) (ops : List HCacheOp) :
    HInvH sp (st sp al ts (j + 1)) S0 (j + 1)
      (ops.foldl (HMem.cacheOp sp S0 (handleTrans sp al S0 (st sp al ts j) m ts[j]).1.S
        (handleTrans sp al S0 (st sp al ts j) m ts[j]).1.D) (handleTrans sp al S0 (st sp al ts j) m ts[j]).2) := by
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
  obtain ⟨h1, h2⟩ := hm.handleTrans_ok hsp hinv hmk hlog hstep hphys hcopy htree hinv' hlog'
  have h3 := HInvH.handleTrans_ok hsp hinv hmk hm hh hlog hstep hphys hcopy htree hinv' hlog'
  rw [h1]
  exact HInvH.cacheOps hinv' hsp.liveSub ops _ h2 h3

/-- The invariant for reads at earlier times, in every run with handles and no
restart, from the startup with handles from R(0). -/
theorem HInvH.run {ts : List (T × Bool × List HCacheOp)} (hok : RunOK sp al (ts.map (·.1)))
    (hph : PhysRunOK sp al (ts.map (·.1))) (hev : EvictRunOK sp al (ts.map (·.1)))
    (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) (hnr : ∀ p ∈ ts, p.2.1 = false) :
    ∀ j ≤ ts.length,
      HInvH sp (st sp al (ts.map (·.1)) j) (init sp).S j (runHandles sp al (ts.take j)).2.1 := by
  intro j
  induction j with
  | zero =>
    intro _
    have : runHandles sp al (ts.take 0) = (init sp, handleStartup sp (init sp).S, (init sp).S) := by
      simp [runHandles]
    rw [this, st_zero]
    exact HInvH.of_live (inv_init sp hok.1) hok.1.liveSub (heinv_init hok hph hj hmk hev)
  | succ j ih =>
    intro hjt
    have hh := ih (by omega)
    obtain ⟨e1, e2, e3⟩ := TC_runH hok hph hev hj hmk hnr (heinv_init hok hph hj hmk hev) j (by omega)
    have hjt' : j < ts.length := by omega
    have hjm : j < (ts.map (·.1)).length := by simp; omega
    rw [runHandles_succ sp al ts hjt']
    have hnrj : ts[j].2.1 = false := hnr _ (List.getElem_mem hjt')
    simp only [hnrj, Bool.false_eq_true, ↓reduceIte]
    rw [e1, e2]
    have htr : (ts.map (·.1))[j] = ts[j].1 := by simp
    have := HInvH.run_step hok hph hev hj hmk hjm e3 hh ts[j].2.2
    rw [htr] at this
    exact this

end Run

/-! ## T-READ with handles -/

/-- `TR_handles` (SIS/HandleTheorems.lean) holds: in a run with handles and no
restart, after any transaction and its operations, a read through the handles
at any time t up to the last record gives P at t. -/
theorem tr_handles (sp : Spec V T) (al : Algo V T) : TR_handles sp al := by
  intro ts hok hph hev hj hmk hnr j hjt t ht db m
  have hst : st sp al (ts.map (·.1)) j = run sp al ((ts.take j).map (·.1)) := by
    unfold st; rw [List.map_take]
  obtain ⟨-, -, e3⟩ := TC_runH hok hph hev hj hmk hnr (heinv_init hok hph hj hmk hev) j hjt
  have hh := HInvH.run hok hph hev hj hmk hnr j hjt
  have hinv := inv_st sp al (ts.map (·.1)) hok (algOK_of sp al (Or.inl hj)) j
    (by rw [List.length_map]; exact hjt)
  rw [hst] at e3 hh hinv
  exact read_list_view (e3.readT_ok hinv hok.1.liveSub hh ht).2.2

end SIS
