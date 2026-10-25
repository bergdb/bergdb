/-
Proofs about the physical layer with handles (bergdb item 009, step 2d), part 4:
reads and the operations between transactions keep the invariant; a read at the
last time k gives P@k (the writer's view, which the next transaction's change
comes from).
-/
import SIS.Proof.HandleFollow

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- A fold that keeps an invariant of its first component. -/
theorem foldl_invH {α β γ : Type} (f : α × β → γ → α × β) (I : α → Prop)
    (hf : ∀ acc z, I acc.1 → I (f acc z).1) : ∀ (l : List γ) (acc : α × β), I acc.1 → I (l.foldl f acc).1
  | [], _, h => h
  | z :: l, acc, h => foldl_invH f I hf l (f acc z) (hf acc z h)

/-- A fold that keeps an invariant of the memory and appends a list per element. -/
theorem fold_invH {α μ : Type} (f : μ × List α → NodeId → μ × List α) (I : μ → Prop)
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

section Reader

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : HMem V}

/-- A reader's follow of any pointer keeps the invariant. -/
theorem HEInv.follow_reader (hinv : Inv sp db k) (hm : HEInv sp db S0 k m) (a : Nat) (y : NodeId) :
    HEInv sp db S0 k (m.follow sp S0 db.S a y false).1 := by
  unfold HMem.follow
  cases hf : m.followR sp S0 db.S a y with
  | none => exact hm
  | some r =>
    obtain ⟨m', n, b⟩ := r
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases ho : m.obj? a with
    | none => unfold HMem.followR at hf; rw [ho] at hf; cases hf
    | some o => exact (hm.followR_ok hinv ho hf).inv

/-- A read at any time, from any object, keeps the invariant. -/
theorem HEInv.readAt (hinv : Inv sp db k) :
    ∀ (fuel : Nat) (m : HMem V) (t : Time) (a : Nat), HEInv sp db S0 k m →
      HEInv sp db S0 k (m.readAt sp S0 db.S fuel t a).1 := by
  intro fuel
  induction fuel with
  | zero => intro m t a hm; exact hm
  | succ fuel ih =>
    intro m t a hm
    unfold HMem.readAt
    cases ho : m.obj? a with
    | none => exact hm
    | some o =>
      simp only
      apply foldl_invH _ (HEInv sp db S0 k) _ _ _ hm
      intro acc z hacc
      have hf := hacc.follow_reader hinv a z
      generalize acc.1.follow sp S0 db.S a z false = res at hf ⊢
      obtain ⟨m1, ob⟩ := res
      cases ob with
      | none => exact hf
      | some b =>
        simp only
        cases ho1 : m1.obj? b with
        | none => exact hf
        | some o1 =>
          simp only
          split
          · exact ih m1 t b hf
          · exact hf

theorem HEInv.read (hinv : Inv sp db k) (hm : HEInv sp db S0 k m) (t : Time) :
    HEInv sp db S0 k (m.read sp S0 db.S t).1 := by
  unfold HMem.read
  cases m.obj? m.root with
  | none => exact hm
  | some o => exact HEInv.readAt hinv _ m t _ hm

/-- Every operation between transactions keeps the invariant. -/
theorem HEInv.cacheOp (hinv : Inv sp db k) (hm : HEInv sp db S0 k m) (op : HCacheOp) :
    HEInv sp db S0 k (m.cacheOp sp S0 db.S db.D op) := by
  cases op with
  | read t => exact hm.read hinv t
  | evict n => exact hm.evict hinv n

theorem HEInv.cacheOps (hinv : Inv sp db k) (ops : List HCacheOp) :
    ∀ m, HEInv sp db S0 k m → HEInv sp db S0 k (ops.foldl (HMem.cacheOp sp S0 db.S db.D) m) := by
  induction ops with
  | nil => intro m hm; exact hm
  | cons op ops ih => intro m hm; exact ih _ (hm.cacheOp hinv op)

end Reader

/-! ## Readable objects -/

theorem mem_pointees_of_liveH {sp : Spec V T} (hls : LiveSub sp) {h : History V} {y : NodeId}
    (hy : y ∈ sp.live h) : y ∈ pointees sp h := by
  obtain ⟨e, he, hye⟩ := hls _ _ hy
  simp only [pointees, List.mem_eraseDups, List.mem_flatMap]
  exact ⟨e, he, hye⟩

section Readable

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : HMem V}

/-- What a readable object of a node reachable at k holds: its node's whole
history, level and kind. -/
theorem HEInv.readable_facts (hinv : Inv sp db k) (hm : HEInv sp db S0 k m) {b : Nat} {y : NodeId}
    (hrd : HReadable sp db m b y) {n : Node V} (hn : db.P.get? y = some n)
    (hr : reachable sp db.P k y = true) :
    ∃ o, m.obj? b = some o ∧ o.node = y ∧ o.hist = n.hist ∧ o.level = n.level ∧ o.isData = n.isData := by
  obtain ⟨o, ho, hoy, hc⟩ := hrd
  refine ⟨o, ho, hoy, ?_⟩
  cases hco : o.canonical with
  | true =>
    obtain ⟨n', hn', h1, h2, h3⟩ := hm.cc b o ho hco
    rw [hoy, hn, Option.some.injEq] at hn'
    subst hn'
    exact ⟨h1, h2, h3⟩
  | false =>
    rcases hc with hc | ⟨hyD, hyw, hpos⟩
    · rw [hco] at hc; cases hc
    obtain ⟨v, hv, hvh, hvl, hvd⟩ := hinv.lv_whole hn hyw hyD hr
    obtain ⟨r1, w1, e1, e2, e3, e4, e5, -, -⟩ := hm.snap b o ho hco
    rw [hpos, hv] at e1
    simp only [Option.map_some, Option.some.injEq] at e1
    rw [← e1, hoy, hinv.lv_at hv, Option.some.injEq] at e2
    subst e2
    exact ⟨by rw [e3, hvh], by rw [e4, hvl], by rw [e5, hvd]⟩

/-- The pointers of a snapshot at the latest version of a written node y not in
D, current at k: for each pointee of its history, not in D (y is clean), the
record rule gives its latest version. -/
theorem HEInv.snap_ptr (hinv : Inv sp db k) (hev : EvLogic sp db k) (hm : HEInv sp db S0 k m)
    {b : Nat} {o : HObj V} (ho : m.obj? b = some o) (hco : o.canonical = false) {y : NodeId}
    (hoy : o.node = y) (hyD : inD db.D y = false) (hyw : written sp y = true)
    (hpos : o.pos = (db.S.lv y).map (·.recNo)) (hr : reachable sp db.P k y = true)
    {z : NodeId} (hz : z ∈ pointees sp o.hist) :
    ∃ p, o.ptr? z = some p ∧ inD db.D z = false ∧ m.ptrRef S0 z p = (db.S.lv z).map (·.recNo) := by
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp (Reach.isSome ((reachable_iff _ _ _ _).mp hr))
  obtain ⟨v, hv, hvh, -, -⟩ := hinv.lv_whole hn hyw hyD hr
  obtain ⟨r1, w1, e1, e2, e3, -, -, e6, e7⟩ := hm.snap b o ho hco
  rw [hpos, hv] at e1
  simp only [Option.map_some, Option.some.injEq] at e1
  rw [← e1, hoy, hinv.lv_at hv, Option.some.injEq] at e2
  subst e2
  have hzp : z ∈ pointees sp n.hist := by
    rw [← hvh, ← e3]; exact hz
  obtain ⟨hzD, v', hv', href⟩ := hev.clean y n hyw hr hn hyD z hzp
  rw [hv, Option.some.injEq] at hv'
  subst hv'
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp (e6 z (by rw [e3, hvh]; exact hzp))
  refine ⟨p, hp, hzD, ?_⟩
  -- The pointer's reference after Rule R is z's latest version, and so is its record.
  have hR := hinv.ruleR_lv0 hm.pre m.s z
  have hsp := e7 z p hp
  cases hlz : db.S.lv z with
  | none =>
    -- z has no version: no reference can name one.
    cases hpr : m.ptrRef S0 z p with
    | none => rfl
    | some r =>
      obtain ⟨-, u, hu, -⟩ := hm.ptrRef_le hinv ho hp hpr
      rw [hlz] at hu; cases hu
  | some lz =>
    have hlow : ∃ r1, ruleRRef S0 m.s z p.ref = some r1 ∧ lz.recNo ≤ r1 := by
      unfold HSnapPtr at hsp
      rw [href, hlz] at hsp
      rw [hlz] at hR
      exact hsp lz.recNo hR
    obtain ⟨r1, hr1, hle1⟩ := hlow
    cases hpr : m.ptrRef S0 z p with
    | none =>
      -- The record rule gives at least the reference after Rule R.
      exfalso
      unfold HMem.ptrRef at hpr
      rw [hr1] at hpr
      cases hph : p.handle.bind m.handle? with
      | none => rw [hph] at hpr; cases hpr
      | some hd =>
        rw [hph] at hpr
        simp only at hpr
        cases hob : hd.obj.bind m.obj? with
        | none =>
          rw [hob] at hpr
          obtain ⟨y', hy', -⟩ := maxRef_ge_left (w := hd.written) (rfl : some r1 = some r1)
          rw [hy'] at hpr; cases hpr
        | some ob =>
          rw [hob] at hpr
          simp only at hpr
          split at hpr
          · rename_i hcc
            -- the canonical object of z is at z's latest version
            cases hb : hd.obj with
            | none => rw [hb] at hob; cases hob
            | some c =>
              rw [hb] at hob
              simp only [Option.bind_some] at hob
              have := hm.pos c ob hob hcc
              rw [hpr] at this
              cases hpn : p.handle with
              | none => rw [hpn] at hph; cases hph
              | some nn =>
                rw [hpn] at hph
                simp only [Option.bind_some] at hph
                obtain ⟨-, ob', hob', hon'⟩ := hm.tbl.obj_of_handle hph hb
                obtain ⟨hdq, hhq, hnq⟩ := hm.tbl.ptrNode ho hp hpn
                rw [hph, Option.some.injEq] at hhq
                subst hhq
                rw [hob, Option.some.injEq] at hob'
                subst hob'
                rw [hon', hnq, hlz] at this
                cases this
          · obtain ⟨y', hy', -⟩ := maxRef_ge_left (w := hd.written) (rfl : some r1 = some r1)
            rw [hy'] at hpr; cases hpr
    | some r =>
      obtain ⟨-, v2, hv2, hle2⟩ := hm.ptrRef_le hinv ho hp hpr
      rw [hlz, Option.some.injEq] at hv2
      subst hv2
      -- and at least the reference after Rule R
      have hge : r1 ≤ r := by
        unfold HMem.ptrRef at hpr
        rw [hr1] at hpr
        cases hph : p.handle.bind m.handle? with
        | none => rw [hph] at hpr; simp only [Option.some.injEq] at hpr; omega
        | some hd =>
          rw [hph] at hpr
          simp only at hpr
          cases hob : hd.obj.bind m.obj? with
          | none =>
            rw [hob] at hpr
            obtain ⟨y', hy', hle'⟩ := maxRef_ge_left (w := hd.written) (rfl : some r1 = some r1)
            rw [hy', Option.some.injEq] at hpr; omega
          | some ob =>
            rw [hob] at hpr
            simp only at hpr
            split at hpr
            · rename_i hcc
              cases hb : hd.obj with
              | none => rw [hb] at hob; cases hob
              | some c =>
                rw [hb] at hob
                simp only [Option.bind_some] at hob
                have := hm.pos c ob hob hcc
                rw [hpr] at this
                cases hpn : p.handle with
                | none => rw [hpn] at hph; cases hph
                | some nn =>
                  rw [hpn] at hph
                  simp only [Option.bind_some] at hph
                  obtain ⟨-, ob', hob', hon'⟩ := hm.tbl.obj_of_handle hph hb
                  obtain ⟨hdq, hhq, hnq⟩ := hm.tbl.ptrNode ho hp hpn
                  rw [hph, Option.some.injEq] at hhq
                  subst hhq
                  rw [hob, Option.some.injEq] at hob'
                  subst hob'
                  rw [hon', hnq, hlz] at this
                  simp only [Option.map_some, Option.some.injEq] at this
                  have := (hinv.ruleR_bound hm.pre m.s (fun r' h' => hm.rver b o z p r' ho hp h') hr1).2
                  obtain ⟨v3, hv3, hle3⟩ := this
                  rw [hlz, Option.some.injEq] at hv3
                  subst hv3
                  omega
            · obtain ⟨y', hy', hle'⟩ := maxRef_ge_left (w := hd.written) (rfl : some r1 = some r1)
              rw [hy', Option.some.injEq] at hpr; omega
      simp only [Option.map_some, Option.some.injEq]
      omega


/-- The pointers of a readable object of a node current at k, for its live
children: good for a read at k. -/
theorem HEInv.readable_ptr (hinv : Inv sp db k) (hev : EvLogic sp db k) (hm : HEInv sp db S0 k m)
    (hls : LiveSub sp) {b : Nat} {y : NodeId} (hrd : HReadable sp db m b y)
    (hr : reachable sp db.P k y = true) {o : HObj V} (ho : m.obj? b = some o) {z : NodeId}
    (hz : z ∈ sp.live o.hist) : ∃ p, o.ptr? z = some p ∧ HPtrGood S0 db m z p := by
  obtain ⟨o1, ho1, hoy, hc⟩ := hrd
  rw [ho, Option.some.injEq] at ho1
  subst ho1
  cases hco : o.canonical with
  | true =>
    obtain ⟨p, hp, h1, h2⟩ := hm.live b o ho hco (by rw [hoy]; exact hr) z hz
    refine ⟨p, hp, ?_⟩
    cases hzD : inD db.D z with
    | true => exact Or.inl ⟨hzD, h1 hzD⟩
    | false => exact Or.inr ⟨hzD, h2 hzD⟩
  | false =>
    rcases hc with hc | ⟨hyD, hyw, hpos⟩
    · rw [hco] at hc; cases hc
    obtain ⟨p, hp, hzD, href⟩ := hm.snap_ptr hinv hev ho hco hoy hyD hyw hpos hr
      (mem_pointees_of_liveH hls hz)
    exact ⟨p, hp, Or.inr ⟨hzD, href⟩⟩

end Readable

/-! ## The follow of a good pointer -/

theorem HMem.load_some (sp : Spec V T) (S : Stream V T) {M : HMem V} {n : Nat} {hd : Handle}
    (hh : M.handle? n = some hd) {x : Nat} {w : Version V} (hw : S.versionAt x hd.node = some w) :
    ∃ M' b, M.load sp S n (some x) = (M', some b) := by
  cases hb : hd.obj with
  | none => exact ⟨_, _, HMem.load_filled sp S hh hb hw⟩
  | some b =>
    cases hob : M.obj? b with
    | none =>
      unfold HMem.load
      simp only [hh, hb, hob, hw]
      exact ⟨_, _, rfl⟩
    | some ob =>
      cases hu : ob.usable (some x) with
      | true => exact ⟨_, _, HMem.load_usable sp S hh hb hob hu⟩
      | false =>
        unfold HMem.load
        simp only [hh, hb, hob, hu, hw, Bool.false_eq_true, ↓reduceIte]
        exact ⟨_, _, rfl⟩

/-- The slow path's live handle is a handle of the pointer's pointee. -/
theorem HMem.resolve_handle {M : HMem V} (ht : HTableOK M) {a : Nat} {y : NodeId} {o : HObj V}
    {p : HPtr} (ho : M.obj? a = some o) (hp : o.ptr? y = some p) :
    ∃ hd, (M.resolve a y).1.handle? (M.resolve a y).2 = some hd ∧ hd.node = y := by
  by_cases hlive : ∃ n hd, p.handle = some n ∧ M.handle? n = some hd ∧ hd.dead = false
  · obtain ⟨n, hd, hn, hh, hl⟩ := hlive
    rw [HMem.resolve_live ho hp hn hh hl]
    obtain ⟨hd', hh', hy⟩ := ht.ptrNode ho hp hn
    rw [hh, Option.some.injEq] at hh'
    subst hh'
    exact ⟨hd, hh, hy⟩
  · have hnl : ∀ n0 hd0, p.handle = some n0 → M.handle? n0 = some hd0 → hd0.dead = true := by
      intro n0 hd0 h1 h2
      cases hd : hd0.dead with
      | true => rfl
      | false => exact absurd ⟨n0, hd0, h1, h2, hd⟩ hlive
    cases htb : M.tableOf y with
    | some n1 =>
      rw [HMem.resolve_table ho hp hnl htb]
      obtain ⟨hd1, -, -, hh1, -, hy1, -⟩ := ht.entry htb
      exact ⟨hd1, by rw [HMem.handle?_setObj]; exact hh1, hy1⟩
    | none =>
      rw [HMem.resolve_new ho hp hnl htb]
      refine ⟨{ node := y, obj := none, written := none, dead := false }, ?_, rfl⟩
      rw [HMem.handle?_setObj, HMem.emptyHandle_handle?]
      simp

section Good

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : HMem V}

/-- The readers' follow of a good pointer to a written node reachable at k
reaches an object. -/
theorem HEInv.followR_some (hinv : Inv sp db k) (hm : HEInv sp db S0 k m) {a : Nat} {o : HObj V}
    {z : NodeId} {p : HPtr} (ho : m.obj? a = some o) (hp : o.ptr? z = some p)
    (hg : HPtrGood S0 db m z p) (hzw : written sp z = true) (hzr : reachable sp db.P k z = true) :
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
    -- Not on the fast path, the good pointer is for a node not in D, and its record is
    -- the node's latest version, which is the slow path's reference.
    have hD : inD db.D z = false ∧ m.ptrRef S0 z p = (db.S.lv z).map (·.recNo) := by
      rcases hg with ⟨hD, n', hn', ht', hc'⟩ | h
      · exfalso
        obtain ⟨c, hcy⟩ := Option.isSome_iff_exists.mp hc'
        obtain ⟨n'', oc, ht'', hoc, hocx, hcc⟩ := (m.canonicalOf_eq_some z c).mp hcy
        rw [ht', Option.some.injEq] at ht''
        subst ht''
        have := hnf n' c oc hn' hoc hocx
        simp [HObj.usable, hcc] at this
      · exact h
    have hrefeq : m.ptrRef S0 z p = m.slowRef S0 z p := by
      apply HMem.ptrRef_eq_slowRef
      intro hd' b' ob' h1 h2 h3
      cases hpn : p.handle with
      | none => rw [hpn] at h1; cases h1
      | some n' =>
        rw [hpn] at h1
        simp only [Option.bind_some] at h1
        cases hc : ob'.canonical with
        | false => rfl
        | true =>
          have := hnf n' b' ob' hpn (by simp [HMem.objOf, h1, h2]) h3
          simp [HObj.usable, hc] at this
    obtain ⟨nz, hnz⟩ := Option.isSome_iff_exists.mp (Reach.isSome ((reachable_iff _ _ _ _).mp hzr))
    obtain ⟨v, hv, -⟩ := hinv.lv_whole hnz hzw hD.1 hzr
    have hsr : m.slowRef S0 z p = some v.recNo := by
      rw [← hrefeq, hD.2, hv]; rfl
    have hm1 := hm.writeBack hinv ho hp
    rw [HMem.setRef_eq ho hp] at hm1 ⊢
    have ho1 := HMem.obj?_setObj_self m a (o.setPtr z { p with ref := m.slowRef S0 z p })
    have hp1 : (o.setPtr z { p with ref := m.slowRef S0 z p }).ptr? z =
        some { p with ref := m.slowRef S0 z p } := by
      rw [HObj.ptr?_setPtr_of hp]; simp
    generalize m.setObj a (o.setPtr z { p with ref := m.slowRef S0 z p }) = M1 at ho1 hm1 ⊢
    obtain ⟨hd, hh, hhn⟩ := HMem.resolve_handle hm1.tbl ho1 hp1
    obtain ⟨M', b, hl⟩ := HMem.load_some sp db.S hh (x := v.recNo) (by rw [hhn]; exact hinv.lv_at hv)
    rw [hsr, hl]
    exact ⟨_, _, _, rfl⟩

/-- The readers' follow of a good pointer to a written node reachable at k
reaches a readable object, as `HEInv.followR_ok` says. -/
theorem HEInv.follow_good (hinv : Inv sp db k) (hm : HEInv sp db S0 k m) {a : Nat} {o : HObj V}
    (ho : m.obj? a = some o) {z : NodeId} {p : HPtr} (hp : o.ptr? z = some p)
    (hg : HPtrGood S0 db m z p) (hzw : written sp z = true) (hzr : reachable sp db.P k z = true) :
    ∃ m1 n b, m.follow sp S0 db.S a z false = (m1, some b) ∧ HFollowed sp S0 db k m m1 a z n b ∧
      HReadable sp db m1 b z := by
  obtain ⟨m1, n, b, hf⟩ := hm.followR_some hinv ho hp hg hzw hzr
  have hF := hm.followR_ok hinv ho hf
  refine ⟨m1, n, b, ?_, hF, hF.readable o p ho hp hg hzw⟩
  unfold HMem.follow
  rw [hf]
  rfl

end Good

/-! ## A read at the last time -/

/-- Every object of a node of P at level ℓ or higher keeps its core from m to m'
(a read from an object at level ℓ follows pointers to lower levels only). -/
def HKeepFrom (P : Struct V) (ℓ : Nat) (m m' : HMem V) : Prop :=
  ∀ x o, m.obj? x = some o → (∀ nn, P.get? o.node = some nn → ℓ ≤ nn.level) →
    ∃ o', m'.obj? x = some o' ∧ o'.core = o.core

theorem HKeepFrom.refl (P : Struct V) (ℓ : Nat) (m : HMem V) : HKeepFrom P ℓ m m :=
  fun _ o ho _ => ⟨o, ho, rfl⟩

theorem HKeepFrom.trans {P : Struct V} {ℓ : Nat} {m1 m2 m3 : HMem V} (h1 : HKeepFrom P ℓ m1 m2)
    (h2 : HKeepFrom P ℓ m2 m3) : HKeepFrom P ℓ m1 m3 := by
  intro x o ho hl
  obtain ⟨o', ho', hc'⟩ := h1 x o ho hl
  have e1 : o'.node = o.node := congrArg (fun c => c.1) hc'
  obtain ⟨o'', ho'', hc''⟩ := h2 x o' ho' (by rw [e1]; exact hl)
  exact ⟨o'', ho'', hc''.trans hc'⟩

theorem HKeepFrom.mono {P : Struct V} {ℓ1 ℓ2 : Nat} {m m' : HMem V} (h : HKeepFrom P ℓ1 m m')
    (hle : ℓ1 ≤ ℓ2) : HKeepFrom P ℓ2 m m' :=
  fun x o ho hl => h x o ho (fun nn hnn => Nat.le_trans hle (hl nn hnn))

theorem HReadable.keep {sp : Spec V T} {db : DB V T} {m m' : HMem V} {b : Nat} {y : NodeId}
    (hr : HReadable sp db m b y) {o o' : HObj V} (ho : m.obj? b = some o) (ho' : m'.obj? b = some o')
    (hc : o'.core = o.core) : HReadable sp db m' b y := by
  obtain ⟨o1, ho1, hn, hcs⟩ := hr
  rw [ho, Option.some.injEq] at ho1
  subst ho1
  have e1 : o'.node = o.node := congrArg (fun c => c.1) hc
  have e5 : o'.canonical = o.canonical := congrArg (fun c => c.2.2.2.2.1) hc
  have e6 : o'.pos = o.pos := congrArg (fun c => c.2.2.2.2.2) hc
  exact ⟨o', ho', by rw [e1, hn], by rw [e5, e6]; exact hcs⟩

/-- One step of a read's fold over the live children of object o at address a. -/
def readStepH (sp : Spec V T) (S0 S : Stream V T) (fuel : Nat) (t : Time) (a : Nat) (o : HObj V)
    (acc : HMem V × List (NodeId × Node V)) (y : NodeId) : HMem V × List (NodeId × Node V) :=
  match acc.1.follow sp S0 S a y false with
  | (m1, some b) =>
    match m1.obj? b with
    | some o1 =>
      if o1.level < o.level then
        let r := HMem.readAt sp S0 S fuel m1 t b
        (r.1, acc.2 ++ r.2)
      else (m1, acc.2)
    | none => (m1, acc.2)
  | (m1, none) => (m1, acc.2)

theorem readAt_succ_eqH (sp : Spec V T) (S0 S : Stream V T) (fuel : Nat) (m : HMem V) (t : Time)
    (a : Nat) {o : HObj V} (ho : m.obj? a = some o) :
    m.readAt sp S0 S (fuel + 1) t a =
      (sp.live (o.hist.upTo t)).foldl (readStepH sp S0 S fuel t a o) (m, [(o.node, o.nodeAt t)]) := by
  rw [HMem.readAt]; simp only [ho]; rfl

section ReadK

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : HMem V}

/-- A read at k from a readable object of a node reachable at k gives the nodes
reachable from it at k, each with its node at k; the invariant is kept, and so
is the core of every object of a node at the object's level or higher. -/
theorem HEInv.readAt_ok (hinv : Inv sp db k) (hls : LiveSub sp) (hev : EvLogic sp db k) :
    ∀ (fuel : Nat) (m : HMem V) (b : Nat) (y : NodeId) (n : Node V), HEInv sp db S0 k m →
      HReadable sp db m b y → db.P.get? y = some n → reachable sp db.P k y = true →
      n.level < fuel →
      HEInv sp db S0 k (m.readAt sp S0 db.S fuel k b).1 ∧
        HKeepFrom db.P n.level m (m.readAt sp S0 db.S fuel k b).1 ∧
        (m.readAt sp S0 db.S fuel k b).2 = (reachFrom sp db.P k y n).map (fun z => (z, nodeAt db.P z k)) := by
  intro fuel
  induction fuel with
  | zero => intro m b y n _ _ _ _ hlt; omega
  | succ fuel ih =>
    intro m b y n hm hrd hn hr hlt
    obtain ⟨o, ho, hoy, hoh, hol, hod⟩ := hm.readable_facts hinv hrd hn hr
    rw [readAt_succ_eqH sp S0 db.S fuel m k b ho]
    have hupk : o.hist.upTo k = o.hist := by rw [hoh]; exact upTo_of_forall _ _ (hinv.times y n hn)
    have hkeepB : ∀ m', HKeepFrom db.P n.level m m' → ∃ o', m'.obj? b = some o' ∧ o'.core = o.core := by
      intro m' hk
      exact hk b o ho (fun nn hnn => by
        rw [hoy, hn, Option.some.injEq] at hnn; subst hnn; exact Nat.le_refl _)
    -- The parent's pointers, in every memory that keeps the invariant and the parent's core.
    have hpar : ∀ (m' : HMem V), HEInv sp db S0 k m' → HKeepFrom db.P n.level m m' →
        ∀ z ∈ sp.live (o.hist.upTo k), ∃ o' p, m'.obj? b = some o' ∧ o'.core = o.core ∧
          o'.ptr? z = some p ∧ HPtrGood S0 db m' z p := by
      intro m' hm' hkc z hz
      obtain ⟨o', ho', hc'⟩ := hkeepB m' hkc
      have e4 : o'.hist = o.hist := congrArg (fun c => c.2.2.2.1) hc'
      obtain ⟨p, hp, hg⟩ := hm'.readable_ptr hinv hev hls (hrd.keep ho ho' hc') hr ho'
        (by rw [e4, ← hupk]; exact hz)
      exact ⟨o', p, ho', hc', hp, hg⟩
    have hlive : sp.live (o.hist.upTo k) = sp.live (n.hist.upTo k) := by rw [hoh]
    obtain ⟨hI, hL⟩ := fold_invH (readStepH sp S0 db.S fuel k b o)
      (fun m' => HEInv sp db S0 k m' ∧ HKeepFrom db.P n.level m m')
      (fun z => match db.P.get? z with
        | some nz => if nz.level < n.level then (reachFrom sp db.P k z nz).map
            (fun z => (z, nodeAt db.P z k)) else []
        | none => []) (sp.live (o.hist.upTo k)) (by
        intro acc z hz ⟨hmA, hkcA⟩
        obtain ⟨o', p, ho', hc', hp, hg⟩ := hpar acc.1 hmA hkcA z hz
        have hz' : z ∈ sp.live (n.hist.upTo k) := by rw [← hlive]; exact hz
        obtain ⟨e, he, hze⟩ := hls _ _ hz'
        obtain ⟨nz, hnz, hlvl⟩ := hinv.ptrs y n hn e (mem_upTo.mp he).1 z hze
        have hrz : reachable sp db.P k z = true := by
          rw [reachable_iff] at hr ⊢
          exact Reach.child hr hn hz' hnz hlvl
        have hzw : written sp z = true :=
          written_of_ne_root sp (hinv.ptr_ne_root hn (mem_upTo.mp he).1 hze)
        obtain ⟨m1, n1, b1, hf1, hF1, hrd1⟩ := hmA.follow_good hinv ho' hp hg hzw hrz
        obtain ⟨o1, ho1, -, -, hol1, -⟩ := hF1.inv.readable_facts hinv hrd1 hnz hrz
        obtain ⟨hI2, hkc2, hL2⟩ := ih m1 b1 z nz hF1.inv hrd1 hnz hrz (by omega)
        have hst : readStepH sp S0 db.S fuel k b o acc z =
            ((HMem.readAt sp S0 db.S fuel m1 k b1).1, acc.2 ++ (HMem.readAt sp S0 db.S fuel m1 k b1).2) := by
          unfold readStepH
          rw [hf1]
          simp only [ho1, hol1, hol, hlvl, ↓reduceIte]
        rw [hst]
        refine ⟨⟨hI2, ?_⟩, ?_⟩
        · -- The follow keeps every object of a node other than z, the read below every
          -- object of a node at z's level or higher.
          refine hkcA.trans (HKeepFrom.trans ?_ (hkc2.mono (Nat.le_of_lt hlvl)))
          intro x ox hx hlev
          apply hF1.frame x ox hx
          intro hxz
          have := hlev nz (by rw [hxz]; exact hnz)
          omega
        · simp only [hnz, hlvl, ↓reduceIte]
          rw [hL2]) (m, [(o.node, o.nodeAt k)]) ⟨hm, HKeepFrom.refl _ _ m⟩
    refine ⟨hI.1, hI.2, ?_⟩
    have hnode : o.nodeAt k = nodeAt db.P y k := by
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

/-- A read at k from the root's object gives P@k, and keeps the invariant. -/
theorem HEInv.read_ok (hinv : Inv sp db k) (hls : LiveSub sp) (hev : EvLogic sp db k)
    (hm : HEInv sp db S0 k m) :
    HEInv sp db S0 k (m.read sp S0 db.S k).1 ∧
      (m.read sp S0 db.S k).2 = (reachList sp db.P k).map (fun z => (z, nodeAt db.P z k)) := by
  obtain ⟨o, ho, hc, hn⟩ := hm.root
  obtain ⟨n0, hn0⟩ := Option.isSome_iff_exists.mp hinv.rootIn
  have hrd : HReadable sp db m m.root SIS.root := ⟨o, ho, hn, Or.inl hc⟩
  obtain ⟨o', ho', -, -, hol, -⟩ := hm.readable_facts hinv hrd hn0 (reachable_root hn0 k)
  rw [ho, Option.some.injEq] at ho'
  subst ho'
  have := HEInv.readAt_ok hinv hls hev (o.level + 1) m m.root SIS.root n0 hm hrd hn0
    (reachable_root hn0 k) (by omega)
  unfold HMem.read
  rw [ho]
  simp only
  refine ⟨this.1, ?_⟩
  rw [this.2.2]
  unfold reachList
  rw [hn0]

/-- The writer's view at k through the handles is P's. -/
theorem HEInv.view_ok (hinv : Inv sp db k) (hls : LiveSub sp) (hev : EvLogic sp db k)
    (hm : HEInv sp db S0 k m) :
    HEInv sp db S0 k (m.view sp S0 db.S k).1 ∧ (m.view sp S0 db.S k).2 = view sp db.P k := by
  obtain ⟨h1, h2⟩ := hm.read_ok hinv hls hev
  refine ⟨h1, ?_⟩
  funext x
  show ((m.read sp S0 db.S k).2).lookup x = _
  rw [h2, lookup_reach_view]

end ReadK

end SIS
