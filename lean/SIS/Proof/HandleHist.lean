/-
Proofs about the physical layer with handles (bergdb item 009, phase 4a), part
1 of T-READ: the invariant for reads at earlier times (`HInvH`). For every
canonical
object, every time t at which its node is reachable, and every live child at t,
its pointer holds a handle that holds a canonical object; or the slow path's
reference (the reference after Rule R, raised to the held handle's written
position) names a version good for t; or both nodes are in D, the object's no
later (INV-SLOT's second half). Reads and evictions keep it: a reader's follow
writes back the slow path's reference, which does not change it; an eviction
of a canonical object gives its handle the object's position, its node's latest
version, which is good for every time at which the node is reachable, since a
canonical object that may be evicted is not of a node of D.
-/
import SIS.Proof.LogicFacts
import SIS.Proof.HandleRecords

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## The invariant -/

/-- Object b, of node y, can be read at time t: it is canonical, or the
snapshot of a version of y good for t. -/
def HReadableT (sp : Spec V T) (db : DB V T) (m : HMem V) (t : Time) (b : Nat) (y : NodeId) : Prop :=
  ∃ o, m.obj? b = some o ∧ o.node = y ∧
    (o.canonical = true ∨ ∃ r w, o.pos = some r ∧ db.S.versionAt r y = some w ∧
      good sp db.S db.P t w = true)

/-- The slow path's reference of pointer p to y names a version of y good for
t. -/
def HGoodRef (sp : Spec V T) (S0 : Stream V T) (db : DB V T) (m : HMem V) (t : Time) (y : NodeId)
    (p : HPtr) : Prop :=
  ∃ r w, m.slowRef S0 y p = some r ∧ db.S.versionAt r y = some w ∧ good sp db.S db.P t w = true

/-- The pointer of a canonical object of node x for y, a live child of it at t,
as a read at t needs it. -/
def HPtrHist (sp : Spec V T) (S0 : Stream V T) (db : DB V T) (m : HMem V) (t : Time) (x y : NodeId)
    (p : HPtr) : Prop :=
  m.holdsCanonical p = true ∨ HGoodRef sp S0 db m t y p ∨ DLater db.D x y

/-- The invariant for reads at earlier times: the pointers of canonical objects
as reads at every time up to k need them. -/
def HInvH (sp : Spec V T) (db : DB V T) (S0 : Stream V T) (k : Nat) (m : HMem V) : Prop :=
  ∀ a o, m.obj? a = some o → o.canonical = true → ∀ t ≤ k, reachable sp db.P t o.node = true →
    ∀ y ∈ sp.live (o.hist.upTo t), ∃ p, o.ptr? y = some p ∧ HPtrHist sp S0 db m t o.node y p

/-! ## Memories that keep what the pointers give -/

section Keep

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m m' : HMem V}

theorem HPtrHist.keep {t : Time} {x y : NodeId} {p : HPtr} (h : HPtrHist sp S0 db m t x y p)
    (hk : m.KeepPtrs m') (hp : ∀ n, p.handle = some n → (m.handle? n).isSome = true) :
    HPtrHist sp S0 db m' t x y p := by
  rcases h with h | ⟨r, w, h1, h2, h3⟩ | h
  · exact Or.inl (hk.canon p h)
  · exact Or.inr (Or.inl ⟨r, w, by rw [hk.slowRef S0 y hp]; exact h1, h2, h3⟩)
  · exact Or.inr (Or.inr h)

/-- The handle of a pointer of an object in memory exists. -/
theorem HTableOK.ptr_handle (ht : HTableOK m) {a : Nat} {o : HObj V} (ho : m.obj? a = some o)
    {y : NodeId} {p : HPtr} (hp : o.ptr? y = some p) :
    ∀ n, p.handle = some n → (m.handle? n).isSome = true := by
  intro n hn
  obtain ⟨hd, hh, -⟩ := ht.ptrNode ho hp hn
  rw [hh]; rfl

/-- The invariant carries over to a memory that keeps what the pointers give, if
every canonical object of the new memory either was canonical with the same
pointer, or has a pointer as the invariant asks. -/
theorem HInvH.transfer (hh : HInvH sp db S0 k m) (ht : HTableOK m) (hk : m.KeepPtrs m')
    (hcan : ∀ a o', m'.obj? a = some o' → o'.canonical = true → ∀ t ≤ k,
      reachable sp db.P t o'.node = true → ∀ y ∈ sp.live (o'.hist.upTo t),
        (∃ o, m.obj? a = some o ∧ o.canonical = true ∧ o.node = o'.node ∧
          o.hist.upTo t = o'.hist.upTo t ∧ o'.ptr? y = o.ptr? y) ∨
        ∃ p, o'.ptr? y = some p ∧ HPtrHist sp S0 db m' t o'.node y p) :
    HInvH sp db S0 k m' := by
  intro a o' ho' hc t ht' hr y hy
  rcases hcan a o' ho' hc t ht' hr y hy with ⟨o, ho, hco, hn, hup, hptr⟩ | h2
  · obtain ⟨p, hp, hph⟩ := hh a o ho hco t ht' (by rw [hn]; exact hr) y (by rw [hup]; exact hy)
    refine ⟨p, by rw [hptr]; exact hp, ?_⟩
    rw [← hn]
    exact hph.keep hk (ht.ptr_handle ho hp)
  · exact h2

end Keep

/-! ## Good versions -/

section Good

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : HMem V}

/-- A live child at t of a canonical object of a node reachable at t is
reachable at t, not the root, and written. -/
theorem HEInv.reach_child (hinv : Inv sp db k) (hls : LiveSub sp) (hm : HEInv sp db S0 k m) {a : Nat}
    {o : HObj V} (ho : m.obj? a = some o) (hc : o.canonical = true) {t : Time}
    (hr : reachable sp db.P t o.node = true) {y : NodeId} (hy : y ∈ sp.live (o.hist.upTo t)) :
    reachable sp db.P t y = true ∧ y ≠ SIS.root ∧ written sp y = true := by
  obtain ⟨n, hn, hh, -, -⟩ := hm.cc a o ho hc
  rw [hh] at hy
  obtain ⟨h1, h2, -⟩ := hinv.reach_child hls hn hr hy
  exact ⟨h1, h2, written_of_ne_root sp h2⟩

/-- Lemma M for a version at least as new as one good for t. -/
theorem Inv.good_of_le (hinv : Inv sp db k) (hls : LiveSub sp) {y : NodeId} {r1 r : Nat}
    {u w : Version V} (hu : db.S.versionAt r1 y = some u) (hw : db.S.versionAt r y = some w)
    (hle : r1 ≤ r) {t : Time} (hg : good sp db.S db.P t u = true) : good sp db.S db.P t w = true :=
  hinv.newer hls (u.level + 1) r1 r y u w (by omega) hu hw hle t hg

/-- A pointer whose record is the latest version of a written pointee not in D,
reachable at t ≤ k, is as a read at t needs it. -/
theorem HPtrHist.clean (hinv : Inv sp db k) (hls : LiveSub sp) {y : NodeId} {p : HPtr}
    (hyD : inD db.D y = false) (hyw : written sp y = true) {t : Time} (ht : t ≤ k)
    (hry : reachable sp db.P t y = true) (href : m.ptrRef S0 y p = (db.S.lv y).map (·.recNo))
    (x : NodeId) : HPtrHist sp S0 db m t x y p := by
  cases hc : m.holdsCanonical p with
  | true => exact Or.inl hc
  | false =>
    right; left
    obtain ⟨v, hv, hg⟩ := hinv.clean_good hls hyD hyw ht hry
    rw [HMem.ptrRef_not_canonical S0 hc, hv] at href
    exact ⟨v.recNo, v, href, hinv.lv_at hv, hg⟩

/-- The pointers of a snapshot of a version good for t, for its live children
at t: the slow path's reference names a version good for t, at least as new as
the version's reference (lemma M). -/
theorem HEInv.snap_goodRef (hinv : Inv sp db k) (hls : LiveSub sp) (hm : HEInv sp db S0 k m) {a : Nat}
    {o : HObj V} (ho : m.obj? a = some o) (hc : o.canonical = false) {r : Nat} {w : Version V}
    (hp : o.pos = some r) (hw : db.S.versionAt r o.node = some w) {t : Time}
    (hg : good sp db.S db.P t w = true) {y : NodeId} (hy : y ∈ sp.live (o.hist.upTo t)) :
    ∃ q, o.ptr? y = some q ∧ HGoodRef sp S0 db m t y q := by
  obtain ⟨r0, w0, hp0, hw0, hh, -, -, hex, hsp⟩ := hm.snap a o ho hc
  rw [hp, Option.some.injEq] at hp0
  subst hp0
  rw [hw, Option.some.injEq] at hw0
  subst hw0
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (hex y (mem_pointees_of_live hls hy))
  rw [hh] at hy
  rw [good_iff] at hg
  obtain ⟨-, hch⟩ := hg
  obtain ⟨r1, u, hr1, hu, -, hgu⟩ := hch y hy
  refine ⟨q, hq, ?_⟩
  -- w's reference after Rule R, and the pointer's, at least as new.
  obtain ⟨q0, hq0⟩ := ruleRRef_some_some S0 m.s y r1
  have hq0le := ruleRRef_some_ge hq0
  obtain ⟨r2, hr2, hle2⟩ := hsp y q hq q0 (by rw [hr1]; exact hq0)
  obtain ⟨r3, hr3, hle3⟩ := m.slowRef_ge S0 y q hr2
  obtain ⟨w3, hw3⟩ := hm.slowRef_ver hinv ho hq hr3
  exact ⟨r3, w3, hr3, hw3, hinv.good_of_le hls hu hw3 (by omega) hgu⟩

/-- The slow path's reference of a pointer that holds y's live handle is its
reference after Rule R: a live handle has no written position. -/
theorem HEInv.slowRef_live (hm : HEInv sp db S0 k m) {y : NodeId} {n : Nat} (ht : m.tableOf y = some n)
    {p : HPtr} (hpn : p.handle = some n) : m.slowRef S0 y p = ruleRRef S0 m.s y p.ref := by
  obtain ⟨hd, -, -, hh, hl, -⟩ := hm.tbl.entry ht
  unfold HMem.slowRef
  rw [hpn]
  simp only [Option.bind_some, hh, hm.liveW n hd hh hl, maxRef_none]

end Good

/-! ## Reads keep the invariant -/

section Read

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : HMem V}

/-- The readers' follow keeps the invariant: every canonical object after it was
canonical before, with the same pointers but the parent's pointer for y; and
that pointer, if the memory changed, held no canonical object, and its slow
path's reference is as it was. -/
theorem HInvH.followR (hinv : Inv sp db k) (hm : HEInv sp db S0 k m) (hh : HInvH sp db S0 k m)
    {a : Nat} {o : HObj V} (ho : m.obj? a = some o) {y : NodeId} {m' : HMem V} {n b : Nat}
    (hf : m.followR sp S0 db.S a y = some (m', n, b)) : HInvH sp db S0 k m' := by
  have hF := hm.followR_ok hinv ho hf
  apply hh.transfer hm.tbl hF.keep
  intro x o' hx hc t ht hr z hz
  obtain ⟨o0, hx0, hcore, hsame, hptrs⟩ := hF.back x o' hx hc
  have e1 : o'.node = o0.node := congrArg (fun c => c.1) hcore
  have e4 : o'.hist = o0.hist := congrArg (fun c => c.2.2.2.1) hcore
  have e5 : o'.canonical = o0.canonical := congrArg (fun c => c.2.2.2.2.1) hcore
  have hco : o0.canonical = true := by rw [← e5]; exact hc
  by_cases hxz : x = a ∧ z = y
  · obtain ⟨hxa, hzy⟩ := hxz
    rw [hxa] at hx0 hx ⊢
    rw [hzy] at hz ⊢
    obtain ⟨p, hp, hph⟩ := hh a o0 hx0 hco t ht (by rw [← e1]; exact hr) y (by rw [← e4]; exact hz)
    rcases hF.ptrA o0 p o' hx0 hp hx with hmm | ⟨hnc, p', hp', href, hn'⟩
    · -- The fast path: the memory is as it was.
      left
      rw [hmm, hx0, Option.some.injEq] at hx
      subst hx
      exact ⟨_, hx0, hco, rfl, rfl, rfl⟩
    · -- The slow path: the pointer held no canonical object, and its slow path's
      -- reference is as it was.
      right
      refine ⟨p', hp', ?_⟩
      rcases hph with h1 | ⟨r, w, h1, h2, h3⟩ | h1
      · rw [hnc] at h1; cases h1
      · right; left
        refine ⟨r, w, ?_, h2, h3⟩
        rw [hF.inv.slowRef_live hF.tableOf hn', href, hF.keep.s, HMem.ruleR_slowRef]
        exact h1
      · right; right; rw [e1]; exact h1
  · left
    refine ⟨o0, hx0, hco, e1.symm, by rw [e4], ?_⟩
    by_cases hxa : x = a
    · exact hptrs z (fun h => hxz ⟨hxa, h⟩)
    · rw [hsame hxa]

/-- A reader's follow of any pointer keeps the invariant. -/
theorem HInvH.follow_reader (hinv : Inv sp db k) (hm : HEInv sp db S0 k m) (hh : HInvH sp db S0 k m)
    (a : Nat) (y : NodeId) : HInvH sp db S0 k (m.follow sp S0 db.S a y false).1 := by
  unfold HMem.follow
  cases hf : m.followR sp S0 db.S a y with
  | none => exact hh
  | some r =>
    obtain ⟨m', n, b⟩ := r
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases ho : m.obj? a with
    | none => unfold HMem.followR at hf; rw [ho] at hf; cases hf
    | some o => exact hh.followR hinv hm ho hf

/-- A read at any time, from any object, keeps both invariants. -/
theorem HInvH.readAt (hinv : Inv sp db k) :
    ∀ (fuel : Nat) (m : HMem V) (t : Time) (a : Nat), HEInv sp db S0 k m → HInvH sp db S0 k m →
      HEInv sp db S0 k (m.readAt sp S0 db.S fuel t a).1 ∧
        HInvH sp db S0 k (m.readAt sp S0 db.S fuel t a).1 := by
  intro fuel
  induction fuel with
  | zero => intro m t a hm hh; exact ⟨hm, hh⟩
  | succ fuel ih =>
    intro m t a hm hh
    unfold HMem.readAt
    cases ho : m.obj? a with
    | none => exact ⟨hm, hh⟩
    | some o =>
      simp only
      apply foldl_invH _ (fun m => HEInv sp db S0 k m ∧ HInvH sp db S0 k m) _ _ _ ⟨hm, hh⟩
      intro acc z ⟨hacc, hhacc⟩
      have hf := hacc.follow_reader hinv a z
      have hfh := hhacc.follow_reader hinv hacc a z
      generalize acc.1.follow sp S0 db.S a z false = res at hf hfh ⊢
      obtain ⟨m1, ob⟩ := res
      cases ob with
      | none => exact ⟨hf, hfh⟩
      | some b =>
        simp only
        cases ho1 : m1.obj? b with
        | none => exact ⟨hf, hfh⟩
        | some o1 =>
          simp only
          split
          · exact ih m1 t b hf hfh
          · exact ⟨hf, hfh⟩

theorem HInvH.read (hinv : Inv sp db k) (hm : HEInv sp db S0 k m) (hh : HInvH sp db S0 k m) (t : Time) :
    HInvH sp db S0 k (m.read sp S0 db.S t).1 := by
  unfold HMem.read
  cases m.obj? m.root with
  | none => exact hh
  | some o => exact (HInvH.readAt hinv _ m t _ hm hh).2

end Read

/-! ## Evictions keep the invariant -/

section Evict

variable {sp : Spec V T} {db : DB V T} {S0 : Stream V T} {k : Nat} {m : HMem V}

/-- An eviction keeps the invariant. A pointer that held the evicted handle and
its canonical object now has the handle's written position, the object's
position, as its slow path's reference: its node's latest version, good for
every time at which the node is reachable, since the node is not in D (the
object was not pinned). Any other pointer gives what it gave. -/
theorem HInvH.evict (hinv : Inv sp db k) (hls : LiveSub sp) (hm : HEInv sp db S0 k m)
    (hh : HInvH sp db S0 k m) (n : Nat) : HInvH sp db S0 k (m.evict db.D n) := by
  cases hev : m.evictable db.D n with
  | false => rw [HMem.evict_not m db.D n hev]; exact hh
  | true =>
  obtain ⟨hd, b, ob, hh0, -, hb, hob, hpin, -⟩ := HMem.evictable_some hev
  have hobjn : m.objOf n = some b := by simp [HMem.objOf, hh0, hb]
  have eobj := HMem.evict_obj? hev hh0 hb
  have ehd := HMem.evict_handle? hev hh0 hb
  have es := HMem.evict_s m db.D n
  obtain ⟨-, ob', hob', hon⟩ := hm.tbl.obj_of_handle hh0 hb
  rw [hob, Option.some.injEq] at hob'
  subst hob'
  -- A pointer that does not hold handle n gives what it gave.
  have hslow : ∀ (z : NodeId) (q : HPtr), q.handle ≠ some n →
      (m.evict db.D n).slowRef S0 z q = m.slowRef S0 z q := by
    intro z q hq
    unfold HMem.slowRef
    rw [es]
    cases hqn : q.handle with
    | none => rfl
    | some n' =>
      have hne : n' ≠ n := fun h => hq (by rw [hqn, h])
      simp only [Option.bind_some, ehd n', hne, ↓reduceIte]
  have hcanq : ∀ q : HPtr, q.handle ≠ some n → m.holdsCanonical q = true →
      (m.evict db.D n).holdsCanonical q = true := by
    intro q hq h
    obtain ⟨n', c, oc, hqn, hc, hoc, hcc⟩ := (m.holdsCanonical_iff q).mp h
    have hne : n' ≠ n := fun h => hq (by rw [hqn, h])
    have hcb : c ≠ b := by
      intro he
      rw [he] at hc
      apply hne
      unfold HMem.objOf at hc
      cases hq' : m.handle? n' with
      | none => rw [hq'] at hc; cases hc
      | some hd'' =>
        rw [hq'] at hc
        simp only [Option.bind_some] at hc
        exact hm.tbl.uniq hq' hc hobjn
    refine ((m.evict db.D n).holdsCanonical_iff q).mpr ⟨n', c, oc, hqn, ?_, ?_, hcc⟩
    · unfold HMem.objOf; rw [ehd n']; simp only [hne, ↓reduceIte]; exact hc
    · rw [eobj]; simp only [hcb, ↓reduceIte]; exact hoc
  intro x o' hx hc t ht hr z hz
  rw [eobj] at hx
  split at hx
  · cases hx
  · obtain ⟨p, hp, hph⟩ := hh x o' hx hc t ht hr z hz
    refine ⟨p, hp, ?_⟩
    by_cases hpn : p.handle = some n
    · -- The pointer held the evicted handle, of z.
      obtain ⟨hd', hh', hnode⟩ := hm.tbl.ptrNode hx hp hpn
      rw [hh0, Option.some.injEq] at hh'
      rw [← hh'] at hnode
      have hslowE : (m.evict db.D n).slowRef S0 z p =
          maxRef (ruleRRef S0 m.s z p.ref) (m.evictWritten hd b) := by
        unfold HMem.slowRef
        rw [es, hpn]
        simp only [Option.bind_some, ehd n, ↓reduceIte]
      cases hcb : ob.canonical with
      | true =>
        right; left
        -- z is not in D: its canonical object was not pinned.
        have hzD : inD db.D z = false := by
          unfold HMem.pinned at hpin
          simp only [Bool.or_eq_false_iff, hob, hcb, Bool.true_and] at hpin
          rw [← hnode, ← hon]; exact hpin.2
        obtain ⟨hrz, -, hzw⟩ := hm.reach_child hinv hls hx hc hr hz
        obtain ⟨v, hv, hg⟩ := hinv.clean_good hls hzD hzw ht hrz
        have hwr : m.evictWritten hd b = some v.recNo := by
          unfold HMem.evictWritten
          rw [hob]
          simp only [hcb, ↓reduceIte]
          rw [hm.pos b ob hob hcb, hon, hnode, hv]
          rfl
        refine ⟨v.recNo, v, ?_, hinv.lv_at hv, hg⟩
        rw [hslowE, hwr]
        apply maxRef_le
        intro r0 hr0
        obtain ⟨-, v', hv', hle⟩ :=
          hinv.ruleR_bound hm.pre m.s (fun r' h' => hm.rver x o' z p r' hx hp h') hr0
        rw [hv, Option.some.injEq] at hv'
        subst hv'
        exact hle
      | false =>
        -- The written position is as it was, and the pointer held no canonical object.
        have hwr : m.evictWritten hd b = hd.written := by
          unfold HMem.evictWritten; rw [hob]; simp only [hcb, Bool.false_eq_true, ↓reduceIte]
        have hsl : (m.evict db.D n).slowRef S0 z p = m.slowRef S0 z p := by
          rw [hslowE, hwr]
          unfold HMem.slowRef
          rw [hpn]
          simp only [Option.bind_some, hh0]
        have hnc : m.holdsCanonical p = false := by
          cases h : m.holdsCanonical p with
          | false => rfl
          | true =>
            obtain ⟨n', c, oc, hn', hc', hoc, hcc⟩ := (m.holdsCanonical_iff p).mp h
            rw [hpn, Option.some.injEq] at hn'
            rw [← hn', hobjn, Option.some.injEq] at hc'
            rw [← hc', hob, Option.some.injEq] at hoc
            rw [← hoc, hcb] at hcc
            cases hcc
        rcases hph with h1 | ⟨r, w, h1, h2, h3⟩ | h1
        · rw [hnc] at h1; cases h1
        · exact Or.inr (Or.inl ⟨r, w, by rw [hsl]; exact h1, h2, h3⟩)
        · exact Or.inr (Or.inr h1)
    · rcases hph with h1 | ⟨r, w, h1, h2, h3⟩ | h1
      · exact Or.inl (hcanq p hpn h1)
      · exact Or.inr (Or.inl ⟨r, w, by rw [hslow z p hpn]; exact h1, h2, h3⟩)
      · exact Or.inr (Or.inr h1)

/-- Every operation between transactions keeps the invariant. -/
theorem HInvH.cacheOp (hinv : Inv sp db k) (hls : LiveSub sp) (hm : HEInv sp db S0 k m)
    (hh : HInvH sp db S0 k m) (op : HCacheOp) : HInvH sp db S0 k (m.cacheOp sp S0 db.S db.D op) := by
  cases op with
  | read t => exact hh.read hinv hm t
  | evict n => exact hh.evict hinv hls hm n

theorem HInvH.cacheOps (hinv : Inv sp db k) (hls : LiveSub sp) (ops : List HCacheOp) :
    ∀ m, HEInv sp db S0 k m → HInvH sp db S0 k m →
      HInvH sp db S0 k (ops.foldl (HMem.cacheOp sp S0 db.S db.D) m) := by
  induction ops with
  | nil => intro m _ hh; exact hh
  | cons op ops ih =>
    intro m hm hh
    exact ih _ (hm.cacheOp hinv op) (hh.cacheOp hinv hls hm op)

end Evict

end SIS
