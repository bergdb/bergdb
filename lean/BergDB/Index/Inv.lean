/-
The user indexes of BergDB 2026.4 in Lean: the invariant and the lemmas for
each kind of step (bergdb 020-29), after 020-26, section 4's argument.

The invariant `Inv` has three parts: `SInv`, of the stream alone, so of every
stream a crash may go back to; `MInv`, of memory with the stream, which a
start makes anew; and `SInv` of every earlier stream, for the lookups at
earlier times. Each holds for every name: the names share only the data, the
time, the virtual keys of their directories and the lock.
-/
import BergDB.Index.Model

namespace BergDB.Index

variable {V F L W : Type}

/-! ### Function updates -/

@[simp] theorem upd_same {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) :
    upd f a b a = b := by simp [upd]

theorem upd_ne {α β : Type} [DecidableEq α] (f : α → β) {a x : α} (b : β) (h : x ≠ a) :
    upd f a b x = f x := by simp [upd, h]

@[simp] theorem upd2_same {β : Type} (f : Name → Gen → β) (n : Name) (g : Gen) (b : β) :
    upd2 f n g b n g = b := by simp [upd2]

theorem upd2_ne {β : Type} (f : Name → Gen → β) {n n' : Name} {g g' : Gen} (b : β)
    (h : ¬ (n' = n ∧ g' = g)) : upd2 f n g b n' g' = f n' g' := by
  simp only [upd2]; rw [ite_eq_right h]

/-! ### The invariant -/

/-- The key k is covered in the generation g of the name n with the function
fn: if its value has an entry, the generation has it. -/
def Covered (sp : Spec V F L) (st : Stream V F L) (n : Name) (g : Gen) (fn : F) (k : Key) :
    Prop :=
  ∀ l, sp.f fn k (st.data k) = some l → st.ent n g k l

/-- Two definitions of a name that agree for the directory dir: if either is
of dir, they are the same index, in whatever state. -/
def sameOn (sp : Spec V F L) (dir : Dir) : Option (Def F) → Option (Def F) → Prop
  | none, none => True
  | some a, some b => (sp.dirF a.fn = dir ∨ sp.dirF b.fn = dir) → a.gen = b.gen ∧ a.fn = b.fn
  | some a, none => sp.dirF a.fn ≠ dir
  | none, some b => sp.dirF b.fn ≠ dir

/-- What holds of the stream at every time (020-26, section 3), for each name. -/
structure SInv (sp : Spec V F L) (st : Stream V F L) : Prop where
  /-- A live generation is at most the latest time, a deleted one before it
  (4.3), so a creation's G is new. -/
  gen_le : ∀ n d, st.dfn n = some d → d.gen ≤ st.now
  mark_lt : ∀ n g, st.mark n g = true → g < st.now
  /-- NoStaleEntry: every entry of a live generation is f of its key's value. -/
  noStale : ∀ n d, st.dfn n = some d → ∀ k l, st.ent n d.gen k l →
    sp.f d.fn k (st.data k) = some l
  /-- With noStale, IndexIsFunction: an active index has every entry of f. -/
  active : ∀ n d, st.dfn n = some d → d.active = true → ∀ k, Covered sp st n d.gen d.fn k
  /-- GensAccounted (020-22's V8): a generation with entries is live or has a marker. -/
  accounted : ∀ n g k l, st.ent n g k l → (∃ d, st.dfn n = some d ∧ d.gen = g) ∨
    st.mark n g = true
  /-- MarkerNotLive (V7): no marker names a live generation, so a start accepts. -/
  markerNotLive : ∀ n d, st.dfn n = some d → st.mark n d.gen = false

/-- A writer's transaction in flight (020-26, section 4, point 1): its R is
fixed; for each key not written after R, the previous value it read is the
key's value; for each key whose directory's virtual key was not written after
R, the index set it read for the key agrees, for that directory, with the
definitions. -/
def WInv (sp : Spec V F L) (st : Stream V F L) : WSt V F → Prop
  | .idle => True
  | .run _ _ R old S =>
      R ≤ st.now ∧ (∀ k, st.wk k ≤ R → st.data k = old k) ∧
        (∀ k m, S k = some m → st.wv (sp.dirOf k) ≤ R →
          ∀ n, sameOn sp (sp.dirOf k) (m n) (st.dfn n))

/-- A build step between its read and its commit (point 3): the values it read
are the keys' values if the keys were not written after R; the keys whose
values had no entry at R are covered, as every writer since has kept them. -/
structure StepInv (sp : Spec V F L) (st : Stream V F L) (n : Name) (g : Gen) (b : BSt V F) :
    Prop where
  R_le : b.R ≤ st.now
  snap : ∀ k, st.wk k ≤ b.R → st.data k = b.snap k
  range : ∃ e, b.E = some e ∧ (b.ended = true → b.hi = e + 1)
  noneCov : ∀ d, st.dfn n = some d → d.gen = g → ∀ k, b.next ≤ k → k < b.hi →
    sp.f b.fn k (b.snap k) = none → Covered sp st n g b.fn k

/-- A build of the generation g of the name n (points 3 to 5; BuildCovers):
while g is live, it has the definition's function, it is building, and every
key the build has passed is covered; at the activation every key is passed. -/
structure BInv (sp : Spec V F L) (st : Stream V F L) (n : Name) (g : Gen) (b : BSt V F) :
    Prop where
  fnEq : ∀ d, st.dfn n = some d → d.gen = g → d.fn = b.fn ∧ d.active = false
  cover : ∀ d, st.dfn n = some d → d.gen = g → ∀ k, b.passed k → Covered sp st n g b.fn k
  done : b.pc = .activate → ∀ k, b.passed k
  inStep : b.pc = .check ∨ b.pc = .commit → StepInv sp st n g b
  live : b.pc = .commit → st.wdef n ≤ b.R → ∃ d, st.dfn n = some d ∧ d.gen = g

/-- A cleanup of the generation g of the name n (point 6): g has its marker;
at its end, g has no entry. -/
structure CInv (st : Stream V F L) (n : Name) (g : Gen) (c : CSt L) : Prop where
  marked : st.mark n g = true
  empty : c.pc = .done → ∀ k l, ¬ st.ent n g k l

/-- What holds of memory with the stream (020-26, section 3: MemAgrees,
LockSane; and the threads' invariants). -/
structure MInv (sp : Spec V F L) (st : Stream V F L) (m : Mem V F L W) : Prop where
  memAgrees : ∀ n, m.mem n = st.dfn n ∨ m.admin.name = some n
  lockMgr : m.lock = .mgr ↔ m.admin ≠ .idle
  adminCreate : ∀ n g fn, m.admin = .create n g fn → st.dfn n = some ⟨g, fn, false⟩
  adminDelete : ∀ n g, m.admin = .delete n g →
    st.dfn n = none ∧ st.mark n g = true ∧ m.cln n g = none
  lockBld : ∀ n g, m.lock = .bld n g → ∃ b, m.bld n g = some b ∧ b.locked = true
  bLocked : ∀ n g b, m.bld n g = some b → b.locked = true → m.lock = .bld n g
  wInv : ∀ w, WInv sp st (m.wr w)
  bInv : ∀ n g b, m.bld n g = some b → BInv sp st n g b
  bLt : ∀ n g b, m.bld n g = some b → g < st.now ∨ ∃ d, st.dfn n = some d ∧ d.gen = g
  cInv : ∀ n g c, m.cln n g = some c → CInv st n g c

/-- The invariant of the system. -/
structure Inv (sp : Spec V F L) (s : Sys V F L W) : Prop where
  sinv : SInv sp s.st
  past : ∀ x ∈ s.past, SInv sp x
  minv : MInv sp s.st s.m

/-! ### Small lemmas -/

theorem sameOn_refl (sp : Spec V F L) (dir : Dir) : ∀ x : Option (Def F), sameOn sp dir x x
  | none => trivial
  | some _ => fun _ => ⟨rfl, rfl⟩

theorem Covered.mono {sp : Spec V F L} {st st' : Stream V F L} {n : Name} {g : Gen} {fn : F}
    {k : Key} (h : Covered sp st n g fn k) (hd : st'.data k = st.data k)
    (he : ∀ l, st.ent n g k l → st'.ent n g k l) : Covered sp st' n g fn k := by
  intro l hl
  rw [hd] at hl
  exact he l (h l hl)

theorem Covered.of_none {sp : Spec V F L} {st : Stream V F L} {n : Name} {g : Gen} {fn : F}
    {k : Key} (h : sp.f fn k (st.data k) = none) : Covered sp st n g fn k := by
  intro l hl
  rw [h] at hl
  cases hl

theorem MInv.adminIdle {sp : Spec V F L} {st : Stream V F L} {m : Mem V F L W}
    (h : MInv sp st m) (hl : m.lock ≠ .mgr) : m.admin = .idle :=
  Classical.byContradiction fun hne => hl (h.lockMgr.mpr hne)

/-- With no definition change under way, the maps are the definitions. -/
theorem MInv.memEq {sp : Spec V F L} {st : Stream V F L} {m : Mem V F L W}
    (h : MInv sp st m) (hl : m.lock ≠ .mgr) (n : Name) : m.mem n = st.dfn n := by
  rcases h.memAgrees n with h1 | h1
  · exact h1
  · rw [h.adminIdle hl] at h1; cases h1

theorem MInv.notLocked {sp : Spec V F L} {st : Stream V F L} {m : Mem V F L W}
    (h : MInv sp st m) {n : Name} {g : Gen} {b : BSt V F} (hb : m.bld n g = some b)
    (hl : m.lock ≠ .bld n g) : b.locked = false := by
  cases hlk : b.locked with
  | false => rfl
  | true => exact absurd (h.bLocked n g b hb hlk) hl

/-! ### Frames: what a commit keeps of the threads' invariants

A commit writes some keys at the time now + 1; a transaction in flight with
R ≤ now that has one of them in its read set will be refused, and the other
keys keep their values. -/

theorem WInv.frame {sp : Spec V F L} {st st' : Stream V F L} {x : WSt V F} (h : WInv sp st x)
    (hnow : st.now ≤ st'.now)
    (hk : ∀ k, (st'.wk k = st.wk k ∧ st'.data k = st.data k) ∨ st.now < st'.wk k)
    (hv : ∀ dir, (st'.wv dir = st.wv dir ∧
        ∀ n x, sameOn sp dir x (st.dfn n) → sameOn sp dir x (st'.dfn n)) ∨
      st.now < st'.wv dir) :
    WInv sp st' x := by
  cases x with
  | idle => trivial
  | run ws nv R old S =>
    simp only [WInv] at h ⊢
    obtain ⟨hR, hd, hS⟩ := h
    refine ⟨by omega, fun k hw => ?_, fun k m hm hw n => ?_⟩
    · rcases hk k with ⟨h1, h2⟩ | h1
      · rw [h2]; exact hd k (by omega)
      · omega
    · rcases hv (sp.dirOf k) with ⟨h1, h2⟩ | h1
      · exact h2 n (m n) (hS k m hm (by omega) n)
      · omega

theorem BInv.frame {sp : Spec V F L} {st st' : Stream V F L} {n : Name} {g : Gen}
    {b : BSt V F} (h : BInv sp st n g b) (hnow : st.now ≤ st'.now)
    (hk : ∀ k, (st'.wk k = st.wk k ∧ st'.data k = st.data k) ∨ st.now < st'.wk k)
    (hdef : (st'.wdef n = st.wdef n ∧ st'.dfn n = st.dfn n) ∨ st.now < st'.wdef n)
    (hlive : ∀ d', st'.dfn n = some d' → d'.gen = g →
      ∃ d, st.dfn n = some d ∧ d.gen = g ∧ d.fn = d'.fn ∧ d.active = d'.active)
    (hcov : ∀ d, st.dfn n = some d → d.gen = g → ∀ k,
      Covered sp st n g b.fn k → Covered sp st' n g b.fn k) :
    BInv sp st' n g b := by
  refine ⟨?_, ?_, h.done, ?_, ?_⟩
  · intro d' hd' hg
    obtain ⟨d, hd, hdg, hdf, hda⟩ := hlive d' hd' hg
    obtain ⟨h1, h2⟩ := h.fnEq d hd hdg
    exact ⟨by rw [← hdf]; exact h1, by rw [← hda]; exact h2⟩
  · intro d' hd' hg k hk'
    obtain ⟨d, hd, hdg, -, -⟩ := hlive d' hd' hg
    exact hcov d hd hdg k (h.cover d hd hdg k hk')
  · intro hpc
    have hs := h.inStep hpc
    refine ⟨Nat.le_trans hs.R_le hnow, fun k hw => ?_, hs.range,
      fun d' hd' hg k h1 h2 h3 => ?_⟩
    · have hR := hs.R_le
      rcases hk k with ⟨e1, e2⟩ | e1
      · rw [e2]; exact hs.snap k (by omega)
      · omega
    · obtain ⟨d, hd, hdg, -, -⟩ := hlive d' hd' hg
      exact hcov d hd hdg k (hs.noneCov d hd hdg k h1 h2 h3)
  · intro hpc hw
    have hR := (h.inStep (Or.inr hpc)).R_le
    rcases hdef with ⟨e1, e2⟩ | e1
    · rw [e2]; exact h.live hpc (by omega)
    · omega

theorem CInv.frame {st st' : Stream V F L} {n : Name} {g : Gen} {c : CSt L} (h : CInv st n g c)
    (hm : st'.mark n g = true) (he : ∀ k l, st'.ent n g k l → st.ent n g k l) :
    CInv st' n g c :=
  ⟨hm, fun hpc k l hkl => h.empty hpc k l (he k l hkl)⟩

/-- Memory kept over a commit that changes neither the definitions nor the
markers nor the virtual and definition keys. -/
theorem MInv.frameS {sp : Spec V F L} {st st' : Stream V F L} {m : Mem V F L W}
    (h : MInv sp st m) (hnow : st.now ≤ st'.now)
    (hk : ∀ k, (st'.wk k = st.wk k ∧ st'.data k = st.data k) ∨ st.now < st'.wk k)
    (hdfn : st'.dfn = st.dfn) (hwv : st'.wv = st.wv) (hwdef : st'.wdef = st.wdef)
    (hmark : st'.mark = st.mark)
    (hcov : ∀ n d, st.dfn n = some d → ∀ k,
      Covered sp st n d.gen d.fn k → Covered sp st' n d.gen d.fn k)
    (hent : ∀ n g k l, st.mark n g = true → st'.ent n g k l → st.ent n g k l) :
    MInv sp st' m := by
  refine ⟨?_, h.lockMgr, ?_, ?_, h.lockBld, h.bLocked, ?_, ?_, ?_, ?_⟩
  · intro n; rw [hdfn]; exact h.memAgrees n
  · intro n g fn ha; rw [hdfn]; exact h.adminCreate n g fn ha
  · intro n g ha; rw [hdfn, hmark]; exact h.adminDelete n g ha
  · intro w
    refine (h.wInv w).frame hnow hk (fun dir => Or.inl ⟨by rw [hwv], ?_⟩)
    intro n x hx; rw [hdfn]; exact hx
  · intro n g b hb
    have hb' := h.bInv n g b hb
    refine hb'.frame hnow hk (Or.inl ⟨by rw [hwdef], by rw [hdfn]⟩) ?_ ?_
    · intro d' hd' hg
      exact ⟨d', by rw [← hdfn]; exact hd', hg, rfl, rfl⟩
    · intro d hd hg k hc
      have hf := (hb'.fnEq d hd hg).1
      have h2 := hcov n d hd k (by rw [hf, hg]; exact hc)
      rw [hg, hf] at h2
      exact h2
  · intro n g b hb
    rcases h.bLt n g b hb with h1 | h1
    · exact Or.inl (Nat.lt_of_lt_of_le h1 hnow)
    · rw [hdfn]; exact Or.inr h1
  · intro n g c hc
    have hc' := h.cInv n g c hc
    exact hc'.frame (by rw [hmark]; exact hc'.marked)
      (fun k l hkl => hent n g k l hc'.marked hkl)

/-! ### Memory changes -/

theorem MInv.setW {sp : Spec V F L} {st : Stream V F L} {m : Mem V F L W} [DecidableEq W]
    (h : MInv sp st m) (w : W) {x : WSt V F} (hx : WInv sp st x) :
    MInv sp st { m with wr := upd m.wr w x } := by
  refine ⟨h.memAgrees, h.lockMgr, h.adminCreate, h.adminDelete, h.lockBld, h.bLocked, ?_,
    h.bInv, h.bLt, h.cInv⟩
  intro w'
  show WInv sp st (upd m.wr w x w')
  by_cases hw : w' = w
  · rw [hw, upd_same]; exact hx
  · rw [upd_ne _ _ hw]; exact h.wInv w'

theorem MInv.setB {sp : Spec V F L} {st : Stream V F L} {m : Mem V F L W}
    (h : MInv sp st m) {n : Name} {g : Gen} {b b' : BSt V F} (hb : m.bld n g = some b)
    (hb' : BInv sp st n g b') (hl : b'.locked = b.locked) :
    MInv sp st { m with bld := upd2 m.bld n g (some b') } := by
  refine ⟨h.memAgrees, h.lockMgr, h.adminCreate, h.adminDelete, ?_, ?_, h.wInv, ?_, ?_, h.cInv⟩
  · intro n' g' hg'
    obtain ⟨b'', hb'', hl''⟩ := h.lockBld n' g' hg'
    show ∃ b, upd2 m.bld n g (some b') n' g' = some b ∧ b.locked = true
    by_cases hgg : n' = n ∧ g' = g
    · rw [hgg.1, hgg.2] at hb'' ⊢
      rw [hb] at hb''
      cases hb''
      exact ⟨b', upd2_same _ _ _ _, by rw [hl]; exact hl''⟩
    · rw [upd2_ne _ _ hgg]; exact ⟨b'', hb'', hl''⟩
  · intro n' g' b'' hb'' hl''
    change upd2 m.bld n g (some b') n' g' = some b'' at hb''
    by_cases hgg : n' = n ∧ g' = g
    · rw [hgg.1, hgg.2, upd2_same] at hb''
      cases hb''
      rw [hgg.1, hgg.2]; exact h.bLocked n g b hb (by rw [← hl]; exact hl'')
    · rw [upd2_ne _ _ hgg] at hb''; exact h.bLocked n' g' b'' hb'' hl''
  · intro n' g' b'' hb''
    change upd2 m.bld n g (some b') n' g' = some b'' at hb''
    by_cases hgg : n' = n ∧ g' = g
    · rw [hgg.1, hgg.2, upd2_same] at hb''
      cases hb''
      rw [hgg.1, hgg.2]; exact hb'
    · rw [upd2_ne _ _ hgg] at hb''; exact h.bInv n' g' b'' hb''
  · intro n' g' b'' hb''
    change upd2 m.bld n g (some b') n' g' = some b'' at hb''
    by_cases hgg : n' = n ∧ g' = g
    · rw [hgg.1, hgg.2]; exact h.bLt n g b hb
    · rw [upd2_ne _ _ hgg] at hb''; exact h.bLt n' g' b'' hb''

/-- A build removed, with the lock free or released. -/
theorem MInv.delB {sp : Spec V F L} {st : Stream V F L} {m : Mem V F L W}
    (h : MInv sp st m) {n : Name} {g : Gen} (hl : m.lock = .free ∨ m.lock = .bld n g) :
    MInv sp st { m with bld := upd2 m.bld n g none, lock := .free } := by
  have hidle : m.admin = .idle := h.adminIdle (by rcases hl with hl | hl <;> rw [hl] <;> simp)
  refine ⟨h.memAgrees, ?_, h.adminCreate, h.adminDelete, ?_, ?_, h.wInv, ?_, ?_, h.cInv⟩
  · show Lock.free = .mgr ↔ m.admin ≠ .idle
    rw [hidle]; simp
  · intro n' g' hg'; cases hg'
  · intro n' g' b'' hb'' hl''
    change upd2 m.bld n g none n' g' = some b'' at hb''
    by_cases hgg : n' = n ∧ g' = g
    · rw [hgg.1, hgg.2, upd2_same] at hb''; cases hb''
    · rw [upd2_ne _ _ hgg] at hb''
      have h1 := h.bLocked n' g' b'' hb'' hl''
      rcases hl with hl | hl
      · rw [hl] at h1; cases h1
      · rw [hl] at h1; cases h1; exact absurd ⟨rfl, rfl⟩ hgg
  · intro n' g' b'' hb''
    change upd2 m.bld n g none n' g' = some b'' at hb''
    by_cases hgg : n' = n ∧ g' = g
    · rw [hgg.1, hgg.2, upd2_same] at hb''; cases hb''
    · rw [upd2_ne _ _ hgg] at hb''; exact h.bInv n' g' b'' hb''
  · intro n' g' b'' hb''
    change upd2 m.bld n g none n' g' = some b'' at hb''
    by_cases hgg : n' = n ∧ g' = g
    · rw [hgg.1, hgg.2, upd2_same] at hb''; cases hb''
    · rw [upd2_ne _ _ hgg] at hb''; exact h.bLt n' g' b'' hb''

theorem MInv.setC {sp : Spec V F L} {st : Stream V F L} {m : Mem V F L W}
    (h : MInv sp st m) {n : Name} {g : Gen} {c c' : CSt L} (hc : m.cln n g = some c)
    (hc' : CInv st n g c') :
    MInv sp st { m with cln := upd2 m.cln n g (some c') } := by
  refine ⟨h.memAgrees, h.lockMgr, h.adminCreate, ?_, h.lockBld, h.bLocked, h.wInv, h.bInv,
    h.bLt, ?_⟩
  · intro n' g' ha
    obtain ⟨h1, h2, h3⟩ := h.adminDelete n' g' ha
    refine ⟨h1, h2, ?_⟩
    show upd2 m.cln n g (some c') n' g' = none
    by_cases hgg : n' = n ∧ g' = g
    · rw [hgg.1, hgg.2] at h3; rw [hc] at h3; cases h3
    · rw [upd2_ne _ _ hgg]; exact h3
  · intro n' g' c'' hc''
    change upd2 m.cln n g (some c') n' g' = some c'' at hc''
    by_cases hgg : n' = n ∧ g' = g
    · rw [hgg.1, hgg.2, upd2_same] at hc''; cases hc''; rw [hgg.1, hgg.2]; exact hc'
    · rw [upd2_ne _ _ hgg] at hc''; exact h.cInv n' g' c'' hc''

/-! ### A start -/

theorem minv_restart {sp : Spec V F L} {st : Stream V F L} :
    MInv sp st (restart (W := W) st) := by
  refine ⟨fun _ => Or.inl rfl, ?_, ?_, ?_, ?_, ?_, fun _ => trivial, ?_, ?_, ?_⟩
  · show Lock.free = .mgr ↔ Admin.idle ≠ (.idle : Admin F)
    simp
  · intro n g fn ha; cases ha
  · intro n g ha; cases ha
  · intro n g hg; cases hg
  · intro n g b hb hl
    change (match st.dfn n with
      | some d => if d.gen = g ∧ d.active = false then some (BSt.init d.fn) else none
      | none => none) = some b at hb
    cases hd : st.dfn n with
    | none => rw [hd] at hb; cases hb
    | some d =>
      rw [hd] at hb
      dsimp only at hb
      split at hb
      · cases hb; cases hl
      · cases hb
  · intro n g b hb
    change (match st.dfn n with
      | some d => if d.gen = g ∧ d.active = false then some (BSt.init d.fn) else none
      | none => none) = some b at hb
    cases hd : st.dfn n with
    | none => rw [hd] at hb; cases hb
    | some d =>
      rw [hd] at hb
      dsimp only at hb
      split at hb
      · rename_i hc
        cases hb
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro d' hd' _
          rw [hd] at hd'; cases hd'
          exact ⟨rfl, hc.2⟩
        · intro d' _ _ k hk
          rcases hk with hk | ⟨e, he, _⟩
          · exact absurd hk (Nat.not_lt_zero k)
          · cases he
        · intro hpc; cases hpc
        · intro hpc; rcases hpc with hpc | hpc <;> cases hpc
        · intro hpc; cases hpc
      · cases hb
  · intro n g b hb
    change (match st.dfn n with
      | some d => if d.gen = g ∧ d.active = false then some (BSt.init d.fn) else none
      | none => none) = some b at hb
    cases hd : st.dfn n with
    | none => rw [hd] at hb; cases hb
    | some d =>
      rw [hd] at hb
      dsimp only at hb
      split at hb
      · rename_i hc
        exact Or.inr ⟨d, rfl, hc.1⟩
      · cases hb
  · intro n g c hc
    change (if st.mark n g = true then some CSt.init else none) = some c at hc
    split at hc
    · rename_i hm
      cases hc
      exact ⟨hm, fun hpc => by cases hpc⟩
    · cases hc

end BergDB.Index
