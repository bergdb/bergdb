/-
The user indexes of BergDB 2026.4 in Lean: the invariant and the lemmas for
each kind of step (bergdb 020-29), after 020-26, section 4's argument.

The invariant `Inv` has three parts: `SInv`, of the stream alone, so of every
stream a crash may go back to; `MInv`, of memory with the stream, which a
start makes anew; and `SInv` of every earlier stream, for the lookups at
earlier times.
-/
import BergDB.Index.Model

namespace BergDB.Index

variable {V F L W : Type}

/-! ### Function updates -/

@[simp] theorem upd_same {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) :
    upd f a b a = b := by simp [upd]

theorem upd_ne {α β : Type} [DecidableEq α] (f : α → β) {a x : α} (b : β) (h : x ≠ a) :
    upd f a b x = f x := by simp [upd, h]

/-! ### The invariant -/

/-- The key k is covered in the generation g with the function fn: if its
value has an entry, the generation has it. -/
def Covered (sp : Spec V F L) (st : Stream V F L) (g : Gen) (fn : F) (k : Key) : Prop :=
  ∀ l, sp.f fn k (st.data k) = some l → st.ent g k l

/-- Two index sets that name the same index, in whatever state. -/
def sameIdx : Option (Def F) → Option (Def F) → Prop
  | none, none => True
  | some a, some b => a.gen = b.gen ∧ a.fn = b.fn
  | _, _ => False

/-- What holds of the stream at every time (020-26, section 3). -/
structure SInv (sp : Spec V F L) (st : Stream V F L) : Prop where
  /-- Every generation is before the latest time (4.3), so a creation's G is new. -/
  gen_lt : ∀ d, st.dfn = some d → d.gen < st.now
  mark_lt : ∀ g, st.mark g = true → g < st.now
  /-- NoStaleEntry: every entry of the live generation is f of its key's value. -/
  noStale : ∀ d, st.dfn = some d → ∀ k l, st.ent d.gen k l → sp.f d.fn k (st.data k) = some l
  /-- With noStale, IndexIsFunction: an active index has every entry of f. -/
  active : ∀ d, st.dfn = some d → d.active = true → ∀ k, Covered sp st d.gen d.fn k
  /-- GensAccounted (020-22's V8): a generation with entries is live or has a marker. -/
  accounted : ∀ g k l, st.ent g k l → (∃ d, st.dfn = some d ∧ d.gen = g) ∨ st.mark g = true
  /-- MarkerNotLive (V7): no marker names the live generation, so a start accepts. -/
  markerNotLive : ∀ d, st.dfn = some d → st.mark d.gen = false

/-- A writer's transaction in flight (020-26, section 4, point 1): its R is
fixed; for each key not written after R, the previous value it read is the
key's value; if the virtual key was not written after R, the index set it read
names the live index, or none if there is none. -/
def WInv (st : Stream V F L) : WSt V F → Prop
  | .idle => True
  | .set _ _ R old => R ≤ st.now ∧ ∀ k, st.wk k ≤ R → st.data k = old k
  | .commit _ _ R old S =>
      R ≤ st.now ∧ (∀ k, st.wk k ≤ R → st.data k = old k) ∧
        (st.wv ≤ R → sameIdx S st.dfn)

/-- A build step between its read and its commit (point 3): the values it read
are the keys' values if the keys were not written after R; the keys whose
values had no entry at R are covered, as every writer since has kept them. -/
structure StepInv (sp : Spec V F L) (st : Stream V F L) (g : Gen) (b : BSt V F) : Prop where
  R_le : b.R ≤ st.now
  snap : ∀ k, st.wk k ≤ b.R → st.data k = b.snap k
  range : ∃ e, b.E = some e ∧ (b.ended = true → b.hi = e + 1)
  noneCov : ∀ d, st.dfn = some d → d.gen = g → ∀ k, b.next ≤ k → k < b.hi →
    sp.f b.fn k (b.snap k) = none → Covered sp st g b.fn k

/-- A build of the generation g (points 3 to 5; BuildCovers): while g is live,
it has the definition's function, it is building, and every key the build has
passed is covered; at the activation every key is passed. -/
structure BInv (sp : Spec V F L) (st : Stream V F L) (g : Gen) (b : BSt V F) : Prop where
  fnEq : ∀ d, st.dfn = some d → d.gen = g → d.fn = b.fn ∧ d.active = false
  cover : ∀ d, st.dfn = some d → d.gen = g → ∀ k, b.passed k → Covered sp st g b.fn k
  done : b.pc = .activate → ∀ k, b.passed k
  inStep : b.pc = .check ∨ b.pc = .commit → StepInv sp st g b
  live : b.pc = .commit → st.wdef ≤ b.R → ∃ d, st.dfn = some d ∧ d.gen = g

/-- A cleanup of the generation g (point 6): g has its marker; at its end, g
has no entry. -/
structure CInv (st : Stream V F L) (g : Gen) (c : CSt L) : Prop where
  marked : st.mark g = true
  empty : c.pc = .done → ∀ k l, ¬ st.ent g k l

/-- What holds of memory with the stream (020-26, section 3: MemAgrees,
LockSane; and the threads' invariants). -/
structure MInv (sp : Spec V F L) (st : Stream V F L) (m : Mem V F L W) : Prop where
  memAgrees : m.admin = .idle → m.mem = st.dfn
  lockMgr : m.lock = .mgr ↔ m.admin ≠ .idle
  adminCreate : ∀ g fn, m.admin = .create g fn → st.dfn = some ⟨g, fn, false⟩
  adminDelete : ∀ g, m.admin = .delete g → st.dfn = none ∧ st.mark g = true ∧ m.cln g = none
  lockBld : ∀ g, m.lock = .bld g → ∃ b, m.bld g = some b ∧ b.locked = true
  bLocked : ∀ g b, m.bld g = some b → b.locked = true → m.lock = .bld g
  wInv : ∀ w, WInv st (m.wr w)
  bInv : ∀ g b, m.bld g = some b → BInv sp st g b
  bLt : ∀ g b, m.bld g = some b → g < st.now
  cInv : ∀ g c, m.cln g = some c → CInv st g c

/-- The invariant of the system. -/
structure Inv (sp : Spec V F L) (s : Sys V F L W) : Prop where
  sinv : SInv sp s.st
  past : ∀ x ∈ s.past, SInv sp x
  minv : MInv sp s.st s.m

/-! ### Small lemmas -/

theorem sameIdx_refl : ∀ x : Option (Def F), sameIdx x x
  | none => trivial
  | some _ => ⟨rfl, rfl⟩

theorem sameIdx_none {y : Option (Def F)} (h : sameIdx none y) : y = none := by
  cases y with
  | none => rfl
  | some d => exact h.elim

theorem sameIdx_some {d0 : Def F} {y : Option (Def F)} (h : sameIdx (some d0) y) :
    ∃ d, y = some d ∧ d0.gen = d.gen ∧ d0.fn = d.fn := by
  cases y with
  | none => exact h.elim
  | some d => exact ⟨d, rfl, h.1, h.2⟩

theorem Covered.mono {sp : Spec V F L} {st st' : Stream V F L} {g : Gen} {fn : F} {k : Key}
    (h : Covered sp st g fn k) (hd : st'.data k = st.data k)
    (he : ∀ l, st.ent g k l → st'.ent g k l) : Covered sp st' g fn k := by
  intro l hl
  rw [hd] at hl
  exact he l (h l hl)

theorem Covered.of_none {sp : Spec V F L} {st : Stream V F L} {g : Gen} {fn : F} {k : Key}
    (h : sp.f fn k (st.data k) = none) : Covered sp st g fn k := by
  intro l hl
  rw [h] at hl
  cases hl

theorem MInv.adminIdle {sp : Spec V F L} {st : Stream V F L} {m : Mem V F L W}
    (h : MInv sp st m) (hl : m.lock ≠ .mgr) : m.admin = .idle :=
  Classical.byContradiction fun hne => hl (h.lockMgr.mpr hne)

theorem MInv.memEq {sp : Spec V F L} {st : Stream V F L} {m : Mem V F L W}
    (h : MInv sp st m) (hl : m.lock ≠ .mgr) : m.mem = st.dfn :=
  h.memAgrees (h.adminIdle hl)

theorem MInv.notLocked {sp : Spec V F L} {st : Stream V F L} {m : Mem V F L W}
    (h : MInv sp st m) {g : Gen} {b : BSt V F} (hb : m.bld g = some b)
    (hl : m.lock ≠ .bld g) : b.locked = false := by
  cases hlk : b.locked with
  | false => rfl
  | true => exact absurd (h.bLocked g b hb hlk) hl

/-! ### Frames: what a commit keeps of the threads' invariants

A commit writes some keys at the time now + 1; a transaction in flight with
R ≤ now that has one of them in its read set will be refused, and the other
keys keep their values. -/

theorem WInv.frame {st st' : Stream V F L} {x : WSt V F} (h : WInv st x)
    (hnow : st.now ≤ st'.now)
    (hk : ∀ k, (st'.wk k = st.wk k ∧ st'.data k = st.data k) ∨ st.now < st'.wk k)
    (hv : (st'.wv = st.wv ∧ ∀ S, sameIdx S st.dfn → sameIdx S st'.dfn) ∨ st.now < st'.wv) :
    WInv st' x := by
  cases x with
  | idle => trivial
  | set ws nv R old =>
    simp only [WInv] at h ⊢
    obtain ⟨hR, hd⟩ := h
    refine ⟨by omega, fun k hw => ?_⟩
    rcases hk k with ⟨h1, h2⟩ | h1
    · rw [h2]; exact hd k (by omega)
    · omega
  | commit ws nv R old S =>
    simp only [WInv] at h ⊢
    obtain ⟨hR, hd, hS⟩ := h
    refine ⟨by omega, fun k hw => ?_, fun hw => ?_⟩
    · rcases hk k with ⟨h1, h2⟩ | h1
      · rw [h2]; exact hd k (by omega)
      · omega
    · rcases hv with ⟨h1, h2⟩ | h1
      · exact h2 S (hS (by omega))
      · omega

theorem BInv.frame {sp : Spec V F L} {st st' : Stream V F L} {g : Gen} {b : BSt V F}
    (h : BInv sp st g b) (hnow : st.now ≤ st'.now)
    (hk : ∀ k, (st'.wk k = st.wk k ∧ st'.data k = st.data k) ∨ st.now < st'.wk k)
    (hdef : (st'.wdef = st.wdef ∧ st'.dfn = st.dfn) ∨ st.now < st'.wdef)
    (hlive : ∀ d', st'.dfn = some d' → d'.gen = g →
      ∃ d, st.dfn = some d ∧ d.gen = g ∧ d.fn = d'.fn ∧ d.active = d'.active)
    (hcov : ∀ d, st.dfn = some d → d.gen = g → ∀ k,
      Covered sp st g b.fn k → Covered sp st' g b.fn k) :
    BInv sp st' g b := by
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

theorem CInv.frame {st st' : Stream V F L} {g : Gen} {c : CSt L} (h : CInv st g c)
    (hm : st'.mark g = true) (he : ∀ k l, st'.ent g k l → st.ent g k l) : CInv st' g c :=
  ⟨hm, fun hpc k l hkl => h.empty hpc k l (he k l hkl)⟩

/-- Memory kept over a commit that changes neither the definition nor the
markers nor the virtual and definition keys. -/
theorem MInv.frameS {sp : Spec V F L} {st st' : Stream V F L} {m : Mem V F L W}
    (h : MInv sp st m) (hnow : st.now ≤ st'.now)
    (hk : ∀ k, (st'.wk k = st.wk k ∧ st'.data k = st.data k) ∨ st.now < st'.wk k)
    (hdfn : st'.dfn = st.dfn) (hwv : st'.wv = st.wv) (hwdef : st'.wdef = st.wdef)
    (hmark : st'.mark = st.mark)
    (hcov : ∀ d, st.dfn = some d → ∀ k,
      Covered sp st d.gen d.fn k → Covered sp st' d.gen d.fn k)
    (hent : ∀ g k l, st.mark g = true → st'.ent g k l → st.ent g k l) :
    MInv sp st' m := by
  refine ⟨?_, h.lockMgr, ?_, ?_, h.lockBld, h.bLocked, ?_, ?_, ?_, ?_⟩
  · intro hi; rw [hdfn]; exact h.memAgrees hi
  · intro g fn ha; rw [hdfn]; exact h.adminCreate g fn ha
  · intro g ha; rw [hdfn, hmark]; exact h.adminDelete g ha
  · intro w
    exact (h.wInv w).frame hnow hk (Or.inl ⟨hwv, fun S hS => by rw [hdfn]; exact hS⟩)
  · intro g b hb
    have hb' := h.bInv g b hb
    refine hb'.frame hnow hk (Or.inl ⟨hwdef, hdfn⟩) ?_ ?_
    · intro d' hd' hg
      exact ⟨d', by rw [← hdfn]; exact hd', hg, rfl, rfl⟩
    · intro d hd hg k hc
      have hf := (hb'.fnEq d hd hg).1
      have h2 := hcov d hd k (by rw [hf, hg]; exact hc)
      rw [hg, hf] at h2
      exact h2
  · intro g b hb; exact Nat.lt_of_lt_of_le (h.bLt g b hb) hnow
  · intro g c hc
    have hc' := h.cInv g c hc
    exact hc'.frame (by rw [hmark]; exact hc'.marked) (fun k l hkl => hent g k l hc'.marked hkl)

/-! ### Memory changes -/

theorem MInv.setW {sp : Spec V F L} {st : Stream V F L} {m : Mem V F L W} [DecidableEq W]
    (h : MInv sp st m) (w : W) {x : WSt V F} (hx : WInv st x) :
    MInv sp st { m with wr := upd m.wr w x } := by
  refine ⟨h.memAgrees, h.lockMgr, h.adminCreate, h.adminDelete, h.lockBld, h.bLocked, ?_,
    h.bInv, h.bLt, h.cInv⟩
  intro w'
  show WInv st (upd m.wr w x w')
  by_cases hw : w' = w
  · rw [hw, upd_same]; exact hx
  · rw [upd_ne _ _ hw]; exact h.wInv w'

theorem MInv.setB {sp : Spec V F L} {st : Stream V F L} {m : Mem V F L W}
    (h : MInv sp st m) {g : Gen} {b b' : BSt V F} (hb : m.bld g = some b)
    (hb' : BInv sp st g b') (hl : b'.locked = b.locked) :
    MInv sp st { m with bld := upd m.bld g (some b') } := by
  refine ⟨h.memAgrees, h.lockMgr, h.adminCreate, h.adminDelete, ?_, ?_, h.wInv, ?_, ?_, h.cInv⟩
  · intro g' hg'
    obtain ⟨b'', hb'', hl''⟩ := h.lockBld g' hg'
    show ∃ b, upd m.bld g (some b') g' = some b ∧ b.locked = true
    by_cases hgg : g' = g
    · rw [hgg] at hb'' ⊢
      rw [hb] at hb''
      cases hb''
      exact ⟨b', upd_same _ _ _, by rw [hl]; exact hl''⟩
    · rw [upd_ne _ _ hgg]; exact ⟨b'', hb'', hl''⟩
  · intro g' b'' hb'' hl''
    change upd m.bld g (some b') g' = some b'' at hb''
    by_cases hgg : g' = g
    · rw [hgg, upd_same] at hb''
      cases hb''
      rw [hgg]; exact h.bLocked g b hb (by rw [← hl]; exact hl'')
    · rw [upd_ne _ _ hgg] at hb''; exact h.bLocked g' b'' hb'' hl''
  · intro g' b'' hb''
    change upd m.bld g (some b') g' = some b'' at hb''
    by_cases hgg : g' = g
    · rw [hgg, upd_same] at hb''
      cases hb''
      rw [hgg]; exact hb'
    · rw [upd_ne _ _ hgg] at hb''; exact h.bInv g' b'' hb''
  · intro g' b'' hb''
    change upd m.bld g (some b') g' = some b'' at hb''
    by_cases hgg : g' = g
    · rw [hgg]; exact h.bLt g b hb
    · rw [upd_ne _ _ hgg] at hb''; exact h.bLt g' b'' hb''

/-- A build removed, with the lock free or released. -/
theorem MInv.delB {sp : Spec V F L} {st : Stream V F L} {m : Mem V F L W}
    (h : MInv sp st m) {g : Gen} (hl : m.lock = .free ∨ m.lock = .bld g) :
    MInv sp st { m with bld := upd m.bld g none, lock := .free } := by
  have hidle : m.admin = .idle := h.adminIdle (by rcases hl with hl | hl <;> rw [hl] <;> simp)
  refine ⟨h.memAgrees, ?_, h.adminCreate, h.adminDelete, ?_, ?_, h.wInv, ?_, ?_, h.cInv⟩
  · show Lock.free = .mgr ↔ m.admin ≠ .idle
    rw [hidle]; simp
  · intro g' hg'; cases hg'
  · intro g' b'' hb'' hl''
    change upd m.bld g none g' = some b'' at hb''
    by_cases hgg : g' = g
    · rw [hgg, upd_same] at hb''; cases hb''
    · rw [upd_ne _ _ hgg] at hb''
      have h1 := h.bLocked g' b'' hb'' hl''
      rcases hl with hl | hl
      · rw [hl] at h1; cases h1
      · rw [hl] at h1; cases h1; exact absurd rfl hgg
  · intro g' b'' hb''
    change upd m.bld g none g' = some b'' at hb''
    by_cases hgg : g' = g
    · rw [hgg, upd_same] at hb''; cases hb''
    · rw [upd_ne _ _ hgg] at hb''; exact h.bInv g' b'' hb''
  · intro g' b'' hb''
    change upd m.bld g none g' = some b'' at hb''
    by_cases hgg : g' = g
    · rw [hgg, upd_same] at hb''; cases hb''
    · rw [upd_ne _ _ hgg] at hb''; exact h.bLt g' b'' hb''

theorem MInv.setC {sp : Spec V F L} {st : Stream V F L} {m : Mem V F L W}
    (h : MInv sp st m) {g : Gen} {c c' : CSt L} (hc : m.cln g = some c) (hc' : CInv st g c') :
    MInv sp st { m with cln := upd m.cln g (some c') } := by
  refine ⟨h.memAgrees, h.lockMgr, h.adminCreate, ?_, h.lockBld, h.bLocked, h.wInv, h.bInv,
    h.bLt, ?_⟩
  · intro g' ha
    obtain ⟨h1, h2, h3⟩ := h.adminDelete g' ha
    refine ⟨h1, h2, ?_⟩
    show upd m.cln g (some c') g' = none
    by_cases hgg : g' = g
    · rw [hgg] at h3; rw [hc] at h3; cases h3
    · rw [upd_ne _ _ hgg]; exact h3
  · intro g' c'' hc''
    change upd m.cln g (some c') g' = some c'' at hc''
    by_cases hgg : g' = g
    · rw [hgg, upd_same] at hc''; cases hc''; rw [hgg]; exact hc'
    · rw [upd_ne _ _ hgg] at hc''; exact h.cInv g' c'' hc''

/-! ### A start -/

theorem minv_restart {sp : Spec V F L} {st : Stream V F L} (hs : SInv sp st) :
    MInv sp st (restart (W := W) st) := by
  refine ⟨fun _ => rfl, ?_, ?_, ?_, ?_, ?_, fun _ => trivial, ?_, ?_, ?_⟩
  · show Lock.free = .mgr ↔ Admin.idle ≠ (.idle : Admin F)
    simp
  · intro g fn ha; cases ha
  · intro g ha; cases ha
  · intro g hg; cases hg
  · intro g b hb hl
    change (match st.dfn with
      | some d => if d.gen = g ∧ d.active = false then some (BSt.init d.fn) else none
      | none => none) = some b at hb
    cases hd : st.dfn with
    | none => rw [hd] at hb; cases hb
    | some d =>
      rw [hd] at hb
      dsimp only at hb
      split at hb
      · cases hb; cases hl
      · cases hb
  · intro g b hb
    change (match st.dfn with
      | some d => if d.gen = g ∧ d.active = false then some (BSt.init d.fn) else none
      | none => none) = some b at hb
    cases hd : st.dfn with
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
  · intro g b hb
    change (match st.dfn with
      | some d => if d.gen = g ∧ d.active = false then some (BSt.init d.fn) else none
      | none => none) = some b at hb
    cases hd : st.dfn with
    | none => rw [hd] at hb; cases hb
    | some d =>
      rw [hd] at hb
      dsimp only at hb
      split at hb
      · rename_i hc
        rw [← hc.1]; exact hs.gen_lt d hd
      · cases hb
  · intro g c hc
    change (if st.mark g = true then some CSt.init else none) = some c at hc
    split at hc
    · rename_i hm
      cases hc
      exact ⟨hm, fun hpc => by cases hpc⟩
    · cases hc

end BergDB.Index
