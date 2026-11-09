/-
The user indexes of BergDB 2026.4 in Lean: each kind of step keeps the
invariant (bergdb 020-29), and so every reachable system has it.

A step that commits a transaction is stated over any stream st' with the
fields it gives (`e1` to `e8`), so that its proof can rewrite with them.
-/
import BergDB.Index.Inv

namespace BergDB.Index

variable {V F L W : Type}

/-! ### Helpers -/

theorem writeData_yes {data : Key → Option V} {ws : Key → Bool} {nv : Key → Option V}
    {k : Key} (h : ws k = true) : writeData data ws nv k = nv k := by
  simp [writeData, h]

theorem writeData_no {data : Key → Option V} {ws : Key → Bool} {nv : Key → Option V}
    {k : Key} (h : ws k = false) : writeData data ws nv k = data k := by
  simp [writeData, h]

theorem writeTimes_yes {wk : Key → Time} {ws : Key → Bool} {t : Time} {k : Key}
    (h : ws k = true) : writeTimes wk ws t k = t := by
  simp [writeTimes, h]

theorem writeTimes_no {wk : Key → Time} {ws : Key → Bool} {t : Time} {k : Key}
    (h : ws k = false) : writeTimes wk ws t k = wk k := by
  simp [writeTimes, h]

/-- A transaction's writes at the time now + 1: each key is written after
every R, or keeps its value and its time. -/
theorem frame_write (st : Stream V F L) (ws : Key → Bool) (nv : Key → Option V) (k : Key) :
    (writeTimes st.wk ws (st.now + 1) k = st.wk k ∧ writeData st.data ws nv k = st.data k) ∨
      st.now < writeTimes st.wk ws (st.now + 1) k := by
  cases hk : ws k with
  | true => right; rw [writeTimes_yes hk]; omega
  | false => left; exact ⟨writeTimes_no hk, writeData_no hk⟩

/-- A writer's commit with S naming the index: at a key it writes, the
generation's entries become f(new), if they were within f(old). -/
theorem wEntries_at {sp : Spec V F L} {ent : Gen → Key → L → Prop} {d0 : Def F}
    {ws : Key → Bool} {old nv : Key → Option V} {k : Key} (hw : ws k = true)
    (hst : ∀ l, ent d0.gen k l → sp.f d0.fn k (old k) = some l) (l : L) :
    wEntries sp ent (some d0) ws old nv d0.gen k l ↔ sp.f d0.fn k (nv k) = some l := by
  show ((ent d0.gen k l ∧ ¬ (d0.gen = d0.gen ∧ ws k = true ∧ sp.f d0.fn k (old k) = some l)) ∨
      (d0.gen = d0.gen ∧ ws k = true ∧ sp.f d0.fn k (nv k) = some l)) ↔ _
  constructor
  · rintro (⟨h1, h2⟩ | ⟨-, -, h3⟩)
    · exact (h2 ⟨rfl, hw, hst l h1⟩).elim
    · exact h3
  · intro h3; exact Or.inr ⟨rfl, hw, h3⟩

/-- Elsewhere a writer's commit changes no entry. -/
theorem wEntries_other {sp : Spec V F L} {ent : Gen → Key → L → Prop} {d0 : Def F}
    {ws : Key → Bool} {old nv : Key → Option V} {g : Gen} {k : Key}
    (hne : ¬ (g = d0.gen ∧ ws k = true)) (l : L) :
    wEntries sp ent (some d0) ws old nv g k l ↔ ent g k l := by
  show ((ent g k l ∧ ¬ (g = d0.gen ∧ ws k = true ∧ sp.f d0.fn k (old k) = some l)) ∨
      (g = d0.gen ∧ ws k = true ∧ sp.f d0.fn k (nv k) = some l)) ↔ _
  constructor
  · rintro (⟨h1, -⟩ | ⟨h2, h3, -⟩)
    · exact h1
    · exact absurd ⟨h2, h3⟩ hne
  · intro h1; exact Or.inl ⟨h1, fun ⟨h2, h3, _⟩ => hne ⟨h2, h3⟩⟩

theorem Inv.commit {sp : Spec V F L} {s : Sys V F L W} (h : Inv sp s)
    {st' : Stream V F L} {m' : Mem V F L W} (hp : SInv sp st' ∧ MInv sp st' m') :
    Inv sp (s.commit st' m') := by
  refine ⟨hp.1, ?_, hp.2⟩
  intro x hx
  rcases List.mem_cons.mp hx with hx | hx
  · rw [hx]; exact h.sinv
  · exact h.past x hx

theorem Inv.setM {sp : Spec V F L} {s : Sys V F L W} (h : Inv sp s) {m' : Mem V F L W}
    (hm : MInv sp s.st m') : Inv sp { s with m := m' } := ⟨h.sinv, h.past, hm⟩

/-! ### The writers (020-26, section 4, points 1 and 2) -/

/-- `WSuffix`: a key with a suffix has no entry in any index. -/
theorem step_wSuffix {sp : Spec V F L} {st st' : Stream V F L} {m : Mem V F L W}
    (hs : SInv sp st) (hm : MInv sp st m) {ws : Key → Bool} {nv : Key → Option V}
    (hsuf : ∀ k, ws k = true → sp.isObj k = false)
    (e1 : st'.data = writeData st.data ws nv) (e2 : st'.ent = st.ent)
    (e3 : st'.wk = writeTimes st.wk ws (st.now + 1)) (e4 : st'.now = st.now + 1)
    (e5 : st'.dfn = st.dfn) (e6 : st'.mark = st.mark) (e7 : st'.wdef = st.wdef)
    (e8 : st'.wv = st.wv) :
    SInv sp st' ∧ MInv sp st' m := by
  have hk : ∀ k, (st'.wk k = st.wk k ∧ st'.data k = st.data k) ∨ st.now < st'.wk k := by
    intro k; rw [e1, e3]; exact frame_write st ws nv k
  have hcov : ∀ g fn k, Covered sp st g fn k → Covered sp st' g fn k := by
    intro g fn k hc
    cases hkk : ws k with
    | true => exact Covered.of_none (sp.f_suffix _ _ _ (hsuf k hkk))
    | false =>
      exact hc.mono (by rw [e1]; exact writeData_no hkk) (fun l hl => by rw [e2]; exact hl)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro d hd; rw [e5] at hd; rw [e4]; exact Nat.lt_succ_of_lt (hs.gen_lt d hd)
  · intro g hg; rw [e6] at hg; rw [e4]; exact Nat.lt_succ_of_lt (hs.mark_lt g hg)
  · intro d hd k l hkl
    rw [e5] at hd; rw [e2] at hkl
    cases hkk : ws k with
    | true =>
      have := hs.noStale d hd k l hkl
      rw [sp.f_suffix _ _ _ (hsuf k hkk)] at this; cases this
    | false => rw [e1, writeData_no hkk]; exact hs.noStale d hd k l hkl
  · intro d hd ha k; rw [e5] at hd; exact hcov _ _ k (hs.active d hd ha k)
  · intro g k l hl; rw [e5, e6]; rw [e2] at hl; exact hs.accounted g k l hl
  · intro d hd; rw [e5] at hd; rw [e6]; exact hs.markerNotLive d hd
  · exact hm.frameS (by omega) hk e5 e8 e7 e6 (fun d _ k hc => hcov _ _ k hc)
      (fun g k l _ hl => by rw [e2] at hl; exact hl)

/-- `WCommit`: point 1. If S names the index, it is the live one (the virtual
key), and the previous values are the keys' values (the keys written); so the
entries of each key written become exactly f(new). If S is empty, there is no
index. -/
theorem step_wCommit {sp : Spec V F L} {st st' : Stream V F L} {m : Mem V F L W}
    [DecidableEq W] (hs : SInv sp st) (hm : MInv sp st m) {w : W} {ws : Key → Bool}
    {nv : Key → Option V} {R : Time} {old : Key → Option V} {S : Option (Def F)}
    (hw : m.wr w = .commit ws nv R old S) (hv : st.wv ≤ R)
    (hk : S ≠ none → ∀ k, ws k = true → st.wk k ≤ R)
    (e1 : st'.data = writeData st.data ws nv) (e2 : st'.ent = wEntries sp st.ent S ws old nv)
    (e3 : st'.wk = writeTimes st.wk ws (st.now + 1)) (e4 : st'.now = st.now + 1)
    (e5 : st'.dfn = st.dfn) (e6 : st'.mark = st.mark) (e7 : st'.wdef = st.wdef)
    (e8 : st'.wv = st.wv) :
    SInv sp st' ∧ MInv sp st' { m with wr := upd m.wr w .idle } := by
  have hwi := hm.wInv w
  rw [hw] at hwi
  simp only [WInv] at hwi
  obtain ⟨_, hold, hS⟩ := hwi
  have hS' := hS hv
  have hkf : ∀ k, (st'.wk k = st.wk k ∧ st'.data k = st.data k) ∨ st.now < st'.wk k := by
    intro k; rw [e1, e3]; exact frame_write st ws nv k
  have hnow : st.now ≤ st'.now := by omega
  have hgl : ∀ d, st'.dfn = some d → d.gen < st'.now := by
    intro d hd; rw [e5] at hd; rw [e4]; exact Nat.lt_succ_of_lt (hs.gen_lt d hd)
  have hml : ∀ g, st'.mark g = true → g < st'.now := by
    intro g hg; rw [e6] at hg; rw [e4]; exact Nat.lt_succ_of_lt (hs.mark_lt g hg)
  have hmnl : ∀ d, st'.dfn = some d → st'.mark d.gen = false := by
    intro d hd; rw [e5] at hd; rw [e6]; exact hs.markerNotLive d hd
  cases S with
  | none =>
    have hd0 := sameIdx_none hS'
    have hent : st'.ent = st.ent := e2
    refine ⟨⟨hgl, hml, ?_, ?_, ?_, hmnl⟩, ?_⟩
    · intro d hd; rw [e5, hd0] at hd; cases hd
    · intro d hd; rw [e5, hd0] at hd; cases hd
    · intro g k l hl; rw [e5, e6]; rw [hent] at hl; exact hs.accounted g k l hl
    · refine (hm.frameS hnow hkf e5 e8 e7 e6 ?_ ?_).setW w trivial
      · intro d hd; rw [hd0] at hd; cases hd
      · intro g k l _ hl; rw [hent] at hl; exact hl
  | some d0 =>
    obtain ⟨d, hd, hdg, hdf⟩ := sameIdx_some hS'
    have hold' : ∀ k, ws k = true → st.data k = old k :=
      fun k hwk => hold k (hk (by simp) k hwk)
    have hwithin : ∀ k, ws k = true → ∀ l, st.ent d0.gen k l → sp.f d0.fn k (old k) = some l := by
      intro k hwk l hl
      rw [hdg] at hl
      have := hs.noStale d hd k l hl
      rw [hold' k hwk, ← hdf] at this
      exact this
    have hat : ∀ k, ws k = true → ∀ l, (st'.ent d.gen k l ↔ sp.f d.fn k (nv k) = some l) := by
      intro k hwk l; rw [e2, ← hdg, ← hdf]; exact wEntries_at hwk (hwithin k hwk) l
    have hoth : ∀ g k l, ¬ (g = d.gen ∧ ws k = true) → (st'.ent g k l ↔ st.ent g k l) := by
      intro g k l hne; rw [e2]; exact wEntries_other (by rw [hdg]; exact hne) l
    have hnot : ∀ k, ws k = false → ¬ (d.gen = d.gen ∧ ws k = true) := by
      intro k hkk h; rw [hkk] at h; cases h.2
    have hsub : ∀ g k l, st'.ent g k l → st.ent g k l ∨ g = d.gen := by
      intro g k l hl
      by_cases hc : g = d.gen ∧ ws k = true
      · exact Or.inr hc.1
      · exact Or.inl ((hoth g k l hc).mp hl)
    have hcov : ∀ k, Covered sp st d.gen d.fn k → Covered sp st' d.gen d.fn k := by
      intro k hc
      cases hkk : ws k with
      | true =>
        intro l hl
        rw [e1, writeData_yes hkk] at hl
        exact (hat k hkk l).mpr hl
      | false =>
        exact hc.mono (by rw [e1]; exact writeData_no hkk)
          (fun l hl => (hoth d.gen k l (hnot k hkk)).mpr hl)
    refine ⟨⟨hgl, hml, ?_, ?_, ?_, hmnl⟩, ?_⟩
    · intro d' hd' k l hkl
      have hdd : d' = d := by rw [e5, hd] at hd'; exact (Option.some.inj hd').symm
      rw [hdd] at hkl ⊢
      cases hkk : ws k with
      | true => rw [e1, writeData_yes hkk]; exact (hat k hkk l).mp hkl
      | false =>
        rw [e1, writeData_no hkk]
        exact hs.noStale d hd k l ((hoth d.gen k l (hnot k hkk)).mp hkl)
    · intro d' hd' ha k
      have hdd : d' = d := by rw [e5, hd] at hd'; exact (Option.some.inj hd').symm
      rw [hdd] at ha ⊢
      exact hcov k (hs.active d hd ha k)
    · intro g k l hl
      rw [e5, e6]
      rcases hsub g k l hl with hl | hl
      · exact hs.accounted g k l hl
      · exact Or.inl ⟨d, hd, hl.symm⟩
    · refine (hm.frameS hnow hkf e5 e8 e7 e6 ?_ ?_).setW w trivial
      · intro d' hd' k hc
        have hdd : d' = d := by rw [hd] at hd'; exact (Option.some.inj hd').symm
        rw [hdd] at hc ⊢; exact hcov k hc
      · intro g k l hmk hl
        rcases hsub g k l hl with hl | hl
        · exact hl
        · rw [hl, hs.markerNotLive d hd] at hmk; cases hmk

/-! ### The definitions' changes (points 1, 2 and 7) -/

/-- `ACreate`: G is the latest time, after every generation there is (point 7). -/
theorem step_aCreate {sp : Spec V F L} {st st' : Stream V F L} {m : Mem V F L W}
    (hs : SInv sp st) (hm : MInv sp st m) {fn : F}
    (ha : m.admin = .idle) (hl : m.lock = .free) (hmem : m.mem = none)
    (e1 : st'.data = st.data) (e2 : st'.ent = st.ent) (e3 : st'.wk = st.wk)
    (e4 : st'.now = st.now + 1) (e5 : st'.dfn = some ⟨st.now, fn, false⟩)
    (e6 : st'.mark = st.mark) (e7 : st'.wdef = st.now + 1) (e8 : st'.wv = st.now + 1) :
    SInv sp st' ∧ MInv sp st' { m with lock := .mgr, admin := .create st.now fn } := by
  have hd0 : st.dfn = none := by rw [← hm.memAgrees ha]; exact hmem
  have hmk : st.mark st.now = false := by
    cases h : st.mark st.now
    · rfl
    · exact absurd (hs.mark_lt _ h) (Nat.lt_irrefl _)
  have hnoent : ∀ k l, ¬ st.ent st.now k l := by
    intro k l hl
    rcases hs.accounted _ k l hl with ⟨d, hd, _⟩ | h
    · rw [hd0] at hd; cases hd
    · rw [hmk] at h; cases h
  have hnolock : ∀ g b, m.bld g = some b → b.locked = false :=
    fun g b hb => hm.notLocked hb (by rw [hl]; simp)
  have hkf : ∀ k, (st'.wk k = st.wk k ∧ st'.data k = st.data k) ∨ st.now < st'.wk k :=
    fun k => Or.inl ⟨by rw [e3], by rw [e1]⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro d hd; rw [e5] at hd; cases hd; show st.now < st'.now; rw [e4]; exact Nat.lt_succ_self _
  · intro g hg; rw [e6] at hg; rw [e4]; exact Nat.lt_succ_of_lt (hs.mark_lt g hg)
  · intro d hd k l hkl; rw [e5] at hd; cases hd; rw [e2] at hkl; exact absurd hkl (hnoent k l)
  · intro d hd ha'; rw [e5] at hd; cases hd; cases ha'
  · intro g k l hl; rw [e2] at hl; rw [e6]
    rcases hs.accounted g k l hl with ⟨d, hd, _⟩ | h
    · rw [hd0] at hd; cases hd
    · exact Or.inr h
  · intro d hd; rw [e5] at hd; cases hd; rw [e6]; exact hmk
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h; cases h
    · show Lock.mgr = .mgr ↔ Admin.create st.now fn ≠ .idle
      simp
    · intro g fn' h
      change Admin.create st.now fn = Admin.create g fn' at h
      cases h; exact e5
    · intro g h; cases h
    · intro g h; cases h
    · intro g b hb hlk; rw [hnolock g b hb] at hlk; cases hlk
    · intro w
      exact (hm.wInv w).frame (by omega) hkf (Or.inr (by omega))
    · intro g b hb
      have hlt := hm.bLt g b hb
      refine (hm.bInv g b hb).frame (by omega) hkf (Or.inr (by omega)) ?_ ?_
      · intro d' hd' hg; rw [e5] at hd'; cases hd'
        exfalso; change st.now = g at hg; omega
      · intro d hd; rw [hd0] at hd; cases hd
    · intro g b hb; rw [e4]; exact Nat.lt_succ_of_lt (hm.bLt g b hb)
    · intro g c hc
      have hc' := hm.cInv g c hc
      exact hc'.frame (by rw [e6]; exact hc'.marked) (fun k l hkl => by rw [e2] at hkl; exact hkl)

/-- `ADelete`: the live generation gets its marker (point 6). -/
theorem step_aDelete {sp : Spec V F L} {st st' : Stream V F L} {m : Mem V F L W}
    (hs : SInv sp st) (hm : MInv sp st m) {d : Def F}
    (ha : m.admin = .idle) (hl : m.lock = .free) (hmem : m.mem = some d)
    (e1 : st'.data = st.data) (e2 : st'.ent = st.ent) (e3 : st'.wk = st.wk)
    (e4 : st'.now = st.now + 1) (e5 : st'.dfn = none) (e6 : st'.mark = upd st.mark d.gen true)
    (e7 : st'.wdef = st.now + 1) (e8 : st'.wv = st.now + 1) :
    SInv sp st' ∧ MInv sp st' { m with lock := .mgr, admin := .delete d.gen } := by
  have hd : st.dfn = some d := by rw [← hm.memAgrees ha]; exact hmem
  have hnolock : ∀ g b, m.bld g = some b → b.locked = false :=
    fun g b hb => hm.notLocked hb (by rw [hl]; simp)
  have hmk' : ∀ g, st.mark g = true → st'.mark g = true := by
    intro g hg; rw [e6]
    by_cases hgg : g = d.gen
    · rw [hgg, upd_same]
    · rw [upd_ne _ _ hgg]; exact hg
  have hkf : ∀ k, (st'.wk k = st.wk k ∧ st'.data k = st.data k) ∨ st.now < st'.wk k :=
    fun k => Or.inl ⟨by rw [e3], by rw [e1]⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro d' hd'; rw [e5] at hd'; cases hd'
  · intro g hg; rw [e6] at hg; rw [e4]
    by_cases hgg : g = d.gen
    · rw [hgg]; exact Nat.lt_succ_of_lt (hs.gen_lt d hd)
    · rw [upd_ne _ _ hgg] at hg; exact Nat.lt_succ_of_lt (hs.mark_lt g hg)
  · intro d' hd'; rw [e5] at hd'; cases hd'
  · intro d' hd'; rw [e5] at hd'; cases hd'
  · intro g k l hl; rw [e2] at hl
    right
    rcases hs.accounted g k l hl with ⟨d', hd', hg⟩ | h
    · rw [hd] at hd'; cases hd'; rw [e6, ← hg, upd_same]
    · exact hmk' g h
  · intro d' hd'; rw [e5] at hd'; cases hd'
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro h; cases h
    · show Lock.mgr = .mgr ↔ Admin.delete d.gen ≠ (.idle : Admin F)
      simp
    · intro g fn h; cases h
    · intro g h
      change Admin.delete d.gen = Admin.delete g at h
      cases h
      refine ⟨e5, by rw [e6, upd_same], ?_⟩
      show m.cln d.gen = none
      cases hc : m.cln d.gen with
      | none => rfl
      | some c =>
        have := (hm.cInv _ c hc).marked
        rw [hs.markerNotLive d hd] at this; cases this
    · intro g h; cases h
    · intro g b hb hlk; rw [hnolock g b hb] at hlk; cases hlk
    · intro w
      exact (hm.wInv w).frame (by omega) hkf (Or.inr (by omega))
    · intro g b hb
      refine (hm.bInv g b hb).frame (by omega) hkf (Or.inr (by omega)) ?_ ?_
      · intro d' hd'; rw [e5] at hd'; cases hd'
      · intro d' _ _ k hc; exact hc.mono (by rw [e1]) (fun l hl => by rw [e2]; exact hl)
    · intro g b hb; rw [e4]; exact Nat.lt_succ_of_lt (hm.bLt g b hb)
    · intro g c hc
      have hc' := hm.cInv g c hc
      exact hc'.frame (hmk' g hc'.marked) (fun k l hkl => by rw [e2] at hkl; exact hkl)

/-! ### The builds (points 3, 4 and 5) -/

/-- The build after its step's commit. -/
def bAfter (b : BSt V F) : BSt V F :=
  { b with pc := if b.ended = true then .activate else .read, next := b.hi, tries := 0,
           locked := false }

/-- `BCommit`: point 3. The step's generation is live (the definition's key,
after `isLive`), and every value whose entry it puts is its key's value (the
values' keys); the keys it passed are covered. -/
theorem step_bCommit {sp : Spec V F L} {st st' : Stream V F L} {m : Mem V F L W}
    (hs : SInv sp st) (hm : MInv sp st m) {g : Gen} {b : BSt V F}
    (hb : m.bld g = some b) (hpc : b.pc = .commit) (hdef : st.wdef ≤ b.R)
    (hkeys : ∀ k, b.next ≤ k → k < b.hi → sp.f b.fn k (b.snap k) ≠ none → st.wk k ≤ b.R)
    (e1 : st'.data = st.data) (e2 : st'.ent = bEntries sp st.ent g b) (e3 : st'.wk = st.wk)
    (e4 : st'.now = st.now + 1) (e5 : st'.dfn = st.dfn) (e6 : st'.mark = st.mark)
    (e7 : st'.wdef = st.wdef) (e8 : st'.wv = st.wv) :
    SInv sp st' ∧
      MInv sp st' { m with bld := upd m.bld g (some (bAfter b)),
                           lock := if b.locked = true then .free else m.lock } := by
  have hbi := hm.bInv g b hb
  have hsi := hbi.inStep (Or.inr hpc)
  obtain ⟨d, hd, hdg⟩ := hbi.live hpc hdef
  obtain ⟨hfn, hact⟩ := hbi.fnEq d hd hdg
  have hmkg : st.mark g = false := by rw [← hdg]; exact hs.markerNotLive d hd
  have hput : ∀ k l, b.next ≤ k → k < b.hi → sp.f b.fn k (b.snap k) = some l →
      st.data k = b.snap k := by
    intro k l h1 h2 h3
    exact hsi.snap k (hkeys k h1 h2 (by rw [h3]; simp))
  have hsub : ∀ g' k l, st'.ent g' k l → st.ent g' k l ∨
      (g' = g ∧ b.next ≤ k ∧ k < b.hi ∧ sp.f b.fn k (b.snap k) = some l) := by
    intro g' k l hl; rw [e2] at hl; exact hl
  have hsup : ∀ g' k l, st.ent g' k l → st'.ent g' k l := by
    intro g' k l hl; rw [e2]; exact Or.inl hl
  have hmono : ∀ g' fn k, Covered sp st g' fn k → Covered sp st' g' fn k :=
    fun g' fn k hc => hc.mono (by rw [e1]) (fun l hl => hsup _ _ _ hl)
  have hsinv : SInv sp st' := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro d' hd'; rw [e5] at hd'; rw [e4]; exact Nat.lt_succ_of_lt (hs.gen_lt d' hd')
    · intro g' hg'; rw [e6] at hg'; rw [e4]; exact Nat.lt_succ_of_lt (hs.mark_lt g' hg')
    · intro d' hd' k l hkl
      rw [e5] at hd'
      rw [e1]
      rcases hsub _ k l hkl with h | ⟨_, h2, h3, h4⟩
      · exact hs.noStale d' hd' k l h
      · have hdd : d' = d := by rw [hd] at hd'; exact (Option.some.inj hd').symm
        rw [hdd, hput k l h2 h3 h4, hfn]; exact h4
    · intro d' hd' ha k
      have hdd : d' = d := by rw [e5, hd] at hd'; exact (Option.some.inj hd').symm
      rw [hdd, hact] at ha; cases ha
    · intro g' k l hl
      rw [e5, e6]
      rcases hsub g' k l hl with h | ⟨h1, -⟩
      · exact hs.accounted g' k l h
      · exact Or.inl ⟨d, hd, by rw [hdg, h1]⟩
    · intro d' hd'; rw [e5] at hd'; rw [e6]; exact hs.markerNotLive d' hd'
  refine ⟨hsinv, ?_⟩
  have hm1 : MInv sp st' m :=
    hm.frameS (by omega) (fun k => Or.inl ⟨by rw [e3], by rw [e1]⟩) e5 e8 e7 e6
      (fun d' _ k hc => hmono _ _ k hc)
      (fun g' k l hmk hl => by
        rcases hsub g' k l hl with h | ⟨h1, -⟩
        · exact h
        · rw [h1, hmkg] at hmk; cases hmk)
  -- the build after its step
  have hb' : BInv sp st' g (bAfter b) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro d' hd' hg'; rw [e5] at hd'; exact hbi.fnEq d' hd' hg'
    · intro _ _ _ k hk
      rcases hk with hk | ⟨e, he, hek⟩
      · change k < b.hi at hk
        by_cases hkn : k < b.next
        · exact hmono _ _ k (hbi.cover d hd hdg k (Or.inl hkn))
        · cases hf : sp.f b.fn k (b.snap k) with
          | none => exact hmono _ _ k (hsi.noneCov d hd hdg k (by omega) hk hf)
          | some l0 =>
            intro l hl
            change sp.f b.fn k (st'.data k) = some l at hl
            rw [e1, hput k l0 (by omega) hk hf] at hl
            rw [e2]; exact Or.inr ⟨rfl, by omega, hk, hl⟩
      · exact hmono _ _ k (hbi.cover d hd hdg k (Or.inr ⟨e, he, hek⟩))
    · intro hpc' k
      obtain ⟨e, he, hend⟩ := hsi.range
      by_cases hen : b.ended = true
      · have hhi := hend hen
        by_cases hk : k < b.hi
        · exact Or.inl hk
        · exact Or.inr ⟨e, he, by omega⟩
      · change (if b.ended = true then BPc.activate else BPc.read) = .activate at hpc'
        rw [ite_eq_right hen] at hpc'; cases hpc'
    · intro hpc'
      change (if b.ended = true then BPc.activate else BPc.read) = .check ∨
        (if b.ended = true then BPc.activate else BPc.read) = .commit at hpc'
      by_cases hen : b.ended = true
      · rw [ite_eq_left hen] at hpc'; rcases hpc' with h | h <;> cases h
      · rw [ite_eq_right hen] at hpc'; rcases hpc' with h | h <;> cases h
    · intro hpc'
      change (if b.ended = true then BPc.activate else BPc.read) = .commit at hpc'
      by_cases hen : b.ended = true
      · rw [ite_eq_left hen] at hpc'; cases hpc'
      · rw [ite_eq_right hen] at hpc'; cases hpc'
  refine ⟨hm1.memAgrees, ?_, hm1.adminCreate, hm1.adminDelete, ?_, ?_, hm1.wInv, ?_, ?_,
    hm1.cInv⟩
  · show (if b.locked = true then Lock.free else m.lock) = .mgr ↔ m.admin ≠ .idle
    by_cases hlk : b.locked = true
    · rw [ite_eq_left hlk]
      have hl := hm.bLocked g b hb hlk
      have hid := hm.adminIdle (by rw [hl]; simp)
      rw [hid]; simp
    · rw [ite_eq_right hlk]; exact hm.lockMgr
  · intro g' hg'
    change (if b.locked = true then Lock.free else m.lock) = .bld g' at hg'
    show ∃ b'', upd m.bld g (some (bAfter b)) g' = some b'' ∧ b''.locked = true
    by_cases hlk : b.locked = true
    · rw [ite_eq_left hlk] at hg'; cases hg'
    · rw [ite_eq_right hlk] at hg'
      obtain ⟨b'', hb'', hl''⟩ := hm.lockBld g' hg'
      by_cases hgg : g' = g
      · rw [hgg, hb] at hb''; cases hb''; exact absurd hl'' hlk
      · rw [upd_ne _ _ hgg]; exact ⟨b'', hb'', hl''⟩
  · intro g' b'' hb'' hl''
    change upd m.bld g (some (bAfter b)) g' = some b'' at hb''
    show (if b.locked = true then Lock.free else m.lock) = .bld g'
    by_cases hgg : g' = g
    · rw [hgg, upd_same] at hb''; cases hb''; cases hl''
    · rw [upd_ne _ _ hgg] at hb''
      have h1 := hm.bLocked g' b'' hb'' hl''
      by_cases hlk : b.locked = true
      · have h2 := hm.bLocked g b hb hlk
        rw [h1] at h2; cases h2; exact absurd rfl hgg
      · rw [ite_eq_right hlk]; exact h1
  · intro g' b'' hb''
    change upd m.bld g (some (bAfter b)) g' = some b'' at hb''
    by_cases hgg : g' = g
    · rw [hgg, upd_same] at hb''; cases hb''; rw [hgg]; exact hb'
    · rw [upd_ne _ _ hgg] at hb''; exact hm1.bInv g' b'' hb''
  · intro g' b'' hb''
    change upd m.bld g (some (bAfter b)) g' = some b'' at hb''
    by_cases hgg : g' = g
    · rw [hgg]; exact hm1.bLt g b hb
    · rw [upd_ne _ _ hgg] at hb''; exact hm1.bLt g' b'' hb''

/-- `BActivate`: point 5. Every key is passed, so covered: the index is a
function of the data when it becomes active. -/
theorem step_bActivate {sp : Spec V F L} {st st' : Stream V F L} {m : Mem V F L W}
    (hs : SInv sp st) (hm : MInv sp st m) {g : Gen} {b : BSt V F} {d : Def F}
    (hb : m.bld g = some b) (hpc : b.pc = .activate) (hl : m.lock = .free)
    (hmem : m.mem = some d) (hdg : d.gen = g)
    (e1 : st'.data = st.data) (e2 : st'.ent = st.ent) (e3 : st'.wk = st.wk)
    (e4 : st'.now = st.now + 1) (e5 : st'.dfn = some ⟨g, b.fn, true⟩)
    (e6 : st'.mark = st.mark) (e7 : st'.wdef = st.now + 1) (e8 : st'.wv = st.wv) :
    SInv sp st' ∧ MInv sp st' { m with mem := some ⟨g, b.fn, true⟩, bld := upd m.bld g none } := by
  have hid : m.admin = .idle := hm.adminIdle (by rw [hl]; simp)
  have hd : st.dfn = some d := by rw [← hm.memAgrees hid]; exact hmem
  have hbi := hm.bInv g b hb
  obtain ⟨hfn, _⟩ := hbi.fnEq d hd hdg
  have hcovAll : ∀ k, Covered sp st g b.fn k := fun k => hbi.cover d hd hdg k (hbi.done hpc k)
  have hsame : ∀ g' fn k, Covered sp st g' fn k → Covered sp st' g' fn k :=
    fun g' fn k hc => hc.mono (by rw [e1]) (fun l hl => by rw [e2]; exact hl)
  have hnolock : ∀ g' b', m.bld g' = some b' → b'.locked = false :=
    fun g' b' hb' => hm.notLocked hb' (by rw [hl]; simp)
  have hkf : ∀ k, (st'.wk k = st.wk k ∧ st'.data k = st.data k) ∨ st.now < st'.wk k :=
    fun k => Or.inl ⟨by rw [e3], by rw [e1]⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro d' hd'; rw [e5] at hd'; cases hd'
    show g < st'.now; rw [e4, ← hdg]; exact Nat.lt_succ_of_lt (hs.gen_lt d hd)
  · intro g' hg'; rw [e6] at hg'; rw [e4]; exact Nat.lt_succ_of_lt (hs.mark_lt g' hg')
  · intro d' hd' k l hkl; rw [e5] at hd'; cases hd'
    change st'.ent g k l at hkl
    show sp.f b.fn k (st'.data k) = some l
    rw [e2] at hkl; rw [e1]
    have := hs.noStale d hd k l (by rw [hdg]; exact hkl)
    rw [hfn] at this; exact this
  · intro d' hd' _ k; rw [e5] at hd'; cases hd'; exact hsame _ _ k (hcovAll k)
  · intro g' k l hl; rw [e2] at hl; rw [e5, e6]
    rcases hs.accounted g' k l hl with ⟨d', hd', hg'⟩ | h
    · rw [hd] at hd'; cases hd'
      exact Or.inl ⟨⟨g, b.fn, true⟩, rfl, by show g = g'; rw [← hg', hdg]⟩
    · exact Or.inr h
  · intro d' hd'; rw [e5] at hd'; cases hd'; rw [e6]
    show st.mark g = false; rw [← hdg]; exact hs.markerNotLive d hd
  · refine ⟨?_, hm.lockMgr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro _; show some ⟨g, b.fn, true⟩ = st'.dfn; rw [e5]
    · intro g' fn' h; change m.admin = _ at h; rw [hid] at h; cases h
    · intro g' h; change m.admin = _ at h; rw [hid] at h; cases h
    · intro g' h; change m.lock = _ at h; rw [hl] at h; cases h
    · intro g' b' hb' hl'
      change upd m.bld g none g' = some b' at hb'
      by_cases hgg : g' = g
      · rw [hgg, upd_same] at hb'; cases hb'
      · rw [upd_ne _ _ hgg] at hb'; rw [hnolock g' b' hb'] at hl'; cases hl'
    · intro w
      refine (hm.wInv w).frame (by omega) hkf (Or.inl ⟨e8, ?_⟩)
      intro S hS
      rw [e5]; rw [hd] at hS
      cases S with
      | none => exact hS.elim
      | some a => exact ⟨by rw [hS.1, hdg], by rw [hS.2, hfn]⟩
    · intro g' b' hb'
      change upd m.bld g none g' = some b' at hb'
      by_cases hgg : g' = g
      · rw [hgg, upd_same] at hb'; cases hb'
      · rw [upd_ne _ _ hgg] at hb'
        refine (hm.bInv g' b' hb').frame (by omega) hkf (Or.inr (by omega)) ?_ ?_
        · intro d' hd' hg'; rw [e5] at hd'; cases hd'
          exact absurd hg'.symm hgg
        · intro d' _ _ k hc; exact hsame _ _ k hc
    · intro g' b' hb'
      change upd m.bld g none g' = some b' at hb'
      by_cases hgg : g' = g
      · rw [hgg, upd_same] at hb'; cases hb'
      · rw [upd_ne _ _ hgg] at hb'; rw [e4]; exact Nat.lt_succ_of_lt (hm.bLt g' b' hb')
    · intro g' c hc
      have hc' := hm.cInv g' c hc
      exact hc'.frame (by rw [e6]; exact hc'.marked) (fun k l hkl => by rw [e2] at hkl; exact hkl)

/-! ### The cleanups (points 6 and 9) -/

/-- `CDel`: a cleanup deletes entries of a generation with a marker, never the
live one's. -/
theorem step_cDel {sp : Spec V F L} {st st' : Stream V F L} {m : Mem V F L W}
    (hs : SInv sp st) (hm : MInv sp st m) {g : Gen} {c : CSt L}
    (hc : m.cln g = some c)
    (e1 : st'.data = st.data)
    (e2 : st'.ent = fun g' k l => st.ent g' k l ∧ ¬ (g' = g ∧ c.keys k l))
    (e3 : st'.wk = st.wk) (e4 : st'.now = st.now + 1) (e5 : st'.dfn = st.dfn)
    (e6 : st'.mark = st.mark) (e7 : st'.wdef = st.wdef) (e8 : st'.wv = st.wv) :
    SInv sp st' ∧ MInv sp st' { m with cln := upd m.cln g (some { c with pc := .scan }) } := by
  have hci := hm.cInv g c hc
  have hsub : ∀ g' k l, st'.ent g' k l → st.ent g' k l := by
    intro g' k l hl; rw [e2] at hl; exact hl.1
  have hlivecov : ∀ d, st.dfn = some d → ∀ k,
      Covered sp st d.gen d.fn k → Covered sp st' d.gen d.fn k := by
    intro d hd k hcv
    have hne : d.gen ≠ g := by
      intro h; have := hs.markerNotLive d hd; rw [h, hci.marked] at this; cases this
    refine hcv.mono (by rw [e1]) (fun l hl => ?_)
    rw [e2]; exact ⟨hl, fun h => hne h.1⟩
  have hsinv : SInv sp st' := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro d hd; rw [e5] at hd; rw [e4]; exact Nat.lt_succ_of_lt (hs.gen_lt d hd)
    · intro g' hg'; rw [e6] at hg'; rw [e4]; exact Nat.lt_succ_of_lt (hs.mark_lt g' hg')
    · intro d hd k l hkl; rw [e5] at hd; rw [e1]; exact hs.noStale d hd k l (hsub _ k l hkl)
    · intro d hd ha k; rw [e5] at hd; exact hlivecov d hd k (hs.active d hd ha k)
    · intro g' k l hl; rw [e5, e6]; exact hs.accounted g' k l (hsub _ k l hl)
    · intro d hd; rw [e5] at hd; rw [e6]; exact hs.markerNotLive d hd
  refine ⟨hsinv, ?_⟩
  have hm1 : MInv sp st' m :=
    hm.frameS (by omega) (fun k => Or.inl ⟨by rw [e3], by rw [e1]⟩) e5 e8 e7 e6
      hlivecov (fun g' k l _ hl => hsub g' k l hl)
  exact hm1.setC hc ⟨by rw [e6]; exact hci.marked, fun h => by cases h⟩

/-- `CEnd`: the marker is deleted when its generation has no entry left; no
later step puts one (points 2 and 3). -/
theorem step_cEnd {sp : Spec V F L} {st st' : Stream V F L} {m : Mem V F L W}
    (hs : SInv sp st) (hm : MInv sp st m) {g : Gen} {c : CSt L}
    (hc : m.cln g = some c) (hpc : c.pc = .done)
    (e1 : st'.data = st.data) (e2 : st'.ent = st.ent)
    (e3 : st'.wk = st.wk) (e4 : st'.now = st.now + 1) (e5 : st'.dfn = st.dfn)
    (e6 : st'.mark = upd st.mark g false) (e7 : st'.wdef = st.wdef) (e8 : st'.wv = st.wv) :
    SInv sp st' ∧ MInv sp st' { m with cln := upd m.cln g none } := by
  have hci := hm.cInv g c hc
  have hempty := hci.empty hpc
  have hmk : ∀ g', g' ≠ g → st'.mark g' = st.mark g' := by
    intro g' hg'; rw [e6]; exact upd_ne _ _ hg'
  have hsinv : SInv sp st' := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro d hd; rw [e5] at hd; rw [e4]; exact Nat.lt_succ_of_lt (hs.gen_lt d hd)
    · intro g' hg'; rw [e4]
      by_cases hgg : g' = g
      · rw [hgg, e6, upd_same] at hg'; cases hg'
      · rw [hmk g' hgg] at hg'; exact Nat.lt_succ_of_lt (hs.mark_lt g' hg')
    · intro d hd k l hkl; rw [e5] at hd; rw [e2] at hkl; rw [e1]; exact hs.noStale d hd k l hkl
    · intro d hd ha k; rw [e5] at hd
      exact (hs.active d hd ha k).mono (by rw [e1]) (fun l hl => by rw [e2]; exact hl)
    · intro g' k l hl; rw [e2] at hl; rw [e5]
      rcases hs.accounted g' k l hl with h | h
      · exact Or.inl h
      · right
        by_cases hgg : g' = g
        · rw [hgg] at hl; exact absurd hl (hempty k l)
        · rw [hmk g' hgg]; exact h
    · intro d hd; rw [e5] at hd
      by_cases hgg : d.gen = g
      · rw [hgg, e6, upd_same]
      · rw [hmk _ hgg]; exact hs.markerNotLive d hd
  refine ⟨hsinv, ?_⟩
  have hkf : ∀ k, (st'.wk k = st.wk k ∧ st'.data k = st.data k) ∨ st.now < st'.wk k :=
    fun k => Or.inl ⟨by rw [e3], by rw [e1]⟩
  refine ⟨?_, hm.lockMgr, ?_, ?_, hm.lockBld, hm.bLocked, ?_, ?_, ?_, ?_⟩
  · intro h; rw [e5]; exact hm.memAgrees h
  · intro g' fn h; rw [e5]; exact hm.adminCreate g' fn h
  · intro g' h
    obtain ⟨h1, h2, h3⟩ := hm.adminDelete g' h
    have hgg : g' ≠ g := by intro he; rw [he, hc] at h3; cases h3
    refine ⟨by rw [e5]; exact h1, by rw [hmk g' hgg]; exact h2, ?_⟩
    show upd m.cln g none g' = none
    rw [upd_ne _ _ hgg]; exact h3
  · intro w
    exact (hm.wInv w).frame (by omega) hkf (Or.inl ⟨e8, fun S hS => by rw [e5]; exact hS⟩)
  · intro g' b hb
    refine (hm.bInv g' b hb).frame (by omega) hkf (Or.inl ⟨e7, e5⟩) ?_ ?_
    · intro d' hd' hg; exact ⟨d', by rw [← e5]; exact hd', hg, rfl, rfl⟩
    · intro d _ _ k hcv; exact hcv.mono (by rw [e1]) (fun l hl => by rw [e2]; exact hl)
  · intro g' b hb; rw [e4]; exact Nat.lt_succ_of_lt (hm.bLt g' b hb)
  · intro g' c' hc'
    change upd m.cln g none g' = some c' at hc'
    by_cases hgg : g' = g
    · rw [hgg, upd_same] at hc'; cases hc'
    · rw [upd_ne _ _ hgg] at hc'
      have hci' := hm.cInv g' c' hc'
      exact ⟨by rw [hmk g' hgg]; exact hci'.marked,
        fun hp k l hl => hci'.empty hp k l (by rw [e2] at hl; exact hl)⟩

/-! ### Steps of memory only -/

theorem minv_wStart {sp : Spec V F L} {st : Stream V F L} {m : Mem V F L W} [DecidableEq W]
    (hm : MInv sp st m) (w : W) (ws : Key → Bool) (nv : Key → Option V) :
    MInv sp st { m with wr := upd m.wr w (.set ws nv st.now st.data) } :=
  hm.setW w (show st.now ≤ st.now ∧ ∀ k, st.wk k ≤ st.now → st.data k = st.data k from
    ⟨Nat.le_refl _, fun _ _ => rfl⟩)

/-- `WReadS`: under the lock, no definition change is under way, so the maps
are the stream's definition. -/
theorem minv_wReadS {sp : Spec V F L} {st : Stream V F L} {m : Mem V F L W} [DecidableEq W]
    (hm : MInv sp st m) {w : W} {ws : Key → Bool} {nv : Key → Option V} {R : Time}
    {old : Key → Option V} (hw : m.wr w = .set ws nv R old) (hl : m.lock = .free) :
    MInv sp st { m with wr := upd m.wr w (.commit ws nv R old m.mem) } := by
  have hwi := hm.wInv w
  rw [hw] at hwi
  simp only [WInv] at hwi
  obtain ⟨h1, h2⟩ := hwi
  apply hm.setW w
  show R ≤ st.now ∧ (∀ k, st.wk k ≤ R → st.data k = old k) ∧
    (st.wv ≤ R → sameIdx m.mem st.dfn)
  refine ⟨h1, h2, fun _ => ?_⟩
  rw [hm.memEq (by rw [hl]; simp)]; exact sameIdx_refl _

theorem minv_aCreateMap {sp : Spec V F L} {st : Stream V F L} {m : Mem V F L W}
    (hs : SInv sp st) (hm : MInv sp st m) {g : Gen} {fn : F} (ha : m.admin = .create g fn) :
    MInv sp st { m with mem := st.dfn, lock := .free, admin := .idle,
                        bld := upd m.bld g (some (BSt.init fn)) } := by
  have hd := hm.adminCreate g fn ha
  have hlk : m.lock = .mgr := hm.lockMgr.mpr (by rw [ha]; simp)
  refine ⟨fun _ => rfl, ?_, ?_, ?_, ?_, ?_, hm.wInv, ?_, ?_, hm.cInv⟩
  · show Lock.free = .mgr ↔ (Admin.idle : Admin F) ≠ .idle; simp
  · intro g' fn' h; cases h
  · intro g' h; cases h
  · intro g' h; cases h
  · intro g' b hb hl
    change upd m.bld g (some (BSt.init fn)) g' = some b at hb
    by_cases hgg : g' = g
    · rw [hgg, upd_same] at hb; cases hb; cases hl
    · rw [upd_ne _ _ hgg] at hb
      have := hm.bLocked g' b hb hl; rw [hlk] at this; cases this
  · intro g' b hb
    change upd m.bld g (some (BSt.init fn)) g' = some b at hb
    by_cases hgg : g' = g
    · rw [hgg, upd_same] at hb; cases hb; rw [hgg]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro d hd' _; rw [hd] at hd'; cases hd'; exact ⟨rfl, rfl⟩
      · intro d _ _ k hk
        rcases hk with hk | ⟨e, he, _⟩
        · exact absurd hk (Nat.not_lt_zero k)
        · cases he
      · intro h; cases h
      · intro h; rcases h with h | h <;> cases h
      · intro h; cases h
    · rw [upd_ne _ _ hgg] at hb; exact hm.bInv g' b hb
  · intro g' b hb
    change upd m.bld g (some (BSt.init fn)) g' = some b at hb
    by_cases hgg : g' = g
    · rw [hgg]; exact hs.gen_lt _ hd
    · rw [upd_ne _ _ hgg] at hb; exact hm.bLt g' b hb

theorem minv_aDeleteMap {sp : Spec V F L} {st : Stream V F L} {m : Mem V F L W}
    (hm : MInv sp st m) {g : Gen} (ha : m.admin = .delete g) :
    MInv sp st { m with mem := none, lock := .free, admin := .idle,
                        cln := upd m.cln g (some CSt.init) } := by
  obtain ⟨hd, hmk, _⟩ := hm.adminDelete g ha
  have hlk : m.lock = .mgr := hm.lockMgr.mpr (by rw [ha]; simp)
  refine ⟨fun _ => hd.symm, ?_, ?_, ?_, ?_, ?_, hm.wInv, hm.bInv, hm.bLt, ?_⟩
  · show Lock.free = .mgr ↔ (Admin.idle : Admin F) ≠ .idle; simp
  · intro g' fn' h; cases h
  · intro g' h; cases h
  · intro g' h; cases h
  · intro g' b hb hl; have := hm.bLocked g' b hb hl; rw [hlk] at this; cases this
  · intro g' c hc
    change upd m.cln g (some CSt.init) g' = some c at hc
    by_cases hgg : g' = g
    · rw [hgg, upd_same] at hc; cases hc; rw [hgg]; exact ⟨hmk, fun h => by cases h⟩
    · rw [upd_ne _ _ hgg] at hc; exact hm.cInv g' c hc

/-- `BReadE`: the keys after E have no value, so they are covered (point 4). -/
theorem minv_bReadE {sp : Spec V F L} {st : Stream V F L} {m : Mem V F L W}
    (hm : MInv sp st m) {g : Gen} {b : BSt V F} {e : Key} (hb : m.bld g = some b)
    (hE : ∀ k, e < k → st.data k = none) :
    MInv sp st { m with bld := upd m.bld g (some { b with E := some e, pc := .read }) } := by
  have hbi := hm.bInv g b hb
  refine hm.setB hb ⟨hbi.fnEq, ?_, ?_, ?_, ?_⟩ rfl
  · intro d hd hg k hk
    rcases hk with hk | ⟨e', he', hek⟩
    · exact hbi.cover d hd hg k (Or.inl hk)
    · cases he'
      exact Covered.of_none (by rw [hE k hek]; exact sp.f_none _ _)
  · intro h; cases h
  · intro h; rcases h with h | h <;> cases h
  · intro h; cases h

/-- `BRead`: the step's values are the data at its R. -/
theorem minv_bRead {sp : Spec V F L} {st : Stream V F L} {m : Mem V F L W}
    (hm : MInv sp st m) {g : Gen} {b : BSt V F} {e hi : Key} (hb : m.bld g = some b)
    (hE : b.E = some e) :
    MInv sp st { m with bld := upd m.bld g (some
        { b with hi := hi, R := st.now, snap := st.data, ended := decide (hi = e + 1),
                 pc := .check }) } := by
  have hbi := hm.bInv g b hb
  refine hm.setB hb ⟨hbi.fnEq, hbi.cover, ?_, ?_, ?_⟩ rfl
  · intro h; cases h
  · intro _
    refine ⟨Nat.le_refl _, fun _ _ => rfl, ⟨e, hE, fun h => of_decide_eq_true h⟩, ?_⟩
    intro _ _ _ k _ _ hf
    exact Covered.of_none hf
  · intro h; cases h

/-- `BCheck`: `isLive` under the lock reads the stream's definition. -/
theorem minv_bCheck {sp : Spec V F L} {st : Stream V F L} {m : Mem V F L W}
    (hm : MInv sp st m) {g : Gen} {b : BSt V F} {d : Def F} (hb : m.bld g = some b)
    (hpc : b.pc = .check) (hl : m.lock = .free ∨ m.lock = .bld g) (hmem : m.mem = some d)
    (hdg : d.gen = g) :
    MInv sp st { m with bld := upd m.bld g (some { b with pc := .commit }) } := by
  have hbi := hm.bInv g b hb
  have hd : st.dfn = some d := by
    rw [← hm.memEq (by rcases hl with hl | hl <;> rw [hl] <;> simp)]; exact hmem
  refine hm.setB hb ⟨hbi.fnEq, hbi.cover, ?_, ?_, ?_⟩ rfl
  · intro h; cases h
  · intro _
    have hsi := hbi.inStep (Or.inl hpc)
    exact ⟨hsi.R_le, hsi.snap, hsi.range, hsi.noneCov⟩
  · intro _ _; exact ⟨d, hd, hdg⟩

theorem minv_bRefused {sp : Spec V F L} {st : Stream V F L} {m : Mem V F L W}
    (hm : MInv sp st m) {g : Gen} {b : BSt V F} (hb : m.bld g = some b) :
    MInv sp st { m with bld := upd m.bld g (some
        { b with pc := if b.locked = false ∧ sp.lockedAfter ≤ b.tries + 1 then .lock else .read,
                 tries := if b.locked = true ∨ sp.lockedAfter ≤ b.tries + 1 then 0
                          else b.tries + 1 }) } := by
  have hbi := hm.bInv g b hb
  refine hm.setB hb ⟨hbi.fnEq, hbi.cover, ?_, ?_, ?_⟩ rfl
  · intro h; dsimp only at h; split at h <;> cases h
  · intro h; dsimp only at h; rcases h with h | h <;> (split at h <;> cases h)
  · intro h; dsimp only at h; split at h <;> cases h

theorem minv_bLock {sp : Spec V F L} {st : Stream V F L} {m : Mem V F L W}
    (hm : MInv sp st m) {g : Gen} {b : BSt V F} (hb : m.bld g = some b)
    (hl : m.lock = .free) :
    MInv sp st { m with lock := .bld g,
                        bld := upd m.bld g (some { b with locked := true, pc := .read }) } := by
  have hbi := hm.bInv g b hb
  have hid : m.admin = .idle := hm.adminIdle (by rw [hl]; simp)
  refine ⟨hm.memAgrees, ?_, hm.adminCreate, hm.adminDelete, ?_, ?_, hm.wInv, ?_, ?_, hm.cInv⟩
  · show Lock.bld g = .mgr ↔ m.admin ≠ .idle
    rw [hid]; simp
  · intro g' hg'
    change Lock.bld g = Lock.bld g' at hg'
    cases hg'
    exact ⟨_, upd_same _ _ _, rfl⟩
  · intro g' b' hb' hl'
    change upd m.bld g (some { b with locked := true, pc := .read }) g' = some b' at hb'
    show Lock.bld g = Lock.bld g'
    by_cases hgg : g' = g
    · rw [hgg]
    · rw [upd_ne _ _ hgg] at hb'
      have := hm.bLocked g' b' hb' hl'; rw [hl] at this; cases this
  · intro g' b' hb'
    change upd m.bld g (some { b with locked := true, pc := .read }) g' = some b' at hb'
    by_cases hgg : g' = g
    · rw [hgg, upd_same] at hb'; cases hb'; rw [hgg]
      refine ⟨hbi.fnEq, hbi.cover, ?_, ?_, ?_⟩
      · intro h; cases h
      · intro h; rcases h with h | h <;> cases h
      · intro h; cases h
    · rw [upd_ne _ _ hgg] at hb'; exact hm.bInv g' b' hb'
  · intro g' b' hb'
    change upd m.bld g (some { b with locked := true, pc := .read }) g' = some b' at hb'
    by_cases hgg : g' = g
    · rw [hgg]; exact hm.bLt g b hb
    · rw [upd_ne _ _ hgg] at hb'; exact hm.bLt g' b' hb'

theorem minv_bActivateFail {sp : Spec V F L} {st : Stream V F L} {m : Mem V F L W}
    (hm : MInv sp st m) {g : Gen} (hl : m.lock = .free) :
    MInv sp st { m with bld := upd m.bld g none } := by
  have e : ({ m with bld := upd m.bld g none } : Mem V F L W) =
      { m with bld := upd m.bld g none, lock := .free } := by
    cases m; dsimp only at hl ⊢; rw [hl]
  rw [e]; exact hm.delB (Or.inl hl)

theorem minv_cScan {sp : Spec V F L} {st : Stream V F L} {m : Mem V F L W}
    (hm : MInv sp st m) {g : Gen} {c : CSt L} {keys : Key → L → Prop} (hc : m.cln g = some c) :
    MInv sp st { m with cln := upd m.cln g (some { c with pc := .del, keys := keys }) } :=
  hm.setC hc ⟨(hm.cInv g c hc).marked, fun h => by cases h⟩

/-- `CScan` that finds no entry: the cleanup's end (point 6). -/
theorem minv_cScanEnd {sp : Spec V F L} {st : Stream V F L} {m : Mem V F L W}
    (hm : MInv sp st m) {g : Gen} {c : CSt L} (hc : m.cln g = some c)
    (hno : ∀ k l, ¬ st.ent g k l) :
    MInv sp st { m with cln := upd m.cln g (some { c with pc := .done }) } :=
  hm.setC hc ⟨(hm.cInv g c hc).marked, fun _ => hno⟩

/-! ### Crashes, the start, and the induction -/

theorem inv_crash {sp : Spec V F L} {s : Sys V F L W} (h : Inv sp s)
    {pre : List (Stream V F L)} {x : Stream V F L} {rest : List (Stream V F L)}
    (he : s.st :: s.past = pre ++ x :: rest) : Inv sp (⟨x, rest, restart x⟩ : Sys V F L W) := by
  have hall : ∀ y ∈ s.st :: s.past, SInv sp y := by
    intro y hy
    rcases List.mem_cons.mp hy with hy | hy
    · rw [hy]; exact h.sinv
    · exact h.past y hy
  have hx : SInv sp x := hall x (by rw [he]; simp)
  refine ⟨hx, fun y hy => hall y ?_, minv_restart hx⟩
  rw [he]; simp [hy]

theorem inv_init (sp : Spec V F L) (d0 : Key → Option V) : Inv sp (Sys.init (W := W) d0) := by
  have hs : SInv sp (Stream.init (F := F) (L := L) d0) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro d hd; cases hd
    · intro g hg; cases hg
    · intro d hd; cases hd
    · intro d hd; cases hd
    · intro g k l hl; exact hl.elim
    · intro d hd; cases hd
  refine ⟨hs, ?_, minv_restart hs⟩
  intro _ h; cases h

variable [DecidableEq W]

/-- Every step keeps the invariant. -/
theorem inv_step {sp : Spec V F L} {s s' : Sys V F L W} (h : Inv sp s) (hst : Step sp s s') :
    Inv sp s' := by
  cases hst with
  | wSuffix ws nv hsuf =>
    exact h.commit (step_wSuffix h.sinv h.minv hsuf rfl rfl rfl rfl rfl rfl rfl rfl)
  | wStart w ws nv _ => exact h.setM (minv_wStart h.minv w ws nv)
  | wReadS w ws nv R old hw hl => exact h.setM (minv_wReadS h.minv hw hl)
  | wCommit w ws nv R old S hw hv hk =>
    exact h.commit (step_wCommit h.sinv h.minv hw hv hk rfl rfl rfl rfl rfl rfl rfl rfl)
  | wDrop w => exact h.setM (h.minv.setW w trivial)
  | aCreate fn ha hl hmem =>
    exact h.commit (step_aCreate h.sinv h.minv ha hl hmem rfl rfl rfl rfl rfl rfl rfl rfl)
  | aCreateMap g fn ha => exact h.setM (minv_aCreateMap h.sinv h.minv ha)
  | aDelete d ha hl hmem =>
    exact h.commit (step_aDelete h.sinv h.minv ha hl hmem rfl rfl rfl rfl rfl rfl rfl rfl)
  | aDeleteMap g ha => exact h.setM (minv_aDeleteMap h.minv ha)
  | bReadE g b e hb _ hE => exact h.setM (minv_bReadE h.minv hb hE)
  | bRead g b e hi hb _ hE _ _ => exact h.setM (minv_bRead h.minv hb hE)
  | bCheck g b d hb hpc hl hmem hdg => exact h.setM (minv_bCheck h.minv hb hpc hl hmem hdg)
  | bCheckFail g b _ _ hl _ => exact h.setM (h.minv.delB hl)
  | bCommit g b hb hpc hdef hkeys =>
    exact h.commit (step_bCommit h.sinv h.minv hb hpc hdef hkeys rfl rfl rfl rfl rfl rfl rfl rfl)
  | bRefused g b hb _ _ => exact h.setM (minv_bRefused h.minv hb)
  | bLock g b hb _ hl => exact h.setM (minv_bLock h.minv hb hl)
  | bActivate g b d hb hpc hl hmem hdg =>
    exact h.commit (step_bActivate h.sinv h.minv hb hpc hl hmem hdg rfl rfl rfl rfl rfl rfl rfl rfl)
  | bActivateFail g b _ _ hl _ => exact h.setM (minv_bActivateFail h.minv hl)
  | cScan g c keys hc _ => exact h.setM (minv_cScan h.minv hc)
  | cScanEnd g c hc _ hno => exact h.setM (minv_cScanEnd h.minv hc hno)
  | cDel g c hc _ =>
    exact h.commit (step_cDel h.sinv h.minv hc rfl rfl rfl rfl rfl rfl rfl rfl)
  | cEnd g c hc hpc =>
    exact h.commit (step_cEnd h.sinv h.minv hc hpc rfl rfl rfl rfl rfl rfl rfl rfl)
  | crash pre x rest he => exact inv_crash h he

/-- Every reachable system has the invariant. -/
theorem reach_inv {sp : Spec V F L} {s : Sys V F L W} (h : Reach sp s) : Inv sp s := by
  induction h with
  | init d0 => exact inv_init sp d0
  | step _ hst ih => exact inv_step ih hst

end BergDB.Index
