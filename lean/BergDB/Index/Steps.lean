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

theorem idxAt_no {ws : Key → Bool} {S : Key → Option (Name → Option (Def F))} {k : Key}
    {n : Name} (h : ws k = false) : idxAt ws S k n = none := by
  simp [idxAt, h]

theorem idxAt_yes {ws : Key → Bool} {S : Key → Option (Name → Option (Def F))} {k : Key}
    {n : Name} {m : Name → Option (Def F)} (h : ws k = true) (hm : S k = some m) :
    idxAt ws S k n = m n := by
  simp [idxAt, h, hm]

theorem wEntries_none {sp : Spec V F L} {ent : Name → Gen → Key → L → Prop}
    {ws : Key → Bool} {S : Key → Option (Name → Option (Def F))} {old nv : Key → Option V}
    {n : Name} {g : Gen} {k : Key} {l : L} (h : idxAt ws S k n = none) :
    wEntries sp ent ws S old nv n g k l ↔ ent n g k l := by
  simp only [wEntries, h]

theorem wEntries_some {sp : Spec V F L} {ent : Name → Gen → Key → L → Prop}
    {ws : Key → Bool} {S : Key → Option (Name → Option (Def F))} {old nv : Key → Option V}
    {n : Name} {g : Gen} {k : Key} {l : L} {a : Def F} (h : idxAt ws S k n = some a) :
    wEntries sp ent ws S old nv n g k l ↔
      ((ent n g k l ∧ ¬ (g = a.gen ∧ sp.f a.fn k (old k) = some l)) ∨
        (g = a.gen ∧ sp.f a.fn k (nv k) = some l)) := by
  simp only [wEntries, h]

/-- A function with an entry at k is of k's directory. -/
theorem dir_of_some {sp : Spec V F L} {fn : F} {k : Key} {v : Option V} {l : L}
    (h : sp.f fn k v = some l) : sp.dirF fn = sp.dirOf k :=
  Classical.byContradiction fun hne => by
    rw [sp.f_dir _ _ _ (fun h' => hne h'.symm)] at h; cases h

theorem sameOn_congr {sp : Spec V F L} {dir : Dir} {x : Option (Def F)} {d d' : Def F}
    (hg : d'.gen = d.gen) (hf : d'.fn = d.fn) (h : sameOn sp dir x (some d)) :
    sameOn sp dir x (some d') := by
  cases x with
  | none => show sp.dirF d'.fn ≠ dir; rw [hf]; exact h
  | some a =>
    intro hr
    rw [hg, hf]
    exact h (by rw [← hf]; exact hr)

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
  have hcov : ∀ n g fn k, Covered sp st n g fn k → Covered sp st' n g fn k := by
    intro n g fn k hc
    cases hkk : ws k with
    | true => exact Covered.of_none (sp.f_suffix _ _ _ (hsuf k hkk))
    | false =>
      exact hc.mono (by rw [e1]; exact writeData_no hkk) (fun l hl => by rw [e2]; exact hl)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro n d hd; rw [e5] at hd; rw [e4]; exact Nat.le_succ_of_le (hs.gen_le n d hd)
  · intro n g hg; rw [e6] at hg; rw [e4]; exact Nat.lt_succ_of_lt (hs.mark_lt n g hg)
  · intro n d hd k l hkl
    rw [e5] at hd; rw [e2] at hkl
    cases hkk : ws k with
    | true =>
      have := hs.noStale n d hd k l hkl
      rw [sp.f_suffix _ _ _ (hsuf k hkk)] at this; cases this
    | false => rw [e1, writeData_no hkk]; exact hs.noStale n d hd k l hkl
  · intro n d hd ha k; rw [e5] at hd; exact hcov _ _ _ k (hs.active n d hd ha k)
  · intro n g k l hl; rw [e5, e6]; rw [e2] at hl; exact hs.accounted n g k l hl
  · intro n d hd; rw [e5] at hd; rw [e6]; exact hs.markerNotLive n d hd
  · exact hm.frameS (by omega) hk e5 e8 e7 e6 (fun n d _ k hc => hcov _ _ _ k hc)
      (fun n g k l _ hl => by rw [e2] at hl; exact hl)

section wcommit

variable {sp : Spec V F L} {st : Stream V F L} {ws : Key → Bool} {nv old : Key → Option V}
  {R : Time} {S : Key → Option (Name → Option (Def F))}

/-- A writer's commit puts an entry only where an index of the set it read
gives one. -/
theorem wcommit_new {ent : Name → Gen → Key → L → Prop} {n : Name} {g : Gen} {k : Key} {l : L}
    (h : wEntries sp ent ws S old nv n g k l) :
    ent n g k l ∨ ∃ a, idxAt ws S k n = some a ∧ g = a.gen ∧ sp.f a.fn k (nv k) = some l := by
  cases hi : idxAt ws S k n with
  | none => exact Or.inl ((wEntries_none hi).mp h)
  | some a =>
    rcases (wEntries_some hi).mp h with ⟨h1, _⟩ | ⟨h2, h3⟩
    · exact Or.inl h1
    · exact Or.inr ⟨a, rfl, h2, h3⟩

/-- Point 1, per name: at a key that a writer writes, a live index's entries
become exactly f(new). If the index is of the key's directory, the set read
for the key has it (the virtual key) and the previous value is the key's value
(the key); if not, f has no entry at the key, and the set read has no index of
the name that gives one. -/
theorem wcommit_exact (hs : SInv sp st) (hold : ∀ k, st.wk k ≤ R → st.data k = old k)
    (hS : ∀ k m, S k = some m → st.wv (sp.dirOf k) ≤ R →
      ∀ n, sameOn sp (sp.dirOf k) (m n) (st.dfn n))
    (hc : ∀ k, ws k = true → sp.isObj k = true → ∃ m, S k = some m ∧
      st.wv (sp.dirOf k) ≤ R ∧ (hasIdx sp m (sp.dirOf k) → st.wk k ≤ R))
    {n : Name} {d : Def F} (hd : st.dfn n = some d) {k : Key} (hk : ws k = true) (l : L) :
    wEntries sp st.ent ws S old nv n d.gen k l ↔ sp.f d.fn k (nv k) = some l := by
  cases hob : sp.isObj k with
  | false =>
    -- a key with a suffix: no index has an entry there, before or after
    rw [sp.f_suffix _ _ _ hob]
    constructor
    · intro h
      exfalso
      rcases wcommit_new h with h1 | ⟨a, _, _, h3⟩
      · have := hs.noStale n d hd k l h1; rw [sp.f_suffix _ _ _ hob] at this; cases this
      · rw [sp.f_suffix _ _ _ hob] at h3; cases h3
    · intro h; cases h
  | true =>
      obtain ⟨m, hm, hv, hidx⟩ := hc k hk hob
      have hsame := hS k m hm hv n
      rw [hd] at hsame
      have hid : idxAt ws S k n = m n := idxAt_yes hk hm
      by_cases hdir : sp.dirF d.fn = sp.dirOf k
      · cases hmn : m n with
        | none =>
          rw [hmn] at hsame
          exact absurd hdir hsame
        | some a =>
          rw [hmn] at hsame
          obtain ⟨hg, hf⟩ := hsame (Or.inr hdir)
          have hwk : st.wk k ≤ R := hidx ⟨n, a, hmn, by rw [hf]; exact hdir⟩
          have hdat := hold k hwk
          rw [wEntries_some (by rw [hid, hmn])]
          rw [hg, hf]
          constructor
          · rintro (⟨h1, h2⟩ | ⟨_, h3⟩)
            · exact (h2 ⟨rfl, by rw [← hdat]; exact hs.noStale n d hd k l h1⟩).elim
            · exact h3
          · intro h3; exact Or.inr ⟨rfl, h3⟩
      · have hfn : ∀ v, sp.f d.fn k v = none := fun v => sp.f_dir _ _ _ (fun h => hdir h.symm)
        rw [hfn]
        constructor
        · intro h
          exfalso
          cases hmn : m n with
          | none =>
            rw [wEntries_none (by rw [hid, hmn])] at h
            have := hs.noStale n d hd k l h; rw [hfn] at this; cases this
          | some a =>
            rw [wEntries_some (by rw [hid, hmn])] at h
            rcases h with ⟨h1, _⟩ | ⟨_, h3⟩
            · have := hs.noStale n d hd k l h1; rw [hfn] at this; cases this
            · have hda := dir_of_some h3
              rw [hmn] at hsame
              obtain ⟨_, hf⟩ := hsame (Or.inl hda)
              exact hdir (by rw [← hf]; exact hda)
        · intro h; cases h

/-- Point 2: such an index is live (the virtual key of the key's directory). -/
theorem wcommit_live
    (hS : ∀ k m, S k = some m → st.wv (sp.dirOf k) ≤ R →
      ∀ n, sameOn sp (sp.dirOf k) (m n) (st.dfn n))
    (hc : ∀ k, ws k = true → sp.isObj k = true → ∃ m, S k = some m ∧
      st.wv (sp.dirOf k) ≤ R ∧ (hasIdx sp m (sp.dirOf k) → st.wk k ≤ R))
    {n : Name} {k : Key} {a : Def F} {l : L}
    (hi : idxAt ws S k n = some a) (hf : sp.f a.fn k (nv k) = some l) :
    ∃ d, st.dfn n = some d ∧ d.gen = a.gen := by
  cases hk : ws k with
  | false => rw [idxAt_no hk] at hi; cases hi
  | true =>
    have hob : sp.isObj k = true := by
      cases h : sp.isObj k with
      | true => rfl
      | false => rw [sp.f_suffix _ _ _ h] at hf; cases hf
    obtain ⟨m, hm, hv, _⟩ := hc k hk hob
    rw [idxAt_yes hk hm] at hi
    have hsame := hS k m hm hv n
    rw [hi] at hsame
    have hda := dir_of_some hf
    cases hd : st.dfn n with
    | none => rw [hd] at hsame; exact absurd hda hsame
    | some d =>
      rw [hd] at hsame
      exact ⟨d, rfl, (hsame (Or.inl hda)).1.symm⟩

end wcommit

/-- `WCommit`: points 1 and 2. At each key written, every live index's entries
become exactly f(new) (`wcommit_exact`); the commit puts entries only in live
generations (`wcommit_live`). -/
theorem step_wCommit {sp : Spec V F L} {st st' : Stream V F L} {m : Mem V F L W}
    [DecidableEq W] (hs : SInv sp st) (hm : MInv sp st m) {w : W} {ws : Key → Bool}
    {nv : Key → Option V} {R : Time} {old : Key → Option V}
    {S : Key → Option (Name → Option (Def F))}
    (hw : m.wr w = .run ws nv R old S)
    (hc : ∀ k, ws k = true → sp.isObj k = true → ∃ mm, S k = some mm ∧
      st.wv (sp.dirOf k) ≤ R ∧ (hasIdx sp mm (sp.dirOf k) → st.wk k ≤ R))
    (e1 : st'.data = writeData st.data ws nv) (e2 : st'.ent = wEntries sp st.ent ws S old nv)
    (e3 : st'.wk = writeTimes st.wk ws (st.now + 1)) (e4 : st'.now = st.now + 1)
    (e5 : st'.dfn = st.dfn) (e6 : st'.mark = st.mark) (e7 : st'.wdef = st.wdef)
    (e8 : st'.wv = st.wv) :
    SInv sp st' ∧ MInv sp st' { m with wr := upd m.wr w .idle } := by
  have hwi := hm.wInv w
  rw [hw] at hwi
  simp only [WInv] at hwi
  obtain ⟨_, hold, hS⟩ := hwi
  have hkf : ∀ k, (st'.wk k = st.wk k ∧ st'.data k = st.data k) ∨ st.now < st'.wk k := by
    intro k; rw [e1, e3]; exact frame_write st ws nv k
  have hnow : st.now ≤ st'.now := by omega
  -- at a key written, a live index's entries are f of the new value
  have hA : ∀ n d, st.dfn n = some d → ∀ k, ws k = true → ∀ l,
      (st'.ent n d.gen k l ↔ sp.f d.fn k (st'.data k) = some l) := by
    intro n d hd k hk l
    rw [e2, e1, writeData_yes hk]
    exact wcommit_exact hs hold hS hc hd hk l
  -- at a key not written, nothing changes
  have hB : ∀ n g k l, ws k = false → (st'.ent n g k l ↔ st.ent n g k l) := by
    intro n g k l hk; rw [e2]; exact wEntries_none (idxAt_no hk)
  have hBd : ∀ k, ws k = false → st'.data k = st.data k := by
    intro k hk; rw [e1]; exact writeData_no hk
  -- a new entry is in a live generation
  have hC : ∀ n g k l, st'.ent n g k l →
      st.ent n g k l ∨ ∃ d, st.dfn n = some d ∧ d.gen = g := by
    intro n g k l hl
    rw [e2] at hl
    rcases wcommit_new hl with h | ⟨a, hi, hg, hf⟩
    · exact Or.inl h
    · obtain ⟨d, hd, hdg⟩ := wcommit_live hS hc hi hf
      exact Or.inr ⟨d, hd, by rw [hdg, hg]⟩
  have hcov : ∀ n d, st.dfn n = some d → ∀ k,
      Covered sp st n d.gen d.fn k → Covered sp st' n d.gen d.fn k := by
    intro n d hd k hcv
    cases hk : ws k with
    | true => intro l hl; exact (hA n d hd k hk l).mpr hl
    | false => exact hcv.mono (hBd k hk) (fun l hl => (hB n d.gen k l hk).mpr hl)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro n d hd; rw [e5] at hd; rw [e4]; exact Nat.le_succ_of_le (hs.gen_le n d hd)
  · intro n g hg; rw [e6] at hg; rw [e4]; exact Nat.lt_succ_of_lt (hs.mark_lt n g hg)
  · intro n d hd k l hkl
    rw [e5] at hd
    cases hk : ws k with
    | true => exact (hA n d hd k hk l).mp hkl
    | false =>
      rw [hBd k hk]; exact hs.noStale n d hd k l ((hB n d.gen k l hk).mp hkl)
  · intro n d hd ha k; rw [e5] at hd; exact hcov n d hd k (hs.active n d hd ha k)
  · intro n g k l hl
    rw [e5, e6]
    rcases hC n g k l hl with h | h
    · exact hs.accounted n g k l h
    · exact Or.inl h
  · intro n d hd; rw [e5] at hd; rw [e6]; exact hs.markerNotLive n d hd
  · refine (hm.frameS hnow hkf e5 e8 e7 e6 hcov ?_).setW w trivial
    intro n g k l hmk hl
    rcases hC n g k l hl with h | ⟨d, hd, hdg⟩
    · exact h
    · rw [← hdg, hs.markerNotLive n d hd] at hmk; cases hmk

/-! ### The definitions' changes (points 1, 2 and 7) -/

/-- `ACreate`: G is the latest time, after every generation there is (point
7); the virtual key of the index's directory is written (point 1). -/
theorem step_aCreate {sp : Spec V F L} {st st' : Stream V F L} {m : Mem V F L W}
    (hs : SInv sp st) (hm : MInv sp st m) {n : Name} {fn : F}
    (hl : m.lock = .free) (hmem : m.mem n = none)
    (e1 : st'.data = st.data) (e2 : st'.ent = st.ent) (e3 : st'.wk = st.wk)
    (e4 : st'.now = st.now + 1)
    (e5 : st'.dfn = upd st.dfn n (some ⟨max 1 st.now, fn, false⟩))
    (e6 : st'.mark = st.mark) (e7 : st'.wdef = upd st.wdef n (st.now + 1))
    (e8 : st'.wv = upd st.wv (sp.dirF fn) (st.now + 1)) :
    SInv sp st' ∧
      MInv sp st' { m with lock := .mgr, admin := .create n (max 1 st.now) fn } := by
  have hlm : m.lock ≠ .mgr := by rw [hl]; simp
  have hd0 : st.dfn n = none := by rw [← hm.memEq hlm n]; exact hmem
  have hmk : st.mark n (max 1 st.now) = false := by
    cases h : st.mark n (max 1 st.now)
    · rfl
    · have := hs.mark_lt _ _ h; omega
  have hnoent : ∀ k l, ¬ st.ent n (max 1 st.now) k l := by
    intro k l hl
    rcases hs.accounted _ _ k l hl with ⟨d, hd, _⟩ | h
    · rw [hd0] at hd; cases hd
    · rw [hmk] at h; cases h
  have hnolock : ∀ n' g b, m.bld n' g = some b → b.locked = false :=
    fun n' g b hb => hm.notLocked hb (by rw [hl]; simp)
  have hkf : ∀ k, (st'.wk k = st.wk k ∧ st'.data k = st.data k) ∨ st.now < st'.wk k :=
    fun k => Or.inl ⟨by rw [e3], by rw [e1]⟩
  have hdn : st'.dfn n = some ⟨max 1 st.now, fn, false⟩ := by rw [e5, upd_same]
  have hdo : ∀ n', n' ≠ n → st'.dfn n' = st.dfn n' := fun n' h => by rw [e5, upd_ne _ _ h]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro n' d hd; rw [e4]
    by_cases hn : n' = n
    · rw [hn, hdn] at hd; cases hd; show max 1 st.now ≤ st.now + 1; omega
    · rw [hdo n' hn] at hd; exact Nat.le_succ_of_le (hs.gen_le n' d hd)
  · intro n' g hg; rw [e6] at hg; rw [e4]; exact Nat.lt_succ_of_lt (hs.mark_lt n' g hg)
  · intro n' d hd k l hkl
    rw [e2] at hkl; rw [e1]
    by_cases hn : n' = n
    · rw [hn, hdn] at hd; cases hd; rw [hn] at hkl; exact absurd hkl (hnoent k l)
    · rw [hdo n' hn] at hd; exact hs.noStale n' d hd k l hkl
  · intro n' d hd ha' k
    by_cases hn : n' = n
    · rw [hn, hdn] at hd; cases hd; cases ha'
    · rw [hdo n' hn] at hd
      exact (hs.active n' d hd ha' k).mono (by rw [e1]) (fun l hl => by rw [e2]; exact hl)
  · intro n' g k l hl; rw [e2] at hl; rw [e6]
    rcases hs.accounted n' g k l hl with ⟨d, hd, hdg⟩ | h
    · by_cases hn : n' = n
      · rw [hn, hd0] at hd; cases hd
      · exact Or.inl ⟨d, by rw [hdo n' hn]; exact hd, hdg⟩
    · exact Or.inr h
  · intro n' d hd; rw [e6]
    by_cases hn : n' = n
    · rw [hn, hdn] at hd; cases hd; rw [hn]; exact hmk
    · rw [hdo n' hn] at hd; exact hs.markerNotLive n' d hd
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro n'
      by_cases hn : n' = n
      · right; rw [hn]; rfl
      · left; rw [hdo n' hn]; exact hm.memEq hlm n'
    · show Lock.mgr = .mgr ↔ Admin.create n (max 1 st.now) fn ≠ .idle
      simp
    · intro n' g fn' h
      change Admin.create n (max 1 st.now) fn = Admin.create n' g fn' at h
      cases h; exact hdn
    · intro n' g h; cases h
    · intro n' g h; cases h
    · intro n' g b hb hlk; rw [hnolock n' g b hb] at hlk; cases hlk
    · intro w
      refine (hm.wInv w).frame (by omega) hkf (fun dir => ?_)
      by_cases hdir : dir = sp.dirF fn
      · right; rw [e8, hdir, upd_same]; omega
      · left
        refine ⟨by rw [e8, upd_ne _ _ hdir], fun n' x hx => ?_⟩
        by_cases hn : n' = n
        · rw [hn, hdn]; rw [hn, hd0] at hx
          cases x with
          | none => exact fun h => hdir h.symm
          | some a =>
            intro hrel
            rcases hrel with hrel | hrel
            · exact absurd hrel hx
            · exact absurd hrel.symm hdir
        · rw [hdo n' hn]; exact hx
    · intro n' g b hb
      refine (hm.bInv n' g b hb).frame (by omega) hkf ?_ ?_ ?_
      · by_cases hn : n' = n
        · right; rw [e7, hn, upd_same]; omega
        · left; exact ⟨by rw [e7, upd_ne _ _ hn], hdo n' hn⟩
      · intro d' hd' hg
        by_cases hn : n' = n
        · rw [hn, hdn] at hd'; cases hd'; exfalso; change max 1 st.now = g at hg
          rcases hm.bLt n' g b hb with h1 | ⟨d0, hdd, _⟩
          · omega
          · rw [hn, hd0] at hdd; cases hdd
        · exact ⟨d', by rw [← hdo n' hn]; exact hd', hg, rfl, rfl⟩
      · intro d _ _ k hcv; exact hcv.mono (by rw [e1]) (fun l hl => by rw [e2]; exact hl)
    · intro n' g b hb; rw [e4]
      rcases hm.bLt n' g b hb with h1 | ⟨d, hd, hdg⟩
      · left; omega
      · by_cases hn : n' = n
        · rw [hn, hd0] at hd; cases hd
        · right; exact ⟨d, by rw [hdo n' hn]; exact hd, hdg⟩
    · intro n' g c hc
      have hc' := hm.cInv n' g c hc
      exact hc'.frame (by rw [e6]; exact hc'.marked) (fun k l hkl => by rw [e2] at hkl; exact hkl)

/-- `ADelete`: the live generation gets its marker (point 6); the virtual key
of the index's directory is written (point 2). -/
theorem step_aDelete {sp : Spec V F L} {st st' : Stream V F L} {m : Mem V F L W}
    (hs : SInv sp st) (hm : MInv sp st m) {n : Name} {d : Def F}
    (hl : m.lock = .free) (hmem : m.mem n = some d)
    (e1 : st'.data = st.data) (e2 : st'.ent = st.ent) (e3 : st'.wk = st.wk)
    (e4 : st'.now = st.now + 1) (e5 : st'.dfn = upd st.dfn n none)
    (e6 : st'.mark = upd2 st.mark n d.gen true) (e7 : st'.wdef = upd st.wdef n (st.now + 1))
    (e8 : st'.wv = upd st.wv (sp.dirF d.fn) (st.now + 1)) :
    SInv sp st' ∧ MInv sp st' { m with lock := .mgr, admin := .delete n d.gen } := by
  have hlm : m.lock ≠ .mgr := by rw [hl]; simp
  have hd : st.dfn n = some d := by rw [← hm.memEq hlm n]; exact hmem
  have hnolock : ∀ n' g b, m.bld n' g = some b → b.locked = false :=
    fun n' g b hb => hm.notLocked hb (by rw [hl]; simp)
  have hkf : ∀ k, (st'.wk k = st.wk k ∧ st'.data k = st.data k) ∨ st.now < st'.wk k :=
    fun k => Or.inl ⟨by rw [e3], by rw [e1]⟩
  have hdn : st'.dfn n = none := by rw [e5, upd_same]
  have hdo : ∀ n', n' ≠ n → st'.dfn n' = st.dfn n' := fun n' h => by rw [e5, upd_ne _ _ h]
  have hmkn : st'.mark n d.gen = true := by rw [e6, upd2_same]
  have hmko : ∀ n' g, ¬ (n' = n ∧ g = d.gen) → st'.mark n' g = st.mark n' g :=
    fun n' g h => by rw [e6, upd2_ne _ _ h]
  have hmk' : ∀ n' g, st.mark n' g = true → st'.mark n' g = true := by
    intro n' g hg
    by_cases hgg : n' = n ∧ g = d.gen
    · rw [hgg.1, hgg.2]; exact hmkn
    · rw [hmko n' g hgg]; exact hg
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro n' d' hd'
    by_cases hn : n' = n
    · rw [hn, hdn] at hd'; cases hd'
    · rw [hdo n' hn] at hd'; rw [e4]; exact Nat.le_succ_of_le (hs.gen_le n' d' hd')
  · intro n' g hg; rw [e4]
    by_cases hgg : n' = n ∧ g = d.gen
    · rw [hgg.2]; exact Nat.lt_succ_of_le (hs.gen_le n d hd)
    · rw [hmko n' g hgg] at hg; exact Nat.lt_succ_of_lt (hs.mark_lt n' g hg)
  · intro n' d' hd' k l hkl
    by_cases hn : n' = n
    · rw [hn, hdn] at hd'; cases hd'
    · rw [hdo n' hn] at hd'; rw [e2] at hkl; rw [e1]; exact hs.noStale n' d' hd' k l hkl
  · intro n' d' hd' ha' k
    by_cases hn : n' = n
    · rw [hn, hdn] at hd'; cases hd'
    · rw [hdo n' hn] at hd'
      exact (hs.active n' d' hd' ha' k).mono (by rw [e1]) (fun l hl => by rw [e2]; exact hl)
  · intro n' g k l hl; rw [e2] at hl
    rcases hs.accounted n' g k l hl with ⟨d', hd', hg⟩ | h
    · by_cases hn : n' = n
      · right; rw [hn] at hd' ⊢; rw [hd] at hd'; cases hd'; rw [← hg]; exact hmkn
      · left; exact ⟨d', by rw [hdo n' hn]; exact hd', hg⟩
    · exact Or.inr (hmk' n' g h)
  · intro n' d' hd'
    by_cases hn : n' = n
    · rw [hn, hdn] at hd'; cases hd'
    · rw [hdo n' hn] at hd'
      rw [hmko n' d'.gen (fun h => hn h.1)]; exact hs.markerNotLive n' d' hd'
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro n'
      by_cases hn : n' = n
      · right; rw [hn]; rfl
      · left; rw [hdo n' hn]; exact hm.memEq hlm n'
    · show Lock.mgr = .mgr ↔ Admin.delete n d.gen ≠ (.idle : Admin F)
      simp
    · intro n' g fn h; cases h
    · intro n' g h
      change Admin.delete n d.gen = Admin.delete n' g at h
      cases h
      refine ⟨hdn, hmkn, ?_⟩
      show m.cln n d.gen = none
      cases hc : m.cln n d.gen with
      | none => rfl
      | some c =>
        have := (hm.cInv _ _ c hc).marked
        rw [hs.markerNotLive n d hd] at this; cases this
    · intro n' g h; cases h
    · intro n' g b hb hlk; rw [hnolock n' g b hb] at hlk; cases hlk
    · intro w
      refine (hm.wInv w).frame (by omega) hkf (fun dir => ?_)
      by_cases hdir : dir = sp.dirF d.fn
      · right; rw [e8, hdir, upd_same]; omega
      · left
        refine ⟨by rw [e8, upd_ne _ _ hdir], fun n' x hx => ?_⟩
        by_cases hn : n' = n
        · rw [hn, hdn]; rw [hn, hd] at hx
          cases x with
          | none => trivial
          | some a =>
            show sp.dirF a.fn ≠ dir
            intro ha'
            have := (hx (Or.inl ha')).2
            exact hdir (by rw [← this]; exact ha'.symm)
        · rw [hdo n' hn]; exact hx
    · intro n' g b hb
      refine (hm.bInv n' g b hb).frame (by omega) hkf ?_ ?_ ?_
      · by_cases hn : n' = n
        · right; rw [e7, hn, upd_same]; omega
        · left; exact ⟨by rw [e7, upd_ne _ _ hn], hdo n' hn⟩
      · intro d' hd' hg
        by_cases hn : n' = n
        · rw [hn, hdn] at hd'; cases hd'
        · exact ⟨d', by rw [← hdo n' hn]; exact hd', hg, rfl, rfl⟩
      · intro d' _ _ k hc; exact hc.mono (by rw [e1]) (fun l hl => by rw [e2]; exact hl)
    · intro n' g b hb; rw [e4]
      rcases hm.bLt n' g b hb with h1 | ⟨d', hd', hdg⟩
      · left; omega
      · by_cases hn : n' = n
        · left; rw [hn, hd] at hd'; cases hd'; rw [← hdg]
          exact Nat.lt_succ_of_le (hs.gen_le n d hd)
        · right; exact ⟨d', by rw [hdo n' hn]; exact hd', hdg⟩
    · intro n' g c hc
      have hc' := hm.cInv n' g c hc
      exact hc'.frame (hmk' n' g hc'.marked) (fun k l hkl => by rw [e2] at hkl; exact hkl)

/-! ### The builds (points 3, 4 and 5) -/

/-- `BCommit`: point 3. The step's generation is live (the definition's key,
after `isLive`), and every value whose entry it puts is its key's value (the
values' keys); the keys it passed are covered. -/
theorem step_bCommit {sp : Spec V F L} {st st' : Stream V F L} {m : Mem V F L W}
    (hs : SInv sp st) (hm : MInv sp st m) {n : Name} {g : Gen} {b : BSt V F}
    (hb : m.bld n g = some b) (hpc : b.pc = .commit) (hdef : st.wdef n ≤ b.R)
    (hkeys : ∀ k, b.next ≤ k → k < b.hi → sp.f b.fn k (b.snap k) ≠ none → st.wk k ≤ b.R)
    (e1 : st'.data = st.data) (e2 : st'.ent = bEntries sp st.ent n g b) (e3 : st'.wk = st.wk)
    (e4 : st'.now = st.now + 1) (e5 : st'.dfn = st.dfn) (e6 : st'.mark = st.mark)
    (e7 : st'.wdef = st.wdef) (e8 : st'.wv = st.wv) :
    SInv sp st' ∧
      MInv sp st' { m with bld := upd2 m.bld n g (some (bAfter b)),
                           lock := if b.locked = true then .free else m.lock } := by
  have hbi := hm.bInv n g b hb
  have hsi := hbi.inStep (Or.inr hpc)
  obtain ⟨d, hd, hdg⟩ := hbi.live hpc hdef
  obtain ⟨hfn, hact⟩ := hbi.fnEq d hd hdg
  have hmkg : st.mark n g = false := by rw [← hdg]; exact hs.markerNotLive n d hd
  have hput : ∀ k l, b.next ≤ k → k < b.hi → sp.f b.fn k (b.snap k) = some l →
      st.data k = b.snap k := by
    intro k l h1 h2 h3
    exact hsi.snap k (hkeys k h1 h2 (by rw [h3]; simp))
  have hsub : ∀ n' g' k l, st'.ent n' g' k l → st.ent n' g' k l ∨
      (n' = n ∧ g' = g ∧ b.next ≤ k ∧ k < b.hi ∧ sp.f b.fn k (b.snap k) = some l) := by
    intro n' g' k l hl; rw [e2] at hl; exact hl
  have hsup : ∀ n' g' k l, st.ent n' g' k l → st'.ent n' g' k l := by
    intro n' g' k l hl; rw [e2]; exact Or.inl hl
  have hmono : ∀ n' g' fn k, Covered sp st n' g' fn k → Covered sp st' n' g' fn k :=
    fun n' g' fn k hc => hc.mono (by rw [e1]) (fun l hl => hsup _ _ _ _ hl)
  have hsinv : SInv sp st' := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro n' d' hd'; rw [e5] at hd'; rw [e4]; exact Nat.le_succ_of_le (hs.gen_le n' d' hd')
    · intro n' g' hg'; rw [e6] at hg'; rw [e4]; exact Nat.lt_succ_of_lt (hs.mark_lt n' g' hg')
    · intro n' d' hd' k l hkl
      rw [e5] at hd'
      rw [e1]
      rcases hsub _ _ k l hkl with h | ⟨h0, _, h2, h3, h4⟩
      · exact hs.noStale n' d' hd' k l h
      · rw [h0] at hd'
        have hdd : d' = d := by rw [hd] at hd'; exact (Option.some.inj hd').symm
        rw [hdd, hput k l h2 h3 h4, hfn]; exact h4
    · intro n' d' hd' ha k
      rw [e5] at hd'
      exact hmono _ _ _ k (hs.active n' d' hd' ha k)
    · intro n' g' k l hl
      rw [e5, e6]
      rcases hsub n' g' k l hl with h | ⟨h0, h1, -⟩
      · exact hs.accounted n' g' k l h
      · exact Or.inl ⟨d, by rw [h0]; exact hd, by rw [hdg, h1]⟩
    · intro n' d' hd'; rw [e5] at hd'; rw [e6]; exact hs.markerNotLive n' d' hd'
  refine ⟨hsinv, ?_⟩
  have hm1 : MInv sp st' m :=
    hm.frameS (by omega) (fun k => Or.inl ⟨by rw [e3], by rw [e1]⟩) e5 e8 e7 e6
      (fun n' d' _ k hc => hmono _ _ _ k hc)
      (fun n' g' k l hmk hl => by
        rcases hsub n' g' k l hl with h | ⟨h0, h1, -⟩
        · exact h
        · rw [h0, h1, hmkg] at hmk; cases hmk)
  -- the build after its step
  have hb' : BInv sp st' n g (bAfter b) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro d' hd' hg'; rw [e5] at hd'; exact hbi.fnEq d' hd' hg'
    · intro _ _ _ k hk
      rcases hk with hk | ⟨e, he, hek⟩
      · change k < b.hi at hk
        by_cases hkn : k < b.next
        · exact hmono _ _ _ k (hbi.cover d hd hdg k (Or.inl hkn))
        · cases hf : sp.f b.fn k (b.snap k) with
          | none => exact hmono _ _ _ k (hsi.noneCov d hd hdg k (by omega) hk hf)
          | some l0 =>
            intro l hl
            change sp.f b.fn k (st'.data k) = some l at hl
            rw [e1, hput k l0 (by omega) hk hf] at hl
            rw [e2]; exact Or.inr ⟨rfl, rfl, by omega, hk, hl⟩
      · exact hmono _ _ _ k (hbi.cover d hd hdg k (Or.inr ⟨e, he, hek⟩))
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
      have hl := hm.bLocked n g b hb hlk
      have hid := hm.adminIdle (by rw [hl]; simp)
      rw [hid]; simp
    · rw [ite_eq_right hlk]; exact hm.lockMgr
  · intro n' g' hg'
    change (if b.locked = true then Lock.free else m.lock) = .bld n' g' at hg'
    show ∃ b'', upd2 m.bld n g (some (bAfter b)) n' g' = some b'' ∧ b''.locked = true
    by_cases hlk : b.locked = true
    · rw [ite_eq_left hlk] at hg'; cases hg'
    · rw [ite_eq_right hlk] at hg'
      obtain ⟨b'', hb'', hl''⟩ := hm.lockBld n' g' hg'
      by_cases hgg : n' = n ∧ g' = g
      · rw [hgg.1, hgg.2, hb] at hb''; cases hb''; exact absurd hl'' hlk
      · rw [upd2_ne _ _ hgg]; exact ⟨b'', hb'', hl''⟩
  · intro n' g' b'' hb'' hl''
    change upd2 m.bld n g (some (bAfter b)) n' g' = some b'' at hb''
    show (if b.locked = true then Lock.free else m.lock) = .bld n' g'
    by_cases hgg : n' = n ∧ g' = g
    · rw [hgg.1, hgg.2, upd2_same] at hb''; cases hb''; cases hl''
    · rw [upd2_ne _ _ hgg] at hb''
      have h1 := hm.bLocked n' g' b'' hb'' hl''
      by_cases hlk : b.locked = true
      · have h2 := hm.bLocked n g b hb hlk
        rw [h1] at h2; cases h2; exact absurd ⟨rfl, rfl⟩ hgg
      · rw [ite_eq_right hlk]; exact h1
  · intro n' g' b'' hb''
    change upd2 m.bld n g (some (bAfter b)) n' g' = some b'' at hb''
    by_cases hgg : n' = n ∧ g' = g
    · rw [hgg.1, hgg.2, upd2_same] at hb''; cases hb''; rw [hgg.1, hgg.2]; exact hb'
    · rw [upd2_ne _ _ hgg] at hb''; exact hm1.bInv n' g' b'' hb''
  · intro n' g' b'' hb''
    change upd2 m.bld n g (some (bAfter b)) n' g' = some b'' at hb''
    by_cases hgg : n' = n ∧ g' = g
    · rw [hgg.1, hgg.2]; exact hm1.bLt n g b hb
    · rw [upd2_ne _ _ hgg] at hb''; exact hm1.bLt n' g' b'' hb''

/-- `BActivate`: point 5. Every key is passed, so covered: the index is a
function of the data when it becomes active. -/
theorem step_bActivate {sp : Spec V F L} {st st' : Stream V F L} {m : Mem V F L W}
    (hs : SInv sp st) (hm : MInv sp st m) {n : Name} {g : Gen} {b : BSt V F} {d : Def F}
    (hb : m.bld n g = some b) (hpc : b.pc = .activate) (hl : m.lock = .free)
    (hmem : m.mem n = some d) (hdg : d.gen = g)
    (e1 : st'.data = st.data) (e2 : st'.ent = st.ent) (e3 : st'.wk = st.wk)
    (e4 : st'.now = st.now + 1) (e5 : st'.dfn = upd st.dfn n (some ⟨g, b.fn, true⟩))
    (e6 : st'.mark = st.mark) (e7 : st'.wdef = upd st.wdef n (st.now + 1))
    (e8 : st'.wv = st.wv) :
    SInv sp st' ∧
      MInv sp st' { m with mem := upd m.mem n (some ⟨g, b.fn, true⟩),
                           bld := upd2 m.bld n g none } := by
  have hlm : m.lock ≠ .mgr := by rw [hl]; simp
  have hid : m.admin = .idle := hm.adminIdle hlm
  have hd : st.dfn n = some d := by rw [← hm.memEq hlm n]; exact hmem
  have hbi := hm.bInv n g b hb
  obtain ⟨hfn, _⟩ := hbi.fnEq d hd hdg
  have hcovAll : ∀ k, Covered sp st n g b.fn k :=
    fun k => hbi.cover d hd hdg k (hbi.done hpc k)
  have hsame : ∀ n' g' fn k, Covered sp st n' g' fn k → Covered sp st' n' g' fn k :=
    fun n' g' fn k hc => hc.mono (by rw [e1]) (fun l hl => by rw [e2]; exact hl)
  have hnolock : ∀ n' g' b', m.bld n' g' = some b' → b'.locked = false :=
    fun n' g' b' hb' => hm.notLocked hb' (by rw [hl]; simp)
  have hkf : ∀ k, (st'.wk k = st.wk k ∧ st'.data k = st.data k) ∨ st.now < st'.wk k :=
    fun k => Or.inl ⟨by rw [e3], by rw [e1]⟩
  have hdn : st'.dfn n = some ⟨g, b.fn, true⟩ := by rw [e5, upd_same]
  have hdo : ∀ n', n' ≠ n → st'.dfn n' = st.dfn n' := fun n' h => by rw [e5, upd_ne _ _ h]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro n' d' hd'; rw [e4]
    by_cases hn : n' = n
    · rw [hn, hdn] at hd'; cases hd'
      show g ≤ st.now + 1; rw [← hdg]; exact Nat.le_succ_of_le (hs.gen_le n d hd)
    · rw [hdo n' hn] at hd'; exact Nat.le_succ_of_le (hs.gen_le n' d' hd')
  · intro n' g' hg'; rw [e6] at hg'; rw [e4]; exact Nat.lt_succ_of_lt (hs.mark_lt n' g' hg')
  · intro n' d' hd' k l hkl
    rw [e2] at hkl; rw [e1]
    by_cases hn : n' = n
    · rw [hn, hdn] at hd'; cases hd'
      change st.ent n' g k l at hkl
      show sp.f b.fn k (st.data k) = some l
      rw [hn] at hkl
      have := hs.noStale n d hd k l (by rw [hdg]; exact hkl)
      rw [hfn] at this; exact this
    · rw [hdo n' hn] at hd'; exact hs.noStale n' d' hd' k l hkl
  · intro n' d' hd' ha k
    by_cases hn : n' = n
    · rw [hn, hdn] at hd'; cases hd'; rw [hn]; exact hsame _ _ _ k (hcovAll k)
    · rw [hdo n' hn] at hd'; exact hsame _ _ _ k (hs.active n' d' hd' ha k)
  · intro n' g' k l hl; rw [e2] at hl; rw [e6]
    rcases hs.accounted n' g' k l hl with ⟨d', hd', hg'⟩ | h
    · by_cases hn : n' = n
      · rw [hn] at hd' ⊢; rw [hd] at hd'; cases hd'
        exact Or.inl ⟨⟨g, b.fn, true⟩, hdn, by show g = g'; rw [← hg', hdg]⟩
      · exact Or.inl ⟨d', by rw [hdo n' hn]; exact hd', hg'⟩
    · exact Or.inr h
  · intro n' d' hd'; rw [e6]
    by_cases hn : n' = n
    · rw [hn, hdn] at hd'; cases hd'
      show st.mark n' g = false; rw [hn, ← hdg]; exact hs.markerNotLive n d hd
    · rw [hdo n' hn] at hd'; exact hs.markerNotLive n' d' hd'
  · refine ⟨?_, hm.lockMgr, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro n'
      left
      show upd m.mem n (some ⟨g, b.fn, true⟩) n' = st'.dfn n'
      by_cases hn : n' = n
      · rw [hn, upd_same, hdn]
      · rw [upd_ne _ _ hn, hdo n' hn]; exact hm.memEq hlm n'
    · intro n' g' fn' h; change m.admin = _ at h; rw [hid] at h; cases h
    · intro n' g' h; change m.admin = _ at h; rw [hid] at h; cases h
    · intro n' g' h; change m.lock = _ at h; rw [hl] at h; cases h
    · intro n' g' b' hb' hl'
      change upd2 m.bld n g none n' g' = some b' at hb'
      by_cases hgg : n' = n ∧ g' = g
      · rw [hgg.1, hgg.2, upd2_same] at hb'; cases hb'
      · rw [upd2_ne _ _ hgg] at hb'; rw [hnolock n' g' b' hb'] at hl'; cases hl'
    · intro w
      refine (hm.wInv w).frame (by omega) hkf (fun dir => Or.inl ⟨by rw [e8], ?_⟩)
      intro n' x hx
      by_cases hn : n' = n
      · rw [hn, hdn]; rw [hn, hd] at hx
        exact sameOn_congr (by show g = d.gen; rw [hdg]) (by show b.fn = d.fn; rw [hfn]) hx
      · rw [hdo n' hn]; exact hx
    · intro n' g' b' hb'
      change upd2 m.bld n g none n' g' = some b' at hb'
      by_cases hgg : n' = n ∧ g' = g
      · rw [hgg.1, hgg.2, upd2_same] at hb'; cases hb'
      · rw [upd2_ne _ _ hgg] at hb'
        refine (hm.bInv n' g' b' hb').frame (by omega) hkf ?_ ?_ ?_
        · by_cases hn : n' = n
          · right; rw [e7, hn, upd_same]; omega
          · left; exact ⟨by rw [e7, upd_ne _ _ hn], hdo n' hn⟩
        · intro d' hd' hg'
          by_cases hn : n' = n
          · rw [hn, hdn] at hd'; cases hd'
            exact absurd ⟨hn, hg'.symm⟩ hgg
          · exact ⟨d', by rw [← hdo n' hn]; exact hd', hg', rfl, rfl⟩
        · intro d' _ _ k hc; exact hsame _ _ _ k hc
    · intro n' g' b' hb'
      change upd2 m.bld n g none n' g' = some b' at hb'
      by_cases hgg : n' = n ∧ g' = g
      · rw [hgg.1, hgg.2, upd2_same] at hb'; cases hb'
      · rw [upd2_ne _ _ hgg] at hb'; rw [e4]
        rcases hm.bLt n' g' b' hb' with h1 | ⟨d', hd', hdg'⟩
        · left; omega
        · by_cases hn : n' = n
          · left; rw [hn, hd] at hd'; cases hd'
            exact absurd ⟨hn, by rw [← hdg', hdg]⟩ hgg
          · right; exact ⟨d', by rw [hdo n' hn]; exact hd', hdg'⟩
    · intro n' g' c hc
      have hc' := hm.cInv n' g' c hc
      exact hc'.frame (by rw [e6]; exact hc'.marked) (fun k l hkl => by rw [e2] at hkl; exact hkl)

/-! ### The cleanups (points 6 and 9) -/

/-- `CDel`: a cleanup deletes entries of a generation with a marker, never a
live one's. -/
theorem step_cDel {sp : Spec V F L} {st st' : Stream V F L} {m : Mem V F L W}
    (hs : SInv sp st) (hm : MInv sp st m) {n : Name} {g : Gen} {c : CSt L}
    (hc : m.cln n g = some c)
    (e1 : st'.data = st.data)
    (e2 : st'.ent = fun n' g' k l => st.ent n' g' k l ∧ ¬ (n' = n ∧ g' = g ∧ c.keys k l))
    (e3 : st'.wk = st.wk) (e4 : st'.now = st.now + 1) (e5 : st'.dfn = st.dfn)
    (e6 : st'.mark = st.mark) (e7 : st'.wdef = st.wdef) (e8 : st'.wv = st.wv) :
    SInv sp st' ∧
      MInv sp st' { m with cln := upd2 m.cln n g (some { c with pc := .scan }) } := by
  have hci := hm.cInv n g c hc
  have hsub : ∀ n' g' k l, st'.ent n' g' k l → st.ent n' g' k l := by
    intro n' g' k l hl; rw [e2] at hl; exact hl.1
  have hlivecov : ∀ n' d, st.dfn n' = some d → ∀ k,
      Covered sp st n' d.gen d.fn k → Covered sp st' n' d.gen d.fn k := by
    intro n' d hd k hcv
    have hne : ¬ (n' = n ∧ d.gen = g) := by
      intro h
      have := hs.markerNotLive n' d hd
      rw [h.1, h.2, hci.marked] at this; cases this
    refine hcv.mono (by rw [e1]) (fun l hl => ?_)
    rw [e2]; exact ⟨hl, fun h => hne ⟨h.1, h.2.1⟩⟩
  have hsinv : SInv sp st' := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro n' d hd; rw [e5] at hd; rw [e4]; exact Nat.le_succ_of_le (hs.gen_le n' d hd)
    · intro n' g' hg'; rw [e6] at hg'; rw [e4]; exact Nat.lt_succ_of_lt (hs.mark_lt n' g' hg')
    · intro n' d hd k l hkl; rw [e5] at hd; rw [e1]
      exact hs.noStale n' d hd k l (hsub _ _ k l hkl)
    · intro n' d hd ha k; rw [e5] at hd; exact hlivecov n' d hd k (hs.active n' d hd ha k)
    · intro n' g' k l hl; rw [e5, e6]; exact hs.accounted n' g' k l (hsub _ _ k l hl)
    · intro n' d hd; rw [e5] at hd; rw [e6]; exact hs.markerNotLive n' d hd
  refine ⟨hsinv, ?_⟩
  have hm1 : MInv sp st' m :=
    hm.frameS (by omega) (fun k => Or.inl ⟨by rw [e3], by rw [e1]⟩) e5 e8 e7 e6
      hlivecov (fun n' g' k l _ hl => hsub n' g' k l hl)
  exact hm1.setC hc ⟨by rw [e6]; exact hci.marked, fun h => by cases h⟩

/-- `CEnd`: the marker is deleted when its generation has no entry left; no
later step puts one (points 2 and 3). -/
theorem step_cEnd {sp : Spec V F L} {st st' : Stream V F L} {m : Mem V F L W}
    (hs : SInv sp st) (hm : MInv sp st m) {n : Name} {g : Gen} {c : CSt L}
    (hc : m.cln n g = some c) (hpc : c.pc = .done)
    (e1 : st'.data = st.data) (e2 : st'.ent = st.ent)
    (e3 : st'.wk = st.wk) (e4 : st'.now = st.now + 1) (e5 : st'.dfn = st.dfn)
    (e6 : st'.mark = upd2 st.mark n g false) (e7 : st'.wdef = st.wdef) (e8 : st'.wv = st.wv) :
    SInv sp st' ∧ MInv sp st' { m with cln := upd2 m.cln n g none } := by
  have hci := hm.cInv n g c hc
  have hempty := hci.empty hpc
  have hmk : ∀ n' g', ¬ (n' = n ∧ g' = g) → st'.mark n' g' = st.mark n' g' := by
    intro n' g' h; rw [e6]; exact upd2_ne _ _ h
  have hmkg : st'.mark n g = false := by rw [e6, upd2_same]
  have hsinv : SInv sp st' := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro n' d hd; rw [e5] at hd; rw [e4]; exact Nat.le_succ_of_le (hs.gen_le n' d hd)
    · intro n' g' hg'; rw [e4]
      by_cases hgg : n' = n ∧ g' = g
      · rw [hgg.1, hgg.2, hmkg] at hg'; cases hg'
      · rw [hmk n' g' hgg] at hg'; exact Nat.lt_succ_of_lt (hs.mark_lt n' g' hg')
    · intro n' d hd k l hkl; rw [e5] at hd; rw [e2] at hkl; rw [e1]
      exact hs.noStale n' d hd k l hkl
    · intro n' d hd ha k; rw [e5] at hd
      exact (hs.active n' d hd ha k).mono (by rw [e1]) (fun l hl => by rw [e2]; exact hl)
    · intro n' g' k l hl; rw [e2] at hl; rw [e5]
      rcases hs.accounted n' g' k l hl with h | h
      · exact Or.inl h
      · right
        by_cases hgg : n' = n ∧ g' = g
        · rw [hgg.1, hgg.2] at hl; exact absurd hl (hempty k l)
        · rw [hmk n' g' hgg]; exact h
    · intro n' d hd; rw [e5] at hd
      by_cases hgg : n' = n ∧ d.gen = g
      · rw [hgg.1, hgg.2, hmkg]
      · rw [hmk _ _ hgg]; exact hs.markerNotLive n' d hd
  refine ⟨hsinv, ?_⟩
  have hkf : ∀ k, (st'.wk k = st.wk k ∧ st'.data k = st.data k) ∨ st.now < st'.wk k :=
    fun k => Or.inl ⟨by rw [e3], by rw [e1]⟩
  refine ⟨?_, hm.lockMgr, ?_, ?_, hm.lockBld, hm.bLocked, ?_, ?_, ?_, ?_⟩
  · intro n'; rw [e5]; exact hm.memAgrees n'
  · intro n' g' fn h; rw [e5]; exact hm.adminCreate n' g' fn h
  · intro n' g' h
    obtain ⟨h1, h2, h3⟩ := hm.adminDelete n' g' h
    have hgg : ¬ (n' = n ∧ g' = g) := by
      intro he; rw [he.1, he.2, hc] at h3; cases h3
    refine ⟨by rw [e5]; exact h1, by rw [hmk n' g' hgg]; exact h2, ?_⟩
    show upd2 m.cln n g none n' g' = none
    rw [upd2_ne _ _ hgg]; exact h3
  · intro w
    refine (hm.wInv w).frame (by omega) hkf (fun dir => Or.inl ⟨by rw [e8], ?_⟩)
    intro n' x hx; rw [e5]; exact hx
  · intro n' g' b hb
    refine (hm.bInv n' g' b hb).frame (by omega) hkf (Or.inl ⟨by rw [e7], by rw [e5]⟩) ?_ ?_
    · intro d' hd' hg; exact ⟨d', by rw [← e5]; exact hd', hg, rfl, rfl⟩
    · intro d _ _ k hcv; exact hcv.mono (by rw [e1]) (fun l hl => by rw [e2]; exact hl)
  · intro n' g' b hb; rw [e4]
    rcases hm.bLt n' g' b hb with h1 | h1
    · left; omega
    · right; rw [e5]; exact h1
  · intro n' g' c' hc'
    change upd2 m.cln n g none n' g' = some c' at hc'
    by_cases hgg : n' = n ∧ g' = g
    · rw [hgg.1, hgg.2, upd2_same] at hc'; cases hc'
    · rw [upd2_ne _ _ hgg] at hc'
      have hci' := hm.cInv n' g' c' hc'
      exact ⟨by rw [hmk n' g' hgg]; exact hci'.marked,
        fun hp k l hl => hci'.empty hp k l (by rw [e2] at hl; exact hl)⟩

/-! ### Steps of memory only -/

theorem minv_wStart {sp : Spec V F L} {st : Stream V F L} {m : Mem V F L W} [DecidableEq W]
    (hm : MInv sp st m) (w : W) (ws : Key → Bool) (nv : Key → Option V) :
    MInv sp st { m with wr := upd m.wr w (.run ws nv st.now st.data (fun _ => none)) } := by
  apply hm.setW w
  show st.now ≤ st.now ∧ (∀ k, st.wk k ≤ st.now → st.data k = st.data k) ∧
    (∀ k mm, (none : Option (Name → Option (Def F))) = some mm →
      st.wv (sp.dirOf k) ≤ st.now → ∀ n, sameOn sp (sp.dirOf k) (mm n) (st.dfn n))
  exact ⟨Nat.le_refl _, fun _ _ => rfl, fun _ _ h => by cases h⟩

/-- `WReadS`: under the lock, no definition change is under way, so the maps
are the stream's definitions. -/
theorem minv_wReadS {sp : Spec V F L} {st : Stream V F L} {m : Mem V F L W} [DecidableEq W]
    (hm : MInv sp st m) {w : W} {k : Key} {ws : Key → Bool} {nv : Key → Option V} {R : Time}
    {old : Key → Option V} {S : Key → Option (Name → Option (Def F))}
    (hw : m.wr w = .run ws nv R old S) (hl : m.lock = .free) :
    MInv sp st { m with wr := upd m.wr w (.run ws nv R old (upd S k (some m.mem))) } := by
  have hwi := hm.wInv w
  rw [hw] at hwi
  simp only [WInv] at hwi
  obtain ⟨h1, h2, h3⟩ := hwi
  apply hm.setW w
  show R ≤ st.now ∧ (∀ k, st.wk k ≤ R → st.data k = old k) ∧
    (∀ k' mm, upd S k (some m.mem) k' = some mm → st.wv (sp.dirOf k') ≤ R →
      ∀ n, sameOn sp (sp.dirOf k') (mm n) (st.dfn n))
  refine ⟨h1, h2, fun k' mm hmm hv n => ?_⟩
  by_cases hk : k' = k
  · rw [hk, upd_same] at hmm
    cases hmm
    rw [hm.memEq (by rw [hl]; simp) n]; exact sameOn_refl _ _ _
  · rw [upd_ne _ _ hk] at hmm; exact h3 k' mm hmm hv n

theorem minv_aCreateMap {sp : Spec V F L} {st : Stream V F L} {m : Mem V F L W}
    (hm : MInv sp st m) {n : Name} {g : Gen} {fn : F}
    (ha : m.admin = .create n g fn) :
    MInv sp st { m with mem := upd m.mem n (st.dfn n), lock := .free, admin := .idle,
                        bld := upd2 m.bld n g (some (BSt.init fn)) } := by
  have hd := hm.adminCreate n g fn ha
  have hlk : m.lock = .mgr := hm.lockMgr.mpr (by rw [ha]; simp)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hm.wInv, ?_, ?_, hm.cInv⟩
  · intro n'
    left
    show upd m.mem n (st.dfn n) n' = st.dfn n'
    by_cases hn : n' = n
    · rw [hn, upd_same]
    · rw [upd_ne _ _ hn]
      rcases hm.memAgrees n' with h | h
      · exact h
      · rw [ha] at h; cases h; exact absurd rfl hn
  · show Lock.free = .mgr ↔ (Admin.idle : Admin F) ≠ .idle; simp
  · intro n' g' fn' h; cases h
  · intro n' g' h; cases h
  · intro n' g' h; cases h
  · intro n' g' b hb hl
    change upd2 m.bld n g (some (BSt.init fn)) n' g' = some b at hb
    by_cases hgg : n' = n ∧ g' = g
    · rw [hgg.1, hgg.2, upd2_same] at hb; cases hb; cases hl
    · rw [upd2_ne _ _ hgg] at hb
      have := hm.bLocked n' g' b hb hl; rw [hlk] at this; cases this
  · intro n' g' b hb
    change upd2 m.bld n g (some (BSt.init fn)) n' g' = some b at hb
    by_cases hgg : n' = n ∧ g' = g
    · rw [hgg.1, hgg.2, upd2_same] at hb; cases hb; rw [hgg.1, hgg.2]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro d hd' _; rw [hd] at hd'; cases hd'; exact ⟨rfl, rfl⟩
      · intro d _ _ k hk
        rcases hk with hk | ⟨e, he, _⟩
        · exact absurd hk (Nat.not_lt_zero k)
        · cases he
      · intro h; cases h
      · intro h; rcases h with h | h <;> cases h
      · intro h; cases h
    · rw [upd2_ne _ _ hgg] at hb; exact hm.bInv n' g' b hb
  · intro n' g' b hb
    change upd2 m.bld n g (some (BSt.init fn)) n' g' = some b at hb
    by_cases hgg : n' = n ∧ g' = g
    · rw [hgg.1, hgg.2]; exact Or.inr ⟨_, hd, rfl⟩
    · rw [upd2_ne _ _ hgg] at hb; exact hm.bLt n' g' b hb

theorem minv_aDeleteMap {sp : Spec V F L} {st : Stream V F L} {m : Mem V F L W}
    (hm : MInv sp st m) {n : Name} {g : Gen} (ha : m.admin = .delete n g) :
    MInv sp st { m with mem := upd m.mem n none, lock := .free, admin := .idle,
                        cln := upd2 m.cln n g (some CSt.init) } := by
  obtain ⟨hd, hmk, _⟩ := hm.adminDelete n g ha
  have hlk : m.lock = .mgr := hm.lockMgr.mpr (by rw [ha]; simp)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hm.wInv, hm.bInv, hm.bLt, ?_⟩
  · intro n'
    left
    show upd m.mem n none n' = st.dfn n'
    by_cases hn : n' = n
    · rw [hn, upd_same, hd]
    · rw [upd_ne _ _ hn]
      rcases hm.memAgrees n' with h | h
      · exact h
      · rw [ha] at h; cases h; exact absurd rfl hn
  · show Lock.free = .mgr ↔ (Admin.idle : Admin F) ≠ .idle; simp
  · intro n' g' fn' h; cases h
  · intro n' g' h; cases h
  · intro n' g' h; cases h
  · intro n' g' b hb hl; have := hm.bLocked n' g' b hb hl; rw [hlk] at this; cases this
  · intro n' g' c hc
    change upd2 m.cln n g (some CSt.init) n' g' = some c at hc
    by_cases hgg : n' = n ∧ g' = g
    · rw [hgg.1, hgg.2, upd2_same] at hc; cases hc; rw [hgg.1, hgg.2]
      exact ⟨hmk, fun h => by cases h⟩
    · rw [upd2_ne _ _ hgg] at hc; exact hm.cInv n' g' c hc

/-- `BReadE`: the keys after E have no entry, so they are covered (point 4). -/
theorem minv_bReadE {sp : Spec V F L} {st : Stream V F L} {m : Mem V F L W}
    (hm : MInv sp st m) {n : Name} {g : Gen} {b : BSt V F} {e : Key} (hb : m.bld n g = some b)
    (hE : ∀ k, e < k → sp.f b.fn k (st.data k) = none) :
    MInv sp st { m with bld := upd2 m.bld n g (some { b with E := some e, pc := .read }) } := by
  have hbi := hm.bInv n g b hb
  refine hm.setB hb ⟨hbi.fnEq, ?_, ?_, ?_, ?_⟩ rfl
  · intro d hd hg k hk
    rcases hk with hk | ⟨e', he', hek⟩
    · exact hbi.cover d hd hg k (Or.inl hk)
    · cases he'
      exact Covered.of_none (hE k hek)
  · intro h; cases h
  · intro h; rcases h with h | h <;> cases h
  · intro h; cases h

/-- `BRead`: the step's values are the data at its R. -/
theorem minv_bRead {sp : Spec V F L} {st : Stream V F L} {m : Mem V F L W}
    (hm : MInv sp st m) {n : Name} {g : Gen} {b : BSt V F} {e hi : Key}
    (hb : m.bld n g = some b) (hE : b.E = some e) :
    MInv sp st { m with bld := upd2 m.bld n g (some
        { b with hi := hi, R := st.now, snap := st.data, ended := decide (hi = e + 1),
                 pc := .check }) } := by
  have hbi := hm.bInv n g b hb
  refine hm.setB hb ⟨hbi.fnEq, hbi.cover, ?_, ?_, ?_⟩ rfl
  · intro h; cases h
  · intro _
    refine ⟨Nat.le_refl _, fun _ _ => rfl, ⟨e, hE, fun h => of_decide_eq_true h⟩, ?_⟩
    intro _ _ _ k _ _ hf
    exact Covered.of_none hf
  · intro h; cases h

/-- `BCheck`: `isLive` under the lock reads the stream's definition. -/
theorem minv_bCheck {sp : Spec V F L} {st : Stream V F L} {m : Mem V F L W}
    (hm : MInv sp st m) {n : Name} {g : Gen} {b : BSt V F} {d : Def F}
    (hb : m.bld n g = some b) (hpc : b.pc = .check)
    (hl : m.lock = .free ∨ m.lock = .bld n g) (hmem : m.mem n = some d) (hdg : d.gen = g) :
    MInv sp st { m with bld := upd2 m.bld n g (some { b with pc := .commit }) } := by
  have hbi := hm.bInv n g b hb
  have hd : st.dfn n = some d := by
    rw [← hm.memEq (by rcases hl with hl | hl <;> rw [hl] <;> simp) n]; exact hmem
  refine hm.setB hb ⟨hbi.fnEq, hbi.cover, ?_, ?_, ?_⟩ rfl
  · intro h; cases h
  · intro _
    have hsi := hbi.inStep (Or.inl hpc)
    exact ⟨hsi.R_le, hsi.snap, hsi.range, hsi.noneCov⟩
  · intro _ _; exact ⟨d, hd, hdg⟩

theorem minv_bRefused {sp : Spec V F L} {st : Stream V F L} {m : Mem V F L W}
    (hm : MInv sp st m) {n : Name} {g : Gen} {b : BSt V F} (hb : m.bld n g = some b) :
    MInv sp st { m with bld := upd2 m.bld n g (some
        { b with pc := if b.locked = false ∧ sp.lockedAfter ≤ b.tries + 1 then .lock else .read,
                 tries := if b.locked = true ∨ sp.lockedAfter ≤ b.tries + 1 then 0
                          else b.tries + 1 }) } := by
  have hbi := hm.bInv n g b hb
  refine hm.setB hb ⟨hbi.fnEq, hbi.cover, ?_, ?_, ?_⟩ rfl
  · intro h; dsimp only at h; split at h <;> cases h
  · intro h; dsimp only at h; rcases h with h | h <;> (split at h <;> cases h)
  · intro h; dsimp only at h; split at h <;> cases h

theorem minv_bLock {sp : Spec V F L} {st : Stream V F L} {m : Mem V F L W}
    (hm : MInv sp st m) {n : Name} {g : Gen} {b : BSt V F} (hb : m.bld n g = some b)
    (hl : m.lock = .free) :
    MInv sp st { m with lock := .bld n g,
                        bld := upd2 m.bld n g (some { b with locked := true, pc := .read }) } := by
  have hbi := hm.bInv n g b hb
  have hid : m.admin = .idle := hm.adminIdle (by rw [hl]; simp)
  refine ⟨hm.memAgrees, ?_, hm.adminCreate, hm.adminDelete, ?_, ?_, hm.wInv, ?_, ?_, hm.cInv⟩
  · show Lock.bld n g = .mgr ↔ m.admin ≠ .idle
    rw [hid]; simp
  · intro n' g' hg'
    change Lock.bld n g = Lock.bld n' g' at hg'
    cases hg'
    exact ⟨_, upd2_same _ _ _ _, rfl⟩
  · intro n' g' b' hb' hl'
    change upd2 m.bld n g (some { b with locked := true, pc := .read }) n' g' = some b' at hb'
    show Lock.bld n g = Lock.bld n' g'
    by_cases hgg : n' = n ∧ g' = g
    · rw [hgg.1, hgg.2]
    · rw [upd2_ne _ _ hgg] at hb'
      have := hm.bLocked n' g' b' hb' hl'; rw [hl] at this; cases this
  · intro n' g' b' hb'
    change upd2 m.bld n g (some { b with locked := true, pc := .read }) n' g' = some b' at hb'
    by_cases hgg : n' = n ∧ g' = g
    · rw [hgg.1, hgg.2, upd2_same] at hb'; cases hb'; rw [hgg.1, hgg.2]
      refine ⟨hbi.fnEq, hbi.cover, ?_, ?_, ?_⟩
      · intro h; cases h
      · intro h; rcases h with h | h <;> cases h
      · intro h; cases h
    · rw [upd2_ne _ _ hgg] at hb'; exact hm.bInv n' g' b' hb'
  · intro n' g' b' hb'
    change upd2 m.bld n g (some { b with locked := true, pc := .read }) n' g' = some b' at hb'
    by_cases hgg : n' = n ∧ g' = g
    · rw [hgg.1, hgg.2]; exact hm.bLt n g b hb
    · rw [upd2_ne _ _ hgg] at hb'; exact hm.bLt n' g' b' hb'

theorem minv_bActivateFail {sp : Spec V F L} {st : Stream V F L} {m : Mem V F L W}
    (hm : MInv sp st m) {n : Name} {g : Gen} (hl : m.lock = .free) :
    MInv sp st { m with bld := upd2 m.bld n g none } := by
  have e : ({ m with bld := upd2 m.bld n g none } : Mem V F L W) =
      { m with bld := upd2 m.bld n g none, lock := .free } := by
    cases m; dsimp only at hl ⊢; rw [hl]
  rw [e]; exact hm.delB (Or.inl hl)

theorem minv_cScan {sp : Spec V F L} {st : Stream V F L} {m : Mem V F L W}
    (hm : MInv sp st m) {n : Name} {g : Gen} {c : CSt L} {keys : Key → L → Prop}
    (hc : m.cln n g = some c) :
    MInv sp st { m with cln := upd2 m.cln n g (some { c with pc := .del, keys := keys }) } :=
  hm.setC hc ⟨(hm.cInv n g c hc).marked, fun h => by cases h⟩

/-- `CScan` that finds no entry: the cleanup's end (point 6). -/
theorem minv_cScanEnd {sp : Spec V F L} {st : Stream V F L} {m : Mem V F L W}
    (hm : MInv sp st m) {n : Name} {g : Gen} {c : CSt L} (hc : m.cln n g = some c)
    (hno : ∀ k l, ¬ st.ent n g k l) :
    MInv sp st { m with cln := upd2 m.cln n g (some { c with pc := .done }) } :=
  hm.setC hc ⟨(hm.cInv n g c hc).marked, fun _ => hno⟩

/-- A build's lock released if it held it, and the build replaced by an
unlocked one. -/
theorem MInv.relB {sp : Spec V F L} {st : Stream V F L} {m : Mem V F L W}
    (hm : MInv sp st m) {n : Name} {g : Gen} {b b' : BSt V F} (hb : m.bld n g = some b)
    (hb' : BInv sp st n g b') (hl' : b'.locked = false) :
    MInv sp st { m with bld := upd2 m.bld n g (some b'),
                        lock := if b.locked = true then .free else m.lock } := by
  refine ⟨hm.memAgrees, ?_, hm.adminCreate, hm.adminDelete, ?_, ?_, hm.wInv, ?_, ?_,
    hm.cInv⟩
  · show (if b.locked = true then Lock.free else m.lock) = .mgr ↔ m.admin ≠ .idle
    by_cases hlk : b.locked = true
    · rw [ite_eq_left hlk]
      have hl := hm.bLocked n g b hb hlk
      have hid := hm.adminIdle (by rw [hl]; simp)
      rw [hid]; simp
    · rw [ite_eq_right hlk]; exact hm.lockMgr
  · intro n' g' hg'
    change (if b.locked = true then Lock.free else m.lock) = .bld n' g' at hg'
    show ∃ b'', upd2 m.bld n g (some b') n' g' = some b'' ∧ b''.locked = true
    by_cases hlk : b.locked = true
    · rw [ite_eq_left hlk] at hg'; cases hg'
    · rw [ite_eq_right hlk] at hg'
      obtain ⟨b'', hb'', hl''⟩ := hm.lockBld n' g' hg'
      by_cases hgg : n' = n ∧ g' = g
      · rw [hgg.1, hgg.2, hb] at hb''; cases hb''; exact absurd hl'' hlk
      · rw [upd2_ne _ _ hgg]; exact ⟨b'', hb'', hl''⟩
  · intro n' g' b'' hb'' hl''
    change upd2 m.bld n g (some b') n' g' = some b'' at hb''
    show (if b.locked = true then Lock.free else m.lock) = .bld n' g'
    by_cases hgg : n' = n ∧ g' = g
    · rw [hgg.1, hgg.2, upd2_same] at hb''; cases hb''; rw [hl'] at hl''; cases hl''
    · rw [upd2_ne _ _ hgg] at hb''
      have h1 := hm.bLocked n' g' b'' hb'' hl''
      by_cases hlk : b.locked = true
      · have h2 := hm.bLocked n g b hb hlk
        rw [h1] at h2; cases h2; exact absurd ⟨rfl, rfl⟩ hgg
      · rw [ite_eq_right hlk]; exact h1
  · intro n' g' b'' hb''
    change upd2 m.bld n g (some b') n' g' = some b'' at hb''
    by_cases hgg : n' = n ∧ g' = g
    · rw [hgg.1, hgg.2, upd2_same] at hb''; cases hb''; rw [hgg.1, hgg.2]; exact hb'
    · rw [upd2_ne _ _ hgg] at hb''; exact hm.bInv n' g' b'' hb''
  · intro n' g' b'' hb''
    change upd2 m.bld n g (some b') n' g' = some b'' at hb''
    by_cases hgg : n' = n ∧ g' = g
    · rw [hgg.1, hgg.2]; exact hm.bLt n g b hb
    · rw [upd2_ne _ _ hgg] at hb''; exact hm.bLt n' g' b'' hb''

/-- `bRetry`: the step again from its start, unlocked. -/
theorem minv_bRetry {sp : Spec V F L} {st : Stream V F L} {m : Mem V F L W}
    (hm : MInv sp st m) {n : Name} {g : Gen} {b : BSt V F} (hb : m.bld n g = some b) :
    MInv sp st { m with
      bld := upd2 m.bld n g (some { b with pc := .read, tries := 0, locked := false }),
      lock := if b.locked = true then .free else m.lock } := by
  have hbi := hm.bInv n g b hb
  refine hm.relB hb ⟨hbi.fnEq, hbi.cover, ?_, ?_, ?_⟩ rfl
  · intro h; cases h
  · intro h; rcases h with h | h <;> cases h
  · intro h; cases h

/-- `bAbort`: a build's thread ends; its lock released if it held it. -/
theorem minv_bAbort {sp : Spec V F L} {st : Stream V F L} {m : Mem V F L W}
    (hm : MInv sp st m) {n : Name} {g : Gen} {b : BSt V F} (hb : m.bld n g = some b) :
    MInv sp st { m with bld := upd2 m.bld n g none,
                        lock := if b.locked = true then .free else m.lock } := by
  by_cases hlk : b.locked = true
  · have hl := hm.bLocked n g b hb hlk
    have e : ({ m with bld := upd2 m.bld n g none,
                       lock := if b.locked = true then .free else m.lock } : Mem V F L W) =
        { m with bld := upd2 m.bld n g none, lock := .free } := by
      rw [ite_eq_left hlk]
    rw [e]; exact hm.delB (Or.inr hl)
  · have hl : m.lock ≠ .bld n g := fun h => by
      obtain ⟨b'', hb'', hl''⟩ := hm.lockBld n g h
      rw [hb] at hb''; cases hb''; exact hlk hl''
    have e : ({ m with bld := upd2 m.bld n g none,
                       lock := if b.locked = true then .free else m.lock } : Mem V F L W) =
        { m with bld := upd2 m.bld n g none } := by
      rw [ite_eq_right hlk]
    rw [e]
    refine ⟨hm.memAgrees, hm.lockMgr, hm.adminCreate, hm.adminDelete, ?_, ?_, hm.wInv, ?_, ?_,
      hm.cInv⟩
    · intro n' g' hg'
      obtain ⟨b'', hb'', hl''⟩ := hm.lockBld n' g' hg'
      show ∃ b, upd2 m.bld n g none n' g' = some b ∧ b.locked = true
      by_cases hgg : n' = n ∧ g' = g
      · rw [hgg.1, hgg.2] at hg'; exact absurd hg' hl
      · rw [upd2_ne _ _ hgg]; exact ⟨b'', hb'', hl''⟩
    · intro n' g' b'' hb'' hl''
      change upd2 m.bld n g none n' g' = some b'' at hb''
      by_cases hgg : n' = n ∧ g' = g
      · rw [hgg.1, hgg.2, upd2_same] at hb''; cases hb''
      · rw [upd2_ne _ _ hgg] at hb''; exact hm.bLocked n' g' b'' hb'' hl''
    · intro n' g' b'' hb''
      change upd2 m.bld n g none n' g' = some b'' at hb''
      by_cases hgg : n' = n ∧ g' = g
      · rw [hgg.1, hgg.2, upd2_same] at hb''; cases hb''
      · rw [upd2_ne _ _ hgg] at hb''; exact hm.bInv n' g' b'' hb''
    · intro n' g' b'' hb''
      change upd2 m.bld n g none n' g' = some b'' at hb''
      by_cases hgg : n' = n ∧ g' = g
      · rw [hgg.1, hgg.2, upd2_same] at hb''; cases hb''
      · rw [upd2_ne _ _ hgg] at hb''; exact hm.bLt n' g' b'' hb''

/-- `cAbort`: a cleanup's thread ends; its marker stays. -/
theorem minv_cAbort {sp : Spec V F L} {st : Stream V F L} {m : Mem V F L W}
    (hm : MInv sp st m) {n : Name} {g : Gen} :
    MInv sp st { m with cln := upd2 m.cln n g none } := by
  refine ⟨hm.memAgrees, hm.lockMgr, hm.adminCreate, ?_, hm.lockBld, hm.bLocked, hm.wInv,
    hm.bInv, hm.bLt, ?_⟩
  · intro n' g' ha
    obtain ⟨h1, h2, h3⟩ := hm.adminDelete n' g' ha
    refine ⟨h1, h2, ?_⟩
    show upd2 m.cln n g none n' g' = none
    by_cases hgg : n' = n ∧ g' = g
    · rw [hgg.1, hgg.2, upd2_same]
    · rw [upd2_ne _ _ hgg]; exact h3
  · intro n' g' c hc
    change upd2 m.cln n g none n' g' = some c at hc
    by_cases hgg : n' = n ∧ g' = g
    · rw [hgg.1, hgg.2, upd2_same] at hc; cases hc
    · rw [upd2_ne _ _ hgg] at hc; exact hm.cInv n' g' c hc

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
  refine ⟨hx, fun y hy => hall y ?_, minv_restart⟩
  rw [he]; simp [hy]

theorem inv_init (sp : Spec V F L) (d0 : Key → Option V) : Inv sp (Sys.init (W := W) d0) := by
  have hs : SInv sp (Stream.init (F := F) (L := L) d0) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro n d hd; cases hd
    · intro n g hg; cases hg
    · intro n d hd; cases hd
    · intro n d hd; cases hd
    · intro n g k l hl; exact hl.elim
    · intro n d hd; cases hd
  refine ⟨hs, ?_, minv_restart⟩
  intro _ h; cases h

variable [DecidableEq W]

/-- Every step keeps the invariant. -/
theorem inv_step {sp : Spec V F L} {s s' : Sys V F L W} {l : Lbl W} (h : Inv sp s)
    (hst : Step sp s l s') : Inv sp s' := by
  cases hst with
  | wSuffix ws nv hsuf =>
    exact h.commit (step_wSuffix h.sinv h.minv hsuf rfl rfl rfl rfl rfl rfl rfl rfl)
  | wStart w ws nv _ => exact h.setM (minv_wStart h.minv w ws nv)
  | wReadS w k ws nv R old S hw hl => exact h.setM (minv_wReadS h.minv hw hl)
  | wCommit w ws nv R old S hw hc =>
    exact h.commit (step_wCommit h.sinv h.minv hw hc rfl rfl rfl rfl rfl rfl rfl rfl)
  | wDrop w _ => exact h.setM (h.minv.setW w trivial)
  | aCreate n fn _ hl hmem =>
    exact h.commit (step_aCreate h.sinv h.minv hl hmem rfl rfl rfl rfl rfl rfl rfl rfl)
  | aCreateMap n g fn ha => exact h.setM (minv_aCreateMap h.minv ha)
  | aDelete n d _ hl hmem =>
    exact h.commit (step_aDelete h.sinv h.minv hl hmem rfl rfl rfl rfl rfl rfl rfl rfl)
  | aDeleteMap n g ha => exact h.setM (minv_aDeleteMap h.minv ha)
  | bReadE n g b e hb _ hE => exact h.setM (minv_bReadE h.minv hb hE)
  | bRead n g b e hi hb _ hE _ _ => exact h.setM (minv_bRead h.minv hb hE)
  | bCheck n g b d hb hpc hl hmem hdg =>
    exact h.setM (minv_bCheck h.minv hb hpc hl hmem hdg)
  | bCheckFail n g b _ _ hl _ => exact h.setM (h.minv.delB hl)
  | bCommit n g b hb hpc hdef hkeys =>
    exact h.commit (step_bCommit h.sinv h.minv hb hpc hdef hkeys rfl rfl rfl rfl rfl rfl rfl rfl)
  | bRefused n g b hb _ _ => exact h.setM (minv_bRefused h.minv hb)
  | bLock n g b hb _ hl => exact h.setM (minv_bLock h.minv hb hl)
  | bActivate n g b d hb hpc hl hmem hdg =>
    exact h.commit
      (step_bActivate h.sinv h.minv hb hpc hl hmem hdg rfl rfl rfl rfl rfl rfl rfl rfl)
  | bActivateFail n g b _ _ hl _ => exact h.setM (minv_bActivateFail h.minv hl)
  | bRetry n g b hb _ => exact h.setM (minv_bRetry h.minv hb)
  | bAbort n g b hb => exact h.setM (minv_bAbort h.minv hb)
  | cScan n g c keys hc _ _ _ => exact h.setM (minv_cScan h.minv hc)
  | cScanEnd n g c hc _ hno => exact h.setM (minv_cScanEnd h.minv hc hno)
  | cDel n g c hc _ =>
    exact h.commit (step_cDel h.sinv h.minv hc rfl rfl rfl rfl rfl rfl rfl rfl)
  | cEnd n g c hc hpc =>
    exact h.commit (step_cEnd h.sinv h.minv hc hpc rfl rfl rfl rfl rfl rfl rfl rfl)
  | cAbort n g c _ => exact h.setM (minv_cAbort h.minv)
  | cut j => exact ⟨h.sinv, fun x hx => h.past x (List.mem_of_mem_take hx), h.minv⟩
  | crash pre x rest he => exact inv_crash h he

/-- Every reachable system has the invariant. -/
theorem reach_inv {sp : Spec V F L} {s : Sys V F L W} (h : Reach sp s) : Inv sp s := by
  induction h with
  | init d0 => exact inv_init sp d0
  | step _ hst ih => exact inv_step ih hst

end BergDB.Index
