/-
The user indexes of BergDB 2026.4 in Lean: the theorems (bergdb 020-29).

The invariants that bergdb 020-26 checked with TLC for small bounds (its
section 3), proved for every reachable system of the model of
BergDB/Index/Model.lean: any number of keys, values, directories, index
names, writers, transactions of any keys, steps of any size, generations,
deletions, creations again and crashes, also crashes that lose committed
transactions. The proofs are in BergDB/Index/Inv.lean and
BergDB/Index/Steps.lean: an inductive invariant, `Inv`, kept by every step
(`inv_step`), after 020-26, section 4's argument.
-/
import BergDB.Index.Steps

namespace BergDB.Index

variable {V F L W : Type}

/-- A stream of a lookup time is one of the system's streams. -/
theorem at_mem {s : Sys V F L W} {t : Time} {x : Stream V F L} (hx : s.at t = some x) :
    x ∈ s.st :: s.past :=
  List.mem_of_find?_eq_some hx

/-- The latest stream is the one of the latest time. -/
theorem at_now (s : Sys V F L W) : s.at s.st.now = some s.st := by
  simp [Sys.at, List.find?]

variable [DecidableEq W]

/-- The stream's invariant holds at every lookup time. -/
theorem sinv_at {sp : Spec V F L} {s : Sys V F L W} (h : Reach sp s) {t : Time}
    {x : Stream V F L} (hx : s.at t = some x) : SInv sp x := by
  have hi := reach_inv h
  rcases List.mem_cons.mp (at_mem hx) with hx | hx
  · rw [hx]; exact hi.sinv
  · exact hi.past x hx

/-- **IndexIsFunction**, the main theorem (020-10, sections 3.4 and 9.1;
020-22's V3; 020-26, section 3): at every lookup time, the entries of every
active index are exactly f over the data at that time: (l, k) is an entry of
its generation if and only if k has a value v with f(v) = l. None is missing,
none is stale. -/
theorem index_is_function {sp : Spec V F L} {s : Sys V F L W} (h : Reach sp s) {t : Time}
    {x : Stream V F L} (hx : s.at t = some x) {n : Name} {d : Def F} (hd : x.dfn n = some d)
    (ha : d.active = true) (k : Key) (l : L) :
    x.ent n d.gen k l ↔ sp.f d.fn k (x.data k) = some l := by
  have hs := sinv_at h hx
  exact ⟨hs.noStale n d hd k l, hs.active n d hd ha k l⟩

/-- **NoStaleEntry** (020-26, section 3): at every lookup time, also while an
index builds, every entry of its live generation is f of its key's value. -/
theorem no_stale_entry {sp : Spec V F L} {s : Sys V F L W} (h : Reach sp s) {t : Time}
    {x : Stream V F L} (hx : s.at t = some x) {n : Name} {d : Def F} (hd : x.dfn n = some d)
    {k : Key} {l : L} (he : x.ent n d.gen k l) : sp.f d.fn k (x.data k) = some l :=
  (sinv_at h hx).noStale n d hd k l he

/-- **BuildCovers** (020-22's V3 while building; 020-18's F4; 020-26,
section 3): for a build of a live generation, every key it has passed, and
every key after its end key E, has exactly its entry. -/
theorem build_covers {sp : Spec V F L} {s : Sys V F L W} (h : Reach sp s) {n : Name}
    {g : Gen} {b : BSt V F} (hb : s.m.bld n g = some b) {d : Def F}
    (hd : s.st.dfn n = some d) (hg : d.gen = g) {k : Key} (hk : b.passed k) (l : L) :
    s.st.ent n g k l ↔ sp.f d.fn k (s.st.data k) = some l := by
  have hi := reach_inv h
  have hbi := hi.minv.bInv n g b hb
  have hfn := (hbi.fnEq d hd hg).1
  constructor
  · intro hl; rw [← hg] at hl; exact hi.sinv.noStale n d hd k l hl
  · intro hl; rw [hfn] at hl; exact hbi.cover d hd hg k hk l hl

/-- **GensAccounted** (020-22's V8): at every lookup time, every generation that
has entries is its name's live definition's or has a marker, so no entry is
out of every cleanup's reach. -/
theorem gens_accounted {sp : Spec V F L} {s : Sys V F L W} (h : Reach sp s) {t : Time}
    {x : Stream V F L} (hx : s.at t = some x) {n : Name} {g : Gen} {k : Key} {l : L}
    (he : x.ent n g k l) :
    (∃ d, x.dfn n = some d ∧ d.gen = g) ∨ x.mark n g = true :=
  (sinv_at h hx).accounted n g k l he

/-- **MarkerNotLive** and **StartAccepted** (V7; 020-10, section 4.5): no marker
names a live generation, so no start refuses the database, after a crash that
kept the latest time or one that lost transactions. -/
theorem start_accepted {sp : Spec V F L} {s : Sys V F L W} (h : Reach sp s) {t : Time}
    {x : Stream V F L} (hx : s.at t = some x) {n : Name} {d : Def F} (hd : x.dfn n = some d) :
    x.mark n d.gen = false :=
  (sinv_at h hx).markerNotLive n d hd

/-- **GenFresh** (020-10, section 4.3): a live generation is at most the latest
time, and the G that a creation of a name takes, the latest time and at least
1 (`Math.max(1, ...)` in the code), is in no marker, entry, build or cleanup
of a name without a live definition. So no late writer, build or cleanup of an
index reaches a new index of the name. -/
theorem gen_fresh {sp : Spec V F L} {s : Sys V F L W} (h : Reach sp s) (n : Name) :
    (∀ d, s.st.dfn n = some d → d.gen ≤ s.st.now) ∧
      (s.st.dfn n = none →
        s.st.mark n (max 1 s.st.now) = false ∧ (∀ k l, ¬ s.st.ent n (max 1 s.st.now) k l) ∧
          s.m.bld n (max 1 s.st.now) = none ∧ s.m.cln n (max 1 s.st.now) = none) := by
  have hi := reach_inv h
  have hs := hi.sinv
  refine ⟨hs.gen_le n, fun hn => ?_⟩
  have hmk : s.st.mark n (max 1 s.st.now) = false := by
    cases hm : s.st.mark n (max 1 s.st.now) with
    | false => rfl
    | true => have := hs.mark_lt _ _ hm; omega
  refine ⟨hmk, ?_, ?_, ?_⟩
  · intro k l hl
    rcases hs.accounted _ _ k l hl with ⟨d, hd, _⟩ | hm
    · rw [hn] at hd; cases hd
    · rw [hmk] at hm; cases hm
  · cases hb : s.m.bld n (max 1 s.st.now) with
    | none => rfl
    | some b =>
      rcases hi.minv.bLt _ _ b hb with h1 | ⟨d, hd, _⟩
      · omega
      · rw [hn] at hd; cases hd
  · cases hc : s.m.cln n (max 1 s.st.now) with
    | none => rfl
    | some c =>
      have := (hi.minv.cInv _ _ c hc).marked
      rw [hmk] at this; cases this

/-- **MemAgrees** (020-10, section 5.2): when no definition change is under way,
the manager's maps are the stream's definitions. -/
theorem mem_agrees {sp : Spec V F L} {s : Sys V F L W} (h : Reach sp s)
    (ha : s.m.admin = .idle) (n : Name) : s.m.mem n = s.st.dfn n := by
  rcases (reach_inv h).minv.memAgrees n with h1 | h1
  · exact h1
  · rw [ha] at h1; cases h1

/-- **LockSane** (020-26, section 3): the lock is held by a definition change
exactly while one is under way, and by a build exactly in its locked phase. -/
theorem lock_sane {sp : Spec V F L} {s : Sys V F L W} (h : Reach sp s) :
    (s.m.lock = .mgr ↔ s.m.admin ≠ .idle) ∧
      ∀ n g, s.m.lock = .bld n g ↔ ∃ b, s.m.bld n g = some b ∧ b.locked = true := by
  have hm := (reach_inv h).minv
  refine ⟨hm.lockMgr, fun n g => ⟨hm.lockBld n g, ?_⟩⟩
  rintro ⟨b, hb, hl⟩
  exact hm.bLocked n g b hb hl

/-- A cleanup ends only when its generation has no entry, and no entry of a
generation with a marker is put again (020-26, section 4, point 6): a cleanup
at its end leaves no entry of its generation. -/
theorem cleanup_done_empty {sp : Spec V F L} {s : Sys V F L W} (h : Reach sp s) {n : Name}
    {g : Gen} {c : CSt L} (hc : s.m.cln n g = some c) (hpc : c.pc = .done) (k : Key) (l : L) :
    ¬ s.st.ent n g k l :=
  ((reach_inv h).minv.cInv n g c hc).empty hpc k l

/-- The index set a writer read for a key, if the virtual key of the key's
directory was not written after its R, agrees with the definitions for that
directory (020-26, section 4, points 1 and 2): after a definition change, no
writer commits with the index set from before it. -/
theorem writer_sees_live {sp : Spec V F L} {s : Sys V F L W} (h : Reach sp s) {w : W}
    {ws : Key → Bool} {nv : Key → Option V} {R : Time} {old : Key → Option V}
    {S : Key → Option (Name → Option (Def F))} (hw : s.m.wr w = .run ws nv R old S)
    {k : Key} {mm : Name → Option (Def F)} (hk : S k = some mm)
    (hv : s.st.wv (sp.dirOf k) ≤ R) (n : Name) :
    sameOn sp (sp.dirOf k) (mm n) (s.st.dfn n) := by
  have hwi := (reach_inv h).minv.wInv w
  rw [hw] at hwi
  exact hwi.2.2 k mm hk hv n

end BergDB.Index
