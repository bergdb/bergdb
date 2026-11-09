/-
The user indexes of BergDB 2026.4 in Lean: the theorems (bergdb 020-29).

The invariants that bergdb 020-26 checked with TLC for small bounds (its
section 3), proved for every reachable system of the model of
BergDB/Index/Model.lean: any number of keys, values, writers, steps of any
size, generations, deletions, creations again and crashes, also crashes that
lose committed transactions. The proofs are in BergDB/Index/Inv.lean and
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
020-22's V3; 020-26, section 3): at every lookup time, the entries of an
active index are exactly f over the directory's values at that time: (l, k)
is an entry of its generation if and only if k has a value v with
f(v) = l. None is missing, none is stale. -/
theorem index_is_function {sp : Spec V F L} {s : Sys V F L W} (h : Reach sp s) {t : Time}
    {x : Stream V F L} (hx : s.at t = some x) {d : Def F} (hd : x.dfn = some d)
    (ha : d.active = true) (k : Key) (l : L) :
    x.ent d.gen k l ↔ sp.f d.fn k (x.data k) = some l := by
  have hs := sinv_at h hx
  exact ⟨hs.noStale d hd k l, hs.active d hd ha k l⟩

/-- **NoStaleEntry** (020-26, section 3): at every lookup time, also while the
index builds, every entry of the live generation is f of its key's value. -/
theorem no_stale_entry {sp : Spec V F L} {s : Sys V F L W} (h : Reach sp s) {t : Time}
    {x : Stream V F L} (hx : s.at t = some x) {d : Def F} (hd : x.dfn = some d)
    {k : Key} {l : L} (he : x.ent d.gen k l) : sp.f d.fn k (x.data k) = some l :=
  (sinv_at h hx).noStale d hd k l he

/-- **BuildCovers** (020-22's V3 while building; 020-18's F4; 020-26,
section 3): for a build of the live generation, every key it has passed, and
every key after its end key E, has exactly its entry. -/
theorem build_covers {sp : Spec V F L} {s : Sys V F L W} (h : Reach sp s) {g : Gen}
    {b : BSt V F} (hb : s.m.bld g = some b) {d : Def F} (hd : s.st.dfn = some d)
    (hg : d.gen = g) {k : Key} (hk : b.passed k) (l : L) :
    s.st.ent g k l ↔ sp.f d.fn k (s.st.data k) = some l := by
  have hi := reach_inv h
  have hbi := hi.minv.bInv g b hb
  have hfn := (hbi.fnEq d hd hg).1
  constructor
  · intro hl; rw [← hg] at hl; exact hi.sinv.noStale d hd k l hl
  · intro hl; rw [hfn] at hl; exact hbi.cover d hd hg k hk l hl

/-- **GensAccounted** (020-22's V8): at every lookup time, every generation that
has entries is the live definition's or has a marker, so no entry is out of
every cleanup's reach. -/
theorem gens_accounted {sp : Spec V F L} {s : Sys V F L W} (h : Reach sp s) {t : Time}
    {x : Stream V F L} (hx : s.at t = some x) {g : Gen} {k : Key} {l : L} (he : x.ent g k l) :
    (∃ d, x.dfn = some d ∧ d.gen = g) ∨ x.mark g = true :=
  (sinv_at h hx).accounted g k l he

/-- **MarkerNotLive** and **StartAccepted** (V7; 020-10, section 4.5): no marker
names the live generation, so no start refuses the database, after a crash
that kept the latest time or one that lost transactions. -/
theorem start_accepted {sp : Spec V F L} {s : Sys V F L W} (h : Reach sp s) {t : Time}
    {x : Stream V F L} (hx : s.at t = some x) {d : Def F} (hd : x.dfn = some d) :
    x.mark d.gen = false :=
  (sinv_at h hx).markerNotLive d hd

/-- **GenFresh** (020-10, section 4.3): the G that a creation takes, the latest
transaction's time, is new: no definition, marker, entry, build or cleanup
has it. So no late writer, build or cleanup of an index reaches a new index of
the name. -/
theorem gen_fresh {sp : Spec V F L} {s : Sys V F L W} (h : Reach sp s) :
    (∀ d, s.st.dfn = some d → d.gen ≠ s.st.now) ∧ s.st.mark s.st.now = false ∧
      (∀ k l, ¬ s.st.ent s.st.now k l) ∧ s.m.bld s.st.now = none ∧
      s.m.cln s.st.now = none := by
  have hi := reach_inv h
  have hs := hi.sinv
  have hmk : s.st.mark s.st.now = false := by
    cases hm : s.st.mark s.st.now with
    | false => rfl
    | true => exact absurd (hs.mark_lt _ hm) (Nat.lt_irrefl _)
  refine ⟨fun d hd he => absurd (hs.gen_lt d hd) (by rw [he]; exact Nat.lt_irrefl _), hmk,
    ?_, ?_, ?_⟩
  · intro k l hl
    rcases hs.accounted _ k l hl with ⟨d, hd, hg⟩ | hm
    · exact absurd (hs.gen_lt d hd) (by rw [hg]; exact Nat.lt_irrefl _)
    · rw [hmk] at hm; cases hm
  · cases hb : s.m.bld s.st.now with
    | none => rfl
    | some b => exact absurd (hi.minv.bLt _ b hb) (Nat.lt_irrefl _)
  · cases hc : s.m.cln s.st.now with
    | none => rfl
    | some c =>
      have := (hi.minv.cInv _ c hc).marked
      rw [hmk] at this; cases this

/-- **MemAgrees** (020-10, section 5.2): when no definition change is under way,
the manager's maps are the stream's definition. -/
theorem mem_agrees {sp : Spec V F L} {s : Sys V F L W} (h : Reach sp s)
    (ha : s.m.admin = .idle) : s.m.mem = s.st.dfn :=
  (reach_inv h).minv.memAgrees ha

/-- **LockSane** (020-26, section 3): the lock is held by a definition change
exactly while one is under way, and by a build exactly in its locked phase. -/
theorem lock_sane {sp : Spec V F L} {s : Sys V F L W} (h : Reach sp s) :
    (s.m.lock = .mgr ↔ s.m.admin ≠ .idle) ∧
      ∀ g, s.m.lock = .bld g ↔ ∃ b, s.m.bld g = some b ∧ b.locked = true := by
  have hm := (reach_inv h).minv
  refine ⟨hm.lockMgr, fun g => ⟨hm.lockBld g, ?_⟩⟩
  rintro ⟨b, hb, hl⟩
  exact hm.bLocked g b hb hl

/-- A cleanup ends only when its generation has no entry, and no entry of a
generation with a marker is put again (020-26, section 4, point 6): a cleanup
at its end leaves no entry of its generation. -/
theorem cleanup_done_empty {sp : Spec V F L} {s : Sys V F L W} (h : Reach sp s) {g : Gen}
    {c : CSt L} (hc : s.m.cln g = some c) (hpc : c.pc = .done) (k : Key) (l : L) :
    ¬ s.st.ent g k l :=
  ((reach_inv h).minv.cInv g c hc).empty hpc k l

/-- A writer's transaction in flight that the Core will accept (its virtual key
not written since R) read the live index (020-26, section 4, points 1 and 2):
after a definition change, no writer commits with the index set from before
it. -/
theorem writer_sees_live {sp : Spec V F L} {s : Sys V F L W} (h : Reach sp s) {w : W}
    {k : Key} {v : Option V} {R : Time} {old : Option V} {S : Option (Def F)}
    (hw : s.m.wr w = .commit k v R old S) (hv : s.st.wv ≤ R) : sameIdx S s.st.dfn := by
  have hwi := (reach_inv h).minv.wInv w
  rw [hw] at hwi
  exact hwi.2.2 hv

end BergDB.Index
