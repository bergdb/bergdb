/-
Proofs about the physical layer, part 15: T1-L, the lazy startup and the
reads and writer follows after it (bergdb item 001, WP L3).
-/
import SIS.Proof.PhysBase

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

section Ops

variable {sp : Spec V T} {db dbK : DB V T} {k : Nat}

/-- Reads at times up to k and the writer's follows keep the invariant at k. -/
theorem MemInv.ops_ok (hctx : PCtx sp db k) (hk : KCtx sp db dbK k) :
    ∀ (ops : List Op) (m : Mem V), MemInv sp db k m → OpsOK sp db.S db.P k m ops →
      MemInv sp db k (ops.foldl (Mem.step sp db.S) m) := by
  intro ops
  induction ops with
  | nil => intro m hm _; exact hm
  | cons op ops ih =>
    intro m hm hops
    simp only [List.foldl_cons]
    cases op with
    | read t =>
      unfold OpsOK at hops
      obtain ⟨ht, hops'⟩ := hops
      exact ih _ (hm.read_ok hctx hk.fixedLe ht).1 hops'
    | write h y =>
      unfold OpsOK at hops
      obtain ⟨⟨o, ho, hc, hr, hy⟩, hops'⟩ := hops
      obtain ⟨m', h1, heq, hm', -, -⟩ := hm.follow_writer hctx hk ho hc hr hy
      apply ih _ _ hops'
      show MemInv sp db k (m.follow sp db.S h y true).1
      rw [heq]; exact hm'

/-- What the invariant at the last time k says: reads give P, the objects. -/
theorem MemInv.t1_facts {m : Mem V} (hm : MemInv sp db k m) (hctx : PCtx sp db k)
    (hk : KCtx sp db dbK k) :
    (∀ t ≤ k, (m.read sp db.S t).2 =
      (reachList sp db.P t).map (fun z => (z, ((db.P.get? z).map (·.hist.upTo t)).getD []))) ∧
    (∀ h o, m.obj? h = some o → o.canonical = true → (db.P.get? o.node).map (·.hist) = some o.hist) ∧
    (∀ h o, m.obj? h = some o → o.canonical = false → ∃ r w, o.pos = some r ∧
      db.S.versionAt r o.node = some w ∧ (o.hist = w.hist ∨ o.hist = w.hist.upTo (lastSp db.S))) ∧
    (∀ h o, m.obj? h = some o → o.canonical = true → ∀ t ≤ k, reachable sp db.P t o.node = true →
      ∀ y ∈ sp.live (o.hist.upTo t), ∀ h', o.slot? y = some (Slot.mem h') →
        ∃ o', m.obj? h' = some o' ∧ o'.node = y ∧ (o'.canonical = true ∨
          ∃ r w, o'.pos = some r ∧ db.S.versionAt r y = some w ∧
            (o'.hist = w.hist → good sp db.S db.P t w = true))) := by
  refine ⟨fun t ht => (hm.read_ok hctx hk.fixedLe ht).2.2, ?_, ?_, ?_⟩
  · intro h o ho hc
    obtain ⟨-, ⟨n, hn, hh, -, -⟩, -⟩ := hm.canon h o ho hc
    rw [hn, hh, upTo_of_forall _ _ (hctx.inv.times o.node n hn)]
    rfl
  · intro h o ho hc
    obtain ⟨w, ⟨r, hp, hv, -, -, h5⟩, -⟩ := hm.snap h o ho hc
    refine ⟨r, w, hp, hv, ?_⟩
    rcases h5 with ⟨h6, -⟩ | ⟨h6, -⟩
    · exact Or.inl h6
    · exact Or.inr h6
  · intro h o ho hc t ht hr y hy h' hsl
    obtain ⟨-, -, -, c4, -⟩ := hm.canon h o ho hc
    obtain ⟨sl, hsl', hg⟩ := c4 t ht hr y hy
    rw [hsl, Option.some.injEq] at hsl'
    subst hsl'
    obtain ⟨o', ho', hy', hc'⟩ := hg
    refine ⟨o', ho', hy', ?_⟩
    rcases hc' with hc' | ⟨w, ⟨r, hp, hv, -, -, -⟩, hg'⟩
    · exact Or.inl hc'
    · exact Or.inr ⟨r, w, hp, by rw [← hy']; exact hv, hg'⟩

end Ops

section Run

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

/-- The lazy startup from the stream after T(k) meets the invariant at k. -/
theorem lazy_ok (hok : RunOK sp al ts) (hph : PhysRunOK sp al ts) (hj : al.stillDirty = javaTest sp)
    {k : Nat} (hk : k ≤ ts.length) :
    MemInv sp (st sp al ts k) k (lazyStartup sp (st sp al ts k).S) := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hctx := pctx_st hok hst hk
  have hsk : lastSp (st sp al ts k).S ≤ k := by have := hctx.inv.spLt; omega
  have hkS := kctx_st sp al ts hok hj hsk hk
  rw [lazyStartup_eq]
  exact rerun_fold_ok hok hph hj hk (hctx.base_ok hkS) (base_sameNodes sp al ts hok hst hk)

/-- T1-L, strong form: after the lazy startup from the stream after T(k) and
admissible operations, the invariant holds at k, and with it what T1-L says. -/
theorem T1_lazy_strong (hok : RunOK sp al ts) (hph : PhysRunOK sp al ts)
    (hj : al.stillDirty = javaTest sp) {k : Nat} (hk : k ≤ ts.length) (ops : List Op)
    (hops : OpsOK sp (st sp al ts k).S (st sp al ts k).P k (lazyStartup sp (st sp al ts k).S) ops) :
    MemInv sp (st sp al ts k) k
        (ops.foldl (Mem.step sp (st sp al ts k).S) (lazyStartup sp (st sp al ts k).S)) ∧
      PCtx sp (st sp al ts k) k ∧ KCtx sp (st sp al ts k) (st sp al ts k) k := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hctx := pctx_st hok hst hk
  have hkk := kctx_st sp al ts hok hj (Nat.le_refl k) hk
  exact ⟨MemInv.ops_ok hctx hkk ops _ (lazy_ok hok hph hj hk) hops, hctx, hkk⟩

end Run

end SIS
