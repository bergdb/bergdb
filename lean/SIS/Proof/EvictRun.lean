/-
Proofs for stage 2 (bergdb item 001, WP E3), part 13: runs with eviction. Every
transaction of a run with any cache schedule appends the model's record and
leaves the model's D, and the memory keeps the invariant after every operation
(T-CACHE, for runs from a startup whose memory has the invariant; E5 adds the
restarts).
-/
import SIS.Proof.EvictTrans

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

theorem runEvict_succ (sp : Spec V T) (al : Algo V T) (ts : List (T × Bool × List CacheOp)) {j : Nat}
    (hj : j < ts.length) :
    runEvict sp al (ts.take (j + 1)) =
      (if ts[j].2.1 then
        (startup sp (evictTrans sp al (runEvict sp al (ts.take j)).2.2 (runEvict sp al (ts.take j)).1
            (runEvict sp al (ts.take j)).2.1 ts[j].1).1.S,
          evictStartup sp (evictTrans sp al (runEvict sp al (ts.take j)).2.2 (runEvict sp al (ts.take j)).1
            (runEvict sp al (ts.take j)).2.1 ts[j].1).1.S,
          (evictTrans sp al (runEvict sp al (ts.take j)).2.2 (runEvict sp al (ts.take j)).1
            (runEvict sp al (ts.take j)).2.1 ts[j].1).1.S)
      else
        ((evictTrans sp al (runEvict sp al (ts.take j)).2.2 (runEvict sp al (ts.take j)).1
            (runEvict sp al (ts.take j)).2.1 ts[j].1).1,
          ts[j].2.2.foldl (Mem.cacheOp sp (runEvict sp al (ts.take j)).2.2
            (evictTrans sp al (runEvict sp al (ts.take j)).2.2 (runEvict sp al (ts.take j)).1
              (runEvict sp al (ts.take j)).2.1 ts[j].1).1.S
            (evictTrans sp al (runEvict sp al (ts.take j)).2.2 (runEvict sp al (ts.take j)).1
              (runEvict sp al (ts.take j)).2.1 ts[j].1).1.D)
            (evictTrans sp al (runEvict sp al (ts.take j)).2.2 (runEvict sp al (ts.take j)).1
              (runEvict sp al (ts.take j)).2.1 ts[j].1).2,
          (runEvict sp al (ts.take j)).2.2)) := by
  have h1 : ts.take (j + 1) = ts.take j ++ [ts[j]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj]; rfl
  unfold runEvict
  rw [h1, List.foldl_append]
  rfl

section Run

variable {sp : Spec V T} {al : Algo V T}

/-- One transaction of a run with eviction, and its cache operations: the
model's record and D, and the invariant. -/
theorem EInv.run_step {ts : List T} (hok : RunOK sp al ts) (hph : PhysRunOK sp al ts)
    (hev : EvictRunOK sp al ts) (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) {j : Nat}
    (hjt : j < ts.length) {S0 : Stream V T} {m : Mem V} (hm : EInv sp (st sp al ts j) S0 j m)
    (ops : List CacheOp) :
    (evictTrans sp al S0 (st sp al ts j) m ts[j]).1 = st sp al ts (j + 1) ∧
      EInv sp (st sp al ts (j + 1)) S0 (j + 1)
        (ops.foldl (Mem.cacheOp sp S0 (evictTrans sp al S0 (st sp al ts j) m ts[j]).1.S
          (evictTrans sp al S0 (st sp al ts j) m ts[j]).1.D) (evictTrans sp al S0 (st sp al ts j) m ts[j]).2) := by
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
  obtain ⟨h1, h2⟩ := hm.evictTrans_ok hsp hinv hmk hlog hstep hphys hcopy htree hinv' hlog'
  refine ⟨h1, ?_⟩
  rw [h1]
  exact EInv.cacheOps hinv' ops _ h2

/-- T-CACHE for a run with eviction and no restart: from a startup memory with
the invariant, after every transaction and its cache operations the database is
the model's (the same records, D and P) and the memory has the invariant. -/
theorem TC_run {ts : List (T × Bool × List CacheOp)} (hok : RunOK sp al (ts.map (·.1)))
    (hph : PhysRunOK sp al (ts.map (·.1))) (hev : EvictRunOK sp al (ts.map (·.1)))
    (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) (hnr : ∀ p ∈ ts, p.2.1 = false)
    (h0 : EInv sp (init sp) (init sp).S 0 (evictStartup sp (init sp).S)) :
    ∀ j ≤ ts.length, (runEvict sp al (ts.take j)).1 = st sp al (ts.map (·.1)) j ∧
      (runEvict sp al (ts.take j)).2.2 = (init sp).S ∧
      EInv sp (st sp al (ts.map (·.1)) j) (init sp).S j (runEvict sp al (ts.take j)).2.1 := by
  intro j
  induction j with
  | zero =>
    intro _
    have : runEvict sp al (ts.take 0) = (init sp, evictStartup sp (init sp).S, (init sp).S) := by
      simp [runEvict]
    rw [this, st_zero]
    exact ⟨rfl, rfl, h0⟩
  | succ j ih =>
    intro hjt
    obtain ⟨e1, e2, e3⟩ := ih (by omega)
    have hjt' : j < ts.length := by omega
    have hjm : j < (ts.map (·.1)).length := by simp; omega
    rw [runEvict_succ sp al ts hjt']
    have hnrj : ts[j].2.1 = false := hnr _ (List.getElem_mem hjt')
    simp only [hnrj, Bool.false_eq_true, ↓reduceIte]
    rw [e1, e2]
    have htr : (ts.map (·.1))[j] = ts[j].1 := by simp
    have := EInv.run_step hok hph hev hj hmk hjm e3 ts[j].2.2
    rw [htr] at this
    obtain ⟨f1, f2⟩ := this
    exact ⟨f1, rfl, f2⟩

end Run

end SIS
