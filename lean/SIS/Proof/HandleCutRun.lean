/-
Proofs about reclaim with handles (bergdb 005-62), part 3 of T9 over handles:
T9's invariant (`CInvH`) along a run with handles, reads, evictions and
restarts. The startup with handles gives it; each transaction and its
operations keep it. So, after a safe cut, a read through the handles at a time
from the first available time on gives the same on the cut stream as on the
whole stream: `t9_handles`.
-/
import SIS.Proof.HandleCutTrans
import SIS.HandleReclaimTheorems
import SIS.Proof.PhysAssumptions

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

section Run

variable {sp : Spec V T} {al : Algo V T}

/-- The startup with handles from the stream after T(k) gives T9's invariant:
every pointer holds a canonical object or has its pointee's latest version as
its slow path's reference, and the root's pointers to the nodes of D hold their
canonical objects. -/
theorem cinvH_startup {ts : List T} (hok : RunOK sp al ts) (hph : PhysRunOK sp al ts)
    (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) (hev : EvictRunOK sp al ts) {k : Nat}
    (hk : k ≤ ts.length) :
    CInvH sp (st sp al ts k) (st sp al ts k).S (handleStartup sp (st sp al ts k).S) := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hinv := inv_st sp al ts hok hst k hk
  obtain ⟨-, -, hptrs, hroot⟩ := heinv_hinvH_startup hok hph hj hmk hev hk
  refine ⟨?_, ?_, ?_⟩
  · intro a o ho _ _ _ v hv y p r0 hp hr0
    rcases hptrs a o y p ho hp with h | h
    · exact Or.inl h
    · right
      obtain ⟨u, hu, hle⟩ := hinv.ref_le_lv hv hr0
      rw [hu] at h
      exact ⟨u.recNo, h, hle⟩
  · intro _ o ho y p hp _ hyD
    exact hroot o y p ho hp hyD
  · intro _ o ho y p hp _ _ u hu
    rcases hptrs _ o y p ho hp with h | h
    · exact Or.inl h
    · right
      rw [hu] at h
      exact ⟨u.recNo, h, Nat.le_refl _⟩

/-- One transaction of a run with handles, and its operations, keep T9's
invariant. -/
theorem CInvH.run_step {ts : List T} (hok : RunOK sp al ts) (hph : PhysRunOK sp al ts)
    (hev : EvictRunOK sp al ts) (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) {j : Nat}
    (hjt : j < ts.length) {S0 : Stream V T} {m : HMem V} (hm : HEInv sp (st sp al ts j) S0 j m)
    (hc : CInvH sp (st sp al ts j) S0 m) (ops : List HCacheOp) :
    CInvH sp (st sp al ts (j + 1)) S0
      (ops.foldl (HMem.cacheOp sp S0 (handleTrans sp al S0 (st sp al ts j) m ts[j]).1.S
        (handleTrans sp al S0 (st sp al ts j) m ts[j]).1.D) (handleTrans sp al S0 (st sp al ts j) m ts[j]).2) := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hsp := hok.1
  have hinv := inv_st sp al ts hok hst j (by omega)
  have hinv' := inv_st sp al ts hok hst (j + 1) (by omega)
  have hlog := evLogic_st sp al ts hok hj hmk hev j (by omega)
  have hlog' := evLogic_st sp al ts hok hj hmk hev (j + 1) (by omega)
  have hcx : (parts sp al (st sp al ts j) ts[j]).c = sp.exec ts[j] (j + 1) (view sp (st sp al ts j).P j) := by
    rw [parts_c, hinv.len, Nat.add_sub_cancel]
  have hstep : StepOK sp (st sp al ts j).P (j + 1) (parts sp al (st sp al ts j) ts[j]).c := by
    rw [hcx]; exact hok.2 j hjt
  have hphys : PhysStep sp (st sp al ts j).P (j + 1) (parts sp al (st sp al ts j) ts[j]).c := by
    rw [hcx]; exact hph j hjt
  have hcopy : CopyStep sp (st sp al ts j).P (j + 1) (parts sp al (st sp al ts j) ts[j]).c := by
    rw [hcx]; exact hev.2 j hjt
  have htree : treeAt sp (st sp al ts j).P j := (hev.1 j (by omega)).tree
  rw [st_succ sp al ts hjt] at hinv' hlog' ⊢
  obtain ⟨h1, h2⟩ := hm.handleTrans_ok hsp hinv hmk hlog hstep hphys hcopy htree hinv' hlog'
  have h3 := CInvH.handleTrans_ok hsp hinv hmk hm hc hlog hstep hphys hcopy htree hinv'
  rw [h1]
  exact CInvH.cacheOps hinv' ops _ h2 h3

/-- `HandleInvR` with T9's invariant, for the stream of the last startup. -/
def HandleInvC (sp : Spec V T) (al : Algo V T) (ts : List (T × Bool × List HCacheOp)) (j : Nat)
    (r : DB V T × HMem V × Stream V T) : Prop :=
  HandleInvR sp al ts j r ∧ CInvH sp (st sp al (ts.map (·.1)) j) r.2.2 r.2.1

/-- One transaction of a run with handles and restarts, and its operations or its
restart, keeps `HandleInvC`. -/
theorem handleInvC_step {ts : List (T × Bool × List HCacheOp)} (hok : RunOK sp al (ts.map (·.1)))
    (hph : PhysRunOK sp al (ts.map (·.1))) (hev : EvictRunOK sp al (ts.map (·.1)))
    (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) {j : Nat} (hjt : j < ts.length)
    {acc : DB V T × HMem V × Stream V T} (hI : HandleInvC sp al ts j acc) :
    HandleInvC sp al ts (j + 1)
      (if ts[j].2.1 then
        (startup sp (handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S,
          handleStartup sp (handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S,
          (handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S)
      else
        ((handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1,
          ts[j].2.2.foldl (HMem.cacheOp sp acc.2.2 (handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S
            (handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.D) (handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).2,
          acc.2.2)) := by
  obtain ⟨hR, hC⟩ := hI
  refine ⟨handleInvR_step hok hph hev hj hmk hjt hR, ?_⟩
  obtain ⟨k1, -, hS0, hrel, hm, -⟩ := hR
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hjm : j < (ts.map (·.1)).length := by simp; omega
  have htr : (ts.map (·.1))[j] = ts[j].1 := by simp
  obtain ⟨hrel1, hmem1⟩ := handleTrans_congr sp al hst acc.2.2 hrel acc.2.1 ts[j].1
  rw [← hS0] at hm
  have hrunC := CInvH.run_step hok hph hev hj hmk hjm hm hC ts[j].2.2
  have hrun := HEInv.run_step hok hph hev hj hmk hjm hm ts[j].2.2
  rw [htr] at hrunC hrun
  obtain ⟨f1, -⟩ := hrun
  have hrel' : Rel (handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1 (st sp al (ts.map (·.1)) (j + 1)) := by
    rw [← f1]; exact hrel1
  split
  · show CInvH sp _ (handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S
      (handleStartup sp (handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S)
    rw [hrel'.1]
    exact cinvH_startup hok hph hj hmk hev (by simp; omega)
  · show CInvH sp _ acc.2.2 (ts[j].2.2.foldl (HMem.cacheOp sp acc.2.2
      (handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S
      (handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.D) (handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).2)
    rw [hrel1.1, hrel1.2.1, hmem1]
    exact hrunC

/-- `HandleInvC` holds after every prefix of a run with handles and restarts. -/
theorem handleInvC_all {ts : List (T × Bool × List HCacheOp)} (hok : RunOK sp al (ts.map (·.1)))
    (hph : PhysRunOK sp al (ts.map (·.1))) (hev : EvictRunOK sp al (ts.map (·.1)))
    (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) :
    ∀ j ≤ ts.length, HandleInvC sp al ts j (runHandles sp al (ts.take j)) := by
  intro j
  induction j with
  | zero =>
    intro _
    have h0 : runHandles sp al (ts.take 0) = (init sp, handleStartup sp (init sp).S, (init sp).S) := by
      simp [runHandles]
    refine ⟨handleInvR_all hok hph hev hj hmk 0 (Nat.zero_le _), ?_⟩
    rw [h0]
    have := cinvH_startup hok hph hj hmk hev (k := 0) (Nat.zero_le _)
    rw [st_zero] at this
    rw [st_zero]
    exact this
  | succ j ih =>
    intro hjt
    rw [runHandles_succ sp al ts (by omega)]
    exact handleInvC_step hok hph hev hj hmk (by omega) (ih (by omega))

/-- T9's proof over handles: in a run with handles, reads, evictions and
restarts, after j transactions, with a safe cut at c, a read through the handles
at a time from the first available time on gives the same on the stream cut at c
as on the whole stream. -/
theorem readCutH (ts : List (T × Bool × List HCacheOp)) (hok : RunOK sp al (ts.map (·.1)))
    (hph : PhysRunOK sp al (ts.map (·.1))) (hev : EvictRunOK sp al (ts.map (·.1)))
    (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) (j : Nat) (hjt : j ≤ ts.length) {c : Nat}
    (hcut : CutOK sp c (run sp al ((ts.take j).map (·.1))) j) {t : Time}
    (hft : lastFa (run sp al ((ts.take j).map (·.1))).S ≤ t) (ht : t ≤ j) :
    (runHandles sp al (ts.take j)).2.1.read sp (runHandles sp al (ts.take j)).2.2
        (cutStream c (run sp al ((ts.take j).map (·.1))).S) t =
      (runHandles sp al (ts.take j)).2.1.read sp (runHandles sp al (ts.take j)).2.2
        (run sp al ((ts.take j).map (·.1))).S t := by
  obtain ⟨⟨k1, -, hS0, -, hm, hh⟩, hc⟩ := handleInvC_all hok hph hev hj hmk j hjt
  have hst : st sp al (ts.map (·.1)) j = run sp al ((ts.take j).map (·.1)) := by
    show run sp al ((ts.map (·.1)).take j) = run sp al ((ts.take j).map (·.1))
    rw [List.map_take]
  have hinv := inv_st sp al (ts.map (·.1)) hok (algOK_of sp al (Or.inl hj)) j (by rw [List.length_map]; exact hjt)
  rw [hst] at hm hh hc hinv
  rw [← hS0] at hm hh
  exact CInvH.read_cut hinv hok.1.liveSub hm hh hc hcut hft ht

end Run

/-- `T9_handles` (SIS/HandleReclaimTheorems.lean) holds: in a run with handles,
after any transaction and its operations or its restart, with a safe cut at c, a
read through the handles at a time from the first available time on gives the
same on the cut stream as on the whole stream, and gives P at that time. -/
theorem t9_handles (sp : Spec V T) (al : Algo V T) : T9_handles sp al := by
  intro ts hok hla hev hj hmk j hjt c t db r m hcut hft ht
  have hph := physRunOK_of_evict hok hla hev
  have he : m.read sp r.2.2 (cutStream c db.S) t = m.read sp r.2.2 db.S t :=
    readCutH ts hok hph hev hj hmk j hjt hcut hft ht
  rw [he]
  exact ⟨rfl, tr_handles_restarts sp al ts hok hla hev hj hmk j hjt t ht⟩

end SIS
