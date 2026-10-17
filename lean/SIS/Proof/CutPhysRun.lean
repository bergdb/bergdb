/-
Proofs about reclaim, part 15 (bergdb item 001, WP R4, T9): T9's invariant
(`CInv`) along a run with eviction, cache operations and restarts. The Level 4
startup gives it; each transaction and its cache operations keep it. So, after
a safe cut, a physical read at a time from the first available time on gives
the same on the cut stream as on the whole stream.
-/
import SIS.Proof.CutPhysTrans
import SIS.Proof.EvictRestart

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

section Run

variable {sp : Spec V T} {al : Algo V T}

/-- The Level 4 startup from the stream after T(k) gives T9's invariant: every
object is canonical, every slot serializes its pointee's latest version, and a
slot of the root's object for a node of D is a memory slot to its canonical
object. -/
theorem cinv_startup {ts : List T} (hok : RunOK sp al ts) (hph : PhysRunOK sp al ts)
    (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) (hev : EvictRunOK sp al ts) {k : Nat}
    (hk : k ≤ ts.length) :
    CInv sp (st sp al ts k) (st sp al ts k).S (evictStartup sp (st sp al ts k).S) := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hinv := inv_st sp al ts hok hst k hk
  obtain ⟨-, -, hcan, hser, hpin, hmem⟩ := einv_hinv_startup_facts hok hph hj hmk hev hk
  constructor
  · -- mono
    intro h o ho _ _ _ v hv y sl r0 hsl hr0
    obtain ⟨u, hu, hle⟩ := hinv.ref_le_lv hv hr0
    exact Or.inr ⟨u.recNo, by rw [hser h o y sl ho hsl, hu]; rfl, hle⟩
  · -- pinSnap: there are no snapshots
    intro _ _ _ _ _ _ h' o' _ _ ho' hco' _
    rw [hcan h' o' ho'] at hco'; cases hco'
  · -- rootD
    intro _ o ho y sl hsl _ hyD
    cases sl with
    | mem h' => exact ⟨h', rfl, hmem _ o y h' ho hsl⟩
    | stream r => exact absurd rfl (hpin _ o y r ho hsl hyD).2
  · -- rootClean
    intro _ o ho y sl hsl _ _
    exact hser _ o y sl ho hsl
  · -- snapND: there are no snapshots
    intro h o _ ho hco
    rw [hcan h o ho] at hco; cases hco

/-- One transaction of a run with eviction, and its cache operations, keep T9's
invariant. -/
theorem CInv.run_step {ts : List T} (hok : RunOK sp al ts) (hph : PhysRunOK sp al ts)
    (hev : EvictRunOK sp al ts) (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) {j : Nat}
    (hjt : j < ts.length) {S0 : Stream V T} {m : Mem V} (hm : EInv sp (st sp al ts j) S0 j m)
    (hc : CInv sp (st sp al ts j) S0 m) (ops : List CacheOp) :
    CInv sp (st sp al ts (j + 1)) S0
      (ops.foldl (Mem.cacheOp sp S0 (evictTrans sp al S0 (st sp al ts j) m ts[j]).1.S
        (evictTrans sp al S0 (st sp al ts j) m ts[j]).1.D) (evictTrans sp al S0 (st sp al ts j) m ts[j]).2) := by
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
  obtain ⟨h1, h2⟩ := hm.evictTrans_ok hsp hinv hmk hlog hstep hphys hcopy htree hinv' hlog'
  have h3 := CInv.evictTrans_ok hsp hinv hmk hm hc hlog hstep hphys hcopy htree hinv' hlog'
  rw [h1]
  exact CInv.cacheOps hinv' ops _ h2 h3

/-- `EvictInvR` with T9's invariant, for the stream of the last startup. -/
def EvictInvC (sp : Spec V T) (al : Algo V T) (ts : List (T × Bool × List CacheOp)) (j : Nat)
    (r : DB V T × Mem V × Stream V T) : Prop :=
  EvictInvR sp al ts j r ∧ CInv sp (st sp al (ts.map (·.1)) j) r.2.2 r.2.1

/-- One transaction of a run with eviction and restarts, and its cache
operations or its restart, keeps `EvictInvC`. -/
theorem evictInvC_step {ts : List (T × Bool × List CacheOp)} (hok : RunOK sp al (ts.map (·.1)))
    (hph : PhysRunOK sp al (ts.map (·.1))) (hev : EvictRunOK sp al (ts.map (·.1)))
    (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) {j : Nat} (hjt : j < ts.length)
    {acc : DB V T × Mem V × Stream V T} (hI : EvictInvC sp al ts j acc) :
    EvictInvC sp al ts (j + 1)
      (if ts[j].2.1 then
        (startup sp (evictTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S,
          evictStartup sp (evictTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S,
          (evictTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S)
      else
        ((evictTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1,
          ts[j].2.2.foldl (Mem.cacheOp sp acc.2.2 (evictTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S
            (evictTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.D) (evictTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).2,
          acc.2.2)) := by
  obtain ⟨hR, hC⟩ := hI
  refine ⟨evictInvR_step hok hph hev hj hmk hjt hR, ?_⟩
  obtain ⟨k1, -, hS0, hrel, hm, -⟩ := hR
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hjm : j < (ts.map (·.1)).length := by simp; omega
  have htr : (ts.map (·.1))[j] = ts[j].1 := by simp
  obtain ⟨hrel1, hmem1⟩ := evictTrans_congr sp al hst acc.2.2 hrel acc.2.1 ts[j].1
  rw [← hS0] at hm
  have hrunC := CInv.run_step hok hph hev hj hmk hjm hm hC ts[j].2.2
  have hrun := EInv.run_step hok hph hev hj hmk hjm hm ts[j].2.2
  rw [htr] at hrunC hrun
  obtain ⟨f1, -⟩ := hrun
  have hrel' : Rel (evictTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1 (st sp al (ts.map (·.1)) (j + 1)) := by
    rw [← f1]; exact hrel1
  split
  · show CInv sp _ (evictTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S
      (evictStartup sp (evictTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S)
    rw [hrel'.1]
    exact cinv_startup hok hph hj hmk hev (by simp; omega)
  · show CInv sp _ acc.2.2 (ts[j].2.2.foldl (Mem.cacheOp sp acc.2.2 (evictTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S
      (evictTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.D) (evictTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).2)
    rw [hrel1.1, hrel1.2.1, hmem1]
    exact hrunC

/-- `EvictInvC` holds after every prefix of a run with eviction and restarts. -/
theorem evictInvC_all {ts : List (T × Bool × List CacheOp)} (hok : RunOK sp al (ts.map (·.1)))
    (hph : PhysRunOK sp al (ts.map (·.1))) (hev : EvictRunOK sp al (ts.map (·.1)))
    (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) :
    ∀ j ≤ ts.length, EvictInvC sp al ts j (runEvict sp al (ts.take j)) := by
  intro j
  induction j with
  | zero =>
    intro _
    have h0 : runEvict sp al (ts.take 0) = (init sp, evictStartup sp (init sp).S, (init sp).S) := by
      simp [runEvict]
    refine ⟨evictInvR_all hok hph hev hj hmk 0 (Nat.zero_le _), ?_⟩
    rw [h0]
    have := cinv_startup hok hph hj hmk hev (k := 0) (Nat.zero_le _)
    rw [st_zero] at this
    rw [st_zero]
    exact this
  | succ j ih =>
    intro hjt
    rw [runEvict_succ sp al ts (by omega)]
    exact evictInvC_step hok hph hev hj hmk (by omega) (ih (by omega))

/-- T9's proof: in a run with eviction, cache operations and restarts, after j
transactions, with a safe cut at c, a physical read at a time from the first
available time on gives the same on the stream cut at c as on the whole
stream. -/
theorem readCut (ts : List (T × Bool × List CacheOp)) (hok : RunOK sp al (ts.map (·.1)))
    (hph : PhysRunOK sp al (ts.map (·.1))) (hev : EvictRunOK sp al (ts.map (·.1)))
    (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) (j : Nat) (hjt : j ≤ ts.length) {c : Nat}
    (hcut : CutOK sp c (run sp al ((ts.take j).map (·.1))) j) {t : Time}
    (hft : lastFa (run sp al ((ts.take j).map (·.1))).S ≤ t) (ht : t ≤ j) :
    (runEvict sp al (ts.take j)).2.1.read4 sp (runEvict sp al (ts.take j)).2.2
        (cutStream c (run sp al ((ts.take j).map (·.1))).S) t =
      (runEvict sp al (ts.take j)).2.1.read4 sp (runEvict sp al (ts.take j)).2.2
        (run sp al ((ts.take j).map (·.1))).S t := by
  obtain ⟨⟨k1, -, hS0, -, hm, hh⟩, hc⟩ := evictInvC_all hok hph hev hj hmk j hjt
  have hst : st sp al (ts.map (·.1)) j = run sp al ((ts.take j).map (·.1)) := by
    show run sp al ((ts.map (·.1)).take j) = run sp al ((ts.take j).map (·.1))
    rw [List.map_take]
  have hinv := inv_st sp al (ts.map (·.1)) hok (algOK_of sp al (Or.inl hj)) j (by rw [List.length_map]; exact hjt)
  rw [hst] at hm hh hc hinv
  rw [← hS0] at hm hh
  exact CInv.read4_cut hinv hok.1.liveSub hm hh hc hcut hft ht

end Run

end SIS
