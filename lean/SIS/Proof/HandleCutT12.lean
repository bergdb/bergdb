/-
Proofs about reclaim with handles (bergdb 005-62), part 5 of T12 over handles:
the run with handles that restarts from cut streams (`runHandlesCut`, C)
appends the records of the run that restarts from cut streams without the
memory (`runRestartsCut`). C is compared with the run with handles that
restarts from the whole streams at the same points (`runHandles`, E), with
C's cache operations (`esH`). After every transaction, C's memory is E's but
for the root's object (`HMem.withRoot`), which holds C's root's history. Then
`t12_handles` follows from the logical T12 (`restartCut`), as
`restartCut_evict` does for the run with eviction.
-/
import SIS.Proof.HandleCutTransSim
import SIS.Proof.HandleCutRun

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## Runs with cut marks -/

section

variable (sp : Spec V T) (al : Algo V T)

/-- The number of transactions before the last restart among the first j (0 if
none). -/
def lastR {C : Type} (cs : List (T × Option Nat × C)) : Nat → Nat
  | 0 => 0
  | i + 1 => if ((cs[i]?).bind (·.2.1)).isSome then i + 1 else lastR cs i

/-- The restarts of C's schedule, for `runRestartsCut`. -/
def logOf {C : Type} (cs : List (T × Option Nat × C)) : List (T × Option Nat) := cs.map (fun p => (p.1, p.2.1))

end

section

variable {sp : Spec V T} {al : Algo V T}

theorem lastR_le {C : Type} (cs : List (T × Option Nat × C)) : ∀ j, lastR cs j ≤ j := by
  intro j
  induction j with
  | zero => exact Nat.le_refl _
  | succ j ih => unfold lastR; split <;> omega

theorem lastR_succ_none {C : Type} (cs : List (T × Option Nat × C)) {j : Nat} (hj : j < cs.length)
    (h : cs[j].2.1 = none) : lastR cs (j + 1) = lastR cs j := by
  show (if ((cs[j]?).bind (·.2.1)).isSome then j + 1 else lastR cs j) = lastR cs j
  rw [List.getElem?_eq_getElem hj]
  simp [h]

theorem lastR_succ_some {C : Type} (cs : List (T × Option Nat × C)) {j : Nat} (hj : j < cs.length) {c : Nat}
    (h : cs[j].2.1 = some c) : lastR cs (j + 1) = j + 1 := by
  show (if ((cs[j]?).bind (·.2.1)).isSome then j + 1 else lastR cs j) = j + 1
  rw [List.getElem?_eq_getElem hj]
  simp [h]

theorem cutMax_take_succ {C : Type} (cs : List (T × Option Nat × C)) {j : Nat} (hj : j < cs.length) :
    cutMax ((cs.take (j + 1)).map (·.2.1)) = max (cutMax ((cs.take j).map (·.2.1))) (cs[j].2.1.getD 0) := by
  have h1 : cs.take (j + 1) = cs.take j ++ [cs[j]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj]; rfl
  rw [h1, List.map_append, List.map_singleton, cutMax_append_one]

theorem runRestartsCut_succ {C : Type} (cs : List (T × Option Nat × C)) {j : Nat} (hj : j < cs.length) :
    runRestartsCut sp al ((logOf cs).take (j + 1)) =
      (match cs[j].2.1 with
       | some c => startup sp (cutStream c (step sp al (runRestartsCut sp al ((logOf cs).take j)) cs[j].1).S)
       | none => step sp al (runRestartsCut sp al ((logOf cs).take j)) cs[j].1) := by
  have hj' : j < (logOf cs).length := by simp [logOf]; exact hj
  have h1 : (logOf cs).take (j + 1) = (logOf cs).take j ++ [(cs[j].1, cs[j].2.1)] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj']
    simp [logOf]
  unfold runRestartsCut
  rw [h1, List.foldl_append]
  rfl

theorem st_fa_mono {ts : List T} (hok : RunOK sp al ts) (hj : al.stillDirty = javaTest sp) :
    ∀ {j1 j : Nat}, j1 ≤ j → j ≤ ts.length → lastFa (st sp al ts j1).S ≤ lastFa (st sp al ts j).S := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  intro j1 j h1 hj'
  induction j with
  | zero =>
    have : j1 = 0 := by omega
    subst this; exact Nat.le_refl _
  | succ j ih =>
    rcases Nat.lt_or_ge j j1 with hlt | hge
    · have : j1 = j + 1 := by omega
      subst this; exact Nat.le_refl _
    · refine Nat.le_trans (ih hge (by omega)) ?_
      have hinv := inv_st sp al ts hok hst j (by omega)
      have hfs := st_fa_le sp al ts (k := j) (by omega)
      rw [st_succ sp al ts (by omega), step_eq_parts]
      simp only [lastFa, List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.map_some,
        Option.getD_some]
      rw [parts_R]
      simp only [parts_fa, firstAvail, parts_s, startupPos]
      rw [hinv.len]
      simp only [Nat.add_sub_cancel]
      unfold lastFa at hfs ⊢
      have hsk : lastSp (st sp al ts j).S ≤ j := by have := hinv.spLt; omega
      omega

theorem logOf_fst {C : Type} (cs : List (T × Option Nat × C)) : (logOf cs).map (·.1) = cs.map (·.1) := by
  simp [logOf]

theorem logOf_snd {C : Type} (cs : List (T × Option Nat × C)) : (logOf cs).map (·.2) = cs.map (·.2.1) := by
  simp [logOf]

end

/-! ## E's schedule -/

/-- E's schedule: C's transactions and cache operations, and a restart from
the whole stream where C restarts from a cut stream. -/
def esH (cs : List (T × Option Nat × List HCacheOp)) : List (T × Bool × List HCacheOp) :=
  cs.map (fun p => (p.1, p.2.1.isSome, p.2.2))

section Facts

variable {sp : Spec V T} {al : Algo V T}

theorem esH_length (cs : List (T × Option Nat × List HCacheOp)) : (esH cs).length = cs.length := by
  simp [esH]

theorem esH_map_fst (cs : List (T × Option Nat × List HCacheOp)) : (esH cs).map (·.1) = cs.map (·.1) := by
  simp [esH]

theorem esH_getElem (cs : List (T × Option Nat × List HCacheOp)) {j : Nat} (hj : j < cs.length) :
    (esH cs)[j]'(by rw [esH_length]; exact hj) = (cs[j].1, cs[j].2.1.isSome, cs[j].2.2) := by
  simp [esH]

theorem runHandlesCut_succ (cs : List (T × Option Nat × List HCacheOp)) {j : Nat} (hj : j < cs.length) :
    runHandlesCut sp al (cs.take (j + 1)) =
      (match cs[j].2.1 with
       | some c =>
         (startup sp (cutStream c (handleTrans sp al (runHandlesCut sp al (cs.take j)).2.2
            (runHandlesCut sp al (cs.take j)).1 (runHandlesCut sp al (cs.take j)).2.1 cs[j].1).1.S),
          handleStartup sp (cutStream c (handleTrans sp al (runHandlesCut sp al (cs.take j)).2.2
            (runHandlesCut sp al (cs.take j)).1 (runHandlesCut sp al (cs.take j)).2.1 cs[j].1).1.S),
          cutStream c (handleTrans sp al (runHandlesCut sp al (cs.take j)).2.2
            (runHandlesCut sp al (cs.take j)).1 (runHandlesCut sp al (cs.take j)).2.1 cs[j].1).1.S)
       | none =>
         ((handleTrans sp al (runHandlesCut sp al (cs.take j)).2.2 (runHandlesCut sp al (cs.take j)).1
            (runHandlesCut sp al (cs.take j)).2.1 cs[j].1).1,
          cs[j].2.2.foldl (HMem.cacheOp sp (runHandlesCut sp al (cs.take j)).2.2
            (handleTrans sp al (runHandlesCut sp al (cs.take j)).2.2 (runHandlesCut sp al (cs.take j)).1
              (runHandlesCut sp al (cs.take j)).2.1 cs[j].1).1.S
            (handleTrans sp al (runHandlesCut sp al (cs.take j)).2.2 (runHandlesCut sp al (cs.take j)).1
              (runHandlesCut sp al (cs.take j)).2.1 cs[j].1).1.D)
            (handleTrans sp al (runHandlesCut sp al (cs.take j)).2.2 (runHandlesCut sp al (cs.take j)).1
              (runHandlesCut sp al (cs.take j)).2.1 cs[j].1).2,
          (runHandlesCut sp al (cs.take j)).2.2)) := by
  have h1 : cs.take (j + 1) = cs.take j ++ [cs[j]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj]; rfl
  unfold runHandlesCut
  rw [h1, List.foldl_append]
  rfl

/-- An eviction keeps the root's object (the root is pinned). -/
theorem HMem.evict_rootObj {m : HMem V} {o : HObj V} (hra : m.obj? m.root = some o) (D : Dirty) (n : Nat) :
    (m.evict D n).obj? (m.evict D n).root = some o := by
  rw [HMem.evict_root]
  cases hev : m.evictable D n with
  | false => rw [HMem.evict_not m D n hev]; exact hra
  | true =>
    obtain ⟨hd, b, ob, hh, -, hb, -, hpin, -⟩ := HMem.evictable_some hev
    have hbr : b ≠ m.root := by
      intro he
      unfold HMem.pinned at hpin
      simp [he] at hpin
    rw [HMem.evict_obj? hev hh hb, ite_eq_right (Ne.symm hbr)]
    exact hra

end Facts

/-! ## The cache operations -/

section OpsSim

variable {sp : Spec V T}

/-- The cache operations of C after a transaction, from the first available
time on, on the memory with another root object and the cut streams: E's, on
memories that differ only in the root's object again, with C's root history
kept. A read is `CInvH.read_sim`; an eviction is the same on both
(`HMem.withRoot_evict`). -/
theorem ops_simH {db1 db : DB V T} {j1 k c : Nat} (hls : LiveSub sp) (hL : Later sp db1 db j1 k)
    (hcut : CutOK sp c db1 j1) :
    ∀ (ops : List HCacheOp) (m : HMem V) (oc oe : HObj V),
      (∀ t, HCacheOp.read t ∈ ops → lastFa db1.S ≤ t ∧ t ≤ k) →
      HEInv sp db db1.S k m → HInvH sp db db1.S k m → CInvH sp db db1.S m →
      m.obj? m.root = some oe → RootRelH sp (lastFa db1.S) oc oe →
      ∃ oc' oe', ops.foldl (HMem.cacheOp sp (cutStream c db1.S) (cutStream c db.S) db.D) (m.withRoot oc) =
          (ops.foldl (HMem.cacheOp sp db1.S db.S db.D) m).withRoot oc' ∧
        (ops.foldl (HMem.cacheOp sp db1.S db.S db.D) m).obj?
          (ops.foldl (HMem.cacheOp sp db1.S db.S db.D) m).root = some oe' ∧
        RootRelH sp (lastFa db1.S) oc' oe' ∧ oc'.hist = oc.hist := by
  have hinv := hL.inv
  intro ops
  induction ops with
  | nil =>
    intro m oc oe _ _ _ _ hra hr
    exact ⟨oc, oe, rfl, hra, hr, rfl⟩
  | cons op ops ih =>
    intro m oc oe hreads hm hh hc hra hr
    have hreads' : ∀ t, HCacheOp.read t ∈ ops → lastFa db1.S ≤ t ∧ t ≤ k :=
      fun t ht => hreads t (List.mem_cons_of_mem _ ht)
    simp only [List.foldl_cons]
    cases op with
    | read t =>
      have ht := hreads t List.mem_cons_self
      obtain ⟨oc1, oe1, tail, h1, -, h3, h4, h5⟩ := hc.read_sim hL hls hm hh hcut ht.1 ht.2 ht.1 hra hr
      have e : HMem.cacheOp sp (cutStream c db1.S) (cutStream c db.S) db.D (m.withRoot oc) (HCacheOp.read t) =
          (HMem.cacheOp sp db1.S db.S db.D m (HCacheOp.read t)).withRoot oc1 := by
        show ((m.withRoot oc).read sp (cutStream c db1.S) (cutStream c db.S) t).1 =
          (m.read sp db1.S db.S t).1.withRoot oc1
        rw [h1]
      rw [e]
      obtain ⟨oc2, oe2, g1, g2, g3, g4⟩ := ih _ oc1 oe1 hreads' (hm.cacheOp hinv (HCacheOp.read t))
        (hh.cacheOp hinv hls hm (HCacheOp.read t)) (hc.cacheOp hinv hm (HCacheOp.read t)) h3 h4
      exact ⟨oc2, oe2, g1, g2, g3, g4.trans h5⟩
    | evict n =>
      have e : HMem.cacheOp sp (cutStream c db1.S) (cutStream c db.S) db.D (m.withRoot oc) (HCacheOp.evict n) =
          (HMem.cacheOp sp db1.S db.S db.D m (HCacheOp.evict n)).withRoot oc :=
        HMem.withRoot_evict hra db.D n
      rw [e]
      exact ih _ oc oe hreads' (hm.cacheOp hinv (HCacheOp.evict n)) (hh.cacheOp hinv hls hm (HCacheOp.evict n))
        (hc.cacheOp hinv hm (HCacheOp.evict n)) (HMem.evict_rootObj hra db.D n) hr

end OpsSim

/-! ## The relation of the two runs -/

/-- C and E after the first j transactions: C's state is the one of the run
that restarts from cut streams; E's last startup was from the run's stream
after `lastR cs j` transactions, and C's from that stream cut at the largest
cut so far; C's structure agrees with the run's (`CutRel`), the cut was safe;
C's memory is E's but for the root's object, which holds C's root's
history. -/
structure RunSimH (sp : Spec V T) (al : Algo V T) (cs : List (T × Option Nat × List HCacheOp)) (j : Nat) :
    Prop where
  log : (runHandlesCut sp al (cs.take j)).1 = runRestartsCut sp al ((logOf cs).take j)
  sE : (runHandles sp al ((esH cs).take j)).2.2 = (st sp al (cs.map (·.1)) (lastR cs j)).S
  sC : (runHandlesCut sp al (cs.take j)).2.2 =
    cutStream (cutMax ((cs.take j).map (·.2.1))) (st sp al (cs.map (·.1)) (lastR cs j)).S
  rel : CutRel sp (cutMax ((cs.take j).map (·.2.1))) (lastFa (st sp al (cs.map (·.1)) (lastR cs j)).S) j
    (runHandlesCut sp al (cs.take j)).1 (st sp al (cs.map (·.1)) j)
  cut : CutOK sp (cutMax ((cs.take j).map (·.2.1))) (st sp al (cs.map (·.1)) (lastR cs j)) (lastR cs j)
  sim : ∃ oc oe, (runHandlesCut sp al (cs.take j)).2.1 = (runHandles sp al ((esH cs).take j)).2.1.withRoot oc ∧
    (runHandles sp al ((esH cs).take j)).2.1.obj? (runHandles sp al ((esH cs).take j)).2.1.root = some oe ∧
    RootRelH sp (lastFa (st sp al (cs.map (·.1)) (lastR cs j)).S) oc oe ∧
    ∀ n, (runHandlesCut sp al (cs.take j)).1.P.get? root = some n → oc.hist = n.hist

section RunProof

variable {sp : Spec V T} {al : Algo V T}

theorem runSimH_zero (cs : List (T × Option Nat × List HCacheOp)) (hok : RunOK sp al (cs.map (·.1)))
    (hph : PhysRunOK sp al (cs.map (·.1))) (hev : EvictRunOK sp al (cs.map (·.1)))
    (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) (hex : ExecRootOK sp) (hvl : VirtLiveOK sp) :
    RunSimH sp al cs 0 := by
  have h0C : runHandlesCut sp al (cs.take 0) = (init sp, handleStartup sp (init sp).S, (init sp).S) := by
    simp [runHandlesCut]
  have h0E : runHandles sp al ((esH cs).take 0) = (init sp, handleStartup sp (init sp).S, (init sp).S) := by
    simp [runHandles]
  have hl0 : lastR cs 0 = 0 := rfl
  have hc0 : cutMax ((cs.take 0).map (·.2.1)) = 0 := by simp [cutMax]
  have hst0 := st_zero sp al (cs.map (·.1))
  obtain ⟨oc, oe, hsim, hra, hrr, hoc⟩ := handleStartup_sim hok hph hev hj hmk hex hvl (k := 0) (c := 0)
    (Nat.zero_le _) (CutOK.zero sp _ 0)
  rw [hst0, cutStream_zero] at hsim hoc
  rw [hst0] at hra hrr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h0C]; simp [runRestartsCut]
  · rw [h0E, hl0, hst0]
  · rw [h0C, hl0, hc0, hst0, cutStream_zero]
  · rw [h0C, hl0, hc0, hst0]
    have hinv := inv_init sp hok.1
    exact ⟨(cutStream_zero _).symm, rfl, hinv.cutAgree_refl _, fun _ _ => rfl, Nat.zero_le _, Nat.le_refl _⟩
  · rw [hl0, hc0]; exact CutOK.zero sp _ 0
  · rw [h0C, h0E, hl0, hst0]
    refine ⟨oc, oe, hsim, hra, hrr, ?_⟩
    intro n hn
    have hT := (T1_strong sp al (cs.map (·.1)) hok (algOK_of sp al (Or.inl hj)) (k := 0) (Nat.zero_le _)).1 root
    rw [hst0] at hT
    exact hoc n (by rw [hT]; exact hn)

theorem runSimH_step (cs : List (T × Option Nat × List HCacheOp)) (hok : RunOK sp al (cs.map (·.1)))
    (hph : PhysRunOK sp al (cs.map (·.1))) (hev : EvictRunOK sp al (cs.map (·.1)))
    (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) (hex : ExecRootOK sp) (hvl : VirtLiveOK sp)
    (hpol : PolicyCutOK al)
    (hcut : ∀ j (h : j < cs.length) c, cs[j].2.1 = some c →
      CutOK sp (cutMax ((cs.take (j + 1)).map (·.2.1))) (st sp al (cs.map (·.1)) (j + 1)) (j + 1))
    (hreads : ∀ j (h : j < cs.length), cs[j].2.1 = none → ∀ t, HCacheOp.read t ∈ cs[j].2.2 →
      lastFa (st sp al (cs.map (·.1)) (j + 1)).S ≤ t ∧ t ≤ j + 1)
    {j : Nat} (hjl : j < cs.length) (hR : RunSimH sp al cs j) : RunSimH sp al cs (j + 1) := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hsp := hok.1
  have hls : LiveSub sp := hsp.liveSub
  have hjt : j < (cs.map (·.1)).length := by simpa using hjl
  have htr : (cs.map (·.1))[j] = cs[j].1 := by simp
  have hes1 : (esH cs).map (·.1) = cs.map (·.1) := esH_map_fst cs
  have hjE : j < (esH cs).length := by rw [esH_length]; exact hjl
  -- E's invariants after j transactions
  obtain ⟨⟨k1, -, hS0, hrelE, hm, hh⟩, hc⟩ :=
    handleInvC_all (ts := esH cs) (by rw [hes1]; exact hok) (by rw [hes1]; exact hph)
      (by rw [hes1]; exact hev) hj hmk j (by omega)
  rw [hes1] at hrelE hm hh hS0 hc
  have hS0' : (st sp al (cs.map (·.1)) k1).S = (st sp al (cs.map (·.1)) (lastR cs j)).S := hS0.symm.trans hR.sE
  rw [hS0'] at hm hh
  rw [hR.sE] at hc
  have hL := later_st hok hst (lastR_le cs j) (by omega : j ≤ (cs.map (·.1)).length)
  -- the step's assumptions
  have hinv := inv_st sp al (cs.map (·.1)) hok hst j (by omega)
  have hinv' := inv_st sp al (cs.map (·.1)) hok hst (j + 1) (by omega)
  have hlog := evLogic_st sp al (cs.map (·.1)) hok hj hmk hev j (by omega)
  have hlog' := evLogic_st sp al (cs.map (·.1)) hok hj hmk hev (j + 1) (by omega)
  have hcx : (parts sp al (st sp al (cs.map (·.1)) j) cs[j].1).c =
      sp.exec cs[j].1 (j + 1) (view sp (st sp al (cs.map (·.1)) j).P j) := by
    rw [parts_c, hinv.len, Nat.add_sub_cancel]
  have hstep : StepOK sp (st sp al (cs.map (·.1)) j).P (j + 1)
      (parts sp al (st sp al (cs.map (·.1)) j) cs[j].1).c := by
    rw [hcx, ← htr]; exact hok.2 j hjt
  have hphys : PhysStep sp (st sp al (cs.map (·.1)) j).P (j + 1)
      (parts sp al (st sp al (cs.map (·.1)) j) cs[j].1).c := by
    rw [hcx, ← htr]; exact hph j hjt
  have hcopy : CopyStep sp (st sp al (cs.map (·.1)) j).P (j + 1)
      (parts sp al (st sp al (cs.map (·.1)) j) cs[j].1).c := by
    rw [hcx, ← htr]; exact hev.2 j hjt
  have htree : treeAt sp (st sp al (cs.map (·.1)) j).P j := (hev.1 j (by omega)).tree
  have hst1 : st sp al (cs.map (·.1)) (j + 1) = step sp al (st sp al (cs.map (·.1)) j) cs[j].1 := by
    rw [st_succ sp al _ hjt, htr]
  rw [hst1] at hinv' hlog'
  -- E's transaction, on the run's state
  have hcongr := handleTrans_congr sp al hst (st sp al (cs.map (·.1)) (lastR cs j)).S hrelE
    (runHandles sp al ((esH cs).take j)).2.1 cs[j].1
  rw [← hR.sE] at hcongr
  obtain ⟨hE1, hE2⟩ := hm.handleTrans_ok hsp hinv hmk hlog hstep hphys hcopy htree hinv' hlog'
  have hE3 := HInvH.handleTrans_ok hsp hinv hmk hm hh hlog hstep hphys hcopy htree hinv' hlog'
  have hE4 := CInvH.handleTrans_ok hsp hinv hmk hm hc hlog hstep hphys hcopy htree hinv'
  have hfsj := st_fa_le sp al (cs.map (·.1)) (k := j) (by omega)
  have hstep_e : StepOK sp (st sp al (cs.map (·.1)) j).P (j + 1)
      (sp.exec cs[j].1 (j + 1) (view sp (st sp al (cs.map (·.1)) j).P j)) := by rw [← hcx]; exact hstep
  obtain ⟨-, -, -, -, -, -, hrel1⟩ := step_congr_cut sp al hsp hinv hj hmk hex hvl hpol hR.rel hfsj cs[j].1 hstep_e
  rw [← hst1] at hrel1
  -- C's transaction
  obtain ⟨oc, oe, hsimm, hra, hrr, hoc⟩ := hR.sim
  obtain ⟨hC1, oc', oe', hsim', hra', hrr', hoc'⟩ := handleTrans_sim hsp hj hmk hex hvl hpol hlog hL hR.cut
    hR.rel hfsj hm hh hc hra hrr hoc hstep hphys hcopy htree hinv'
  rw [← hR.sC, ← hsimm] at hC1 hsim'
  have hcg2 : (handleTrans sp al (runHandles sp al ((esH cs).take j)).2.2 (runHandles sp al ((esH cs).take j)).1
      (runHandles sp al ((esH cs).take j)).2.1 cs[j].1).2 =
      (handleTrans sp al (st sp al (cs.map (·.1)) (lastR cs j)).S (st sp al (cs.map (·.1)) j)
        (runHandles sp al ((esH cs).take j)).2.1 cs[j].1).2 := by rw [hcongr.2, hR.sE]
  rw [← hcg2] at hsim' hra'
  have hE1' : (handleTrans sp al (runHandles sp al ((esH cs).take j)).2.2 (runHandles sp al ((esH cs).take j)).1
      (runHandles sp al ((esH cs).take j)).2.1 cs[j].1).1.S = (st sp al (cs.map (·.1)) (j + 1)).S ∧
      (handleTrans sp al (runHandles sp al ((esH cs).take j)).2.2 (runHandles sp al ((esH cs).take j)).1
      (runHandles sp al ((esH cs).take j)).2.1 cs[j].1).1.D = (st sp al (cs.map (·.1)) (j + 1)).D := by
    obtain ⟨r1, r2, -⟩ := hcongr.1
    rw [r1, r2, hR.sE, hE1, hst1]
    exact ⟨rfl, rfl⟩
  have hlog1 := hR.log
  have hesj := esH_getElem cs hjl
  have hCs := runHandlesCut_succ (sp := sp) (al := al) cs hjl
  have hEs := runHandles_succ sp al (esH cs) hjE
  have hRs := runRestartsCut_succ (sp := sp) (al := al) cs hjl
  have hcm := cutMax_take_succ cs hjl
  rw [hesj] at hEs
  simp only at hEs
  rw [← hst1, ← hcg2] at hE2 hE3 hE4
  cases hcj : cs[j].2.1 with
  | none =>
    simp only [hcj] at hCs hRs hEs hcm
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hEs
    have hm0 : cutMax ((cs.take (j + 1)).map (·.2.1)) = cutMax ((cs.take j).map (·.2.1)) := by rw [hcm]; simp
    have hlr := lastR_succ_none cs hjl hcj
    have hlogS : step sp al (runHandlesCut sp al (cs.take j)).1 cs[j].1 =
        runRestartsCut sp al ((logOf cs).take (j + 1)) := by
      rw [hRs, hlog1]
    generalize hTC : handleTrans sp al (runHandlesCut sp al (cs.take j)).2.2 (runHandlesCut sp al (cs.take j)).1
      (runHandlesCut sp al (cs.take j)).2.1 cs[j].1 = TC at hC1 hsim' hCs
    generalize hTE : handleTrans sp al (runHandles sp al ((esH cs).take j)).2.2
      (runHandles sp al ((esH cs).take j)).1 (runHandles sp al ((esH cs).take j)).2.1 cs[j].1 = TE
      at hsim' hra' hE1' hEs hE2 hE3 hE4
    have hL' := later_st hok hst (j1 := lastR cs j) (j := j + 1) (by have := lastR_le cs j; omega) (by omega)
    have hTCS : TC.1.S = cutStream (cutMax ((cs.take j).map (·.2.1))) (st sp al (cs.map (·.1)) (j + 1)).S := by
      rw [hC1, hrel1.stream]
    have hTCD : TC.1.D = (st sp al (cs.map (·.1)) (j + 1)).D := by rw [hC1, hrel1.dirty]
    have hreads' : ∀ t, HCacheOp.read t ∈ cs[j].2.2 →
        lastFa (st sp al (cs.map (·.1)) (lastR cs j)).S ≤ t ∧ t ≤ j + 1 := by
      intro t ht
      obtain ⟨h1, h2⟩ := hreads j hjl hcj t ht
      exact ⟨Nat.le_trans (st_fa_mono hok hj (Nat.le_trans (lastR_le cs j) (Nat.le_succ j)) (by omega)) h1, h2⟩
    obtain ⟨oc'', oe'', g1, g2, g3, g4⟩ := ops_simH (db := st sp al (cs.map (·.1)) (j + 1)) (k := j + 1)
      hls hL' hR.cut cs[j].2.2 TE.2 oc' oe' hreads' hE2 hE3 hE4 hra' hrr'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hCs]; exact hC1.trans hlogS
    · rw [hEs, hR.sE, hlr]
    · rw [hCs, hR.sC, hm0, hlr]
    · rw [hCs, hm0, hlr]; simp only; rw [hC1]; exact hrel1
    · rw [hm0, hlr]; exact hR.cut
    · rw [hCs, hEs]
      simp only
      rw [hsim', hlr, hR.sC, hR.sE, hTCS, hTCD, hE1'.1, hE1'.2]
      refine ⟨oc'', oe'', g1, g2, g3, ?_⟩
      intro n hn
      rw [hC1] at hn
      rw [g4]
      exact hoc' n hn
  | some c =>
    simp only [hcj] at hCs hRs hEs hcm
    simp only [Option.isSome_some, ↓reduceIte] at hEs
    have hlr := lastR_succ_some cs hjl hcj
    have hcut1 := hcut j hjl c hcj
    have hm1 : cutMax ((cs.take (j + 1)).map (·.2.1)) = max (cutMax ((cs.take j).map (·.2.1))) c := by
      rw [hcm]; rfl
    have hTCS : (handleTrans sp al (runHandlesCut sp al (cs.take j)).2.2 (runHandlesCut sp al (cs.take j)).1
        (runHandlesCut sp al (cs.take j)).2.1 cs[j].1).1.S =
        cutStream (cutMax ((cs.take j).map (·.2.1))) (st sp al (cs.map (·.1)) (j + 1)).S := by
      rw [hC1, hrel1.stream]
    have hSC : cutStream c (handleTrans sp al (runHandlesCut sp al (cs.take j)).2.2
        (runHandlesCut sp al (cs.take j)).1 (runHandlesCut sp al (cs.take j)).2.1 cs[j].1).1.S =
        cutStream (cutMax ((cs.take (j + 1)).map (·.2.1))) (st sp al (cs.map (·.1)) (j + 1)).S := by
      rw [hTCS, cutStream_cutStream, hm1, Nat.max_comm]
    have hSE := hE1'.1
    obtain ⟨ocs, oes, hsims, hras, hrrs, hocs⟩ := handleStartup_sim hok hph hev hj hmk hex hvl (k := j + 1)
      (by simp; omega) hcut1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hCs]; simp only; rw [hRs, ← hlog1, ← hC1]
    · rw [hEs, hlr]; exact hSE
    · rw [hCs, hlr]; exact hSC
    · rw [hCs, hlr]
      simp only
      rw [hSC]
      obtain ⟨hag, hdn⟩ := recoverCut_dNodes sp al (cs.map (·.1)) hok hj hmk (k := j + 1) (by simp; omega) hex hvl
        hcut1
      obtain ⟨-, hD⟩ := recoverCut sp al (cs.map (·.1)) hok hst (k := j + 1) (by simp; omega) hex hvl hcut1
      exact ⟨rfl, hD, hag, hdn, hcut1.1, Nat.le_refl _⟩
    · rw [hlr]; exact hcut1
    · rw [hCs, hEs, hlr]
      simp only
      rw [hSC, hSE]
      exact ⟨ocs, oes, hsims, hras, hrrs, hocs⟩

/-- T12 over handles, first form: the run with handles that restarts from safe
cut streams appends the records of the run that restarts from them without
the memory. -/
theorem handleCut_restartsCut (cs : List (T × Option Nat × List HCacheOp)) (hok : RunOK sp al (cs.map (·.1)))
    (hph : PhysRunOK sp al (cs.map (·.1))) (hev : EvictRunOK sp al (cs.map (·.1)))
    (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) (hex : ExecRootOK sp) (hvl : VirtLiveOK sp)
    (hpol : PolicyCutOK al)
    (hcut : ∀ j (h : j < cs.length) c, cs[j].2.1 = some c →
      CutOK sp (cutMax ((cs.take (j + 1)).map (·.2.1))) (st sp al (cs.map (·.1)) (j + 1)) (j + 1))
    (hreads : ∀ j (h : j < cs.length), cs[j].2.1 = none → ∀ t, HCacheOp.read t ∈ cs[j].2.2 →
      lastFa (st sp al (cs.map (·.1)) (j + 1)).S ≤ t ∧ t ≤ j + 1) :
    (runHandlesCut sp al cs).1 = runRestartsCut sp al (logOf cs) := by
  have key : ∀ j ≤ cs.length, RunSimH sp al cs j := by
    intro j
    induction j with
    | zero => intro _; exact runSimH_zero cs hok hph hev hj hmk hex hvl
    | succ j ih =>
      intro hj'
      exact runSimH_step cs hok hph hev hj hmk hex hvl hpol hcut hreads (by omega) (ih (by omega))
  have := (key cs.length (Nat.le_refl _)).log
  rw [List.take_length] at this
  have h2 : (logOf cs).take cs.length = logOf cs := List.take_of_length_le (by simp [logOf])
  rw [h2] at this
  exact this

/-- T12 over handles (`T12_handles`): from `handleCut_restartsCut` and the
logical T12 (`restartCut`), as `restartCut_evict`. -/
theorem t12_handles (sp : Spec V T) (al : Algo V T) : T12_handles sp al := by
  intro cs hok hph hev hj hmk hex hvl hpol hcut hreads
  dsimp only
  rw [handleCut_restartsCut cs hok hph hev hj hmk hex hvl hpol hcut hreads]
  have h := restartCut sp al (logOf cs) (by rw [logOf_fst]; exact hok) hj hmk hex hvl hpol (by
    intro j hjl c hc
    have hjl' : j < cs.length := by simpa [logOf] using hjl
    have hc' : cs[j].2.1 = some c := by simpa [logOf] using hc
    have hm : ((logOf cs).take (j + 1)).map (·.2) = (cs.take (j + 1)).map (·.2.1) := by
      rw [List.map_take, logOf_snd, List.map_take]
    rw [logOf_fst, hm]
    exact hcut j hjl' c hc')
  have hlen : (logOf cs).length = cs.length := by simp [logOf]
  rw [logOf_fst, logOf_snd, hlen] at h
  exact h

end RunProof

end SIS
