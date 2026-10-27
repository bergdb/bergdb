/-
Proofs about reclaim, part 22 (bergdb item 001, WP R5, T12 with eviction): the
run with eviction that restarts from cut streams (`runEvictCut`, C) appends
the records of the run that restarts from cut streams without eviction
(`runRestartsCut`). C is compared with the run with eviction that restarts
from the whole streams at the same points (`runEvict`, E), whose cache
operations are C's with extra unswizzles of its root's slots before each
release (`esOf`).
-/
import SIS.Proof.CutLaterStart

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## E's schedule -/

section Defs

variable (sp : Spec V T) (al : Algo V T)

/-- The number of transactions before the last restart among the first j (0 if
none). -/
def lastR {C : Type} (cs : List (T × Option Nat × C)) : Nat → Nat
  | 0 => 0
  | i + 1 => if ((cs[i]?).bind (·.2.1)).isSome then i + 1 else lastR cs i

/-- The root's history in a structure. -/
def rootHist (P : Struct V) : History V := ((P.get? root).map (·.hist)).getD []

/-- The restarts of C's schedule, for `runRestartsCut`. -/
def logOf {C : Type} (cs : List (T × Option Nat × C)) : List (T × Option Nat) := cs.map (fun p => (p.1, p.2.1))

/-- The root children of E's root, after transaction j + 1, that C's root has not. -/
def extraY (cs : List (T × Option Nat × List CacheOp)) (j : Nat) : List NodeId :=
  (pointees sp (rootHist (st sp al (cs.map (·.1)) (j + 1)).P)).filter
    (fun y => !(pointees sp (rootHist (runRestartsCut sp al ((logOf cs).take (j + 1))).P)).contains y)

/-- E's schedule: C's transactions, restarts from the whole streams at the same
points, and C's cache operations with the extra unswizzles before each
release. -/
def esOf (cs : List (T × Option Nat × List CacheOp)) : List (T × Bool × List CacheOp) :=
  cs.mapIdx (fun j p => (p.1, p.2.1.isSome,
    augment ((extraY sp al cs j).map
      (CacheOp.unswizzle (evictStartup sp (st sp al (cs.map (·.1)) (lastR cs (j + 1))).S).root)) p.2.2))

end Defs

/-! ## Facts about the schedules -/

section Facts

variable {sp : Spec V T} {al : Algo V T}

theorem runEvictCut_succ (cs : List (T × Option Nat × List CacheOp)) {j : Nat} (hj : j < cs.length) :
    runEvictCut sp al (cs.take (j + 1)) =
      (match cs[j].2.1 with
       | some c =>
         (startup sp (cutStream c (evictTrans sp al (runEvictCut sp al (cs.take j)).2.2 (runEvictCut sp al (cs.take j)).1
            (runEvictCut sp al (cs.take j)).2.1 cs[j].1).1.S),
          evictStartup sp (cutStream c (evictTrans sp al (runEvictCut sp al (cs.take j)).2.2
            (runEvictCut sp al (cs.take j)).1 (runEvictCut sp al (cs.take j)).2.1 cs[j].1).1.S),
          cutStream c (evictTrans sp al (runEvictCut sp al (cs.take j)).2.2 (runEvictCut sp al (cs.take j)).1
            (runEvictCut sp al (cs.take j)).2.1 cs[j].1).1.S)
       | none =>
         ((evictTrans sp al (runEvictCut sp al (cs.take j)).2.2 (runEvictCut sp al (cs.take j)).1
            (runEvictCut sp al (cs.take j)).2.1 cs[j].1).1,
          cs[j].2.2.foldl (Mem.cacheOp sp (runEvictCut sp al (cs.take j)).2.2
            (evictTrans sp al (runEvictCut sp al (cs.take j)).2.2 (runEvictCut sp al (cs.take j)).1
              (runEvictCut sp al (cs.take j)).2.1 cs[j].1).1.S
            (evictTrans sp al (runEvictCut sp al (cs.take j)).2.2 (runEvictCut sp al (cs.take j)).1
              (runEvictCut sp al (cs.take j)).2.1 cs[j].1).1.D)
            (evictTrans sp al (runEvictCut sp al (cs.take j)).2.2 (runEvictCut sp al (cs.take j)).1
              (runEvictCut sp al (cs.take j)).2.1 cs[j].1).2,
          (runEvictCut sp al (cs.take j)).2.2)) := by
  have h1 : cs.take (j + 1) = cs.take j ++ [cs[j]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj]; rfl
  unfold runEvictCut
  rw [h1, List.foldl_append]
  rfl

theorem esOf_length (cs : List (T × Option Nat × List CacheOp)) : (esOf sp al cs).length = cs.length := by
  simp [esOf]

theorem esOf_getElem (cs : List (T × Option Nat × List CacheOp)) {j : Nat} (hj : j < cs.length) :
    (esOf sp al cs)[j]'(by rw [esOf_length]; exact hj) = (cs[j].1, cs[j].2.1.isSome,
      augment ((extraY sp al cs j).map
        (CacheOp.unswizzle (evictStartup sp (st sp al (cs.map (·.1)) (lastR cs (j + 1))).S).root)) cs[j].2.2) := by
  simp [esOf]

theorem esOf_map_fst (cs : List (T × Option Nat × List CacheOp)) : (esOf sp al cs).map (·.1) = cs.map (·.1) := by
  apply List.ext_getElem
  · simp [esOf_length]
  · intro n h1 h2
    simp only [List.getElem_map]
    rw [esOf_getElem (sp := sp) (al := al) cs (by simpa using h2)]

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

theorem writeNodes_root (S0 : Stream V T) (D : Dirty) (i : Nat) (xs : List NodeId) (m : Mem V) :
    (m.writeNodes sp S0 D i xs).1.root = m.root := by
  rw [writeNodes_eq_foldl]
  have : ∀ (xs : List NodeId) (acc : Mem V × List (Version V)), (xs.foldl (wnStep sp S0 D i) acc).1.root = acc.1.root := by
    intro xs
    induction xs with
    | nil => intro acc; rfl
    | cons x xs ih =>
      intro acc
      simp only [List.foldl_cons]
      rw [ih, wnStep_fst]
      unfold Mem.writeNode
      cases acc.1.canonicalOf x with
      | none => rfl
      | some h =>
        dsimp only
        cases acc.1.obj? h with
        | none => rfl
        | some o => rfl
  exact this xs (m, [])

theorem applyChange4_root (P : Struct V) (j : Time) (c : Changes V) (m : Mem V) :
    (m.applyChange4 sp P j c).root = m.root := by
  rw [applyChange4_eq]
  have : ∀ (L : List (NodeId × V)) (a : Mem V),
      (L.foldl (addsStep4 sp P j (c.new.foldl SIS.addNew m)) a).root = a.root := by
    intro L
    induction L with
    | nil => intro a; rfl
    | cons x L ih =>
      intro a
      simp only [List.foldl_cons]
      rw [ih]
      unfold addsStep4
      cases a.canonicalOf x.1 with
      | none => rfl
      | some h =>
        dsimp only
        cases a.obj? h with
        | none => rfl
        | some o => rfl
  rw [this, foldl_addNew_root]

theorem evictTrans_root (S0 : Stream V T) (db : DB V T) (m : Mem V) (tr : T) :
    (evictTrans sp al S0 db m tr).2.root = m.root := by
  rw [evictTrans_eq, evictAfter_eq]
  simp only
  rw [writeNodes_root, writeNodes_root]
  unfold preWrite
  simp only
  rw [applyChange4_root]
  have : ∀ (L : List NodeId) (a : Mem V),
      (L.foldl (Mem.reachOnPath4 sp S0 db.S db.P db.S.length
        (pathOf sp db.P (sp.exec tr db.S.length (m.view4 sp S0 db.S (db.S.length - 1)).2) db.S.length)) a).root = a.root := by
    intro L
    induction L with
    | nil => intro a; rfl
    | cons x L ih =>
      intro a
      simp only [List.foldl_cons]
      rw [ih]
      unfold Mem.reachOnPath4
      dsimp only
      split
      · split
        · exact follow4_root' _ _ _ _
        · rfl
      · rfl
  rw [this]
  show (m.read4 sp S0 db.S (db.S.length - 1)).1.root = m.root
  unfold Mem.read4
  cases m.obj? m.root with
  | none => rfl
  | some o => exact readAt4_root _ m _ _

end Facts

/-! ## The relation of the two runs -/

/-- C and E after the first j transactions: C's state is the one of the run
with restarts from cut streams; E's last startup was from the run's stream
after `lastR cs j` transactions, and C's from that stream cut at the largest
cut so far; C's structure agrees with the run's (`CutRel`), the cut was safe;
C's memory is E's but for the root's object, which holds C's root's history. -/
structure RunSim (sp : Spec V T) (al : Algo V T) (cs : List (T × Option Nat × List CacheOp)) (j : Nat) : Prop where
  log : (runEvictCut sp al (cs.take j)).1 = runRestartsCut sp al ((logOf cs).take j)
  sE : (runEvict sp al ((esOf sp al cs).take j)).2.2 = (st sp al (cs.map (·.1)) (lastR cs j)).S
  sC : (runEvictCut sp al (cs.take j)).2.2 =
    cutStream (cutMax ((cs.take j).map (·.2.1))) (st sp al (cs.map (·.1)) (lastR cs j)).S
  rel : CutRel sp (cutMax ((cs.take j).map (·.2.1))) (lastFa (st sp al (cs.map (·.1)) (lastR cs j)).S) j
    (runEvictCut sp al (cs.take j)).1 (st sp al (cs.map (·.1)) j)
  cut : CutOK sp (cutMax ((cs.take j).map (·.2.1))) (st sp al (cs.map (·.1)) (lastR cs j)) (lastR cs j)
  sim : ∃ oc oe, SimC sp (lastFa (st sp al (cs.map (·.1)) (lastR cs j)).S) (runEvictCut sp al (cs.take j)).2.1
      (runEvict sp al ((esOf sp al cs).take j)).2.1 oc oe ∧
    ∀ n, (runEvictCut sp al (cs.take j)).1.P.get? root = some n → oc.hist = n.hist
  rootE : (runEvict sp al ((esOf sp al cs).take j)).2.1.root =
    (evictStartup sp (st sp al (cs.map (·.1)) (lastR cs j)).S).root
  ndC : SlotsND (runEvictCut sp al (cs.take j)).2.1

section RunProof

variable {sp : Spec V T} {al : Algo V T}

theorem runSim_zero (cs : List (T × Option Nat × List CacheOp)) (hok : RunOK sp al (cs.map (·.1)))
    (hph : PhysRunOK sp al (cs.map (·.1))) (hev : EvictRunOK sp al (cs.map (·.1)))
    (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) (hex : ExecRootOK sp) (hvl : VirtLiveOK sp) :
    RunSim sp al cs 0 := by
  have h0C : runEvictCut sp al (cs.take 0) = (init sp, evictStartup sp (init sp).S, (init sp).S) := by
    simp [runEvictCut]
  have h0E : runEvict sp al ((esOf sp al cs).take 0) = (init sp, evictStartup sp (init sp).S, (init sp).S) := by
    simp [runEvict]
  have hl0 : lastR cs 0 = 0 := rfl
  have hc0 : cutMax ((cs.take 0).map (·.2.1)) = 0 := by simp [cutMax]
  have hst0 := st_zero sp al (cs.map (·.1))
  obtain ⟨oc, oe, hsim, hoc⟩ := startup_sim hok hph hev hj hmk hex hvl (k := 0) (c := 0) (Nat.zero_le _)
    (CutOK.zero sp _ 0)
  rw [hst0, cutStream_zero] at hsim hoc
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h0C]; simp [runRestartsCut]
  · rw [h0E, hl0, hst0]
  · rw [h0C, hl0, hc0, hst0, cutStream_zero]
  · rw [h0C, hl0, hc0, hst0]
    have hinv := inv_init sp hok.1
    exact ⟨(cutStream_zero _).symm, rfl, hinv.cutAgree_refl _, fun _ _ => rfl, Nat.zero_le _, Nat.le_refl _⟩
  · rw [hl0, hc0]; exact CutOK.zero sp _ 0
  · rw [h0C, h0E, hl0, hst0]
    refine ⟨oc, oe, hsim, ?_⟩
    intro n hn
    have hT := (T1_strong sp al (cs.map (·.1)) hok (algOK_of sp al (Or.inl hj)) (k := 0) (Nat.zero_le _)).1 root
    rw [hst0] at hT
    exact hoc n (by rw [hT]; exact hn)
  · rw [h0E, hl0, hst0]
  · rw [h0C]; exact slotsND_evictStartup sp _

theorem runSim_step (cs : List (T × Option Nat × List CacheOp)) (hok : RunOK sp al (cs.map (·.1)))
    (hph : PhysRunOK sp al (cs.map (·.1))) (hev : EvictRunOK sp al (cs.map (·.1)))
    (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) (hex : ExecRootOK sp) (hvl : VirtLiveOK sp)
    (hpol : PolicyCutOK al)
    (hcut : ∀ j (h : j < cs.length) c, cs[j].2.1 = some c →
      CutOK sp (cutMax ((cs.take (j + 1)).map (·.2.1))) (st sp al (cs.map (·.1)) (j + 1)) (j + 1))
    (hreads : ∀ j (h : j < cs.length), cs[j].2.1 = none → ∀ t, CacheOp.read t ∈ cs[j].2.2 →
      lastFa (st sp al (cs.map (·.1)) (j + 1)).S ≤ t ∧ t ≤ j + 1)
    {j : Nat} (hjl : j < cs.length) (hR : RunSim sp al cs j) : RunSim sp al cs (j + 1) := by
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hsp := hok.1
  have hls : LiveSub sp := hsp.liveSub
  have hjt : j < (cs.map (·.1)).length := by simpa using hjl
  have htr : (cs.map (·.1))[j] = cs[j].1 := by simp
  have hes1 : (esOf sp al cs).map (·.1) = cs.map (·.1) := esOf_map_fst cs
  have hjE : j < (esOf sp al cs).length := by rw [esOf_length]; exact hjl
  -- E's invariants after j transactions
  obtain ⟨⟨⟨k1, -, hS0, hrelE, hm, hh⟩, -⟩, hn⟩ :=
    evictInvN_all (ts := esOf sp al cs) (by rw [hes1]; exact hok) (by rw [hes1]; exact hph)
      (by rw [hes1]; exact hev) hj hmk j (by omega)
  rw [hes1] at hrelE hm hh hn hS0
  have hS0' : (st sp al (cs.map (·.1)) k1).S = (st sp al (cs.map (·.1)) (lastR cs j)).S := hS0.symm.trans hR.sE
  rw [hS0'] at hm hh
  rw [hR.sE] at hn
  have hL := later_st hok hst (lastR_le cs j) (by omega : j ≤ (cs.map (·.1)).length)
  -- the step's assumptions
  have hinv := inv_st sp al (cs.map (·.1)) hok hst j (by omega)
  have hinv' := inv_st sp al (cs.map (·.1)) hok hst (j + 1) (by omega)
  have hlog := evLogic_st sp al (cs.map (·.1)) hok hj hmk hev j (by omega)
  have hlog' := evLogic_st sp al (cs.map (·.1)) hok hj hmk hev (j + 1) (by omega)
  have hc : (parts sp al (st sp al (cs.map (·.1)) j) cs[j].1).c =
      sp.exec cs[j].1 (j + 1) (view sp (st sp al (cs.map (·.1)) j).P j) := by
    rw [parts_c, hinv.len, Nat.add_sub_cancel]
  have hstep : StepOK sp (st sp al (cs.map (·.1)) j).P (j + 1) (parts sp al (st sp al (cs.map (·.1)) j) cs[j].1).c := by
    rw [hc, ← htr]; exact hok.2 j hjt
  have hphys : PhysStep sp (st sp al (cs.map (·.1)) j).P (j + 1)
      (parts sp al (st sp al (cs.map (·.1)) j) cs[j].1).c := by
    rw [hc, ← htr]; exact hph j hjt
  have hcopy : CopyStep sp (st sp al (cs.map (·.1)) j).P (j + 1)
      (parts sp al (st sp al (cs.map (·.1)) j) cs[j].1).c := by
    rw [hc, ← htr]; exact hev.2 j hjt
  have htree : treeAt sp (st sp al (cs.map (·.1)) j).P j := (hev.1 j (by omega)).tree
  have hst1 : st sp al (cs.map (·.1)) (j + 1) = step sp al (st sp al (cs.map (·.1)) j) cs[j].1 := by
    rw [st_succ sp al _ hjt, htr]
  rw [hst1] at hinv' hlog'
  -- E's transaction, on the run's state
  have hcongr := evictTrans_congr sp al hst (st sp al (cs.map (·.1)) (lastR cs j)).S hrelE
    (runEvict sp al ((esOf sp al cs).take j)).2.1 cs[j].1
  rw [← hR.sE] at hcongr
  obtain ⟨hE1, hE2⟩ := hm.evictTrans_ok hsp hinv hmk hlog hstep hphys hcopy htree hinv' hlog'
  have hE3 := HInv.evictTrans_ok hsp hinv hmk hm hh hlog hstep hphys hcopy htree hinv' hlog'
  have hE4 := NInv.evictTrans_ok hsp hinv hmk hm hn hlog hstep hphys hcopy htree hinv'
  have hfsj := st_fa_le sp al (cs.map (·.1)) (k := j) (by omega)
  have hstep_e : StepOK sp (st sp al (cs.map (·.1)) j).P (j + 1)
      (sp.exec cs[j].1 (j + 1) (view sp (st sp al (cs.map (·.1)) j).P j)) := by rw [← hc]; exact hstep
  obtain ⟨-, -, -, -, -, -, hrel1⟩ := step_congr_cut sp al hsp hinv hj hmk hex hvl hpol hR.rel hfsj cs[j].1 hstep_e
  rw [← hst1] at hrel1
  -- C's transaction
  obtain ⟨oc, oe, hsim, hoc⟩ := hR.sim
  obtain ⟨hC1, oc', oe', hsim', hoc'⟩ := evictTrans_sim hsp hj hmk hex hvl hpol hlog hL hR.cut hR.rel hfsj hm hh hn
    hsim hoc hstep hphys hcopy htree hinv'
  rw [← hR.sC] at hC1 hsim'
  have hcg2 : (evictTrans sp al (runEvict sp al ((esOf sp al cs).take j)).2.2 (runEvict sp al ((esOf sp al cs).take j)).1
      (runEvict sp al ((esOf sp al cs).take j)).2.1 cs[j].1).2 =
      (evictTrans sp al (st sp al (cs.map (·.1)) (lastR cs j)).S (st sp al (cs.map (·.1)) j)
        (runEvict sp al ((esOf sp al cs).take j)).2.1 cs[j].1).2 := by rw [hcongr.2, hR.sE]
  rw [← hcg2] at hsim'
  have hrtE : (evictTrans sp al (runEvict sp al ((esOf sp al cs).take j)).2.2 (runEvict sp al ((esOf sp al cs).take j)).1
      (runEvict sp al ((esOf sp al cs).take j)).2.1 cs[j].1).2.root =
      (evictStartup sp (st sp al (cs.map (·.1)) (lastR cs j)).S).root := by
    rw [evictTrans_root, hR.rootE]
  have hE1' : (evictTrans sp al (runEvict sp al ((esOf sp al cs).take j)).2.2 (runEvict sp al ((esOf sp al cs).take j)).1
      (runEvict sp al ((esOf sp al cs).take j)).2.1 cs[j].1).1.S = (st sp al (cs.map (·.1)) (j + 1)).S ∧
      (evictTrans sp al (runEvict sp al ((esOf sp al cs).take j)).2.2 (runEvict sp al ((esOf sp al cs).take j)).1
      (runEvict sp al ((esOf sp al cs).take j)).2.1 cs[j].1).1.D = (st sp al (cs.map (·.1)) (j + 1)).D := by
    obtain ⟨r1, r2, -⟩ := hcongr.1
    rw [r1, r2, hR.sE, hE1, hst1]
    exact ⟨rfl, rfl⟩
  have hlog1 := hR.log
  have hesj := esOf_getElem (sp := sp) (al := al) cs hjl
  have hCs := runEvictCut_succ (sp := sp) (al := al) cs hjl
  have hEs := runEvict_succ sp al (esOf sp al cs) hjE
  have hRs := runRestartsCut_succ (sp := sp) (al := al) cs hjl
  have hcm := cutMax_take_succ cs hjl
  rw [hesj] at hEs
  simp only at hEs
  have hndC' := hR.ndC.evictTrans sp al (runEvictCut sp al (cs.take j)).2.2 (runEvictCut sp al (cs.take j)).1 cs[j].1
  have hndE' := (slotsND_runEvict sp al ((esOf sp al cs).take j)).evictTrans sp al
    (runEvict sp al ((esOf sp al cs).take j)).2.2 (runEvict sp al ((esOf sp al cs).take j)).1 cs[j].1
  rw [← hst1, ← hcg2] at hE2 hE3 hE4
  have hroot1 : ∃ n, (step sp al (runEvictCut sp al (cs.take j)).1 cs[j].1).P.get? root = some n :=
    Option.isSome_iff_exists.mp hrel1.agree.rootP'
  cases hcj : cs[j].2.1 with
  | none =>
    simp only [hcj] at hCs hRs hEs hcm
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hEs
    have hm0 : cutMax ((cs.take (j + 1)).map (·.2.1)) = cutMax ((cs.take j).map (·.2.1)) := by rw [hcm]; simp
    have hlr := lastR_succ_none cs hjl hcj
    have hlogS : step sp al (runEvictCut sp al (cs.take j)).1 cs[j].1 = runRestartsCut sp al ((logOf cs).take (j + 1)) := by
      rw [hRs, hlog1]
    generalize hTC : evictTrans sp al (runEvictCut sp al (cs.take j)).2.2 (runEvictCut sp al (cs.take j)).1
      (runEvictCut sp al (cs.take j)).2.1 cs[j].1 = TC at hC1 hsim' hCs hndC'
    generalize hTE : evictTrans sp al (runEvict sp al ((esOf sp al cs).take j)).2.2 (runEvict sp al ((esOf sp al cs).take j)).1
      (runEvict sp al ((esOf sp al cs).take j)).2.1 cs[j].1 = TE at hsim' hrtE hE1' hEs hE2 hE3 hE4 hndE'
    have hL' := later_st hok hst (j1 := lastR cs j) (j := j + 1) (by have := lastR_le cs j; omega) (by omega)
    have hTCS : TC.1.S = cutStream (cutMax ((cs.take j).map (·.2.1))) (st sp al (cs.map (·.1)) (j + 1)).S := by
      rw [hC1, hrel1.stream]
    have hTCD : TC.1.D = (st sp al (cs.map (·.1)) (j + 1)).D := by rw [hC1, hrel1.dirty]
    -- E's extra unswizzles
    have hX : (extraY sp al cs j).map (CacheOp.unswizzle (evictStartup sp (st sp al (cs.map (·.1)) (lastR cs (j + 1))).S).root) =
        (extraY sp al cs j).map (CacheOp.unswizzle TE.2.root) := by rw [hlr, hrtE]
    have hreads' : ∀ t, CacheOp.read t ∈ cs[j].2.2 → lastFa (st sp al (cs.map (·.1)) (lastR cs j)).S ≤ t ∧ t ≤ j + 1 := by
      intro t ht
      obtain ⟨h1, h2⟩ := hreads j hjl hcj t ht
      exact ⟨Nat.le_trans (st_fa_mono hok hj (Nat.le_trans (lastR_le cs j) (Nat.le_succ j)) (by omega)) h1, h2⟩
    obtain ⟨n1, hn1⟩ := hroot1
    have hoc1 : oc'.hist = rootHist (runRestartsCut sp al ((logOf cs).take (j + 1))).P := by
      rw [hoc' n1 hn1, ← hlogS]; unfold rootHist; rw [hn1]; rfl
    have hoe1 : oe'.hist = rootHist (st sp al (cs.map (·.1)) (j + 1)).P := by
      obtain ⟨n2, hn2, hh2⟩ := hE2.root_hist hsim'.rootE
      rw [hh2]; unfold rootHist; rw [hn2]; rfl
    have hY : ∀ y ∈ extraY sp al cs j, y ∉ pointees sp oc'.hist := by
      intro y hy
      unfold extraY at hy
      rw [hoc1]
      have := (List.mem_filter.mp hy).2
      simpa using this
    have hcov : ∀ y, y ∈ pointees sp oe'.hist → y ∉ pointees sp oc'.hist → y ∈ extraY sp al cs j := by
      intro y hy1 hy2
      unfold extraY
      rw [hoe1] at hy1
      rw [hoc1] at hy2
      exact List.mem_filter.mpr ⟨hy1, by simpa using hy2⟩
    have hYnv : sp.virt = false → extraY sp al cs j = [] := by
      intro hv
      have hfk : lastFa (st sp al (cs.map (·.1)) (lastR cs j)).S ≤ j + 1 := by
        have := hrel1.fa
        have := st_fa_le sp al (cs.map (·.1)) (k := j + 1) (by omega)
        have hinv1 := inv_st sp al (cs.map (·.1)) hok hst (j + 1) (by omega)
        have := hinv1.spLt
        omega
      have hre := hrel1.agree.root_eq hv hfk
      have hrh : rootHist (runRestartsCut sp al ((logOf cs).take (j + 1))).P =
          rootHist (st sp al (cs.map (·.1)) (j + 1)).P := by
        unfold rootHist; rw [← hlogS, hre]
      unfold extraY
      rw [hrh]
      apply List.filter_eq_nil_iff.mpr
      intro y hy
      simp [hy]
    obtain ⟨oc'', oe'', hsim'', hh1, hh2⟩ := ops_sim (db := st sp al (cs.map (·.1)) (j + 1)) (k := j + 1) hls hL' hR.cut rfl
      (extraY sp al cs j) hYnv cs[j].2.2 TC.2 TE.2 oc' oe' hreads' hE2 hE3 hE4 hndC' hndE' hsim' hY hcov
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hCs]; exact hC1.trans hlogS
    · rw [hEs, hR.sE, hlr]
    · rw [hCs, hR.sC, hm0, hlr]
    · rw [hCs, hm0, hlr]; simp only; rw [hC1]; exact hrel1
    · rw [hm0, hlr]; exact hR.cut
    · rw [hCs, hEs]
      simp only
      rw [hX, hlr, hR.sC, hR.sE, hTCS, hTCD, hE1'.1, hE1'.2]
      refine ⟨oc'', oe'', hsim'', ?_⟩
      intro n hn
      rw [hC1, hlogS] at hn
      rw [hh1, hoc1]
      unfold rootHist; rw [hn]; rfl
    · rw [hEs, hlr]
      simp only
      rw [Mem.cacheOps_root, hrtE]
    · rw [hCs]; exact SlotsND.cacheOps sp _ _ _ _ _ hndC'

  | some c =>
    simp only [hcj] at hCs hRs hEs hcm
    simp only [Option.isSome_some, ↓reduceIte] at hEs
    have hlr := lastR_succ_some cs hjl hcj
    have hcut1 := hcut j hjl c hcj
    have hm1 : cutMax ((cs.take (j + 1)).map (·.2.1)) = max (cutMax ((cs.take j).map (·.2.1))) c := by
      rw [hcm]; rfl
    have hTCS : (evictTrans sp al (runEvictCut sp al (cs.take j)).2.2 (runEvictCut sp al (cs.take j)).1
        (runEvictCut sp al (cs.take j)).2.1 cs[j].1).1.S =
        cutStream (cutMax ((cs.take j).map (·.2.1))) (st sp al (cs.map (·.1)) (j + 1)).S := by
      rw [hC1, hrel1.stream]
    have hSC : cutStream c (evictTrans sp al (runEvictCut sp al (cs.take j)).2.2 (runEvictCut sp al (cs.take j)).1
        (runEvictCut sp al (cs.take j)).2.1 cs[j].1).1.S =
        cutStream (cutMax ((cs.take (j + 1)).map (·.2.1))) (st sp al (cs.map (·.1)) (j + 1)).S := by
      rw [hTCS, cutStream_cutStream, hm1, Nat.max_comm]
    have hSE := hE1'.1
    obtain ⟨ocs, oes, hsims, hocs⟩ := startup_sim hok hph hev hj hmk hex hvl (k := j + 1) (by simp; omega) hcut1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hCs]; simp only; rw [hRs, ← hlog1, ← hC1]
    · rw [hEs, hlr]; exact hSE
    · rw [hCs, hlr]; exact hSC
    · rw [hCs, hlr]
      simp only
      rw [hSC]
      obtain ⟨hag, hdn⟩ := recoverCut_dNodes sp al (cs.map (·.1)) hok hj hmk (k := j + 1) (by simp; omega) hex hvl hcut1
      obtain ⟨-, hD⟩ := recoverCut sp al (cs.map (·.1)) hok hst (k := j + 1) (by simp; omega) hex hvl hcut1
      exact ⟨rfl, hD, hag, hdn, hcut1.1, Nat.le_refl _⟩
    · rw [hlr]; exact hcut1
    · rw [hCs, hEs, hlr]
      simp only
      rw [hSC, hSE]
      exact ⟨ocs, oes, hsims, hocs⟩
    · rw [hEs, hlr]
      simp only
      rw [hSE]
    · rw [hCs]; exact slotsND_evictStartup sp _

/-- T12 with eviction: the run with eviction that restarts from safe cut
streams appends the records of the run that restarts from them without
eviction. -/
theorem evictCut_restartsCut (cs : List (T × Option Nat × List CacheOp)) (hok : RunOK sp al (cs.map (·.1)))
    (hph : PhysRunOK sp al (cs.map (·.1))) (hev : EvictRunOK sp al (cs.map (·.1)))
    (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) (hex : ExecRootOK sp) (hvl : VirtLiveOK sp)
    (hpol : PolicyCutOK al)
    (hcut : ∀ j (h : j < cs.length) c, cs[j].2.1 = some c →
      CutOK sp (cutMax ((cs.take (j + 1)).map (·.2.1))) (st sp al (cs.map (·.1)) (j + 1)) (j + 1))
    (hreads : ∀ j (h : j < cs.length), cs[j].2.1 = none → ∀ t, CacheOp.read t ∈ cs[j].2.2 →
      lastFa (st sp al (cs.map (·.1)) (j + 1)).S ≤ t ∧ t ≤ j + 1) :
    (runEvictCut sp al cs).1 = runRestartsCut sp al (logOf cs) := by
  have key : ∀ j ≤ cs.length, RunSim sp al cs j := by
    intro j
    induction j with
    | zero => intro _; exact runSim_zero cs hok hph hev hj hmk hex hvl
    | succ j ih => intro hj'; exact runSim_step cs hok hph hev hj hmk hex hvl hpol hcut hreads (by omega) (ih (by omega))
  have := (key cs.length (Nat.le_refl _)).log
  rw [List.take_length] at this
  have h2 : (logOf cs).take cs.length = logOf cs := List.take_of_length_le (by simp [logOf])
  rw [h2] at this
  exact this

theorem logOf_fst {C : Type} (cs : List (T × Option Nat × C)) : (logOf cs).map (·.1) = cs.map (·.1) := by
  simp [logOf]

theorem logOf_snd {C : Type} (cs : List (T × Option Nat × C)) : (logOf cs).map (·.2) = cs.map (·.2.1) := by
  simp [logOf]

/-- T12 with eviction: the run with eviction that restarts from safe cut
streams appends the records of the run without restarts (`restartCut`, for
the run without eviction that it equals). -/
theorem restartCut_evict (cs : List (T × Option Nat × List CacheOp)) (hok : RunOK sp al (cs.map (·.1)))
    (hph : PhysRunOK sp al (cs.map (·.1))) (hev : EvictRunOK sp al (cs.map (·.1)))
    (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) (hex : ExecRootOK sp) (hvl : VirtLiveOK sp)
    (hpol : PolicyCutOK al)
    (hcut : ∀ j (h : j < cs.length) c, cs[j].2.1 = some c →
      CutOK sp (cutMax ((cs.take (j + 1)).map (·.2.1))) (run sp al ((cs.map (·.1)).take (j + 1))) (j + 1))
    (hreads : ∀ j (h : j < cs.length), cs[j].2.1 = none → ∀ t, CacheOp.read t ∈ cs[j].2.2 →
      lastFa (run sp al ((cs.map (·.1)).take (j + 1))).S ≤ t ∧ t ≤ j + 1) :
    (runEvictCut sp al cs).1.S = cutStream (cutMax (cs.map (·.2.1))) (run sp al (cs.map (·.1))).S ∧
      (runEvictCut sp al cs).1.D = (run sp al (cs.map (·.1))).D ∧
      SameFrom sp (lastFa (run sp al (cs.map (·.1))).S) cs.length (runEvictCut sp al cs).1.P
        (run sp al (cs.map (·.1))).P := by
  rw [evictCut_restartsCut cs hok hph hev hj hmk hex hvl hpol hcut hreads]
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
