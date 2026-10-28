/-
Proofs about the physical layer with handles (bergdb item 009, phase 4a):
restarts, T2-C and T-READ with restarts over handles (`t2_handles`,
`tr_handles_restarts`). The startup with handles from the stream after T(k) has
the invariant and the invariant for reads at earlier times
(`heinv_hinvH_startup`, from `StartMem.handles`, SIS/Proof/HandleStart.lean). The
physical writer with handles depends on P only through its nodes
(`handleTrans_congr`), so a run with restarts keeps both (`handleInvR_all`).
-/
import SIS.Proof.HandleReadT

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-! ## The startup with handles from the stream after T(k) -/

section Startup

variable {sp : Spec V T} {al : Algo V T} {ts : List T}

/-- The startup with handles from a memory that meets `StartMem` in state db at
time k has the invariant for reads at earlier times: a pointer that holds no
canonical object names its pointee's latest version, which is good for t: the
pointee is clean, or the object is not pinned, so its node is clean and names a
version of the pointee good for t (and lemma M). -/
theorem StartMem.hinvH {sp : Spec V T} {db : DB V T} {M : Mem V} (hS : StartMem sp db M) {k : Nat}
    (hinv : Inv sp db k) (hls : LiveSub sp) : HInvH sp db db.S k (M.toH.linkD db.D) := by
  have hback : ∀ a o', (M.toH.linkD db.D).obj? a = some o' →
      ∃ o, M.obj? a = some o ∧ o' = M.toH.linkObj db.D a (M.objH o) := fun _ _ h => hS.back h
  have hcore := linkObjH_core M db.D
  have hpinD : ∀ a o y q, M.obj? a = some o → (M.toH.linkObj db.D a (M.objH o)).ptr? y = some q →
      (inD db.D o.node || a == M.root) = true → inD db.D y = true →
      ∃ b, q.handle = some b ∧ M.canonicalOf y = some b := fun _ _ _ _ ho hq hp hy => hS.pinD hinv ho hq hp hy
  have hrec : ∀ a o y q, M.obj? a = some o → (M.toH.linkObj db.D a (M.objH o)).ptr? y = some q →
      (M.toH.linkD db.D).ptrRef db.S y q = (db.S.lv y).map (·.recNo) ∧
      ((M.toH.linkD db.D).holdsCanonical q = true ∨
        (q.handle = none ∧ (M.toH.linkD db.D).slowRef db.S y q = (db.S.lv y).map (·.recNo))) :=
    fun _ _ _ _ ho hq => hS.refs hinv ho hq
  have hptr : ∀ a o y, M.obj? a = some o → y ∈ pointees sp o.hist →
      ∃ q, (M.toH.linkObj db.D a (M.objH o)).ptr? y = some q := fun _ _ _ ho hy => hS.ptrOf ho hy
  have hunpin : ∀ a o, M.obj? a = some o → (inD db.D o.node || a == M.root) = false →
      inD db.D o.node = false ∧ written sp o.node = true := fun _ _ ho hp => hS.unpin ho hp
  intro a o' ho' _ t ht hrt y hy
  obtain ⟨o, ho, rfl⟩ := hback a o' ho'
  obtain ⟨e1, -, -, e4, -⟩ := hcore a o
  rw [e4] at hy
  rw [e1] at hrt ⊢
  obtain ⟨n, hn, hh, -⟩ := hS.cc a o ho
  obtain ⟨q, hq⟩ := hptr a o y ho (mem_pointees_of_live hls hy)
  refine ⟨q, hq, ?_⟩
  rcases (hrec a o y q ho hq).2 with hc | ⟨hqn, hsr⟩
  · exact Or.inl hc
  · right; left
    obtain ⟨e, he, hye⟩ := hls _ _ hy
    have he' : e ∈ n.hist := by rw [← hh]; exact (mem_upTo.mp he).1
    have hyr : y ≠ SIS.root := hinv.ptr_ne_root hn he' hye
    have hry : reachable sp db.P t y = true := by
      rw [reachable_iff] at hrt ⊢
      obtain ⟨m', hm', hlt⟩ := hinv.ptrs o.node n hn e he' y hye
      exact Reach.child hrt hn (by rw [← hh]; exact hy) hm' hlt
    obtain ⟨w, hw, hg⟩ : ∃ w, db.S.lv y = some w ∧ good sp db.S db.P t w = true := by
      cases hyD : inD db.D y with
      | false => exact hinv.clean_good hls hyD (written_of_ne_root sp hyr) ht hry
      | true =>
        -- the object is not pinned: y has a canonical object, which rule 4 would link
        have hp : (inD db.D o.node || a == M.root) = false := by
          cases hp : (inD db.D o.node || a == M.root)
          · rfl
          · obtain ⟨b, hb, -⟩ := hpinD a o y q ho hq hp hyD
            rw [hqn] at hb; cases hb
        obtain ⟨hxD, hxw⟩ := hunpin a o ho hp
        obtain ⟨v, hv, hgv⟩ := hinv.clean_good hls hxD hxw ht hrt
        obtain ⟨rv, hrv⟩ := lv_versionAt hv
        obtain ⟨hvx, -⟩ := hinv.version_node hrv
        obtain ⟨⟨n', hn', hvh⟩, hch⟩ := (good_iff sp _ _ t v).mp hgv
        rw [hvx, hn, Option.some.injEq] at hn'
        subst hn'
        have hyv : y ∈ sp.live (v.hist.upTo t) := by rw [hvh, ← hh]; exact hy
        obtain ⟨r0, w0, -, hw0, -, hg0⟩ := hch y hyv
        obtain ⟨r', u', hu', hlu, hr0⟩ := lv_recNo_ge hw0
        exact ⟨u', hlu, hinv.newer hls (w0.level + 1) r0 r' y w0 u' (by omega) hw0 hu' hr0 t hg0⟩
    refine ⟨w.recNo, w, ?_, hinv.lv_at hw, hg⟩
    rw [hsr, hw]
    rfl

/-- T2-C's startup with handles: the startup with handles from the stream after
T(k) gives a memory with the invariant, and with the invariant for reads at
earlier times; every pointer holds a canonical object or has its pointee's latest
version as its slow path's reference, and the root's pointers to the nodes of D
hold canonical objects (what T9's invariant over handles needs, bergdb 005-62).
The memory before `Mem.toH` and rule 4 meets `StartMem` (`startMem_st`). -/
theorem heinv_hinvH_startup (hok : RunOK sp al ts) (hph : PhysRunOK sp al ts) (hj : al.stillDirty = javaTest sp)
    (hmk : al.mark = true) (hev : EvictRunOK sp al ts) {k : Nat} (hk : k ≤ ts.length) :
    HEInv sp (st sp al ts k) (st sp al ts k).S k (handleStartup sp (st sp al ts k).S) ∧
      HInvH sp (st sp al ts k) (st sp al ts k).S k (handleStartup sp (st sp al ts k).S) ∧
      (∀ a o y p, (handleStartup sp (st sp al ts k).S).obj? a = some o → o.ptr? y = some p →
        (handleStartup sp (st sp al ts k).S).holdsCanonical p = true ∨
          (handleStartup sp (st sp al ts k).S).slowRef (st sp al ts k).S y p =
            ((st sp al ts k).S.lv y).map (·.recNo)) ∧
      (∀ o y p, (handleStartup sp (st sp al ts k).S).obj? (handleStartup sp (st sp al ts k).S).root = some o →
        o.ptr? y = some p → inD (st sp al ts k).D y = true →
        (handleStartup sp (st sp al ts k).S).holdsCanonical p = true) := by
  obtain ⟨h1, h3, h4⟩ := heinv_startup hok hph hj hmk hev hk
  refine ⟨h1, ?_, h3, h4⟩
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hinv := inv_st sp al ts hok hst k hk
  have hD : (startup sp (st sp al ts k).S).D = (st sp al ts k).D := (T1_strong sp al ts hok hst hk).2
  unfold handleStartup
  rw [hD]
  exact (startMem_st hok hph hj hmk hev hk).hinvH hinv hok.1.liveSub

end Startup

/-! ## The physical writer with handles depends on P only through its nodes -/

section Congr

variable {sp : Spec V T} {P P' : Struct V} (hP : SameNodes P P')
include hP

theorem reachOnPathH_congr (S0 S : Stream V T) (j : Time) (path : List NodeId) :
    HMem.reachOnPath sp S0 S P j path = HMem.reachOnPath sp S0 S P' j path := by
  have hP' : ∀ x, P.get? x = P'.get? x := hP
  funext m x
  unfold HMem.reachOnPath
  simp only [hP']

theorem srcOKH_congr (j : Time) (y : NodeId) : srcOKH sp P j y = srcOKH sp P' j y := by
  have hP' : ∀ x, P.get? x = P'.get? x := hP
  funext p
  unfold srcOKH
  simp only [hP.reachable, hP']

theorem newPtr_congr (j : Time) (m : HMem V) (o : HObj V) (y : NodeId) :
    m.newPtr sp P j o y = m.newPtr sp P' j o y := by
  unfold HMem.newPtr
  rw [srcOKH_congr hP]

theorem applyChangeH_congr (j : Time) (c : Changes V) (m : HMem V) :
    m.applyChange sp P j c = m.applyChange sp P' j c := by
  unfold HMem.applyChange
  simp only [newPtr_congr hP]

theorem preWriteH_congr (S0 : Stream V T) (D : Dirty) (S : Stream V T) (c : Changes V) (m1 : HMem V) :
    preWriteH sp S0 ⟨P, D, S⟩ c m1 = preWriteH sp S0 ⟨P', D, S⟩ c m1 := by
  have hP' : ∀ x, P.get? x = P'.get? x := hP
  unfold preWriteH
  simp only [pathOf_congr hP, hP', reachOnPathH_congr hP, applyChangeH_congr hP]

end Congr

/-- A transaction of the physical writer with handles from states with the same
stream, D and nodes: the same record and D, and the same memory. -/
theorem handleTrans_congr (sp : Spec V T) (al : Algo V T) (hst : AlgOK sp al) (S0 : Stream V T)
    {db1 db2 : DB V T} (h : Rel db1 db2) (m : HMem V) (tr : T) :
    Rel (handleTrans sp al S0 db1 m tr).1 (handleTrans sp al S0 db2 m tr).1 ∧
      (handleTrans sp al S0 db1 m tr).2 = (handleTrans sp al S0 db2 m tr).2 := by
  obtain ⟨hS, hD, hP⟩ := h
  obtain ⟨P1, D1, S1⟩ := db1
  obtain ⟨P2, D2, S2⟩ := db2
  simp only at hS hD hP
  subst hS hD
  rw [handleTrans_eq, handleTrans_eq, handleAfter_eq, handleAfter_eq]
  simp only [preWriteH_congr hP, D1Of_congr hP, takenOf_congr hP]
  exact ⟨stepOf_congr hP al hst _ _ _ _ _ _, trivial⟩

/-! ## Runs with restarts -/

section Run

variable {sp : Spec V T} {al : Algo V T}

/-- What holds after the first j transactions of a run with handles and
restarts, with the last restart (or the start) after k1 transactions: the
stream of the last startup is the run's after k1; ⟨P, D, S⟩ is the run's after
j (the same stream and D, the same nodes); the memory has the invariant at j for
the startup from that stream, and the invariant for reads at earlier times. -/
def HandleInvR (sp : Spec V T) (al : Algo V T) (ts : List (T × Bool × List HCacheOp)) (j : Nat)
    (r : DB V T × HMem V × Stream V T) : Prop :=
  ∃ k1, k1 ≤ j ∧ r.2.2 = (st sp al (ts.map (·.1)) k1).S ∧ Rel r.1 (st sp al (ts.map (·.1)) j) ∧
    HEInv sp (st sp al (ts.map (·.1)) j) (st sp al (ts.map (·.1)) k1).S j r.2.1 ∧
    HInvH sp (st sp al (ts.map (·.1)) j) (st sp al (ts.map (·.1)) k1).S j r.2.1

/-- One transaction of a run with handles and restarts, and its operations or
its restart, keeps `HandleInvR`. -/
theorem handleInvR_step {ts : List (T × Bool × List HCacheOp)} (hok : RunOK sp al (ts.map (·.1)))
    (hph : PhysRunOK sp al (ts.map (·.1))) (hev : EvictRunOK sp al (ts.map (·.1)))
    (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) {j : Nat} (hjt : j < ts.length)
    {acc : DB V T × HMem V × Stream V T} (hI : HandleInvR sp al ts j acc) :
    HandleInvR sp al ts (j + 1)
      (if ts[j].2.1 then
        (startup sp (handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S,
          handleStartup sp (handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S,
          (handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S)
      else
        ((handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1,
          ts[j].2.2.foldl (HMem.cacheOp sp acc.2.2 (handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S
            (handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.D) (handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).2,
          acc.2.2)) := by
  obtain ⟨k1, hk1, hS0, hrel, hm, hh⟩ := hI
  have hst : AlgOK sp al := algOK_of sp al (Or.inl hj)
  have hjm : j < (ts.map (·.1)).length := by simp; omega
  have htr : (ts.map (·.1))[j] = ts[j].1 := by simp
  obtain ⟨hrel1, hmem1⟩ := handleTrans_congr sp al hst acc.2.2 hrel acc.2.1 ts[j].1
  have hrun := HEInv.run_step hok hph hev hj hmk hjm hm ts[j].2.2
  have hrunH := HInvH.run_step hok hph hev hj hmk hjm hm hh ts[j].2.2
  rw [htr, ← hS0] at hrun hrunH
  obtain ⟨f1, f2⟩ := hrun
  have hrel' : Rel (handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1 (st sp al (ts.map (·.1)) (j + 1)) := by
    rw [← f1]; exact hrel1
  unfold HandleInvR
  split
  · -- A restart after j + 1: the logical startup and the startup with handles from the stream.
    refine ⟨j + 1, Nat.le_refl _, hrel'.1, ?_, ?_, ?_⟩
    · show Rel (startup sp (handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S) _
      rw [hrel'.1]
      have hT1 := T1_strong sp al (ts.map (·.1)) hok hst (k := j + 1) (by simp; omega)
      exact ⟨rfl, hT1.2, hT1.1⟩
    · show HEInv sp _ _ _ (handleStartup sp (handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S)
      rw [hrel'.1]
      exact (heinv_hinvH_startup hok hph hj hmk hev (by simp; omega)).1
    · show HInvH sp _ _ _ (handleStartup sp (handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S)
      rw [hrel'.1]
      exact (heinv_hinvH_startup hok hph hj hmk hev (by simp; omega)).2.1
  · -- No restart: the same startup stream; the memory is the one from the run's state.
    refine ⟨k1, by omega, hS0, hrel', ?_, ?_⟩
    · show HEInv sp _ _ _ (ts[j].2.2.foldl (HMem.cacheOp sp acc.2.2
        (handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S
        (handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.D) (handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).2)
      rw [hrel1.1, hrel1.2.1, hmem1, ← hS0]
      exact f2
    · show HInvH sp _ _ _ (ts[j].2.2.foldl (HMem.cacheOp sp acc.2.2
        (handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.S
        (handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).1.D) (handleTrans sp al acc.2.2 acc.1 acc.2.1 ts[j].1).2)
      rw [hrel1.1, hrel1.2.1, hmem1, ← hS0]
      exact hrunH

/-- `HandleInvR` holds after every prefix of a run with handles and restarts. -/
theorem handleInvR_all {ts : List (T × Bool × List HCacheOp)} (hok : RunOK sp al (ts.map (·.1)))
    (hph : PhysRunOK sp al (ts.map (·.1))) (hev : EvictRunOK sp al (ts.map (·.1)))
    (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) :
    ∀ j ≤ ts.length, HandleInvR sp al ts j (runHandles sp al (ts.take j)) := by
  intro j
  induction j with
  | zero =>
    intro _
    have h0 : runHandles sp al (ts.take 0) = (init sp, handleStartup sp (init sp).S, (init sp).S) := by
      simp [runHandles]
    rw [h0]
    refine ⟨0, Nat.le_refl _, by rw [st_zero], by rw [st_zero]; exact ⟨rfl, rfl, SameNodes.refl _⟩, ?_, ?_⟩
    · rw [st_zero]
      exact heinv_init hok hph hj hmk hev
    · rw [st_zero]
      exact HInvH.of_live (inv_init sp hok.1) hok.1.liveSub (heinv_init hok hph hj hmk hev)
  | succ j ih =>
    intro hjt
    rw [runHandles_succ sp al ts (by omega)]
    exact handleInvR_step hok hph hev hj hmk (by omega) (ih (by omega))

end Run

/-! ## T2-C and T-READ with restarts over handles -/

/-- `T2_handles` (SIS/HandleTheorems.lean) holds. -/
theorem t2_handles (sp : Spec V T) (al : Algo V T) : T2_handles sp al := by
  intro ts hok hph hev hj hmk j hjt db r m
  obtain ⟨k1, hk1, hS0, hrel, hm, -⟩ := handleInvR_all hok hph hev hj hmk j hjt
  have hst : st sp al (ts.map (·.1)) j = run sp al ((ts.take j).map (·.1)) := by
    unfold st; rw [List.map_take]
  have hst1 : st sp al (ts.map (·.1)) k1 = run sp al ((ts.take k1).map (·.1)) := by
    unfold st; rw [List.map_take]
  rw [hst] at hrel hm
  rw [hst1] at hS0 hm
  rw [← hS0] at hm
  obtain ⟨e1, e2, e3⟩ := hrel
  exact ⟨e1, e2, e3, k1, hk1, hS0, hm.tbl, hm.hcan, hm.hsnap, hm.hslot, hm.ruleR, hm.liveW, hm.hwritten⟩

/-- `TR_handles_restarts` (SIS/HandleTheorems.lean) holds. -/
theorem tr_handles_restarts (sp : Spec V T) (al : Algo V T) : TR_handles_restarts sp al := by
  intro ts hok hph hev hj hmk j hjt t ht db r m
  obtain ⟨k1, -, hS0, -, hm, hh⟩ := handleInvR_all hok hph hev hj hmk j hjt
  have hst : st sp al (ts.map (·.1)) j = run sp al ((ts.take j).map (·.1)) := by
    unfold st; rw [List.map_take]
  have hinv := inv_st sp al (ts.map (·.1)) hok (algOK_of sp al (Or.inl hj)) j
    (by rw [List.length_map]; exact hjt)
  rw [hst] at hm hh hinv
  rw [← hS0] at hm hh
  exact read_list_view (hm.readT_ok hinv hok.1.liveSub hh ht).2.2

end SIS
