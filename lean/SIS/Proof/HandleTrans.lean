/-
Proofs about the physical layer with handles (bergdb item 009, step 2d), part
11: one transaction of the physical writer with handles (`handleTrans`) appends
the model's record and leaves the model's D, and the memory after it, and after
any reads and evictions, has the invariant; and so for every transaction of a
run with any reads and evictions and no restart.
-/
import SIS.Proof.HandleStepInv

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- The transaction with handles after the writer's view, from the memory m1
that the view leaves, with the change c. -/
def handleAfter (sp : Spec V T) (al : Algo V T) (S0 : Stream V T) (db : DB V T) (tr : T) (c : Changes V)
    (m1 : HMem V) : DB V T × HMem V :=
  let i := db.S.length
  let path := pathOf sp db.P c i
  let path' := path.mergeSort (fun a b => decide
    (((db.P.get? b).map (·.level)).getD 0 ≤ ((db.P.get? a).map (·.level)).getD 0))
  let m2 := path'.foldl (HMem.reachOnPath sp S0 db.S db.P i path) m1
  let m3 := m2.applyChange sp db.P i c
  let P := db.P.apply i c
  let w2 := m3.writeNodes sp S0 db.D i ((c.new.filter (·.isData)).map (·.id))
  let vs0 := w2.2
  let gd3 := gotDirty3 sp al db.S vs0 P c db.D i
  let D1 : Dirty := db.D ++ gd3.map (fun x => (x, i))
  let s : Nat := startupPos al db.S D1 i tr
  let fa : Nat := firstAvail al db.S D1 i tr s
  let taken := byLevel P ((D1.filter (fun e : NodeId × Nat => decide (e.2 ≤ s))).map (·.1))
  let D2 : Dirty := D1.filter (fun e : NodeId × Nat => decide (s < e.2))
  let w6 := w2.1.writeNodes sp S0 D1 i taken
  let vs := vs0 ++ w6.2
  let S' : Stream V T := db.S.building vs
  let r7 := stillDirtyOf al S' P D2 i taken
  let R : Record V T :=
    { trans := some tr, sp := s, vers := vs, gd := gd3 ++ r7.2, top := topOf sp P S' s, fa := fa }
  ({ P := P, D := r7.1, S := db.S ++ [R] }, w6.1)

/-- The memory with handles before the writes: after the writer's paths and the
change. -/
def preWriteH (sp : Spec V T) (S0 : Stream V T) (db : DB V T) (c : Changes V) (m1 : HMem V) : HMem V :=
  let i := db.S.length
  let path := pathOf sp db.P c i
  let path' := path.mergeSort (fun a b => decide
    (((db.P.get? b).map (·.level)).getD 0 ≤ ((db.P.get? a).map (·.level)).getD 0))
  (path'.foldl (HMem.reachOnPath sp S0 db.S db.P i path) m1).applyChange sp db.P i c

theorem handleAfter_eq (sp : Spec V T) (al : Algo V T) (S0 : Stream V T) (db : DB V T) (tr : T)
    (c : Changes V) (m1 : HMem V) :
    handleAfter sp al S0 db tr c m1 =
      (stepOf sp al db tr c
        ((preWriteH sp S0 db c m1).writeNodes sp S0 db.D db.S.length ((c.new.filter (·.isData)).map (·.id))).2
        (((preWriteH sp S0 db c m1).writeNodes sp S0 db.D db.S.length ((c.new.filter (·.isData)).map (·.id))).2 ++
          (((preWriteH sp S0 db c m1).writeNodes sp S0 db.D db.S.length
            ((c.new.filter (·.isData)).map (·.id))).1.writeNodes sp S0
            (D1Of sp al db c ((preWriteH sp S0 db c m1).writeNodes sp S0 db.D db.S.length
              ((c.new.filter (·.isData)).map (·.id))).2) db.S.length
            (takenOf sp al db tr c ((preWriteH sp S0 db c m1).writeNodes sp S0 db.D db.S.length
              ((c.new.filter (·.isData)).map (·.id))).2)).2),
       (((preWriteH sp S0 db c m1).writeNodes sp S0 db.D db.S.length
            ((c.new.filter (·.isData)).map (·.id))).1.writeNodes sp S0
            (D1Of sp al db c ((preWriteH sp S0 db c m1).writeNodes sp S0 db.D db.S.length
              ((c.new.filter (·.isData)).map (·.id))).2) db.S.length
            (takenOf sp al db tr c ((preWriteH sp S0 db c m1).writeNodes sp S0 db.D db.S.length
              ((c.new.filter (·.isData)).map (·.id))).2)).1) := rfl

theorem handleTrans_eq (sp : Spec V T) (al : Algo V T) (S0 : Stream V T) (db : DB V T) (m : HMem V) (tr : T) :
    handleTrans sp al S0 db m tr = handleAfter sp al S0 db tr
      (sp.exec tr db.S.length (m.view sp S0 db.S (db.S.length - 1)).2)
      (m.view sp S0 db.S (db.S.length - 1)).1 := rfl

section Trans

variable {sp : Spec V T} {al : Algo V T} {db : DB V T} {tr : T} {S0 : Stream V T} {k : Nat} {m : HMem V}

/-- One transaction of the physical writer with handles: the model's record and
D, and the invariant of the next state. -/
theorem HEInv.handleTrans_ok (hsp : SpecOK sp) (hinv : Inv sp db k) (hmk : al.mark = true)
    (hm : HEInv sp db S0 k m) (hev : EvLogic sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) (hphys : PhysStep sp db.P (k + 1) (parts sp al db tr).c)
    (hcopy : CopyStep sp db.P (k + 1) (parts sp al db tr).c) (htree : treeAt sp db.P k)
    (hinv' : Inv sp (step sp al db tr) (k + 1)) (hev' : EvLogic sp (step sp al db tr) (k + 1)) :
    (handleTrans sp al S0 db m tr).1 = step sp al db tr ∧
      HEInv sp (step sp al db tr) S0 (k + 1) (handleTrans sp al S0 db m tr).2 := by
  have hls : LiveSub sp := hsp.liveSub
  have hlen := hinv.len
  have hK1 : k + 1 - 1 = k := by omega
  obtain ⟨hm1, hv⟩ := hm.view_ok hinv hls hev
  have hc : sp.exec tr db.S.length (m.view sp S0 db.S (db.S.length - 1)).2 = (parts sp al db tr).c := by
    rw [hlen, hK1, hv, parts_c, hlen, hK1]
  rw [handleTrans_eq, hc, handleAfter_eq]
  have hm1' : HEInv sp db S0 k (m.view sp S0 db.S (db.S.length - 1)).1 := by rw [hlen, hK1]; exact hm1
  generalize (m.view sp S0 db.S (db.S.length - 1)).1 = m1 at hm1' ⊢
  -- The writer's paths.
  have hpr : ∀ p ∈ pathOf sp db.P (parts sp al db tr).c (k + 1), reachable sp db.P k p = true := by
    intro p hp; have := (mem_pathOf hp).1; rw [hK1] at this; exact this
  have hparent : ∀ x ∈ pathOf sp db.P (parts sp al db tr).c (k + 1), x ≠ SIS.root →
      ∃ p ∈ pathOf sp db.P (parts sp al db tr).c (k + 1), ∃ np nx, db.P.get? p = some np ∧
        db.P.get? x = some nx ∧ nx.level < np.level ∧ x ∈ sp.live (np.hist.upTo k) := by
    intro x hx hxr
    have hrx := (mem_pathOf hx).1
    rw [hK1] at hrx
    obtain ⟨p, np, nx, hrp, hnp, hnx, hlt, hxl⟩ := reach_parent hrx hxr
    refine ⟨p, pathOf_parent hx (by rw [hK1]; exact hrp) hnp (by rw [hK1]; exact hxl) hnx hlt, np, nx, hnp,
      hnx, hlt, hxl⟩
  have hpnd : (pathOf sp db.P (parts sp al db tr).c (k + 1)).Nodup := by
    unfold pathOf; exact nodup_filter (nodup_eraseDups _) _
  have hsorted := pairwise_byLevelDesc db.P (pathOf sp db.P (parts sp al db tr).c (k + 1))
  obtain ⟨hm2, hpd⟩ := HEInv.reachPath_ok (S0 := S0) hinv hls hev hpr hparent
    ((pathOf sp db.P (parts sp al db tr).c (k + 1)).mergeSort (fun a b => decide (lev db.P b ≤ lev db.P a))) []
    m1 hm1' (fun a ha => by cases ha)
    (fun x => by rw [List.nil_append]; exact (List.mergeSort_perm _ _).mem_iff)
    (by rw [List.nil_append]; exact (List.mergeSort_perm _ _).nodup_iff.mpr hpnd)
    (by rw [List.nil_append]; exact hsorted)
  -- The change.
  have ha := hm2.applyChange_ok hinv hls hpd hstep hphys hcopy htree
  have hpre : preWriteH sp S0 db (parts sp al db tr).c m1 =
      (((pathOf sp db.P (parts sp al db tr).c (k + 1)).mergeSort (fun a b => decide (lev db.P b ≤ lev db.P a))).foldl
        (HMem.reachOnPath sp S0 db.S db.P (k + 1) (pathOf sp db.P (parts sp al db tr).c (k + 1))) m1).applyChange
        sp db.P (k + 1) (parts sp al db tr).c := by
    unfold preWriteH; rw [hlen]; rfl
  rw [hpre, hlen]
  generalize (((pathOf sp db.P (parts sp al db tr).c (k + 1)).mergeSort
    (fun a b => decide (lev db.P b ≤ lev db.P a))).foldl
      (HMem.reachOnPath sp S0 db.S db.P (k + 1) (pathOf sp db.P (parts sp al db tr).c (k + 1))) m1).applyChange
      sp db.P (k + 1) (parts sp al db tr).c = m3 at ha ⊢
  -- The writes.
  obtain ⟨e1, e2, e3, e4⟩ := ha.loops_vs hsp hinv hmk hstep hinv'
  have hdata : ((parts sp al db tr).c.new.filter (·.isData)).map (·.id) = dataIds sp al db tr := rfl
  rw [hdata]
  rw [e1]
  rw [← parts_D1Of, ← parts_takenOf]
  rw [e1] at e3
  rw [e3]
  refine ⟨(step_eq_stepOf sp al db tr).symm, ?_⟩
  -- the frame of the two loops
  have hdnd : (dataIds sp al db tr).Nodup := (List.Sublist.map _ List.filter_sublist).nodup hstep.distinct
  have hdisj : ∀ x ∈ dataIds sp al db tr, x ∉ (parts sp al db tr).taken := by
    intro x hx hxt
    obtain ⟨d, hxd, -⟩ := step_taken_inD (al := al) (tr := tr) hinv hxt
    obtain ⟨hnone, -⟩ := step_dataIds_spec sp al db tr hinv hstep hx
    have := hinv.dIndex (x, d) hxd
    simp [isIndex, hnone] at this
  have hfr := loopsFrameH sp S0 db.D (parts sp al db tr).D1 (k + 1) (dataIds sp al db tr)
    (parts sp al db tr).taken m3 hdnd (step_taken_nodup sp al db tr hinv) ha.tbl hdisj
  exact ha.final_ok hsp hinv hmk hstep hinv' hev' hfr e4

end Trans

/-! ## Runs with reads and evictions -/

theorem runHandles_succ (sp : Spec V T) (al : Algo V T) (ts : List (T × Bool × List HCacheOp)) {j : Nat}
    (hj : j < ts.length) :
    runHandles sp al (ts.take (j + 1)) =
      (if ts[j].2.1 then
        (startup sp (handleTrans sp al (runHandles sp al (ts.take j)).2.2 (runHandles sp al (ts.take j)).1
            (runHandles sp al (ts.take j)).2.1 ts[j].1).1.S,
          handleStartup sp (handleTrans sp al (runHandles sp al (ts.take j)).2.2 (runHandles sp al (ts.take j)).1
            (runHandles sp al (ts.take j)).2.1 ts[j].1).1.S,
          (handleTrans sp al (runHandles sp al (ts.take j)).2.2 (runHandles sp al (ts.take j)).1
            (runHandles sp al (ts.take j)).2.1 ts[j].1).1.S)
      else
        ((handleTrans sp al (runHandles sp al (ts.take j)).2.2 (runHandles sp al (ts.take j)).1
            (runHandles sp al (ts.take j)).2.1 ts[j].1).1,
          ts[j].2.2.foldl (HMem.cacheOp sp (runHandles sp al (ts.take j)).2.2
            (handleTrans sp al (runHandles sp al (ts.take j)).2.2 (runHandles sp al (ts.take j)).1
              (runHandles sp al (ts.take j)).2.1 ts[j].1).1.S
            (handleTrans sp al (runHandles sp al (ts.take j)).2.2 (runHandles sp al (ts.take j)).1
              (runHandles sp al (ts.take j)).2.1 ts[j].1).1.D)
            (handleTrans sp al (runHandles sp al (ts.take j)).2.2 (runHandles sp al (ts.take j)).1
              (runHandles sp al (ts.take j)).2.1 ts[j].1).2,
          (runHandles sp al (ts.take j)).2.2)) := by
  have h1 : ts.take (j + 1) = ts.take j ++ [ts[j]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj]; rfl
  unfold runHandles
  rw [h1, List.foldl_append]
  rfl

section Run

variable {sp : Spec V T} {al : Algo V T}

/-- One transaction of a run with handles, and its reads and evictions: the
model's record and D, and the invariant. -/
theorem HEInv.run_step {ts : List T} (hok : RunOK sp al ts) (hph : PhysRunOK sp al ts)
    (hev : EvictRunOK sp al ts) (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) {j : Nat}
    (hjt : j < ts.length) {S0 : Stream V T} {m : HMem V} (hm : HEInv sp (st sp al ts j) S0 j m)
    (ops : List HCacheOp) :
    (handleTrans sp al S0 (st sp al ts j) m ts[j]).1 = st sp al ts (j + 1) ∧
      HEInv sp (st sp al ts (j + 1)) S0 (j + 1)
        (ops.foldl (HMem.cacheOp sp S0 (handleTrans sp al S0 (st sp al ts j) m ts[j]).1.S
          (handleTrans sp al S0 (st sp al ts j) m ts[j]).1.D) (handleTrans sp al S0 (st sp al ts j) m ts[j]).2) := by
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
  obtain ⟨h1, h2⟩ := hm.handleTrans_ok hsp hinv hmk hlog hstep hphys hcopy htree hinv' hlog'
  refine ⟨h1, ?_⟩
  rw [h1]
  exact HEInv.cacheOps hinv' ops _ h2

/-- T-CACHE for a run with handles and no restart: from a startup memory with
the invariant, after every transaction and its reads and evictions the
database is the model's (the same records, D and P) and the memory has the
invariant. -/
theorem TC_runH {ts : List (T × Bool × List HCacheOp)} (hok : RunOK sp al (ts.map (·.1)))
    (hph : PhysRunOK sp al (ts.map (·.1))) (hev : EvictRunOK sp al (ts.map (·.1)))
    (hj : al.stillDirty = javaTest sp) (hmk : al.mark = true) (hnr : ∀ p ∈ ts, p.2.1 = false)
    (h0 : HEInv sp (init sp) (init sp).S 0 (handleStartup sp (init sp).S)) :
    ∀ j ≤ ts.length, (runHandles sp al (ts.take j)).1 = st sp al (ts.map (·.1)) j ∧
      (runHandles sp al (ts.take j)).2.2 = (init sp).S ∧
      HEInv sp (st sp al (ts.map (·.1)) j) (init sp).S j (runHandles sp al (ts.take j)).2.1 := by
  intro j
  induction j with
  | zero =>
    intro _
    have : runHandles sp al (ts.take 0) = (init sp, handleStartup sp (init sp).S, (init sp).S) := by
      simp [runHandles]
    rw [this, st_zero]
    exact ⟨rfl, rfl, h0⟩
  | succ j ih =>
    intro hjt
    obtain ⟨e1, e2, e3⟩ := ih (by omega)
    have hjt' : j < ts.length := by omega
    have hjm : j < (ts.map (·.1)).length := by simp; omega
    rw [runHandles_succ sp al ts hjt']
    have hnrj : ts[j].2.1 = false := hnr _ (List.getElem_mem hjt')
    simp only [hnrj, Bool.false_eq_true, ↓reduceIte]
    rw [e1, e2]
    have htr : (ts.map (·.1))[j] = ts[j].1 := by simp
    have := HEInv.run_step hok hph hev hj hmk hjm e3 ts[j].2.2
    rw [htr] at this
    obtain ⟨f1, f2⟩ := this
    exact ⟨f1, rfl, f2⟩

end Run

end SIS
