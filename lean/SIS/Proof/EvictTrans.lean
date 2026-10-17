/-
Proofs for stage 2 (bergdb item 001, WP E3), part 12: one transaction of the
physical writer with eviction appends the model's record and leaves the model's
D, and the memory after it, and after any cache operations, has the invariant.
-/
import SIS.Proof.EvictStepInv

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- The transaction after the writer's view, from the memory m1 that the view
leaves, with the change c. -/
def evictAfter (sp : Spec V T) (al : Algo V T) (S0 : Stream V T) (db : DB V T) (tr : T) (c : Changes V)
    (m1 : Mem V) : DB V T × Mem V :=
  let i := db.S.length
  let path := pathOf sp db.P c i
  let path' := path.mergeSort (fun a b => decide
    (((db.P.get? b).map (·.level)).getD 0 ≤ ((db.P.get? a).map (·.level)).getD 0))
  let m2 := path'.foldl (Mem.reachOnPath4 sp S0 db.S db.P i path) m1
  let m3 := m2.applyChange4 sp db.P i c
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

/-- Steps 3 to 8 of a transaction, from the versions of step 2 (vs0), and the
record's versions (vs): as `stepWith`. -/
def D1Of (sp : Spec V T) (al : Algo V T) (db : DB V T) (c : Changes V) (vs0 : List (Version V)) : Dirty :=
  let i := db.S.length
  let P := db.P.apply i c
  let gd3 := gotDirty3 sp al db.S vs0 P c db.D i
  db.D ++ gd3.map (fun x => (x, i))

def takenOf (sp : Spec V T) (al : Algo V T) (db : DB V T) (tr : T) (c : Changes V) (vs0 : List (Version V)) :
    List NodeId :=
  let i := db.S.length
  let P := db.P.apply i c
  let D1 := D1Of sp al db c vs0
  let s : Nat := startupPos al db.S D1 i tr
  byLevel P ((D1.filter (fun e : NodeId × Nat => decide (e.2 ≤ s))).map (·.1))

def stepOf (sp : Spec V T) (al : Algo V T) (db : DB V T) (tr : T) (c : Changes V)
    (vs0 vs : List (Version V)) : DB V T :=
  let i := db.S.length
  let P := db.P.apply i c
  let gd3 := gotDirty3 sp al db.S vs0 P c db.D i
  let D1 : Dirty := db.D ++ gd3.map (fun x => (x, i))
  let s : Nat := startupPos al db.S D1 i tr
  let fa : Nat := firstAvail al db.S D1 i tr s
  let taken := byLevel P ((D1.filter (fun e : NodeId × Nat => decide (e.2 ≤ s))).map (·.1))
  let D2 : Dirty := D1.filter (fun e : NodeId × Nat => decide (s < e.2))
  let S' : Stream V T := db.S.building vs
  let r7 := stillDirtyOf al S' P D2 i taken
  let R : Record V T :=
    { trans := some tr, sp := s, vers := vs, gd := gd3 ++ r7.2, top := topOf sp P S' s, fa := fa }
  { P := P, D := r7.1, S := db.S ++ [R] }

/-- The memory before the writes: after the writer's paths and the change. -/
def preWrite (sp : Spec V T) (S0 : Stream V T) (db : DB V T) (c : Changes V) (m1 : Mem V) : Mem V :=
  let i := db.S.length
  let path := pathOf sp db.P c i
  let path' := path.mergeSort (fun a b => decide
    (((db.P.get? b).map (·.level)).getD 0 ≤ ((db.P.get? a).map (·.level)).getD 0))
  (path'.foldl (Mem.reachOnPath4 sp S0 db.S db.P i path) m1).applyChange4 sp db.P i c

theorem evictAfter_eq (sp : Spec V T) (al : Algo V T) (S0 : Stream V T) (db : DB V T) (tr : T) (c : Changes V)
    (m1 : Mem V) :
    evictAfter sp al S0 db tr c m1 =
      (stepOf sp al db tr c
        ((preWrite sp S0 db c m1).writeNodes sp S0 db.D db.S.length ((c.new.filter (·.isData)).map (·.id))).2
        (((preWrite sp S0 db c m1).writeNodes sp S0 db.D db.S.length ((c.new.filter (·.isData)).map (·.id))).2 ++
          (((preWrite sp S0 db c m1).writeNodes sp S0 db.D db.S.length
            ((c.new.filter (·.isData)).map (·.id))).1.writeNodes sp S0
            (D1Of sp al db c ((preWrite sp S0 db c m1).writeNodes sp S0 db.D db.S.length
              ((c.new.filter (·.isData)).map (·.id))).2) db.S.length
            (takenOf sp al db tr c ((preWrite sp S0 db c m1).writeNodes sp S0 db.D db.S.length
              ((c.new.filter (·.isData)).map (·.id))).2)).2),
       (((preWrite sp S0 db c m1).writeNodes sp S0 db.D db.S.length
            ((c.new.filter (·.isData)).map (·.id))).1.writeNodes sp S0
            (D1Of sp al db c ((preWrite sp S0 db c m1).writeNodes sp S0 db.D db.S.length
              ((c.new.filter (·.isData)).map (·.id))).2) db.S.length
            (takenOf sp al db tr c ((preWrite sp S0 db c m1).writeNodes sp S0 db.D db.S.length
              ((c.new.filter (·.isData)).map (·.id))).2)).1) := rfl

theorem step_eq_stepOf (sp : Spec V T) (al : Algo V T) (db : DB V T) (tr : T) :
    step sp al db tr = stepOf sp al db tr (parts sp al db tr).c (parts sp al db tr).vs0 (parts sp al db tr).vs :=
  rfl

theorem parts_D1Of (sp : Spec V T) (al : Algo V T) (db : DB V T) (tr : T) :
    (parts sp al db tr).D1 = D1Of sp al db (parts sp al db tr).c (parts sp al db tr).vs0 := rfl

theorem parts_takenOf (sp : Spec V T) (al : Algo V T) (db : DB V T) (tr : T) :
    (parts sp al db tr).taken = takenOf sp al db tr (parts sp al db tr).c (parts sp al db tr).vs0 := rfl

theorem evictTrans_eq (sp : Spec V T) (al : Algo V T) (S0 : Stream V T) (db : DB V T) (m : Mem V) (tr : T) :
    evictTrans sp al S0 db m tr = evictAfter sp al S0 db tr
      (sp.exec tr db.S.length (m.view4 sp S0 db.S (db.S.length - 1)).2)
      (m.view4 sp S0 db.S (db.S.length - 1)).1 := rfl

section Trans

variable {sp : Spec V T} {al : Algo V T} {db : DB V T} {tr : T} {S0 : Stream V T} {k : Nat} {m : Mem V}

/-- One transaction of the physical writer with eviction: the model's record
and D, and the invariant of the next state. -/
theorem EInv.evictTrans_ok (hsp : SpecOK sp) (hinv : Inv sp db k) (hmk : al.mark = true)
    (hm : EInv sp db S0 k m) (hev : EvLogic sp db k)
    (hstep : StepOK sp db.P (k + 1) (parts sp al db tr).c) (hphys : PhysStep sp db.P (k + 1) (parts sp al db tr).c)
    (hcopy : CopyStep sp db.P (k + 1) (parts sp al db tr).c) (htree : treeAt sp db.P k)
    (hinv' : Inv sp (step sp al db tr) (k + 1)) (hev' : EvLogic sp (step sp al db tr) (k + 1)) :
    (evictTrans sp al S0 db m tr).1 = step sp al db tr ∧
      EInv sp (step sp al db tr) S0 (k + 1) (evictTrans sp al S0 db m tr).2 := by
  have hls : LiveSub sp := hsp.liveSub
  have hlen := hinv.len
  have hK1 : k + 1 - 1 = k := by omega
  obtain ⟨hm1, hv⟩ := hm.view4_ok hinv hls hev
  have hc : sp.exec tr db.S.length (m.view4 sp S0 db.S (db.S.length - 1)).2 = (parts sp al db tr).c := by
    rw [hlen, hK1, hv, parts_c, hlen, hK1]
  rw [evictTrans_eq, hc, evictAfter_eq]
  have hm1' : EInv sp db S0 k (m.view4 sp S0 db.S (db.S.length - 1)).1 := by rw [hlen, hK1]; exact hm1
  generalize (m.view4 sp S0 db.S (db.S.length - 1)).1 = m1 at hm1' ⊢
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
    refine ⟨p, pathOf_parent hx (by rw [hK1]; exact hrp) hnp (by rw [hK1]; exact hxl) hnx hlt, np, nx, hnp, hnx,
      hlt, hxl⟩
  have hpnd : (pathOf sp db.P (parts sp al db tr).c (k + 1)).Nodup := by
    unfold pathOf; exact nodup_filter (nodup_eraseDups _) _
  have hsorted := pairwise_byLevelDesc db.P (pathOf sp db.P (parts sp al db tr).c (k + 1))
  obtain ⟨hm2, hpd⟩ := EInv.reachPath4_ok (S0 := S0) hinv hls hev hpr hparent
    ((pathOf sp db.P (parts sp al db tr).c (k + 1)).mergeSort (fun a b => decide (lev db.P b ≤ lev db.P a))) []
    m1 hm1' (fun a ha => by cases ha)
    (fun x => by rw [List.nil_append]; exact (List.mergeSort_perm _ _).mem_iff)
    (by rw [List.nil_append]; exact (List.mergeSort_perm _ _).nodup_iff.mpr hpnd)
    (by rw [List.nil_append]; exact hsorted)
  -- The change.
  have ha := hm2.applyChange4_ok hinv hls hpd hstep hphys hcopy htree
  have hpre : preWrite sp S0 db (parts sp al db tr).c m1 =
      (((pathOf sp db.P (parts sp al db tr).c (k + 1)).mergeSort (fun a b => decide (lev db.P b ≤ lev db.P a))).foldl
        (Mem.reachOnPath4 sp S0 db.S db.P (k + 1) (pathOf sp db.P (parts sp al db tr).c (k + 1))) m1).applyChange4
        sp db.P (k + 1) (parts sp al db tr).c := by
    unfold preWrite; rw [hlen]; rfl
  rw [hpre, hlen]
  generalize (((pathOf sp db.P (parts sp al db tr).c (k + 1)).mergeSort
    (fun a b => decide (lev db.P b ≤ lev db.P a))).foldl
      (Mem.reachOnPath4 sp S0 db.S db.P (k + 1) (pathOf sp db.P (parts sp al db tr).c (k + 1))) m1).applyChange4
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
  have hfr := loopsFrame sp S0 db.D (parts sp al db tr).D1 (k + 1) (dataIds sp al db tr) (parts sp al db tr).taken
    m3 hdnd (step_taken_nodup sp al db tr hinv) ha.tbl hdisj
  exact ha.final_ok hsp hinv hmk hstep hinv' hev' hfr e4

end Trans

end SIS
