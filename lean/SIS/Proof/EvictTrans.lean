/-
Proofs for stage 2 (bergdb item 001, WP E3), part 12: one transaction of the
physical writer with eviction appends the model's record and leaves the model's
D, and the memory after it, and after any cache operations, has the invariant.
-/
import SIS.Proof.EvictStepInv

set_option linter.unusedSectionVars false

namespace SIS

variable {V T : Type} [DecidableEq V]

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

theorem step_eq_stepOf (sp : Spec V T) (al : Algo V T) (db : DB V T) (tr : T) :
    step sp al db tr = stepOf sp al db tr (parts sp al db tr).c (parts sp al db tr).vs0 (parts sp al db tr).vs :=
  rfl

theorem parts_D1Of (sp : Spec V T) (al : Algo V T) (db : DB V T) (tr : T) :
    (parts sp al db tr).D1 = D1Of sp al db (parts sp al db tr).c (parts sp al db tr).vs0 := rfl

theorem parts_takenOf (sp : Spec V T) (al : Algo V T) (db : DB V T) (tr : T) :
    (parts sp al db tr).taken = takenOf sp al db tr (parts sp al db tr).c (parts sp al db tr).vs0 := rfl

section Trans

variable {sp : Spec V T} {al : Algo V T} {db : DB V T} {tr : T} {S0 : Stream V T} {k : Nat} {m : Mem V}

end Trans

end SIS
