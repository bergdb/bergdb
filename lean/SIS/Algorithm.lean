/-
Self-indexed streams in Lean: the algorithm, transaction by transaction.

Section numbers refer to theory/sis-model.md. Trusted part.
-/
import SIS.Stream

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- D: node id and got-dirty index d(x), in the order the nodes got dirty (5.3). -/
abbrev Dirty := List (NodeId × Nat)

/-- The database, DB = <P, D, S> (6). -/
structure DB (V T : Type) where
  P : Struct V
  D : Dirty
  S : Stream V T

/-- The algorithm's free choices (6.1). -/
structure Algo (V T : Type) where
  /-- The startup pos policy, step 4. It may depend on S, D and i. The
  algorithm clamps it so that s(i-1) <= s(i) < i. -/
  policy : Stream V T → Dirty → Time → Nat
  /-- The still-dirty test, step 7. -/
  stillDirty : Stream V T → Struct V → Dirty → Time → NodeId → Bool

/-- The exact still-dirty test: the definition of dirty (5.2). -/
def exactTest (sp : Spec V T) : Stream V T → Struct V → Dirty → Time → NodeId → Bool :=
  fun S P _ i x => dirty sp S P i x

/-- The stream S followed by a record under construction that holds the
versions vs so far. Used to find latest versions while record i is built. -/
def Stream.building (S : Stream V T) (vs : List (Version V)) : Stream V T :=
  S ++ [{ trans := none, sp := 0, vers := vs, gd := [], top := none }]

/-- Write versions of the nodes xs, in that order, into record i, after the
versions vs already in it. -/
def writeAll (sp : Spec V T) (S : Stream V T) (i : Nat) (P : Struct V) (xs : List NodeId)
    (vs : List (Version V)) : List (Version V) :=
  xs.foldl (fun vs x =>
    match P.get? x with
    | some n => vs ++ [mkVersion sp (S.building vs) i x n]
    | none => vs) vs

/-- The nodes xs, lowest level first (6.1, step 6). -/
def byLevel (P : Struct V) (xs : List NodeId) : List NodeId :=
  xs.mergeSort (fun a b =>
    decide (((P.get? a).map (·.level)).getD 0 ≤ ((P.get? b).map (·.level)).getD 0))

/-- The startup pos of the last record. -/
def lastSp (S : Stream V T) : Nat :=
  (S.getLast?.map (·.sp)).getD 0

/-- Is x in D? -/
def inD (D : Dirty) (x : NodeId) : Bool :=
  D.any (fun e => e.1 == x)

/-- The ids of the nodes of P, without repeats. -/
def allIds (P : Struct V) : List NodeId :=
  (P.map (·.1)).eraseDups

/-- x is an index node of P (3.2). -/
def isIndex (P : Struct V) (x : NodeId) : Bool :=
  match P.get? x with
  | some n => !n.isData
  | none => false

/-- Step 3: the index nodes that are not in D and are dirty, sorted by id, so
that a record does not depend on the order of nodes in P. -/
def gotDirtyOf (sp : Spec V T) (S : Stream V T) (P : Struct V) (D : Dirty) (i : Time) :
    List NodeId :=
  ((allIds P).filter (fun x => isIndex P x && !inD D x && dirty sp S P i x)).mergeSort
    (fun a b => decide (a ≤ b))

/-- Step 4: the startup pos s(i), clamped so that s(i-1) <= s(i) < i. -/
def startupPos (al : Algo V T) (S : Stream V T) (D : Dirty) (i : Time) : Nat :=
  min (i - 1) (max (lastSp S) (al.policy S D i))

/-- Step 7, Rule A: test the taken nodes, lowest level first; each one that is
still dirty goes back into D with d(x) = i, so that a later test may see it.
Returns the new D and the nodes that stayed dirty. -/
def stillDirtyOf (al : Algo V T) (S : Stream V T) (P : Struct V) (D : Dirty) (i : Time)
    (taken : List NodeId) : Dirty × List NodeId :=
  taken.foldl (fun (acc : Dirty × List NodeId) x =>
    if al.stillDirty S P acc.1 i x then (acc.1 ++ [(x, i)], acc.2 ++ [x]) else acc) (D, [])

/-- Transaction i = S.length (6.1). -/
def step (sp : Spec V T) (al : Algo V T) (db : DB V T) (tr : T) : DB V T :=
  let i := db.S.length
  -- 1. Change.
  let c := sp.exec tr i (view sp db.P (i - 1))
  let P := db.P.apply i c
  -- 2. Write data: a version of each data node created by T(i).
  let vs0 := writeAll sp db.S i P ((c.new.filter (·.isData)).map (·.id)) []
  -- 3. Got dirty: index nodes not in D that are dirty now.
  let gd3 := gotDirtyOf sp (db.S.building vs0) P db.D i
  let D1 : Dirty := db.D ++ gd3.map (fun x => (x, i))
  -- 4. Startup pos.
  let s : Nat := startupPos al db.S D1 i
  -- 5. Take every node with d(x) <= s(i).
  let taken := byLevel P ((D1.filter (fun e : NodeId × Nat => decide (e.2 ≤ s))).map (·.1))
  let D2 : Dirty := D1.filter (fun e : NodeId × Nat => decide (s < e.2))
  -- 6. Write index: a version of each taken node, lowest level first.
  let vs := writeAll sp db.S i P taken vs0
  let S' : Stream V T := db.S.building vs
  -- 7. Still dirty (Rule A).
  let r7 := stillDirtyOf al S' P D2 i taken
  -- 8. Append R(i).
  let R : Record V T :=
    { trans := some tr, sp := s, vers := vs, gd := gd3 ++ r7.2,
      top := (S'.lv root).map (·.recNo) }
  { P := P, D := r7.1, S := db.S ++ [R] }

/-- T(0): the initial structure, all of it written to R(0) (4). -/
def init (sp : Spec V T) : DB V T :=
  let P := sp.init
  let vs := writeAll sp [] 0 P (byLevel P (P.map (·.1))) []
  let S' : Stream V T := Stream.building [] vs
  { P := P, D := [],
    S := [{ trans := none, sp := 0, vers := vs, gd := [], top := (S'.lv root).map (·.recNo) }] }

/-- A run without crashes: T(0), then the transactions ts. -/
def run (sp : Spec V T) (al : Algo V T) (ts : List T) : DB V T :=
  ts.foldl (step sp al) (init sp)

end SIS
