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
  /-- The startup pos policy, step 4. It may depend on S, D, i and the
  transaction T(i) (BergDB's limit on the nodes taken depends on T(i): M10,
  added 2026-10-16). The algorithm clamps it so that s(i-1) <= s(i) < i. -/
  policy : Stream V T → Dirty → Time → T → Nat
  /-- The still-dirty test, step 7. -/
  stillDirty : Stream V T → Struct V → Dirty → Time → NodeId → Bool
  /-- Step 3: mark the access path of the change (`markOf`, BergDB's way),
  instead of testing every index node for dirtiness (`gotDirtyOf`). T13 says
  the two give the same nodes. Added 2026-10-15 (bergdb 011-11,
  M2). -/
  mark : Bool := false
  /-- The first available time policy, fa(i) (bergdb item 001, WP R3;
  bergdb 001-07, 2.4): the earliest time that lookups must still
  answer. It may depend on S, D, i and T(i), as the startup pos policy; the
  algorithm clamps it so that it never decreases and stays at most the
  startup pos (`firstAvail`). Java's: the end of the newest iteration of
  reclaim marked cut in its table. 0 by default: no reclaim. Added
  2026-10-17. -/
  faPolicy : Stream V T → Dirty → Time → T → Nat := fun _ _ _ _ => 0

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

/-- BergDB's still-dirty test (Rule A, conservative; `DbHelper.hasDirtyChild`
in bergdb's Java code): a written node goes back into D if one of its
pointees, live or dead, is in D. Step 7 (`stillDirtyOf`) tests the written
nodes lowest level first, with D holding the nodes put back so far, which gives
the least fixpoint of BergDB's loop. Added 2026-10-15
(bergdb 011-11, M3). -/
def javaTest (sp : Spec V T) : Stream V T → Struct V → Dirty → Time → NodeId → Bool :=
  fun _ P D _ x => match P.get? x with
    | some n => (pointees sp n.hist).any (inD D)
    | none => true

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

/-- The changes c create node z, or give it an entry. -/
def changed (c : Changes V) (z : NodeId) : Bool :=
  c.new.any (fun n => n.id == z) || c.adds.any (fun a => a.1 == z)

/-- Node x is on the access path of the change at time i: it is reachable at
i, and some node reachable from it at i (itself included) is changed. In a
tree these are the changed nodes and their current ancestors. -/
def marked (sp : Spec V T) (P : Struct V) (c : Changes V) (i : Time) (x : NodeId) : Bool :=
  reachable sp P i x &&
    match P.get? x with
    | some n => (reachFrom sp P i x n).any (changed c)
    | none => false

/-- Step 3 by marking: the index nodes that are not in D and are on the access
path of the change, sorted by id. No dirty test. -/
def markOf (sp : Spec V T) (P : Struct V) (c : Changes V) (D : Dirty) (i : Time) :
    List NodeId :=
  ((allIds P).filter (fun x => isIndex P x && !inD D x && marked sp P c i x)).mergeSort
    (fun a b => decide (a ≤ b))

/-- The nodes that can be in D and be written: all but a virtual root
(`Spec.virt`). -/
def written (sp : Spec V T) (x : NodeId) : Bool := !(sp.virt && x == root)

/-- top(i) with a virtual root: the root's child named by its last entry up to
time s (the root's live child at s; BergDB's super root at the startup time),
and the record of that child's latest version. -/
def topV (sp : Spec V T) (P : Struct V) (S : Stream V T) (s : Nat) : Option (NodeId × Nat) :=
  match (P.get? root).bind (fun n => (n.hist.upTo s).getLast?) with
  | some e =>
    match (sp.ptrs e.val).head? with
    | some z => (S.lv z).map (fun v => (z, v.recNo))
    | none => none
  | none => none

/-- top(i): the version that startup reads first, as its node and record. The
latest version of root, or, with a virtual root, `topV` (BergDB's topPos,
bergdb 011-11, 8.2 and 8.3). -/
def topOf (sp : Spec V T) (P : Struct V) (S : Stream V T) (s : Nat) : Option (NodeId × Nat) :=
  if sp.virt then topV sp P S s else (S.lv root).map (fun v => (root, v.recNo))

/-- Step 4: the startup pos s(i), clamped so that s(i-1) <= s(i) < i. -/
def startupPos (al : Algo V T) (S : Stream V T) (D : Dirty) (i : Time) (tr : T) : Nat :=
  min (i - 1) (max (lastSp S) (al.policy S D i tr))

/-- The first available time of the last record (bergdb item 001, WP R3). -/
def lastFa (S : Stream V T) : Nat :=
  (S.getLast?.map (·.fa)).getD 0

/-- fa(i), with s = s(i): the policy, clamped so that fa(i-1) <= fa(i) <= s(i)
(bergdb item 001, WP R3). -/
def firstAvail (al : Algo V T) (S : Stream V T) (D : Dirty) (i : Time) (tr : T) (s : Nat) : Nat :=
  min s (max (lastFa S) (al.faPolicy S D i tr))

/-- The nodes that the touch of change c marks, besides the nodes `base` that
step 3 found otherwise: the touched index nodes not in D and not in `base`,
sorted by id (bergdb item 001, WP R3; Java's `Db.touchRange`, M17). -/
def touchOf (P : Struct V) (c : Changes V) (D : Dirty) (base : List NodeId) : List NodeId :=
  (c.touch.eraseDups.filter (fun x => isIndex P x && !inD D x && !base.contains x)).mergeSort
    (fun a b => decide (a ≤ b))

/-- Step 3: the index nodes that got dirty in T(i), found by testing every index
node not in D (`gotDirtyOf`) or by marking the access path of the change
(`markOf`, `Algo.mark`), and the nodes the change's touch marks (`touchOf`);
never a virtual root. vs0 are the versions of step 2. (A function since
2026-10-17, bergdb item 001, WP R3, with the touch; before, the same
expression stood in `step`.) -/
def gotDirty3 (sp : Spec V T) (al : Algo V T) (S : Stream V T) (vs0 : List (Version V))
    (P : Struct V) (c : Changes V) (D : Dirty) (i : Time) : List NodeId :=
  let base := if al.mark then markOf sp P c D i else gotDirtyOf sp (S.building vs0) P D i
  (base ++ touchOf P c D base).filter (written sp)

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
  -- 3. Got dirty: index nodes not in D that are dirty now, found by testing
  -- them, or by marking the access path of the change, and the nodes the
  -- touch marks; never a virtual root.
  let gd3 := gotDirty3 sp al db.S vs0 P c db.D i
  let D1 : Dirty := db.D ++ gd3.map (fun x => (x, i))
  -- 4. Startup pos, and the first available time.
  let s : Nat := startupPos al db.S D1 i tr
  let fa : Nat := firstAvail al db.S D1 i tr s
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
    { trans := some tr, sp := s, vers := vs, gd := gd3 ++ r7.2, top := topOf sp P S' s, fa := fa }
  { P := P, D := r7.1, S := db.S ++ [R] }

/-- T(0): the initial structure, all of it written to R(0) (4), but a
virtual root. -/
def init (sp : Spec V T) : DB V T :=
  let P := sp.init
  let vs := writeAll sp [] 0 P (byLevel P ((P.map (·.1)).filter (written sp))) []
  let S' : Stream V T := Stream.building [] vs
  { P := P, D := [],
    S := [{ trans := none, sp := 0, vers := vs, gd := [], top := topOf sp P S' 0 }] }

/-- A run without crashes: T(0), then the transactions ts. -/
def run (sp : Spec V T) (al : Algo V T) (ts : List T) : DB V T :=
  ts.foldl (step sp al) (init sp)

end SIS
