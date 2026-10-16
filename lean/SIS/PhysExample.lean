/-
The physical layer by running (bergdb item 001, WP L1): examples with
`#guard` checks. Not part of the trusted part.
-/
import SIS.Phys
import SIS.Example

namespace SIS.PhysExample

open SIS SIS.Example

variable {T : Type}

/-- The physical read at time t gives P@t: each node it reaches has its history
at t in P and is reachable at t, and it reaches every node reachable at t. -/
def readOK (sp : Spec Val T) (db : DB Val T) (l : List (NodeId × History Val)) (t : Time) : Bool :=
  l.all (fun p => ((view sp db.P t p.1).map (·.hist)) == some p.2) &&
    (reachList sp db.P t).all (fun x => l.any (·.1 == x))

/-- Reads at the times ts, one after the other on the same memory; true if each
gives P at its time. -/
def readsOK (sp : Spec Val T) (db : DB Val T) (m : Mem Val) (ts : List Time) : Bool :=
  (ts.foldl (fun (acc : Mem Val × Bool) t =>
    let (m', l) := acc.1.read sp db.S t
    (m', acc.2 && readOK sp db l t)) (m, true)).2

/-- Every canonical object holds its node's whole history. -/
def canonOK (db : DB Val T) (m : Mem Val) : Bool :=
  m.objs.all (fun p => !p.2.canonical || p.2.node == root ||
    ((db.P.get? p.2.node).map (·.hist)) == some p.2.hist)

/-- In every state of a run of example 3: the lazy startup from its stream, then
reads at every time up to the last record, in increasing and in decreasing
order; returns (states, states where all reads give P, states where every
canonical object holds its node's whole history). -/
def checkRun3 (seed n : Nat) : Nat × Nat × Nat :=
  let ts := (randomTs3 seed n).map (·.1)
  let al : Algo Val Tr3 :=
    { policy := fun _ _ i tr => i - 1 - (lcg i / 4096 + tr.n) % 5, stillDirty := javaTest spec3, mark := true }
  (states spec3 al ts).foldl (fun acc db =>
    let m := lazyStartup spec3 db.S
    let k := db.S.length - 1
    let up := List.range (k + 1)
    let ok := readsOK spec3 db m up && readsOK spec3 db m up.reverse
    (acc.1 + 1, acc.2.1 + (if ok then 1 else 0), acc.2.2 + (if canonOK db m then 1 else 0))) (0, 0, 0)

-- Example 3 (a virtual root): in every state of two runs, the lazy startup, then
-- reads at every time in increasing and then in decreasing order give P, and every
-- canonical object holds its node's whole history.
#guard checkRun3 1 16 == (17, 17, 17)
#guard checkRun3 2 16 == (17, 17, 17)

/-- As `checkRun3`, for example 2 (a written root), with one of `algos2`. -/
def checkRun2 (al : Algo Val Tr2) (seed n : Nat) : Nat × Nat × Nat :=
  let ts := (randomTs seed n).map (·.1)
  (states spec2 al ts).foldl (fun acc db =>
    let m := lazyStartup spec2 db.S
    let k := db.S.length - 1
    let up := List.range (k + 1)
    let ok := readsOK spec2 db m up && readsOK spec2 db m up.reverse
    (acc.1 + 1, acc.2.1 + (if ok then 1 else 0), acc.2.2 + (if canonOK db m then 1 else 0))) (0, 0, 0)

-- Example 2 (a written root), with four of its algorithms.
#guard [0, 1, 4, 13].all (fun a => match algos2[a]? with
  | some al => checkRun2 al 1 12 == (13, 13, 13)
  | none => false)

/-- A path from the root to x at time t in P, by DFS over live children on lower levels. -/
def pathTo (sp : Spec Val T) (P : Struct Val) (t : Time) (x : NodeId) : Nat → NodeId → Option (List NodeId)
  | 0, _ => none
  | fuel + 1, y =>
    if y == x then some [y] else
    match P.get? y with
    | none => none
    | some n => (sp.live (n.hist.upTo t)).findSome? (fun z =>
        match P.get? z with
        | some mz => if mz.level < n.level then (pathTo sp P t x fuel z).map (y :: ·) else none
        | none => none)

/-- The writer follows the path from the root to x at the last time, step by step. -/
def writerWalk (sp : Spec Val T) (S : SIS.Stream Val T) (m : Mem Val) (path : List NodeId) : Mem Val :=
  (path.zip path.tail).foldl (fun m (p, c) =>
    match m.canonicalOf p with
    | some hp => (m.follow sp S hp c true).1
    | none => m) m

/-- In every state of a run of example 3: the lazy startup; then, for every node
reachable at the last time, a read at a time and the writer's walk to the
node, in turn; then reads at every time. All reads must give P, and every
canonical object must hold its node's whole history. -/
def checkWalk3 (seed n : Nat) : Nat × Nat :=
  let ts := (randomTs3 seed n).map (·.1)
  let al : Algo Val Tr3 :=
    { policy := fun _ _ i tr => i - 1 - (lcg i / 4096 + tr.n) % 5, stillDirty := javaTest spec3, mark := true }
  (states spec3 al ts).foldl (fun acc db =>
    let k := db.S.length - 1
    let xs := (reachList spec3 db.P k).eraseDups
    let r := xs.zipIdx.foldl (fun (acc : Mem Val × Bool) (x, idx) =>
      let (m1, l) := acc.1.read spec3 db.S (idx % (k + 1))
      let m2 := match pathTo spec3 db.P k x 2000 root with
        | some p => writerWalk spec3 db.S m1 p
        | none => m1
      (m2, acc.2 && readOK spec3 db l (idx % (k + 1)) && canonOK db m2)) (lazyStartup spec3 db.S, true)
    let ok := r.2 && readsOK spec3 db r.1 (List.range (k + 1))
    (acc.1 + 1, acc.2 + (if ok then 1 else 0))) (0, 0)

-- Reads at various times and the writer's walks to every reachable node, in turn.
#guard checkWalk3 1 14 == (15, 15)

/-! ## The assumptions of the physical layer, by running -/

/-- `PhysStep` by running: for the changes c made at time i to P, both
assumptions, for every node of P after the change. -/
def physStepB (sp : Spec Val T) (P : Struct Val) (i : Time) (c : Changes Val) : Bool :=
  let P' := P.apply i c
  let liveOld := fun x => match P.get? x with
    | some n0 => sp.live (n0.hist.upTo (i - 1))
    | none => []
  (allIds P').all (fun x => match P'.get? x with
    | some n =>
      (sp.live (n.hist.upTo i)).all (fun y => (liveOld x).contains y ||
        c.adds.any (fun a => a.1 == x && (sp.ptrs a.2).contains y)) &&
      (!reachable sp P' i x || (sp.live (n.hist.upTo i)).all (fun y =>
        (liveOld x).contains y || (c.new.map (·.id)).contains y ||
        (allIds P).any (fun z => match P.get? z with
          | some nz => reachable sp P (i - 1) z && (changed c z || !reachable sp P' i z) &&
              (sp.live (nz.hist.upTo (i - 1))).contains y
          | none => false)))
    | none => true)

/-- `PhysRunOK` by running. -/
def physRunOKB (sp : Spec Val T) (al : Algo Val T) (ts : List T) : Bool :=
  (List.range ts.length).all (fun j =>
    match ts[j]? with
    | some tr =>
      let db := run sp al (ts.take j)
      physStepB sp db.P (j + 1) (sp.exec tr (j + 1) (view sp db.P j))
    | none => false)

-- Examples 2 and 3 meet the assumptions of the physical layer.
#guard physRunOKB spec3
  { policy := fun _ _ i tr => i - 1 - (lcg i / 4096 + tr.n) % 5, stillDirty := javaTest spec3, mark := true }
  ((randomTs3 1 16).map (·.1))
#guard [0, 1, 4, 13].all (fun a => match algos2[a]? with
  | some al => physRunOKB spec2 al ((randomTs 1 12).map (·.1))
  | none => false)

/-! ## The invariant of the proof of T1-L, by running (WP L3) -/

/-- The proof's invariant of memory m after a startup from the stream of db, at
time k, the last record (`SIS.MemInv` in `Proof/PhysInv.lean`), by running:
canonical objects (in the node table, with the whole history, their slots
good at every time their node is reachable, and fresh at k); other objects
(versions, cut back only if empty and the table's, slots at least as new as
the version's references); memory slots (the table's object, or an older
version); coverage (D, the section, the entries after s). -/
def memInvB (sp : Spec Val T) (db : DB Val T) (m : Mem Val) : Bool :=
  let S := db.S
  let P := db.P
  let k := S.length - 1
  let s := lastSp S
  let lvRec := fun y => (S.lv y).map (·.recNo)
  let histAt := fun (y : NodeId) (t : Nat) => ((P.get? y).map (·.hist.upTo t)).getD []
  let verOf := fun (o : Obj Val) => o.pos.bind (fun r => S.versionAt r o.node)
  let snapGood := fun (o : Obj Val) (t : Nat) => match verOf o with
    | some w => good sp S P t w && o.hist.upTo t == w.hist.upTo t
    | none => false
  let targetGood := fun (y : NodeId) (sl : Slot) (t : Nat) => match sl with
    | .mem h' => match m.obj? h' with
      | some o' => o'.node == y && (o'.canonical || snapGood o' t)
      | none => false
    | .stream r => (m.canonicalOf y).isSome || match ruleRRef S s y r with
      | some r' => match S.versionAt r' y with
        | some u => good sp S P t u
        | none => false
      | none => false
  let fresh := fun (y : NodeId) (sl : Slot) => match sl with
    | .mem h' => m.tableOf y == some h' && match m.obj? h' with
      | some o' => o'.canonical || o'.pos == lvRec y
      | none => false
    | .stream r => (m.canonicalOf y).isSome || ruleRRef S s y r == lvRec y
  m.objs.all (fun p =>
    let h := p.1
    let o := p.2
    (!o.canonical || (m.tableOf o.node == some h &&
      ((P.get? o.node).map (·.hist)) == some o.hist &&
      (List.range (k + 1)).all (fun t => !reachable sp P t o.node ||
        (sp.live (o.hist.upTo t)).all (fun y => match o.slot? y with
          | some sl => targetGood y sl t
          | none => false)) &&
      (!reachable sp P k o.node || (sp.live o.hist).all (fun y => match o.slot? y with
          | some sl => fresh y sl
          | none => false)))) &&
    (o.canonical || match verOf o with
      | some w => (o.hist == w.hist ||
          (o.hist == w.hist.upTo s && m.tableOf o.node == some h && histAt o.node k == [])) &&
        o.slots.all (fun q => match q.2 with
          | .stream r => r == w.ref? q.1
          | .mem h' => match m.obj? h' with
            | some o' => o'.node == q.1 && (o'.canonical ||
                match o'.pos, ruleRRef S s q.1 (w.ref? q.1) with
                | some p', some r' => decide (r' ≤ p')
                | _, _ => false)
            | none => false)
      | none => false) &&
    o.slots.all (fun q => match q.2 with
      | .mem h' => m.tableOf q.1 == some h' || match m.obj? h', m.tableOf q.1 with
        | some o', some h0 => match m.obj? h0 with
          | some o0 => !o'.canonical && (match o'.pos, o0.pos with
              | some p', some p0 => decide (p' < p0)
              | _, _ => false) && (match verOf o' with
              | some w' => o'.hist == w'.hist
              | none => false)
          | none => false
        | _, _ => false
      | .stream _ => true)) &&
  db.D.all (fun e => (m.canonicalOf e.1).isSome || histAt e.1 k == []) &&
  (allIds P).all (fun x => (m.canonicalOf x).isSome ||
    (!((P.get? x).map (fun n => n.hist.any (fun e => decide (s < e.time)))).getD false &&
     !((newest S s x).map (fun w => !w.isData && !(w.hist.upTo s).isEmpty)).getD false))


/-! ## Unit examples of the first touch -/

/-- Node 5 has a version in R(0) and a newer one in R(2); the startup pos is 1. -/
def vY0 : Version Val :=
  { node := 5, recNo := 0, level := 1, isData := false, hist := [⟨0, .ref 7⟩], refs := [(7, 0)] }
def vY2 : Version Val :=
  { node := 5, recNo := 2, level := 1, isData := false, hist := [⟨0, .ref 7⟩, ⟨2, .ref 8⟩],
    refs := [(7, 0), (8, 2)] }
def S1 : SIS.Stream Val Tr3 :=
  [{ trans := none, sp := 0, vers := [vY0], gd := [], top := none },
   { trans := none, sp := 0, vers := [], gd := [], top := none },
   { trans := none, sp := 1, vers := [vY2], gd := [], top := none }]

/-- An object of node 3 whose slot for node 5 is a stream slot naming R(0). -/
def parent3 : Obj Val :=
  { node := 3, level := 2, isData := false, hist := [⟨0, .ref 5⟩], canonical := true,
    pos := some 0, slots := [(5, .stream (some 0))] }

/- Rule R: the slot names R(0), but node 5 has a newer version in R(1), ..., R(2):
the first touch reads that one, cut back to the startup time 1 (Java's runtime
cut back, M22). The slot then names the new object. -/
def mR : Mem Val := { objs := [(1, parent3)], table := [(3, 1)], s := 1, root := 1, next := 2 }
#guard (let (m', h) := mR.follow spec3 S1 1 5 false
        match h.bind m'.obj? with
        | some o => o.pos == some 2 && o.hist == [⟨0, .ref 7⟩] && !o.canonical &&
            ((m'.obj? 1).bind (·.slot? 5)) == some (.mem 2)
        | none => false)

/- A newer snapshot in the table: no section (s = 3), the table holds a snapshot
of node 5's version in R(2), read earlier by another pointer; the slot names R(0),
so the table's snapshot, at least as new, serves. -/
def mT : Mem Val :=
  { objs := [(1, parent3), (2, Obj.ofVersion spec3 vY2 none)], table := [(3, 1), (5, 2)],
    s := 3, root := 1, next := 3 }
#guard (let (m', h) := mT.follow spec3 S1 1 5 false
        h == some 2 && ((m'.obj? 1).bind (·.slot? 5)) == some (.mem 2))

-- The writer makes the object it reaches canonical: here the table's snapshot,
-- which is the newest version of node 5.
#guard (let (m', h) := mT.follow spec3 S1 1 5 true
        h == some 2 && ((h.bind m'.obj?).map (·.canonical)) == some true &&
          m'.tableOf 5 == some 2)

/- Without the table's snapshot, the version that the slot names is read. -/
def mV : Mem Val := { objs := [(1, parent3)], table := [(3, 1)], s := 3, root := 1, next := 2 }
#guard (let (m', h) := mV.follow spec3 S1 1 5 false
        ((h.bind m'.obj?).map (·.pos)) == some (some 0) && m'.tableOf 5 == h)

/-! ## A node of D that the rerun does not reach

In the model every node of D is on a path of the rerun or has a version in the
section: a node gets into D marked on the path of a change, or put back by step 7
after a write in the section. In Java such a node came from a delete of a key that
did not exist, which marked its path without storing anything to rerun, until F1-008-11's
D1 (2026-10-16). `canonicalNode` still covers it: the node's latest version, cut
back to the startup time. -/

/- Node 5 has versions in R(0) only; the startup pos is 1: its object is made
from its latest version, canonical. -/
def S5 : SIS.Stream Val Tr3 :=
  [{ trans := none, sp := 0, vers := [vY0], gd := [], top := none },
   { trans := none, sp := 0, vers := [], gd := [5], top := none }]
def mD : Mem Val := { objs := [], table := [], s := 1, root := 0, next := 1 }
#guard (let m' := mD.canonicalNode spec3 S5 5
        match m'.canonicalOf 5 with
        | some h => ((m'.obj? h).map (fun o => o.pos == some 0 && o.hist == vY0.hist)) == some true
        | none => false)
