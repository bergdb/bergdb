/-
The physical layer with handles by running (bergdb item 009, phase 2, step 2b):
EvictExample.lean's runs, with handles (SIS/Handle.lean). After every
transaction, the records and D must be the model's, reads must give P, and the
invariants that HandleTheorems.lean states must hold, under schedules that
evict nothing, everything that may be evicted, and a mix. `#guard` checks. Not
part of the trusted part.
-/
import SIS.Handle
import SIS.EvictExample

namespace SIS.HandleExample

open SIS SIS.Example SIS.PhysExample SIS.EvictExample

variable {T : Type}

/-! ## The invariants by running

Each is the `Bool` twin of a `Prop` of HandleTheorems.lean, with the same
name but for the `B` at the end and a lower case first letter. -/

/-- The table and the handles (`HTableOK`): every entry of the table names a
live handle of its node that holds an object in memory of that node; one entry
per node; every live handle is its node's entry, and a dead one holds no object
and is not in the table; every object in memory is held by its node's live
handle; addresses and handle numbers do not repeat; every pointer's handle
exists and is of the pointer's pointee. -/
def hTableOKB (m : HMem Val) : Bool :=
  m.table.all (fun e => match m.handle? e.2 with
    | some hd => !hd.dead && hd.node == e.1 && match hd.obj with
      | some a => match m.obj? a with
        | some o => o.node == e.1
        | none => false
      | none => false
    | none => false) &&
  (m.table.map (·.1)).eraseDups.length == m.table.length &&
  m.handles.all (fun p =>
    if p.2.dead then p.2.obj.isNone && !(m.table.any (·.2 == p.1))
    else m.tableOf p.2.node == some p.1) &&
  m.objs.all (fun p => match m.tableOf p.2.node with
    | some n => m.objOf n == some p.1
    | none => false) &&
  (m.objs.map (·.1)).eraseDups.length == m.objs.length &&
  (m.handles.map (·.1)).eraseDups.length == m.handles.length &&
  m.objs.all (fun p => p.2.ptrs.all (fun q => match q.2.handle with
    | some n => match m.handle? n with
      | some hd => hd.node == q.1
      | none => false
    | none => true))

/-- INV-CAN with handles (`HCanOK`): a canonical object is its node's canonical
object (the object of its live handle), holds its node's whole history, level
and kind, and is at its node's latest record; every node of D has a canonical
object; a written canonical object of a node not in D holds its node's latest
version. -/
def hCanOKB (db : DB Val T) (m : HMem Val) : Bool :=
  let canon := m.objs.filter (·.2.canonical)
  canon.all (fun p => m.canonicalOf p.2.node == some p.1) &&
  canon.all (fun p => match db.P.get? p.2.node with
    | some n => n.hist == p.2.hist && n.level == p.2.level && n.isData == p.2.isData
    | none => false) &&
  canon.all (fun p => p.2.pos == lvRec db.S p.2.node) &&
  db.D.all (fun e => (m.canonicalOf e.1).isSome) &&
  canon.all (fun p => inD db.D p.2.node || p.2.pos.isNone ||
    ((db.S.lv p.2.node).map (·.hist)) == some p.2.hist)

/-- INV-SNAP with handles (`HSnapOK`): every other object is the version of S at
its position, exactly. -/
def hSnapOKB (db : DB Val T) (m : HMem Val) : Bool :=
  m.objs.all (fun p => p.2.canonical || match p.2.pos with
    | some r => match db.S.versionAt r p.2.node with
      | some w => w.hist == p.2.hist && w.level == p.2.level && w.isData == p.2.isData
      | none => false
    | none => false)

/-- INV-SLOT with handles, the record rule of 02, 4.6 (`HSlotOK`): for every
canonical object of a node that is current at the last time or in D (a virtual
root aside, which is never written), and every pointee y: the object has a
pointer for y; writing it now would give y its latest version (`HMem.refOf`,
which finds a pointee of D by node id); and if y is in D and the pointer does
not hold y's live handle with its canonical object, the object's node is in D
with an index at most y's (it is written no later than y). -/
def hSlotOKB (sp : Spec Val T) (S0 : SIS.Stream Val T) (db : DB Val T) (m : HMem Val) : Bool :=
  let k := db.S.length - 1
  let dOf := fun x => (db.D.find? (·.1 == x)).map (·.2)
  m.objs.all (fun p =>
    let o := p.2
    !o.canonical || (sp.virt && o.node == root) ||
    !(reachable sp db.P k o.node || inD db.D o.node) ||
    (pointees sp o.hist).all (fun y =>
      let liveCanon := match o.ptr? y with
        | some q => q.handle.isSome && q.handle == m.tableOf y && (m.canonicalOf y).isSome
        | none => false
      (o.ptr? y).isSome &&
      m.refOf S0 db.D o y == lvRec db.S y &&
      (!inD db.D y || liveCanon ||
        (inD db.D o.node && match dOf o.node, dOf y with
          | some a, some b => decide (a ≤ b)
          | _, _ => false))))

/-- Rule R and the snapshots (`HRuleROK`, open points 1 and 2 of 02): every
snapshot in a handle is at least as new as its node's newest version in the
startup section of the last startup (stream S0, startup pos `m.s`). -/
def hRuleROKB (S0 : SIS.Stream Val T) (m : HMem Val) : Bool :=
  m.handles.all (fun p => match p.2.obj.bind m.obj? with
    | some o => o.canonical || match newest S0 m.s p.2.node with
      | some w => match o.pos with
        | some q => decide (w.recNo ≤ q)
        | none => false
      | none => true
    | none => true)

/-- The snapshots and the written positions (`HSnapWrittenOK`): every snapshot
that a handle holds is at least as new as the handle's written position. -/
def hSnapWrittenOKB (m : HMem Val) : Bool :=
  m.handles.all (fun p => match p.2.obj.bind m.obj?, p.2.written with
    | some o, some w => o.canonical || match o.pos with
      | some q => decide (w ≤ q)
      | none => false
    | _, _ => true)

/-- References and written positions name versions (`HWrittenOK`): a handle's
written position, and a pointer's reference, is a record that holds a version of
its node. -/
def hWrittenOKB (db : DB Val T) (m : HMem Val) : Bool :=
  m.handles.all (fun p => match p.2.written with
    | some w => (db.S.versionAt w p.2.node).isSome
    | none => true) &&
  m.objs.all (fun p => p.2.ptrs.all (fun q => match q.2.ref with
    | some r => (db.S.versionAt r q.1).isSome
    | none => true))

/-- T-PIN with handles by running (`TP_handles`): every live handle whose object
is not pinned may be evicted, and one eviction removes the object and kills the
handle. -/
def hPinOKB (D : Dirty) (m : HMem Val) : Bool :=
  m.handles.all (fun p => p.2.dead || match p.2.obj with
    | some a => m.pinned D a ||
        (m.evictable D p.1 && ((m.evict D p.1).obj? a).isNone &&
          ((m.evict D p.1).handle? p.1).map (·.dead) == some true)
    | none => false)

/-- All the invariants. -/
def hInvB (sp : Spec Val T) (S0 : SIS.Stream Val T) (db : DB Val T) (m : HMem Val) : Bool :=
  hTableOKB m && hCanOKB db m && hSnapOKB db m && hSlotOKB sp S0 db m && hRuleROKB S0 m &&
    hSnapWrittenOKB m && hWrittenOKB db m && hPinOKB db.D m

/-- Reads at the times ts through the handles, one after the other on the same
memory; the memory after, and whether each read gave P at its time. -/
def readsH (sp : Spec Val T) (S0 : SIS.Stream Val T) (db : DB Val T) (m : HMem Val)
    (ts : List Time) : HMem Val × Bool :=
  ts.foldl (fun (acc : HMem Val × Bool) t =>
    let (m', l) := acc.1.read sp S0 db.S t
    (m', acc.2 && readOK sp db l t)) (m, true)

/-! ## Schedules -/

/-- Whether handle n holds a canonical object. -/
def holdsCanon (m : HMem Val) (n : Nat) : Bool :=
  match (m.objOf n).bind m.obj? with
  | some o => o.canonical
  | none => false

/-- A schedule of evictions after transaction j, over the live handles: 0, none;
1, every handle that may be evicted; 2, each with probability 0.3; 3, those that
hold canonical objects only; 4, those that hold snapshots only. (`HMem.evict`
evicts only what may be evicted.) -/
def hschedule (policy seed j : Nat) (D : Dirty) (m : HMem Val) : HMem Val :=
  let live := m.table.map (·.2)
  match policy with
  | 0 => m
  | 1 => live.foldl (fun mm n => mm.evict D n) m
  | 2 => live.foldl (fun mm n =>
      if (lcg (seed * 1000003 + j * 97 + n)) / 65536 % 10 < 3 then mm.evict D n else mm) m
  | 3 => live.foldl (fun mm n => if holdsCanon mm n then mm.evict D n else mm) m
  | _ => live.foldl (fun mm n => if holdsCanon mm n then mm else mm.evict D n) m

/-! ## Runs with handles, checked after every transaction -/

/-- The reads after transaction j, at the last time k and two earlier times:
the last time first after an even transaction, last after an odd one. A read
at an earlier time right after evictions may load an older version of a node
than a read at k would; the order matters (choice 7 of Handle.lean). -/
def readTimes (seed j k : Nat) : List Time :=
  let r := lcg (seed + j) % (k + 1)
  if j % 2 == 0 then [k, k / 2, r] else [r, k / 2, k]

/-- The operations of a run after transaction j, as `checkHandles` does them:
the schedule, reads (`readTimes`), the schedule again, and reads at time 1 and
k / 2, before the next transaction's view at k. The memory after, and whether
the reads gave P. -/
def afterTrans (sp : Spec Val T) (S0 : SIS.Stream Val T) (db : DB Val T) (m : HMem Val)
    (policy seed j : Nat) : HMem Val × Bool :=
  let k := db.S.length - 1
  let m1 := hschedule policy seed j db.D m
  let (m2, ok1) := readsH sp S0 db m1 (readTimes seed j k)
  let m3 := hschedule policy (seed + 7) j db.D m2
  let (m4, ok2) := readsH sp S0 db m3 [1, k / 2]
  (m4, ok1 && ok2)

/-- A run with restarts and the schedule `policy`, as EvictExample's
`checkEvict`: after every transaction, the records and D are those of the run
without restarts or eviction; then the operations of `afterTrans` (evictions and
reads); then the invariants and the reads (they give P), and after a restart
the invariants of the new memory. Returns (transactions, failures). -/
def checkHandles [DecidableEq T] (sp : Spec Val T) (al : Algo Val T) (ts : List (T × Bool))
    (policy seed : Nat) : Nat × Nat :=
  let ts1 := ts.map (·.1)
  let r := ts.zipIdx.foldl
    (fun (acc : (DB Val T × HMem Val × SIS.Stream Val T) × Nat × Nat) (p, j) =>
      let ((db, m, S0), n, bad) := acc
      let (db', m') := handleTrans sp al S0 db m p.1
      let after := run sp al (ts1.take (j + 1))
      let (m3, readsOK) := afterTrans sp S0 db' m' policy seed j
      let ok := db'.S == after.S && db'.D == after.D && readsOK && hInvB sp S0 db' m3
      let st' := if p.2 then (startup sp db'.S, handleStartup sp db'.S, db'.S) else (db', m3, S0)
      let ok' := ok && (!p.2 || hInvB sp st'.2.2 st'.1 st'.2.1)
      (st', n + 1, bad + (if ok' then 0 else 1)))
    ((init sp, handleStartup sp (init sp).S, (init sp).S), 0, 0)
  (r.2.1, r.2.2)

-- Example 3 (a virtual root), the five schedules.
#guard [0, 1, 2, 3, 4].all (fun pol => checkHandles spec3 al3 (randomTs3 1 12) pol 1 == (12, 0))

-- Example 2 (a written root), BergDB's still-dirty test (algos2's odd entries).
#guard [1, 3].all (fun a => match algos2[a]? with
  | some al => [0, 1, 2, 3, 4].all (fun pol => checkHandles spec2 al (randomTs 1 10) pol 1 == (10, 0))
  | none => false)

-- Example 5 (example 3 with drops), the five schedules, two seeds.
#guard [0, 1, 2, 3, 4].all (fun pol => checkHandles spec5 al5 (randomTs5 1 16) pol 1 == (16, 0))
#guard [0, 1, 2, 3, 4].all (fun pol => checkHandles spec5 al5 (randomTs5 2 16) pol 2 == (16, 0))

/-! ## The trusted run, `runHandles`

`checkHandles` computes its schedule from the memory. `runHandles` takes the
operations as a list: here, after every transaction, a read at the last time,
the eviction of every handle number up to 400 (each only if it may be evicted),
and a read at time 1. -/

/-- The operations after transaction j: a read at j + 1, evict handles 0 to 399,
a read at time 1. -/
def opsAll (j : Nat) : List HCacheOp :=
  [.read (j + 1)] ++ (List.range 400).map .evict ++ [.read 1]

/-- The run of `ts` with `opsAll` after every transaction; its records and D
must be the run's without restarts or eviction. -/
def checkRunHandles [DecidableEq T] (sp : Spec Val T) (al : Algo Val T) (ts : List (T × Bool)) :
    Bool :=
  let tsH := ts.zipIdx.map (fun (p, j) => (p.1, p.2, opsAll j))
  let r := runHandles sp al tsH
  let lg := run sp al (ts.map (·.1))
  r.1.S == lg.S && r.1.D == lg.D

#guard checkRunHandles spec3 al3 (randomTs3 1 12)
#guard checkRunHandles spec5 al5 (randomTs5 1 16)
#guard match algos2[1]? with
  | some al => checkRunHandles spec2 al (randomTs 1 10)
  | none => false

/-! ## The open points of 02, by running

Counts over the states of a run (after every transaction and its schedule), to
show that the runs above reach the cases of 02's open points 1 and 3 and of
choice 1 of Handle.lean (a re-resolve keeps the written position). -/

/-- Counts in memory m (S0 the stream of the last startup, db the state):
1. the pointers of objects in memory whose reference is older than their
   pointee's newest version in the startup section and whose handle holds a
   snapshot (open point 1: the fast path compares with the reference without
   Rule R);
2. the pointers whose handle holds a snapshot that the fast path's test accepts
   with the pointer's reference and the slow path's test would reject, with the
   larger of the reference after Rule R and the handle's written position (must
   be none: `HFastOK`);
3. the pointers of canonical objects whose records matter (a written node
   current at the last time or in D), to a pointee not in D, whose reference is
   a vpos and whose record is their handle's written position (open point 3);
4. such pointers (any reference) that hold a live handle with a snapshot or no
   object, and whose record is not their reference after Rule R: it is the
   written position that a re-resolve put into the live handle (choice 1);
5. such pointers that hold a dead handle, and whose record is not their
   reference after Rule R: the dead handle's written position. -/
def pointCounts (sp : Spec Val T) (S0 : SIS.Stream Val T) (db : DB Val T) (m : HMem Val) :
    Nat × Nat × Nat × Nat × Nat :=
  let k := db.S.length - 1
  let relevant := fun (o : HObj Val) => o.canonical && written sp o.node &&
    (reachable sp db.P k o.node || inD db.D o.node)
  m.objs.foldl (fun acc p =>
    let o := p.2
    o.ptrs.foldl (fun (acc : Nat × Nat × Nat × Nat × Nat) q =>
      let (c1, c2, c3, c4, c5) := acc
      let y := q.1
      let ptr := q.2
      let rr := ruleRRef S0 m.s y ptr.ref
      let hd := ptr.handle.bind m.handle?
      let snap : Option (HObj Val) := match hd with
        | some h => match h.obj.bind m.obj? with
          | some ob => if ob.canonical then none else some ob
          | none => none
        | none => none
      let older := match ptr.ref, newest S0 m.s y with
        | some r0, some w => decide (r0 < w.recNo)
        | _, _ => false
      let c1 := c1 + (if older && snap.isSome then 1 else 0)
      let c2 := c2 + (match snap, hd with
        | some ob, some h => if ob.usable ptr.ref && !ob.usable (maxRef rr h.written) then 1 else 0
        | _, _ => 0)
      let rel := relevant o && !inD db.D y
      let recRef := m.ptrRef S0 y ptr
      let fromWp := recRef != rr && match hd with
        | some h => (h.obj.bind m.obj?).all (fun ob => !ob.canonical) && recRef == h.written
        | none => false
      let c3 := c3 + (if rel && ptr.ref.isNone && fromWp then 1 else 0)
      let live := match hd with
        | some h => !h.dead
        | none => false
      let c4 := c4 + (if rel && fromWp && live then 1 else 0)
      let c5 := c5 + (if rel && fromWp && !live then 1 else 0)
      (c1, c2, c3, c4, c5)) acc) (0, 0, 0, 0, 0)

/-- `pointCounts` summed over the states of a run as in `checkHandles` (after
every transaction and its schedule, before a restart). -/
def runCounts [DecidableEq T] (sp : Spec Val T) (al : Algo Val T) (ts : List (T × Bool))
    (policy seed : Nat) : Nat × Nat × Nat × Nat × Nat :=
  let r := ts.zipIdx.foldl
    (fun (acc : (DB Val T × HMem Val × SIS.Stream Val T) × (Nat × Nat × Nat × Nat × Nat)) (p, j) =>
      let ((db, m, S0), (a1, a2, a3, a4, a5)) := acc
      let (db', m') := handleTrans sp al S0 db m p.1
      let (m3, _) := afterTrans sp S0 db' m' policy seed j
      let (c1, c2, c3, c4, c5) := pointCounts sp S0 db' m3
      let st' := if p.2 then (startup sp db'.S, handleStartup sp db'.S, db'.S) else (db', m3, S0)
      (st', (a1 + c1, a2 + c2, a3 + c3, a4 + c4, a5 + c5)))
    ((init sp, handleStartup sp (init sp).S, (init sp).S), (0, 0, 0, 0, 0))
  r.2

-- In the runs above: open point 3 (column 3) and choice 1 (column 4) are reached
-- with random evictions; columns 1 and 2 are 0 in these short runs.
#guard runCounts spec3 al3 (randomTs3 1 12) 2 1 == (0, 0, 14, 10, 10)
-- In a longer run of example 5, pointers older than the startup section have
-- snapshots in their handles (column 1), and the fast path's test never accepts
-- what the slow path's test would reject (column 2). The run itself passes.
#guard runCounts spec5 al5 (randomTs5 1 40) 2 1 == (4, 0, 60, 29, 41)
#guard checkHandles spec5 al5 (randomTs5 1 40) 2 1 == (40, 0)

/-! ## Three small examples

Node 5 has a version in R(0) and a newer one in R(2): `vY0`, `vY2` and the
stream `S1` of PhysExample.lean. -/

/-- An object of node 3, canonical, at R(0), whose pointer for node 5 names R(0)
and holds handle h, or none. -/
def parentH (h : Option Nat) : HObj Val :=
  { node := 3, level := 2, isData := false, hist := [⟨0, .ref 5⟩], canonical := true,
    pos := some 0, ptrs := [(5, { ref := some 0, handle := h })] }

/-- A memory with the object `parentH h` at address 1, held by handle 1 of node
3; besides it, the handles hs. The startup pos is s. -/
def memH (h : Option Nat) (hs : List (Nat × Handle)) (s : Nat) : HMem Val :=
  { objs := [(1, parentH h)],
    handles := (1, { node := 3, obj := some 1, written := none, dead := false }) :: hs,
    table := [(3, 1)], s := s, root := 1, nextObj := 2, nextHandle := 8 }

/- Open point 1. The startup pos is 1, so Rule R takes node 5's pointer from
R(0) to R(2). The first follow takes the slow path: a new handle (8), and the
version that Rule R names, R(2), as a snapshot. The second follow takes the
fast path: the pointer's own reference, R(0), is older than the section's R(2),
and the test without Rule R (0 ≤ 2) accepts the snapshot, as the test with Rule
R (2 ≤ 2) would: nothing changes, and the reader gets R(2). -/
#guard (let m0 := memH none [] 1
        let (m1, b1) := m0.follow spec3 S1 S1 1 5 false
        let (m2, b2) := m1.follow spec3 S1 S1 1 5 false
        b1 == some 2 && b2 == b1 && ((b1.bind m1.obj?).map (·.pos)) == some (some 2) &&
          m1.tableOf 5 == some 8 && m2.objs.length == m1.objs.length &&
          m2.handles.length == m1.handles.length && m2.nextObj == m1.nextObj &&
          hRuleROKB S1 m1)

/- Choice 1 of Handle.lean. No startup section (the startup pos is 3), so Rule R
changes nothing. The pointer names R(0) and holds handle 7, dead, whose written
position is R(2): this process wrote node 5 there, and then evicted it. Its
record is R(2) (`HMem.refOf`). A read re-resolves the pointer to a new live
handle (8), which keeps R(2) as its written position; the load reads R(2), and
the record stays R(2). Had the new handle not kept it, as with a dead handle
that has no written position, the read would load R(0), and the record would
be R(0). -/
def dead7 (w : Option Nat) : List (Nat × Handle) :=
  [(7, { node := 5, obj := none, written := w, dead := true })]

#guard (let m0 := memH (some 7) (dead7 (some 2)) 3
        let (m1, b) := m0.follow spec3 S1 S1 1 5 false
        m0.refOf S1 [] (parentH (some 7)) 5 == some 2 &&
          ((b.bind m1.obj?).map (·.pos)) == some (some 2) &&
          ((m1.handle? 8).map (·.written)) == some (some 2) &&
          ((m1.obj? 1).bind (fun o => m1.refOf S1 [] o 5)) == some 2)
#guard (let m0 := memH (some 7) (dead7 none) 3
        let (m1, b) := m0.follow spec3 S1 S1 1 5 false
        ((b.bind m1.obj?).map (·.pos)) == some (some 0) &&
          ((m1.obj? 1).bind (fun o => m1.refOf S1 [] o 5)) == some 0)

/- Choice 7 of Handle.lean. As above, the pointer names R(0) and holds the dead
handle 7, whose written position is R(2); but node 5 has a live handle again
(8), which holds a snapshot of R(0): after the eviction, a reader came to node 5
through an older pointer (of a node that is no longer current, whose version
names R(0)) and loaded that version. A read through the pointer re-resolves it
to handle 8, which takes the written position R(2), and the slow path compares
the snapshot with R(2): it is older, so the reader loads R(2), which the
pointer's record names. With 02's test, the reference after Rule R only (R(0)),
the snapshot would serve, and the reader would get R(0). -/
def live8 : List (Nat × Handle) :=
  (8, { node := 5, obj := some 2, written := none, dead := false }) :: dead7 (some 2)

/-- `memH` with the parent's pointer holding the dead handle 7 and node 5's live
handle 8, which holds a snapshot of R(0) at address 2. -/
def memH8 : HMem Val :=
  let m := memH (some 7) live8 3
  { m with objs := (2, HObj.ofVersion spec3 vY0) :: m.objs, table := (5, 8) :: m.table,
           nextObj := 3, nextHandle := 9 }

#guard (let (m1, b) := memH8.follow spec3 S1 S1 1 5 false
        ((b.bind m1.obj?).map (·.pos)) == some (some 2) &&
          ((m1.handle? 8).map (·.written)) == some (some 2) &&
          ((m1.obj? 1).bind (fun o => m1.refOf S1 [] o 5)) == some 2)
-- 02's test: after the same resolve, a load that compares the snapshot with the
-- reference after Rule R only, R(0), keeps the snapshot of R(0).
#guard (let r := memH8.resolve 1 5
        let (m2, b) := r.1.load spec3 S1 r.2 (ruleRRef S1 memH8.s 5 (some 0))
        ((b.bind m2.obj?).map (·.pos)) == some (some 0))

end SIS.HandleExample
