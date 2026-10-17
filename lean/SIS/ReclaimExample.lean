/-
Level 3, reclaim, by running (bergdb item 001, WP R3): example 4, F1-008-07's
reclaim example adapted to BergDB (a virtual root with top nodes, a touch that
marks without adding entries, rewrites of the values, the first available time
at the end of an iteration), with `#guard` checks; and random runs that restart
from the stream cut at the largest safe position, logical and with eviction,
for `lake exe reclaimtest`. Not part of the trusted part.
-/
import SIS.Reclaim
import SIS.EvictExample

namespace SIS.ReclaimExample

open SIS SIS.Example SIS.PhysExample SIS.EvictExample

/-! ## Example 4: reclaim

As example 3: the virtual root 0 (level 1000), whose live child is the newest
top node; a top node points to a tree root (live) and to the previous top node
(dead, BergDB's skip pointer). The tree root has slots 0 and 1 for the mid
nodes, a mid node slots 0 and 1 for the leaves; key k (0 to 3) is in leaf slot
k % 2 of mid slot k / 2. A leaf holds one value: its slot 0 points to a data
node; key 3 has no value at first, so its leaf has no entries. `put k n` writes
a new data node for key k. `split` makes a new tree root
(a copy of the current one's live slots) and a new top node above it, as BergDB
does when the root key node splits. `step lo hi last b` is a reclaim step for
the keys lo to hi (BergDB's `Reclaim` step): it touches every index node that
its range traversal visits at i - 1 (the top node, the tree root, and the mid
nodes and leaves of those keys), and rewrites each of those keys' values that
was stored before time b, BergDB's pCut (a new data node with the same value);
`last` ends an iteration. Ids of new nodes are made from i: 10000 + 8i (the
data node of a put), 10002 + 8i (a tree root), 10003 + 8i (a top node),
10004 + 8i + k (the rewritten value of key k); so a data node with id below
10000 + 8b was stored before time b. -/

inductive Tr4 where
  | put (k n : Nat)
  | split
  | step (lo hi : Nat) (last : Bool) (b : Nat)
  deriving DecidableEq, Repr

/-- The value of a data node: its last `dat` entry. -/
def valOf (n : Node Val) : Nat :=
  (n.hist.filterMap (fun e => match e.val with | .dat v => some v | _ => none)).getLastD 0

/-- The mid node and the leaf of key k below tree root t, at the view. -/
def pathOf4 (view : View Val) (t : NodeId) (k : Nat) : Option (NodeId × NodeId) :=
  (view t).bind (fun tn => (slotOf tn.hist (k / 2 % 2)).bind (fun m =>
    (view m).bind (fun mn => (slotOf mn.hist (k % 2)).map (fun l => (m, l)))))

def exec4 (tr : Tr4) (i : Time) (view : View Val) : Changes Val :=
  let none' : Changes Val := { new := [], adds := [] }
  match (view 0).bind (fun r => slotOf r.hist 0) with
  | none => none'
  | some z =>
    match (view z).bind (fun zn => (live zn.hist).head?) with
    | none => none'
    | some t =>
      match tr with
      | .split =>
        match view t with
        | none => none'
        | some tn =>
          let t' := 10002 + 8 * i
          let z' := 10003 + 8 * i
          { new := [⟨t', 3, false⟩, ⟨z', 100 + i, false⟩],
            adds := ((slotOf tn.hist 0).toList.map (fun m => (t', Val.slot 0 m))) ++
              ((slotOf tn.hist 1).toList.map (fun m => (t', Val.slot 1 m))) ++
              [(z', .ref t'), (z', .dead z), (0, .slot 0 z')] }
      | .put k n =>
        match pathOf4 view t k with
        | none => none'
        | some (_, l) =>
          let d := 10000 + 8 * i
          { new := [⟨d, 0, true⟩], adds := [(d, .dat n), (l, .slot 0 d)] }
      | .step lo hi _ b =>
        let paths := ((List.range 4).filter (fun k => lo ≤ k && k ≤ hi)).filterMap (fun k =>
          (pathOf4 view t k).map (fun p => (k, p.1, p.2)))
        let vals := paths.filterMap (fun p => (view p.2.2).bind (fun ln =>
          (slotOf ln.hist 0).bind (fun d => if d < 10000 + 8 * b then
            (view d).map (fun dn => (p.1, p.2.2, valOf dn)) else none)))
        { new := vals.map (fun v => ⟨10004 + 8 * i + v.1, 0, true⟩),
          adds := vals.flatMap (fun v =>
            [(10004 + 8 * i + v.1, .dat v.2.2), (v.2.1, .slot 0 (10004 + 8 * i + v.1))]),
          touch := ([z, t] ++ paths.map (·.2.1) ++ paths.map (·.2.2)).eraseDups }

def spec4 : Spec Val Tr4 where
  ptrs := ptrs
  live := live
  exec := exec4
  virt := true
  topLevel := 100
  rootVal := fun z => .slot 0 z
  init := [(0, { level := 1000, isData := false, hist := [⟨0, .slot 0 30⟩] }),
           (30, { level := 100, isData := false, hist := [⟨0, .ref 20⟩] }),
           (20, mk 3 [.slot 0 1, .slot 1 2]),
           (1, mk 2 [.slot 0 3, .slot 1 4]), (2, mk 2 [.slot 0 5, .slot 1 6]),
           (3, mk 1 [.slot 0 7]), (4, mk 1 [.slot 0 8]), (5, mk 1 [.slot 0 9]), (6, mk 1 []),
           (7, { level := 0, isData := true, hist := [⟨0, .dat 1⟩] }),
           (8, { level := 0, isData := true, hist := [⟨0, .dat 2⟩] }),
           (9, { level := 0, isData := true, hist := [⟨0, .dat 3⟩] })]

/-- The time of the newest record whose transaction ends an iteration, 0 if
there is none. A cut removes the transactions of the records before it, but
the first available time policy below gives the same then (`PolicyCutOK`): an
iteration end that a safe cut removed is at most the first available time. -/
def lastIterEnd (S : SIS.Stream Val Tr4) : Nat :=
  ((List.range S.length).filter (fun j => match S[j]?.bind (·.trans) with
    | some (.step _ _ true _) => true
    | _ => false)).getLastD 0

/-- BergDB's bookkeeping (marking, its still-dirty test), the startup pos
policy pol, and the first available time at the end of the newest iteration
once the startup pos has passed it (BergDB waits for pEnd), in the next
transaction. -/
def algo4 (pol : SIS.Stream Val Tr4 → Dirty → Time → Tr4 → Nat) : Algo Val Tr4 :=
  { policy := pol, stillDirty := javaTest spec4, mark := true,
    faPolicy := fun S _ _ _ => if lastIterEnd S ≤ lastSp S then lastIterEnd S else 0 }

/-! ## Checks -/

variable {T : Type}

/-- The versions that a lookup at time t may read (`ReadsAt`), by running, as
(node, record) pairs: from the latest versions of the nodes reachable at t,
through the pointers to live children at t, with Rule R. -/
def readsAtB (sp : Spec Val T) (S : SIS.Stream Val T) (P : Struct Val) (t : Time) :
    List (NodeId × Nat) :=
  let s := lastSp S
  let start := (reachList sp P t).eraseDups.filterMap (fun x => S.lv x)
  let fuel := S.foldl (fun n R => n + R.vers.length) 0 + 1
  let res := (List.range fuel).foldl (fun (acc : List (Version Val) × List (NodeId × Nat)) _ =>
    if acc.1.isEmpty then acc else
    let next := acc.1.flatMap (fun v =>
      (sp.live (v.hist.upTo t)).filterMap (fun y => follow S s true y (v.ref? y)))
    let fresh := next.foldl (fun (l : List (Version Val)) w =>
      if acc.2.contains (w.node, w.recNo) || l.any (fun u => u.node == w.node && u.recNo == w.recNo)
      then l else l ++ [w]) []
    (fresh, acc.2 ++ fresh.map (fun w => (w.node, w.recNo))))
    (start, start.map (fun v => (v.node, v.recNo)))
  res.2

/-- The versions that a physical read at time t may follow (`ReadsPhys`), by
running, as (node, record) pairs: as `readsAtB`, and through a pointer to a live
child also every version of the child at or after the record that the pointer
names (every version if it names none), but not through a version that Rule A
put back and that is still in D ((x, r) ∈ D). With all = true, also through such
versions (`ReadsPhys` as WP R6 first had it, for `schemeWitness`). -/
def readsPhysB (sp : Spec Val T) (S : SIS.Stream Val T) (P : Struct Val) (D : Dirty) (t : Time)
    (all : Bool := false) : List (NodeId × Nat) :=
  let s := lastSp S
  let start := (reachList sp P t).eraseDups.filterMap (fun x => S.lv x)
  let fuel := S.foldl (fun n R => n + R.vers.length) 0 + 1
  let versOf := fun (y : NodeId) (lo : Nat) =>
    (List.range S.length).filterMap (fun r => if lo ≤ r then S.versionAt r y else none)
  let res := (List.range fuel).foldl (fun (acc : List (Version Val) × List (NodeId × Nat)) _ =>
    if acc.1.isEmpty then acc else
    let next := acc.1.flatMap (fun v =>
      (sp.live (v.hist.upTo t)).flatMap (fun y =>
        (follow S s true y (v.ref? y)).toList ++
          (if all || !D.contains (v.node, v.recNo) then versOf y ((v.ref? y).getD 0) else [])))
    let fresh := next.foldl (fun (l : List (Version Val)) w =>
      if acc.2.contains (w.node, w.recNo) || l.any (fun u => u.node == w.node && u.recNo == w.recNo)
      then l else l ++ [w]) []
    (fresh, acc.2 ++ fresh.map (fun w => (w.node, w.recNo))))
    (start, start.map (fun v => (v.node, v.recNo)))
  res.2

/-- Conditions 1 and 2 of WP R7's `CutOK` by running: c is at most the first
available time f, and every version that a lookup at some time from f to k may
read (`ReadsAt`) is at c or later. -/
def cutReachAtB (sp : Spec Val T) (c : Nat) (db : DB Val T) (k : Nat) : Bool :=
  let f := lastFa db.S
  decide (c ≤ f) &&
  (List.range' f (k + 1 - f)).all (fun t => (readsAtB sp db.S db.P t).all (fun p => decide (c ≤ p.2)))

/-- Conditions 1 and 2 of `CutOK` by running: c is at most the first available
time f, and every version that a read at some time from f to k may follow
(`ReadsPhys`, since WP R6) is at c or later. With all = true, part 2 also through
the versions of D that Rule A put back (`schemeWitness`). -/
def cutReachB (sp : Spec Val T) (c : Nat) (db : DB Val T) (k : Nat) (all : Bool := false) : Bool :=
  let f := lastFa db.S
  decide (c ≤ f) &&
  (List.range' f (k + 1 - f)).all (fun t =>
    (readsPhysB sp db.S db.P db.D t all).all (fun p => decide (c ≤ p.2)))

/-- Conditions 3 and 4 of `CutOK` by running: the nodes of D, top(k). -/
def cutDTopB (c : Nat) (db : DB Val T) : Bool :=
  db.D.all (fun e => match db.S.lv e.1 with
    | some v => decide (c ≤ v.recNo) &&
        v.refs.all (fun q => decide (c ≤ q.2) || (db.S.lv q.1).map (·.recNo) == some q.2)
    | none => true) &&
  (match db.S.getLast? with
   | some R => match R.top with
     | some (_, r) => decide (c ≤ r)
     | none => true
   | none => true)

/-- `CutOK` by running (with all = true, part 2 as WP R6 first had it). -/
def cutOKB (sp : Spec Val T) (c : Nat) (db : DB Val T) (k : Nat) (all : Bool := false) : Bool :=
  cutReachB sp c db k all && cutDTopB c db

/-- WP R7's `CutOK` (part 2 over `ReadsAt`) by running. -/
def cutOKAtB (sp : Spec Val T) (c : Nat) (db : DB Val T) (k : Nat) : Bool :=
  cutReachAtB sp c db k && cutDTopB c db

/-- The largest c that `CutOK` allows in state db (after T(k)), by running: each
part of it holds for c exactly when c is at most a bound (the first available
time, the records of the versions that lookups from it on may read, of the
latest versions of D's nodes and of their stale references, and of top(k)). -/
def cutBoundB (sp : Spec Val T) (db : DB Val T) (k : Nat) : Nat :=
  let f := lastFa db.S
  let reads := (List.range' f (k + 1 - f)).flatMap (fun t => (readsPhysB sp db.S db.P db.D t).map (·.2))
  let dl := db.D.filterMap (fun e => (db.S.lv e.1).map (·.recNo))
  let stale := db.D.flatMap (fun e => match db.S.lv e.1 with
    | some v => (v.refs.filter (fun q => (db.S.lv q.1).map (·.recNo) != some q.2)).map (·.2)
    | none => [])
  let top := match db.S.getLast? with
    | some R => (R.top.map (·.2)).toList
    | none => []
  (reads ++ dl ++ stale ++ top).foldl min f

/-- The largest safe cut in state db (after T(k)); 0 if none is safe. -/
def safeCut (sp : Spec Val T) (db : DB Val T) (k : Nat) : Nat := cutBoundB sp db k

/-- P and P' agree at every time from f to k for lookups (`SameAt`), by
comparing views: every node but a virtual root, and a virtual root's live
children. -/
def equivFromB (sp : Spec Val T) (f k : Time) (P P' : Struct Val) : Bool :=
  (List.range' f (k + 1 - f)).all (fun t => (ids P P').all (fun x =>
    if sp.virt && x == root then
      (view sp P t x).map (fun n => sp.live n.hist) == (view sp P' t x).map (fun n => sp.live n.hist)
    else view sp P t x == view sp P' t x))

/-- T8 by running, in state db with a cut at c: startup from the cut stream
gives P at every time from the first available time on, and D. -/
def checkT8 (sp : Spec Val T) (c : Nat) (db : DB Val T) : Bool :=
  let db' := startup sp (cutStream c db.S)
  equivFromB sp (lastFa db.S) (db.S.length - 1) db'.P db.P && db'.D == db.D

/-- `PolicyCutOK` by running, in state db, for the transaction tr that comes
next: the same startup pos and first available time on the stream cut at
every c up to the first available time. -/
def policyCutB (al : Algo Val T) (db : DB Val T) (tr : T) : Bool :=
  let i := db.S.length
  (List.range (lastFa db.S + 1)).all (fun c =>
    let S' := cutStream c db.S
    startupPos al S' db.D i tr == startupPos al db.S db.D i tr &&
    (List.range (i + 1)).all (fun s => firstAvail al S' db.D i tr s == firstAvail al db.S db.D i tr s))

/-- The restarts of a run, each from the stream cut at the largest safe
position of the run without restarts at that point. -/
def cutsFor (sp : Spec Val T) (al : Algo Val T) (ts : List (T × Bool)) : List (T × Option Nat) :=
  ts.zipIdx.map (fun p =>
    (p.1.1, if p.1.2 then some (safeCut sp (run sp al ((ts.map (·.1)).take (p.2 + 1))) (p.2 + 1))
      else none))

/-- Results for a run with restarts from cut streams, cs (from `cutsFor`): (the
assumptions and PolicyCutOK hold, T8 holds at every restart, T12 holds: the
stream is the whole stream cut at the largest cut, the same D, the same P from
the first available time on; the largest cut). -/
def checkCut [DecidableEq T] (sp : Spec Val T) (al : Algo Val T) (cs : List (T × Option Nat)) :
    Bool × Bool × Bool × Nat :=
  let tr := cs.map (·.1)
  let ok := runOKB sp al tr &&
    tr.zipIdx.all (fun p => policyCutB al (run sp al (tr.take p.2)) p.1)
  let t8 := cs.zipIdx.all (fun p => match p.1.2 with
    | some c => checkT8 sp c (run sp al (tr.take (p.2 + 1)))
    | none => true)
  let db := runRestartsCut sp al cs
  let r := run sp al tr
  let cm := cutMax (cs.map (·.2))
  let t12 := db.S == cutStream cm r.S && db.D == r.D &&
    equivFromB sp (lastFa r.S) tr.length db.P r.P
  (ok, t8, t12, cm)

/-- As `checkEvict`, with restarts from the stream cut at the given position:
after every transaction the records are the run's, cut at the largest cut so
far, and D is the run's; the schedule, reads at three times from the first
available time on (they give P), the schedule again, the invariants; at a cut,
reads on the cut stream from the running memory at every time from the first
available time on (T9), then the restart from the cut stream, its invariants
and its reads. Returns (transactions, failures). -/
def checkEvictCut [DecidableEq T] (sp : Spec Val T) (al : Algo Val T) (ts : List (T × Option Nat))
    (policy seed : Nat) : Nat × Nat :=
  let ts1 := ts.map (·.1)
  let r := ts.zipIdx.foldl
    (fun (acc : (DB Val T × Mem Val × SIS.Stream Val T) × Nat × Nat × Nat) (p, j) =>
      let ((db, m, S0), cm, n, bad) := acc
      let (db', m') := evictTrans sp al S0 db m p.1
      let after := run sp al (ts1.take (j + 1))
      let k := db'.S.length - 1
      let f := lastFa after.S
      let m1 := schedule policy seed j db'.D m'
      let (m2, readsOK) := reads4 sp S0 db' m1 [k, (f + k) / 2, f + lcg (seed + j) % (k + 1 - f)]
      let m3 := schedule policy (seed + 7) j db'.D m2
      let ok := db'.S == cutStream cm after.S && db'.D == after.D && readsOK &&
        invCanB db' m3 && invSnapB db' m3 && noDanglingB m3 && invSlotB sp S0 db' m3
      match p.2 with
      | some c =>
        let cut := cutStream c db'.S
        let (_, t9) := reads4 sp S0 { db' with S := cut } m3 (List.range' f (k + 1 - f))
        let db2 := startup sp cut
        let m4 := evictStartup sp cut
        let (_, r2) := reads4 sp cut db2 m4 (List.range' f (k + 1 - f))
        let ok' := ok && t9 && r2 && invCanB db2 m4 && noDanglingB m4 && invSlotB sp cut db2 m4
        (((db2, m4, cut), max cm c, n + 1, bad + (if ok' then 0 else 1)))
      | none => (((db', m3, S0), cm, n + 1, bad + (if ok then 0 else 1))))
    ((init sp, evictStartup sp (init sp).S, (init sp).S), 0, 0, 0)
  (r.2.2.1, r.2.2.2)

/-- The cut points of a run with cuts where D holds a node that is not
reachable from the first available time on (a historical node that Rule A keeps
in D, the delicate case of the plan's 8.7). -/
def historicalAtCuts (sp : Spec Val T) (al : Algo Val T) (cs : List (T × Option Nat)) : Nat :=
  let tr := cs.map (·.1)
  (cs.zipIdx.filter (fun p => match p.1.2 with
    | some c =>
      let db := run sp al (tr.take (p.2 + 1))
      let k := p.2 + 1
      let f := lastFa db.S
      decide (0 < c) && db.D.any (fun e => !((List.range' f (k + 1 - f)).any (fun t => reachable sp db.P t e.1)))
    | none => false)).length

/-! ## Random runs -/

/-- n pseudo-random transactions for example 4, with restart marks: puts, now
and then a split, and iterations of two reclaim steps (keys 0 and 1, then 2
and 3) with other transactions between them; each iteration rewrites the
values stored before the previous iteration's first step (pCut). -/
def randomTs4 (seed n : Nat) : List (Tr4 × Bool) :=
  -- The transactions so far, the generator, the step of the iteration that
  -- comes next (0 or 1), this iteration's first step time and the previous
  -- iteration's.
  (List.range n).foldl (fun (acc : List (Tr4 × Bool) × Nat × Nat × Nat × Nat) _ =>
    let (l, g, it, p0, p1) := acc
    let i := l.length + 1
    let x := lcg g
    let y := lcg x
    let r := x / 65536 % 10
    let (tr, it', p0', p1') : Tr4 × Nat × Nat × Nat :=
      if it == 1 && r < 4 then (.step 2 3 true p1, 0, p0, p1)
      else if it == 0 && r < 2 then (.step 0 1 false p0, 1, i, p0)
      else if r == 9 then (.split, it, p0, p1)
      else (.put (y / 1024 % 4) (y / 65536 % 100), it, p0, p1)
    (l ++ [(tr, x / 1024 % 3 == 0)], y, it', p0', p1')) ([], seed, 0, 0, 0)
  |>.1

/-- Startup pos policies: keep the last d transactions in the section, or an
erratic one. None looks at the stream, so `PolicyCutOK` holds for them. -/
def policies4 : List (SIS.Stream Val Tr4 → Dirty → Time → Tr4 → Nat) :=
  [fun _ _ i _ => i - 1, fun _ _ i _ => i - 2, fun _ _ i _ => i - 4,
   fun _ _ i _ => i - 1 - lcg i / 4096 % 5]

/-! ## Example 4, fixed -/

/-- Puts to keys 0 to 2 (key 3 stays empty), an iteration of two reclaim steps at
times 6 and 7 that rewrites the values stored before time 3, and more puts. -/
def ts4 : List Tr4 :=
  [.put 0 11, .put 1 12, .put 0 13, .put 2 14, .put 1 15, .step 0 1 false 3, .step 2 3 true 3,
   .put 0 16, .put 1 17, .put 2 18, .put 0 19, .put 1 20, .put 2 21, .put 0 22, .put 1 23]

/-- Startup pos i - 2. -/
def al4 : Algo Val Tr4 := algo4 (fun _ _ i _ => i - 2)

def run4 : DB Val Tr4 := run spec4 al4 ts4

/-- Example 4 without the touch. -/
def spec4n : Spec Val Tr4 := { spec4 with exec := fun tr i v => { exec4 tr i v with touch := [] } }

-- The run meets the assumptions, the touch's included, and the policies give the
-- same on cut streams.
#guard runOKB spec4 al4 ts4
#guard ts4.zipIdx.all (fun p => policyCutB al4 (run spec4 al4 (ts4.take p.2)) p.1)
-- The step at 7 touches mid node 2 and leaves 5 and 6, whose values are not
-- rewritten (stored at 4, or none): they get dirty without entries (T13'); then
-- Rule A puts back nodes 1, 20 and 30. Without the touch, no node gets dirty.
#guard (run4.S[7]?.map (·.gd)) == some [2, 5, 6, 1, 20, 30]
#guard ((run spec4n al4 ts4).S[7]?.map (·.gd)) == some []
-- The first available time moves to 7, the end of the iteration, in T(10): the
-- startup pos passed 7 in T(9).
#guard (states spec4 al4 ts4).map (fun db => lastFa db.S) ==
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 7, 7, 7, 7, 7, 7]
-- From then on a cut at 3 is safe, and not one at 4: key 0's value of T(3) was not
-- rewritten. Without the touch, no cut is safe: leaf 6 has its only version in R(0).
#guard cutOKB spec4 3 (run spec4 al4 (ts4.take 10)) 10 && !cutOKB spec4 4 (run spec4 al4 (ts4.take 10)) 10
#guard safeCut spec4 run4 15 == 3
#guard safeCut spec4n (run spec4n al4 ts4) 15 == 0
-- T8: startup from the stream cut at 3 gives P at every time from 7 on, and D;
-- not at every time before (the cut removed versions that only earlier times need).
#guard checkT8 spec4 3 run4
#guard !equivFromB spec4 0 15 (startup spec4 (cutStream 3 run4.S)).P run4.P

/-- Restarts after T(10) and T(13), each from the stream cut at the largest safe
position. -/
def tsCut4 : List (Tr4 × Option Nat) :=
  cutsFor spec4 al4 (ts4.zipIdx.map (fun p => (p.1, p.2 + 1 == 10 || p.2 + 1 == 13)))

-- T12: the same records, but those before 3 cut; the same D; the same P from 7 on.
#guard tsCut4.map (·.2) == [none, none, none, none, none, none, none, none, none, some 3, none, none,
  some 3, none, none]
#guard (runRestartsCut spec4 al4 tsCut4).S == cutStream 3 run4.S
#guard (runRestartsCut spec4 al4 tsCut4).D == run4.D
#guard equivFromB spec4 7 15 (runRestartsCut spec4 al4 tsCut4).P run4.P
-- T12's assumption on the cuts (`T12_restartCut`): at each restart, `CutOK` at the
-- largest cut so far, in the run without restarts then.
#guard tsCut4.zipIdx.all (fun p => match p.1.2 with
  | some _ => cutOKB spec4 (cutMax ((tsCut4.take (p.2 + 1)).map (·.2)))
      (run spec4 al4 ((tsCut4.map (·.1)).take (p.2 + 1))) (p.2 + 1)
  | none => true)
-- With eviction and the four cache schedules: the records, D, reads from the first
-- available time on (on the cut stream from the running memory too, T9), the
-- invariants, and the restarts from the cut streams.
#guard [0, 1, 2, 3].all (fun sched => checkEvictCut spec4 al4 tsCut4 sched 1 == (15, 0))

/-- The pSafe wait, found by search on 2026-10-17: seed 11 of `randomTs4`, startup
pos i - 4. After T(7) the first available time is 2 and every node reachable from 2
on has its latest version at 1 or later, but a cut at 1 is not safe: the tree root
(node 20), written at 5 before its mid node 2 (written at 6) and kept in D by Rule
A, names node 2's version in R(0). T(9) writes the tree root again, and then a cut
at 1 is safe. Returns (the assumptions hold; the cut at 1 is not safe after T(7)
only by condition 3, by WP R7's `CutOK` and by `CutOK` since WP R6, whose part 2
does not extend through the tree root's version of R(5), which Rule A put back;
part 2 without that exception, as WP R6 first had it, fails after T(7) too; the
cut is safe after T(9)). -/
def pSafeWitness : Bool × Bool × Bool × Bool × Bool :=
  let al := algo4 (fun _ _ i _ => i - 4)
  let tr := (randomTs4 11 9).map (·.1)
  let db7 := run spec4 al (tr.take 7)
  let db9 := run spec4 al (tr.take 9)
  (runOKB spec4 al tr, cutReachAtB spec4 1 db7 7 && !cutOKAtB spec4 1 db7 7,
    cutReachB spec4 1 db7 7 && !cutOKB spec4 1 db7 7, !cutReachB spec4 1 db7 7 true,
    cutOKB spec4 1 db9 9)

#guard pSafeWitness == (true, true, true, true, true)

-- The bound gives the same cuts as `CutOK` by running, on the fixed run.
#guard (states spec4 al4 ts4).zipIdx.all (fun (db, k) =>
  (List.range (lastFa db.S + 1)).all (fun c => cutOKB spec4 c db k == decide (c ≤ cutBoundB spec4 db k)))

/-! ### A stale reference before the cut (WP R7)

Example 4 with both leaves of mid node 2 empty, so that nothing under it is
written for a while. Puts to keys 0 and 1 write the tree root (node 20) at
record 3, naming mid node 2's version of R(0); then a split (T(3)) replaces the
tree root, and puts to keys 2 and 3 write mid node 2 again, through the new
tree root, at records 5 and 6. With the first available time 2, every node
reachable from 2 on has its latest version at 1 or later, which WP R3's part 2
asked; but a lookup at 2 reads the tree root's version of R(3), which names
mid node 2's version of R(0). -/

/-- Example 4 with both leaves of mid node 2 empty at first. -/
def spec4e : Spec Val Tr4 :=
  { spec4 with init := [(0, { level := 1000, isData := false, hist := [⟨0, .slot 0 30⟩] }),
      (30, { level := 100, isData := false, hist := [⟨0, .ref 20⟩] }),
      (20, mk 3 [.slot 0 1, .slot 1 2]),
      (1, mk 2 [.slot 0 3, .slot 1 4]), (2, mk 2 [.slot 0 5, .slot 1 6]),
      (3, mk 1 [.slot 0 7]), (4, mk 1 [.slot 0 8]), (5, mk 1 []), (6, mk 1 []),
      (7, { level := 0, isData := true, hist := [⟨0, .dat 1⟩] }),
      (8, { level := 0, isData := true, hist := [⟨0, .dat 2⟩] })] }

/-- Startup pos i - 1, the first available time 2 (from T(3) on, clamped). -/
def alE : Algo Val Tr4 :=
  { policy := fun _ _ i _ => i - 1, stillDirty := javaTest spec4e, mark := true,
    faPolicy := fun _ _ _ _ => 2 }

def tsE : List Tr4 := [.put 0 11, .put 1 12, .split, .put 2 13, .put 3 14, .put 0 15, .put 0 16, .put 0 17]

/-- WP R3's part 2: every node reachable at some time from f to k has its latest
version at c or later. -/
def latestB (sp : Spec Val T) (c : Nat) (db : DB Val T) (k : Nat) : Bool :=
  let f := lastFa db.S
  decide (c ≤ f) &&
  (allIds db.P).all (fun x =>
    !((List.range' f (k + 1 - f)).any (fun t => reachable sp db.P t x)) ||
    ((db.S.lv x).map (fun v => decide (c ≤ v.recNo))).getD true)

/-- Returns (the assumptions hold; WP R3's `CutOK` allows a cut at 1 after T(8);
then a physical read at 2, after a restart from the stream cut at 1, does not
give P; the `CutOK` of WP R7 does not allow it; from the whole stream the read
gives P). Found on 2026-10-17. -/
def staleWitness : Bool × Bool × Bool × Bool × Bool :=
  let db := run spec4e alE tsE
  let cut := cutStream 1 db.S
  let (_, onCut) := reads4 spec4e cut { db with S := cut } (evictStartup spec4e cut) [2]
  let (_, onWhole) := reads4 spec4e db.S db (evictStartup spec4e db.S) [2]
  (runOKB spec4e alE tsE, latestB spec4e 1 db 8 && cutDTopB 1 db, !onCut, !cutOKB spec4e 1 db 8, onWhole)

#guard staleWitness == (true, true, true, true, true)

/-- A run with eviction (cache schedule `policy`, as in `checkEvict`), without
restarts: the records and D, the memory, the stream of the last startup. -/
def runEvictWith (sp : Spec Val T) (al : Algo Val T) (ts : List T) (policy seed : Nat) :
    DB Val T × Mem Val × SIS.Stream Val T :=
  ts.zipIdx.foldl (fun (acc : DB Val T × Mem Val × SIS.Stream Val T) p =>
      let r := evictTrans sp al acc.2.2 acc.1 acc.2.1 p.1
      (r.1, schedule policy seed p.2 r.1.D r.2, acc.2.2))
    (init sp, evictStartup sp (init sp).S, (init sp).S)

/-- Returns (the assumptions hold, and the run with eviction appends the run's
records; WP R7's `CutOK` allows a cut at 1 after T(6); with every object that may
be evicted evicted after each transaction (schedule 1), a read at the first
available time 2 from the running memory, with Rule R of the startup at R(0),
does not give P on the stream cut at 1; on the whole stream it does; `CutOK`
since WP R6 does not allow the cut). The tree root 20, reachable at 2 and
replaced at 3, names mid node 2's version of R(0); the mid node's latest version
is of R(6), in the startup section, so the lookups' reads (`ReadsAt`) take that
one by Rule R. The running memory's Rule R is the startup's, which does not know
it, and the mid node's canonical object was evicted: the read loads R(0), which
the cut removed. Physical reads in the running process after a cut needed more
than WP R7's `CutOK` (bergdb item 001, WP R4: T9; register M48); `CutOK`'s part 2
over `ReadsPhys` (WP R6, M48's option (a), Frans 2026-10-17) covers R(0). Found
on 2026-10-17. -/
def cutReadWitness : Bool × Bool × Bool × Bool × Bool :=
  let ts := tsE.take 6
  let db := run spec4e alE ts
  let r := runEvictWith spec4e alE ts 1 1
  let (_, onCut) := reads4 spec4e r.2.2 { r.1 with S := cutStream 1 r.1.S } r.2.1 [2]
  let (_, onWhole) := reads4 spec4e r.2.2 r.1 r.2.1 [2]
  (runOKB spec4e alE ts && r.1.S == db.S && r.1.D == db.D, cutOKAtB spec4e 1 db 6, !onCut, onWhole,
    !cutOKB spec4e 1 db 6)

#guard cutReadWitness == (true, true, true, true, true)

/-! ### Java's scheme and part 2 of `CutOK` (WP R6)

T-SCHEME, by running before proving: in example 4's random runs, with the
scheme's conditions (the touches of an iteration's steps cover the index nodes
reachable at its end that have no version after pStart, `touchCoverB`; its
rewrites leave every data node reachable at its end at pCut or later,
`rewritesB`; the startup pos passed tEnd at a transaction j0, the decision
needs it past j0), part 2 of `CutOK` held in every state when it extends
through every version that a physical read may follow, but in one of about
22,000 (policy 2, seed 14, n = 60) when the wait for tEnd was not strict. A
search for the pattern gave this witness, with Java's strict waits: an iteration
of steps at 1 and 3 (pStart 0, pCut 1), a put to key 3 between them, then puts
to key 0, and a startup pos that lags. The tree root 20 is put back by Rule A at
5 (mid node 2 in D), mid node 2 at 6 (leaf 5 in D, its version of R(0) named),
leaf 5 written at 7, the tree root put back again at 9 (mid node 2 in D still),
naming mid node 2's version of R(6); mid node 2 written at 10. After T(11) (startup
pos 8, past j0 = 7, where it first passed tEnd = 3), part 2 without the exception
fails: the tree root's version of R(9), in D, leads to mid node 2's of R(6) and so
to leaf 5's of R(0), before the cut at 1. The running memory reads through the
tree root's canonical object, whose slot names mid node 2's latest version: with
every cache schedule, the reads from 3 to 11 give P on the stream cut at 1. Hence
the exception in `ReadsPhys`. -/

/-- The touches of transactions pStart + 1 to tEnd cover every index node
reachable at tEnd whose latest version then is at pStart or before. -/
def touchCoverB (sp : Spec Val Tr4) (al : Algo Val Tr4) (ts : List Tr4) (pStart tEnd : Nat) : Bool :=
  let db := run sp al (ts.take tEnd)
  (allIds db.P).all (fun x =>
    if isIndex db.P x && written sp x && reachable sp db.P tEnd x then
      match db.S.lv x with
      | some v => !(decide (v.recNo ≤ pStart)) ||
          (List.range' (pStart + 1) (tEnd - pStart)).any (fun i =>
            match ts[i - 1]? with
            | some tr => (sp.exec tr i (view sp (run sp al (ts.take (i - 1))).P (i - 1))).touch.contains x
            | none => false)
      | none => true
    else true)

/-- Every data node reachable at tEnd has its version at pCut or later. -/
def rewritesB (sp : Spec Val Tr4) (al : Algo Val Tr4) (ts : List Tr4) (pCut tEnd : Nat) : Bool :=
  let db := run sp al (ts.take tEnd)
  (allIds db.P).all (fun x =>
    match db.P.get? x with
    | some n => !(n.isData && reachable sp db.P tEnd x) ||
        ((db.S.lv x).map (fun v => decide (pCut ≤ v.recNo))).getD false
    | none => true)

/-- The witness's startup pos, by transaction. -/
def spW : List Nat := [0, 0, 0, 0, 0, 1, 2, 4, 4, 5, 6, 8]

def alW : Algo Val Tr4 := algo4 (fun _ _ i _ => spW.getD i (i - 1))

def tsW : List Tr4 :=
  [.step 0 1 false 1, .put 3 50, .step 2 3 true 1, .put 0 60, .put 0 61, .put 0 62, .put 0 63,
   .put 0 64, .put 0 65, .put 0 66, .put 0 67]

/-- Returns (the assumptions hold; the scheme's conditions: the touches cover,
the rewrites, the startup pos passed tEnd = 3 first at T(7) and is past 7 at T(11),
and the first available time is 3; part 2 without the exception for put-back
versions fails at 1 after T(11); `CutOK` holds at 1 after T(11), and so does WP
R7's; with every cache schedule, the reads from the running memory at every time
from 3 to 11 give P on the stream cut at 1). -/
def schemeWitness : Bool × Bool × Bool × Bool × Bool :=
  let db := run spec4 alW tsW
  let sps := (List.range 12).map (fun j => lastSp (run spec4 alW (tsW.take j)).S)
  let reads := [0, 1, 2, 3].all (fun sched =>
    let r := runEvictWith spec4 alW tsW sched 1
    r.1.S == db.S && (List.range' 3 9).all (fun t =>
      (reads4 spec4 r.2.2 { r.1 with S := cutStream 1 r.1.S } r.2.1 [t]).2))
  (runOKB spec4 alW tsW,
    touchCoverB spec4 alW tsW 0 3 && rewritesB spec4 alW tsW 1 3 &&
      sps.findIdx? (fun s => decide (3 < s)) == some 7 && decide (7 < lastSp db.S) && lastFa db.S == 3,
    !cutReachB spec4 1 db 11 true, cutOKB spec4 1 db 11 && cutOKAtB spec4 1 db 11, reads)

#guard schemeWitness == (true, true, true, true, true)

/-! ## Example 4 meets T8's assumptions on its virtual root

The root's entries are `.slot 0 z`. Its live child is the root child of its
last entry (`VirtLiveOK`), and example 4's transactions see the root only through
it (`ExecRootOK`). -/

theorem foldl_slot_root (k : Nat) : ∀ (h : History Val) (acc : Option NodeId),
    (∀ e ∈ h, ∃ z, e.val = Val.slot 0 z) →
    h.foldl (fun acc e => match e.val with
      | .slot k' y => if k' = k then some y else acc
      | _ => acc) acc =
      if k = 0 then (h.getLast?.bind (fun e => (ptrs e.val).head?)).or acc else acc := by
  intro h
  induction h with
  | nil => intro acc _; simp
  | cons a l ih =>
    intro acc hh
    obtain ⟨za, hza⟩ := hh a List.mem_cons_self
    rw [List.foldl_cons, ih _ (fun e he => hh e (List.mem_cons_of_mem a he))]
    by_cases hk : k = 0
    · subst hk
      simp only [hza, ↓reduceIte]
      cases hl : l.getLast? with
      | none =>
        rw [List.getLast?_eq_none_iff] at hl
        subst hl
        simp [hza, ptrs]
      | some e =>
        have hne : l ≠ [] := by intro h0; rw [h0] at hl; simp at hl
        rw [List.getLast?_cons_of_ne_nil hne, hl]
        obtain ⟨ze, hze⟩ := hh e (List.mem_cons_of_mem a (List.mem_of_getLast? hl))
        simp [hze, ptrs]
    · have h0k : (0 = k) = False := by simp; omega
      simp [hza, hk, h0k]

theorem slotOf_root (h : History Val) (hh : ∀ e ∈ h, ∃ z, e.val = Val.slot 0 z) (k : Nat) :
    slotOf h k = if k = 0 then h.getLast?.bind (fun e => (ptrs e.val).head?) else none := by
  unfold slotOf
  exact (foldl_slot_root k h none hh).trans (by split <;> simp)

theorem filterMap_eq_map_of {α β : Type} (f : α → Option β) (g : α → β) :
    ∀ (l : List α), (∀ a ∈ l, f a = some (g a)) → l.filterMap f = l.map g := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    intro h
    rw [List.filterMap_cons, h a List.mem_cons_self, List.map_cons,
      ih (fun b hb => h b (List.mem_cons_of_mem a hb))]

theorem live_root (h : History Val) (hh : ∀ e ∈ h, ∃ z, e.val = Val.slot 0 z) :
    live h = (h.getLast?.map (fun e => ptrs e.val)).getD [] := by
  unfold live
  dsimp only
  rw [(List.filterMap_eq_nil_iff (l := h)).mpr ?hr]
  rotate_left
  · intro e he
    obtain ⟨z, hz⟩ := hh e he
    simp [hz]
  rw [filterMap_eq_map_of _ (fun _ => 0) h ?hs]
  rotate_left
  · intro e he
    obtain ⟨z, hz⟩ := hh e he
    simp [hz]
  rw [List.nil_append]
  cases hl : h.getLast? with
  | none => rw [List.getLast?_eq_none_iff] at hl; subst hl; rfl
  | some e =>
    obtain ⟨z, hz⟩ := hh e (List.mem_of_getLast? hl)
    have hsl : slotOf h 0 = some z := by
      rw [slotOf_root h hh 0, hl]; simp [hz, ptrs]
    obtain ⟨a, l, rfl⟩ : ∃ a l, h = a :: l := by
      cases h with
      | nil => simp at hl
      | cons a l => exact ⟨a, l, rfl⟩
    have hf : (l.map (fun _ => (0 : Nat))).filter (fun b => !b == 0) = [] := by
      rw [List.filter_eq_nil_iff]
      intro b hb
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hb
      simp
    simp only [List.map_cons, List.eraseDups_cons, hf, List.eraseDups_nil, List.filterMap_cons,
      List.filterMap_nil, hsl]
    simp [hz, ptrs]

/-- In a history of root entries, the live child is the one of slot 0. -/
theorem live_head_root (h : History Val) (hh : ∀ e ∈ h, ∃ z, e.val = Val.slot 0 z) :
    (live h).head? = slotOf h 0 := by
  rw [live_root h hh, slotOf_root h hh 0]
  cases hl : h.getLast? with
  | none => rfl
  | some e =>
    obtain ⟨z, hz⟩ := hh e (List.mem_of_getLast? hl)
    simp [hz, ptrs]

theorem valOf_root (n : Node Val) (hh : ∀ e ∈ n.hist, ∃ z, e.val = Val.slot 0 z) : valOf n = 0 := by
  unfold valOf
  rw [(List.filterMap_eq_nil_iff (l := n.hist)).mpr ?hd]
  · rfl
  · intro e he
    obtain ⟨z, hz⟩ := hh e he
    simp [hz]

theorem virtLiveOK_spec4 : VirtLiveOK spec4 := fun _ h hh => live_root h hh

theorem virtLiveOK_spec4e : VirtLiveOK spec4e := fun _ h hh => live_root h hh

/-- Two views that example 4's transactions cannot tell apart: the same nodes,
with the same slots, live pointers and values. -/
def SameObs (v v' : View Val) : Prop :=
  ∀ x, ((v x).isSome = (v' x).isSome) ∧ ∀ n n', v x = some n → v' x = some n' →
    (∀ k, slotOf n.hist k = slotOf n'.hist k) ∧ live n.hist = live n'.hist ∧ valOf n = valOf n'

section Obs

variable {v v' : View Val}

theorem SameObs.cases (h : SameObs v v') (x : NodeId) :
    (v x = none ∧ v' x = none) ∨ ∃ n n', v x = some n ∧ v' x = some n' ∧
      (∀ k, slotOf n.hist k = slotOf n'.hist k) ∧ live n.hist = live n'.hist ∧ valOf n = valOf n' := by
  obtain ⟨hs, hn⟩ := h x
  cases hv : v x with
  | none =>
    cases hv' : v' x with
    | none => exact Or.inl ⟨rfl, rfl⟩
    | some n' => rw [hv, hv'] at hs; simp at hs
  | some n =>
    cases hv' : v' x with
    | none => rw [hv, hv'] at hs; simp at hs
    | some n' => exact Or.inr ⟨n, n', rfl, rfl, hn n n' hv hv'⟩

theorem SameObs.bind_slot (h : SameObs v v') (x : NodeId) (k : Nat) :
    (v x).bind (fun n => slotOf n.hist k) = (v' x).bind (fun n => slotOf n.hist k) := by
  rcases h.cases x with ⟨h1, h2⟩ | ⟨n, n', h1, h2, hs, -, -⟩
  · rw [h1, h2] <;> rfl
  · rw [h1, h2]; exact hs k

theorem SameObs.bind_live (h : SameObs v v') (x : NodeId) :
    (v x).bind (fun n => (live n.hist).head?) = (v' x).bind (fun n => (live n.hist).head?) := by
  rcases h.cases x with ⟨h1, h2⟩ | ⟨n, n', h1, h2, -, hl, -⟩
  · rw [h1, h2] <;> rfl
  · rw [h1, h2]; simp only [Option.bind_some]; rw [hl]

theorem SameObs.path4 (h : SameObs v v') (t : NodeId) (k : Nat) :
    pathOf4 v t k = pathOf4 v' t k := by
  unfold pathOf4
  rcases h.cases t with ⟨h1, h2⟩ | ⟨n, n', h1, h2, hs, -, -⟩
  · rw [h1, h2] <;> rfl
  · rw [h1, h2]
    simp only [Option.bind_some]
    rw [hs (k / 2 % 2)]
    cases slotOf n'.hist (k / 2 % 2) with
    | none => rfl
    | some m =>
      simp only [Option.bind_some]
      rcases h.cases m with ⟨g1, g2⟩ | ⟨u, u', g1, g2, gs, -, -⟩
      · rw [g1, g2] <;> rfl
      · rw [g1, g2]; simp only [Option.bind_some]; rw [gs (k % 2)]

theorem SameObs.vals (h : SameObs v v') (p : Nat × NodeId × NodeId) (b : Nat) :
    (v p.2.2).bind (fun ln => (slotOf ln.hist 0).bind (fun d => if d < 10000 + 8 * b then
      (v d).map (fun dn => (p.1, p.2.2, valOf dn)) else none)) =
    (v' p.2.2).bind (fun ln => (slotOf ln.hist 0).bind (fun d => if d < 10000 + 8 * b then
      (v' d).map (fun dn => (p.1, p.2.2, valOf dn)) else none)) := by
  rcases h.cases p.2.2 with ⟨h1, h2⟩ | ⟨n, n', h1, h2, hs, -, -⟩
  · rw [h1, h2] <;> rfl
  · rw [h1, h2]
    simp only [Option.bind_some]
    rw [hs 0]
    cases slotOf n'.hist 0 with
    | none => rfl
    | some d =>
      simp only [Option.bind_some]
      split
      · rcases h.cases d with ⟨g1, g2⟩ | ⟨u, u', g1, g2, -, -, gv⟩
        · rw [g1, g2] <;> rfl
        · rw [g1, g2]; simp only [Option.map_some]; rw [gv]
      · rfl

/-- Example 4's transactions give the same changes on views they cannot tell
apart. -/
theorem exec4_sameObs (tr : Tr4) (i : Time) (h : SameObs v v') : exec4 tr i v = exec4 tr i v' := by
  unfold exec4
  rw [h.bind_slot 0 0]
  cases (v' 0).bind (fun r => slotOf r.hist 0) with
  | none => rfl
  | some z =>
    simp only
    rw [h.bind_live z]
    cases (v' z).bind (fun zn => (live zn.hist).head?) with
    | none => rfl
    | some t =>
      simp only
      cases tr with
      | split =>
        simp only
        rcases h.cases t with ⟨h1, h2⟩ | ⟨n, n', h1, h2, hs, -, -⟩
        · rw [h1, h2]
        · rw [h1, h2]
          simp only
          rw [hs 0, hs 1]
      | put k n =>
        simp only
        rw [h.path4 t k]
      | step lo hi last b =>
        simp only [h.path4, h.vals]

end Obs

theorem execRootOK_spec4 : ExecRootOK spec4 := by
  intro _ tr i v v' hr hr' hx hl
  apply exec4_sameObs
  intro x
  by_cases hx0 : x = root
  · subst hx0
    refine ⟨?_, ?_⟩
    · have := congrArg Option.isSome hl
      simpa using this
    · intro n n' h1 h2
      rw [h1, h2] at hl
      simp only [Option.map_some, Option.some.injEq] at hl
      have e1 : ∀ e ∈ n.hist, ∃ z, e.val = Val.slot 0 z := hr n h1
      have e2 : ∀ e ∈ n'.hist, ∃ z, e.val = Val.slot 0 z := hr' n' h2
      refine ⟨fun k => ?_, hl, by rw [valOf_root n e1, valOf_root n' e2]⟩
      by_cases hk : k = 0
      · subst hk
        rw [← live_head_root n.hist e1, ← live_head_root n'.hist e2]
        exact congrArg List.head? hl
      · rw [slotOf_root n.hist e1 k, slotOf_root n'.hist e2 k]
        simp [hk]
  · rw [hx x hx0]
    exact ⟨rfl, fun n n' h1 h2 => by rw [h1] at h2; cases h2; exact ⟨fun _ => rfl, rfl, rfl⟩⟩

end SIS.ReclaimExample
