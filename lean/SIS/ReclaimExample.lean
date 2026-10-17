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

/-- Conditions 1 and 2 of `CutOK` by running: c is at most the first available
time f, and every node reachable at some time from f to k has its latest
version at c or later. -/
def cutReachB (sp : Spec Val T) (c : Nat) (db : DB Val T) (k : Nat) : Bool :=
  let f := lastFa db.S
  decide (c ≤ f) &&
  (allIds db.P).all (fun x =>
    !((List.range' f (k + 1 - f)).any (fun t => reachable sp db.P t x)) ||
    ((db.S.lv x).map (fun v => decide (c ≤ v.recNo))).getD true)

/-- `CutOK` by running. -/
def cutOKB (sp : Spec Val T) (c : Nat) (db : DB Val T) (k : Nat) : Bool :=
  cutReachB sp c db k &&
  db.D.all (fun e => match db.S.lv e.1 with
    | some v => decide (c ≤ v.recNo) &&
        v.refs.all (fun q => decide (c ≤ q.2) || (db.S.lv q.1).map (·.recNo) == some q.2)
    | none => true) &&
  (match db.S.getLast? with
   | some R => match R.top with
     | some (_, r) => decide (c ≤ r)
     | none => true
   | none => true)

/-- The largest safe cut in state db (after T(k)): every c from the first
available time down is tried; 0 if none is safe. -/
def safeCut (sp : Spec Val T) (db : DB Val T) (k : Nat) : Nat :=
  ((List.range (lastFa db.S + 1)).reverse.find? (fun c => cutOKB sp c db k)).getD 0

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
-- With eviction and the four cache schedules: the records, D, reads from the first
-- available time on (on the cut stream from the running memory too, T9), the
-- invariants, and the restarts from the cut streams.
#guard [0, 1, 2, 3].all (fun sched => checkEvictCut spec4 al4 tsCut4 sched 1 == (15, 0))

/-- The pSafe wait, found by search on 2026-10-17: seed 11 of `randomTs4`, startup
pos i - 4. After T(7) the first available time is 2 and every node reachable from 2
on has its latest version at 1 or later, but a cut at 1 is not safe: the tree root
(node 20), written at 5 before its mid node 2 (written at 6) and kept in D by Rule
A, names node 2's version in R(0). T(9) writes the tree root again, and then a cut
at 1 is safe. Returns (the assumptions hold, the cut at 1 is not safe after T(7)
only by condition 3, it is safe after T(9)). -/
def pSafeWitness : Bool × Bool × Bool :=
  let al := algo4 (fun _ _ i _ => i - 4)
  let tr := (randomTs4 11 9).map (·.1)
  let db7 := run spec4 al (tr.take 7)
  let db9 := run spec4 al (tr.take 9)
  (runOKB spec4 al tr, cutReachB spec4 1 db7 7 && !cutOKB spec4 1 db7 7, cutOKB spec4 1 db9 9)

#guard pSafeWitness == (true, true, true)

end SIS.ReclaimExample
