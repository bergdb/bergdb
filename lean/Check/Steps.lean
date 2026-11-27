/-
The trace checker: the checks (bergdb 011-11, 8.5; 027-02).

Not part of the trusted part. The checker runs the model's own `init` and
`step` (SIS/Algorithm.lean) with the switches of `Opts`: marking in step 3
(`Algo.mark`), BergDB's still-dirty test in step 7 (`javaTest`), and the
virtual root of option (a) (`Spec.virt`). Written 2026-10-15 for F1-008-11,
WP C2; since 2026-10-16 (WP E3) without checker-local definitions.
-/
import Check.Trace
import Check.Fast
import SIS.Phys
import SIS.Handle
import SIS.Reclaim
import Check.R4
import Check.Tree
import Std.Data.HashSet
import Std.Data.HashMap

namespace SIS.Check

open SIS

/-- The checker's switches. -/
structure Opts where
  /-- Step 3 marks the access path of the change (`Algo.mark`) instead of the
  exact dirty test. -/
  mark : Bool := true
  /-- Step 7 is BergDB's test (`javaTest`: a written node goes back to D if one
  of its pointees, live or dead, is in D) instead of the exact test. -/
  java7 : Bool := true
  /-- The root is virtual (option (a), `Spec.virt`): never in D, never
  written; top(i) is the latest version of the root's child at s(i). -/
  virtual : Bool := true
  /-- Also check that every dirty index node is in D (INV-2). Slow. -/
  inv : Bool := false

/-- The model's algorithm with the checker's switches; pol gives the startup
pos that Java chose for transaction j, and faPol its first available time
(bergdb item 001, WP R7; the model clamps it, `firstAvail`). -/
def algoOf (sp : Spec BVal Nat) (o : Opts) (pol : Nat → Nat) (faPol : Nat → Nat := fun _ => 0) :
    Algo BVal Nat :=
  { policy := fun _ _ j _ => pol j, stillDirty := if o.java7 then javaTest sp else exactTest sp,
    mark := o.mark, faPolicy := fun _ _ j _ => faPol j }

/-! ## Comparisons -/

def sameList {α : Type} [BEq α] (a b : List α) : Bool :=
  a.all (b.contains ·) && b.all (a.contains ·)

def showOpt (o : Option (Nat × Nat)) : String :=
  match o with
  | some (z, r) => s!"R({r}) of node {z}"
  | none => "-"

def showIds (l : List Nat) : String :=
  " ".intercalate ((l.take 12).map toString) ++ (if l.length > 12 then " ..." else "")

/-- The differences of two records, by field: (field, message). Versions are
compared as a set by node, gd as a set (docs, 7.3). The node of top is compared
when the trace gives it (node 0 otherwise). -/
def diffRecord (m j : Record BVal Nat) : List (String × String) :=
  let sp := if m.sp == j.sp then [] else [("sp", s!"sp: model {m.sp}, Java {j.sp}")]
  let fa := if m.fa == j.fa then [] else [("fa", s!"fa: model {m.fa}, Java {j.fa}")]
  let topOk := m.top.map (·.2) == j.top.map (·.2) &&
    (j.top.map (·.1) == some 0 || m.top.map (·.1) == j.top.map (·.1))
  let top := if topOk then []
    else [("top", s!"top: model {showOpt m.top}, Java {showOpt j.top}")]
  let gdDup := if j.gd.eraseDups.length == j.gd.length then [] else [("gd", "gd: Java repeats a node")]
  let gd := if sameList m.gd j.gd then []
    else [("gd", s!"gd: model only [{showIds (m.gd.filter (!j.gd.contains ·))}], " ++
      s!"Java only [{showIds (j.gd.filter (!m.gd.contains ·))}]")]
  let mIds := m.vers.map (·.node)
  let jIds := j.vers.map (·.node)
  let missing := mIds.filter (!jIds.contains ·)
  let extra := jIds.filter (!mIds.contains ·)
  let vset := (if missing.isEmpty then [] else [("versions", s!"versions only in the model: [{showIds missing}]")]) ++
    (if extra.isEmpty then [] else [("versions", s!"versions only in Java: [{showIds extra}]")])
  let common := mIds.filter (jIds.contains ·)
  let vdiff := common.filterMap (fun x =>
    match m.vers.find? (·.node == x), j.vers.find? (·.node == x) with
    | some a, some b =>
      if a.hist != b.hist then some ("hist", s!"history of node {x} differs")
      else if !sameList a.refs b.refs then
        some ("refs", s!"references of node {x}: model {a.refs.take 6}, Java {b.refs.take 6}")
      else if a.level != b.level || a.isData != b.isData then some ("kind", s!"level or kind of node {x}")
      else none
    | _, _ => none)
  sp ++ fa ++ top ++ gdDup ++ gd ++ vset ++ vdiff

/-! ## The assumptions, by running (SIS/Assumptions.lean; Example.lean has the
same checks for its examples) -/

/-- The failures of `VirtStep` (R1 to R4 with a virtual root) for transaction
i, by name. rlNow holds `reachList sp (P.apply i c) i`. -/
def virtFailures (sp : Spec BVal Nat) (P : Struct BVal) (i : Time) (c : Changes BVal)
    (rlNow : Std.HashSet NodeId) : List (String × List NodeId) :=
  let P' := P.apply i c
  let topNode := fun (p : NodeId × Node BVal) => p.1 != root && decide (sp.topLevel ≤ p.2.level)
  let topIds : Std.HashSet NodeId := Std.HashSet.ofList ((P'.filter topNode).map (·.1))
  let tops := c.new.filter (fun nn => decide (sp.topLevel ≤ nn.level))
  let newTop := if tops.length ≤ 1 && tops.all (fun nn => !nn.isData && c.adds.any (fun a => a.1 == nn.id))
    then [] else tops.map (·.id)
  let topFixed := (c.adds.filter (fun a => match P.get? a.1 with
    | some n => a.1 != root && decide (sp.topLevel ≤ n.level)
    | none => false)).map (·.1)
  let rootAdds := if c.adds.filter (fun a => a.1 == root) == tops.map (fun nn => (root, sp.rootVal nn.id))
    then [] else [root]
  -- R4: the root children of P not in the closure of the new one. Since bergdb item 001,
  -- WP C2, first the chain test (Check/R4.lean): when it passes, every one is in the
  -- closure (`r4Fast_sound`), so the filter would give none, and `topClosure`, exponential
  -- in the number of root children, is not evaluated.
  let r4 := tops.flatMap (fun nn => match P'.get? nn.id with
    | some n =>
      if TopBridge.r4Fast sp P P' nn.id then []
      else
        let cl := topClosure sp P' nn.id n
        (allIds P).filter (fun y => isTop sp P y && !cl.contains y)
    | none => [nn.id])
  let dead := (P'.filter topNode).flatMap (fun p =>
    (pointees sp p.2.hist).filter (fun y => topIds.contains y && rlNow.contains y))
  [("R-newTop", newTop.eraseDups), ("R3-topFixed", topFixed.eraseDups), ("R2-rootAdds", rootAdds),
   ("R4", r4.eraseDups), ("R-dead", dead.eraseDups)].filter (fun p => !p.2.isEmpty)

/-- The failures of `StepOK` and A5 for transaction i, by name, with the nodes.
rlPrev and rlNow hold the nodes reachable before (at i - 1) and after (at i);
rlNowList is the latter as a list. -/
def stepFailures (sp : Spec BVal Nat) (P : Struct BVal) (i : Time) (c : Changes BVal)
    (rlPrev rlNow : Std.HashSet NodeId) (rlNowList : List NodeId) : List (String × List NodeId) :=
  let P' := P.apply i c
  let ids := c.new.map (·.id)
  let fresh := (c.new.filter (fun n => (P.get? n.id).isSome)).map (·.id)
  let distinct := if ids.eraseDups.length == ids.length then [] else ids
  let a2 := (c.adds.filter (fun a => !rlNow.contains a.1)).map (·.1)
  let dataFixed := (c.adds.filter (fun a => match P.get? a.1 with
    | some n => n.isData
    | none => false)).map (·.1)
  let dataNoPtrs := (c.adds.filter (fun a => c.new.any (fun n => n.id == a.1 && n.isData) &&
    !(sp.ptrs a.2).isEmpty)).map (·.1)
  let a4 := (c.adds.filter (fun a => !(sp.ptrs a.2).all (fun y =>
    match P'.get? a.1, P'.get? y with
    | some n, some m => decide (m.level < n.level)
    | _, _ => false))).map (·.1)
  let a3 := (c.new.filter (fun n => !rlNow.contains n.id)).map (·.id)
  let a5 := rlNowList.filter (fun y => !rlPrev.contains y && !ids.contains y)
  [("fresh", fresh.eraseDups), ("distinct", distinct.eraseDups), ("A2", a2.eraseDups),
   ("dataFixed", dataFixed.eraseDups), ("dataNoPtrs", dataNoPtrs.eraseDups), ("A4", a4.eraseDups),
   ("A3", a3.eraseDups), ("A5", a5.eraseDups)].filter (fun p => !p.2.isEmpty) ++
  (if sp.virt then virtFailures sp P i c rlNow else [])

/-- TouchOK (`StepOK.touchIndex`, `touchReach` and `touchUp`; bergdb item 001,
WPs R3 and R7), by name: the touched nodes that are no index nodes of P, or not
reachable at i - 1; and the nodes reachable at i - 1 with a touched node below
them, through live pointers to lower levels as `reachFrom`, that are not touched
themselves, a virtual root aside. Lowest level first, as `copyFailures`. rlPrev
holds `reachList sp P (i - 1)`, rlPrevSet the same as a set.

And the bound of the touch (`TouchOnPaths` of SIS/ReclaimTheorems.lean; 024-07),
`touchPath`: the touched nodes that have no node below them at i - 1, themselves
included, that the change gives an entry or that is no longer reachable at i.
rlNowSet holds the nodes reachable at i. -/
def touchFailures (sp : Spec BVal Nat) (P : Struct BVal) (i : Time) (c : Changes BVal)
    (rlPrev : List NodeId) (rlPrevSet rlNowSet : Std.HashSet NodeId) : List (String × List NodeId) :=
  if c.touch.isEmpty then [] else
  let tset : Std.HashSet NodeId := Std.HashSet.ofList c.touch
  let notIndex := c.touch.filter (fun x => !isIndex P x)
  let notReach := c.touch.filter (fun x => !rlPrevSet.contains x)
  let lv := fun x => ((P.get? x).map (·.level)).getD 0
  let xs := rlPrev.eraseDups.mergeSort (fun a b => decide (lv a ≤ lv b))
  let below : Std.HashMap NodeId Bool := xs.foldl (fun m x =>
    match P.get? x with
    | some n => m.insert x (tset.contains x || (sp.live (n.hist.upTo (i - 1))).any (fun y =>
        match P.get? y with
        | some ny => decide (ny.level < n.level) && m.getD y false
        | none => false))
    | none => m) {}
  let up := xs.filter (fun x => below.getD x false && !tset.contains x && !(sp.virt && x == root))
  let onPath : Std.HashMap NodeId Bool := xs.foldl (fun m x =>
    match P.get? x with
    | some n => m.insert x (changed c x || !rlNowSet.contains x ||
        (sp.live (n.hist.upTo (i - 1))).any (fun y =>
          match P.get? y with
          | some ny => decide (ny.level < n.level) && m.getD y false
          | none => false))
    | none => m) {}
  let offPath := c.touch.filter (fun x => rlPrevSet.contains x && !onPath.getD x false)
  [("touchIndex", notIndex), ("touchReach", notReach), ("touchUp", up),
   ("touchPath", offPath)].filter (fun p => !p.2.isEmpty)

/-- T-COVER's second premise at time f (bergdb 024-07; `T_cover` of
SIS/ReclaimTheorems.lean), by running: the index nodes reachable at f, a virtual
root aside, that have no data node below them at f, through live pointers to
lower levels as `reachFrom`. rl holds `reachList sp P f`. BergDB's delete
unlinks the nodes it empties, so there is none but an empty space root; since
024-07 no touch writes such a node again, so a cut could leave its version
behind. -/
def liveBelowFailures (sp : Spec BVal Nat) (P : Struct BVal) (f : Time) (rl : List NodeId) :
    List NodeId :=
  let lv := fun x => ((P.get? x).map (·.level)).getD 0
  let xs := rl.eraseDups.mergeSort (fun a b => decide (lv a ≤ lv b))
  let has : Std.HashMap NodeId Bool := xs.foldl (fun m x =>
    match P.get? x with
    | some n => m.insert x (n.isData || (sp.live (n.hist.upTo f)).any (fun y =>
        match P.get? y with
        | some ny => decide (ny.level < n.level) && m.getD y false
        | none => false))
    | none => m) {}
  xs.filter (fun x => isIndex P x && !(sp.virt && x == root) && !has.getD x false)

/-- The versions, as (node, record), that a lookup at time t may read (`ReadsAt` of
SIS/Reclaim.lean, bergdb item 001, WP R7) and that are before c: from the latest
version of every node of rl (the nodes reachable at t), through the pointers to
live children at t, with Rule R (newestSec gives a node's newest record in R(s), ...,
R(i)). lvRec gives a node's latest record, verAt the version of a node in a record;
fuel bounds the versions visited. -/
def readsBelow (sp : Spec BVal Nat) (t c : Nat) (rl : List NodeId) (lvRec : NodeId → Option Nat)
    (verAt : Nat → NodeId → Option (Version BVal)) (newestSec : NodeId → Option Nat)
    (fuel : Nat) : List (NodeId × Nat) :=
  let start := rl.eraseDups.filterMap (fun x => (lvRec x).map (fun r => (x, r)))
  let rec go : Nat → List (NodeId × Nat) → Std.HashSet (NodeId × Nat) → List (NodeId × Nat) →
      List (NodeId × Nat)
    | 0, _, _, below => below
    | _, [], _, below => below
    | fuel + 1, (x, r) :: rest, seen, below =>
      let below := if r < c then (x, r) :: below else below
      match verAt r x with
      | none => go fuel rest seen below
      | some v =>
        let kids := (sp.live (v.hist.upTo t)).filterMap (fun y =>
          match newestSec y with
          | some r' => some (y, r')
          | none => (v.ref? y).map (fun r' => (y, r')))
        let fresh := (kids.filter (fun p => !seen.contains p)).eraseDups
        go fuel (fresh ++ rest) (fresh.foldl (fun s p => s.insert p) seen) below
  go fuel start (Std.HashSet.ofList start) []

/-- As `readsBelow`, for the versions that a physical read in the running process may
follow (bergdb item 001, WP R4, the diagnostic C-CUT+; since WP R6 part of C-CUT,
`ReadsPhys`): through a pointer to a live child, every version of the child at or after
the record that the pointer names (before Rule R; every version if it names none),
since the running memory's Rule R is that of its last startup, and its canonical objects
and snapshots may be newer; but through a version that Rule A put back and that is still
in D ((x, r) ∈ D), only what a lookup reads (Rule R: newestSec, else the record named),
since the memory holds that node's canonical object. recsOf gives the records of a
node's versions so far. -/
def readsBelowPhys (sp : Spec BVal Nat) (t c : Nat) (rl : List NodeId) (lvRec : NodeId → Option Nat)
    (verAt : Nat → NodeId → Option (Version BVal)) (recsOf : NodeId → List Nat)
    (newestSec : NodeId → Option Nat) (D : Dirty) (fuel : Nat) : List (NodeId × Nat) :=
  let start := rl.eraseDups.filterMap (fun x => (lvRec x).map (fun r => (x, r)))
  let rec go : Nat → List (NodeId × Nat) → Std.HashSet (NodeId × Nat) → List (NodeId × Nat) →
      List (NodeId × Nat)
    | 0, _, _, below => below
    | _, [], _, below => below
    | fuel + 1, (x, r) :: rest, seen, below =>
      let below := if r < c then (x, r) :: below else below
      match verAt r x with
      | none => go fuel rest seen below
      | some v =>
        let putBack := D.contains (x, r)
        let kids := (sp.live (v.hist.upTo t)).flatMap (fun y =>
          if putBack then
            match newestSec y with
            | some r' => [(y, r')]
            | none => ((v.ref? y).map (fun r' => (y, r'))).toList
          else
          match v.ref? y with
          | some r' => ((recsOf y).filter (fun q => decide (r' ≤ q))).map (fun q => (y, q))
          | none => (recsOf y).map (fun q => (y, q)))
        let fresh := (kids.filter (fun p => !seen.contains p)).eraseDups
        go fuel (fresh ++ rest) (fresh.foldl (fun s p => s.insert p) seen) below
  go fuel start (Std.HashSet.ofList start) []

/-- C-CUT (bergdb item 001, WP R7): `CutOK c` of SIS/Reclaim.lean in the state after
T(i), by running, with the failures by name: c after the first available time f;
versions that reads from f to i may follow before c, latest ones (the node's latest
version) and others (through a pointer to an older version); nodes of D with a
latest version before c, or with a reference before c that does not name its
node's latest version; top(i) before c. below holds the versions before c that reads
may follow at every time from f to i: a lookup's (`readsBelow`) and, since WP R6,
a physical read's (`readsBelowPhys`; `ReadsPhys`); lvOf gives a node's latest
version, as its record and references. -/
def cutFailures (c f : Nat) (D : Dirty) (below : List (NodeId × Nat))
    (top : Option (NodeId × Nat)) (lvOf : NodeId → Option (Nat × List (NodeId × Nat))) :
    List (String × String) :=
  let order := if c ≤ f then [] else [("CUT-order", s!"cut at {c}, after the first available time {f}")]
  let old := (below.filter (fun p => (lvOf p.1).map (·.1) == some p.2)).map (·.1)
  let stale := below.filter (fun p => (lvOf p.1).map (·.1) != some p.2)
  let dOld := D.filterMap (fun e => match lvOf e.1 with
    | some (r, _) => if r < c then some e.1 else none
    | none => none)
  let dRef := D.filterMap (fun e => match lvOf e.1 with
    | some (r, refs) =>
      if r < c then none
      else if refs.all (fun q => decide (c ≤ q.2) || (lvOf q.1).map (·.1) == some q.2) then none
      else some e.1
    | none => none)
  let topOld := match top with
    | some (_, r) => if c ≤ r then [] else [("CUT-top", s!"top(i) names R({r}), before the cut")]
    | none => []
  order ++
    (if old.isEmpty then [] else
      [("CUT-reach", s!"reachable from {f} on, latest version before {c}: {showIds (old.eraseDups.mergeSort (· ≤ ·))}")]) ++
    (if stale.isEmpty then [] else
      [("CUT-stale", s!"read from {f} on through a pointer to an older version before {c}: {(stale.eraseDups.take 8)}")]) ++
    (if dOld.isEmpty then [] else [("CUT-D", s!"in D, latest version before {c}: {showIds dOld}")]) ++
    (if dRef.isEmpty then [] else
      [("CUT-Dref", s!"in D, a reference before {c} to a version that is not its node's latest: {showIds dRef}")]) ++
    topOld

/-- Reclaim's contract RC at a CUT line in TX i (bergdb 030-22, section 2.2;
030-23), the conditions that C-CUT's other checks do not name: RC1, the cut at
or after the earlier cuts (prev, the largest so far; c ≤ f is CUT-order, f the
record's fa CUT-fa); RC2, every data node reachable at f, the iteration's end
that Java makes the first available time, has its version at c or later
(dataOld, those that do not); RC4, Java's two waits: v, the first record whose
startup pos is at f or later, is before the startup pos of R(i) (sps, the
startup pos of R(0), ..., R(i)). RC3 is CUT-live. Also returns v. -/
def rcFailures (c f prev i : Nat) (sps : List Nat) (dataOld : List NodeId) :
    List (String × String) × Option Nat :=
  let v := sps.findIdx? (fun s => decide (f ≤ s))
  let spi := sps.getD i 0
  let r1 := if prev ≤ c then [] else [("RC1-order", s!"cut at {c}, before the earlier cut at {prev}")]
  let r2 := if dataOld.isEmpty then [] else
    [("RC2-rewrites", s!"data nodes reachable at {f} with a version before {c}: {showIds dataOld}")]
  let r4 := match v with
    | some v => if v < spi then [] else
        [("RC4-waits", s!"startup pos {spi} at or before R({v}), the first record whose startup pos reached {f}")]
    | none => [("RC4-waits", s!"no record up to R({i}) has its startup pos at {f} or later")]
  (r1 ++ r2 ++ r4, v)

/- RC4 fails when the startup pos has reached the iteration's end but not passed v,
the first record whose startup pos reached it; RC1 and RC2 by name. -/
#guard (rcFailures 1 3 0 4 [0, 1, 2, 3, 3] []).1.map (·.1) == ["RC4-waits"]
#guard (rcFailures 1 3 0 5 [0, 1, 2, 3, 3, 4] []).1.isEmpty
#guard (rcFailures 1 3 2 5 [0, 1, 2, 3, 3, 4] [7]).1.map (·.1) == ["RC1-order", "RC2-rewrites"]
#guard (rcFailures 1 9 0 2 [0, 1, 2] []).1.map (·.1) == ["RC4-waits"]

/-- The failures of `SpecOK` for the initial structure, with `VirtInit` for a
virtual root. -/
def initFailures (sp : Spec BVal Nat) : List String :=
  let P := sp.init
  let ids := P.map (·.1)
  let tops := P.filter (fun p => p.1 != root && decide (sp.topLevel ≤ p.2.level))
  (if ids.eraseDups.length == ids.length then [] else ["initDistinct"]) ++
  (if (P.get? root).isSome then [] else ["initRoot"]) ++
  (if P.all (fun p => p.2.hist.all (fun e => e.time == 0)) then [] else ["initTime"]) ++
  (if P.all (fun p => !p.2.isData || p.2.hist.all (fun e => (sp.ptrs e.val).isEmpty)) then []
   else ["initData"]) ++
  (if P.all (fun p => p.2.hist.all (fun e => (sp.ptrs e.val).all (fun y =>
      match P.get? y with
      | some m => decide (m.level < p.2.level)
      | none => false)))
   then [] else ["initLevels"]) ++
  (let rl := reachList sp P 0
   if P.all (fun p => rl.contains p.1) then [] else ["initReachable"]) ++
  (if !sp.virt then [] else
   (if P.all (fun p => sp.ptrs (sp.rootVal p.1) == [p.1]) then [] else ["R1-rootPtrs"]) ++
   (match P.get? root with
    | some n => if !n.isData && n.hist == tops.map (fun p => (⟨0, sp.rootVal p.1⟩ : Entry BVal)) then []
      else ["R2-initRootHist"]
    | none => ["R2-initRootHist"]) ++
   (if tops.length ≤ 1 && tops.all (fun p => !p.2.isData && !p.2.hist.isEmpty) then [] else ["initTop"]))

/-- D closed upward (T15's property): the index nodes reachable at i, not in D,
with a node of D reachable from them. -/
def closedFailures (sp : Spec BVal Nat) (P : Struct BVal) (i : Time) (D : Dirty) : List NodeId :=
  let rl := reachList sp P i
  rl.eraseDups.filter (fun x => isIndex P x && !inD D x && written sp x &&
    (match P.get? x with
     | some n => (reachFrom sp P i x n).any (fun y => inD D y)
     | none => false))

/-- A6', no adoption, the weaker form (`adoptAt` in SIS/Phys.lean, an assumption
of stage 2; bergdb 001-08, 5.5), first: the pairs (x, y) of a node x
reachable at i and a pointee y of x, live or dead, that is not a live child of x
at i, is an index node reachable at i, and is not reachable from x at i through
live pointers. Second, the pairs that fail only A6, the stronger form (bergdb
item 001, WP A4), which asks that y be a data node or not reachable: y is below
x. A6' allows them, and Java makes them where a transaction splits in place a
segment root that it made (bergdb 005-04). Before 005-04 the checker computed A6,
as a diagnostic. rl holds `reachList sp P i`, rlList the same as a list. P is
looked up through `nodeMap` (`nodeMap_get?`), and `reachFromG` through it is
`reachFrom` (`reachFromG_nodeMap`). -/
def adoptFailures (sp : Spec BVal Nat) (P : Struct BVal) (i : Time)
    (rl : Std.HashSet NodeId) (rlList : List NodeId) :
    List (NodeId × NodeId) × List (NodeId × NodeId) :=
  let m := SIS.Fast.nodeMap P
  let adopted := rlList.eraseDups.flatMap (fun x =>
    match m[x]? with
    | some n =>
      let lv := sp.live (n.hist.upTo i)
      ((pointees sp n.hist).filter (fun y => !lv.contains y && rl.contains y &&
        match m[y]? with
        | some ny => !ny.isData
        | none => false)).map (fun y => (x, y))
    | none => [])
  adopted.partition (fun p => match m[p.1]? with
    | some n => !(SIS.Fast.reachFromG sp (fun z => m[z]?) i p.1 n).contains p.2
    | none => true)

/-- TREE, one current parent (`treeAt` in SIS/Phys.lean, an assumption of stage 2;
bergdb item 001, WP A4; sis-model.md, section 11): the nodes reachable at i, the
root aside, that are the live child at i of no node or of more than one node
reachable at i. -/
def treeFailures (sp : Spec BVal Nat) (P : Struct BVal) (i : Time) (rlList : List NodeId) :
    List NodeId :=
  let xs := rlList.eraseDups
  let counts : Std.HashMap NodeId Nat := xs.foldl (fun m x =>
    match P.get? x with
    | some n => (sp.live (n.hist.upTo i)).eraseDups.foldl (fun m y => m.insert y (m.getD y 0 + 1)) m
    | none => m) {}
  xs.filter (fun y => y != root && counts.getD y 0 != 1)

/-- A-COPY (bergdb item 001, WPs E2 and E3; `CopyStep` in SIS/Phys.lean): the
pointers of transaction i's new entries, as (node, pointee), that name a node the
transaction does not create, not on the writer's paths, and not a pointee of a
node of the paths (written, or a live child of a virtual root at i - 1). The
paths are `pathOf`'s: the nodes reachable at i - 1 with a node below them,
themselves included, that the change gives entries, creates or touches (its
touch, since bergdb item 001, WP R3) or that is not reachable at i;
here computed lowest level first (checker-local). rlPrev holds
`reachList sp P (i - 1)`, rlNowSet the nodes reachable at i after the change. An
assumption of stage 2, as TREE and A6'. -/
def copyFailures (sp : Spec BVal Nat) (P : Struct BVal) (i : Time) (c : Changes BVal)
    (rlPrev : List NodeId) (rlNowSet : Std.HashSet NodeId) : List (NodeId × NodeId) :=
  let newIds : Std.HashSet NodeId := Std.HashSet.ofList (c.new.map (·.id))
  let addIds : Std.HashSet NodeId := Std.HashSet.ofList (c.adds.map (·.1))
  let touchIds : Std.HashSet NodeId := Std.HashSet.ofList c.touch
  let touched := fun z => newIds.contains z || addIds.contains z || touchIds.contains z ||
    !rlNowSet.contains z
  let lv := fun x => ((P.get? x).map (·.level)).getD 0
  let xs := rlPrev.eraseDups.mergeSort (fun a b => decide (lv a ≤ lv b))
  let below : Std.HashMap NodeId Bool := xs.foldl (fun m x =>
    match P.get? x with
    | some n => m.insert x (touched x || (sp.live (n.hist.upTo (i - 1))).any (fun y =>
        match P.get? y with
        | some ny => decide (ny.level < n.level) && m.getD y false
        | none => false))
    | none => m) {}
  let paths := xs.filter (fun x => below.getD x false)
  let allowed : Std.HashSet NodeId := paths.foldl (fun s z =>
    match P.get? z with
    | some nz =>
      let ys := if written sp z then pointees sp nz.hist else sp.live (nz.hist.upTo (i - 1))
      ys.foldl (fun s y => s.insert y) (s.insert z)
    | none => s.insert z) {}
  c.adds.flatMap (fun a => ((sp.ptrs a.2).filter (fun y => !newIds.contains y && !allowed.contains y)).map
    (fun y => (a.1, y)))

/-- INV-2: the dirty index nodes not in D (a virtual root aside). -/
def inv2Failures (sp : Spec BVal Nat) (S : Stream BVal Nat) (P : Struct BVal) (i : Time)
    (D : Dirty) : List NodeId :=
  (allIds P).filter (fun x => isIndex P x && !inD D x && written sp x && dirty sp S P i x)

/-! ## Lazy reading (bergdb item 001, WP L5) -/

/-- C-L: a first touch after the restart after T(i) follows the first-touch rule
of `SIS/Phys.lean` (`Mem.follow`): the record that the pointer names after Rule R
holds a version of the node, and is at least the newest in R(s), ..., R(i), the
section of that startup (`ruleRRef`; from a vpos, Rule R gives that version if
there is one); Java took the node table's canonical object, or a snapshot at
least as new, or the version named, which it cut back to the startup time
exactly when it is a key node version of R(s) on. S is the whole stream; s is
the startup pos. -/
def firstFailures (sp : Spec BVal Nat) (S : Stream BVal Nat) (i s : Nat) (f : TFirst) : List String :=
  let x := f.node
  let sec := newest (S.take (i + 1)) s x
  let nFails : List String := match f.named with
    | some n =>
      (match S.versionAt n x with
        | some _ => []
        | none => [s!"node {x}: R({n}) holds no version of it"]) ++
      (match sec with
        | some w0 => if w0.recNo ≤ n then [] else
            [s!"node {x}: Rule R gives R({w0.recNo}), the pointer R({n})"]
        | none => [])
    | none => match sec with
      | some w0 => [s!"node {x}: a vpos, but Rule R gives R({w0.recNo})"]
      | none => if f.kind == "version" then [s!"node {x}: a version read from a vpos"] else []
  let kFails : List String :=
    if f.kind == "canonical" then
      if f.took.isNone && !f.cut then [] else [s!"node {x}: a canonical object with a record or cut"]
    else if f.kind == "snapshot" then
      match f.took with
      | some r =>
        (if (S.versionAt r x).isSome then [] else [s!"node {x}: the snapshot's R({r}) holds no version"]) ++
        (match f.named with
          | some n => if n ≤ r then [] else [s!"node {x}: a snapshot of R({r}), older than R({n})"]
          | none => []) ++
        (if f.cut then [s!"node {x}: a snapshot reported as cut back"] else [])
      | none => [s!"node {x}: a snapshot without a record"]
    else if f.kind == "version" then
      match f.named, f.took with
      | some n, some r =>
        if r != n then [s!"node {x}: read R({r}) for a pointer to R({n})"] else
        match S.versionAt n x with
        | some w =>
          let rule := decide (s ≤ n) && isKeyLevel sp w.isData w.level
          if rule == f.cut then [] else
            [s!"node {x}: R({n}) read, cut back {f.cut}, the rule says {rule}"]
        | none => []
      | _, _ => [s!"node {x}: a version without a record"]
    else [s!"node {x}: unknown kind {f.kind}"]
  nFails ++ kFails

/-- C-P, INV-SLOT on Java's physical states (bergdb item 001, WP J4; the
INV-SLOT of the design before handles, `invSlotB` of SIS/EvictExample.lean,
proved in `TC_records`, until bergdb 005-62): the SLOT lines of T(i), run E's
resident canonical objects at the end of T(i). For an
object of a written node that is current at i (`now`) or in D: its slot for a
pointee not in D names the pointee's latest version (`lvRec`); its slot for a
pointee in D is a memory slot to the pointee's canonical object, or the
object's node is in D with an index at most the pointee's (it is written no
later); a dead slot (below the stream's first position, M33) is not checked.
And it has a slot for every pointee of its node's history in P. Also the
number of slots checked. -/
def slotFailures (sp : Spec BVal Nat) (P : Struct BVal) (now : Std.HashSet NodeId) (D : Dirty)
    (lvRec : NodeId → Option Nat) (ss : List TSlot) : List String × Nat :=
  let dOf : Std.HashMap NodeId Nat := D.foldl (fun m e => m.insert e.1 e.2) {}
  let checked := ss.filter (fun s => written sp s.node && (now.contains s.node || dOf.contains s.node))
  let showR := fun (o : Option Nat) => match o with
    | some r => s!"R({r})"
    | none => "a vpos"
  let bad := checked.filterMap (fun s =>
    if s.kind == "dead" then none
    else if !dOf.contains s.pointee then
      if s.ser == lvRec s.pointee then none
      else some s!"the slot of {s.node} for {s.pointee} names {showR s.ser}, its latest version is {showR (lvRec s.pointee)}"
    else if s.kind == "canon" then none
    else match dOf.get? s.node, dOf.get? s.pointee with
      | some a, some b => if a ≤ b then none
        else some s!"the slot of {s.node} (in D at {a}) for {s.pointee} (in D at {b}) is not a memory slot to its canonical object"
      | _, _ => some s!"the slot of {s.node} for {s.pointee}, in D, is not a memory slot to its canonical object, and {s.node} is not in D")
  let pairs : Std.HashSet (NodeId × NodeId) := checked.foldl (fun m s => m.insert (s.node, s.pointee)) {}
  let nodes := (checked.map (·.node)).eraseDups
  let missing := nodes.flatMap (fun x => match P.get? x with
    | some n => (pointees sp n.hist).filterMap (fun y =>
        if pairs.contains (x, y) then none else some s!"the object of {x} has no slot for {y}")
    | none => [s!"SLOT lines for {x}, which is not a node of P"])
  (bad ++ missing, (checked.filter (·.kind != "dead")).length)

/-! ## The handle state (bergdb item 009, step 4c) -/

/-- The elements of xs that occur more than once, each once. -/
def repeated (xs : List Nat) : List Nat :=
  (xs.foldl (fun (acc : Std.HashSet Nat × List Nat) x =>
    if !acc.1.contains x then (acc.1.insert x, acc.2)
    else if acc.2.contains x then acc else (acc.1, acc.2 ++ [x])) ({}, [])).2

/-- A record, or what none stands for (dflt). -/
def showRec (o : Option Nat) (dflt : String) : String :=
  match o with
  | some r => s!"R({r})"
  | none => dflt

/-- Run E's handle state at the end of T(i), the HTABLE, HANDLE, HOBJ and HPTR lines, as the
model's memory with handles (`HMem`, SIS/Handle.lean; the mapping α of
bergdb 009-05, section 2): the objects by their numbers, each with its pointers;
the handles by their numbers, a loading one as live (the model has no LOADING state); the
table. The trace gives an object's number of entries and their hash, not its history: a
canonical object gets its node's history in P (g), a snapshot the history of the version at
its position (verAt); C-H compares the numbers and the hashes. s is Rule R's startup pos.
Java has no object for a virtual root (TopDs stands for it, register R7), so the root's
address is 0, which no object has. -/
def toHMem (g : NodeId → Option (Node BVal)) (verAt : Nat → NodeId → Option (Version BVal))
    (s : Nat) (r : TRec) : HMem BVal :=
  let ptrsOf : Std.HashMap Nat (Array (NodeId × HPtr)) := r.hptrs.foldl (fun m q =>
    m.insert q.obj ((m.getD q.obj #[]).push (q.pointee, { ref := q.ref, handle := q.handle }))) {}
  { objs := r.hobjs.toList.map (fun o =>
      let hist := if o.canonical then ((g o.node).map (·.hist)).getD []
        else ((o.pos.bind (verAt · o.node)).map (·.hist)).getD []
      (o.num, ({ node := o.node, level := ((g o.node).map (·.level)).getD 0, isData := false,
                 hist := hist, canonical := o.canonical, pos := o.pos,
                 ptrs := (ptrsOf.getD o.num #[]).toList } : HObj BVal))),
    handles := r.handles.toList.map (fun h =>
      (h.num, ({ node := h.node, obj := h.obj, written := h.written, dead := h.state == "dead" } : Handle))),
    table := r.htable.toList, s := s, root := 0,
    nextObj := r.hobjs.foldl (fun n o => max n (o.num + 1)) 1,
    nextHandle := r.handles.foldl (fun n h => max n (h.num + 1)) 1 }

/-- What C-H met in run E's states (bergdb item 009, step 4c), besides failures: the pointers
it checked against the record rule, the objects whose histories it compared by their hashes;
and, as `pointCounts` of SIS/HandleExample.lean for the model's runs, how often Java's states
reach the cases that the model's runs found: snapshots; snapshots, after a restart, of nodes
with a version in the startup section (where `HRuleROK` says something); pointers whose handle
holds a snapshot (where `HFastOK` does); pointers checked whose record is their handle's
written position, newer than their reference after Rule R (choice 1 of SIS/Handle.lean), and
those of them whose reference is a vpos (open point 3 of 02, section 7); pointers whose handle
holds a snapshot and whose reference is older than the pointee's newest version in the
startup section (open point 1). -/
structure HCounts where
  checked : Nat := 0
  hashed : Nat := 0
  snaps : Nat := 0
  snapsSection : Nat := 0
  ptrSnaps : Nat := 0
  written : Nat := 0
  writtenVpos : Nat := 0
  olderSnap : Nat := 0

def HCounts.add (a b : HCounts) : HCounts :=
  { checked := a.checked + b.checked, hashed := a.hashed + b.hashed, snaps := a.snaps + b.snaps,
    snapsSection := a.snapsSection + b.snapsSection, ptrSnaps := a.ptrSnaps + b.ptrSnaps,
    written := a.written + b.written, writtenVpos := a.writtenVpos + b.writtenVpos,
    olderSnap := a.olderSnap + b.olderSnap }

/-- C-H, the model's invariants with handles on Java's states (bergdb item 009, step 4c): the
`Prop`s of SIS/HandleTheorems.lean, which `tc_handles` and `t2_handles` prove for the model,
after their `Bool` twins in SIS/HandleExample.lean, on run E's state at the end of T(i)
(`toHMem`), in the state after T(i): P (g gives a node of P), the nodes current at i (now), D,
the latest records (lvRec), the versions of the stream (verAt); S0 is the stream that the
state's startup read, for Rule R, and first the stream's first record. By invariant:

* `HTableOK`: the table's entries name live handles of their nodes, each with an object of its
  node; one entry per node; every live handle is the table's; a dead handle holds no object;
  every object is held by its node's live handle; a pointer's handle is of its pointee.
  Numbers do not repeat.
* `HCanOK`: a canonical object holds its node's history and is at its node's latest record;
  every node of D has a canonical object. The history is compared by its number of entries,
  and, if the trace gives it, by its hash (`historyHash`).
* `HSnapOK`: a snapshot is at a record that holds a version of its node, with the version's
  history: as many entries and, if the trace gives it, the same hash.
* `HSlotOK`, the record rule: a canonical object of a written node current at i or in D has a
  pointer for every pointee of its history that is an index node, and each such pointer gives
  the pointee's latest version (`HMem.refOf`, the model's record rule); one for a pointee in D
  holds the pointee's live handle with its canonical object, or the object's node is in D with
  an index at most the pointee's. A pointer whose handle holds no object that may serve it
  (`HObj.usable`) and whose reference, raised to the handle's written position, is before the
  stream's first record (reclaim's cut, M33) is not checked, as C-P's dead slots. Values have
  no handles in Java (register R1); C-P checks their slots.
* `HRuleROK`: a snapshot in a handle is at least as new as its node's newest version in the
  startup section of S0.
* `HLiveWrittenOK`: a live handle has no written position.
* `HWrittenOK`: a written position and a pointer's reference name records that hold versions
  of their nodes; and (`pointees`) a pointer's pointee is a pointee of its object's history.
* `HFastOK`: for a pointer whose reference is a position and whose handle holds an object, the
  fast path's test with the reference (`HObj.usable`) gives the slow path's answer.
* T-PIN (`TP_handles`): every live handle's object that is not pinned (`HMem.pinned`) may be
  evicted (`HMem.evictable`: it has been written).
* 02, 4.1 and 4.10: no handle is loading at a transaction's end, and a dead handle (deadBefore:
  those seen dead in earlier states) is never live again.

Returns the failures, as (invariant, message), and what C-H met (`HCounts`). -/
def handleFailures (sp : Spec BVal Nat) (g : NodeId → Option (Node BVal)) (now : Std.HashSet NodeId)
    (D : Dirty) (lvRec : NodeId → Option Nat) (verAt : Nat → NodeId → Option (Version BVal))
    (S0 : Stream BVal Nat) (first : Nat) (deadBefore : Std.HashSet Nat) (r : TRec) :
    List (String × String) × HCounts :=
  let s := lastSp S0
  let m := toHMem g verAt s r
  let hmap : Std.HashMap Nat THandle := r.handles.foldl (fun mm h => mm.insert h.num h) {}
  let omap : Std.HashMap Nat TObj := r.hobjs.foldl (fun mm o => mm.insert o.num o) {}
  let tmap : Std.HashMap NodeId Nat :=
    r.htable.foldl (fun mm e => if mm.contains e.1 then mm else mm.insert e.1 e.2) {}
  let dOf : Std.HashMap NodeId Nat := D.foldl (fun mm e => mm.insert e.1 e.2) {}
  let nodeOf := fun (a : Nat) => ((omap.get? a).map (·.node)).getD 0
  let showH := fun (n : Option Nat) => match n with
    | some n => s!"handle {n}"
    | none => "no handle"
  -- HTableOK
  let numbers := (repeated (r.handles.toList.map (·.num))).map (fun n => s!"handle {n} is listed twice") ++
    (repeated (r.hobjs.toList.map (·.num))).map (fun a => s!"object {a} is listed twice")
  let entries := r.htable.toList.filterMap (fun (y, n) =>
    match hmap.get? n with
    | none => some s!"the table's entry for {y} is handle {n}, which the state does not list"
    | some hd =>
      if hd.state == "dead" then some s!"the table's entry for {y} is handle {n}, which is dead"
      else if hd.node != y then some s!"the table's entry for {y} is handle {n}, of node {hd.node}"
      else match hd.obj with
        | none => some s!"the table's handle {n} of {y} holds no object"
        | some a => match omap.get? a with
          | none => some s!"the table's handle {n} of {y} holds object {a}, which the state does not list"
          | some o => if o.node == y then none
            else some s!"the table's handle {n} of {y} holds an object of {o.node}")
  let once := (repeated (r.htable.toList.map (·.1))).map (fun y => s!"the table has two entries for {y}")
  let live := r.handles.toList.filterMap (fun h =>
    if h.state == "dead" then
      if h.obj.isSome then some s!"dead handle {h.num} of {h.node} holds an object" else none
    else if tmap.get? h.node == some h.num then none
    else some s!"live handle {h.num} of {h.node} is not the table's ({showH (tmap.get? h.node)} is)")
  let held := r.hobjs.toList.filterMap (fun o =>
    match tmap.get? o.node with
    | some n => if ((hmap.get? n).bind (·.obj)) == some o.num then none
      else some s!"object {o.num} of {o.node} is not the object of its node's live handle {n}"
    | none => some s!"object {o.num} of {o.node}: the table has no handle for its node")
  let ptrHandles := r.hptrs.toList.filterMap (fun q =>
    if !omap.contains q.obj then some s!"a pointer of object {q.obj}, which the state does not list"
    else match q.handle with
    | none => none
    | some n => match hmap.get? n with
      | none => some s!"the pointer of {nodeOf q.obj} for {q.pointee} holds handle {n}, which the state does not list"
      | some hd => if hd.node == q.pointee then none
        else some s!"the pointer of {nodeOf q.obj} for {q.pointee} holds handle {n}, of node {hd.node}")
  let tableF := numbers ++ entries ++ once ++ live ++ held ++ ptrHandles
  -- HCanOK
  let canF := r.hobjs.toList.filterMap (fun o =>
    if !o.canonical then none else
    match g o.node with
    | none => some s!"canonical object {o.num} of {o.node}, which is not a node of P"
    | some n =>
      if n.isData then some s!"canonical object {o.num} of {o.node}, a data node"
      else if o.entries != n.hist.length then
        some s!"the canonical object of {o.node} has {o.entries} entries, its node in P {n.hist.length}"
      else if o.hash.any (· != (historyHash n.hist).toNat) then
        some s!"the canonical object of {o.node} (object {o.num}) has as many entries as its node in P, other ones: the history hash {o.hash.getD 0}, P's {(historyHash n.hist).toNat}"
      else if o.pos != lvRec o.node then
        some s!"the canonical object of {o.node} is at {showRec o.pos "no position"}, its latest version {showRec (lvRec o.node) "none"}"
      else none)
  let dCanF := D.filterMap (fun e =>
    if (m.canonicalOf e.1).isSome then none else some s!"{e.1} is in D and has no canonical object")
  -- HSnapOK
  let snapF := r.hobjs.toList.filterMap (fun o =>
    if o.canonical then none else
    match o.pos with
    | none => some s!"snapshot {o.num} of {o.node} has no position"
    | some p => match verAt p o.node with
      | none => some s!"the snapshot of {o.node} is at R({p}), which holds no version of it"
      | some w =>
        if w.hist.length != o.entries then
          some s!"the snapshot of {o.node} at R({p}) has {o.entries} entries, the version {w.hist.length}"
        else if o.hash.any (· != (historyHash w.hist).toNat) then
          some s!"the snapshot of {o.node} at R({p}) (object {o.num}) has as many entries as the version, other ones: the history hash {o.hash.getD 0}, the version's {(historyHash w.hist).toNat}"
        else none)
  -- HSlotOK, by the model's record rule
  let heldCanonical := fun (q : HPtr) => m.holdsCanonical q
  let writtenOf := fun (q : HPtr) => (q.handle.bind m.handle?).bind (·.written)
  -- C-P's dead slot: no object that may serve the pointer (Java's getPointerNode), and the
  -- record rule's reference before Rule R (Java's getSerializedRef) before the cut.
  let deadPtr := fun (q : HPtr) => !(((q.handle.bind m.objOf).bind m.obj?).any (·.usable q.ref)) &&
    match maxRef q.ref (writtenOf q) with
    | some p => decide (p < first)
    | none => false
  let slotRes := m.objs.map (fun p =>
    let o := p.2
    if !o.canonical || !written sp o.node || !(now.contains o.node || dOf.contains o.node) then ([], 0, 0, 0) else
    let ys := (pointees sp o.hist).filter (fun y => match g y with
      | some n => !n.isData
      | none => false)
    ys.foldl (fun (acc : List String × Nat × Nat × Nat) y =>
      let qs := (o.ptrs.filter (·.1 == y)).map (·.2)
      if qs.isEmpty then (acc.1 ++ [s!"the object of {o.node} has no pointer for {y}"], acc.2) else
      qs.foldl (fun (acc : List String × Nat × Nat × Nat) q =>
        if deadPtr q then acc else
        let got := m.refOf S0 D { o with ptrs := [(y, q)] } y
        -- Choice 1 and open point 3 (`pointCounts`'s columns 4 and 3).
        let fromWritten := !dOf.contains y && !heldCanonical q &&
          m.ptrRef S0 y q != ruleRRef S0 s y q.ref && m.ptrRef S0 y q == writtenOf q
        let w1 := if fromWritten then 1 else 0
        let w2 := if fromWritten && q.ref.isNone then 1 else 0
        let f1 := if got == lvRec y then [] else
          [s!"the pointer of {o.node} for {y} names {showRec q.ref "a vpos"} and holds {showH q.handle}: the record rule gives {showRec got "a vpos"}, its latest version is {showRec (lvRec y) "none"}"]
        let f2 := if !dOf.contains y then [] else
          let liveCanon := q.handle.isSome && q.handle == m.tableOf y && (m.canonicalOf y).isSome
          if liveCanon then [] else match dOf.get? o.node, dOf.get? y with
            | some a, some b => if a ≤ b then []
              else [s!"the pointer of {o.node} (in D at {a}) for {y} (in D at {b}) does not hold {y}'s live handle with its canonical object"]
            | _, _ => [s!"the pointer of {o.node} for {y}, in D, does not hold {y}'s live handle with its canonical object, and {o.node} is not in D"]
        (acc.1 ++ f1 ++ f2, acc.2.1 + 1, acc.2.2.1 + w1, acc.2.2.2 + w2)) acc) ([], 0, 0, 0))
  let slotF := slotRes.flatMap (·.1)
  -- HRuleROK
  let ruleF := r.handles.toList.filterMap (fun h =>
    match h.obj.bind omap.get? with
    | some o =>
      if o.canonical then none else
      match newest S0 s h.node, o.pos with
      | some w, some p => if w.recNo ≤ p then none
        else some s!"the snapshot of {h.node} at R({p}) in handle {h.num} is older than R({w.recNo}), its newest version in the startup section"
      | _, _ => none
    | none => none)
  -- HLiveWrittenOK
  let liveWrittenF := r.handles.toList.filterMap (fun h =>
    if h.state != "dead" && h.written.isSome then
      some s!"live handle {h.num} of {h.node} has a written position, {showRec h.written ""}"
    else none)
  -- HWrittenOK, and the pointees of the objects' pointers
  let writtenF := r.handles.toList.filterMap (fun h =>
    match h.written with
    | some w => if (verAt w h.node).isSome then none
      else some s!"handle {h.num} of {h.node} has the written position R({w}), which holds no version of it"
    | none => none) ++
    r.hptrs.toList.filterMap (fun q =>
      match q.ref with
      | some rr => if (verAt rr q.pointee).isSome then none
        else some s!"the pointer of {nodeOf q.obj} for {q.pointee} names R({rr}), which holds no version of it"
      | none => none)
  let pointeesF := m.objs.flatMap (fun p =>
    let ys := pointees sp p.2.hist
    (p.2.ptrs.filter (fun q => !ys.contains q.1)).map (fun q =>
      s!"object {p.1} of {p.2.node} has a pointer for {q.1}, which is not a pointee of its history"))
  -- HFastOK
  let fastF := m.objs.flatMap (fun p => p.2.ptrs.filterMap (fun (y, q) =>
    match q.ref, q.handle.bind m.handle? with
    | some _, some hd => match hd.obj.bind m.obj? with
      | some ob =>
        if ob.usable q.ref == ob.usable (maxRef (ruleRRef S0 s y q.ref) hd.written) then none
        else some s!"the pointer of {p.2.node} for {y}: the fast path's test {ob.usable q.ref}, the slow path's {!ob.usable q.ref}"
      | none => none
    | _, _ => none))
  -- T-PIN
  let pinF := r.handles.toList.filterMap (fun h =>
    match h.obj with
    | some a =>
      if h.state == "dead" || m.pinned D a || m.evictable D h.num then none
      else some s!"the object of {h.node} in handle {h.num} is not pinned and has not been written, so it may not be evicted"
    | none => none)
  -- 02, 4.1 and 4.10
  let stateF := r.handles.toList.filterMap (fun h =>
    if h.state == "loading" then some s!"handle {h.num} of {h.node} is loading at the end of the transaction"
    else if h.state == "live" && deadBefore.contains h.num then
      some s!"handle {h.num} of {h.node}, dead in an earlier state, is live"
    else none)
  -- The cases reached
  let snapObjs := m.objs.filter (!·.2.canonical)
  let snapPtrs := m.objs.flatMap (fun p => p.2.ptrs.filter (fun q => match (q.2.handle.bind m.objOf).bind m.obj? with
    | some ob => !ob.canonical
    | none => false))
  let counts : HCounts :=
    { checked := slotRes.foldl (fun n x => n + x.2.1) 0,
      hashed := (r.hobjs.filter (fun o => o.hash.isSome && if o.canonical then
          ((g o.node).map (·.hist.length)) == some o.entries
        else ((o.pos.bind (verAt · o.node)).map (·.hist.length)) == some o.entries)).size,
      snaps := snapObjs.length,
      snapsSection := if S0.length ≤ 1 then 0
        else (snapObjs.filter (fun p => (newest S0 s p.2.node).isSome)).length,
      ptrSnaps := snapPtrs.length,
      written := slotRes.foldl (fun n x => n + x.2.2.1) 0,
      writtenVpos := slotRes.foldl (fun n x => n + x.2.2.2) 0,
      olderSnap := (snapPtrs.filter (fun q => match q.2.ref, newest S0 s q.1 with
        | some r0, some w => decide (r0 < w.recNo)
        | _, _ => false)).length }
  let named := fun (name : String) (l : List String) => l.map (fun msg => (name, msg))
  (named "HTableOK" tableF ++ named "HCanOK" (canF ++ dCanF) ++ named "HSnapOK" snapF ++
    named "HSlotOK" slotF ++ named "HRuleROK" ruleF ++ named "HLiveWrittenOK" liveWrittenF ++
    named "HWrittenOK" writtenF ++ named "pointees" pointeesF ++ named "HFastOK" fastF ++
    named "T-PIN" pinF ++ named "state" stateF, counts)

/-- C-L4, a diagnostic (bergdb item 001, WP R8, change 3): a first touch follows
the Level 4 loader of the design before handles (`Mem.follow4`, SIS/Evict.lean
until bergdb 005-62): the node table's canonical object, or exactly the version
that the pointer names after Rule R, read and not entered in the node table;
never a snapshot from the table, which stage 1's rule
(C-L) allows. C-L checks the rest of the line. A cut back is C-L's alone: since
R8's change 2, Java cuts back only while it reconstructs the database at
startup, and the trace does not mark which first touches those are. -/
def loader4Failures (f : TFirst) : List String :=
  if f.kind == "snapshot" then
    match f.took with
    | some r => [s!"node {f.node}: a snapshot of R({r}) from the node table"]
    | none => [s!"node {f.node}: a snapshot from the node table"]
  else []

/-- The skip slots of a top node's version (M29; review-13-claude, 5.2): with
ordinal n (the node's level minus `topLevel`), slot j holds a skip pointer
exactly when bit j of n is set; its target is top n with the bits below j
cleared, minus one; and the time the slot caches is the target's creation
time. P is the structure after the record, lv the levels. -/
def topFailures (sp : Spec BVal Nat) (P : Struct BVal) (lv : List (NodeId × Nat × Bool))
    (w : TVer) : List String :=
  let level := ((lv.lookup w.node).map (·.1)).getD 0
  if w.isData || w.node == root || level < sp.topLevel then [] else
  let n := level - sp.topLevel
  let skips := w.hist.toList.filterMap (fun e => match e.val with
    | .skip j z => some (j, z)
    | _ => none)
  let height := if n == 0 then 0 else n.log2 + 1
  let popFails := (List.range (height + 1)).filterMap (fun j =>
    if n.testBit j == skips.any (·.1 == j) then none
    else some s!"top {w.node} (ordinal {n}): slot {j} {if n.testBit j then "empty" else "populated"}")
  let extra := skips.filterMap (fun (j, _) =>
    if j ≤ height then none else some s!"top {w.node}: slot {j} beyond its height")
  let targetFails := skips.filterMap (fun (j, z) =>
    let zl := ((lv.lookup z).map (·.1)).getD 0
    let want := n / 2 ^ j * 2 ^ j - 1
    if zl ≥ sp.topLevel && zl - sp.topLevel == want then none
    else some s!"top {w.node} (ordinal {n}): slot {j} points to {z}, not to ordinal {want}")
  let timeFails := skips.filterMap (fun (j, z) =>
    match w.skipt.find? (·.1 == j), (P.get? z).bind (·.hist.head?) with
    | some (_, t), some e => if t == e.time then none
        else some s!"top {w.node}: slot {j} caches time {t}, its target {z} was created at {e.time}"
    | none, _ => if w.skipt.isEmpty then none   -- a trace without SKIPT lines
        else some s!"top {w.node}: no SKIPT line for slot {j}"
    | some _, none => some s!"top {w.node}: slot {j}'s target {z} has no entries")
  popFails ++ extra ++ targetFails ++ timeFails

/-! ## Reclaim's steps (bergdb 030-27)

C-STEP: each step of reclaim against the model of the steps of bergdb 030-25 (`StepsOK`,
lean/contract's Contract/ReclaimSteps.lean; 027-13, section 1.4), on trace format 3 with
STEP lines (the exporter's steps=1). Reads with the tree model (SIS/Tree/Read.lean). -/

/-- The value node that a key names at time t, from segment root r: the tree model's
`getFrom` with the node's id in place of its value. -/
def valueNodeFrom (p : SIS.Tree.Params) (view : View BVal) (t : Time) :
    List Nat → NodeId → Option NodeId
  | [], _ => none
  | [cv], r => (SIS.Tree.getEq p view t cv p.fuel r).filter (fun y => (view y).any (·.isData))
  | cv :: rest, r =>
    match SIS.Tree.getEq p view t cv p.fuel r with
    | some y => if (SIS.Tree.knodeOf p view y).isSome then valueNodeFrom p view t rest y else none
    | none => none

/-- The live keys after transaction t, in key order, each with the value node it names
(bergdb 030-24's `idContents`) and its value's hash (bergdb 030-34): the tree model's scan
of every key, and `valueNodeFrom`. -/
def liveKeysAt (p : SIS.Tree.Params) (view : View BVal) (t : Time) :
    List (SIS.Tree.Key × Option NodeId × Nat) :=
  match SIS.Tree.rootAt view t with
  | none => []
  | some r => (SIS.Tree.scan p view t {} 1000000000).map (fun kv =>
      (kv.key, valueNodeFrom p view t kv.key r, kv.h))

/-- Key a at or before key b. -/
def keyLe (a b : SIS.Tree.Key) : Bool := !SIS.Tree.keyLt b a

def showKeyOpt : Option SIS.Tree.Key → String
  | some k => s!"{k}"
  | none => "-"

/-- C-STEP for the STEP line s of T(i), at the step's state (bergdb 030-27; 030-25,
section 5): prev is the STEP line before it in the trace; e the greatest key live after
T(t0), E (`endKey`); live the live keys after T(i - 1), the state that the step's scan
reads, with their value nodes and values (hashes); madeAt the record whose transaction made
a node; ops the record's OP lines (true: a noop); copies the keys of its `OP C` lines, the
copies (bergdb 031-06: a step rides in the record of a commit or of a part, beside the
action's operations, and its copies carry the copy mark); row the key of reclaim's row,
`reclaimRowKey` (another key only in the tests below). The failures by name, and the number
of old KVs that the step met (a value node made before c), each one the record must write:
- STEP-chain: L is the L' of the iteration's step before (none for its first, `StepsFrom`),
  with the same c; a new iteration comes after a step with eod, with a later t0;
- STEP-c: c ≤ t0 + 1, and the step after T(t0);
- STEP-range: L' is L (no KV met) or a key of the range, the live keys after L up to E;
  with eod the range's last key (the scan met all of it);
- STEP-puts: the record writes every KV of the range up to L' whose value node is old: a
  copy of it, or another operation at its key, the action's put or delete (Java leaves out
  a copy at a key that the action writes, bergdb 031-06) or reclaim's put of its row or
  table there; the action's operations are checked against the action as submitted by
  STEP-action (`actionFailures`);
- STEP-values (bergdb 030-34): each copy writes the value that the scan read, the key's
  value after T(i - 1);
- STEP-ops: the record's operations have distinct keys; it puts the row (not as a copy), at
  its key in the model, `reclaimRowKey` (bergdb 030-39, F1); and each copy is of an old KV
  met (bergdb 031-06: until then the step's record held its rewrites and its row only, and
  STEP-ops required no other operation and no delete). -/
def reclaimStepFailures (i : Nat) (s : SIS.Check.Tree.TStep) (prev : Option SIS.Check.Tree.TStep)
    (e : Option SIS.Tree.Key) (live : List (SIS.Tree.Key × Option NodeId × Nat))
    (madeAt : NodeId → Option Nat) (ops : List (SIS.Tree.Op × Bool)) (copies : List SIS.Tree.Key)
    (row : SIS.Tree.Key := reclaimRowKey) :
    List (String × String) × Nat :=
  let first := if s.last.isNone then [] else
    [s!"the iteration's first step with lastKey {showKeyOpt s.last}"]
  let chain : List String := match prev with
    | some q =>
      if q.t0 == s.t0 then
        (if q.c == s.c then [] else [s!"c {s.c}, the iteration's step before has c {q.c}"]) ++
        (if q.next == s.last then [] else
          [s!"lastKey before {showKeyOpt s.last}, the step before left {showKeyOpt q.next}"])
      else
        (if q.eod then [] else
          [s!"a new iteration (t0 {s.t0}) before a step with eod in the one of t0 {q.t0}"]) ++
        (if q.t0 < s.t0 then [] else [s!"t0 {s.t0}, not after the iteration before's, {q.t0}"]) ++
        first
    | none => first
  let cf := (if s.c ≤ s.t0 + 1 then [] else [s!"c {s.c} after t0 + 1 = {s.t0 + 1}"]) ++
    (if s.t0 < i then [] else [s!"t0 {s.t0}, not before the step"])
  let range := live.filter (fun (k, _) =>
    s.last.all (fun l => SIS.Tree.keyLt l k) && e.any (fun e => keyLe k e))
  let inRange := s.next == s.last || s.next.any (fun n => range.any (·.1 == n))
  let lastOk := !s.eod || (match range.getLast? with
    | some (k, _) => s.next == some k
    | none => s.next == s.last)
  let rf := (if inRange then [] else
      [s!"lastKey after {showKeyOpt s.next}: not L, nor a key of the range after {showKeyOpt s.last} up to E = {showKeyOpt e}"]) ++
    (if lastOk then [] else
      [s!"eod, but lastKey after {showKeyOpt s.next} is not the range's last key, {showKeyOpt (range.getLast?.map (·.1))}"])
  let met := if s.next == s.last then [] else match s.next with
    | some n => range.filter (fun (k, _) => keyLe k n)
    | none => []
  let noNode := met.filter (·.2.1.isNone)
  let old := met.filter (fun (_, y, _) => y.any (fun y => (madeAt y).all (· < s.c)))
  let keys := ops.map (·.1.key)
  -- Every old KV met is written by the record: a copy, the action's put or delete, or
  -- reclaim's row or table (bergdb 031-06).
  let missing := old.filter (fun (k, _) => !keys.contains k)
  let pf := (if noNode.isEmpty then [] else
      [s!"keys met without a value node: {(noNode.map (·.1)).take 4}"]) ++
    (if missing.isEmpty then [] else
      [s!"{missing.length} of {old.length} old KVs met not written by the record: {(missing.map (fun (k, y, _) => s!"{k} (node {y.getD 0})")).take 4}"])
  -- The copies, each with the value the scan read (bergdb 030-34).
  let copyPuts : List (SIS.Tree.Key × Nat) := ops.filterMap (fun (o, _) => match o with
    | .put k v => if copies.contains k then some (k, v) else none
    | .del _ => none)
  let readOf := fun (k : SIS.Tree.Key) => (old.find? (·.1 == k)).map (·.2.2)
  let vf := (copyPuts.filterMap (fun (k, v) => (readOf k).bind (fun h =>
    if h == v then none else some s!"the copy of the old KV {k} writes the value {v}, the scan read {h}"))).take 4
  let extra := copyPuts.filter (fun (k, _) => (readOf k).isNone)
  let rowPut := ops.any (fun (o, _) => match o with
    | .put k _ => k == row && !copies.contains k
    | .del _ => false)
  let of := (if keys.eraseDups.length == keys.length then [] else ["two operations of one key"]) ++
    (if rowPut then [] else [s!"no put of the row's key {row}"]) ++
    (if extra.isEmpty then [] else
      [s!"{extra.length} copies of no old KV met: {(extra.map (·.1)).take 4}"])
  (chain.map (fun m => ("STEP-chain", m)) ++ cf.map (fun m => ("STEP-c", m)) ++
   rf.map (fun m => ("STEP-range", m)) ++ pf.map (fun m => ("STEP-puts", m)) ++
   vf.map (fun m => ("STEP-values", m)) ++ of.map (fun m => ("STEP-ops", m)),
   old.length)

/-- STEP-action (bergdb 031-06), for every record of a trace with STEP lines: a record is
its action's operations and the maintenance it carries, one operation a key. ops are its OP
lines (true: a noop), copies the keys of its `OP C` lines, acts its ACT lines, the action as
submitted (of two at one key the last), step whether it has a TOUCH line. The operations
that are not copies are the action's, as submitted: each operation of the action is one of
them (a put with its value, a delete as `OP D` or, if it deleted nothing, `OP N`), and every
other is a put at a key of reclaim's reserved prefix (`reclaimReserved`: the row, the table),
which no action writes. The copies are in a step's record only, and at no key of the
action's (Java leaves such a copy out, Codex's E4). So the record's effect on the keys
outside reclaim's prefix is its action's and its copies', and the copies put again the
values the scan read (STEP-values). -/
def actionFailures (ops : List (SIS.Tree.Op × Bool)) (copies : List SIS.Tree.Key)
    (acts : List SIS.Tree.Op) (step : Bool) : List String :=
  let acts := acts.foldl (fun m a => m.filter (·.key != a.key) ++ [a]) []
  let isCopy := fun (o : SIS.Tree.Op) => match o with
    | .put k _ => copies.contains k
    | .del _ => false
  let own := (ops.filter (fun q => !isCopy q.1)).map (·.1)
  let missing := acts.filter (fun a => !own.contains a)
  let other := own.filter (fun o => !acts.any (·.key == o.key))
  let notReserved := other.filter (fun o => match o with
    | .put k _ => !reclaimReserved k
    | .del _ => true)
  let atAction := copies.filter (fun k => acts.any (·.key == k))
  (if missing.isEmpty then [] else
    [s!"{missing.length} operations of the action as submitted not in the record as given: {(missing.map reprStr).take 3}"]) ++
  (if notReserved.isEmpty then [] else
    [s!"{notReserved.length} operations neither the action's nor a put of reclaim's: {(notReserved.map reprStr).take 3}"]) ++
  (if atAction.isEmpty then [] else
    [s!"{atAction.length} copies at keys the action writes: {atAction.take 3}"]) ++
  (if step || copies.isEmpty then [] else [s!"{copies.length} copies in a record without a step"])

/- A step with keys [8] (old, node 5, value 1), [16] (new, node 7, value 1) and [24] (old,
node 9, value 3) live, E = [24], c = 3, the row at [99]: the first step meets [8] and [16]
and copies [8], with the row; a second step that left out [24], or a first step that claims
eod after [16], fails; so does a step that copies [8] with another value, copies [16] (a KV
met whose value is not old), or leaves out the row. -/
#guard (reclaimStepFailures 4 ⟨1, 2, none, some [16], false⟩ none (some [24])
  [([8], some 5, 1), ([16], some 7, 1), ([24], some 9, 3)] (fun y => if y == 7 then some 3 else some 1)
  [(.put [8] 1, false), (.put [99] 2, false)] [[8]] [99]) == ([], 1)
#guard ((reclaimStepFailures 6 ⟨1, 2, some [16], some [24], true⟩ (some ⟨1, 2, none, some [16], false⟩)
  (some [24]) [([8], some 5, 1), ([16], some 7, 1), ([24], some 9, 3)] (fun _ => some 1)
  [(.put [99] 2, false)] [] [99]).1.map (·.1)) == ["STEP-puts"]
#guard ((reclaimStepFailures 4 ⟨1, 2, none, some [16], true⟩ none (some [24])
  [([8], some 5, 1), ([16], some 7, 1), ([24], some 9, 3)] (fun _ => some 1)
  [(.put [8] 1, false), (.put [16] 1, false), (.put [99] 2, false)] [[8], [16]] [99]).1.map (·.1)) == ["STEP-range"]
#guard ((reclaimStepFailures 4 ⟨1, 3, some [8], some [16], false⟩ none (some [24])
  [([8], some 5, 1), ([16], some 7, 1)] (fun _ => some 1)
  [(.put [16] 1, false), (.put [16] 1, false), (.put [99] 2, false)] [[16]] [99]).1.map (·.1)) ==
  ["STEP-chain", "STEP-c", "STEP-ops"]
#guard ((reclaimStepFailures 4 ⟨1, 2, none, some [16], false⟩ none (some [24])
  [([8], some 5, 1), ([16], some 7, 1), ([24], some 9, 3)] (fun y => if y == 7 then some 3 else some 1)
  [(.put [8] 4, false), (.put [99] 2, false)] [[8]] [99]).1.map (·.1)) == ["STEP-values"]
#guard ((reclaimStepFailures 4 ⟨1, 2, none, some [16], false⟩ none (some [24])
  [([8], some 5, 1), ([16], some 7, 1), ([24], some 9, 3)] (fun y => if y == 7 then some 3 else some 1)
  [(.put [8] 1, false), (.put [16] 1, false), (.put [99] 2, false)] [[8], [16]] [99]).1.map (·.1)) == ["STEP-ops"]
#guard ((reclaimStepFailures 4 ⟨1, 2, none, some [16], false⟩ none (some [24])
  [([8], some 5, 1), ([16], some 7, 1), ([24], some 9, 3)] (fun y => if y == 7 then some 3 else some 1)
  [(.put [8] 1, false), (.put [98] 2, false)] [[8]] [99]).1.map (·.1)) == ["STEP-ops"]
-- The row at a key met whose value is old: the row's put writes another value there.
#guard (reclaimStepFailures 4 ⟨1, 2, none, some [16], false⟩ none (some [24])
  [([8], some 5, 1), ([16], some 7, 1), ([24], some 9, 3)] (fun y => if y == 7 then some 3 else some 1)
  [(.put [8] 6, false)] [] [8]) == ([], 1)
-- The row at its key in the model (bergdb 030-39, F1): a step that copies [8] and puts the
-- row passes; one that puts the row at another key, [99], fails (no row; the put of [99]
-- is neither the action's nor reclaim's: STEP-action); one that copies [8] with another
-- value and puts no row fails twice (STEP-values, STEP-ops).
#guard (reclaimStepFailures 4 ⟨1, 2, none, some [16], false⟩ none (some [24])
  [([8], some 5, 1), ([16], some 7, 1), ([24], some 9, 3)] (fun y => if y == 7 then some 3 else some 1)
  [(.put [8] 1, false), (.put reclaimRowKey 2, false)] [[8]]) == ([], 1)
#guard ((reclaimStepFailures 4 ⟨1, 2, none, some [16], false⟩ none (some [24])
  [([8], some 5, 1), ([16], some 7, 1), ([24], some 9, 3)] (fun y => if y == 7 then some 3 else some 1)
  [(.put [8] 1, false), (.put [99] 2, false)] [[8]]).1.map (·.1)) == ["STEP-ops"]
#guard ((reclaimStepFailures 4 ⟨1, 2, none, some [8], true⟩ none (some [8])
  [([8], some 5, 1)] (fun _ => some 1) [(.put [8] 999, false)] [[8]]).1.map (·.1)) ==
  ["STEP-values", "STEP-ops"]
/- bergdb 031-06, a step in a commit's record: the last step meets [8], [16] and [24]; the
action deletes [8] and puts [16]; the step copies [24], the other old KV met, and puts the
row. The record writes both old KVs met. Without the action's delete, [8] is not written
(STEP-puts); a copy of [8] beside the action's delete is two operations of one key. -/
#guard (reclaimStepFailures 6 ⟨1, 2, none, some [24], true⟩ none (some [24])
  [([8], some 5, 1), ([16], some 7, 1), ([24], some 9, 3)] (fun y => if y == 7 then some 3 else some 1)
  [(.del [8], false), (.put [16] 5, false), (.put [24] 3, false), (.put [99] 2, false)] [[24]] [99]) == ([], 2)
#guard ((reclaimStepFailures 6 ⟨1, 2, none, some [24], true⟩ none (some [24])
  [([8], some 5, 1), ([16], some 7, 1), ([24], some 9, 3)] (fun y => if y == 7 then some 3 else some 1)
  [(.put [16] 5, false), (.put [24] 3, false), (.put [99] 2, false)] [[24]] [99]).1.map (·.1)) == ["STEP-puts"]
#guard ((reclaimStepFailures 6 ⟨1, 2, none, some [24], true⟩ none (some [24])
  [([8], some 5, 1), ([16], some 7, 1), ([24], some 9, 3)] (fun y => if y == 7 then some 3 else some 1)
  [(.del [8], false), (.put [8] 1, false), (.put [24] 3, false), (.put [99] 2, false)] [[8], [24]] [99]).1.map (·.1)) ==
  ["STEP-ops"]

/- STEP-action (bergdb 031-06): that record against its action as submitted passes; so do a
delete that deleted nothing and a put of reclaim's at its reserved key. The action's put
with another value, an extra put of a user key, a copy left unmarked, an action's put
marked as a copy, or a copy in a record without a step, each fails. -/
#guard actionFailures [(.del [8], false), (.put [16] 5, false), (.put [24] 3, false),
  (.put reclaimRowKey 2, false)] [[24]] [.del [8], .put [16] 5] true == []
#guard actionFailures [(.del [40], true), (.put reclaimRowKey 2, false)] [] [.del [40]] false == []
#guard (actionFailures [(.del [8], false), (.put [16] 5, false), (.put [24] 3, false),
  (.put reclaimRowKey 2, false)] [[24]] [.del [8], .put [16] 6] true).length == 1
#guard (actionFailures [(.del [8], false), (.put [16] 5, false), (.put [24] 3, false), (.put [40] 1, false),
  (.put reclaimRowKey 2, false)] [[24]] [.del [8], .put [16] 5] true).length == 1
#guard (actionFailures [(.del [8], false), (.put [16] 5, false), (.put [24] 3, false),
  (.put reclaimRowKey 2, false)] [] [.del [8], .put [16] 5] true).length == 1
#guard (actionFailures [(.del [8], false), (.put [16] 5, false), (.put [24] 3, false),
  (.put reclaimRowKey 2, false)] [[16], [24]] [.del [8], .put [16] 5] true).length == 2
#guard (actionFailures [(.put [24] 3, false)] [[24]] [] false).length == 1

/-- STEP-resume (bergdb 030-31) for the RESUME line ρ after a restart after T(i): the row that
the start read from the stream is the iteration's row as its last step left it (030-25: a
restart resumes from the row the step committed). prev is the STEP line before it; e the
greatest key live after T(ρ.t0), E. If prev is of ρ's iteration: the same c, lastKey the
step's L', and the iteration not ended (no eod); else the iteration has had no step: lastKey
none, after an iteration ended by a step with eod, with a later t0, c ≤ t0 + 1 and t0 ≤ i.
And ρ's E is e. -/
def resumeFailures (i : Nat) (ρ : SIS.Check.Tree.TResume) (prev : Option SIS.Check.Tree.TStep)
    (e : Option SIS.Tree.Key) : List String :=
  let row : List String := match prev with
    | some q =>
      if q.t0 == ρ.t0 then
        (if q.c == ρ.c then [] else [s!"c {ρ.c}, the iteration's last step has c {q.c}"]) ++
        (if q.next == ρ.last then [] else
          [s!"lastKey {showKeyOpt ρ.last}, the iteration's last step left {showKeyOpt q.next}"]) ++
        (if q.eod then [s!"the iteration of t0 {ρ.t0} resumed, but its last step had eod"] else [])
      else
        (if ρ.last.isNone then [] else [s!"lastKey {showKeyOpt ρ.last} in an iteration without a step"]) ++
        (if q.eod then [] else [s!"a new iteration (t0 {ρ.t0}) resumed before a step with eod in the one of t0 {q.t0}"]) ++
        (if q.t0 < ρ.t0 then [] else [s!"t0 {ρ.t0}, not after the iteration before's, {q.t0}"])
    | none => if ρ.last.isNone then [] else [s!"lastKey {showKeyOpt ρ.last} in an iteration without a step"]
  let cf := (if ρ.c ≤ ρ.t0 + 1 then [] else [s!"c {ρ.c} after t0 + 1 = {ρ.t0 + 1}"]) ++
    (if ρ.t0 ≤ i then [] else [s!"t0 {ρ.t0} after the restart's record {i}"])
  let ef := if ρ.e == e then [] else
    [s!"endKey {showKeyOpt ρ.e}, but the greatest key live after T({ρ.t0}) is {showKeyOpt e}"]
  row ++ cf ++ ef

#guard resumeFailures 9 ⟨1, 2, some [16], some [24]⟩ (some ⟨1, 2, none, some [16], false⟩) (some [24]) == []
#guard (resumeFailures 9 ⟨1, 2, some [8], some [16]⟩ (some ⟨1, 2, none, some [16], true⟩) (some [24])).length == 3
#guard resumeFailures 9 ⟨5, 2, none, none⟩ (some ⟨1, 2, none, some [16], true⟩) none == []

/-- The counts of C-STEP, and its failures, each with its record. -/
structure StepReport where
  /-- STEP lines checked. -/
  steps : Nat := 0
  /-- Iterations (STEP lines' t0), and those whose last step has eod. -/
  iterations : Nat := 0
  ended : Nat := 0
  /-- The old KVs that the steps met, each checked written by the record. -/
  old : Nat := 0
  /-- Records checked against their actions as submitted (STEP-action; bergdb 031-06), the
  operations of those actions, and the copies. -/
  actions : Nat := 0
  actionOps : Nat := 0
  copies : Nat := 0
  /-- CUT lines checked against their iteration's last step. -/
  cuts : Nat := 0
  /-- Restarts (RESTART lines; bergdb 030-31), the crashes among them, the RESUME lines with
  an iteration in progress, and the iterations with a step before a restart and the next
  after it. -/
  restarts : Nat := 0
  crashes : Nat := 0
  resumed : Nat := 0
  spans : Nat := 0
  fails : List (Nat × List (String × String)) := []

/-- C-STEP over a trace with STEP lines (bergdb 030-27): `reclaimStepFailures` for every STEP line,
on the tree model's reads of P after its record; STEP-action (bergdb 031-06): every record
against its action as submitted (`actionFailures`); STEP-line: a STEP line in every step of
reclaim (a record with a TOUCH line) and in no other record, one a record; and CUT-steps:
at every CUT line `CUT c f`, the iteration with that c has its last step, with eod, at f,
the first available time (Java's fa := tEnd, the time of the step whose scan passed the
end). -/
def stepCheck (tr : Trace) (tt : SIS.Check.Tree.TTrace) : StepReport := Id.run do
  match tt.tree with
  | none => return { fails := [(0, [("STEP-form", "STEP lines without the TREE line of trace format 3")])] }
  | some (p, _) =>
    let recs := tr.recs
    let madeMap : Std.HashMap NodeId Nat := recs.foldl (fun m r =>
      r.new.foldl (fun m (x, _, _) => m.insert x r.idx) m) {}
    -- The record of each iteration's last STEP line, by t0; the STEP line of each record.
    let lastOf : Std.HashMap Nat Nat := tt.txs.foldl (fun m x =>
      x.steps.foldl (fun m s => m.insert s.t0 x.idx) m) {}
    let stepAt : Std.HashMap Nat SIS.Check.Tree.TStep := tt.txs.foldl (fun m x =>
      match x.steps[0]? with
      | some s => m.insert x.idx s
      | none => m) {}
    let mut rep : StepReport := {}
    if tt.txs.size != recs.size || !tt.bad.isEmpty then
      rep := { rep with fails := [(0, [("STEP-form",
        s!"{recs.size} transactions, {tt.txs.size} with tree lines; bad lines: {tt.bad.toList.take 4}")])] }
    let mut P : SIS.Check.Tree.PMap := {}
    let mut prev : Option SIS.Check.Tree.TStep := none
    let mut eOf : Option (Nat × Option SIS.Tree.Key) := none
    -- The row resumed by the last restart, until the next STEP line, and whether its
    -- iteration had a step before the restart (bergdb 030-31).
    let mut pending : Option (SIS.Check.Tree.TResume × Bool) := none
    for (r, x) in recs.toList.zip tt.txs.toList do
      let after := SIS.Check.Tree.applyRec p P r
      let mut f : List (String × String) := []
      if x.idx != r.idx then f := f ++ [("STEP-form", s!"the tree lines of TX {x.idx} at TX {r.idx}")]
      if x.steps.size > 1 then f := f ++ [("STEP-line", s!"{x.steps.size} STEP lines")]
      let isStep := !r.touch.isEmpty
      -- STEP-action (bergdb 031-06): every record of TX i, i > 0, against its action as
      -- submitted (its ACT lines).
      if r.idx > 0 then
        let af := actionFailures x.ops.toList x.copies.toList x.acts.toList isStep
        f := f ++ af.map (fun m => ("STEP-action", m))
        rep := { rep with actions := rep.actions + 1, copies := rep.copies + x.copies.size }
        rep := { rep with actionOps := rep.actionOps + x.acts.size }
      match x.steps[0]? with
      | none =>
        if isStep then f := f ++ [("STEP-line", "a step (a TOUCH line) without a STEP line")]
      | some s =>
        if !isStep then f := f ++ [("STEP-line", "a STEP line in a transaction without a TOUCH line")]
        -- STEP-resume (bergdb 030-31): the first step after a restart goes on from the row
        -- that the start resumed.
        match pending with
        | some (ρ, before) =>
          if s.t0 != ρ.t0 || s.c != ρ.c || s.last != ρ.last then
            f := f ++ [("STEP-resume", s!"the first step after the restart (t0 {s.t0}, c {s.c}, lastKey {showKeyOpt s.last}) is not of the row resumed (t0 {ρ.t0}, c {ρ.c}, lastKey {showKeyOpt ρ.last})")]
          else if before then rep := { rep with spans := rep.spans + 1 }
          pending := none
        | none => pure ()
        let view : View BVal := fun y => after[y]?
        let e := match eOf with
          | some (t0, e) => if t0 == s.t0 then e else ((liveKeysAt p view s.t0).getLast?.map (·.1))
          | none => (liveKeysAt p view s.t0).getLast?.map (·.1)
        eOf := some (s.t0, e)
        let (sf, n) := reclaimStepFailures r.idx s prev e (liveKeysAt p view (r.idx - 1))
          (fun y => madeMap[y]?) x.ops.toList x.copies.toList
        f := f ++ sf
        if prev.all (·.t0 != s.t0) then rep := { rep with iterations := rep.iterations + 1 }
        if s.eod && lastOf[s.t0]? == some r.idx then rep := { rep with ended := rep.ended + 1 }
        rep := { rep with steps := rep.steps + 1, old := rep.old + n }
        prev := some s
      -- RESTART and RESUME (bergdb 030-31): the iteration that the start read, at the state
      -- after T(i), against the STEP lines before.
      match x.restart, x.resume with
      | none, none => pure ()
      | none, some _ => f := f ++ [("STEP-resume", "a RESUME line without a restart")]
      | some _, none => f := f ++ [("STEP-resume", "a restart without a RESUME line")]
      | some k, some ρo =>
        rep := { rep with restarts := rep.restarts + 1, crashes := rep.crashes + (if k == "crash" then 1 else 0) }
        match ρo with
        | none =>
          if prev.any (!·.eod) then
            f := f ++ [("STEP-resume", s!"no iteration resumed, but the one of t0 {(prev.map (·.t0)).getD 0} has had no step with eod")]
          pending := none
        | some ρ =>
          let view : View BVal := fun y => after[y]?
          let e := (liveKeysAt p view ρ.t0).getLast?.map (·.1)
          f := f ++ (resumeFailures r.idx ρ prev e).map (fun m => ("STEP-resume", m))
          rep := { rep with resumed := rep.resumed + 1 }
          pending := some (ρ, prev.any (·.t0 == ρ.t0))
      match r.cut with
      | some (c, fa) =>
        rep := { rep with cuts := rep.cuts + 1 }
        match stepAt[fa]? with
        | none => f := f ++ [("CUT-steps", s!"CUT {c} {fa}: no STEP line at R({fa}), the first available time")]
        | some s =>
          if s.c != c then
            f := f ++ [("CUT-steps", s!"CUT {c} {fa}: the step at R({fa}) has c {s.c}")]
          if !s.eod then
            f := f ++ [("CUT-steps", s!"CUT {c} {fa}: the step at R({fa}) has no eod")]
          if lastOf[s.t0]? != some fa then
            f := f ++ [("CUT-steps", s!"CUT {c} {fa}: the iteration of t0 {s.t0} has a step after R({fa})")]
      | none => pure ()
      if !f.isEmpty then rep := { rep with fails := rep.fails ++ [(r.idx, f)] }
      P := after
    return rep

end SIS.Check
