/-
The trace checker: the checks (docs/level2-alignment.md, 8.5 and 9).

Not part of the trusted part. The checker runs the model's own `init` and
`step` (SIS/Algorithm.lean) with the switches of `Opts`: marking in step 3
(`Algo.mark`), BergDB's still-dirty test in step 7 (`javaTest`), and the
virtual root of option (a) (`Spec.virt`). Written 2026-10-15 for F1-008-11,
WP C2; since 2026-10-16 (WP E3) without checker-local definitions.
-/
import Check.Trace
import Std.Data.HashSet

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
pos that Java chose for transaction j. -/
def algoOf (sp : Spec BVal Nat) (o : Opts) (pol : Nat → Nat) : Algo BVal Nat :=
  { policy := fun _ _ j _ => pol j, stillDirty := if o.java7 then javaTest sp else exactTest sp,
    mark := o.mark }

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
  sp ++ top ++ gdDup ++ gd ++ vset ++ vdiff

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
  let r4 := tops.flatMap (fun nn => match P'.get? nn.id with
    | some n =>
      let cl := topClosure sp P' nn.id n
      (P.filter (fun p => topNode p && !cl.contains p.1)).map (·.1)
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

/-- INV-2: the dirty index nodes not in D (a virtual root aside). -/
def inv2Failures (sp : Spec BVal Nat) (S : Stream BVal Nat) (P : Struct BVal) (i : Time)
    (D : Dirty) : List NodeId :=
  (allIds P).filter (fun x => isIndex P x && !inD D x && written sp x && dirty sp S P i x)

end SIS.Check
