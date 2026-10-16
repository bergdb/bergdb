/-
The trace checker: the checks (docs/level2-alignment.md, 8.5 and 9).

Not part of the trusted part. The checker runs the model's own `init` and
`step` (SIS/Algorithm.lean) with the switches of `Opts`: marking in step 3
(`Algo.mark`), BergDB's still-dirty test in step 7 (`javaTest`), and the
virtual root of option (a) (`Spec.virt`). Written 2026-10-15 for F1-008-11,
WP C2; since 2026-10-16 (WP E3) without checker-local definitions.
-/
import Check.Trace
import Check.Fast
import SIS.Phys
import Check.R4
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

/-- A6, no adoption (bergdb item 001, WP A4; its plan, 8.5): the index nodes
reachable at i that a node reachable at i points to, live or dead, without
being its live child at i. Option K needs none: a pointer that stops being live
in a node that stays current points to a node that stops being current, or to a
data node. A diagnostic, not yet an assumption (WP E1 decides). rl holds
`reachList sp P i`, rlList the same as a list. -/
def adoptionFailures (sp : Spec BVal Nat) (P : Struct BVal) (i : Time)
    (rl : Std.HashSet NodeId) (rlList : List NodeId) : List NodeId :=
  rlList.eraseDups.flatMap (fun x =>
    match P.get? x with
    | some n =>
      let lv := sp.live (n.hist.upTo i)
      (pointees sp n.hist).filter (fun y => !lv.contains y && rl.contains y && isIndex P y)
    | none => [])

/-- TREE, one current parent (bergdb item 001, WP A4; sis-model.md, section 11):
the nodes reachable at i, the root aside, that are the live child at i of no
node or of more than one node reachable at i. A diagnostic, as A6. -/
def treeFailures (sp : Spec BVal Nat) (P : Struct BVal) (i : Time) (rlList : List NodeId) :
    List NodeId :=
  let xs := rlList.eraseDups
  let counts : Std.HashMap NodeId Nat := xs.foldl (fun m x =>
    match P.get? x with
    | some n => (sp.live (n.hist.upTo i)).eraseDups.foldl (fun m y => m.insert y (m.getD y 0 + 1)) m
    | none => m) {}
  xs.filter (fun y => y != root && counts.getD y 0 != 1)

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

end SIS.Check
