/-
bergdb 026-25: pecmp. The tree checker's writer, lean/SIS/Tree/Pe.lean
(`SIS.Tree.Pe.peTx`, a copy of the proved writer on the model's P, with Java's
ids), against the proved writer itself, lean/contract/Contract/PeWriter.lean
(`Contract.PE.peTx`, bergdb 030-21), on Java's traces of format 3.

Usage: pecmp [--cap-h] TRACE...

--cap-h, the tool's own test: the proved writer runs with the cut size h, the
copy with M / 2, so the trees differ where a list is cut into three parts or
more, or into two where it holds more than M / 2 entries; the run must fail.

For each transaction of each trace: Java's structure before it (the trace's
records, as the tree checker reads them), given to both writers with the
transaction's operations (its noops too), the cut size M / 2 for both. Each
writer's tree after it is walked from its space root, and the two walks must
meet node for node: the same old nodes, and a node written on one side written
on the other, with the same level, kind and klongs, the ids of nodes made
renamed (a bijection, built by the walk); values made with the same hash; and
every node written by either reached by the walk. Prints a line a trace and
PECMP OK, or the first differences and PECMP FAILED.
-/
import Check.Tree
import Contract.PeWriter

open SIS SIS.Check SIS.Check.Tree SIS.Tree

namespace PeCmp

def toCK : SIS.Tree.Klong → Contract.Klong
  | .time t => .time t
  | .key c y => .key c y
  | .del b => .del b

/-- The contract's tree from Java's structure P (key nodes and values; the
space roots from the root's entries). -/
def ctree (p : Params) (P : PMap) : Contract.Tree :=
  let roots := match P[root]? with
    | some r => r.hist.filterMap (fun e => match e.val with
        | .top z => match P[z]? with
          | some nz => nz.hist.findSome? (fun f => match f.val with
              | .rootKey y => some (e.time, y)
              | _ => none)
          | none => none
        | _ => none)
    | none => []
  { obj := fun x => match P[x]? with
      | some nd =>
        if nd.isData then
          nd.hist.findSome? (fun e => match e.val with
            | .data h => some (Contract.Obj.val h)
            | _ => none)
        else if nd.level != 0 && nd.level ≤ p.keyMax then
          some (.key ⟨nd.level, p.heightOf nd.level == 0, (klongsOf nd.hist).map toCK⟩)
        else none
      | none => none,
    roots := roots }

def opOf : SIS.Tree.Op → Contract.Op
  | .put k h => .put k h
  | .del k => .del k

/-- A node of a side after the transaction: written, or as before. -/
inductive N where
  | key (level : Nat) (leaf : Bool) (ks : List Contract.Klong)
  | val (h : Nat)
  | none
  deriving BEq, Repr

/-- The contract's fresh ids start here, far above Java's. -/
def cBase : Nat := 2 ^ 50

structure St where
  map : Std.HashMap Nat Nat := {}      -- SIS id of a node made ↦ contract id
  seenS : Std.HashSet Nat := {}
  seenC : Std.HashSet Nat := {}
  stack : List (Nat × Nat) := []
  errs : List String := []

/-- The walk of the two trees after the transaction from their space roots. -/
def compare (newS : Nat → Bool) (getS getC : Nat → N) (wsS wsC : Std.HashSet Nat)
    (rS rC : Nat) : List String := Id.run do
  let mut st : St := { stack := [(rS, rC)] }
  let mut fuel := 10000000
  while !st.stack.isEmpty && fuel > 0 && st.errs.length < 5 do
    fuel := fuel - 1
    match st.stack with
    | [] => pure ()
    | (s, c) :: rest =>
      st := { st with stack := rest }
      if st.seenS.contains s then
        if st.map[s]? != some c && !(!newS s && s == c) then
          st := { st with errs := st.errs ++ [s!"node {s} met again with {c}"] }
        continue
      st := { st with seenS := st.seenS.insert s, seenC := st.seenC.insert c }
      let sNew := newS s
      let cNew := decide (cBase ≤ c)
      if sNew != cNew then
        st := { st with errs := st.errs ++ [s!"node {s} (new {sNew}) against {c} (new {cNew})"] }
        continue
      if sNew then
        st := { st with map := st.map.insert s c }
      else if s != c then
        st := { st with errs := st.errs ++ [s!"old node {s} against old node {c}"] }
        continue
      if wsS.contains s != wsC.contains c then
        st := { st with errs := st.errs ++ [s!"node {s}: written by one writer only ({wsS.contains s}, {wsC.contains c})"] }
        continue
      match getS s, getC c with
      | .val h1, .val h2 =>
        if h1 != h2 then st := { st with errs := st.errs ++ [s!"value {s}: hash {h1} against {h2}"] }
      | .key l1 f1 k1, .key l2 f2 k2 =>
        if l1 != l2 || f1 != f2 || k1.length != k2.length then
          st := { st with errs := st.errs ++ [s!"key node {s}/{c}: level {l1}/{l2}, leaf {f1}/{f2}, {k1.length}/{k2.length} klongs"] }
          continue
        -- below a node: its live children (a node written below an old one is reached
        -- through live klongs; an old node's dead children are history)
        let liveS := (Contract.live k1).map (·.2)
        for (a, b) in k1.zip k2 do
          match a, b with
          | .key ca ya, .key cb yb =>
            if ca != cb then
              st := { st with errs := st.errs ++ [s!"key node {s}/{c}: compare value {ca} against {cb}"] }
            else if newS ya || liveS.contains ya then
              st := { st with stack := (ya, yb) :: st.stack }
            else if ya != yb then
              st := { st with errs := st.errs ++ [s!"key node {s}/{c}: a dead klong to {ya} against {yb}"] }
          | .time ta, .time tb =>
            if ta != tb then st := { st with errs := st.errs ++ [s!"key node {s}/{c}: time {ta} against {tb}"] }
          | .del ba, .del bb =>
            if ba.eraseDups.mergeSort (· ≤ ·) != bb.eraseDups.mergeSort (· ≤ ·) then
              st := { st with errs := st.errs ++ [s!"key node {s}/{c}: bitmap {ba} against {bb}"] }
          | _, _ => st := { st with errs := st.errs ++ [s!"key node {s}/{c}: klongs of other kinds"] }
      | a, b => st := { st with errs := st.errs ++ [s!"node {s}/{c}: {repr a} against {repr b}"] }
  -- every node written is reached
  for x in wsS.toList do
    if !st.seenS.contains x then st := { st with errs := st.errs ++ [s!"SIS wrote node {x}, not reached"] }
  for x in wsC.toList do
    if !st.seenC.contains x then st := { st with errs := st.errs ++ [s!"the contract's writer wrote node {x}, not reached"] }
  return st.errs

/-- Checks one transaction: the differences, or none. -/
def checkTx (capH : Bool) (p : Params) (P : PMap) (i : Nat) (base : Nat) (ops : List SIS.Tree.Op) :
    Except String (List String) := do
  let view : View BVal := fun y => P[y]?
  let z ← match lastTop view with
    | some z => pure z
    | none => throw "no top node"
  let top ← match topOf p (rootless view) z with
    | .ok t => pure t
    | .error e => throw e
  let cfS := SIS.Tree.Pe.Cfg.of p
  let s := SIS.Tree.Pe.lookOf p view
  -- Contract.PE.Cfg: M, G, H, m, c, h, theta, cap.
  let cfC : Contract.PE.Cfg := ⟨p.M, p.G, p.H, p.mergeBelow, p.mergeMax, p.splitAbove, p.theta,
    if capH then p.splitAbove else SIS.Tree.Pe.cutSize p.M⟩
  let ct := ctree p P
  let tp : Contract.Top := [(z, ⟨top.time, top.rootKey, []⟩)]
  let oS := SIS.Tree.Pe.peTx cfS i s top.rootKey base ops
  let oC := Contract.PE.peTx cfC i ct tp cBase (ops.map opOf)
  match oS, oC with
  | none, none => return []
  | none, some _ => return [s!"T({i}): the copy refused, the proved writer did not"]
  | some _, none => return [s!"T({i}): the proved writer refused, the copy did not"]
  | some os, some oc =>
    let wsS : Std.HashMap Nat SIS.Tree.Pe.Obj := os.ws.foldl (fun m (x, o) => if m.contains x then m else m.insert x o) {}
    let wsC : Std.HashMap Nat Contract.Obj := oc.ws.foldl (fun m (x, o) => if m.contains x then m else m.insert x o) {}
    let dupS := os.ws.length - wsS.size
    let dupC := oc.ws.length - wsC.size
    let getS : Nat → N := fun x => match wsS[x]? with
      | some (.key n) => .key n.level n.leaf (n.ks.map toCK)
      | some (.val h) => .val h
      | none => match s x with
        | some n => .key n.level n.leaf (n.ks.map toCK)
        | none => match P[x]? with
          | some nd => if nd.isData then
              (match nd.hist.findSome? (fun e => match e.val with | .data h => some h | _ => none) with
               | some h => .val h | none => .none) else .none
          | none => .none
    let getC : Nat → N := fun x => match wsC[x]? with
      | some (.key n) => .key n.level n.leaf n.ks
      | some (.val h) => .val h
      | none => match ct.obj x with
        | some (.key n) => .key n.level n.leaf n.ks
        | some (.val h) => .val h
        | none => .none
    let rS := os.root.getD top.rootKey
    let rC := (oc.roots.getLast?.map (·.2)).getD top.rootKey
    let keysS : Std.HashSet Nat := Std.HashSet.ofList (wsS.toList.map (·.1))
    let keysC : Std.HashSet Nat := Std.HashSet.ofList (wsC.toList.map (·.1))
    let errs := compare (fun x => base ≤ x) getS getC keysS keysC rS rC
    let errs := (if dupS + dupC > 0 then [s!"nodes written twice: {dupS}, {dupC}"] else []) ++ errs
    return errs.map (fun e => s!"T({i}): {e}")

def runTrace (capH : Bool) (file : String) : IO (Nat × Nat × List String) := do
  let text ← IO.FS.readFile file
  let tr := parseTrace text
  let tt := parseTree text
  match tt.tree with
  | none => return (0, 0, ["no TREE line"])
  | some (p, _) =>
    let mut P : PMap := {}
    let mut n := 0
    let mut bad := 0
    let mut errs : List String := []
    for (r, x) in tr.recs.toList.zip tt.txs.toList do
      if r.idx != 0 then
        match x.base with
        | some base =>
          n := n + 1
          match checkTx capH p P r.idx base (x.ops.toList.map (·.1)) with
          | .ok [] => pure ()
          | .ok es =>
            bad := bad + 1
            if errs.length < 6 then errs := errs ++ es.take 3
          | .error e =>
            bad := bad + 1
            if errs.length < 6 then errs := errs ++ [s!"T({r.idx}): {e}"]
        | none => pure ()
      P := applyRec p P r
    return (n, bad, errs)

end PeCmp

def main (args : List String) : IO UInt32 := do
  let mut total := 0
  let mut bad := 0
  let mut traces := 0
  let capH := args.contains "--cap-h"
  for f in args.filter (· != "--cap-h") do
    let (n, b, errs) ← PeCmp.runTrace capH f
    traces := traces + 1
    total := total + n
    bad := bad + b
    IO.println s!"{f}: {n} transactions, {b} differ"
    for e in errs do
      IO.println s!"  {e}"
  IO.println s!"total: {traces} traces, {total} transactions, {bad} differ"
  if bad == 0 && traces > 0 then
    IO.println "PECMP OK"
    return 0
  else
    IO.println "PECMP FAILED"
    return 1
