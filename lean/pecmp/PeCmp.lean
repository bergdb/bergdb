/-
bergdb 030-28: pecmp, the tested writer against the proved writer, a routine
step of java/stress/level2.sh. The tree checker (treecheck, Check/Tree.lean,
Check/TreeRun.lean) compares Java with lean/SIS/Tree/Pe.lean (`SIS.Tree.Pe`, the
copy); 030-21 proves lean/contract/Contract/PeWriter.lean (`Contract.PE`, the
proved writer). This tool runs both on Java's traces and fails if they make
anything different, so that Java, the copy and the proved writer cannot drift
apart without a level script failing. First made by 026-25 (its pecmp, which
compared the trees from the space roots); 030-28 added the comparison of the
writes in their order, of the ids' order, and of the top node.

Usage: pecmp [--cap-h | --top-fault] TRACE...

For each transaction of each trace (format 3): Java's structure P before it, as
the tree checker reads it, given to both writers with the transaction's
operations (its noops too), the cut size M / 2 for both (Java's `Dag.cutSize`):
the copy as the tree checker runs it (`SIS.Tree.Pe.runOps`, and its `peTx` for
the writes), the proved writer with the contract's tree (the key nodes and
values of P, the space roots of the root's entries) and the whole top (every
top node of P in the order of the root's entries, with the cached times of
its skip pointers). Then:

1. Both refuse, or neither.
2. The writes: the same number, and the k-th write of each is the same old
   node, or a node made by both; a node made gets an id from each writer, and
   the ids of the nodes made correspond one to one (the copy gives Java's ids,
   two on, and an id to a delete node, which it does not write; the proved
   writer one on), in the same order; each write is the same object: a value
   with the same hash, a key node with the same level, kind and klongs, a
   child renamed, a bitmap as a set of bits (the copy keeps bits sorted
   without repeats, as Java's `long`; the proved writer's list may repeat
   one).
3. The trees after it, walked from their space roots: the same old nodes,
   the nodes made met in the same places, every node written reached.
4. The top: the copy makes a new top node if and only if the proved writer
   does; then the same time, root, ordinal (the proved writer's is the top's
   length, the copy's the super root's ordinal and one), the same skip
   pointers by index and target, and the proved writer's cached time of each
   is its target's time in P; the new top node's id is a node made after
   every other.

Prints a line a trace and PECMP OK, or the first differences and PECMP
FAILED. Its own tests, each must fail on a trace of node size 30 or more:
--cap-h gives the proved writer the cut size h instead of M / 2 (the trees
differ where a list is cut into three or more parts, or into two of more
than M / 2 entries); --top-fault gives it a top with one more top node at its
start, so that each new top node's ordinal is one too high.
-/
import Check.Tree
import Contract.PeWriter

open SIS SIS.Check SIS.Check.Tree SIS.Tree

namespace PeCmp

def toCK : SIS.Tree.Klong → Contract.Klong
  | .time t => .time t
  | .key c y => .key c y
  | .del b => .del b

/-- The root time of top node z of P: the time of its root pointer. -/
def topTime (P : PMap) (z : NodeId) : Option Nat :=
  (P[z]?).bind (fun (nd : Node BVal) => nd.hist.findSome? (fun (e : Entry BVal) => match e.val with
    | .rootKey _ => some e.time
    | _ => none))

/-- The contract's top from Java's structure P: every top node, in the order
of the root's entries, with its time, its root and its skip pointers, each with
its target's time (`TopNode.skips`' cached time). -/
def ctop (P : PMap) : Except String Contract.Top := do
  let zs := match P[root]? with
    | some r => r.hist.filterMap (fun (e : Entry BVal) => match e.val with
        | .top z => some z
        | _ => none)
    | none => []
  zs.mapM (fun z => do
    let nd ← match P[z]? with
      | some nd => pure nd
      | none => throw s!"top node {z} is not in P"
    let (t, y) ← match nd.hist.findSome? (fun (e : Entry BVal) => match e.val with
        | .rootKey y => some (e.time, y)
        | _ => none) with
      | some q => pure q
      | none => throw s!"top node {z} has no root pointer"
    let skips ← (nd.hist.filterMap (fun (e : Entry BVal) => match e.val with
        | .skip j s => some (j, s)
        | _ => none)).mapM (fun (j, s) => match topTime P s with
          | some ts => pure (j, s, ts)
          | none => throw s!"top node {z}: skip pointer {j} to {s}, no top node")
    pure (z, (⟨t, y, skips⟩ : Contract.TopNode)))

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

/-- A bitmap as a set: its bits sorted, without repeats. -/
def bitSet (b : List Nat) : List Nat := b.eraseDups.mergeSort (· ≤ ·)

structure St where
  map : Std.HashMap Nat Nat := {}      -- SIS id of a node made ↦ contract id
  seenS : Std.HashSet Nat := {}
  seenC : Std.HashSet Nat := {}
  stack : List (Nat × Nat) := []
  errs : List String := []

/-- The walk of the two trees after the transaction from their space roots. -/
def compare (newS : Nat → Bool) (getS getC : Nat → N) (wsS wsC : Std.HashSet Nat)
    (rS rC : Nat) : List String × Std.HashMap Nat Nat := Id.run do
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
            if bitSet ba != bitSet bb then
              st := { st with errs := st.errs ++ [s!"key node {s}/{c}: bitmap {ba} against {bb}"] }
          | _, _ => st := { st with errs := st.errs ++ [s!"key node {s}/{c}: klongs of other kinds"] }
      | a, b => st := { st with errs := st.errs ++ [s!"node {s}/{c}: {repr a} against {repr b}"] }
  -- every node written is reached
  for x in wsS.toList do
    if !st.seenS.contains x then st := { st with errs := st.errs ++ [s!"SIS wrote node {x}, not reached"] }
  for x in wsC.toList do
    if !st.seenC.contains x then st := { st with errs := st.errs ++ [s!"the contract's writer wrote node {x}, not reached"] }
  return (st.errs, st.map)

/-- A klong of the copy against one of the proved writer, the ids of nodes
made renamed by `ren` (the copy's id ↦ the proved writer's). -/
def sameKlong (ren : Nat → Nat) : Contract.Klong → Contract.Klong → Bool
  | .key ca ya, .key cb yb => ca == cb && ren ya == yb
  | .time ta, .time tb => ta == tb
  | .del ba, .del bb => bitSet ba == bitSet bb
  | _, _ => false

/-- The writes of the two writers in their order (2. in the header): the
differences, and the correspondence of the ids of the nodes made. -/
def compareWrites (newS : Nat → Bool) (wsS : List (Nat × SIS.Tree.Pe.Obj))
    (wsC : List (Nat × Contract.Obj)) : List String × Std.HashMap Nat Nat := Id.run do
  let mut errs : List String := []
  let mut ren : Std.HashMap Nat Nat := {}
  if wsS.length != wsC.length then
    errs := errs ++ [s!"{wsS.length} writes against {wsC.length}"]
  -- The ids of the nodes made, pair by pair, in the order of the writes.
  for ((s, _), (c, _)) in wsS.zip wsC do
    let sNew := newS s
    let cNew := decide (cBase ≤ c)
    if sNew != cNew then
      errs := errs ++ [s!"a write of node {s} (new {sNew}) against node {c} (new {cNew})"]
    else if sNew then
      match ren[s]? with
      | some c' => if c' != c then errs := errs ++ [s!"node {s} written as {c'} and as {c}"]
      | none => ren := ren.insert s c
    else if s != c then
      errs := errs ++ [s!"a write of old node {s} against old node {c}"]
  -- The same order of fresh ids: the correspondence is increasing.
  let pairs := ren.toList.mergeSort (fun a b => decide (a.1 ≤ b.1))
  for (a, b) in pairs.zip (pairs.drop 1) do
    if b.2 ≤ a.2 then
      errs := errs ++ [s!"the ids of the nodes made in another order: {a.1} ↦ {a.2}, {b.1} ↦ {b.2}"]
  let rn : Nat → Nat := fun y => if newS y then ren.getD y y else y
  for ((s, oS), (c, oC)) in wsS.zip wsC do
    match oS, oC with
    | .val h1, .val h2 =>
      if h1 != h2 then errs := errs ++ [s!"write {s}/{c}: value hash {h1} against {h2}"]
    | .key n1, .key n2 =>
      let k1 := n1.ks.map toCK
      if n1.level != n2.level || n1.leaf != n2.leaf || k1.length != n2.ks.length
          || !(k1.zip n2.ks).all (fun (a, b) => sameKlong rn a b) then
        errs := errs ++ [s!"write {s}/{c}: key node level {n1.level}/{n2.level}, leaf {n1.leaf}/{n2.leaf}, klongs differ"]
    | _, _ => errs := errs ++ [s!"write {s}/{c}: a value against a key node"]
  return (errs.take 5, ren)

/-- Checks one transaction: the differences, or none. -/
def checkTx (capH topFault : Bool) (p : Params) (P : PMap) (i : Nat) (base : Nat)
    (ops : List SIS.Tree.Op) : Except String (List String) := do
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
  let tp0 ← ctop P
  if tp0.getLast?.map (·.1) != some z then
    throw s!"the root's last top node {tp0.getLast?.map (·.1)}, the super root {z}"
  if tp0.length != top.ord + 1 then
    throw s!"{tp0.length} top nodes, the super root's ordinal {top.ord}"
  let tp : Contract.Top := if topFault then (cBase - 1, ⟨0, 0, []⟩) :: tp0 else tp0
  let oS := SIS.Tree.Pe.peTx cfS i s top.rootKey base ops
  let rS := SIS.Tree.Pe.runOps p base ops i view
  let oC := Contract.PE.peTx cfC i ct tp cBase (ops.map opOf)
  match oS, rS, oC with
  | none, .error _, none => return []
  | some _, .error e, _ => return [s!"T({i}): the copy's runOps refused, its peTx did not: {e}"]
  | none, .ok _, _ => return [s!"T({i}): the copy's peTx refused, its runOps did not"]
  | none, _, some _ => return [s!"T({i}): the copy refused, the proved writer did not"]
  | some _, _, none => return [s!"T({i}): the proved writer refused, the copy did not"]
  | some os, .ok (_, w), some oc =>
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
    let newS := fun x => decide (base ≤ x)
    let (errs, walkMap) := compare newS getS getC keysS keysC rS rC
    -- 2. The writes in their order.
    let (werrs, ren) := compareWrites newS os.ws.reverse oc.ws.reverse
    let mut errs := (if dupS + dupC > 0 then [s!"nodes written twice: {dupS}, {dupC}"] else []) ++ errs ++ werrs
    for (a, b) in walkMap.toList do
      if ren[a]? != some b then
        errs := errs ++ [s!"node {a}: {b} by the walk, {ren[a]?} by the writes"]
    -- 4. The top.
    let cNew := oc.top.length == tp.length + 1
    if !cNew && oc.top.length != tp.length then
      errs := errs ++ [s!"the proved writer's top: {tp.length} top nodes, then {oc.top.length}"]
    if os.root.isSome != cNew || w.newTop != cNew then
      errs := errs ++ [s!"a new top node: the copy's writes {os.root.isSome}, its runOps {w.newTop}, the proved writer {cNew}"]
    if cNew then
      match oc.top.getLast?, oc.roots.getLast? with
      | some (zc, tn), some (rt, rr) =>
        let ordC := tp.length
        if w.top.ord != ordC then
          errs := errs ++ [s!"the new top node's ordinal: the copy {w.top.ord}, the proved writer {ordC}"]
        if w.top.time != i || tn.time != i || rt != i then
          errs := errs ++ [s!"the new top node's time: the copy {w.top.time}, the proved writer {tn.time} (root {rt}), the transaction {i}"]
        if tn.root != rr || ren.getD w.top.rootKey w.top.rootKey != tn.root || os.root != some w.top.rootKey then
          errs := errs ++ [s!"the new top node's root: the copy {w.top.rootKey}, the proved writer {tn.root} (space root {rr})"]
        if w.top.skips != tn.skips.map (fun q => (q.1, q.2.1)) then
          errs := errs ++ [s!"the new top node's skip pointers: the copy {w.top.skips}, the proved writer {tn.skips.map (fun q => (q.1, q.2.1))}"]
        for (j, y, t) in tn.skips do
          let ty := if y == z then some top.time else topTime P y
          if ty != some t then
            errs := errs ++ [s!"the new top node's skip pointer {j} to {y}: cached time {t}, the target's {ty}"]
        if ren.toList.any (fun q => zc ≤ q.2) || ren.toList.any (fun q => w.top.id ≤ q.1) then
          errs := errs ++ [s!"the new top node's id is not after every node made: {w.top.id}, {zc}"]
        if w.top.id != os.next then
          errs := errs ++ [s!"the copy's new top node {w.top.id}, its next id {os.next}"]
      | _, _ => errs := errs ++ ["the proved writer: a new top node without a space root"]
    else if oc.roots != ct.roots then
      errs := errs ++ ["the proved writer changed the space roots without a new top node"]
    return errs.map (fun e => s!"T({i}): {e}")

def runTrace (capH topFault : Bool) (file : String) : IO (Nat × Nat × Nat × List String) := do
  let text ← IO.FS.readFile file
  let tr := parseTrace text
  let tt := parseTree text
  match tt.tree with
  | none => return (0, 0, 0, ["no TREE line"])
  | some (p, _) =>
    let mut P : PMap := {}
    let mut n := 0
    let mut tops := 0
    let mut bad := 0
    let mut errs : List String := []
    if tr.recs.size != tt.txs.size then
      return (0, 1, 0, [s!"{tr.recs.size} records, {tt.txs.size} transactions of tree lines"])
    for (r, x) in tr.recs.toList.zip tt.txs.toList do
      if r.idx != 0 then
        match x.base with
        | some base =>
          n := n + 1
          if r.adds.any (fun a => a.1 == root) then tops := tops + 1
          match checkTx capH topFault p P r.idx base (x.ops.toList.map (·.1)) with
          | .ok [] => pure ()
          | .ok es =>
            bad := bad + 1
            if errs.length < 6 then errs := errs ++ es.take 3
          | .error e =>
            bad := bad + 1
            if errs.length < 6 then errs := errs ++ [s!"T({r.idx}): {e}"]
        | none => pure ()
      P := applyRec p P r
    return (n, bad, tops, errs)

end PeCmp

def main (args : List String) : IO UInt32 := do
  let mut total := 0
  let mut bad := 0
  let mut tops := 0
  let mut traces := 0
  let capH := args.contains "--cap-h"
  let topFault := args.contains "--top-fault"
  for f in args.filter (fun a => a != "--cap-h" && a != "--top-fault") do
    let (n, b, t, errs) ← PeCmp.runTrace capH topFault f
    traces := traces + 1
    total := total + n
    bad := bad + b
    tops := tops + t
    IO.println s!"{f}: {n} transactions, {t} new top nodes, {b} differ"
    for e in errs do
      IO.println s!"  {e}"
  IO.println s!"total: {traces} traces, {total} transactions, {tops} new top nodes, {bad} differ"
  if bad == 0 && traces > 0 && total > 0 then
    IO.println "PECMP OK"
    return 0
  else
    IO.println "PECMP FAILED"
    return 1
