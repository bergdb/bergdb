/-
The writer checker (bergdb 030-10): `lake exe writercheck TRACE...` reads
traces of format 3 (bergdb 027-02) and runs the model's writer
(lean/SIS/Tree/Exec.lean) on Java's tree before every traced transaction, one
operation at a time. It checks:

* S, the start: the model's view shows the contract's tree and top (`Shows`,
  computed over the heap), and the books (`Books`: the times before i, the
  ids below the first id, the space roots the top's).
* M, the map: the contract's tree, top and space roots of the writer's state
  after the transaction (`treeOf`, `topOf`) are Java's tree and top after it
  (the checker's `applyTx`, `applyTop`), node for node.
* J, after every operation of the transaction, on the map of the writer's
  state then: J1 the invariants at time i; J2 the contents are those before
  the transaction with the operations so far applied; J3 the frame; J4 TREE;
  J5 the top's clauses and the space roots; and the candidates for the
  writer's books within a transaction, each by name (B1 to B9, below).
* The writer's own rules (`shapeFaults`) after every operation, by name.

Prints one line per trace and WRITER OK or WRITER FAILED; a failure names the
trace, the transaction and the operation. Not part of what is trusted.
-/
import Check.Tree
import Contract.Writer
import Contract.Trace
import Contract.CheckShape
import Contract.TraceTop

open Contract

structure WCounts where
  txs : Nat := 0
  ops : Nat := 0
  errs : Nat := 0
  s : Nat := 0
  m : Nat := 0
  j1 : Nat := 0
  j2 : Nat := 0
  j3 : Nat := 0
  j4 : Nat := 0
  j5 : Nat := 0
  books : List (String × Nat) := []
  shape : List (String × Nat) := []
  first : Option String := none

def WCounts.fail (c : WCounts) (msg : String) : WCounts :=
  { c with first := c.first.orElse (fun _ => some msg) }

def bump (l : List (String × Nat)) (name : String) : List (String × Nat) :=
  if l.any (·.1 == name) then l.map (fun q => if q.1 == name then (q.1, q.2 + 1) else q)
  else l ++ [(name, 1)]

/-- `Shows`, computed over the heap; and the books of the start. -/
def showsFaults (p : MParams) (i : Time) (base : NodeId) (P : SIS.Check.Tree.PMap) (h : Heap)
    (tp : Top) : List String := Id.run do
  let mut f : List String := []
  for (x, o) in h.objs.toList do
    if base ≤ x then f := f ++ [s!"node {x} is not below the first id {base}"]
    match o with
    | .key n =>
      if !timesBefore i n.ks then f := f ++ [s!"key node {x} has a time at or after {i}"]
      match n.ks with
      | .time _ :: _ => pure ()
      | _ => f := f ++ [s!"key node {x} does not start with a time klong"]
      if n.level == 0 then f := f ++ [s!"key node {x} has level 0"]
      if !n.leaf && !(n.ks.all (fun k => match k with
          | .key _ y => (match h.objs[y]? with
            | some (.key m) => m.level + 1 == n.level
            | _ => false)
          | _ => true)) then f := f ++ [s!"inner node {x} names a node not one level below"]
      match P[x]? with
      | some nd =>
        if nd.isData || nd.level != n.level || p.keyMax < n.level ||
            (SIS.Tree.klongsOf nd.hist).map kOf != n.ks ||
            n.leaf != (p.heightOf n.level == 0) then
          f := f ++ [s!"the view does not show key node {x}"]
      | none => f := f ++ [s!"the view has no key node {x}"]
    | .val _ => pure ()
  let v : SIS.View SIS.Check.BVal := fun y => P[y]?
  match SIS.Tree.lastTop v, tp.getLast? with
  | some z, some (z', zn) =>
    match SIS.Tree.topOf p (SIS.Tree.rootless v) z with
    | .ok t =>
      if !(z == z' && t.id == z && t.time == zn.time && t.rootKey == zn.root &&
          t.skips == zn.skips.map (fun q => (q.1, q.2.1))) then
        f := f ++ ["the view's super root is not the last top node"]
    | .error e => f := f ++ [s!"the view's super root: {e}"]
  | _, _ => f := f ++ ["no super root"]
  for (z, _) in tp do
    if base ≤ z then f := f ++ [s!"top node {z} is not below the first id {base}"]
  if h.roots != rootsOf tp then f := f ++ ["the space roots are not the top's"]
  if !h.roots.all (fun r => decide (r.1 < i)) then f := f ++ ["a space root's time is not before i"]
  return f

/-- The key klongs of a node's klongs: the nodes they name. -/
def named (ks : List MKlong) : List NodeId :=
  ks.filterMap (fun k => match k with
    | .key _ y => some y
    | _ => none)

/-- The candidates for the writer's books within a transaction, on the state w
of the transaction at time i from the heap h: the names of those that fail. -/
def bookFaults (p : MParams) (i : Time) (base : NodeId) (h : Heap) (w : MW) : List String :=
  let s := treeOf i h.tree w
  let reached := reach (s.at i)
  let live := w.nodes.filter (fun q => !w.taken.contains q.1)
  let madeIds := w.made.map (·.id)
  -- B1: an overlay node is of s exactly if its first time is not i.
  (if live.all (fun q => (h.objs.contains q.1) == (q.2.firstTime != some i)) then []
    else ["B1 made = first time i"]) ++
  -- B2: no time after i in the overlay.
  (if w.nodes.all (fun q => q.2.ks.all (fun k => match k with
      | .time t => decide (t ≤ i)
      | _ => true)) then [] else ["B2 times at most i"]) ++
  -- B3: a node replaced (`madeFor`) is a key node of s.
  (if w.madeFor.all (fun q => match h.objs[q.2]? with
      | some (.key _) => true
      | _ => false) then [] else ["B3 madeFor names a node of s"]) ++
  -- B4: no klong of a node kept, live or dead, names a node taken back.
  (if live.all (fun q => (named q.2.ks).all (fun y => !w.taken.contains y)) then []
    else ["B4 no klong names a node taken back"]) ++
  -- B5: the level of an overlay node is that of its segment and height; a
  -- segment leaf exactly at height 0.
  (if live.all (fun q => match w.gh.lookup q.1 with
      | some (g, ht) => wLevel h.tree w q.1 == p.keyLevel g ht && q.2.leaf == (ht == 0)
      | none => false) then [] else ["B5 levels are the segments and heights"]) ++
  -- B6: every id of the state is below the next id; a node made is at or
  -- above the first id, and no node of s.
  (if w.nodes.all (fun q => decide (q.1 < w.next)) && w.vals.all (fun q => decide (q.1 < w.next)) &&
      madeIds.all (fun x => decide (x < w.next) && decide (base ≤ x) && !h.objs.contains x) &&
      decide (base ≤ w.next) && (!w.newTop || decide (w.top.id < w.next))
    then [] else ["B6 ids"]) ++
  -- B7: a key node of s in the overlay that is not reached at i has its klongs of s.
  (if live.all (fun q => match h.objs[q.1]? with
      | some (.key n) => reached.contains q.1 || q.2.ks.map kOf == n.ks
      | _ => true) then [] else ["B7 an old node not reached is as it was"]) ++
  -- B8: a node made and not taken back is reached at i.
  (if madeIds.all (fun x => w.taken.contains x || reached.contains x || x == w.top.id) then []
    else ["B8 a node made is reached"]) ++
  -- B9: a node taken back was made by the transaction.
  (if w.taken.all (fun x => madeIds.contains x) then [] else ["B9 taken back was made"]) ++
  -- B10: a node of the overlay that is no node of s was made by the transaction.
  (if w.nodes.all (fun q => h.objs.contains q.1 || madeIds.contains q.1) then []
    else ["B10 overlay nodes are of s or made"]) ++
  -- B11: an outside node (beyond G, H) is not reached.
  (if w.outside.all (fun q => w.taken.contains q.1) then [] else ["B11 outside nodes taken back"]) ++
  -- B13: every node kept of the overlay starts with a time klong.
  (if live.all (fun q => match q.2.ks with
      | .time _ :: _ => true
      | _ => false) then [] else ["B13 a time klong first"]) ++
  -- B14: BalancedOK for every node kept of the overlay and every key klong of it,
  -- live or dead: an inner node's klong names a key node one level below.
  (if live.all (fun q => q.2.leaf || (named q.2.ks).all (fun y => match s.obj y, s.obj q.1 with
      | some (.key m), some (.key n) => m.level + 1 == n.level
      | _, _ => false)) then [] else ["B14 every klong of an inner node names a node one level below"]) ++
  -- B12: a made node's `madeFor`, if any, is of its segment, at its height or
  -- below (a root made by a split replaces the node split).
  (if w.madeFor.all (fun q => match w.gh.lookup q.1, h.objs[q.2]? with
      | some (g, ht), some (.key n) => g == p.segOf n.level && decide (p.heightOf n.level ≤ ht)
      | _, _ => false) then [] else ["B12 madeFor keeps the segment"])

/-- The ids to compare for the map: of the heaps and of the writer's state. -/
def idsOf (h h' : Heap) (w : MW) : List NodeId :=
  h.objs.toList.map (·.1) ++ h'.objs.toList.map (·.1) ++ w.nodes.map (·.1) ++ w.vals.map (·.1) ++
    w.made.map (·.id)

def checkWriterTrace (p : MParams) (tr : Trace) (old : SIS.Check.Trace)
    (tt : SIS.Check.Tree.TTrace) : WCounts := Id.run do
  let cp : Params := { M := tr.M }
  let mut h : Heap := {}
  let mut P : SIS.Check.Tree.PMap := {}
  let mut tp : Top := []
  let mut c : WCounts := {}
  let mut pos := 0
  for tx in tr.txs do
    let i := tx.i
    let r := old.recs.getD pos default
    let x := tt.txs.getD pos default
    let h' := applyTx h tx
    let tp' := applyTop tp tx
    let after := SIS.Check.Tree.applyRec p P r
    if r.idx != i || x.idx != i then
      c := { c.fail s!"TX {i}: the readers differ" with errs := c.errs + 1 }
    if i != 0 then
      c := { c with txs := c.txs + 1, ops := c.ops + tx.ops.length }
      let ops := x.ops.toList.map (·.1)
      if ops.map opOf != tx.ops then
        c := { c.fail s!"TX {i}: the readers' operations differ" with errs := c.errs + 1 }
      match x.base with
      | none => c := { c.fail s!"TX {i}: no BASE line" with errs := c.errs + 1 }
      | some base =>
        -- S: the start.
        let sf := showsFaults p i base P h tp
        if !sf.isEmpty then c := { c.fail s!"TX {i}: S, {sf.take 2}" with s := c.s + 1 }
        let v : SIS.View SIS.Check.BVal := fun y => P[y]?
        match SIS.Tree.lastTop v with
        | none => c := { c.fail s!"TX {i}: no super root" with errs := c.errs + 1 }
        | some z =>
          match SIS.Tree.topOf p (SIS.Tree.rootless v) z with
          | .error e => c := { c.fail s!"TX {i}: {e}" with errs := c.errs + 1 }
          | .ok top =>
            let ctx : SIS.Tree.Ctx := { p := p, i := i, view := SIS.Tree.rootless v }
            let mut w : MW := { next := base, top := top }
            let mut done : List Op := []
            let mut k := 0
            let mut failed := false
            let before := contents (h.tree.at (i - 1))
            for op in ops do
              if !failed then
                match ((SIS.Tree.putKv op).run ctx).run w with
                | .error e =>
                  c := { c.fail s!"TX {i}, operation {k}: the model's error: {e}" with errs := c.errs + 1 }
                  failed := true
                | .ok (_, w') =>
                  w := w'
                  done := done ++ [opOf op]
                  let s' := (treeOf i h.tree w).at i
                  let tpw := topOf i tp w
                  if !(invOk cp s') then
                    c := { c.fail s!"TX {i}, operation {k}: J1, the invariants" with j1 := c.j1 + 1 }
                  if !(contents s' == applyOps done before) then
                    c := { c.fail s!"TX {i}, operation {k}: J2, the contents" with j2 := c.j2 + 1 }
                  if !(h.objs.toList.all (fun xo => match (treeOf i h.tree w).obj xo.1 with
                      | some o' => extOk i xo.2 o' && ((dirtyOf w).contains xo.1 || o' == xo.2)
                      | none => false) &&
                      rootsExt i h.roots (treeOf i h.tree w).roots) then
                    c := { c.fail s!"TX {i}, operation {k}: J3, the frame" with j3 := c.j3 + 1 }
                  if !(treeOkB s') then
                    c := { c.fail s!"TX {i}, operation {k}: J4, TREE" with j4 := c.j4 + 1 }
                  if !(topStepB i tp tpw && (treeOf i h.tree w).roots == rootsOf tpw) then
                    c := { c.fail s!"TX {i}, operation {k}: J5, the top" with j5 := c.j5 + 1 }
                  for b in bookFaults p i base h w do
                    c := { c.fail s!"TX {i}, operation {k}: {b}" with books := bump c.books b }
                  for b in (shapeFaults tr.shape s').eraseDups do
                    c := { c with shape := bump c.shape b }
              k := k + 1
            if !failed then
              -- M: the map of the writer's state is Java's tree and top.
              let s' := treeOf i h.tree w
              let bad := (idsOf h h' w).filter (fun y => s'.obj y != h'.objs[y]?)
              if !bad.isEmpty then
                c := { c.fail s!"TX {i}: M, the map differs from Java's tree at {bad.take 3}" with m := c.m + 1 }
              if s'.roots != h'.roots then
                c := { c.fail s!"TX {i}: M, the space roots" with m := c.m + 1 }
              if topOf i tp w != tp' then
                c := { c.fail s!"TX {i}: M, the top" with m := c.m + 1 }
    h := h'
    tp := tp'
    P := after
    pos := pos + 1
  return c

def showCounts (l : List (String × Nat)) : String :=
  if l.isEmpty then "none" else ", ".intercalate (l.map (fun q => s!"{q.1} {q.2}"))

def addCounts (a b : List (String × Nat)) : List (String × Nat) :=
  b.foldl (fun l q => if l.any (·.1 == q.1) then l.map (fun r => if r.1 == q.1 then (r.1, r.2 + q.2) else r)
    else l ++ [q]) a

def main (args : List String) : IO UInt32 := do
  let mut failed := 0
  let mut total : WCounts := {}
  for path in args do
    let lines ← IO.FS.lines path
    let text ← IO.FS.readFile path
    let old := SIS.Check.parseTrace text
    let tt := SIS.Check.Tree.parseTree text
    match readTrace lines, tt.tree with
    | .error e, _ =>
      IO.println s!"{path}: unreadable: {e}"
      failed := failed + 1
    | _, none =>
      IO.println s!"{path}: no TREE line"
      failed := failed + 1
    | .ok tr, some (p, _) =>
      let c := checkWriterTrace p tr old tt
      let nb := (c.books.map (·.2)).foldl (· + ·) 0
      let bad := c.errs + c.s + c.m + c.j1 + c.j2 + c.j3 + c.j4 + c.j5 + nb
      IO.println s!"{path}: {c.txs} transactions, {c.ops} operations; failures: errors {c.errs}, S {c.s}, M {c.m}, J1 {c.j1}, J2 {c.j2}, J3 {c.j3}, J4 {c.j4}, J5 {c.j5}; books: {showCounts c.books}; shape faults: {showCounts c.shape}{match c.first with | some m => "; first: " ++ m | none => ""}"
      if bad != 0 || c.txs == 0 then failed := failed + 1
      total := { total with txs := total.txs + c.txs, ops := total.ops + c.ops,
                            errs := total.errs + c.errs, s := total.s + c.s, m := total.m + c.m,
                            j1 := total.j1 + c.j1, j2 := total.j2 + c.j2, j3 := total.j3 + c.j3,
                            j4 := total.j4 + c.j4, j5 := total.j5 + c.j5,
                            books := addCounts total.books c.books,
                            shape := addCounts total.shape c.shape }
  IO.println s!"total: {args.length} traces, {total.txs} transactions, {total.ops} operations; failures: errors {total.errs}, S {total.s}, M {total.m}, J1 {total.j1}, J2 {total.j2}, J3 {total.j3}, J4 {total.j4}, J5 {total.j5}; books: {showCounts total.books}; shape faults: {showCounts total.shape}"
  if failed == 0 then
    IO.println "WRITER OK"
    return 0
  else
    IO.println s!"WRITER FAILED: {failed} traces"
    return 1
