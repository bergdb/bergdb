/-
The tree checker: checks a trace of format 3 (java/stress/TraceExport.java with
tree=1) against the tree model, SIS/Tree/*.lean (bergdb 024-12, section 2.7;
bergdb 027-02, section 4).

Usage: lake exe treecheck TRACE [--norun] [--hplus | --hplus=K]

Checks, per transaction i of the trace, from Java's structure before it:
  C-T1  the change: the model's `Tree.exec` of the transaction's operations gives
        the trace's change: every node made, with its id, level and kind, and
        every entry added (NEW and ADD lines), as lists
  C-T2  the klongs: each KN line is the model's node, klong by klong (the size,
        the bitmaps by index, the lone time klong of 024-12, D4); and it is the
        klongs of the node's history (`klongsOf`), and gives it (`entriesOf`)
  C-T3  the noops: an `OP N` is a noop of the model, an `OP D` is not
  C-T4  the reads: each GET line is the model's `get` on Java's structure, each
        SCAN line the model's `scan`
  C-T5  the touch (reclaim's steps): the TOUCH line is the model's `touchOf`:
        the index nodes on the paths of the transaction's keys
  C-T6  the invariants (SIS/Tree/Inv.lean, `faultsAt`): on Java's structure after
        the transaction, at its time: the leftmost rule (LE-b), a live klong in
        every node but the space root, two in an inner root, the order, the
        kinds of the children, the sizes, well-formed klongs, with merges m live
        klongs (V1), with option 2 at most theta dead klongs a node (TP39); and
        every pointer of an entry added names a node of P
  C-T8  the bound: the key nodes that the transaction marks (those on the access
        path of its change) are at most `dirtyNodeBound` of its operations on
        the tree before it (Java's `Dag.dirtyNodeBound`, restated)
  C-T9  the whole run (Check/TreeRun.lean): the model's `init` and `step` with
        the tree's `exec`, from R(0), given of Java's run only each
        transaction's operations, first id, startup pos and first available
        time, write Java's records (the versions with their histories and
        references, gd, top) and keep Java's D; not with --norun
  C-T7  the form: the keys of a transaction's operations strictly increasing,
        each key as `Keys.toSegments` makes them; no error of the model

Prints one line a check, the first failures, counts of what the trace reached
(splits, take-backs, noops), and TREE OK or TREE FAILED.

With --hplus (k = 1) or --hplus=K (bergdb 025-03): every check runs the model at
H + k, on the trace with its levels at H + k (`shiftTrace`): a node keeps its
segment and height, so the checks that compare levels compare those. Two more:
  NoOutside  no transaction's writer at H + k makes a key node outside G and H + k
             (`W.outside` empty, even for a node taken back)
  SameTree   the writer at the trace's own H and at H + k, on Java's structure
             before each transaction, read and make the same nodes with the same
             klongs, segments and heights, and take back the same ones
and the line `hplus:`, the transactions whose writer at the trace's own H makes a
key node outside G and H, and the least k that covers them.
-/
import Check.TreeRun

open SIS SIS.Check SIS.Check.Tree SIS.Tree

/-! ## The model with a larger H (bergdb 025-03) -/

/-- Level l of a trace's node at the bounds p, as the level of the same node at the bounds
q, whose G is p's and whose H is at least p's: a key node keeps its segment and its height
(`Params.segOf`, `Params.heightOf`), a top node its ordinal, the root stays above them, a
value stays at 0. The levels shift with H; the segment and the height do not. -/
def shiftLevel (p q : Params) (l : Nat) : Nat :=
  if l == 0 then 0
  else if l ≤ p.keyMax then q.keyLevel (p.segOf l) (p.heightOf l)
  else l - p.keyMax + q.keyMax

/-- A trace with the levels of its NEW lines at the bounds q (`shiftLevel`); its versions
take their levels from these lines (`levelMap`). A check that compares levels at q then
compares a key node's segment and height, a top node's ordinal. -/
def shiftTrace (p q : Params) (tr : Trace) : Trace :=
  { tr with recs := tr.recs.map (fun r =>
      { r with new := r.new.map (fun (x, l, d) => (x, shiftLevel p q l, d)) }) }

/-- Transaction i run by the writer at the trace's own bounds p on P, Java's structure
before it, and at the bounds q on Q, the same structure at q's levels: the key nodes that
each run makes outside its G and H (`W.outside`, taken back or not), and where the two
runs differ, the levels apart: the noops, the nodes read and made with their klongs,
segments and heights, the values, the nodes taken back, the top node. -/
structure HPlusTx where
  outside : List (NodeId × Nat × Nat) := []
  outsideQ : List (NodeId × Nat × Nat) := []
  diffs : List String := []

def hplusTx (p q : Params) (P Q : PMap) (i : Time) (x : TTx) : HPlusTx :=
  match x.base with
  | none => {}
  | some base =>
    let ops := x.ops.toList.map (·.1)
    match runOps p base ops i (fun y => P[y]?), runOps q base ops i (fun y => Q[y]?) with
    | .ok (f0, w0), .ok (f1, w1) =>
      let kinds := fun (w : W) => w.made.map (fun n => (n.id, n.isData))
      let same := [("noops", f0 == f1), ("nodes", w0.nodes == w1.nodes),
        ("segments and heights", w0.gh == w1.gh), ("nodes made", kinds w0 == kinds w1),
        ("values", w0.vals == w1.vals), ("nodes taken back", w0.taken == w1.taken),
        ("top nodes", w0.top == w1.top && w0.newTop == w1.newTop)]
      { outside := w0.outside, outsideQ := w1.outside,
        diffs := (same.filter (!·.2)).map (fun (s, _) =>
          s!"T({i}): the {s} differ at H = {p.H} and at H = {q.H}") }
    | .error e, _ => { diffs := [s!"T({i}): at H = {p.H}, the model's error: {e}"] }
    | _, .error e => { diffs := [s!"T({i}): at H = {q.H}, the model's error: {e}"] }

def report (name : String) (fails : Array String) (n : Nat) : IO Unit := do
  IO.println s!"{name}: {fails.size} failures in {n} transactions"
  for f in fails.toList.take 8 do
    IO.println s!"  {f}"

/-- The option --hplus (k = 1) or --hplus=K: some k; none without it. -/
def hplusOf (opts : List String) : Option Nat :=
  opts.foldl (fun k o =>
    if o == "--hplus" then some 1
    else if o.startsWith "--hplus=" then (o.drop 8).toNat? else k) none

/-- Key nodes outside the bounds (`W.outside`), in the order made. -/
def showOutside (o : List (NodeId × Nat × Nat)) : String :=
  ", ".intercalate (o.reverse.map (fun (y, g, h) => s!"node {y} at segment {g}, height {h}"))

def main (args : List String) : IO UInt32 := do
  match args with
  | file :: opts =>
    let hk := hplusOf opts
    if opts.any (·.startsWith "--hplus") && hk.isNone then
      IO.println "Usage: treecheck TRACE [--norun] [--hplus | --hplus=K]"
      return 2
    let text ← IO.FS.readFile file
    let tr0 := parseTrace text
    let tt := parseTree text
    match tt.tree with
    | none =>
      IO.println "TREE FAILED: no TREE line (a trace of format 3 is made with tree=1)"
      return 1
    | some (p0, k0) =>
      -- With --hplus: the model at H + k, on the trace's levels at H + k.
      let p := match hk with
        | some k => { p0 with H := p0.H + k }
        | none => p0
      let tr := match hk with
        | some _ => shiftTrace p0 p tr0
        | none => tr0
      let mut P0 : PMap := {}
      let mut outTxs := 0
      let mut outNodes := 0
      let mut outSeg := 0
      let mut outHigh := 0
      let mut outList : Array String := #[]
      let mut noOutside : Array String := #[]
      let mut sameTree : Array String := #[]
      let mut P : PMap := {}
      let mut change : Array String := #[]
      let mut klongs : Array String := #[]
      let mut noops : Array String := #[]
      let mut reads : Array String := #[]
      let mut touch : Array String := #[]
      let mut inv : Array String := #[]
      let mut bound : Array String := #[]
      let mut markedSum := 0
      let mut boundSum := 0
      let mut madeMax := 0
      let mut scans := 0
      let mut touches := 0
      let mut form : Array String := #[]
      let mut errors : Array String := #[]
      let mut kn := 0
      let mut gets := 0
      let mut opsN := 0
      let mut noopN := 0
      let mut made := 0
      let mut taken := 0
      let mut n := 0
      let mut trail : Std.HashMap String Nat := {}
      if tr.recs.size != tt.txs.size then
        errors := errors.push s!"{tr.recs.size} transactions, {tt.txs.size} with tree lines"
      for (r, r0, x) in tr.recs.toList.zip (tr0.recs.toList.zip tt.txs.toList) do
        let after := applyRec p P r
        let after0 := if hk.isSome then applyRec p0 P0 r0 else P0
        if r.idx == 0 then
          -- R(0): the primordial structure, and its key node's klongs.
          for (y, jn) in x.kns do
            kn := kn + 1
            match after[y]? with
            | some nd =>
              if klongsOf nd.hist != jn.ks then
                klongs := klongs.push s!"R(0): KN {y}: the history gives {showKs (klongsOf nd.hist)}, Java has {showKs jn.ks}"
            | none => klongs := klongs.push s!"R(0): KN {y}: no such node"
          if (rootAt (fun y => after[y]?) 0) != some k0 then
            errors := errors.push s!"R(0): the space root is not the TREE line's key node {k0}"
        else
          n := n + 1
          let res := checkTx p P after r x
          change := change ++ res.change.toArray
          klongs := klongs ++ res.klongs.toArray
          noops := noops ++ res.noops.toArray
          reads := reads ++ res.reads.toArray
          touch := touch ++ res.touch.toArray
          inv := inv ++ res.inv.toArray
          bound := bound ++ res.bound.toArray
          markedSum := markedSum + res.markedSum
          boundSum := boundSum + res.boundSum
          madeMax := max madeMax res.madeMax
          scans := scans + res.scanCount
          touches := touches + res.touchCount
          form := form ++ res.form.toArray
          errors := errors ++ res.errors.toArray
          kn := kn + res.knCount
          gets := gets + res.getCount
          opsN := opsN + res.opCount
          noopN := noopN + res.noopCount
          made := made + res.splitNodes
          taken := taken + res.takenBack
          for s in res.trail do
            trail := trail.insert s (trail.getD s 0 + 1)
          if hk.isSome then
            let h := hplusTx p0 p P0 P r.idx x
            if !h.outside.isEmpty then
              outTxs := outTxs + 1
              outNodes := outNodes + h.outside.length
              outList := outList.push s!"T({r.idx}): {showOutside h.outside}"
              for (_, g, ht) in h.outside do
                if p0.G < g then outSeg := outSeg + 1 else outHigh := max outHigh ht
            if !h.outsideQ.isEmpty then
              noOutside := noOutside.push s!"T({r.idx}): outside G = {p.G}, H = {p.H}: {showOutside h.outsideQ}"
            sameTree := sameTree ++ h.diffs.toArray
        P := after
        P0 := after0
      for b in tt.bad.toList.take 8 do
        IO.println s!"bad line: {b}"
      IO.println s!"tree: M={p.M} G={p.G} H={p.H}{if p.merges then s!" m={p.mergeBelow} c={p.mergeMax} h={p.splitAbove}" else ""}{if p.theta != 0 then s!" theta={p.theta}" else ""}; {n} transactions, {opsN} operations ({noopN} noops), {made} key nodes made, {taken} taken back, {kn} KN lines, {gets} GET lines, {scans} SCAN lines, {touches} touches"
      let names := trail.toList.mergeSort (fun a b => decide (a.1 ≤ b.1))
      IO.println ("reached: " ++ ", ".intercalate (names.map (fun (s, k) => s!"{s} {k}")))
      report "C-T1 change" change n
      report "C-T2 klongs" klongs n
      report "C-T3 noops" noops n
      report "C-T4 reads" reads n
      report "C-T5 touch" touch n
      report "C-T6 invariants" inv n
      report "C-T8 bound" bound n
      IO.println s!"bound: {markedSum} key nodes marked, dirtyNodeBound {boundSum}, summed; at most {madeMax} nodes made an operation, MadeBound allows {4 * p.fuel + 1}"
      let mut runFails : Array String := #[]
      if !opts.contains "--norun" then
        let (rf, rn) := wholeRun p tr tt
        runFails := rf.toArray
        IO.println s!"run: {rn} records of the model's own run compared with Java's"
        report "C-T9 run" runFails n
      report "C-T7 form" form n
      report "C-T7 model errors" errors n
      if let some k := hk then
        let least := if 0 < outSeg then "none (a node outside G)"
          else toString (outHigh - p0.H)
        let what := if outTxs == 0 then s!"no transaction makes a key node outside G = {p0.G}, H = {p0.H}"
          else s!"{outTxs} transactions make {outNodes} key nodes outside G = {p0.G}, H = {p0.H} (taken back or not), {outSeg} of them outside G, the highest at height {outHigh}"
        IO.println s!"hplus: the model at H = {p.H}, the trace's H = {p0.H} and k = {k}; at H = {p0.H}, {what}; the least k: {least}"
        for s in outList.toList.take 8 do
          IO.println s!"  {s}"
        report "NoOutside" noOutside n
        report "SameTree" sameTree n
      let bad := change.size + klongs.size + noops.size + reads.size + touch.size + inv.size + bound.size + runFails.size + form.size + errors.size + tt.bad.size + noOutside.size + sameTree.size
      if bad == 0 then
        IO.println "TREE OK"
        return 0
      else
        IO.println s!"TREE FAILED: {bad} failures"
        return 1
  | _ =>
    IO.println "Usage: treecheck TRACE"
    return 2
