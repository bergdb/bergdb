/-
The tree checker: checks a trace of format 3 (java/stress/TraceExport.java with
tree=1) against the tree model, SIS/Tree/*.lean (bergdb 024-12, section 2.7;
docs/trace-format.md, section 4).

Usage: lake exe treecheck TRACE [--norun]

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
        kinds of the children, the sizes, well-formed klongs; and every pointer
        of an entry added names a node of P
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
-/
import Check.TreeRun

open SIS SIS.Check SIS.Check.Tree SIS.Tree

def report (name : String) (fails : Array String) (n : Nat) : IO Unit := do
  IO.println s!"{name}: {fails.size} failures in {n} transactions"
  for f in fails.toList.take 8 do
    IO.println s!"  {f}"

def main (args : List String) : IO UInt32 := do
  match args with
  | file :: opts =>
    let text ← IO.FS.readFile file
    let tr := parseTrace text
    let tt := parseTree text
    match tt.tree with
    | none =>
      IO.println "TREE FAILED: no TREE line (a trace of format 3 is made with tree=1)"
      return 1
    | some (p, k0) =>
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
      for (r, x) in tr.recs.toList.zip tt.txs.toList do
        let after := applyRec p P r
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
        P := after
      for b in tt.bad.toList.take 8 do
        IO.println s!"bad line: {b}"
      IO.println s!"tree: M={p.M} G={p.G} H={p.H}{if p.merges then s!" m={p.mergeBelow} c={p.mergeMax} h={p.splitAbove}" else ""}; {n} transactions, {opsN} operations ({noopN} noops), {made} key nodes made, {taken} taken back, {kn} KN lines, {gets} GET lines, {scans} SCAN lines, {touches} touches"
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
      let bad := change.size + klongs.size + noops.size + reads.size + touch.size + inv.size + bound.size + runFails.size + form.size + errors.size + tt.bad.size
      if bad == 0 then
        IO.println "TREE OK"
        return 0
      else
        IO.println s!"TREE FAILED: {bad} failures"
        return 1
  | _ =>
    IO.println "Usage: treecheck TRACE"
    return 2
