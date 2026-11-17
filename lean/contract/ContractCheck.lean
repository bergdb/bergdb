/-
The contract checker (bergdb 030-04, section 7.4 (d)): `lake exe contractcheck
TRACE...` reads traces of format 3 (bergdb 027-02) and checks, for every
traced transaction alone, on Java's tree before and after it:

* C1, the invariants: `invOk` of the tree after it, at its time;
* C2, the contents: those of the tree after it are those of the tree before
  it with the transaction's operations applied;
* C3, the frame: `frameCheck`, with D the dirty nodes when the transaction
  ends, before its record is written: D after the record before (the DIRTY
  line of the transaction before) and the nodes that got dirty (its own GD
  line);
  (C1 to C3 together are `checkTx`, which is the writer's contract:
  `checkTx_sound`, Contract/Check.lean)
* R1, the reads: each GET line is `get`, each SCAN line is `scan`, on the tree
  after it at the line's time;
* S, the writer's own rules (`shapeFaults`), reported apart: they are not in
  the contract.

For TX 0: the start tree meets the invariants and is empty (`Start`).

Before that, the trace must be whole (`completeFault`, Complete.lean; bergdb
030-09): TRACE 3, no ERROR line and no line of an unknown kind, the
transactions numbered 0, 1, 2, ... and closed, a DONE line naming the last,
and each transaction's NEW, ADD and KN lines all of its change. TX j is
checked at time j, so a trace that passes is a history that meets the
contract (`historyOk_meets`, Contract/History.lean). With LIVE lines (the
exporter's live=1), L1: each is Java's search and top search as the
package's (`liveOk`).
Prints one line per trace and CONTRACT OK or CONTRACT FAILED; a failure
names the trace and the transaction.
-/
import Contract.Complete

open Contract

structure Counts where
  txs : Nat := 0
  ops : Nat := 0
  gets : Nat := 0
  scans : Nat := 0
  c1 : Nat := 0
  c2 : Nat := 0
  c3 : Nat := 0
  r1 : Nat := 0
  lives : Nat := 0
  l1 : Nat := 0
  shape : Nat := 0
  shapeNames : List String := []
  first : Option String := none

def Counts.fail (c : Counts) (msg : String) : Counts :=
  { c with first := c.first.orElse (fun _ => some msg) }

def checkTrace (tr : Trace) : Counts := Id.run do
  let p : Params := { M := tr.M }
  let mut h : Heap := {}
  let mut c : Counts := {}
  let mut dirtyBefore : List NodeId := []
  let mut j := 0
  let mut topRoot : List (NodeId × NodeId) := []
  for tx in tr.txs do
    if tx.i != j then c := { c.fail s!"TX {tx.i} read as transaction {j}" with c1 := c.c1 + 1 }
    let d := dirtyBefore ++ tx.gd
    let h' := applyTx h tx
    let i := tx.i
    let s' := h'.tree.at i
    if i == 0 then
      if !(invOk p s') then c := { c.fail "TX 0: C1, the start tree's invariants" with c1 := c.c1 + 1 }
      if !(contents s').isEmpty then c := { c.fail "TX 0: C2, the start tree is not empty" with c2 := c.c2 + 1 }
    else
      c := { c with txs := c.txs + 1, ops := c.ops + tx.ops.length }
      if !(invOk p s') then c := { c.fail s!"TX {i}: C1, the invariants" with c1 := c.c1 + 1 }
      if !(contents s' == applyOps tx.ops (contents (h.tree.at (i - 1)))) then
        c := { c.fail s!"TX {i}: C2, the contents" with c2 := c.c2 + 1 }
      if !(frameCheck i h d h') then c := { c.fail s!"TX {i}: C3, the frame" with c3 := c.c3 + 1 }
      -- The contract itself, as one value (the same three checks).
      if checkTx p i h tx.ops d h' != (invOk p s' &&
          contents s' == applyOps tx.ops (contents (h.tree.at (i - 1))) && frameCheck i h d h') then
        c := { c.fail s!"TX {i}: checkTx differs from its parts" with c3 := c.c3 + 1 }
    for g in tx.gets do
      c := { c with gets := c.gets + 1 }
      if get (h'.tree.at g.t) g.key != g.v then
        c := { c.fail s!"TX {i}: R1, a GET at {g.t} of {g.key}" with r1 := c.r1 + 1 }
    for sc in tx.scans do
      c := { c with scans := c.scans + 1 }
      if scan (h'.tree.at sc.t) sc.req sc.limit != sc.res then
        c := { c.fail s!"TX {i}: R1, a SCAN at {sc.t}" with r1 := c.r1 + 1 }
    topRoot := topRoot ++ tx.rootPtrs
    for (x, t, ys) in tx.lives do
      c := { c with lives := c.lives + 1 }
      if !liveOk h' topRoot x t ys then
        c := { c.fail s!"TX {i}: L1, a LIVE line of {x} at {t}" with l1 := c.l1 + 1 }
    let sf := shapeFaults tr.shape s'
    if !sf.isEmpty then
      c := { c with shape := c.shape + sf.length,
                    shapeNames := (c.shapeNames ++ sf).eraseDups }
    h := h'
    dirtyBefore := tx.dirty
    j := j + 1
  return c

def main (args : List String) : IO UInt32 := do
  let mut failed := 0
  let mut total : Counts := {}
  for path in args do
    let lines ← IO.FS.lines path
    if let some e := completeFault lines then
      IO.println s!"{path}: not whole: {e}"
      failed := failed + 1
    match readTrace lines with
    | .error e =>
      IO.println s!"{path}: unreadable: {e}"
      failed := failed + 1
    | .ok tr =>
      let c := checkTrace tr
      let bad := c.c1 + c.c2 + c.c3 + c.r1 + c.l1
      IO.println s!"{path}: M={tr.M} {c.txs} transactions, {c.ops} operations, {c.gets} GET, {c.scans} SCAN, {c.lives} LIVE; failures: C1 {c.c1}, C2 {c.c2}, C3 {c.c3}, R1 {c.r1}, L1 {c.l1}; shape faults {c.shape} {c.shapeNames}{match c.first with | some m => "; first: " ++ m | none => ""}"
      if bad != 0 || c.txs == 0 then failed := failed + 1
      total := { total with txs := total.txs + c.txs, ops := total.ops + c.ops,
                            gets := total.gets + c.gets, scans := total.scans + c.scans,
                            c1 := total.c1 + c.c1, c2 := total.c2 + c.c2, c3 := total.c3 + c.c3,
                            r1 := total.r1 + c.r1, lives := total.lives + c.lives,
                            l1 := total.l1 + c.l1, shape := total.shape + c.shape,
                            shapeNames := (total.shapeNames ++ c.shapeNames).eraseDups }
  IO.println s!"total: {args.length} traces, {total.txs} transactions, {total.ops} operations, {total.gets} GET, {total.scans} SCAN, {total.lives} LIVE; failures: C1 {total.c1}, C2 {total.c2}, C3 {total.c3}, R1 {total.r1}, L1 {total.l1}; shape faults {total.shape} {total.shapeNames}"
  if failed == 0 then
    IO.println "CONTRACT OK"
    return 0
  else
    IO.println s!"CONTRACT FAILED: {failed} traces"
    return 1
