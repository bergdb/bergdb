/-
The bridge checker (bergdb 030-07): `lake exe bridgecheck TRACE...` reads
traces of format 3 (bergdb 027-02) and checks, for every traced transaction
alone, on Java's tree before and after it and the transaction's NEW, ADD and
TOUCH lines, the computed clauses of the bridge (Contract/Bridge.lean):

* N, the nodes made (`newsOk`, `madeCheck`);
* K, the entries added are those of the klongs added (`addsOk`);
* L, for the key nodes of D: F4, W1 to W5 and A4 (`localOk`);
* A2, A3, A5 (`currentOk`, `madeOk`, `noResOk`);
  (together `bridgeOk` and `Made`, by `madeCheck_sound`)

and for TX 0 the start (`startCheck`). D is as in the contract checker: D
after the record before and the nodes that got dirty. Prints one line per
trace and BRIDGE OK or BRIDGE FAILED; a failure names the trace and the
transaction.
-/
import Contract.BridgeHeap
import Contract.Trace

open Contract

structure BCounts where
  txs : Nat := 0
  news : Nat := 0
  adds : Nat := 0
  touch : Nat := 0
  s : Nat := 0
  n : Nat := 0
  k : Nat := 0
  l : Nat := 0
  a2 : Nat := 0
  a3 : Nat := 0
  a5 : Nat := 0
  first : Option String := none

def BCounts.fail (c : BCounts) (msg : String) : BCounts :=
  { c with first := c.first.orElse (fun _ => some msg) }

def checkBridgeTrace (tr : Trace) (old : SIS.Check.Trace) : BCounts := Id.run do
  let chs := old.recs.map SIS.Check.changesOf
  let p0 := SIS.Struct.apply (V := SIS.Check.BVal) [] 0 (chs.getD 0 { new := [], adds := [] })
  let topLevel := SIS.Check.topLevelOf p0
  let mut h : Heap := {}
  let mut c : BCounts := {}
  let mut dirtyBefore : List NodeId := []
  let mut pos := 0
  for tx in tr.txs do
    let d := dirtyBefore ++ tx.gd
    let h' := applyTx h tx
    let i := tx.i
    let ch := chs.getD pos { new := [], adds := [] }
    if (old.recs.getD pos default).idx != i then
      c := { c.fail s!"TX {i}: the two readers differ" with s := c.s + 1 }
    if i == 0 then
      if !(startCheck ch h') then c := { c.fail "TX 0: the start" with s := c.s + 1 }
    else
      c := { c with txs := c.txs + 1, news := c.news + ch.new.length,
                    adds := c.adds + ch.adds.length, touch := c.touch + ch.touch.length }
      let s := h.tree
      let s' := h'.tree
      if !(newsOk topLevel s s' ch && madeCheck h h' ch) then
        c := { c.fail s!"TX {i}: N, the nodes made" with n := c.n + 1 }
      if !(addsOk s s' d ch) then c := { c.fail s!"TX {i}: K, the entries added" with k := c.k + 1 }
      if !(localOk i s s' d) then c := { c.fail s!"TX {i}: L, the key nodes of D" with l := c.l + 1 }
      let now := nodesAt (s'.at i)
      let before := nodesAt (s.at (i - 1))
      if !(currentOk (s'.at i) ch now) then c := { c.fail s!"TX {i}: A2" with a2 := c.a2 + 1 }
      if !(madeOk (s'.at i) ch now) then c := { c.fail s!"TX {i}: A3" with a3 := c.a3 + 1 }
      if !(noResOk ch before now) then c := { c.fail s!"TX {i}: A5" with a5 := c.a5 + 1 }
    h := h'
    dirtyBefore := tx.dirty
    pos := pos + 1
  return c

def main (args : List String) : IO UInt32 := do
  let mut failed := 0
  let mut total : BCounts := {}
  for path in args do
    let lines ← IO.FS.lines path
    let old := SIS.Check.parseTrace (← IO.FS.readFile path)
    match readTrace lines with
    | .error e =>
      IO.println s!"{path}: unreadable: {e}"
      failed := failed + 1
    | .ok tr =>
      let c := checkBridgeTrace tr old
      let bad := c.s + c.n + c.k + c.l + c.a2 + c.a3 + c.a5
      IO.println s!"{path}: {c.txs} transactions, {c.news} nodes made, {c.adds} entries, {c.touch} touched; failures: start {c.s}, N {c.n}, K {c.k}, L {c.l}, A2 {c.a2}, A3 {c.a3}, A5 {c.a5}{match c.first with | some m => "; first: " ++ m | none => ""}"
      if bad != 0 || c.txs == 0 || !old.bad.isEmpty then failed := failed + 1
      total := { total with txs := total.txs + c.txs, news := total.news + c.news,
                            adds := total.adds + c.adds, touch := total.touch + c.touch,
                            s := total.s + c.s, n := total.n + c.n, k := total.k + c.k,
                            l := total.l + c.l, a2 := total.a2 + c.a2, a3 := total.a3 + c.a3,
                            a5 := total.a5 + c.a5 }
  IO.println s!"total: {args.length} traces, {total.txs} transactions, {total.news} nodes made, {total.adds} entries, {total.touch} touched; failures: start {total.s}, N {total.n}, K {total.k}, L {total.l}, A2 {total.a2}, A3 {total.a3}, A5 {total.a5}"
  if failed == 0 then
    IO.println "BRIDGE OK"
    return 0
  else
    IO.println s!"BRIDGE FAILED: {failed} traces"
    return 1
