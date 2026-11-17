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

and for TX 0 the start (`startCheck`); and, on the model's structure before
and after the transaction (the trace checker's: the changes applied in
order), the clauses in the model's words (Contract/BridgeModel.lean):

* TOP, the top's clauses (`topOkB`, which gives `TopOK`);
* TOUCH, the touch rules (`touchB`, which gives `TouchOK`);
* TREE, the contract's TREE after the transaction (`treeOkB`, bergdb 030-08);
* A6', after the transaction and at the start (`adoptB`);
* COPY, A-COPY in its sufficient form (`copyB`);
* TB, the top in the contract's words (BridgeTop.lean), with the top that the
  trace's lines give (`applyTop`, bergdb 030-08): 030-08's step of the top
  (`topStepB`), the tree's space roots are the top's, and clause TB
  (`topChangeOk`); for TX 0 `topStartOk`. These give `TopOK`
  (`MeetsBridgeTop.meetsBridge`).

Then the verdict on the whole trace as one value (`bridgeHistoryOk`, with the
writer's contract for every transaction), which gives a history that meets
`MeetsBridge` and `MeetsEvict` (`bridgeHistoryOk_meets`). D is as in the
contract checker: D after the record before and the nodes that got dirty. Prints one line per trace and BRIDGE OK or BRIDGE FAILED; a
failure names the trace and the transaction. With `--tree` as the first
argument the clauses on the model's structure are left out (they take
longer).
-/
import Contract.BridgeHeap
import Contract.BridgeModel
import Contract.BridgeTop
import Contract.Trace
import Contract.TraceTop

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
  top : Nat := 0
  tch : Nat := 0
  tree : Nat := 0
  a6 : Nat := 0
  copy : Nat := 0
  tb : Nat := 0
  first : Option String := none

def BCounts.fail (c : BCounts) (msg : String) : BCounts :=
  { c with first := c.first.orElse (fun _ => some msg) }

def checkBridgeTrace (model : Bool) (tr : Trace) (old : SIS.Check.Trace) : BCounts := Id.run do
  let chs := old.recs.map SIS.Check.changesOf
  let p0 := SIS.Struct.apply (V := SIS.Check.BVal) [] 0 (chs.getD 0 { new := [], adds := [] })
  let sp := SIS.Check.bspec chs p0 true
  let topLevel := sp.topLevel
  let mut P := p0
  let mut tp : Top := []
  let mut h : Heap := {}
  let mut h0 : Heap := {}
  let mut steps : Array TStep := #[]
  let mut c : BCounts := {}
  let mut dirtyBefore : List NodeId := []
  let mut pos := 0
  for tx in tr.txs do
    let d := dirtyBefore ++ tx.gd
    let h' := applyTx h tx
    let tp' := applyTop tp tx
    let i := tx.i
    let ch := chs.getD pos { new := [], adds := [] }
    if (old.recs.getD pos default).idx != i then
      c := { c.fail s!"TX {i}: the two readers differ" with s := c.s + 1 }
    if i == 0 then
      h0 := h'
      if !(startCheck ch h') then c := { c.fail "TX 0: the start" with s := c.s + 1 }
      if model then
        if !(treeOkB (h'.tree.at 0)) then c := { c.fail "TX 0: TREE" with tree := c.tree + 1 }
        if !(adoptB sp p0 0) then c := { c.fail "TX 0: A6'" with a6 := c.a6 + 1 }
        if !(topStartOk ch tp' h'.tree) then c := { c.fail "TX 0: TB, the start's top" with tb := c.tb + 1 }
    else
      steps := steps.push { ops := tx.ops, D := d, heap := h', c := ch }
      c := { c with txs := c.txs + 1, news := c.news + ch.new.length,
                    adds := c.adds + ch.adds.length, touch := c.touch + ch.touch.length }
      let s := h.tree
      let s' := h'.tree
      if !(newsOk topLevel s s' ch && madeCheck h h' ch) then
        c := { c.fail s!"TX {i}: N, the nodes made" with n := c.n + 1 }
      if !(addsOk s s' d ch) then c := { c.fail s!"TX {i}: K, the entries added" with k := c.k + 1 }
      if !(localOk i s s' d) then c := { c.fail s!"TX {i}: L, the key nodes of D" with l := c.l + 1 }
      let now := reach (s'.at i)
      let before := reach (s.at (i - 1))
      if !(currentOk (s'.at i) ch now) then c := { c.fail s!"TX {i}: A2" with a2 := c.a2 + 1 }
      if !(madeOk (s'.at i) ch now) then c := { c.fail s!"TX {i}: A3" with a3 := c.a3 + 1 }
      if !(noResOk ch before now) then c := { c.fail s!"TX {i}: A5" with a5 := c.a5 + 1 }
      if model then
        let P' := P.apply i ch
        if !(topOkB sp P P' i s s' ch) then c := { c.fail s!"TX {i}: TOP" with top := c.top + 1 }
        if !(touchB sp P i ch) then c := { c.fail s!"TX {i}: TOUCH" with tch := c.tch + 1 }
        if !(treeOkB (s'.at i)) then c := { c.fail s!"TX {i}: TREE" with tree := c.tree + 1 }
        if !(adoptB sp P' i) then c := { c.fail s!"TX {i}: A6'" with a6 := c.a6 + 1 }
        if !(copyB sp P P' i ch) then c := { c.fail s!"TX {i}: COPY" with copy := c.copy + 1 }
        if !(topStepB i tp tp' && s'.roots == rootsOf tp' && topChangeOk topLevel P s' tp tp' ch) then
          c := { c.fail s!"TX {i}: TB, the top in the contract's words" with tb := c.tb + 1 }
        -- The clauses as one value each (`checkBridgeTx_sound`, `checkEvictTx_sound`).
        if checkBridgeTx sp P i h d h' ch != (bridgeOk topLevel i s s' d ch && madeCheck h h' ch &&
            topOkB sp P P' i s s' ch && touchB sp P i ch) ||
           checkEvictTx sp P i h' ch != (treeOkB (s'.at i) && adoptB sp P' i && copyB sp P P' i ch) then
          c := { c.fail s!"TX {i}: a check differs from its parts" with s := c.s + 1 }
        P := P'
    h := h'
    tp := tp'
    dirtyBefore := tx.dirty
    pos := pos + 1
  -- The verdict on the whole trace, which gives `MeetsBridge` and `MeetsEvict`
  -- (`bridgeHistoryOk_meets`): it holds if no clause above failed.
  if model then
    let bad := c.s + c.n + c.k + c.l + c.a2 + c.a3 + c.a5 + c.top + c.tch + c.tree + c.a6 + c.copy + c.tb
    if bad == 0 && !(bridgeHistoryOk { M := tr.M } h0 (chs.getD 0 { new := [], adds := [] }) steps.toList) then
      c := { c.fail "the verdict on the whole trace (bridgeHistoryOk) fails" with s := c.s + 1 }
  return c

def main (args : List String) : IO UInt32 := do
  let model := args.head? != some "--tree"
  let paths := if model then args else args.drop 1
  let mut failed := 0
  let mut total : BCounts := {}
  for path in paths do
    let lines ← IO.FS.lines path
    let old := SIS.Check.parseTrace (← IO.FS.readFile path)
    match readTrace lines with
    | .error e =>
      IO.println s!"{path}: unreadable: {e}"
      failed := failed + 1
    | .ok tr =>
      let c := checkBridgeTrace model tr old
      let bad := c.s + c.n + c.k + c.l + c.a2 + c.a3 + c.a5 + c.top + c.tch + c.tree + c.a6 + c.copy + c.tb
      IO.println s!"{path}: {c.txs} transactions, {c.news} nodes made, {c.adds} entries, {c.touch} touched; failures: start {c.s}, N {c.n}, K {c.k}, L {c.l}, A2 {c.a2}, A3 {c.a3}, A5 {c.a5}, TOP {c.top}, TOUCH {c.tch}, TREE {c.tree}, A6' {c.a6}, COPY {c.copy}, TB {c.tb}{match c.first with | some m => "; first: " ++ m | none => ""}"
      if bad != 0 || c.txs == 0 || !old.bad.isEmpty then failed := failed + 1
      total := { total with txs := total.txs + c.txs, news := total.news + c.news,
                            adds := total.adds + c.adds, touch := total.touch + c.touch,
                            s := total.s + c.s, n := total.n + c.n, k := total.k + c.k,
                            l := total.l + c.l, a2 := total.a2 + c.a2, a3 := total.a3 + c.a3,
                            a5 := total.a5 + c.a5, top := total.top + c.top,
                            tch := total.tch + c.tch, tree := total.tree + c.tree,
                            a6 := total.a6 + c.a6, copy := total.copy + c.copy,
                            tb := total.tb + c.tb }
  IO.println s!"total: {paths.length} traces, {total.txs} transactions, {total.news} nodes made, {total.adds} entries, {total.touch} touched; failures: start {total.s}, N {total.n}, K {total.k}, L {total.l}, A2 {total.a2}, A3 {total.a3}, A5 {total.a5}, TOP {total.top}, TOUCH {total.tch}, TREE {total.tree}, A6' {total.a6}, COPY {total.copy}, TB {total.tb}{if model then "" else " (the model's clauses left out)"}"
  if failed == 0 then
    IO.println "BRIDGE OK"
    return 0
  else
    IO.println s!"BRIDGE FAILED: {failed} traces"
    return 1
