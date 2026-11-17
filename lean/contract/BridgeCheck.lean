/-
The bridge checker (bergdb 030-07): `lake exe bridgecheck [--model] TRACE...`
reads traces of format 3 (bergdb 027-02) and checks, for every traced
transaction alone, on Java's tree and top before and after it and the
transaction's NEW, ADD and TOUCH lines, the clauses of the bridge, each in
the contract's words (Contract/Bridge.lean, Contract/BridgeTop.lean):

* N, the nodes made (`newsOk`, `madeCheck`);
* K, the entries added are those of the klongs added (`addsOk`);
* L, for the key nodes of D: F4, W1 to W5 and A4 (`localOk`);
* A2, A3, A5 (`currentOk`, `madeOk`, `noResOk`);
* TREE after the transaction (`treeOkB`, bergdb 030-08);
* TB, the top: 030-08's step of the top (`topStepB`) with the top that the
  trace's lines give (`applyTop`), the tree's space roots are the top's, and
  clause TB (`topChangeOk`);
* TOUCH, A6' and COPY (`touchOk`, `adoptOk`, `copyOk`);
* KIND, K-LEVEL (bergdb 030-14): every key node of D has the kind that its
  level gives with the TREE line's h (`kindsOk`, `kindOfHeight`);

and for TX 0 the start (`startCheck`, `topStartOk`), TREE, A6' and KIND. Then the
verdict on the whole trace as one value (`fullHistoryOk`, with the writer's
contract for every transaction), which gives a history that meets every
clause (`MeetsFull`: `fullHistoryOk_meets`), and so `MeetsBridge` and
`MeetsEvict`; and the verdict on K-LEVEL (`kindsHistoryOk`, which gives
`KindsOK`: `kindsHistoryOk_meets`).

With `--model` as the first argument also the clauses in the model's words, on
the model's structure before and after the transaction (the trace checker's:
the changes applied in order; Contract/BridgeModel.lean): the top's clauses
(`topOkB`), the touch rules (`touchB`), A6' (`adoptB`) and A-COPY in its
sufficient form (`copyB`); and the verdict that gives `MeetsBridge` and
`MeetsEvict` from them (`bridgeHistoryOk`). They follow from the clauses
above (Proof/BridgeTop.lean, Proof/BridgeWords.lean); the checks take about
twice as long.

D is as in the contract checker: D after the record before and the nodes
that got dirty. Prints one line per trace and BRIDGE OK or BRIDGE FAILED; a
failure names the trace and the transaction.

Before that, the trace must be whole, as for the contract checker
(`completeFault`, Complete.lean; bergdb 030-11, finding 4): no ERROR line, no
line of an unknown kind, the transactions numbered 0, 1, 2, ... and a DONE
line naming the last.
-/
import Contract.Complete
import Contract.BridgeHeap
import Contract.Trace
import Contract.TraceTop
import Contract.RecoverCheck

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
  tree : Nat := 0
  tb : Nat := 0
  tch : Nat := 0
  a6 : Nat := 0
  copy : Nat := 0
  mtop : Nat := 0
  mtch : Nat := 0
  ma6 : Nat := 0
  mcopy : Nat := 0
  kd : Nat := 0
  first : Option String := none

def BCounts.fail (c : BCounts) (msg : String) : BCounts :=
  { c with first := c.first.orElse (fun _ => some msg) }

def BCounts.bad (c : BCounts) : Nat :=
  c.s + c.n + c.k + c.l + c.a2 + c.a3 + c.a5 + c.tree + c.tb + c.tch + c.a6 + c.copy +
    c.mtop + c.mtch + c.ma6 + c.mcopy + c.kd

def BCounts.show (c : BCounts) (model : Bool) : String :=
  s!"{c.txs} transactions, {c.news} nodes made, {c.adds} entries, {c.touch} touched; failures: start {c.s}, N {c.n}, K {c.k}, L {c.l}, A2 {c.a2}, A3 {c.a3}, A5 {c.a5}, TREE {c.tree}, TB {c.tb}, TOUCH {c.tch}, A6' {c.a6}, COPY {c.copy}, KIND {c.kd}" ++
  (if model then s!"; in the model's words: TOP {c.mtop}, TOUCH {c.mtch}, A6' {c.ma6}, COPY {c.mcopy}" else "")

def BCounts.add (a c : BCounts) : BCounts :=
  { txs := a.txs + c.txs, news := a.news + c.news, adds := a.adds + c.adds,
    touch := a.touch + c.touch, s := a.s + c.s, n := a.n + c.n, k := a.k + c.k, l := a.l + c.l,
    a2 := a.a2 + c.a2, a3 := a.a3 + c.a3, a5 := a.a5 + c.a5, tree := a.tree + c.tree,
    tb := a.tb + c.tb, tch := a.tch + c.tch, a6 := a.a6 + c.a6, copy := a.copy + c.copy,
    mtop := a.mtop + c.mtop, mtch := a.mtch + c.mtch, ma6 := a.ma6 + c.ma6,
    mcopy := a.mcopy + c.mcopy, kd := a.kd + c.kd }

def checkBridgeTrace (model : Bool) (tr : Trace) (old : SIS.Check.Trace) : BCounts := Id.run do
  let chs := old.recs.map SIS.Check.changesOf
  let c0 := chs.getD 0 { new := [], adds := [] }
  let p0 := SIS.Struct.apply (V := SIS.Check.BVal) [] 0 c0
  let sp := SIS.Check.bspec chs p0 true
  let topLevel := sp.topLevel
  let kind := kindOfHeight tr.shape.H
  let mut P := p0
  let mut tp : Top := []
  let mut tp0 : Top := []
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
      tp0 := tp'
      if !(startCheck ch h') then c := { c.fail "TX 0: the start" with s := c.s + 1 }
      if !(topStartOk ch tp' h'.tree) then c := { c.fail "TX 0: TB, the start's top" with tb := c.tb + 1 }
      if !(treeOkB (h'.tree.at 0)) then c := { c.fail "TX 0: TREE" with tree := c.tree + 1 }
      if !(adoptOk (h'.tree.at 0)) then c := { c.fail "TX 0: A6'" with a6 := c.a6 + 1 }
      if !(startKindsOk kind h') then c := { c.fail "TX 0: KIND" with kd := c.kd + 1 }
      if model then
        if !(adoptB sp p0 0) then c := { c.fail "TX 0: A6' in the model's words" with ma6 := c.ma6 + 1 }
    else
      steps := steps.push { ops := tx.ops, D := d, heap := h', c := ch, top := tp' }
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
      if !(treeOkB (s'.at i)) then c := { c.fail s!"TX {i}: TREE" with tree := c.tree + 1 }
      if !(topStepB i tp tp' && s'.roots == rootsOf tp' && topChangeOk topLevel P s' tp tp' ch) then
        c := { c.fail s!"TX {i}: TB, the top" with tb := c.tb + 1 }
      if !(touchOk (s.at (i - 1)) tp ch.touch) then c := { c.fail s!"TX {i}: TOUCH" with tch := c.tch + 1 }
      if !(adoptOk (s'.at i)) then c := { c.fail s!"TX {i}: A6'" with a6 := c.a6 + 1 }
      if !(copyOk i s s' tp ch) then c := { c.fail s!"TX {i}: COPY" with copy := c.copy + 1 }
      if !(kindsOk kind s' d) then c := { c.fail s!"TX {i}: KIND" with kd := c.kd + 1 }
      let P' := P.apply i ch
      if model then
        if !(topOkB sp P P' i s s' ch) then
          c := { c.fail s!"TX {i}: TOP in the model's words" with mtop := c.mtop + 1 }
        if !(touchB sp P i ch) then
          c := { c.fail s!"TX {i}: TOUCH in the model's words" with mtch := c.mtch + 1 }
        if !(adoptB sp P' i) then
          c := { c.fail s!"TX {i}: A6' in the model's words" with ma6 := c.ma6 + 1 }
        if !(copyB sp P P' i ch) then
          c := { c.fail s!"TX {i}: COPY in the model's words" with mcopy := c.mcopy + 1 }
      P := P'
    h := h'
    tp := tp'
    dirtyBefore := tx.dirty
    pos := pos + 1
  -- The verdicts on the whole trace: they hold if no clause above failed (and the writer's
  -- contract holds, which the contract checker reports by clause).
  if c.bad == 0 then
    if !(fullHistoryOk { M := tr.M } h0 c0 tp0 steps.toList) then
      c := { c.fail "the verdict on the whole trace (fullHistoryOk) fails" with s := c.s + 1 }
    if !(kindsHistoryOk kind h0 steps.toList) then
      c := { c.fail "the verdict on K-LEVEL (kindsHistoryOk) fails" with s := c.s + 1 }
    if model && !(bridgeHistoryOk { M := tr.M } h0 c0 steps.toList) then
      c := { c.fail "the verdict on the whole trace in the model's words (bridgeHistoryOk) fails" with s := c.s + 1 }
  return c

def main (args : List String) : IO UInt32 := do
  let model := args.head? == some "--model"
  let paths := if model then args.drop 1 else args
  let mut failed := 0
  let mut total : BCounts := {}
  for path in paths do
    let lines ← IO.FS.lines path
    if let some e := completeFault lines then
      IO.println s!"{path}: not whole: {e}"
      failed := failed + 1
    let old := SIS.Check.parseTrace (← IO.FS.readFile path)
    match readTrace lines with
    | .error e =>
      IO.println s!"{path}: unreadable: {e}"
      failed := failed + 1
    | .ok tr =>
      let c := checkBridgeTrace model tr old
      IO.println s!"{path}: {c.show model}{match c.first with | some m => "; first: " ++ m | none => ""}"
      if c.bad != 0 || c.txs == 0 || !old.bad.isEmpty then failed := failed + 1
      total := total.add c
  IO.println s!"total: {paths.length} traces, {total.show model}"
  if failed == 0 then
    IO.println "BRIDGE OK"
    return 0
  else
    IO.println s!"BRIDGE FAILED: {failed} traces"
    return 1
