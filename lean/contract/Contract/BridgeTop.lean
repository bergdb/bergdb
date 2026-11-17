/-
The contract package (bergdb 030-07): the bridge over the contract's top
(bergdb 030-08, Top.lean). To read and to trust, with Bridge.lean.

Bridge.lean takes what the abstract model assumes of the root and the top
nodes as a premise in the model's words (`TopOK`). Since 030-08 the top nodes
are in the contract's state (`Top`), with their clauses (`TopStart`,
`TopStep`: at most one top node made a transaction, the old ones fixed, the
skip pointers as `TopDs.newSuperRoot` makes them). Here the premise is
replaced by those clauses and one more, clause TB, which says that the
change's part for the root and the top nodes is what the top's step is:

* TB1. No node made has the root's id, 0, or a top node's; a node made that
  is a node of the tree (a key node or a value) has a level below the top
  nodes' level.
* TB2. If the transaction makes no top node, every node made and every entry
  added is a node's of the tree.
* TB3. If it makes the top node z, the change makes exactly one node that is
  no node of the tree, z, on a level above every top node's before it and
  below the root's; z's entries are its root pointer and then its skip
  pointers, in their order; the root's entries are the one for z; every other
  entry is a node's of the tree.

The levels are the model's (the trace's NEW lines): a top node's level is the
top nodes' level plus its ordinal, so later top nodes are on higher levels.

`MeetsBridgeTop`: a history, with the top after each transaction, that meets
the writer's contract, the computed clauses of the bridge, `Made`, the touch
rules, 030-08's top clauses and TB. Proof/BridgeTop.lean proves that it meets
`MeetsBridge` (`MeetsBridgeTop.meetsBridge`): `TopOK` is then a theorem, and
the theorems of BridgeTheorems.lean hold with no premise in the model's words
about the top.
-/
import Contract.Bridge
import Contract.ShapeStatement

namespace Contract

open SIS (Struct Changes Entry History Node NewNode Spec)
open SIS.Check (BVal)

/-- The model's entry values of a top node: its root pointer, then its skip
pointers in their order (bergdb 027-02, section 1: `R y`, `S j z`). -/
def topVals (n : TopNode) : List BVal :=
  .rootKey n.root :: n.skips.map (fun q => .skip q.1 q.2.1)

/-- The level of a node in the model's structure, 0 if it is no node. -/
def levelIn (P : Struct BVal) (x : NodeId) : Nat :=
  match P.get? x with
  | some n => n.level
  | none => 0

/-- Clause TB, computed, for the change c of a transaction: P is the model's
structure before it, s' the tree after it, tp and tp' the top before and
after it. -/
def topChangeOk (topLevel : Nat) (P : Struct BVal) (s' : Tree) (tp tp' : Top)
    (c : Changes BVal) : Bool :=
  c.new.all (fun nn => nn.id != SIS.root && (tp.node nn.id).isNone &&
    ((s'.obj nn.id).isNone || decide (nn.level < topLevel))) &&
  (if tp' == tp then
    c.new.all (fun nn => (s'.obj nn.id).isSome) && c.adds.all (fun a => (s'.obj a.1).isSome)
  else
    match tp'.getLast?, c.new.filter (fun nn => (s'.obj nn.id).isNone) with
    | some (z, n), [nn] =>
      nn.id == z && tp.all (fun zm => decide (levelIn P zm.1 < nn.level)) &&
      decide (nn.level < levelIn P SIS.root) &&
      (c.adds.filter (fun a => a.1 == z)).map (·.2) == topVals n &&
      (c.adds.filter (fun a => a.1 == SIS.root)).map (·.2) == [.top z] &&
      c.adds.all (fun a => (s'.obj a.1).isSome || a.1 == z || a.1 == SIS.root)
    | _, _ => false)

/-- The start's top, computed: one top node, the one that the primordial
change makes, of time 0 and without skip pointers; the start tree's space
root is its root pointer. -/
def topStartOk (c0 : Changes BVal) (tp0 : Top) (s0 : Tree) : Bool :=
  match tp0, c0.adds with
  | [(z, n)], [(_, .top z'), _] =>
    z == z' && n.time == 0 && n.skips.isEmpty && s0.roots == rootsOf tp0
  | _, _ => false

/-- A history, with the top after each transaction (`top j`: after the first
j), that meets the contract, the bridge's clauses about key nodes and values,
the touch rules, and the top's clauses of 030-08 with clause TB. -/
structure MeetsBridgeTop (p : Params) (h : BHist) (top : Nat → Top) : Prop where
  start : StartB h
  startTop : topStartOk h.c0 (top 0) h.s0 = true
  step : ∀ j (hj : j < h.txs.length),
    Contract p (j + 1) (h.tree j) h.txs[j].ops h.txs[j].D (h.tree (j + 1)) ∧
    bridgeOk h.topLevel (j + 1) (h.tree j) (h.tree (j + 1)) h.txs[j].D h.txs[j].c = true ∧
    Made (h.tree j) (h.tree (j + 1)) h.txs[j].c ∧
    TopStep (j + 1) (top j) (top (j + 1)) ∧
    (h.tree (j + 1)).roots = rootsOf (top (j + 1)) ∧
    topChangeOk h.topLevel (h.P j) (h.tree (j + 1)) (top j) (top (j + 1)) h.txs[j].c = true ∧
    TouchOK h.spec (h.P j) (j + 1) h.txs[j].c

/-! ## The touch, A6' and A-COPY in the contract's words

English. With the top in the contract's state, the three clauses that
Bridge.lean takes in the model's words can be said of the tree and its top.
"Reached" is the walk of TREE (`reach`); "below x" is the walk from x
(`reachAt`); the super root is the last top node.

* The touch (`touchOk`), on the tree and the top before the transaction, at
  time i - 1. A touched node is the super root or a key node that the tree
  reaches. If any node is touched, the super root is; and every key node
  reached with a touched node below it is touched.
* A6' (`adoptOk`), on the tree after the transaction, at time i. For every
  key node x reached and every key klong of x, live or dead, with pointee y:
  y is a live pointee of x, or a value, or not reached, or below x.
* A-COPY (`copyOk`). Call a node of the writer's paths a node that the tree
  reached at time i - 1 and that the transaction gives an entry, touches, or
  leaves unreached at time i. A key entry added, or the root pointer of a top
  node made, names a node made, a node of the writer's paths, the pointee of
  a key klong of a key node of the writer's paths, or, if the transaction
  makes a top node, the space root before it (the root pointer of the super
  root before, which the transaction replaces). A skip pointer of a top node
  made names the super root before it, or the pointee of one of that node's
  skip pointers (`TopDs.newSuperRoot`). -/

/-- The super root: the last top node. -/
def superRoot (tp : Top) : Option NodeId := tp.getLast?.map (·.1)

/-- The touch rules, in the contract's words, computed. -/
def touchOk (s : Tree) (tp : Top) (touch : List NodeId) : Bool :=
  let rl := reach s
  touch.all (fun x => superRoot tp == some x ||
    (match s.obj x with
      | some (.key _) => rl.contains x
      | _ => false)) &&
  (touch.isEmpty ||
    ((match superRoot tp with
      | some z => touch.contains z
      | none => false) &&
     rl.all (fun q => touch.contains q ||
      (match s.obj q with
        | some (.key _) =>
          let below := reachAt s (s.fuel q) q
          touch.all (fun x => !below.contains x)
        | _ => true))))

/-- A6', in the contract's words, computed. -/
def adoptOk (s : Tree) : Bool :=
  let rl := reach s
  rl.all (fun x => match s.obj x with
    | some (.key n) =>
      let lv := (live n.ks).map (·.2)
      let below := reachAt s (s.fuel x) x
      n.ks.all (fun k => match k with
        | .key _ y => lv.contains y ||
            (match s.obj y with
              | some (.val _) => true
              | _ => false) || !rl.contains y || below.contains y
        | _ => true)
    | _ => true)

/-- A key node of the tree has a key klong with pointee y. -/
def namesKey (s : Tree) (z y : NodeId) : Bool :=
  match s.obj z with
  | some (.key n) => n.ks.any (fun k => match k with
    | .key _ y' => y' == y
    | _ => false)
  | _ => false

/-- A-COPY, in the contract's words, computed: s and tp before the
transaction at time i, s' after it, c its change. -/
def copyOk (i : Nat) (s s' : Tree) (tp : Top) (c : Changes BVal) : Bool :=
  let before := reach (s.at (i - 1))
  let now := reach (s'.at i)
  let path := before.filter (fun x => c.adds.any (fun a => a.1 == x) || c.touch.contains x ||
    !now.contains x)
  let topMade := c.adds.any (fun a => match a.2 with
    | .top _ => true
    | _ => false)
  let named := fun y => c.new.any (fun nn => nn.id == y) || path.contains y ||
    path.any (fun z => namesKey s z y) ||
    (topMade && match tp.getLast? with
      | some (_, nw) => nw.root == y
      | none => false)
  c.adds.all (fun a => match a.2 with
    | .key _ y => named y
    | .rootKey y => named y
    | .skip _ y =>
      match tp.getLast? with
      | some (w, nw) => y == w || nw.skips.any (fun q => q.2.1 == y)
      | none => false
    | _ => true)

/-- A history, with the top after each transaction, that meets every clause,
each in the contract's words: the writer's contract, the bridge's clauses
about key nodes and values, 030-08's top clauses with TB, the touch, TREE,
A6' and A-COPY. Proof/BridgeWords.lean proves that it meets `MeetsBridge`
and `MeetsEvict` (`MeetsFull.meetsBridge`, `MeetsFull.meetsEvict`), so every
theorem of BridgeTheorems.lean holds for it. -/
structure MeetsFull (p : Params) (h : BHist) (top : Nat → Top) : Prop where
  start : StartB h
  startTop : topStartOk h.c0 (top 0) h.s0 = true
  step : ∀ j (hj : j < h.txs.length),
    Contract p (j + 1) (h.tree j) h.txs[j].ops h.txs[j].D (h.tree (j + 1)) ∧
    bridgeOk h.topLevel (j + 1) (h.tree j) (h.tree (j + 1)) h.txs[j].D h.txs[j].c = true ∧
    Made (h.tree j) (h.tree (j + 1)) h.txs[j].c ∧
    TopStep (j + 1) (top j) (top (j + 1)) ∧
    (h.tree (j + 1)).roots = rootsOf (top (j + 1)) ∧
    topChangeOk h.topLevel (h.P j) (h.tree (j + 1)) (top j) (top (j + 1)) h.txs[j].c = true ∧
    touchOk ((h.tree j).at j) (top j) h.txs[j].c.touch = true ∧
    copyOk (j + 1) (h.tree j) (h.tree (j + 1)) (top j) h.txs[j].c = true
  tree : ∀ j, j ≤ h.txs.length → TreeOk ((h.tree j).at j)
  adopt : ∀ j, j ≤ h.txs.length → adoptOk ((h.tree j).at j) = true

end Contract
