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

end Contract
