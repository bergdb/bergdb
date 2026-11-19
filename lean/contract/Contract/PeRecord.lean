/-
bergdb 030-21, part 2: PE's record in the model's words, for `MeetsFull`
(BridgeTop.lean): what each transaction of PE changes, as the model's
`Changes` (the trace's NEW and ADD lines; bergdb 027-02), and the history of
a run of PE as a `BHist` with its tops.

* The start (`c0`): Java's primordial structure, as `StartB` asks: the root
  (node 0) on the root's level, the space root (node 1, PE's empty segment
  leaf) on segment 0's leaf level, and the start top node (node 2) on the top
  nodes' level, which names it; the root names the top node.
* A transaction (`peChange`): the nodes it made (each fresh id it wrote, with
  its level, a value as a data node; the new top node, on the top nodes'
  level plus its ordinal), and the entries it added: for each node written,
  in the order written, the entries of the klongs it got (`newVals`); for a
  new top node, the root's entry for it and its root and skip pointers. No
  touch: PE's transactions touch nothing (no reclaim step).
* The levels are the model's (lean/SIS/Tree/Node.lean): the top nodes' level
  is one above the largest key level, the root's above every top node of
  fewer than 2^48 (`Params.topLevel`, `Params.rootLevel`).
-/
import Contract.PeStatement
import Contract.BridgeTop

namespace Contract.PE

open SIS (Changes NewNode)
open SIS.Check (BVal)

/-- The largest level of a key node (`Params.keyMax`). -/
def Cfg.keyMax (cf : Cfg) : Nat := 1 + cf.G * (cf.H + 1) + cf.H

/-- The level of the start top node, ordinal 0 (`Params.topLevel 0`). -/
def Cfg.topBase (cf : Cfg) : Nat := cf.keyMax + 1

/-- The root's level (`Params.rootLevel`). -/
def Cfg.rootLevel (cf : Cfg) : Nat := cf.keyMax + 2 + (2 ^ 48 - 1)

/-- The primordial change: the root, the space root (node 1), the start top
node (node 2); the root's entry for the top node, the top node's root
pointer. -/
def c0 (cf : Cfg) : Changes BVal :=
  { new := [⟨0, cf.rootLevel, false⟩, ⟨1, cf.lev 0 0, false⟩, ⟨2, cf.topBase, false⟩],
    adds := [(0, .top 2), (2, .rootKey 1)],
    touch := [] }

/-- The top node a transaction made, if any: the last of the top after it,
if the top grew. -/
def newTopOf (tp : Top) (o : Out) : Option (NodeId × TopNode) :=
  if o.top.length = tp.length then none else o.top.getLast?

/-- The level of node x of a tree in the model, and whether it is a data
node. -/
def lvlOf (T : Tree) (x : NodeId) : Nat :=
  match T.obj x with
  | some ob => lvl ob
  | none => 0

def isDataOf (T : Tree) (x : NodeId) : Bool :=
  match T.obj x with
  | some (.val _) => true
  | _ => false

/-- PE's change of a transaction from the tree s with the top tp, which gave
o: the nodes made and the entries added, in the model's words. -/
def peChange (cf : Cfg) (s : Tree) (tp : Top) (o : Out) : Changes BVal :=
  let T := o.tree s
  let xs := (o.ws.map (·.1)).reverse
  { new := (xs.filter (fun x => (s.obj x).isNone)).map (fun x => ⟨x, lvlOf T x, isDataOf T x⟩) ++
      (match newTopOf tp o with
       | some (z, _) => [⟨z, cf.topBase + tp.length, false⟩]
       | none => []),
    adds := xs.flatMap (fun x => (newVals s T x).map (fun v => (x, v))) ++
      (match newTopOf tp o with
       | some (z, n) => (0, BVal.top z) :: (topVals n).map (fun v => (z, v))
       | none => []),
    touch := [] }

/-- A run of PE from the tree s with the top tp and the next id nx, the
transactions at times i + 1, i + 2, ...: each transaction with its operations,
its dirty nodes, its tree and its change, and the top after it; none if PE
refuses one. -/
def peRun (cf : Cfg) : Tree → Top → NodeId → Time → List (List Op) → Option (List (BTx × Top))
  | _, _, _, _, [] => some []
  | s, tp, nx, i, ops :: rest =>
    match peTx cf (i + 1) s tp nx ops with
    | none => none
    | some o =>
      (peRun cf (o.tree s) o.top o.next (i + 1) rest).map
        (fun L => (⟨ops, o.D, o.tree s, peChange cf s tp o⟩, o.top) :: L)

/-- The history of a run of PE from the empty tree, with the top after the
first j transactions (`top j`). -/
def peHist (cf : Cfg) (txs : List (List Op)) : Option (BHist × (Nat → Top)) :=
  (peRun cf (startTree cf) startTop startNext 0 txs).map (fun L =>
    (⟨startTree cf, c0 cf, L.map (·.1)⟩,
     fun j => match j with
       | 0 => startTop
       | j + 1 => ((L[j]?).map (·.2)).getD startTop))

/-- PE's kinds by level (K-LEVEL, Recover.lean): a key node is a segment leaf
exactly at height 0. -/
def peKind (cf : Cfg) (l : Nat) : Bool := cf.htOf l == 0

end Contract.PE
