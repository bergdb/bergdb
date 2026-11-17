/-
The contract package (bergdb 030-10): the model's writer against the writer's
contract. To read and to trust for 030-10, with Statement.lean,
ShapeStatement.lean and the model's writer itself (lean/SIS/Tree/Exec.lean,
`runOpsFrom`, the run of `Tree.exec?`).

The model's writer (bergdb 024-12) is Java's `Dag.putKv` and everything below
it, restated step by step; Java matches it node for node on the traces
(`treecheck`). The contract says what must hold when a transaction ends.
This file says how the two meet:

* Section 1, the refinement map. The writer's state within a transaction (`W`:
  the key nodes read, made or changed, as klongs; the values made; the nodes
  taken back; its top node) and the tree before the transaction give the
  contract's tree (`treeOf`), its top (`topOf`) and the dirty nodes
  (`dirtyOf`).
* Section 2, what the writer starts from (`Shows`): the model's view of
  P@(i-1) shows the contract's tree, and the writer's own books at the start
  of a transaction (`Books`).
* Section 3, the statement (`WriterMeets`): a transaction that the writer
  accepts ends in a state whose map meets the contract, TREE and the top's
  clauses, and the books again.

The definitions of section 1 run: `writercheck` (WriterCheck.lean) checks on
Java's traces that the map of the model's state after each transaction is
Java's tree, and the statement's premises and conclusions after every
operation. Nothing here needs Mathlib.
-/
import SIS.Tree.Exec
import Contract.ShapeStatement

namespace Contract

open SIS (View)
open SIS.Check (BVal)

/-! ## 1. The refinement map

English. The model has its own klongs, key nodes and operations, the same as
the contract's but for the key node's level, which the model keeps apart
(`W.gh`, `W.made`). After the writer's state w of a transaction at time i,
from the tree s:

* a node that the writer took back is no node;
* a key node of the writer's overlay (`W.nodes`: read, made or changed) is the
  key node with these klongs, with the level it had in s, or for a node made
  the level the writer gave it (`W.made`, the trace's NEW line);
* a value made is a value;
* any other node is as in s;
* the space roots are those of s, and one more of time i, the root pointer of
  the writer's top node, if the writer made a top node;
* the top is the top before, and the writer's top node if it made one;
* D is the overlay: every node the writer read, made or changed. (The
  contract's frame holds for any D that holds the nodes changed and the key
  nodes made; that the model's D is Java's is `treecheck`'s test.) -/

abbrev MKlong := SIS.Tree.Klong
abbrev MNode := SIS.Tree.KNode
abbrev MOp := SIS.Tree.Op
abbrev MParams := SIS.Tree.Params
abbrev MW := SIS.Tree.W

/-- A klong of the model as the contract's. -/
def kOf : MKlong → Klong
  | .time t => .time t
  | .key c y => .key c y
  | .del b => .del b

/-- An operation of the model as the contract's. -/
def opOf : MOp → Op
  | .put k h => .put k h
  | .del k => .del k

/-- The level of key node x of the writer's state: the level it had in s; for
a node made, the level the writer gave it. -/
def wLevel (s : Tree) (w : MW) (x : NodeId) : Nat :=
  match s.obj x with
  | some (.key n) => n.level
  | _ =>
    match w.made.find? (fun m => m.id == x) with
    | some m => m.level
    | none => 0

/-- The contract's tree of the writer's state w at time i, from the tree s. -/
def treeOf (i : Time) (s : Tree) (w : MW) : Tree :=
  { obj := fun x =>
      if w.taken.contains x then none else
        match w.nodes.lookup x with
        | some n => some (.key { level := wLevel s w x, leaf := n.leaf, ks := n.ks.map kOf })
        | none =>
          match w.vals.lookup x with
          | some h => some (.val h)
          | none => s.obj x,
    roots := if w.newTop then s.roots ++ [(i, w.top.rootKey)] else s.roots }

/-- The contract's top of the writer's state w at time i, from the top tp: a
skip pointer caches the root time of the top node it names. -/
def topOf (i : Time) (tp : Top) (w : MW) : Top :=
  if w.newTop then
    tp ++ [(w.top.id, { time := i, root := w.top.rootKey,
                        skips := w.top.skips.map (fun q =>
                          (q.1, q.2, ((tp.node q.2).map (·.time)).getD 0)) })]
  else tp

/-- D of the writer's state: its overlay. -/
def dirtyOf (w : MW) : List NodeId := w.nodes.map (·.1)

/-! ## 2. What the writer starts from

English. The model's writer reads the tree through a view of the abstract
model's structure P@(i-1), where a key node is its entries, and through its
super root, the last top node. `Shows`: the view shows the tree s with the top
tp to the writer:

* every key node of s is in the view an index node on its level, at most the
  largest level of a key node, whose entries give its klongs (`klongsOf`), a
  segment leaf exactly if its level says height 0;
* the writer's super root z is the last top node of tp, and the view gives it
  the root pointer, the root time and the skip pointers of that top node;
  its ordinal is whatever the view says (no clause of the contract needs it).

`Books`, the writer's own rules that it relies on at the start of the
transaction at time i with first id `base`, beside the contract's invariants:

* every time of a klong of s, and of a space root, is before i;
* every node of s and every top node has an id below `base`: the ids that the
  transaction makes are new;
* the space root of s is the root pointer of the last top node. -/

/-- The view v shows the tree s and the top tp, with super root z. -/
structure Shows (p : MParams) (v : View BVal) (z : NodeId) (s : Tree) (tp : Top) : Prop where
  key : ∀ x n, s.obj x = some (.key n) → ∃ nd, v x = some nd ∧ nd.isData = false ∧
    nd.level = n.level ∧ n.level ≤ p.keyMax ∧ (SIS.Tree.klongsOf nd.hist).map kOf = n.ks ∧
    n.leaf = (p.heightOf n.level == 0)
  top : ∃ t zn, SIS.Tree.topOf p v z = .ok t ∧ tp.getLast? = some (z, zn) ∧ t.id = z ∧
    t.time = zn.time ∧ t.rootKey = zn.root ∧ t.skips = zn.skips.map (fun q => (q.1, q.2.1))

/-- The time of every time klong of the klongs is before i. -/
def timesBefore (i : Time) (ks : List Klong) : Bool :=
  ks.all (fun k => match k with
    | .time t => decide (t < i)
    | _ => true)

/-- The writer's books at the start of the transaction at time i with the
first id `base`. -/
structure Books (i : Time) (base : NodeId) (s : Tree) (tp : Top) : Prop where
  times : ∀ x n, s.obj x = some (.key n) → timesBefore i n.ks = true
  rootTimes : ∀ r ∈ s.roots, r.1 < i
  ids : ∀ x, base ≤ x → s.obj x = none ∧ tp.node x = none
  roots : s.roots = rootsOf tp

end Contract
