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
import Contract.Shape

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

* every key node of s that is reached from the space root is in the view an
  index node on its level, at most the largest level of a key node, whose
  entries give its klongs (`klongsOf`), a segment leaf exactly if its level
  says height 0. (Only the nodes reached: the model's view, `SIS.view`, holds
  the nodes reachable at the time, and s keeps the nodes of earlier times
  too. Until a second independent review, 2026-11-17, this asked for every
  key node of s, which the model's own view does not meet after a split.)
* the writer's super root z is the last top node of tp, and the view gives it
  the root pointer, the root time and the skip pointers of that top node;
  its skip pointers have the indexes of the bits set in its ordinal, as
  `TopDs.newSuperRoot` makes them (the ordinal is the view's; the contract
  has none, and the writer needs this to make the next top node's lowest skip
  pointer name the super root).

`Books`, the writer's own rules that it relies on at the start of the
transaction at time i with first id `base`, beside the contract's invariants:

* every key node of s starts with a time klong, and every time of a klong
  of s, and of a space root, is before i;
* every node of s and every top node has an id below `base`: the ids that the
  transaction makes are new;
* the space roots of s are the root pointers of the top nodes, and each skip
  pointer of the last top node names a top node and caches its root time. -/

/-- The view v shows the tree s and the top tp, with super root z. -/
structure Shows (p : MParams) (v : View BVal) (z : NodeId) (s : Tree) (tp : Top) : Prop where
  key : ∀ x ∈ reach s, ∀ n, s.obj x = some (.key n) → ∃ nd, v x = some nd ∧ nd.isData = false ∧
    nd.level = n.level ∧ n.level ≤ p.keyMax ∧ (SIS.Tree.klongsOf nd.hist).map kOf = n.ks ∧
    n.leaf = (p.heightOf n.level == 0)
  top : ∃ t zn, SIS.Tree.topOf p v z = .ok t ∧ tp.getLast? = some (z, zn) ∧ t.id = z ∧
    t.time = zn.time ∧ t.rootKey = zn.root ∧ t.skips = zn.skips.map (fun q => (q.1, q.2.1)) ∧
    t.skips.map (·.1) = (List.range (SIS.Tree.topHeight t.ord)).filter (fun j => t.ord.testBit j)

/-- The time of every time klong of the klongs is before i. -/
def timesBefore (i : Time) (ks : List Klong) : Bool :=
  ks.all (fun k => match k with
    | .time t => decide (t < i)
    | _ => true)

/-- The writer's books at the start of the transaction at time i with the
first id `base`. -/
structure Books (i : Time) (base : NodeId) (s : Tree) (tp : Top) : Prop where
  first : ∀ x n, s.obj x = some (.key n) → ∃ t rest, n.ks = Klong.time t :: rest
  times : ∀ x n, s.obj x = some (.key n) → timesBefore i n.ks = true
  rootTimes : ∀ r ∈ s.roots, r.1 < i
  ids : ∀ x, base ≤ x → s.obj x = none ∧ tp.node x = none
  roots : s.roots = rootsOf tp
  skips : ∀ z zn, tp.getLast? = some (z, zn) → ∀ q ∈ zn.skips,
    (tp.node q.2.1).map (·.time) = some q.2.2

/-! ## 3. The statement

English. The parameters of the contract and of the writer's rules are the
model's: the node size M; H, m and theta.

### 3.1 Between two operations

`Mid`: what holds of the writer's state w between two operations of the
transaction at time i from the tree s with the top tp, after the operations
`done`. The times of s are before i and the writer makes no time after i, so
the tree at time i is the tree, and s at time i - 1 is s.

* J1. The map of w meets the contract's invariants.
* J2. Its contents are those of s with the operations done applied.
* J3. The frame, from s, with D the overlay.
* J4. TREE.
* J5. The top (`WTopInv`): either the writer has made no top node, and its
  super root is the one it started with; or it has made one, of time i, with
  a new id and skip pointers that meet the top's clause T3. With it the
  top's clauses hold (`TopStep`) and the space roots are the top's.
* BalancedOK, of the writer's own rules (Shape.lean), for the key nodes
  reached from the space root (`Balanced`): a key node has a level above 0
  and is a segment leaf exactly at height 0 of its segment tree, and a live
  klong of an inner node names a key node one level below it. (The other
  four rules of Shape.lean, the fill among them, are not here: see 3.3.)
* The writer's books within a transaction (`MidBooks`), B1 to B14:
  * B1. A key node of the overlay that is kept (not taken back) is a node of s
    exactly if its first time is not i: the nodes made are those of first
    time i.
  * B2. No klong of the overlay has a time after i.
  * B3. A node replaced (`W.madeFor`'s second) is a key node of s.
  * B4. No klong, live or dead, of a node kept names a node taken back.
  * B5. A node kept has the level of its segment and height (`W.gh`), which
    are within G and H, and is a segment leaf exactly at height 0.
  * B6. Every id of the state is below the next id, the top node's too if
    the writer made it; a node made has an id at or above the first id, and
    so has the next id.
  * B7. A key node of s in the overlay that is not reached has its klongs of
    s (a node replaced has lost its klongs of the transaction).
  * B8. A key node made and kept is reached (or is the top node).
  * B9. A node taken back was made by the transaction.
  * B10. A node of the overlay is a node of s or was made by the transaction.
  * B11. No key node was made outside the bounds G and H of the levels.
  * B12. A node made with a node it replaces is of that node's segment, at
    its height or above.
  * B13. A key node kept starts with a time klong.
  * B15 (`OldReach`, a field of `Mid` beside the books; the checker's B16).
    A node of s that is reached in the state's map was reached in s.
  * B14. The link of a key node made and kept: the klongs that name it are
    klongs of the transaction (after the last time klong, of time i), all in
    one node kept. (The checker's B15; its B14 is BalancedOK on the overlay.)

### 3.2 The statement

`OpStep`, one operation: from a state with `Mid`, an operation on a key as
`Keys.toSegments` makes it (`keyWf`) that the writer accepts (`putKv` gives
no error), and that leaves no key node outside G and H, ends in a state with
`Mid`, the operation done.

`WriterMeets`, one transaction: from a tree s and a top tp that meet the
contract's invariants, TREE and BalancedOK, with the books of a start
(`Books`), shown to the writer by its view (`Shows`): if the writer accepts
the operations one by one (`OpsRun`: each `putKv` gives no error, and no key
node is outside G and H after it), then the map of its last state meets the
writer's contract for the transaction, with TREE and the top's clauses, and
BalancedOK again.

### 3.3 What is not in it

* The fill (FillOK), the two live klongs of an inner root (RootsOK), the
  leftmost rule (LeftmostOK) and the bound on dead klongs (DeadOK). The writer
  checks what it relies on as it goes and gives an error (Java's `Bug`) where
  a rule fails: no sibling to merge with, an inner node without the empty
  key's klong, an emptied inner space root. A transaction with an error is not
  accepted, and the statement speaks of the accepted ones, as the contract
  does (bergdb 030-04, section 3.2). That the writer never gives an error from
  a tree in shape is a statement of its own, not made here; there the fill
  comes back.
* The bounds G and H are the model's, not Java's (bergdb 024-12, D5): a
  transaction with a key node outside them is not covered, even if a later
  operation takes the node back.
* The view after the transaction (the model's `changesOf`, applied to P, must
  show the map of the last state): the model's own round trip from klongs to
  entries and back (bergdb 024-12, D3 and D4). -/

/-- A node of s that is reached in the state's map was reached in s: the
writer links no node of an earlier time again. (With it, a node that the
writer reads from its view is one that the view holds.) -/
def OldReach (i : Time) (s : Tree) (w : MW) : Prop :=
  ∀ z ∈ reach (treeOf i s w), (s.obj z).isSome = true → z ∈ reach s

/-- The contract's parameters, from the model's. -/
def cpOf (p : MParams) : Params := { M := p.M }

/-- The parameters of the writer's own rules, from the model's. -/
def shapeOf (p : MParams) : ShapeParams := ⟨p.H, p.mergeBelow, p.theta⟩

/-- BalancedOK of the writer's own rules (Shape.lean), for the key nodes
reached from the space root: a key node's level is above 0 and it is a segment
leaf exactly at height 0 of its segment tree; a live klong of an inner node
names a key node one level below. (Until bergdb 030-16 found it false after
a delete, this spoke of every key node of the map and every key klong, live
or dead: a take-back leaves a dead klong that names a node further down, and
a node that is no longer reached may name a node taken back. The form here is
the coordinator's decision of 2026-11-17, 20:46.) -/
def Balanced (p : MParams) (s : Tree) : Prop :=
  ∀ x ∈ reach s, ∀ n, s.obj x = some (.key n) → 0 < n.level ∧
    n.leaf = (p.heightOf n.level == 0) ∧
    (n.leaf = false → ∀ c y, (c, y) ∈ live n.ks → ∃ m, s.obj y = some (.key m) ∧
      m.level + 1 = n.level)

/-- J5: the writer's super root t, and whether the writer made it. -/
def WTopInv (i : Time) (s : Tree) (tp : Top) (t : SIS.Tree.Top) (newTop : Bool) : Prop :=
  s.roots = rootsOf tp ∧
  (newTop = false → t.time < i ∧ ∃ zn, tp.getLast? = some (t.id, zn) ∧
    t.skips = zn.skips.map (fun q => (q.1, q.2.1)) ∧
    t.skips.map (·.1) = (List.range (SIS.Tree.topHeight t.ord)).filter (fun j => t.ord.testBit j) ∧
    ∀ q ∈ zn.skips, (tp.node q.2.1).map (·.time) = some q.2.2) ∧
  (newTop = true → t.time = i ∧ tp.node t.id = none ∧
    skipsOk tp { time := i, root := t.rootKey,
                 skips := t.skips.map (fun q => (q.1, q.2, ((tp.node q.2).map (·.time)).getD 0)) }
      = true)

/-- The writer's books within the transaction at time i, B1 to B14. -/
structure MidBooks (p : MParams) (i : Time) (base : NodeId) (s : Tree) (w : MW) : Prop where
  first : ∀ x n, w.nodes.lookup x = some n → w.taken.contains x = false →
    ((s.obj x).isSome = true ↔ n.firstTime ≠ some i)
  times : ∀ x n, w.nodes.lookup x = some n → ∀ t, SIS.Tree.Klong.time t ∈ n.ks → t ≤ i
  madeFor : ∀ m o, (m, o) ∈ w.madeFor → ∃ n, s.obj o = some (.key n)
  named : ∀ x n, w.nodes.lookup x = some n → w.taken.contains x = false →
    ∀ c y, SIS.Tree.Klong.key c y ∈ n.ks → w.taken.contains y = false
  levels : ∀ x n, w.nodes.lookup x = some n → w.taken.contains x = false →
    ∃ g h, w.gh.lookup x = some (g, h) ∧ g ≤ p.G ∧ h ≤ p.H ∧ wLevel s w x = p.keyLevel g h ∧
      n.leaf = (h == 0)
  ids : (∀ x n, w.nodes.lookup x = some n → x < w.next) ∧
    (∀ x h, w.vals.lookup x = some h → x < w.next) ∧
    (∀ m ∈ w.made, m.id < w.next ∧ base ≤ m.id) ∧
    base ≤ w.next ∧ (w.newTop = true → w.top.id < w.next)
  old : ∀ x n n0, w.nodes.lookup x = some n → w.taken.contains x = false →
    s.obj x = some (.key n0) → x ∉ reach (treeOf i s w) → n.ks.map kOf = n0.ks
  reached : ∀ m ∈ w.made, m.isData = false → w.taken.contains m.id = false →
    m.id ≠ w.top.id → m.id ∈ reach (treeOf i s w)
  taken : ∀ x, w.taken.contains x = true → x ∈ w.made.map (·.id)
  overlay : ∀ x n, w.nodes.lookup x = some n → (s.obj x).isSome = true ∨ x ∈ w.made.map (·.id)
  within : w.outside = []
  madeSeg : ∀ m o g h n, (m, o) ∈ w.madeFor → w.gh.lookup m = some (g, h) →
    s.obj o = some (.key n) → g = p.segOf n.level ∧ p.heightOf n.level ≤ h
  timeFirst : ∀ x n, w.nodes.lookup x = some n → w.taken.contains x = false →
    ∃ t rest, n.ks = SIS.Tree.Klong.time t :: rest
  link : ∀ m ∈ w.made, m.isData = false → w.taken.contains m.id = false →
    ∀ x n x' n', w.nodes.lookup x = some n → w.taken.contains x = false →
      w.nodes.lookup x' = some n' → w.taken.contains x' = false →
      (∀ j c, n.ks[j]? = some (SIS.Tree.Klong.key c m.id) →
        n.lastTime = some i ∧ ∃ ti, n.lastTimeIndex = some ti ∧ ti < j) ∧
      ((∃ c, SIS.Tree.Klong.key c m.id ∈ n.ks) → (∃ c, SIS.Tree.Klong.key c m.id ∈ n'.ks) → x = x')

/-- What holds between two operations of the transaction at time i from the
tree s with the top tp, after the operations `done`: J1 to J5, BalancedOK and
the books. -/
structure Mid (p : MParams) (i : Time) (base : NodeId) (s : Tree) (tp : Top) (done : List Op)
    (w : MW) : Prop where
  inv : invOk (cpOf p) (treeOf i s w) = true
  contents : contents (treeOf i s w) = applyOps done (contents s)
  frame : Frame i s (dirtyOf w) (treeOf i s w)
  tree : TreeOk (treeOf i s w)
  top : WTopInv i s tp w.top w.newTop
  balanced : Balanced p (treeOf i s w)
  old : OldReach i s w
  books : MidBooks p i base s w

/-- One operation: the writer's `putKv` from the state w, accepted, with no
key node outside G and H after it, keeps `Mid`. -/
def OpStep (p : MParams) (op : MOp) : Prop :=
  ∀ (i : Time) (base : NodeId) (s : Tree) (tp : Top) (v : View BVal) (z : NodeId)
    (done : List Op) (w w' : MW) (b : Bool),
    Shows p v z s tp → Books i base s tp → Mid p i base s tp done w → keyWf op.key = true →
    SIS.Tree.putKv op { p := p, i := i, view := v } w = .ok (b, w') → w'.outside = [] →
    Mid p i base s tp (done ++ [opOf op]) w'

/-- The writer accepts the operations one by one, each on a key as
`Keys.toSegments` makes it, from the state w to the state w', with no key
node outside G and H after any of them. -/
inductive OpsRun (c : SIS.Tree.Ctx) : MW → List MOp → MW → Prop where
  | nil (w : MW) : OpsRun c w [] w
  | cons (w w1 w' : MW) (op : MOp) (ops : List MOp) (b : Bool) :
      keyWf op.key = true → SIS.Tree.putKv op c w = .ok (b, w1) → w1.outside = [] →
      OpsRun c w1 ops w' →
      OpsRun c w (op :: ops) w'

/-- The tree s with the top tp before the transaction at time i with first id
`base`: the contract's invariants, TREE, BalancedOK, a top, and the books. -/
structure Before (p : MParams) (i : Time) (base : NodeId) (s : Tree) (tp : Top) : Prop where
  inv : invOk (cpOf p) s = true
  tree : TreeOk s
  balanced : Balanced p s
  books : Books i base s tp

/-- One transaction: the model's writer meets the writer's contract. -/
def WriterMeets (p : MParams) (ops : List MOp) : Prop :=
  ∀ (i : Time) (base : NodeId) (s : Tree) (tp : Top) (v : View BVal) (z : NodeId) (t : SIS.Tree.Top)
    (w : MW),
    Before p i base s tp → Shows p v z s tp → SIS.Tree.topOf p v z = .ok t →
    OpsRun { p := p, i := i, view := v } { next := base, top := t } ops w →
    Contract (cpOf p) i s (ops.map opOf) (dirtyOf w) (treeOf i s w) ∧
      TreeOk ((treeOf i s w).at i) ∧ TopStep i tp (topOf i tp w) ∧
      (treeOf i s w).roots = rootsOf (topOf i tp w) ∧
      invOk (cpOf p) (treeOf i s w) = true ∧ TreeOk (treeOf i s w) ∧
      Balanced p (treeOf i s w) ∧
      (∀ x n, (treeOf i s w).obj x = some (.key n) → ∃ t rest, n.ks = Klong.time t :: rest) ∧
      (∀ x n, (treeOf i s w).obj x = some (.key n) → timesBefore (i + 1) n.ks = true) ∧
      (∀ r ∈ (treeOf i s w).roots, r.1 < i + 1) ∧
      (∀ x, w.next ≤ x → (treeOf i s w).obj x = none ∧ (topOf i tp w).node x = none) ∧
      (∀ z zn, (topOf i tp w).getLast? = some (z, zn) → ∀ q ∈ zn.skips,
        ((topOf i tp w).node q.2.1).map (·.time) = some q.2.2)

/-! ## 4. A run

English. A run of the model's writer (`Runs`): from a start tree, empty, with
its top, that meets `Before` for the first transaction; then transaction by
transaction, the j-th at time j: a view that shows the tree and the top to the
writer, a first id above every id of the tree and the top, and the writer
accepts the operations one by one. The tree and the top after the
transaction are the map of the writer's last state.

`WriterMeets` for every transaction gives: a run is a history that meets the
writer's contract, TREE and the top's clauses (`runs_meetsTop`,
Proof/WriterRun.lean), the premise of the theorems on reads. -/

/-- A run of the model's writer from a start tree: the transactions' operations,
the tree and the top after them. -/
inductive Runs (p : MParams) : List (List Op) → Tree → Top → Prop where
  | start (s : Tree) (tp : Top) (base : NodeId) :
      Before p 1 base s tp → contents s = [] → TopStart tp → Runs p [] s tp
  | step (txs : List (List Op)) (s : Tree) (tp : Top) (ops : List MOp) (base : NodeId)
      (v : View BVal) (z : NodeId) (t : SIS.Tree.Top) (w : MW) :
      Runs p txs s tp → Shows p v z s tp → SIS.Tree.topOf p v z = .ok t →
      (∀ x, base ≤ x → s.obj x = none ∧ tp.node x = none) →
      OpsRun { p := p, i := txs.length + 1, view := v } { next := base, top := t } ops w →
      Runs p (txs ++ [ops.map opOf]) (treeOf (txs.length + 1) s w) (topOf (txs.length + 1) tp w)

end Contract
