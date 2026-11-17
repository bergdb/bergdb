/-
The contract package (bergdb 030-14): reads after a crash, a restart, under
eviction and after reclaim's cut, end to end. To read and to trust, with
Statement.lean (the plain map), Read.lean (the readers) and Bridge.lean (the
history and the model's structure).

The reads' theorems (Theorems.lean, TheoremsTop.lean) speak of the contract's
tree, a heap of key nodes with their klongs. The bridge's theorems (recovery,
restarts, lazy reading, eviction with handles, the cut: BridgeFull.lean)
speak of the abstract model's structure, nodes with entries, and what they
give back is the model's view at a time t (`SIS.view`, P@t): every node
reachable at t, with its entries up to t. The map from klongs to entries
forgets (BridgeExample4.lean, `entries_forget`), so the step between them is
stated here: a reader that reads the model's view.

English. The reader at time t that reads the view V (the view at t of a
structure, as recovery, a restart, a read through the handles or a startup
from a cut stream gives it) reads the tree `viewTree V leaf`:

* its space root is the root's live child (the top node of time t) and that
  node's live child (its root pointer), as `blive` gives them;
* a data node of V is a value, with its data entry's value;
* an index node of V other than the root is a key node with V's level, the
  kind `leaf x` (segment leaf or inner node: the model's entries do not hold
  it; Java's record does), and as klongs one time klong and then, for each
  compare value that the node holds live, its key klong: the pointee of its
  last key entry, unless a later delete entry names the compare value (the
  fold of `blive`, lean/SIS/Tree/Val.lean).

So the reader reads the live klongs that the entries at t give, and nothing
else of V. `vget` and `vscan` are the readers of Read.lean on that tree.

`ReadsRight V leaf txs t`: every get and every scan of that reader gives what
the plain map after the first t transactions of txs gives. The theorems
(RecoverTheorems.lean) prove it for the views after a crash, after restarts,
under eviction with handles, after a lazy startup and after safe cuts.

Everything here runs; nothing needs Mathlib.
-/
import Contract.Bridge

namespace Contract

open SIS (Struct Entry History Node View)
open SIS.Check (BVal blive setAssoc)

/-! ## The live klongs of the entries -/

/-- One entry of the fold of the live klongs (the first part of `blive`'s
fold): a key entry sets its compare value's pointee; a delete entry clears
each compare value that it names and that has a pointee so far. -/
def liveStep (m : List (Nat × Option Nat)) (e : Entry BVal) : List (Nat × Option Nat) :=
  match e.val with
  | .key c y => setAssoc m c (some y)
  | .del cs => cs.foldl (fun m c => if m.any (fun p => p.1 == c) then setAssoc m c none else m) m
  | _ => m

/-- The fold of the live klongs: for each compare value of a key entry, the
pointee of its last key entry, or none if a later delete entry names it. -/
def liveOfE (hist : History BVal) : List (Nat × Option Nat) := hist.foldl liveStep []

/-- The klongs that a key node with the history `hist` reads as: one time
klong, then a key klong for each compare value that has a pointee. -/
def klongsOfE (hist : History BVal) : List Klong :=
  .time 0 :: (liveOfE hist).filterMap (fun cv => cv.2.map (Klong.key cv.1))

/-- The value of a data node: its data entry's. -/
def dataOf (hist : History BVal) : Option Nat :=
  hist.findSome? (fun e => match e.val with
    | .data v => some v
    | _ => none)

/-! ## The tree of a view -/

/-- A node of the model's view as the reader's tree has it: a data node is a
value; an index node is a key node with its level, the kind `leaf`, and the
klongs of its entries. -/
def objOf (leaf : Bool) (n : Node BVal) : Option Obj :=
  if n.isData then (dataOf n.hist).map Obj.val
  else some (.key { level := n.level, leaf := leaf, ks := klongsOfE n.hist })

/-- The space root of a view: the root's live child (a top node), and its
live child. -/
def viewRoot (V : View BVal) : Option NodeId :=
  match (V SIS.root).map (fun n0 => blive n0.hist) with
  | some (z :: _) =>
    if z = SIS.root then none
    else
      match V z with
      | some nz => (blive nz.hist).head?
      | none => none
  | _ => none

/-- The tree that a reader of the view V reads, with the kinds `leaf`: every
node of V but the root, as `objOf` has it, and the space root of V. -/
def viewTree (V : View BVal) (leaf : NodeId → Bool) : Tree :=
  { obj := fun x => if x = SIS.root then none else (V x).bind (objOf (leaf x)),
    roots := (viewRoot V).toList.map (fun y => (0, y)) }

/-- A get from the view V (`Dag.getOne` on the tree of the view). -/
def vget (V : View BVal) (leaf : NodeId → Bool) (key : Key) : Option Nat :=
  get (viewTree V leaf) key

/-- A scan from the view V (`Dag.getMany` on the tree of the view). -/
def vscan (V : View BVal) (leaf : NodeId → Bool) (req : ScanReq) (limit : Nat) :
    List (Key × Nat) :=
  scan (viewTree V leaf) req limit

/-- The kinds of the key nodes of a tree: true for a segment leaf. -/
def leafOf (s : Tree) (x : NodeId) : Bool :=
  match s.obj x with
  | some (.key n) => n.leaf
  | _ => false

/-- The view that a list of nodes with their contents gives: what a read
through the handles, or a lazy read, returns (`SIS.Mem.read`). -/
def viewOfList (L : List (NodeId × Node BVal)) : View BVal := fun x => L.lookup x

/-! ## The statement -/

/-- The reader of the view V at time t is right: every get, and every scan
that the API allows, gives what the plain map after the first t transactions
of txs gives. -/
def ReadsRight (V : View BVal) (leaf : NodeId → Bool) (txs : List (List Op)) (t : Time) :
    Prop :=
  (∀ key, vget V leaf key = refGet (refMap (txs.take t)) key) ∧
  (∀ req, req.wf = true → ∀ limit,
    vscan V leaf req limit = refScan (refMap (txs.take t)) req limit)

end Contract
