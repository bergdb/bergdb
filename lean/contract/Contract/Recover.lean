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
  it; Java's record does; the theorems take it from the level, `kindOf`,
  below), and as klongs one time klong and then, for each
  compare value that the node holds live, its key klong: the pointee of its
  last key entry, unless a later delete entry names the compare value (the
  fold of `blive`, lean/SIS/Tree/Val.lean).

So the reader reads the live klongs that the entries at t give, and nothing
else of V. `vget` and `vscan` are the readers of Read.lean on that tree.

`ReadsRight V leaf txs t`: every get and every scan of that reader gives what
the plain map after the first t transactions of txs gives. The theorems
(RecoverTheorems.lean) prove it, with the kinds from the levels
(`kindOf kind V`) for a history that meets K-LEVEL (`KindsOK`), for the views
after a crash, after restarts, under eviction with handles, after a lazy
startup and after safe cuts.

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

/-! ## The kinds of the key nodes, by their levels

English. The model's nodes have a level, a data flag and entries; the kind of
a key node (segment leaf or inner node) is not among them, and the reads need
it: in a segment leaf a klong consumes a key segment, in an inner node it
does not (Read.lean). Java writes the kind in the node's record
(`StoredKeyNode`). Two histories that differ only in one node's kind can have
one model structure and one stream, and different reads (bergdb 030-14,
section 2: an independent review's `FullLeafGap`). So the kind must come
through the model's structure: here, through the level, which the model has
and recovery gives back.

* K-LEVEL, a clause of the history: a key node's kind is a function `kind` of
  its level. Java's traces: a key node in segment s at height e has level
  1 + (g - s)(h + 1) + e, a segment leaf height 0 (bergdb 027-02, section 4,
  the TREE line), so `kind l` is `(l - 1) % (h + 1) == 0`
  (`kindOfHeight h`). Checked on every key node of D after every transaction
  and on the start (`kindsOk`; RecoverCheck.lean, the bridge checker).
* The reader of a view takes each node's kind from its level in the view
  (`kindOf kind V`). -/

/-- The kind that the TREE line's h gives a level: a segment leaf if its
height in its segment tree is 0. -/
def kindOfHeight (h : Nat) (l : Nat) : Bool := (l - 1) % (h + 1) == 0

/-- The kinds of the nodes of a view, from their levels. -/
def kindOf (kind : Nat → Bool) (V : View BVal) (x : NodeId) : Bool :=
  match V x with
  | some n => kind n.level
  | none => false

/-- K-LEVEL for the key nodes xs of a tree, computed. -/
def kindsOk (kind : Nat → Bool) (s : Tree) (xs : List NodeId) : Bool :=
  xs.all (fun x => match s.obj x with
    | some (.key n) => n.leaf == kind n.level
    | _ => true)

/-- K-LEVEL for a history: every key node of the start, and every key node of
D after every transaction, has the kind of its level. (A key node that is not
in D is unchanged: the frame.) -/
def KindsOK (kind : Nat → Bool) (h : BHist) : Prop :=
  (∀ x n, h.s0.obj x = some (.key n) → n.leaf = kind n.level) ∧
  ∀ j (hj : j < h.txs.length), kindsOk kind (h.tree (j + 1)) h.txs[j].D = true

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
