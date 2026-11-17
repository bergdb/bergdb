/-
The contract package (bergdb 030-14): Java's readers after a startup. To read
and to trust, with Recover.lean and Top.lean.

Recover.lean's reader reads the model's view at a time t through a tree built
from it. Java's reader reads Java's own tree, whose key nodes have klongs as
the stream's bytes give them (030-04, 3.5, item 5), and starts from Java's
search through the skip pointers of its top nodes (`jget`, `jscan`,
Top.lean). Here, what Java's tree and top must hold for Java's readers to
read as the reader of the view, said of the data only:

* `HoldsView V leaf t s`: every node of the view but the root and its live
  child (the top node of the time) is a node of s that, as a reader at t sees
  it (`Tree.at`), holds the same: a key node with the view's level, the kind
  `leaf x`, and klongs at t that are well formed (W1 to W5 of Statement.lean
  and Bridge.lean) and whose entries are the view's; a value with the view's
  value. Any klongs with those entries will do: the map from klongs to
  entries forgets (BridgeExample4.lean, `entries_forget`), and the reads do
  not depend on what it forgets.
* `topOfP P`: the top that a structure of the model holds: the root's
  entries, in order, each naming a top node, with the time of the entry; a
  top node's root pointer and skip pointers, each skip pointer with the time
  of the top node it names (Java's `pointersTime`).
* `JReadsRight s tp t mid txs`: Java's get and scan on s, from the search
  through tp at time t (between the records t and t + 1 if `mid`), give what
  the plain map after the first t transactions gives.

Everything here runs; nothing needs Mathlib.
-/
import Contract.Recover
import Contract.Top

namespace Contract

open SIS (Struct Entry History Node View)
open SIS.Check (BVal blive)

/-- The top node of a view: the root's live child. -/
def viewTop (V : View BVal) : Option NodeId :=
  (V SIS.root).bind (fun n0 => (blive n0.hist).head?)

/-- The tree s holds the view V at time t, with the kinds `leaf`: every node
of V but the root and its live child is a node of s that, read at t, holds
the same. -/
def HoldsView (V : View BVal) (leaf : NodeId → Bool) (t : Time) (s : Tree) : Prop :=
  ∀ x n, x ≠ SIS.root → viewTop V ≠ some x → V x = some n →
    (n.isData = false → ∃ kn, s.obj x = some (.key kn) ∧ kn.level = n.level ∧
      kn.leaf = leaf x ∧ klongsWf (prefixAt kn.ks t) = true ∧
      fullOk (prefixAt kn.ks t) = true ∧ entriesOf (prefixAt kn.ks t) = n.hist) ∧
    (n.isData = true → ∃ v, dataOf n.hist = some v ∧ s.obj x = some (.val v))

/-- Java's get and scan on the tree s, from its search through the top tp at
time t (between the records t and t + 1 if `mid`), are right. -/
def JReadsRight (s : Tree) (tp : Top) (t : Time) (mid : Bool) (txs : List (List Op)) : Prop :=
  (∀ key, jget s tp t mid key = refGet (refMap (txs.take t)) key) ∧
  (∀ req, req.wf = true → ∀ limit,
    jscan s tp t mid req limit = refScan (refMap (txs.take t)) req limit)

/-! ## The top of a structure -/

/-- The pointee of the first root pointer of a history. -/
def rootPtrOf (hist : History BVal) : NodeId :=
  (hist.findSome? (fun e => match e.val with
    | .rootKey y => some y
    | _ => none)).getD 0

/-- The time of the root's entry for the top node z, in the root's history. -/
def topTime (hist0 : History BVal) (z : NodeId) : Time :=
  ((hist0.find? (fun e => e.val == .top z)).map (·.time)).getD 0

/-- A top node of a structure, made at time `time`, with the history `hist`;
`hist0` is the root's history. -/
def topNodeOf (hist0 : History BVal) (time : Time) (hist : History BVal) : TopNode :=
  { time := time, root := rootPtrOf hist,
    skips := hist.filterMap (fun e => match e.val with
      | .skip j y => some (j, y, topTime hist0 y)
      | _ => none) }

/-- The top that the structure P holds: for each entry of the root, in order,
the top node it names. -/
def topOfP (P : Struct BVal) : Top :=
  match P.get? SIS.root with
  | some n0 =>
    n0.hist.filterMap (fun e => match e.val with
      | .top z => (P.get? z).map (fun nz => (z, topNodeOf n0.hist e.time nz.hist))
      | _ => none)
  | none => []

end Contract
