/-
The tree model (bergdb 024-12, section 2.5): BergDB's key tree as an instance
of the model's `Spec`. With it, `SIS.step` is BergDB whole: the tree makes the
change of a transaction (`Tree.exec`), the model of SIS/Algorithm.lean its
record and D. Trusted part.

The theorems of the model hold for any `Spec` that meets their assumptions
(SIS/Assumptions.lean, Phys.lean, Handle.lean); that `treeSpec` meets them is
stated in SIS/Tree/Props.lean, not proved (bergdb 024-06, C1).
-/
import SIS.Tree.Read

namespace SIS.Tree

open SIS SIS.Check

/-- The tree's `exec` (A1): the changes of transaction tx at time i, from
P@(i-1): its touch first, which changes nothing, then its operations in their
order. An error of the writer (Java's `Bug`) gives no change. -/
def exec (p : Params) (tx : Tx) (i : Time) (view : View BVal) : Changes BVal :=
  let touch := match tx.touch with
    | some (src, to) => touchOf p view (i - 1) src to
    | none => []
  match exec? p tx i view with
  | .ok c => { c with touch := touch }
  | .error _ => { new := [], adds := [], touch := touch }

/-- The primordial structure, R(0) (`Db`'s creation of a database): the root; the
primordial key node, a segment leaf of one time klong (the marker); the first
top node, which names it. -/
def initStruct (p : Params) : Struct BVal :=
  [(root, { level := p.rootLevel, isData := false, hist := [⟨0, .top 2⟩] }),
   (1, { level := p.keyLevel 0 0, isData := false, hist := [⟨0, marker⟩] }),
   (2, { level := p.topLevel 0, isData := false, hist := [⟨0, .rootKey 1⟩] })]

/-- BergDB's key tree as a `Spec`: entries `BVal`, transactions `Tx`, a virtual
root whose children are the top nodes. -/
def treeSpec (p : Params) : Spec BVal Tx where
  ptrs := bptrs
  live := blive
  exec := exec p
  init := initStruct p
  virt := true
  topLevel := p.topLevel 0
  rootVal := .top

/-! ## One operation a key (`Db.sortByKey`, `Trans.Builder.build`) -/

/-- `Tx.sorted`: the keys of the operations are strictly increasing, so the
transaction has one operation a key, in key order. -/
def Tx.sorted (tx : Tx) : Bool := sortedKeys (tx.ops.map (·.key))

/-- Every key of the transaction is one that `Keys.toSegments` makes. -/
def Tx.wf (tx : Tx) : Bool := tx.ops.all (fun op => keyWf op.key)

/-- `Db.sortByKey`: the operations sorted by key, stably, and of operations on
one key one kept: the last put, or the last delete if there is no put (a delete
never replaces a put). -/
def normalize (ops : List Op) : List Op :=
  (ops.mergeSort (fun a b => !keyLt b.key a.key)).foldl (fun acc op =>
    match acc.getLast? with
    | none => [op]
    | some prev =>
      if prev.key == op.key then
        match op, prev with
        | .del _, .put _ _ => acc
        | _, _ => acc.dropLast ++ [op]
      else acc ++ [op]) []

end SIS.Tree
