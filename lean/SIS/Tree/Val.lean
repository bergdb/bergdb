/-
The entry values of the BergDB instance of the model's `Spec`, and its `ptrs`
and `live` (bergdb 011-11, section 2.4; docs/trace-format.md, section 1).

Moved here from Check/Trace.lean on 2026-11-11 (bergdb 024-12, section 2.5),
unchanged and with their names, so that the tree model (SIS/Tree/*.lean), which
is part of the model, and the trace checker use the same definitions. Trusted
part since then: `blive` says which children of a key node are live.
-/
import SIS.Basic

namespace SIS.Check

open SIS

/-- The entry values of the BergDB instance (docs, 2.4 and 9.1). -/
inductive BVal where
  /-- A key klong: compare value c, child y. -/
  | key (c y : Nat)
  /-- A delete bitmap: the key entries before it with these compare values are
  deleted. -/
  | del (cs : List Nat)
  /-- A top node's pointer to its root key node. -/
  | rootKey (y : Nat)
  /-- A top node's skip pointer j to an older top node. -/
  | skip (j z : Nat)
  /-- The root's entry for a top node. -/
  | top (z : Nat)
  /-- A value node's data, as a hash. -/
  | data (h : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- The nodes an entry points to. -/
def bptrs : BVal → List NodeId
  | .key _ y => [y]
  | .rootKey y => [y]
  | .skip _ z => [z]
  | .top z => [z]
  | _ => []

/-- Sets the value for compare value c in an association list, keeping the
order of first appearance. -/
def setAssoc (m : List (Nat × Option Nat)) (c : Nat) (v : Option Nat) :
    List (Nat × Option Nat) :=
  if m.any (fun p => p.1 == c) then m.map (fun p => if p.1 == c then (c, v) else p)
  else m ++ [(c, v)]

/-- The live children of a node with history h: for a key node, the child of
the last key entry of each compare value that no later delete entry names; for
a top node, its last root pointer; for the root, its last top node. -/
def blive (h : History BVal) : List NodeId :=
  let st := h.foldl (fun (acc : List (Nat × Option Nat) × Option Nat × Option Nat) e =>
    match e.val with
    | .key c y => (setAssoc acc.1 c (some y), acc.2.1, acc.2.2)
    | .del cs =>
      (cs.foldl (fun m c => if m.any (fun p => p.1 == c) then setAssoc m c none else m) acc.1,
        acc.2.1, acc.2.2)
    | .rootKey y => (acc.1, some y, acc.2.2)
    | .top z => (acc.1, acc.2.1, some z)
    | _ => acc) ([], none, none)
  ((st.1.filterMap (·.2)) ++ st.2.1.toList ++ st.2.2.toList).eraseDups

end SIS.Check
