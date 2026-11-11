/-
The tree model (bergdb 024-12): the search through the top nodes' skip pointers
(`TopDs.findSuperRootAtTime`), which finds the top node of a lookup time. The
readers of SIS/Tree/Read.lean use its specification, `topAt`: the top node of
the root's last entry at or before the time (024-12, D6). That the search finds
that node is TP24, `SkipSearchOK`, not proved. Trusted part.

A lookup time of Java's is a clock time; the model's times are the records'
indexes. A Java time at a record's own time is a model time t; a Java time
after record t's and before the next record's is "t and a half": `mid`.
-/
import SIS.Tree.Props

namespace SIS.Tree

open SIS SIS.Check

/-- The root time of top node z (`TopNode.rootTime`): the time of its entries. -/
def topTime (view : View BVal) (z : NodeId) : Option Time :=
  (view z).bind (fun nd => nd.hist.findSome? (fun e => match e.val with
    | .rootKey _ => some e.time
    | _ => none))

/-- The skip pointers of top node z, by index, each with its target and the
target's root time (`TopNode.pointers`, `pointersTime`). -/
def topSkips (view : View BVal) (z : NodeId) : List (Nat × NodeId × Time) :=
  match view z with
  | some nd => nd.hist.filterMap (fun e => match e.val with
    | .skip j s => (topTime view s).map (fun st => (j, s, st))
    | _ => none)
  | none => []

/-- A root time x is at or after the lookup time: t, or t and a half. -/
def atOrAfter (x t : Time) (mid : Bool) : Bool := if mid then decide (t < x) else decide (t ≤ x)

/-- `TopDs.rightMostGte`: the skip pointer with the highest index whose target's
root time is at or after the lookup time. -/
def rightMostGte (view : View BVal) (z : NodeId) (t : Time) (mid : Bool) : Option NodeId :=
  ((topSkips view z).mergeSort (fun a b => decide (b.1 ≤ a.1))).findSome? (fun q =>
    if atOrAfter q.2.2 t mid then some q.2.1 else none)

/-- `TopDs.leftMost`: the skip pointer with the lowest index, if its target's
root time is at or before the lookup time. -/
def leftMost (view : View BVal) (z : NodeId) (t : Time) : Option NodeId :=
  match ((topSkips view z).mergeSort (fun a b => decide (a.1 ≤ b.1))).head? with
  | some q => if q.2.2 ≤ t then some q.2.1 else none
  | none => none

/-- The first loop of `TopDs.findSuperRootAtTime`: along the highest skip
pointers that stay at or after the lookup time. -/
def skipDown (view : View BVal) (t : Time) (mid : Bool) : Nat → NodeId → NodeId
  | 0, z => z
  | f + 1, z =>
    match rightMostGte view z t mid with
    | some y => skipDown view t mid f y
    | none => z

/-- `TopDs.findSuperRootAtTime`: the top node that was the super root at the
lookup time (t, or t and a half), from the newest top node through the skip
pointers; none if there is none old enough. -/
def findSuperRootAt (view : View BVal) (t : Time) (mid : Bool) : Option NodeId :=
  match view root with
  | none => none
  | some r =>
    match r.hist.getLast? with
    | some ⟨_, .top s⟩ =>
      match topTime view s with
      | none => none
      | some st =>
        if st ≤ t then some s else
          let z := skipDown view t mid (r.hist.length + 1) s
          if !mid && topTime view z == some t then some z else leftMost view z t
    | _ => none

/-- TP24. The search through the skip pointers finds the top node of the lookup
time: the one of the root's last entry at or before it (`topAt`), at a record's
time and between two records. The skip list of `TopDs.newSuperRoot` is right. -/
def SkipSearchOK (p : Params) : Prop :=
  ∀ ts, Within p ts → ∀ t ≤ ts.length, ∀ mid : Bool,
    findSuperRootAt (viewOf (treeRun p ts)) t mid = topAt (viewOf (treeRun p ts)) t

end SIS.Tree
