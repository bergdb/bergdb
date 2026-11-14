/-
Self-indexed streams in Lean: bounds, part 3, the nodes a change makes
unreachable, with an assumption that BergDB's writer meets (bergdb item 007;
007-03, step 6; 007-09). Trusted part: the definitions. The theorems are in
SIS/BoundColdDropJTheorems.lean, the proofs in SIS/Proof/BoundColdDropJ.lean.
Added 2026-11-13.

Why a new assumption. `DropStep` (SIS/BoundColdDrop.lean) is false for Java
(007-09's second review, items/007-bounds/09-t4-in-lean/second-review.md):

* "One `.del [a,b,c]` entry removes three children. `Dag.appendDeleteKlong`
  updates `node.klongs[sz - 1] = union`." In Java a node's delete bitmap of
  the transaction's time is one klong, which each delete of the transaction in
  that node updates in place (`Dag.appendDeleteKlong`: "If 'node' ends with a
  delete klong of the current transaction (same transaction time), said
  delete klong is updated to set a delete bit for the specified
  compareValue."). So one entry kills as many pointers as it names compare
  values. Here an entry is charged by a weight w (`DropStepJ.kept`): for
  BergDB `bvalW`, the compare values it deletes, or 1 for a pointer that
  replaces one.
* "`Dag.deleteUpward` instead executes `unlink(n, pd)` along an emptied chain.
  Parent and child can both disappear." A delete that empties a segment leaf
  does not write it: "it deletes the parent's klong to it instead, and so on
  upward while a node is left with no live klong" (`Dag.deleteUpward`'s
  comment, bergdb 023-05, P1); "An unlinked node gets no entry of tt"
  (`Dag.unlink`: `node.toPreviousState(pd.tt - 1)` and
  `keyNodeReplaced`). The unlinked leaf's values and the chain's nodes are
  then unreachable together, and no entry of the transaction names them.
  Here these are counted by a number k of the transaction
  (`DropStepJ.dropped`): the pointers that the nodes it makes unreachable
  had, at j - 1, to nodes it makes unreachable too.

What k is for Java (a reading of the code, not proved here). A node that a
transaction makes unreachable is one that `Dag.unlink` unlinks (in
`deleteUpward`'s climb, in `merge`'s M5, in `replaceRoot` of root collapse)
or that `Dag.handleFullNode` replaces by a split (`keyNodeReplaced`). Of its
live children at j - 1, a split's replacement takes every one that stays live
("'last' copies every live klong", `handleFullNode`), a merge's new nodes take
every live klong of both nodes (`Dag.merge`, M3), and root collapse's child
takes the root's place (`collapseRoot`). So the children it loses are those
whose klong the transaction deletes or replaces in it: a delete's compare
value in the emptied leaf and in each node of the climb (one a level of the
delete's path, `deleteUpward`), or the klong that a put or delete replaces in
a node that its write splits (`appendDeleteKlong` and the put's
`handleFullNode` with `node.lastVersionGivenDel`). This file first read that
as k ≤ (h + 1) times the operations, h the height of the tree; that is false
with merges (SIS/BoundColdCascadeExample.lean: a parent whose two children
merge loses both, k = 10 at h = 7 for one delete). With TREE, k is at most
the nodes the change makes unreachable (`DropStepJ_dropped_removed`); a
bound on those per operation, about 2 (h + 1) in the runs checked, is open. The
`#guard`s of SIS/BoundColdDropJExample.lean check `DropStepJ` with BergDB's
`bvalW` on runs of 024-12's tree model (`treeSpec`).
-/
import SIS.BoundColdDrop
import SIS.Tree.Val

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- The live children of node p at j - 1 in P (without repeats) that are not
reachable at j in P', the structure after the change at j: the pointers of p
that lead to nodes the change makes unreachable. -/
def lostTo (sp : Spec V T) (P P' : Struct V) (j : Time) (p : NodeId) : List NodeId :=
  match P.get? p with
  | some n => (sp.live (n.hist.upTo (j - 1))).eraseDups.filter (fun y => !reachable sp P' j y)
  | none => []

/-- The weight of the entries that change c gives node p, by the weight w of
an entry value. -/
def addsWeight (w : V → Nat) (c : Changes V) (p : NodeId) : Nat :=
  ((c.adds.filter (fun a => a.1 == p)).map (fun a => w a.2)).sum

/-- The change c at time j to P drops subtrees only as BergDB does, with w the
pointers an entry may kill and k the pointers that the nodes c makes
unreachable lose to nodes c makes unreachable too:

1. `kept`: a node reachable at j - 1 and at j loses, to nodes that are not
   reachable at j, at most as many live children as the weights of the
   entries c gives it (BergDB: a key klong replaces at most the earlier klong
   of its compare value, a delete bitmap deletes its compare values; `bvalW`);
2. `dropped`: the nodes that c makes unreachable (`removedAt`) lose, summed
   over them, at most k live children to nodes c makes unreachable too
   (BergDB: the unlinked chain of `Dag.deleteUpward` and its emptied leaf's
   values, and a klong replaced in a node that a split replaces).

Unlike `DropStep`, nothing asks that a node's children stay reachable when the
node does not. -/
structure DropStepJ (sp : Spec V T) (w : V → Nat) (P : Struct V) (j : Time) (c : Changes V)
    (k : Nat) : Prop where
  kept : ∀ p, reachable sp P (j - 1) p = true → reachable sp (P.apply j c) j p = true →
    (lostTo sp P (P.apply j c) j p).length ≤ addsWeight w c p
  dropped : ((removedAt sp P c j).map (fun z => (lostTo sp P (P.apply j c) j z).length)).sum ≤ k

/-- `DropStepJ` for every transaction T(j + 1) of a run, with k (j + 1) for
it. -/
def DropRunOKJ (sp : Spec V T) (al : Algo V T) (w : V → Nat) (k : Nat → Nat) (ts : List T) :
    Prop :=
  ∀ j (h : j < ts.length),
    let db := run sp al (ts.take j)
    DropStepJ sp w db.P (j + 1) (sp.exec ts[j] (j + 1) (view sp db.P j)) (k (j + 1))

/-- The weight of a BergDB entry value (`SIS.Check.BVal`): the live pointers
it may kill. A key klong replaces the earlier klong of its compare value
(`KeyNode`: the live klong of a compare value is its last key klong, `blive`);
a delete bitmap deletes its compare values (`Dag.appendDeleteKlong`, one
bitmap a node and transaction, `node.klongs[sz - 1] = union`); a top node's
root pointer replaces the earlier one, and the root's entry for a new top node
replaces the old top node (`TopDs.newSuperRoot`); a skip pointer is never
live, and data has no pointer. -/
def bvalW : SIS.Check.BVal → Nat
  | .key _ _ => 1
  | .del cs => cs.length
  | .rootKey _ => 1
  | .top _ => 1
  | .skip _ _ => 0
  | .data _ => 0

end SIS
