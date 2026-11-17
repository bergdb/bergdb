/-
The contract package (bergdb 030-08): the top of Java's tree from a trace's
lines (bergdb 027-02, sections 2 and 4), for the trace checker, and the
checks of Java's own top search and cached times.

* `applyTop`: each top node made (`ADD 0 i T z`) with its root time i, its
  root pointer (`ADD z i R y`) and its skip pointers (`ADD z i S j y`, in
  their order). The trace gives a skip pointer's cached time only in the
  SKIPT lines of a version of the top node, written in a later record; so
  `applyTop` caches the root time of the top node named, and `skiptFaults`
  compares every SKIPT line with it: the cached times of the contract's top
  are Java's wherever a version of the top node is in the trace.
* `liveFaults`: Java's search at every time (`LIVE 0 t z`, with the
  exporter's `live=1`: at each record's time and at the last time before the
  next record, which the model calls t and a half) against `findTop`.
-/
import Contract.Trace
import Contract.Top

namespace Contract

/-- The top after a transaction's lines, from the top before it. -/
def applyTop (tp : Top) (tx : TxLines) : Top :=
  tx.tops.foldl (fun tp z =>
    let skips := (tx.skipLines.filter (fun q => q.1 == z)).map (fun q =>
      (q.2.1, q.2.2, ((tp.node q.2.2).map (·.time)).getD 0))
    tp ++ [(z, { time := tx.i, root := (tx.rootPtrs.lookup z).getD 0, skips := skips })]) tp

/-- The SKIPT lines of a transaction that differ from the cached times of the
top: (top node, index, time), and the number of SKIPT lines of top nodes. -/
def skiptFaults (tp : Top) (tx : TxLines) : List (NodeId × Nat × Time) × Nat :=
  tx.skipts.foldl (fun (acc : List (NodeId × Nat × Time) × Nat) (z, j, t) =>
    match tp.node z with
    | some n =>
      ((if (n.skips.find? (fun q => q.1 == j)).map (·.2.2) == some t then acc.1
        else acc.1 ++ [(z, j, t)]), acc.2 + 1)
    | none => (acc.1 ++ [(z, j, t)], acc.2 + 1)) ([], 0)

/-- The LIVE 0 lines of a transaction that differ from `findTop` on the top
after it: (time, Java's top node). The second line of a time is between the
records (`mid`). -/
def liveFaults (tp : Top) (tx : TxLines) : List (Time × Option NodeId) :=
  (tx.lives.foldl (fun (acc : List (Time × Option NodeId) × Option Time) (t, z) =>
    let mid := acc.2 == some t
    ((if findTop tp t mid == z then acc.1 else acc.1 ++ [(t, z)]), some t)) ([], none)).1

end Contract
