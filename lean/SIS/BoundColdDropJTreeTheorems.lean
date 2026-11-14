/-
Self-indexed streams in Lean: `DropStepJ`'s first point proved for 024-12's
tree model of BergDB (bergdb item 007; SIS/BoundColdDropJ.lean). Trusted part:
the statements. The definitions they are about are in SIS/BoundColdDropJ.lean
(`DropRunOKJ`, `lostTo`, `addsWeight`, `bvalW`), SIS/Tree/Val.lean (`blive`) and
SIS/Tree/Spec.lean (`treeSpec`); the proofs in SIS/Proof/BoundColdDropJTree.lean.
Added 2026-11-13.

So for BergDB's model what `DropStepJ` assumes is its second point only: the
count k of the pointers that the nodes a transaction makes unreachable lose to
nodes it makes unreachable too (`Dag.deleteUpward`'s unlinked chains and their
values, and a klong replaced in a node that a split replaces).
-/
import SIS.Proof.BoundColdDropJTree

namespace SIS

open SIS.Check SIS.Tree

/-- `blive` takes away, for entries appended to a history, at most their
weights `bvalW`: the live children of h that are not live children of h ++ es
are at most the sum of `bvalW` over es. A key klong replaces at most the child
of its compare value, a delete bitmap the children of its compare values. -/
theorem blive_lost_le (h es : History BVal) :
    ((blive h).filter (fun y => !(blive (h ++ es)).contains y)).length ≤
      (es.map (fun e => bvalW e.val)).sum :=
  blive_lost h es

/-- `DropStepJ.kept` in BergDB's tree model: in a run of `treeSpec` with
`RunOK` and BergDB's still-dirty test (or the exact one; `AlgOK`), a node
reachable before and after T(j + 1) loses, to nodes that T(j + 1) makes
unreachable, at most the weights `bvalW` of the entries T(j + 1) gives it. -/
theorem DropStepJ_kept_tree (p : Params) (al : Algo BVal Tx) (ts : List Tx)
    (hok : RunOK (treeSpec p) al ts)
    (hst : al.stillDirty = javaTest (treeSpec p) ∨
      ((treeSpec p).virt = false ∧ al.stillDirty = exactTest (treeSpec p)))
    (j : Nat) (hj : j < ts.length) (q : NodeId) :
    let db := run (treeSpec p) al (ts.take j)
    let c := (treeSpec p).exec ts[j] (j + 1) (view (treeSpec p) db.P j)
    reachable (treeSpec p) db.P j q = true → reachable (treeSpec p) (db.P.apply (j + 1) c) (j + 1) q = true →
    (lostTo (treeSpec p) db.P (db.P.apply (j + 1) c) (j + 1) q).length ≤ addsWeight bvalW c q :=
  fun hq hq' => kept_tree p al ts hok (algOK_of _ al hst) j hj q hq hq'

/-- In BergDB's tree model, `DropRunOKJ` with `bvalW` follows from its second
point alone, the count k. -/
theorem DropRunOKJ_tree (p : Params) (al : Algo BVal Tx) (ts : List Tx)
    (hok : RunOK (treeSpec p) al ts)
    (hst : al.stillDirty = javaTest (treeSpec p) ∨
      ((treeSpec p).virt = false ∧ al.stillDirty = exactTest (treeSpec p)))
    (k : Nat → Nat)
    (hk : ∀ j (h : j < ts.length),
      let db := run (treeSpec p) al (ts.take j)
      let c := (treeSpec p).exec ts[j] (j + 1) (view (treeSpec p) db.P j)
      ((removedAt (treeSpec p) db.P c (j + 1)).map
        (fun z => (lostTo (treeSpec p) db.P (db.P.apply (j + 1) c) (j + 1) z).length)).sum ≤
        k (j + 1)) :
    DropRunOKJ (treeSpec p) al bvalW k ts :=
  dropRunOKJ_tree p al ts hok (algOK_of _ al hst) k hk

end SIS
