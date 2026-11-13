/-
Self-indexed streams in Lean: `DropStep` and `DropStepJ` on runs of 024-12's
tree model of BergDB's writer (`treeSpec`), by running (bergdb item 007;
SIS/BoundColdDropJ.lean). Not part of the trusted part: checks by running, not
proofs. Added 2026-11-13.

The tree: node size 8, no merges (`pp`), twelve keys put in T(1); then one of
two transactions T(2) on it.

1. The upward unlink (`Dag.deleteUpward`). T(2) deletes keys 0 and 1, the two
   keys of leaf 112, which is emptied: it gets no entry, its parent 116 gets a
   delete of the leaf's klong and the empty key pointed to the next leaf
   (`emptyKeyNext`). The leaf and its two values are unreachable: parent and
   children disappear together. `DropStep`'s second point fails; `DropStepJ`
   holds with k = 2 (the leaf's two values), and not with k = 1.
2. A bitmap (`Dag.appendDeleteKlong`). T(2) deletes keys 9, 10 and 11 of leaf
   134, which keeps key 8: one entry, a delete bitmap of three compare values,
   kills three live children. `DropStep`'s first point fails (3 children lost
   for 1 entry); `DropStepJ` holds with BergDB's weights (`bvalW`: 3 for the
   bitmap) and k = 0.

Then two runs of seven transactions, 40 puts and six rounds of deletes, with
and without merges (`Params.withMerges`): every transaction runs without error
in the model, meets `DropStepJ` with k its own count of lost pointers, and
that count is at most 3 per operation of the transaction (the root's live
height is at most 6 in these runs).
-/
import SIS.Tree.Props
import SIS.BoundColdDropJTheorems

namespace SIS.BoundColdDropJExample

open SIS SIS.Tree SIS.Check

def pp : Params := ({M := 8, G := 1, H := 6} : Params)
def ppm : Params := ({M := 8, G := 1, H := 8} : Params).withMerges
def key (j : Nat) : Key := [64 * j + 8]

/-- T(1): twelve keys. -/
def tx1 : Tx := {base := 100, ops := (List.range 12).map (fun j => .put (key j) 1)}
/-- T(2), case 1: the two keys of leaf 112. -/
def txUp : Tx := {base := 300, ops := [.del (key 0), .del (key 1)]}
/-- T(2), case 2: three of the four keys of leaf 134. -/
def txBits : Tx := {base := 300, ops := [.del (key 9), .del (key 10), .del (key 11)]}

def P1 : Struct BVal := treeRun pp [tx1]
def cUp : Changes BVal := exec pp txUp 2 (view (treeSpec pp) P1 1)
def cBits : Changes BVal := exec pp txBits 2 (view (treeSpec pp) P1 1)

-- Case 1: the leaf 112 and its two values are made unreachable.
#guard isOk (exec? pp txUp 2 (view (treeSpec pp) P1 1))
#guard cUp.adds == [(116, .del [136]), (116, .key 0 114)] && cUp.new == []
#guard removedAt (treeSpec pp) P1 cUp 2 == [112, 100, 102]
-- `DropStep.adopted` fails: 112 is unreachable at 2, 100 was its live child at
-- 1, and 100 is not reachable at 2.
#guard ((P1.get? 112).map (fun n => (blive (n.hist.upTo 1)).contains 100)) == some true &&
  !reachable (treeSpec pp) (P1.apply 2 cUp) 2 112 && !reachable (treeSpec pp) (P1.apply 2 cUp) 2 100
-- `DropStepJ` holds with k = 2, not with k = 1.
#guard dropStepJB (treeSpec pp) bvalW P1 2 cUp 2
#guard !dropStepJB (treeSpec pp) bvalW P1 2 cUp 1

-- Case 2: one bitmap entry, three children lost.
#guard isOk (exec? pp txBits 2 (view (treeSpec pp) P1 1))
#guard cBits.adds == [(134, .del [584, 648, 712])] && cBits.new == []
#guard lostLive (treeSpec pp) P1 (P1.apply 2 cBits) 2 134 == [128, 130, 132]
#guard (cBits.adds.filter (fun a => a.1 == 134)).length == 1
#guard dropStepJB (treeSpec pp) bvalW P1 2 cBits 0

/-- Seven transactions: 40 puts, then six rounds of deletes. -/
def txs : List Tx :=
  [{base := 1000, ops := (List.range 40).map (fun j => .put (key j) 1)}] ++
  (List.range 6).map (fun r =>
    ({ base := 2000 + 1000 * r,
       ops := ((List.range 40).filter (fun j => (j + r) % 3 == 0 && j % 2 == r % 2)).map
         (fun j => .del (key j)) } : Tx))

/-- For each transaction of the run: it runs without error, it meets
`DropStepJ` with k its own count of lost pointers, that count is at most 3 per
operation, and the nodes it makes unreachable are at most the weights of its
entries plus that count (`removedAt_bound_J`, checked). -/
def checkRun (p : Params) (ts : List Tx) : Bool :=
  (List.range ts.length).all (fun i =>
    let P := treeRun p (ts.take i)
    let tx := ts[i]!
    let c := exec p tx (i + 1) (view (treeSpec p) P i)
    let rem := removedAt (treeSpec p) P c (i + 1)
    let drop := (rem.map (fun z => (lostTo (treeSpec p) P (P.apply (i + 1) c) (i + 1) z).length)).sum
    isOk (exec? p tx (i + 1) (view (treeSpec p) P i)) &&
      dropStepJB (treeSpec p) bvalW P (i + 1) c drop &&
      decide (drop ≤ 3 * tx.ops.length) &&
      decide (rem.length ≤ (c.adds.map (fun a => bvalW a.2)).sum + drop))

#guard checkRun pp txs
#guard checkRun ppm txs

end SIS.BoundColdDropJExample
