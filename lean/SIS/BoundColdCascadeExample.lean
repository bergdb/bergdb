/-
Self-indexed streams in Lean: the count k of `DropStepJ` on a run of 024-12's
tree model of BergDB with merges (`treeSpec`), by running (bergdb item 007;
SIS/BoundColdDropJ.lean). Not part of the trusted part: checks by running, not
proofs. Added 2026-11-13.

The question (007, the cascade count k of `DropStepJ`): do the nodes that one
transaction makes unreachable lose at most (H + 1) pointers to each other per
operation, H the root's live height (`LiveHeightLe`, as `coldReadsJ_height_noD`
takes it)? SIS/BoundColdDropJ.lean reads Java so: "k ≤ (h + 1) times the
operations of the transaction, h the height of the tree".

No: a merge cascade loses two pointers a height. Node size 8 with format 7's
merges (`Params.withMerges`: m = 2, c = 4), one segment; T(1) puts 200 keys,
then T(2) to T(201) delete one key each, in the order 7, 10, 13, ... (3 j + 7
mod 200). The root's live height stays at most 7 for T(1) to T(92) (a key tree
of height 4, with the virtual root, the top node and the values). T(92)
deletes one key, in leaf 1238, which is left with one live klong:

* the leaf merges with its sibling 189000; their parent 1248 is left with one
  live klong and merges with its sibling 187002; so do 187004 (with 178004)
  and 178006 (with 164014), which make two new nodes; the segment root 164016
  gets their klongs and is replaced by a new node (`handleFull`); and the
  transaction's new top node replaces the old one, 164018;
* every merged node is unreachable at 92, and so is each node whose two
  children merged: 1248 loses both 1238 and 189000, 187004 both 187002 and
  1248, 178006 both 178004 and 187004, the root 164016 both 178006 and 164014;
* with the leaf's value 1228 and the old top node's pointer to the old root,
  the removed nodes lose 1 + 2 + 2 + 2 + 2 + 1 = 10 pointers to each other.

So k(92) = 10 > 8 = (H + 1) x 1. `DropStepJ` holds with k = 10 and fails with
k = 8. The reason in plain words: a merge removes two nodes of a height, and
when the parent of the two merges in its turn, it loses both of them. Each
height of the cascade costs two pointers, not one, so the count is about
2 (H + 1) per operation, not (H + 1). The upward unlink (`Dag.deleteUpward`)
and the splits cost one a height; the merges at the delete (024-22) two.
-/
import SIS.BoundColdDropJExample
import SIS.BoundHeight

namespace SIS.BoundColdCascadeExample

open SIS SIS.Tree SIS.Check

/-- Node size 8, format 7's merges (m = 2, c = 4, h = 4), G = 1, H = 8. -/
def ppm : Params := ({M := 8, G := 1, H := 8} : Params).withMerges

def key (j : Nat) : Key := [64 * j + 8]

/-- The order of the deletes: 7, 10, 13, ... (3 j + 7 mod 200). -/
def order : List Nat := (List.range 200).map (fun j => (j * 3 + 7) % 200)

/-- T(1) puts 200 keys; T(2) to T(201) delete one key each. -/
def txs : List Tx :=
  [{base := 1000, ops := (List.range 200).map (fun j => .put (key j) 1)}] ++
  order.zipIdx.map (fun (kj, i) => ({base := 100000 + 1000 * (i + 1), ops := [.del (key kj)]} : Tx))

/-- `LiveHeightLe` for `blive`, by running. -/
def liveHeightB (P : Struct BVal) (t : Time) : Nat → NodeId → Bool
  | 0, x => match P.get? x with
    | some n => (blive (n.hist.upTo t)).isEmpty
    | none => true
  | h + 1, x => match P.get? x with
    | some n => (blive (n.hist.upTo t)).all (liveHeightB P t h)
    | none => true

theorem liveHeightLe_of_B (P : Struct BVal) (t : Time) :
    ∀ h x, liveHeightB P t h x = true → LiveHeightLe (treeSpec ppm) P t h x
  | 0, x, hb => by
    intro n hn
    unfold liveHeightB at hb
    rw [hn] at hb
    exact List.isEmpty_iff.mp hb
  | h + 1, x, hb => by
    intro n hn y hy
    unfold liveHeightB at hb
    rw [hn] at hb
    exact liveHeightLe_of_B P t h y (List.all_eq_true.mp hb y hy)

/-- The first n transactions are a run within the model's reach (`Within`:
sorted and well-formed keys, a first id above every id before, no error of the
writer), and the root's live height is at most H at times 0 to n. -/
def checkPrefix (n H : Nat) : Bool :=
  let r := ((txs.take n).zipIdx).foldl (fun (acc : Struct BVal × Bool) (q : Tx × Nat) =>
    let (P, ok) := acc
    let tx := q.1
    let j := q.2
    let ok' := ok && tx.sorted && tx.wf && P.all (fun e => decide (e.1 < tx.base)) &&
      isOk (exec? ppm tx (j + 1) (view (treeSpec ppm) P j)) &&
      liveHeightB P j H root
    (P.apply (j + 1) (exec ppm tx (j + 1) (view (treeSpec ppm) P j)), ok')) (initStruct ppm, true)
  r.2 && liveHeightB r.1 n H root

-- T(1) to T(92) run without error, and the root's live height is at most 7 at
-- times 0 to 92.
#guard checkPrefix 92 7

/-- P after T(91), and T(92)'s change. -/
def P91 : Struct BVal := treeRun ppm (txs.take 91)
def c92 : Changes BVal := exec ppm txs[91]! 92 (view (treeSpec ppm) P91 91)

-- T(92) is one delete.
#guard txs[91]!.ops == [.del (key 77)]
-- Its nodes made unreachable, each with the pointers it loses to nodes made
-- unreachable too: 10 in all.
#guard (removedAt (treeSpec ppm) P91 c92 92).map
    (fun z => (z, lostTo (treeSpec ppm) P91 (P91.apply 92 c92) 92 z)) ==
  [(164018, [164016]), (164016, [178006, 164014]), (178006, [178004, 187004]),
   (178004, []), (187004, [187002, 1248]), (187002, []), (1248, [189000, 1238]),
   (189000, []), (1238, [1228]), (1228, []), (164014, [])]
-- `DropStepJ` with BergDB's weights holds with k = 10, and fails with
-- k = (H + 1) x (its operations) = 8.
#guard dropStepJB (treeSpec ppm) bvalW P91 92 c92 10
#guard !dropStepJB (treeSpec ppm) bvalW P91 92 c92 ((7 + 1) * txs[91]!.ops.length)

end SIS.BoundColdCascadeExample
