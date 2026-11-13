/-
Self-indexed streams in Lean: T4 with BergDB's still-dirty test, by running
(bergdb item 007; 007-01, section 6, second point). Not part of the trusted
part: a check by running, not a proof. Added 2026-11-13.

With BergDB's test (`javaTest`) no bound in the changes of the last sections
holds: a family of runs, all meeting the assumptions and TREE, with the same
last three transactions (each its own startup section), in which D holds m + 3
nodes after m replacements of an index node made earlier. For m = 8, D has 11
nodes while `T4_debt_tree`'s bound, proved for the exact test, is 9; and the
first node replaced, x = 1, is in D though no change has been on its access
path since T(2), so `DebtByChanges` fails too. `DebtByChains` (T4_debt_java)
holds: x reaches the leaf changed last through its old pointer.

Why, in plain words. BergDB's test keeps a written node in D while any node it
points to, live or dead, is in D. A node that a split (here a copy) replaced is
no longer reachable, so no change is on its access path, but it keeps its
pointers to its old children, which now hang under the new node. The two leaves
y1 and y2 are written in turn, one per transaction, with one transaction per
section: when the old node is taken, the leaf written in that transaction has
just got dirty, is in D, and puts the old node back. So it stays in D for ever,
and each replacement above the two leaves adds one more such node. D grows with
the number of replacements in the run's past, which the last sections do not
see. The count needs the pointer parents (`ptrParents`, here m + 1 for each
leaf; `T4_debt_java_tree`).

The tree: the root 0 (level 2) has slot 0 pointing to x = 1 (level 1), which
points to the leaves y1 = 2 and y2 = 3 (level 0, index nodes with data
entries, as in example 1 of SIS/Example.lean). A transaction is its own change
(`exec` returns it). The startup pos asked for is i - 1.

1. T(1) writes y1, T(2) y2.
2. m times: a replacement, a new node x' = 10 + k on level 1 that points to y1
   and y2, put in slot 0 of the root (the old x is no longer reachable), with a
   write of y1; then a write of y2.
3. y1, y2, y1, y2.
-/
import SIS.BoundT4Java
import SIS.Example

namespace SIS.BoundT4JavaExample

open SIS SIS.Example

def specJ : Spec Val (Changes Val) where
  ptrs := ptrs
  live := live
  exec := fun tr _ _ => tr
  init := [(0, mk 2 [.slot 0 1]), (1, mk 1 [.ref 2, .ref 3]), (2, mk 0 []), (3, mk 0 [])]
  rootVal := .ref

/-- BergDB's still-dirty test, step 3 by marking (BergDB's way), the startup
pos i - 1: one transaction per section. -/
def algoJ : Algo Val (Changes Val) :=
  { policy := fun _ _ i _ => i - 1, stillDirty := javaTest specJ, mark := true }

/-- A write of leaf y. -/
def upd (y n : NodeId) : Changes Val := { new := [], adds := [(y, .dat n)] }

/-- The replacement of the node in the root's slot 0 by a new node x' that
points to both leaves, with a write of leaf y. -/
def repl (x' y n : NodeId) : Changes Val :=
  { new := [⟨x', 1, false⟩], adds := [(0, .slot 0 x'), (x', .ref 2), (x', .ref 3), (y, .dat n)] }

/-- The last transactions, the same in every run of the family. -/
def tail : List (Changes Val) := [upd 2 100, upd 3 101, upd 2 102, upd 3 103]

/-- The run with m replacements. -/
def tsJ (m : Nat) : List (Changes Val) :=
  [upd 2 0, upd 3 1] ++ (List.range m).flatMap (fun k => [repl (10 + k) 2 (2 * k + 2), upd 3 (2 * k + 3)])
    ++ tail

def runJ (m : Nat) : DB Val (Changes Val) := run specJ algoJ (tsJ m)

/-- `onAccessPath` as a `Bool`, for the run with m replacements. -/
def onAccessPathB (m τ : Nat) (x : NodeId) : Bool :=
  0 < τ && match (tsJ m)[τ - 1]? with
    | some tr =>
      let db := run specJ algoJ ((tsJ m).take (τ - 1))
      let c := specJ.exec tr τ (view specJ db.P (τ - 1))
      marked specJ (db.P.apply τ c) c τ x || c.touch.contains x
    | none => false

/-- The nodes that x reaches through pointers, live or dead (`PtrBelow`), within
`fuel` steps. -/
def ptrBelowList (P : Struct Val) : Nat → NodeId → List NodeId
  | 0, x => [x]
  | fuel + 1, x => x :: match P.get? x with
    | some n => (pointees specJ n.hist).flatMap (ptrBelowList P fuel)
    | none => []

/-- TREE at time i, by running (`treeAt`). -/
def treeAtB (P : Struct Val) (i : Time) : Bool :=
  (reachList specJ P i).eraseDups.all (fun y => y == root ||
    ((reachList specJ P i).eraseDups.filter (fun x => match P.get? x with
      | some n => (specJ.live (n.hist.upTo i)).contains y
      | none => false)).length == 1)

/-- `TreeRunOK`, by running. -/
def treeRunOKB (m : Nat) : Bool :=
  (List.range (tsJ m).length).all (fun j =>
    treeAtB (run specJ algoJ ((tsJ m).take (j + 1))).P (j + 1))

/-- `DebtByChains` for the run with m replacements, by running. -/
def chainsB (m : Nat) : Bool :=
  let db := runJ m
  let k := (tsJ m).length
  db.D.all (fun e => (List.range (k + 1)).any (fun τ =>
    decide (spIter db.S (levelOf db.P e.1 + 1) k < τ) &&
      (ptrBelowList db.P 4 e.1).any (onAccessPathB m τ)))

/-- `DebtByChanges` for the run with m replacements, by running. -/
def changesB (m : Nat) : Bool :=
  let db := runJ m
  let k := (tsJ m).length
  db.D.all (fun e => (List.range (k + 1)).any (fun τ =>
    decide (spIter db.S (levelOf db.P e.1 + 1) k < τ) && onAccessPathB m τ e.1))

/-- `T4_debt_tree`'s bound (proved for the exact test) for the run with m
replacements: H = 2, the root's level. -/
def treeBound (m : Nat) : Nat :=
  let db := runJ m
  let k := (tsJ m).length
  let a := spIter db.S 3 k
  ((List.range' (a + 1) (k - a)).map (fun τ =>
    3 * ((changeAt specJ algoJ (tsJ m) τ).new.length + (changeAt specJ algoJ (tsJ m) τ).adds.length) +
      (changeAt specJ algoJ (tsJ m) τ).touch.length)).sum

/-- The most pointer parents of a node after the run (`ptrParents`). -/
def maxParents (m : Nat) : Nat :=
  let P := (runJ m).P
  ((allIds P).map (fun z => (ptrParents specJ P z).length)).foldl max 0

-- Every run of the family meets the assumptions (RunOK) and TREE, by running.
#guard (List.range 9).all (fun m => runOKB specJ algoJ (tsJ m) && treeRunOKB m)
-- The startup pos: one transaction per section, s(i) = i - 1.
#guard (List.range 9).all (fun m =>
  (runJ m).S.map (·.sp) == [0] ++ (List.range (tsJ m).length))
-- D has m + 3 nodes: the root, the m + 1 nodes that slot 0 has pointed to, and
-- the leaf written last.
#guard (List.range 9).all (fun m => (runJ m).D.length == m + 3)
#guard (runJ 2).D == [(3, 10), (11, 10), (10, 10), (1, 10), (0, 10)]
-- The last three sections are the last three transactions, the same in every
-- run: the changes of the last sections are the same, and D is not bounded by
-- them.
#guard (List.range 9).all (fun m =>
  spIter (runJ m).S 3 (tsJ m).length == (tsJ m).length - 3 &&
    ((tsJ m).drop ((tsJ m).length - 3)).length == 3)
-- For m = 8: |D| = 11 > 9, `T4_debt_tree`'s bound.
#guard (runJ 8).D.length == 11
#guard treeBound 8 == 9
-- x = 1 is in D after T(22) but not reachable since T(3), and on no access path
-- after T(2): `DebtByChanges` fails.
#guard (runJ 8).D.any (fun e => e.1 == 1)
#guard (List.range 23).filter (fun τ => onAccessPathB 8 τ 1) == [1, 2]
#guard !changesB 8
-- Nor does x hold a pointer made in the last sections: its entries are all of
-- time 0. It stays in D through pointers made before the sections.
#guard ((runJ 8).P.get? 1).map (fun n => n.hist.all (·.time == 0)) == some true
-- `DebtByChains` holds (T4_debt_java), in every run of the family.
#guard (List.range 9).all chainsB
-- The pointer parents: each leaf has m + 1 (the nodes slot 0 has pointed to).
#guard maxParents 8 == 9
#guard ptrParents specJ (runJ 8).P 2 == [1, 10, 11, 12, 13, 14, 15, 16, 17]

end SIS.BoundT4JavaExample
