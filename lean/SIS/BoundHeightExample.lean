/-
Self-indexed streams in Lean: the assumptions of the bounds by height and of
`removedAt_bound`, by running (bergdb item 007). Not part of the trusted part:
a check by running, not a proof. Added 2026-11-13.

On the runs of SIS/BoundT4JavaExample.lean (BergDB's test, replacements of the
node above two leaves): every transaction meets `DropStep` (the replacing node
takes the old node's children), the root's live height is 2 after every
transaction, and the nodes of D have height at most 2 along all pointers. So
`coldReads_height` and `T4_debt_java_tree_height` apply to them, with
H = Hl = Hp = 2, while `T4_debt_tree`'s bound by the changes alone fails there.
-/
import SIS.BoundHeight
import SIS.BoundColdDrop
import SIS.BoundT4JavaExample

namespace SIS.BoundHeightExample

open SIS SIS.Example SIS.BoundT4JavaExample

/-- `LiveHeightLe` by running. -/
def liveHeightB (P : Struct Val) (t : Time) : Nat → NodeId → Bool
  | 0, x => match P.get? x with
    | some n => (specJ.live (n.hist.upTo t)).isEmpty
    | none => true
  | h + 1, x => match P.get? x with
    | some n => (specJ.live (n.hist.upTo t)).all (liveHeightB P t h)
    | none => true

/-- `PtrHeightLe` by running. -/
def ptrHeightB (P : Struct Val) : Nat → NodeId → Bool
  | 0, x => match P.get? x with
    | some n => (pointees specJ n.hist).isEmpty
    | none => true
  | h + 1, x => match P.get? x with
    | some n => (pointees specJ n.hist).all (ptrHeightB P h)
    | none => true

/-- `DropStep` by running, for the change c at time j to P. -/
def dropStepB (P : Struct Val) (j : Time) (c : Changes Val) : Bool :=
  let P' := P.apply j c
  (reachList specJ P (j - 1)).eraseDups.all (fun p =>
    (!reachable specJ P' j p ||
      decide ((lostLive specJ P P' j p).length ≤ (c.adds.filter (fun a => a.1 == p)).length)) &&
    (reachable specJ P' j p || match P.get? p with
      | some n => (specJ.live (n.hist.upTo (j - 1))).all (reachable specJ P' j)
      | none => true))

/-- `DropRunOK` by running, for the run with m replacements. -/
def dropRunB (m : Nat) : Bool :=
  (List.range (tsJ m).length).all (fun j =>
    match (tsJ m)[j]? with
    | some tr =>
      let P := (run specJ algoJ ((tsJ m).take j)).P
      dropStepB P (j + 1) (specJ.exec tr (j + 1) (view specJ P j))
    | none => false)

-- Every transaction of the runs meets `DropStep`.
#guard (List.range 9).all dropRunB
-- The root's live height is at most 2 after every transaction (and at T(0)).
#guard (List.range 9).all (fun m => (List.range ((tsJ m).length + 1)).all (fun t =>
  liveHeightB (run specJ algoJ ((tsJ m).take t)).P t 2 root))
-- The nodes of D have height at most 2 along all pointers.
#guard (List.range 9).all (fun m => (runJ m).D.all (fun e => ptrHeightB (runJ m).P 2 e.1))
-- The bound of `T4_debt_java_tree_height` for m = 8: Q = 9, Hp = Hl = 2, with
-- 1 + 9 + 81 = 91 times 9: it holds (|D| = 11), as the theorem says.
#guard geomSum 9 2 * treeBound 8 == 819

end SIS.BoundHeightExample
