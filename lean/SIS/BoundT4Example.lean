/-
Self-indexed streams in Lean: T4 by running (bergdb item 007). Not part of the
trusted part: a check by running, not a proof.

A run, with the exact still-dirty test, in which a node of D has no change
below it in the last two startup sections, only in the last three: 007-01's
"about the last two sections" (section 6) does not hold in general, and
`DebtByChanges` (lev(x) + 1 sections) does. Added 2026-11-13.

The tree: the root 0 (level 4) has x = 1 and w = 5 (level 3); x has y1 = 2
(level 2), y1 has y2 = 3 and y2' = 4 (level 1); w has w1 = 6 (level 2), w1 has
w2 = 7 (level 1). A transaction is its own change (`exec` returns it).

1. x gets a new child z1 = 20: x, z1 and the root get dirty, d = 1.
2. y2' gets a new data node 21: y2' and y1 get dirty, d = 2.
3. y2 gets a new data node 22: y2 gets dirty, d = 3.
4 to 8. w2 gets a new data node each time: changes outside x.

The startup pos: s(1), ..., s(8) = 0, 0, 0, 1, 2, 3, 4, 6. In T(4) x is taken
and stays dirty (y1's version is stale), d(x) = 4; in T(5) y1 is taken and
stays dirty (y2's version is stale), d(y1) = 5; in T(6) y2 is taken, clean; in
T(7) x is taken again and stays dirty: its new version names y1's version of
T(5), which names y2's version before T(3). So after T(8), x is in D with
d(x) = 7 > s(8) = 6, while the last change below x is T(3), and s(s(8)) = 3:
none in the last two sections. s(s(s(8))) = 0: the last three hold it.
-/
import SIS.BoundT4
import SIS.Example

namespace SIS.BoundT4Example

open SIS SIS.Example

/-- An index node with all entries at time 0. -/
def node (level : Nat) (vals : List Val) : Node Val := mk level vals

def specX : Spec Val (Changes Val) where
  ptrs := ptrs
  live := live
  exec := fun tr _ _ => tr
  init := [(0, node 4 [.ref 1, .ref 5]), (1, node 3 [.ref 2]), (2, node 2 [.ref 3, .ref 4]),
    (3, node 1 []), (4, node 1 []), (5, node 3 [.ref 6]), (6, node 2 [.ref 7]), (7, node 1 [])]
  rootVal := .ref

/-- The startup pos asked for in transaction i. -/
def sched (i : Nat) : Nat := [0, 0, 0, 0, 1, 2, 3, 4, 6].getD i 0

def algoX : Algo Val (Changes Val) := { policy := fun _ _ i _ => sched i, stillDirty := exactTest specX }

/-- A new data node d under the leaf y. -/
def dataUnder (y d : NodeId) : Changes Val :=
  { new := [⟨d, 0, true⟩], adds := [(y, .ref d)] }

def tsX : List (Changes Val) :=
  [{ new := [⟨20, 2, false⟩], adds := [(1, .ref 20)] }, dataUnder 4 21, dataUnder 3 22,
   dataUnder 7 23, dataUnder 7 24, dataUnder 7 25, dataUnder 7 26, dataUnder 7 27]

def runX : DB Val (Changes Val) := run specX algoX tsX

/-- `onAccessPath` as a `Bool`, for this run. -/
def onAccessPathB (τ : Nat) (x : NodeId) : Bool :=
  0 < τ && match tsX[τ - 1]? with
    | some tr =>
      let db := run specX algoX (tsX.take (τ - 1))
      let c := specX.exec tr τ (view specX db.P (τ - 1))
      marked specX (db.P.apply τ c) c τ x || c.touch.contains x
    | none => false

-- The run meets the assumptions (RunOK, by running).
#guard runOKB specX algoX tsX
-- The startup pos: s(0), ..., s(8).
#guard runX.S.map (·.sp) == [0, 0, 0, 0, 1, 2, 3, 4, 6]
-- D after T(8): x with d(x) = 7, the root, and w, w1, w2 of T(8).
#guard runX.D == [(1, 7), (0, 7), (5, 8), (6, 8), (7, 8)]
-- x is on the access path of T(1), T(2) and T(3) only.
#guard (List.range 9).filter (fun τ => onAccessPathB τ 1) == [1, 2, 3]
-- The last two sections: the transactions after s(s(8)) = 3. None holds x.
#guard spIter runX.S 2 8 == 3
-- The last three: after s(s(s(8))) = 0. x's level is 3: `DebtByChanges` asks
-- for the last lev + 1 = 4, after 0.
#guard spIter runX.S 3 8 == 0
#guard spIter runX.S (levelOf runX.P 1 + 1) 8 == 0
-- `DebtByChanges` holds for every node of D (T4_debt), by running.
#guard runX.D.all (fun e => (List.range 9).any (fun τ =>
  decide (spIter runX.S (levelOf runX.P e.1 + 1) 8 < τ) && onAccessPathB τ e.1))
-- Two sections do not hold for x.
#guard !(List.range 9).any (fun τ => decide (spIter runX.S 2 8 < τ) && onAccessPathB τ 1)

end SIS.BoundT4Example
