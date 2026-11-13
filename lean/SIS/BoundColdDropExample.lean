/-
Self-indexed streams in Lean: the nodes a change makes unreachable, by running
(bergdb item 007; SIS/BoundColdDrop.lean). Not part of the trusted part: a
check by running, not a proof. Added 2026-11-13.

Without `DropStep` no bound on `removedAt` by the change holds: one
transaction, with one new node and one entry, replaces the root's child x = 1
by a new empty node, and makes x and its five leaves unreachable. The run
meets the assumptions and TREE; `DropStep`'s second point fails (x's children
are not taken over).
-/
import SIS.BoundColdDrop
import SIS.Example

namespace SIS.BoundColdDropExample

open SIS SIS.Example

def specD : Spec Val (Changes Val) where
  ptrs := ptrs
  live := live
  exec := fun tr _ _ => tr
  init := [(0, mk 2 [.slot 0 1]), (1, mk 1 [.ref 2, .ref 3, .ref 4, .ref 5, .ref 6]),
    (2, mk 0 []), (3, mk 0 []), (4, mk 0 []), (5, mk 0 []), (6, mk 0 [])]
  rootVal := .ref

def algoD : Algo Val (Changes Val) :=
  { policy := fun _ _ i _ => i - 1, stillDirty := javaTest specD, mark := true }

/-- The root's slot 0 gets a new empty node 9. -/
def dropTr : Changes Val := { new := [⟨9, 1, false⟩], adds := [(0, .slot 0 9)] }

def P0 : Struct Val := (run specD algoD []).P

-- The run meets the assumptions (RunOK), by running.
#guard runOKB specD algoD [dropTr]
-- TREE after T(1): the root and node 9 are reachable, 9 with one parent.
#guard reachList specD (run specD algoD [dropTr]).P 1 == [0, 9]
-- The change makes six nodes unreachable, with one entry and one new node.
#guard removedAt specD P0 dropTr 1 == [1, 2, 3, 4, 5, 6]
-- `DropStep`'s first point holds for the root: it loses one live child, x,
-- for its one entry.
#guard lostLive specD P0 (P0.apply 1 dropTr) 1 0 == [1]
-- Its second point fails: x is made unreachable, and its children are not
-- reachable at 1.
#guard !reachable specD (P0.apply 1 dropTr) 1 2

end SIS.BoundColdDropExample
