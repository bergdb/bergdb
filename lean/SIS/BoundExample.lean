/-
Self-indexed streams in Lean: examples and checks of T3 (bergdb item 007).

Not part of the trusted part. These are tests: they run the definitions of
SIS/Bound.lean on the structures of SIS/Example.lean. Added 2026-10-23.
-/
import SIS.BoundTheorems
import SIS.Example

namespace SIS.Example

open SIS

/-! ## Section 7: the policy is a startup distance of two records

With every record costing 1, a startup distance of 2 asks for s(i) = i - 2,
the policy of the example of section 7 (`algo1`). -/

def algo1sd : Algo Val Tr1 := { algo1 with policy := sdPolicy (fun _ => 1) 2 }

#guard (run spec1 algo1sd [.add 1 10, .add 2 20, .add 1 30, .add 1 40]).S == run1.S

/-! ## Example 2: a cost like bytes, the startup distance, and BergDB's take -/

/-- A cost of a version like its bytes: a header, 8 per entry, 8 per reference. -/
def vbytes (v : Version Val) : Nat := 16 + 8 * v.hist.length + 8 * v.refs.length

/-- A cost of a record like its bytes: a header, the transaction, 8 per
got-dirty id, and its versions. -/
def bytes2 (R : Record Val Tr2) : Nat :=
  32 + (if R.trans.isSome then 16 else 0) + 8 * R.gd.length + (R.vers.map vbytes).sum

/-- A sketch of BergDB's take (`TransSeq.take`), for these checks: from
s(i-1) + 1 on, take whole transactions while they begin at least d before the
end of the stream, and fewer than two have been taken or their got-dirty ids
are fewer than `lim`. Java's limit is 4 per value of the transaction and 1 per
KB; Java's limit on the size of a record is left out. -/
def javaTake {V T : Type} (size : Record V T → Nat) (d lim : Nat) (S : Stream V T) : Nat :=
  go (lastSp S + 1) 0 0 (lastSp S)
where
  go (j taken nodes acc : Nat) : Nat :=
    if h : j < S.length then
      if d ≤ S.cost size j S.length ∧ (taken < 2 ∨ nodes < lim) then
        go (j + 1) (taken + 1) (nodes + S[j].gd.length) j
      else acc
    else acc
  termination_by S.length - j

/-- The cost of the startup section without its last record, R(s+1), ..., R(k-1). -/
def sec2 (S : Stream Val Tr2) : Nat := S.cost bytes2 (lastSp S + 1) (S.length - 1)

/-- BergDB's still-dirty test and marking, with the policy p. -/
def algo2 (p : Stream Val Tr2 → Dirty → Time → Tr2 → Nat) : Algo Val Tr2 :=
  { policy := p, stillDirty := javaTest spec2, mark := true }

/-- The states of a random run of example 2 with `algo2 p`. -/
def states2 (p : Stream Val Tr2 → Dirty → Time → Tr2 → Nat) (seed n : Nat) : List (DB Val Tr2) :=
  states spec2 (algo2 p) ((randomTs seed n).map (·.1))

-- T3, checked by running: with the startup distance policy, the section
-- without its last record costs less than d = 400 in every state.
#guard (states2 (sdPolicy bytes2 400) 1 60).all (fun db => sec2 db.S < 400)
#guard (states2 (sdPolicy bytes2 400) 2 60).all (fun db => sec2 db.S < 400)
-- And with restarts (T3_restarts).
#guard sec2 (runRestarts spec2 (algo2 (sdPolicy bytes2 400)) (randomTs 1 60)).S < 400

-- BergDB's take with a tight limit does not keep up: in some state the
-- section without its last record costs more than d (560 here, at the end).
#guard (states2 (fun S _ _ _ => javaTake bytes2 400 1 S) 1 60).any (fun db => 400 < sec2 db.S)

end SIS.Example
