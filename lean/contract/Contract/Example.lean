/-
The contract package (bergdb 030-04, section 7.4 (b)): the premises of the
theorems can be met. A start tree, the empty tree as Java makes it (one key
node, a segment leaf with one time klong, as in TX 0 of a trace), and one
transaction that puts one key: the two trees and the transaction meet the
writer's contract, so they are a history that `Meets` it, and the theorems
speak about it. The theorems are not vacuous.
-/
import Contract.Theorems

namespace Contract.Example

open Contract

/-- The node size. -/
def p : Params := { M := 8 }

/-- The empty tree: key node 1, a segment leaf made at time 0; the space root
from time 0 on. -/
def s0 : Tree :=
  { obj := fun x => if x = 1 then some (.key { level := 1, leaf := true, ks := [.time 0] })
      else none,
    roots := [(0, 1)] }

/-- The transaction: a put of the key with the one segment 8 (a short
segment) and the value 5. -/
def ops : List Op := [.put [8] 5]

/-- The tree after the transaction at time 1: the value is node 2, and key
node 1 has a time klong of 1 and a key klong for the key. -/
def s1 : Tree :=
  { obj := fun x =>
      if x = 1 then
        some (.key { level := 1, leaf := true, ks := [.time 0, .time 1, .key 8 2] })
      else if x = 2 then some (.val 5)
      else none,
    roots := [(0, 1)] }

/-- The empty tree is a start tree. -/
theorem start : Start p s0 := by
  constructor <;> decide

/-- The frame, clause 3, with the dirty node 1. -/
theorem frame : Frame 1 s0 [1] s1 := by
  refine ⟨?_, ?_, ⟨[], by simp [s0, s1], by simp⟩⟩
  · intro x o hx
    by_cases h1 : x = 1
    · subst h1
      simp only [s0, ite_true, Option.some.injEq] at hx
      subst hx
      refine ⟨.key { level := 1, leaf := true, ks := [.time 0, .time 1, .key 8 2] },
        by simp [s1], ?_, fun h => by simp at h⟩
      exact ⟨rfl, rfl, Or.inr ⟨[.key 8 2], rfl⟩⟩
    · simp [s0, h1] at hx
  · intro x n hx hno
    by_cases h1 : x = 1
    · simp [h1]
    · by_cases h2 : x = 2
      · simp [s1, h2] at hx
      · simp [s1, h1, h2] at hx

/-- The transaction meets the writer's contract. -/
theorem contract : Contract p 1 s0 ops [1] s1 :=
  ⟨by decide, frame⟩

/-- A history that meets the contract. -/
theorem meets : Meets p [ops] s1 :=
  Meets.step [] s0 ops [1] s1 (Meets.start s0 start) contract

/-- What the theorems say of it: at time 1 the key has its value, at time 0
it has none, and a scan at time 1 gives the key. -/
example : get (s1.at 1) [8] = some 5 := by
  rw [get_right meets 1 (by decide)]; decide

example : get (s1.at 0) [8] = none := by
  rw [get_right meets 0 (by decide)]; decide

example : scan (s1.at 1) {} 10 = [([8], 5)] := by
  rw [scan_right meets 1 (by decide) {} (by decide)]; decide

end Contract.Example
