/-
The contract package (bergdb 030-06, the review of 030-05): the contract does
not give TREE. One transaction from the empty tree puts the keys [56, 8] and
[120, 8] (56 and 120 are long segments) with one value, and the two segment
leaves of the new inner root share the next segment's tree (node 3) and its
value (node 2). The transaction meets the writer's contract, and the theorems
on reads hold for it; but node 3 is a live child of two reachable nodes, so
the abstract model's TREE (lean/SIS/Phys.lean, `treeAt`), which the theorems
of eviction and handles assume, fails. A clause for step 4 (030-06, F3).
-/
import Contract.Theorems

namespace Contract.ExampleDag

open Contract

def p : Params := { M := 8 }

def s0 : Tree :=
  { obj := fun x => if x = 1 then some (.key { level := 1, leaf := true, ks := [.time 0] })
      else none,
    roots := [(0, 1)] }

/-- The inner root 4; its segment leaves 5 and 6; the shared tree 3 of the
second segment; the shared value 2. -/
def inner : KNode := { level := 3, leaf := false, ks := [.time 1, .key 0 5, .key 120 6] }
def leaf5 : KNode := { level := 2, leaf := true, ks := [.time 1, .key 56 3] }
def leaf6 : KNode := { level := 2, leaf := true, ks := [.time 1, .key 120 3] }
def leaf3 : KNode := { level := 1, leaf := true, ks := [.time 1, .key 8 2] }

def s1 : Tree :=
  { obj := fun x =>
      if x = 1 then some (.key { level := 1, leaf := true, ks := [.time 0] })
      else if x = 2 then some (.val 5) else if x = 3 then some (.key leaf3)
      else if x = 4 then some (.key inner) else if x = 5 then some (.key leaf5)
      else if x = 6 then some (.key leaf6) else none,
    roots := [(0, 1), (1, 4)] }

def ops : List Op := [.put [56, 8] 5, .put [120, 8] 5]

theorem frame : Frame 1 s0 [3, 4, 5, 6] s1 := by
  refine ⟨?_, ?_, ⟨[(1, 4)], by simp [s0, s1], by simp⟩⟩
  · intro x o hx
    by_cases h1 : x = 1
    · subst h1
      simp only [s0, ite_true, Option.some.injEq] at hx
      subst hx
      exact ⟨.key { level := 1, leaf := true, ks := [.time 0] }, by simp [s1],
        ⟨rfl, rfl, Or.inl rfl⟩, fun _ => rfl⟩
    · simp [s0, h1] at hx
  · intro x n hx hno
    by_cases h1 : x = 1
    · simp [s0, h1] at hno
    · by_cases h2 : x = 2
      · simp [s1, h2] at hx
      · by_cases h3 : x = 3
        · simp [h3]
        · by_cases h4 : x = 4
          · simp [h4]
          · by_cases h5 : x = 5
            · simp [h5]
            · by_cases h6 : x = 6
              · simp [h6]
              · simp [s1, h1, h2, h3, h4, h5, h6] at hx

/-- The transaction meets the contract: a history of one transaction. -/
theorem meets : Meets p [ops] s1 :=
  Meets.step [] s0 ops [3, 4, 5, 6] s1 (Meets.start s0 (by constructor <;> decide))
    ⟨by decide, frame⟩

/-- The reads are right, as the theorems say. -/
example : scan (s1.at 1) {} 10 = [([56, 8], 5), ([120, 8], 5)] := by
  rw [scan_right meets 1 (by decide) {} (by decide)]; decide

/-- But node 3 is a live child of two nodes that the root reaches at time 1:
leaf 5 and leaf 6, both live children of the space root 4. Not a tree. -/
example : s1.root = some 4 ∧ (live inner.ks).map (·.2) = [5, 6] ∧
    (live leaf5.ks).map (·.2) = [3] ∧ (live leaf6.ks).map (·.2) = [3] := by decide

end Contract.ExampleDag
