/-
The contract package (bergdb 030-08): the shape clauses are not vacuous, and
TREE does what it is for.

* Example3's history of three transactions (a put, a split of the root into
  a new inner root, a delete that unlinks a leaf) meets the contract with
  TREE (`Example3.meetsShape`).
* ExampleDag's transaction meets the contract, but not TREE: two segment
  leaves share the next segment's tree (`ExampleDag.not_tree`). So the
  contract with TREE rules it out.
* Example3's history with its top, two top nodes: the first, of time 0,
  names leaf 1; the second, made at time 2 with the new inner root 4, has a
  skip pointer to the first. It meets the contract with TREE and the top
  (`Example3.meetsTop`); Java's readers, from the search through the skip
  pointer, read every time right, between the records too.
-/
import Contract.TheoremsTop
import Contract.Example3
import Contract.ExampleDag

namespace Contract

open Contract

theorem Example3.meetsShape :
    MeetsShape Example3.p [Example3.ops1, Example3.ops2, Example3.ops3] Example3.s3 :=
  MeetsShape.step [Example3.ops1, Example3.ops2] Example3.s2 Example3.ops3 [4] Example3.s3
    (MeetsShape.step [Example3.ops1] Example3.s1 Example3.ops2 [4, 6] Example3.s2
      (MeetsShape.step [] Example3.s0 Example3.ops1 [1] Example3.s1
        (MeetsShape.start Example3.s0 Example3.start (by decide))
        ⟨by decide, Example3.frame1⟩ (by decide))
      ⟨by decide, Example3.frame2⟩ (by decide))
    ⟨by decide, Example3.frame3⟩ (by decide)

/-- TREE at the earlier times, as `tree_right` says; at time 3 the inner root
has a dead klong to leaf 1, which is not reached. -/
example : reach (Example3.s3.at 3) = [4, 6, 3] := by decide
example : reach (Example3.s3.at 2) = [4, 1, 2, 6, 3] := by decide

/-- ExampleDag's transaction does not meet TREE: node 3 and value 2 are
reached twice. -/
theorem ExampleDag.not_tree : ¬ TreeOk (ExampleDag.s1.at 1) := by decide

example : reach (ExampleDag.s1.at 1) = [4, 5, 3, 2, 6, 3, 2] := by decide

/-- Example3's top: the start's top node 10, and top node 11 of time 2. -/
def Example3.top0 : Top := [(10, { time := 0, root := 1, skips := [] })]
def Example3.top2 : Top := Example3.top0 ++ [(11, { time := 2, root := 4, skips := [(0, 10, 0)] })]

theorem Example3.meetsTop :
    MeetsTop Example3.p [Example3.ops1, Example3.ops2, Example3.ops3] Example3.s3 Example3.top2 :=
  MeetsTop.step [Example3.ops1, Example3.ops2] Example3.s2 Example3.top2 Example3.ops3 [4]
    Example3.s3 Example3.top2
    (MeetsTop.step [Example3.ops1] Example3.s1 Example3.top0 Example3.ops2 [4, 6] Example3.s2
      Example3.top2
      (MeetsTop.step [] Example3.s0 Example3.top0 Example3.ops1 [1] Example3.s1 Example3.top0
        (MeetsTop.start Example3.s0 Example3.top0 Example3.start (by decide)
          ⟨10, _, rfl, rfl, rfl⟩ (by decide))
        ⟨by decide, Example3.frame1⟩ (by decide) (Or.inl rfl) (by decide))
      ⟨by decide, Example3.frame2⟩ (by decide)
      (Or.inr ⟨11, _, rfl, by decide, rfl, by decide⟩) (by decide))
    ⟨by decide, Example3.frame3⟩ (by decide) (Or.inl rfl) (by decide)

/-- What the search finds: at time 1, and between the records 1 and 2, the
first top node, through the skip pointer of the second; at time 2, the
second. -/
example : findTop Example3.top2 1 false = some 10 := by decide
example : findTop Example3.top2 1 true = some 10 := by decide
example : findTop Example3.top2 2 false = some 11 := by decide

/-- Java's readers, as the theorems say, at a record's time and between two
records. -/
example : jget Example3.s3 Example3.top2 1 true [8] = some 5 := by
  rw [jget_right Example3.meetsTop 1 (by decide)]; decide
example : jget Example3.s3 Example3.top2 3 false [8] = none := by
  rw [jget_right Example3.meetsTop 3 (by decide)]; decide
example : jscan Example3.s3 Example3.top2 2 true {} 10 = [([8], 5), ([16], 6)] := by
  rw [jscan_right Example3.meetsTop 2 (by decide) _ {} (by decide)]; decide

end Contract
