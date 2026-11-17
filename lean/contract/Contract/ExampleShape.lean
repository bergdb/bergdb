/-
The contract package (bergdb 030-08): the shape clauses are not vacuous, and
TREE does what it is for.

* Example3's history of three transactions (a put, a split of the root into
  a new inner root, a delete that unlinks a leaf) meets the contract with
  TREE (`Example3.meetsShape`).
* ExampleDag's transaction meets the contract, but not TREE: two segment
  leaves share the next segment's tree (`ExampleDag.not_tree`). So the
  contract with TREE rules it out.
-/
import Contract.TheoremsShape
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

end Contract
