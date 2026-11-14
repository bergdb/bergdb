import SIS.Tree.WriterGrowth

namespace SIS.Tree

open SIS SIS.Check

/-- All heights seen by the writer are at most cap. -/
def SeenHeightBound (cap : Nat) (w : W) : Prop :=
  ∀ x g h, (x, g, h) ∈ w.gh → h ≤ cap

theorem gh_lookup_mem {ns : List (NodeId × Nat × Nat)} {x g h : Nat}
    (hm : ns.lookup x = some (g, h)) : (x, g, h) ∈ ns := by
  obtain ⟨a, b, he, _⟩ := List.lookup_eq_some_iff.mp hm
  rw [he]
  simp

end SIS.Tree
