/-
The tree model (bergdb 024-12, section 6): TP13 closed. `SpecOK` for the tree's
structure, from SIS/Proof/TreeInit.lean (`specOKTree_of_liveSub`) and
`blive_sub` of Check/Live.lean (bergdb 024-09), the property of `blive` that
`SpecOK.liveSub` asks. Here and not in SIS/Proof, as `blive_sub` is proved in
the checker's library. Proofs; not needed for reading the statements.
-/
import Check.Live
import SIS.Proof.TreeInit

namespace SIS.Tree

open SIS SIS.Check

/-- TP13, proved: the tree's structure meets `SpecOK`, with `VirtInit`. -/
theorem specOKTree (p : Params) : SpecOKTree p :=
  specOKTree_of_liveSub p (fun h y hy => blive_sub h y hy)

end SIS.Tree
