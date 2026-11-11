/-
The tree model (bergdb 024-12, section 6): TP13 and TP15 closed. `SpecOK` for
the tree's structure, from SIS/Proof/TreeInit.lean (`specOKTree_of_liveSub`)
and `blive_sub` of Check/Live.lean (bergdb 024-09), the property of `blive`
that `SpecOK.liveSub` asks; and `LiveAppend`, which is `blive_append` there.
Here and not in SIS/Proof, as both are proved in the checker's library.
Proofs; not needed for reading the statements.
-/
import Check.Live
import SIS.Proof.TreeInit

namespace SIS.Tree

open SIS SIS.Check

/-- TP13, proved: the tree's structure meets `SpecOK`, with `VirtInit`. -/
theorem specOKTree (p : Params) : SpecOKTree p :=
  specOKTree_of_liveSub p (fun h y hy => blive_sub h y hy)

/-- TP15, proved: the tree's `live` has `LiveAppend`. -/
theorem liveAppendTree (p : Params) : LiveAppendTree p :=
  blive_append

end SIS.Tree
