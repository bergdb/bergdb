/-
Self-indexed streams in Lean: bounds counted by the height of the tree (bergdb
item 007; 007-09, section 5). Trusted part: the statements. The definitions
they are about are in SIS/BoundHeight.lean (`LiveHeightLe`),
SIS/BoundT4Java.lean (`PtrHeightLe`, `ptrParents`, `geomSum`),
SIS/BoundColdDrop.lean (`DropRunOK`), SIS/BoundCold.lean and SIS/BoundT4.lean;
the proofs in SIS/Proof/BoundHeight.lean. Added 2026-11-13.

In 024-12's tree model a level is a code, so the root's level says nothing of
the height. Here H counts nodes on paths: `LiveHeightLe` along the live
pointers at a time (for BergDB, the tree's height then, plus one for the
virtual root), `PtrHeightLe` along all pointers, live or dead.
-/
import SIS.Proof.BoundHeight

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- T4's debt with BergDB's test and TREE, by height: with the assumptions of
`T4_debt_java_tree`, every node of D of height at most Hp along all pointers
(`PtrHeightLe`), and the root's live height at most Hl after every transaction
(`LiveHeightLe`), D has at most

  (1 + Q + ... + Q^Hp) ((Hl + 1) (new nodes + entries of T(τ)) + (touched nodes of T(τ)))

summed over the transactions T(τ) of the last Hp + 1 startup sections,
a < τ ≤ k, a = spIter S (Hp + 1) k. With a virtual root too. -/
theorem T4_debt_java_tree_height (sp : Spec V T) (al : Algo V T) (ts : List T)
    (hok : RunOK sp al ts) (hj : al.stillDirty = javaTest sp) (htree : TreeRunOK sp al ts)
    (Hp Hl Q : Nat)
    (hHp : ∀ e ∈ (run sp al ts).D, PtrHeightLe sp (run sp al ts).P Hp e.1)
    (hHl : ∀ t ≤ ts.length, LiveHeightLe sp (run sp al (ts.take t)).P t Hl root)
    (hQ : ∀ z, (ptrParents sp (run sp al ts).P z).length ≤ Q) :
    let a := spIter (run sp al ts).S (Hp + 1) ts.length
    (run sp al ts).D.length ≤ geomSum Q Hp *
      ((List.range' (a + 1) (ts.length - a)).map (fun τ =>
        (Hl + 1) * ((changeAt sp al ts τ).new.length + (changeAt sp al ts τ).adds.length) +
          (changeAt sp al ts τ).touch.length)).sum :=
  debt_tree_java_h sp al ts hok hj htree Hp Hl Q hHp hHl hQ

/-- A cold start's reads after a run, by height (007-03, step 6: "at most a
node per level of the tree for each key rerun"): with BergDB's still-dirty
test, `RunOK`, `LiveAppend`, TREE in the initial structure and after every
transaction, `DropRunOK`, and the root's live height at most H after every
transaction, the lazy startup from the run's stream gives out at most

  (the section's index nodes) + (for each transaction T(j) of the section,
  (H + 1) (new nodes + 2 entries + touched nodes of T(j)) + its new nodes) + 2

handles. No |D| term, no `removedAt`, no level number. -/
theorem coldReads_height (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hla : LiveAppend sp) (hj : al.stillDirty = javaTest sp)
    (htree0 : treeAt sp (run sp al []).P 0) (htree : TreeRunOK sp al ts) (hdrop : DropRunOK sp al ts)
    (H : Nat) (hH : ∀ t ≤ ts.length, LiveHeightLe sp (run sp al (ts.take t)).P t H root) :
    let S := (run sp al ts).S
    (lazyStartup sp S).next ≤ (sectionNodes S (lastSp S)).length +
      ((sectionIdx S (lastSp S)).map (fun j =>
        (H + 1) * ((changeAt sp al ts j).new.length + 2 * (changeAt sp al ts j).adds.length +
          (changeAt sp al ts j).touch.length) +
        (changeAt sp al ts j).new.length)).sum + 2 :=
  coldReads_height_of sp al ts hok hla hj htree0 htree hdrop H hH

end SIS
