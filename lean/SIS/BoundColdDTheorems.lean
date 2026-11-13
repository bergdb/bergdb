/-
Self-indexed streams in Lean: bounds, part 3, a cold start's reads without the
|D| term, and the nodes a change makes unreachable (bergdb item 007; 007-03,
step 6).

Trusted part: the statements. The definitions they are about are in
SIS/BoundCold.lean (`rerunReach`, `removedAt`), SIS/BoundColdDrop.lean
(`DropStep`, `DropRunOK`) and SIS/BoundT4.lean (`changeAt`), the proofs in
SIS/Proof/BoundColdD.lean; the proofs here only connect them. Added
2026-11-13.
-/
import SIS.Proof.BoundColdD

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- A cold start's reads after a run, without D (007-03, step 6: "a cold
startup reads at random only what the rerun touches ... without T4"): with
BergDB's still-dirty test, `RunOK`, `LiveAppend` and TREE after every
transaction, the lazy startup from the run's stream gives out at most

  (the section's index nodes) + (for each transaction T(j) of the section,
  s < j ≤ k, the nodes of its writer's paths in the run's P after T(j - 1),
  and the nodes it creates) + 2

handles: `coldReads_run` without its |D| term. Every node of gd(j) already has
a canonical object when the rerun of T(j) comes to it (the lazy startup's
invariant, `MemInv.coverGd`), so making D canonical reads nothing more. -/
theorem coldReads_run_noD (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hla : LiveAppend sp) (htree : TreeRunOK sp al ts) (hj : al.stillDirty = javaTest sp) :
    let S := (run sp al ts).S
    (lazyStartup sp S).next ≤ (sectionNodes S (lastSp S)).length +
      ((sectionIdx S (lastSp S)).map (fun j =>
        (pathOf sp (run sp al (ts.take (j - 1))).P (changeAt sp al ts j) j).length +
          (changeAt sp al ts j).new.length)).sum + 2 :=
  coldReads_run_noD_of sp al ts hok hla htree hj

/-- A cold start's reads after a run with TREE, without D: with the assumptions
of `coldReads_run_noD`, TREE in the initial structure, and H the root's level
after the run, `coldReads_tree`'s bound without its |D| term. -/
theorem coldReads_tree_noD (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hla : LiveAppend sp) (hj : al.stillDirty = javaTest sp)
    (htree0 : treeAt sp (run sp al []).P 0) (htree : TreeRunOK sp al ts)
    (n0 : Node V) (h0 : (run sp al ts).P.get? root = some n0) :
    let S := (run sp al ts).S
    (lazyStartup sp S).next ≤ (sectionNodes S (lastSp S)).length +
      ((sectionIdx S (lastSp S)).map (fun j =>
        (n0.level + 1) * ((changeAt sp al ts j).new.length + (changeAt sp al ts j).adds.length +
          (changeAt sp al ts j).touch.length +
          (removedAt sp (run sp al (ts.take (j - 1))).P (changeAt sp al ts j) j).length) +
        (changeAt sp al ts j).new.length)).sum + 2 :=
  coldReads_tree_noD_of sp al ts hok hla hj htree0 htree n0 h0

/-- The nodes a change makes unreachable (`removedAt`): with `DropStep` (BergDB
drops no subtree: a split's new nodes take the children of the node it
replaces), at most as many as the change's entries. No TREE is needed.
Without `DropStep` no such bound holds (SIS/BoundColdDropExample.lean). -/
theorem removedAt_bound (sp : Spec V T) (P : Struct V) (j : Time) (c : Changes V)
    (hd : DropStep sp P j c) : (removedAt sp P c j).length ≤ c.adds.length :=
  removedAt_le_adds sp P j c hd

/-- A cold start's reads after a run with TREE, without D and without
`removedAt`: with the assumptions of `coldReads_tree_noD` and `DropRunOK`, the
lazy startup gives out at most

  (the section's index nodes) + (for each transaction T(j) of the section,
  (H + 1) (new nodes + 2 entries + touched nodes of T(j)) + its new nodes) + 2

handles, H the root's level after the run. -/
theorem coldReads_tree_drop (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hla : LiveAppend sp) (hj : al.stillDirty = javaTest sp)
    (htree0 : treeAt sp (run sp al []).P 0) (htree : TreeRunOK sp al ts) (hdrop : DropRunOK sp al ts)
    (n0 : Node V) (h0 : (run sp al ts).P.get? root = some n0) :
    let S := (run sp al ts).S
    (lazyStartup sp S).next ≤ (sectionNodes S (lastSp S)).length +
      ((sectionIdx S (lastSp S)).map (fun j =>
        (n0.level + 1) * ((changeAt sp al ts j).new.length + 2 * (changeAt sp al ts j).adds.length +
          (changeAt sp al ts j).touch.length) +
        (changeAt sp al ts j).new.length)).sum + 2 :=
  coldReads_tree_drop_of sp al ts hok hla hj htree0 htree hdrop n0 h0

end SIS
