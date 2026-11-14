/-
Self-indexed streams in Lean: bounds, part 3, a cold start's reads (bergdb item
007; 007-03, step 6; 005-57 and 005-58).

Trusted part: the statements. The definition they are about is in
SIS/BoundCold.lean (`rerunReach`) and SIS/BoundT4.lean (`changeAt`), the
proofs in SIS/Proof/BoundCold.lean; the proofs here only connect them. Added
2026-11-13.
-/
import SIS.Proof.BoundCold

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- A cold start's reads, bounded (007-03, step 6: "a cold startup reads at
random only what the rerun touches"): the lazy startup from any stream S gives
out at most |sectionNodes| + `rerunReach` + 2 handles, one for each object it
makes. The section's index nodes are read in order (`sectionNodes`, R(s),
..., R(k)); the rest is the root's version and, for each transaction T(j) of
the section, the nodes of its writer's paths, the nodes it creates (which are
not read) and the nodes of gd(j): `rerunReach`. Nothing depends on D but
through the gd(j), whose union is the D that the startup rebuilds (INV-1),
which T4 bounds; nothing on the size of the database. Rule 4 reads nothing in
the model, and 005-58 proved that Java's rule 4 by position links what it
links (`Rule4Pos_handles`). Nothing is assumed of S. This counts objects, not
reads: Java reads more (header reads, among them rule 4's for a top node's
pointers; every version of the section, repeats included; the merges'
siblings), which `lazyReads` counts (SIS/BoundCold.lean's header; bergdb
007-09, section 2.1). -/
theorem coldReads_lazy (sp : Spec V T) (S : Stream V T) :
    (lazyStartup sp S).next ≤ (sectionNodes S (lastSp S)).length + rerunReach sp S + 2 :=
  lazyStartup_next sp S

/-- The same for the startup with handles (`handleStartup`, rule 4 by node id)
and with Java's rule 4 by position (`handleStartupPos`): they give out the
lazy startup's objects and make no more. -/
theorem coldReads_handles (sp : Spec V T) (S : Stream V T) :
    (handleStartup sp S).nextObj ≤ (sectionNodes S (lastSp S)).length + rerunReach sp S + 2 ∧
      (handleStartupPos sp S).nextObj ≤ (sectionNodes S (lastSp S)).length + rerunReach sp S + 2 :=
  ⟨lazyStartup_next sp S, lazyStartup_next sp S⟩

/-- A cold start's reads after a run (BergDB's still-dirty test, or the exact
one with a written root, and `RunOK`): the lazy startup from the run's stream
gives out at most

  (the section's index nodes) + (for each transaction T(j) of the section,
  s < j ≤ k, the nodes of its writer's paths in the run's P after T(j - 1),
  and the nodes it creates) + |D| + 2

handles. So a cold start reads the section's nodes in order, at most the
rerun's writer paths at random, and the debt D (`T4_debt` bounds it with the
exact test). T3 bounds the transactions of the section (`T3_take_rerun`); a
bound on a transaction's writer paths, the nodes reachable at j - 1 with a node
below that T(j) changes, touches or makes unreachable (`pathOf`), is not
stated here. -/
theorem coldReads_run (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hst : al.stillDirty = javaTest sp ∨ (sp.virt = false ∧ al.stillDirty = exactTest sp)) :
    let S := (run sp al ts).S
    (lazyStartup sp S).next ≤ (sectionNodes S (lastSp S)).length +
      ((sectionIdx S (lastSp S)).map (fun j =>
        (pathOf sp (run sp al (ts.take (j - 1))).P (changeAt sp al ts j) j).length +
          (changeAt sp al ts j).new.length)).sum + (run sp al ts).D.length + 2 :=
  coldReads_run_of sp al ts hok (algOK_of sp al hst)

/-- A cold start's reads after a run, with TREE (007-03, step 6: "at most a node
per level of the tree for each key rerun"): with the assumptions of
`coldReads_run`, TREE in the initial structure and after every transaction
(`TreeRunOK`), and H the root's level after the run, the lazy startup gives out
at most

  (the section's index nodes) + (for each transaction T(j) of the section,
  (H + 1) times the nodes it creates, gives entries (`Changes.adds`), touches
  or makes unreachable (`removedAt`), and the nodes it creates) + |D| + 2

handles. In BergDB a node that a transaction makes unreachable is one a split
replaces, a child of a node given an entry. -/
theorem coldReads_tree (sp : Spec V T) (al : Algo V T) (ts : List T) (hok : RunOK sp al ts)
    (hst : al.stillDirty = javaTest sp ∨ (sp.virt = false ∧ al.stillDirty = exactTest sp))
    (htree0 : treeAt sp (run sp al []).P 0) (htree : TreeRunOK sp al ts)
    (n0 : Node V) (h0 : (run sp al ts).P.get? root = some n0) :
    let S := (run sp al ts).S
    (lazyStartup sp S).next ≤ (sectionNodes S (lastSp S)).length +
      ((sectionIdx S (lastSp S)).map (fun j =>
        (n0.level + 1) * ((changeAt sp al ts j).new.length + (changeAt sp al ts j).adds.length +
          (changeAt sp al ts j).touch.length +
          (removedAt sp (run sp al (ts.take (j - 1))).P (changeAt sp al ts j) j).length) +
        (changeAt sp al ts j).new.length)).sum + (run sp al ts).D.length + 2 :=
  coldReads_tree_of sp al ts hok (algOK_of sp al hst) htree0 htree n0 h0

end SIS
