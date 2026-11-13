/-
Self-indexed streams in Lean: bounds, part 3, a cold start's reads (bergdb item
007; 007-03, step 6; 005-57 and 005-58).

Trusted part: the statements. The definition they are about is in
SIS/BoundCold.lean (`rerunReach`), the proofs in SIS/Proof/BoundCold.lean; the
proofs here only connect them. Added 2026-11-13.
-/
import SIS.Proof.BoundCold

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- A cold start's reads, bounded (007-03, step 6: "a cold startup reads at
random only what the rerun touches"): the lazy startup from any stream S gives
out at most |sectionNodes| + `rerunReach` + 2 handles, one for each object it
makes, so it reads at most that many versions. The section's index nodes are
read in order (`sectionNodes`, R(s), ..., R(k)); the rest is the root's
version and, for each transaction T(j) of the section, the nodes of its
writer's paths, the nodes it creates (which are not read) and the nodes of
gd(j): `rerunReach`. Nothing depends on D but through the gd(j), whose union
is the D that the startup rebuilds (INV-1), which T4 bounds; nothing on the
size of the database. Rule 4 reads nothing in the model, and 005-58 proved
that Java's rule 4 by position links what it links (`Rule4Pos_handles`).
Nothing is assumed of S. -/
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

end SIS
