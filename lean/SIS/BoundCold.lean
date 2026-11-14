/-
Self-indexed streams in Lean: bounds, part 3, a cold start's reads (bergdb item
007; 007-01, 5.3; 007-03, step 6; 005-57 and 005-58).

Trusted part: the definition that the bound is about. The statements are in
SIS/BoundColdTheorems.lean, the proofs in SIS/Proof/BoundCold.lean. Added
2026-11-13.

The prose (007-03, step 6, after 005-57): "With the reads few (B) or gone (C),
a cold startup reads at random only what the rerun touches, at most a node per
level of the tree for each key rerun, and the section bounds that, with T3 and
the deadline, without T4." 005-58 proved that rule 4 by position (Java since
005-57) links what rule 4 by node id links (`Rule4Pos_handles`). The theorems
of SIS/BoundColdTheorems.lean bound, with `rerunReach`, the objects that the
model's lazy startup makes (`lazyStartup`, SIS/Phys.lean; with handles
`handleStartup`): each object is a version it reads (the section's index nodes
in order, each once, the root, a first touch of the rerun's writer through a
stream slot, a node of a section's gd), or a node that a rerun transaction
creates, and each takes a new handle (`Mem.addObj`), so the handles given out
bound the objects made.

They do not bound Java's reads (bergdb 007-09, section 2.1, and its second
review): rule 4 reads a header for a pointer of a top node of D, at most one
for each (the top-node fallback of `NodeCollection.linkToCanonical`;
`topHeaderReads`, the Pt term of `bounded_startup`); Java parses every version
of the section, repeats included (`StoredTrans.Parser.parse`), where the
model's section nodes have none; a follow of a stream pointer reads a header
before it finds a cached object; and the merges read siblings outside the
writer's paths. `lazyReads` (SIS/BoundColdReads.lean) counts these reads, and
the theorems on it (SIS/BoundColdReadsTheorems.lean) bound them.
-/
import SIS.Phys

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- What the rerun of the lazy startup from S reaches (`lazyStartup`, step 3):
over the transactions T(j) of the startup section, s < j ≤ k, with P the
structure that directs the writer (the logical startup's, `baseStruct` and the
rerun), the nodes on the writer's paths for T(j)'s change (`pathOf`), the
nodes T(j) creates, and the nodes of gd(j), summed. -/
def rerunReach (sp : Spec V T) (S : Stream V T) : Nat :=
  let s := lastSp S
  ((sectionIdx S s).foldl (fun (acc : Nat × Struct V) j =>
    match S[j]? with
    | some R =>
      match R.trans with
      | some tr =>
        let c := sp.exec tr j (view sp acc.2 (j - 1))
        (acc.1 + (pathOf sp acc.2 c j).length + c.new.length + R.gd.length, acc.2.apply j c)
      | none => acc
    | none => acc) (0, baseStruct sp S s true)).1

/-- The nodes that the change c at time j makes unreachable: reachable at j - 1
in P, not at j after the change. In BergDB a node that a split replaces. -/
def removedAt (sp : Spec V T) (P : Struct V) (c : Changes V) (j : Time) : List NodeId :=
  (reachList sp P (j - 1)).eraseDups.filter (fun z => !reachable sp (P.apply j c) j z)

end SIS
