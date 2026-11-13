/-
Self-indexed streams in Lean: bounds, part 3, a cold start's reads counted as
reads (bergdb item 007; 007-03, step 6; 007-09's second review). Trusted part:
the statements. The definitions they are about are in SIS/BoundColdReads.lean
(`lazyReads`, `lazyReadsRun`, `sectionVersions`, `topHeaderReads`, `sibReach`),
SIS/BoundCold.lean (`rerunReach`), SIS/BoundColdDropJ.lean (`DropRunOKJ`),
SIS/BoundHeight.lean (`LiveHeightLe`) and SIS/BoundT4.lean (`changeAt`); the
proofs in SIS/Proof/BoundColdReads.lean and SIS/Proof/BoundColdReadsD.lean. Added 2026-11-13.
-/
import SIS.Proof.BoundColdReadsD

namespace SIS

variable {V T : Type} [DecidableEq V]

/-- The counted rerun is the lazy startup's: its memory after the rerun is
`lazyStartup`'s. So `lazyReads` counts the reads of the same start. -/
theorem lazyReads_same_start (sp : Spec V T) (sib : T → Nat) (S : Stream V T) :
    (lazyReadsRun sp sib S).1.1 = lazyStartup sp S :=
  lazyReadsRun_mem sp sib S

/-- A cold start's reads, for any stream S: at most every version of the
section (with repeats, as Java parses them), 2 for the top node of the last
transaction, the header reads of rule 4's top-node fallback, twice what the
rerun reaches (`rerunReach`: a header and a version for each node of a
writer's path, a version for each node of gd(j)), and twice the writer's
follows outside its paths (`sibReach`: `Dag.merge`'s siblings). Nothing is
assumed of S. -/
theorem coldReadsJ_lazy (sp : Spec V T) (sib : T → Nat) (S : Stream V T) :
    lazyReads sp sib S ≤ sectionVersions S (lastSp S) + 2 + topHeaderReads sp S (lastSp S) +
      2 * rerunReach sp S + 2 * sibReach sib S :=
  lazyReads_le sp sib S

/-- A cold start's reads after a run (`RunOK`, BergDB's still-dirty test or the
exact one with a written root): at most every version of the section, 2, the
top-node header reads, twice (for each transaction T(j) of the section, its
writer's paths in the run's P after T(j - 1) and its new nodes), 2 |D|, and
twice the follows outside the paths. -/
theorem coldReadsJ_run (sp : Spec V T) (al : Algo V T) (sib : T → Nat) (ts : List T)
    (hok : RunOK sp al ts)
    (hst : al.stillDirty = javaTest sp ∨ (sp.virt = false ∧ al.stillDirty = exactTest sp)) :
    let S := (run sp al ts).S
    lazyReads sp sib S ≤ sectionVersions S (lastSp S) + 2 + topHeaderReads sp S (lastSp S) +
      2 * ((sectionIdx S (lastSp S)).map (fun j =>
        (pathOf sp (run sp al (ts.take (j - 1))).P (changeAt sp al ts j) j).length +
          (changeAt sp al ts j).new.length)).sum +
      2 * (run sp al ts).D.length + 2 * sibReach sib S :=
  lazyReads_run sp al sib ts hok (algOK_of sp al hst)

/-- A cold start's reads after a run, by height, with `DropRunOKJ` (Java's
removals): with the assumptions of `coldReadsJ_run`, TREE in the initial
structure and after every transaction, and the root's live height at most H
after every transaction, at most every version of the section, 2, the
top-node header reads, twice (for each transaction T(j) of the section,
(H + 1) (new nodes + entries + touched nodes + the weights of its entries +
k j) + its new nodes), 2 |D|, and twice the follows outside the paths. -/
theorem coldReadsJ_height (sp : Spec V T) (al : Algo V T) (sib : T → Nat) (ts : List T)
    (hok : RunOK sp al ts)
    (hst : al.stillDirty = javaTest sp ∨ (sp.virt = false ∧ al.stillDirty = exactTest sp))
    (htree0 : treeAt sp (run sp al []).P 0) (htree : TreeRunOK sp al ts)
    (w : V → Nat) (k : Nat → Nat) (hdrop : DropRunOKJ sp al w k ts)
    (H : Nat) (hH : ∀ t ≤ ts.length, LiveHeightLe sp (run sp al (ts.take t)).P t H root) :
    let S := (run sp al ts).S
    lazyReads sp sib S ≤ sectionVersions S (lastSp S) + 2 + topHeaderReads sp S (lastSp S) +
      2 * ((sectionIdx S (lastSp S)).map (fun j =>
        (H + 1) * ((changeAt sp al ts j).new.length + (changeAt sp al ts j).adds.length +
          (changeAt sp al ts j).touch.length +
          ((changeAt sp al ts j).adds.map (fun a => w a.2)).sum + k j) +
        (changeAt sp al ts j).new.length)).sum +
      2 * (run sp al ts).D.length + 2 * sibReach sib S :=
  lazyReads_height_dropJ sp al sib ts hok (algOK_of sp al hst) htree0 htree w k hdrop H hH

/-- A cold start's reads after a run, without the |D| term (007-03, step 6:
"... without T4"): with BergDB's still-dirty test, `RunOK`, `LiveAppend` and
TREE after every transaction, at most every version of the section, 2, the
top-node header reads, twice the writer's paths of the section's transactions
in the run's P, and twice the follows outside the paths. Every node of gd(j)
has a canonical object when the rerun comes to it, so making D canonical reads
nothing more. -/
theorem coldReadsJ_run_noD (sp : Spec V T) (al : Algo V T) (sib : T → Nat) (ts : List T)
    (hok : RunOK sp al ts) (hla : LiveAppend sp) (htree : TreeRunOK sp al ts)
    (hj : al.stillDirty = javaTest sp) :
    let S := (run sp al ts).S
    lazyReads sp sib S ≤ sectionVersions S (lastSp S) + 2 + topHeaderReads sp S (lastSp S) +
      2 * ((sectionIdx S (lastSp S)).map (fun j =>
        (pathOf sp (run sp al (ts.take (j - 1))).P (changeAt sp al ts j) j).length)).sum +
      2 * sibReach sib S :=
  lazyReads_run_noD sp al sib ts hok hla htree hj

/-- A cold start's reads after a run, by height, with Java's removals
(`DropRunOKJ`), without the |D| term: with the assumptions of
`coldReadsJ_run_noD`, TREE in the initial structure, and the root's live
height at most H after every transaction, at most

  (every version of the section) + 2 + (the top-node header reads) +
  2 (for each transaction T(j) of the section, (H + 1) (new nodes + entries +
  touched nodes + the weights of its entries + k j)) + 2 (follows outside the
  writer's paths)

reads. No |D|, no `removedAt`, no level number, every version and header read
counted. -/
theorem coldReadsJ_height_noD (sp : Spec V T) (al : Algo V T) (sib : T → Nat) (ts : List T)
    (hok : RunOK sp al ts) (hla : LiveAppend sp) (hj : al.stillDirty = javaTest sp)
    (htree0 : treeAt sp (run sp al []).P 0) (htree : TreeRunOK sp al ts)
    (w : V → Nat) (k : Nat → Nat) (hdrop : DropRunOKJ sp al w k ts)
    (H : Nat) (hH : ∀ t ≤ ts.length, LiveHeightLe sp (run sp al (ts.take t)).P t H root) :
    let S := (run sp al ts).S
    lazyReads sp sib S ≤ sectionVersions S (lastSp S) + 2 + topHeaderReads sp S (lastSp S) +
      2 * ((sectionIdx S (lastSp S)).map (fun j =>
        (H + 1) * ((changeAt sp al ts j).new.length + (changeAt sp al ts j).adds.length +
          (changeAt sp al ts j).touch.length +
          ((changeAt sp al ts j).adds.map (fun a => w a.2)).sum + k j))).sum +
      2 * sibReach sib S :=
  lazyReads_height_noD sp al sib ts hok hla hj htree0 htree w k hdrop H hH

end SIS
